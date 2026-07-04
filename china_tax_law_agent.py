#!/usr/bin/env python3
"""
china_tax_law_agent.py
=======================
Automated intelligence agent: China corporate tax and business law watch.

Business context
-----------------
- Entity      : TLD Group (Alvest subsidiary) - APAC Finance Department (CFO)
- Scope       : Mainland China (Shanghai & Wuxi manufacturing sites), WFOE
                structuring, HK-registered director mandates.
- Objective   : detect any tax, legal, customs, or compliance change likely
                to affect a foreign-owned manufacturing entity (WFOE) in
                China and its APAC reporting/structuring.

Architecture (aligned with the GSE / China Eco Watch agent suite)
-------------------------------------------------------------------
1. Static source scraping (BeautifulSoup + exponential retry/backoff)
2. Complementary Tavily search (bypasses IP-blocking of .gov.cn sources from
   GitHub Actions US runners, covers non-scrapable / JS-heavy sources)
3. Weekly structural brief via DeepSeek (training-knowledge only, cached for
   7 days to avoid wasting API calls)
4. Article enrichment (page body extraction)
5. Keyword filtering (strict \\b word-boundary matching for any ASCII
   acronym of 4 uppercase letters or fewer, to avoid false positives)
6. DeepSeek analysis with delimiter-based structured output + truncation
   detection
7. HTML report (CRITICAL/IMPORTANT/WATCH/INFO impact levels), executive
   summary, "top risk to watch" section, clickable sources
"""

from __future__ import annotations

import functools
import json
import logging
import os
import random
import re
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Optional
from urllib.parse import urljoin

import markdown as markdown_lib
import requests
from bs4 import BeautifulSoup

try:
    from tavily import TavilyClient
except ImportError:  # pragma: no cover - safeguard if the package isn't installed
    TavilyClient = None


# ---------------------------------------------------------------------------
# CONFIGURATION
# ---------------------------------------------------------------------------

ORG_NAME = "TLD Group"
ORG_CONTEXT = "APAC Finance Department (CFO) - Shanghai & Wuxi manufacturing sites, WFOE entities"
REGION_LABEL = "Mainland China (PRC)"
REPORT_LANG = "en"

DEEPSEEK_API_KEY = os.environ.get("DEEPSEEK_API_KEY", "")
TAVILY_API_KEY = os.environ.get("TAVILY_API_KEY", "")

BASE_DIR = Path(__file__).resolve().parent
DATA_DIR = BASE_DIR / "data"
REPORTS_DIR = BASE_DIR / "reports"
DATA_DIR.mkdir(parents=True, exist_ok=True)
REPORTS_DIR.mkdir(parents=True, exist_ok=True)

WEEKLY_BRIEF_CACHE_FILE = DATA_DIR / "weekly_brief_cache.json"
SEEN_URLS_FILE = DATA_DIR / "seen_urls.json"
WEEKLY_BRIEF_MAX_AGE_DAYS = 7
SEEN_URLS_RETENTION_DAYS = 30

TEST_MODE = "--test" in os.sys.argv or os.environ.get("TEST_MODE") == "1"

REQUEST_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
    ),
    "Accept-Language": "en-US,en;q=0.9,fr;q=0.8,zh-CN;q=0.7",
}

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
)
logger = logging.getLogger("china_tax_law_agent")


# ---------------------------------------------------------------------------
# SOURCES
# ---------------------------------------------------------------------------
# type="scrape" -> direct HTML scraping (BeautifulSoup)
# Chinese government sites and JS-heavy sites are deliberately duplicated by
# targeted Tavily queries (see TAVILY_QUERIES) because their scrapability
# from US-based runners is uncertain (IP-blocking / anti-bot protections).

STATIC_SOURCES = [
    {
        "name": "China Briefing (Dezan Shira) - Tax",
        "url": "https://www.china-briefing.com/news/category/tax/",
        "max_items": 15,
        "min_text_len": 20,
    },
    {
        "name": "China Briefing (Dezan Shira) - Legal & Regulatory",
        "url": "https://www.china-briefing.com/news/category/legal-regulatory/",
        "max_items": 15,
        "min_text_len": 20,
    },
    {
        "name": "Global Compliance News - China",
        "url": "https://www.globalcompliancenews.com/category/china/",
        "max_items": 15,
        "min_text_len": 20,
    },
    {
        "name": "State Council of China - English News",
        "url": "https://english.www.gov.cn/news/",
        "max_items": 15,
        "min_text_len": 20,
    },
    {
        "name": "MOFCOM - Significant News (English)",
        "url": "http://english.mofcom.gov.cn/article/newsrelease/significantnews/",
        "max_items": 15,
        "min_text_len": 20,
    },
    {
        "name": "State Taxation Administration - English",
        "url": "http://www.chinatax.gov.cn/eng/c101270/c5121583/index.html",
        "max_items": 15,
        "min_text_len": 20,
    },
    {
        "name": "Deloitte China - Tax Newsflash",
        "url": "https://www2.deloitte.com/cn/en/pages/tax/topics/tax-newsflash.html",
        "max_items": 15,
        "min_text_len": 20,
    },
    {
        "name": "Mondaq - China Tax Authorities",
        "url": "https://www.mondaq.com/china/tax-authorities",
        "max_items": 15,
        "min_text_len": 20,
    },
]

# Tavily queries: safety net for non-scrapable sources (JS SPAs, anti-bot)
# and to cover Chinese authorities that are frequently IP-blocked.
TAVILY_QUERIES = [
    "China corporate income tax law change",
    "China VAT export rebate policy update",
    "China individual income tax expatriate policy update",
    "China foreign investment law amendment",
    "China transfer pricing regulation SAT State Taxation Administration",
    "Shanghai free trade zone tax incentive update",
    "China company law amendment implementation 2026",
    "China customs duty tariff manufacturing export regulation",
    "China data security law PIPL compliance update foreign company",
    "China social security contribution foreign employee regulation",
]

ENTITIES_TO_WATCH = [
    "State Taxation Administration (SAT) / 国家税务总局",
    "Ministry of Finance (MOF) / 财政部",
    "State Administration for Market Regulation (SAMR) / 市场监管总局",
    "Ministry of Commerce (MOFCOM) / 商务部",
    "National Development and Reform Commission (NDRC) / 国家发展和改革委员会",
    "State Council / 国务院",
    "Shanghai / Wuxi local tax bureaus / 地方税务局",
    "China (Shanghai) Pilot Free Trade Zone / 中国（上海）自由贸易试验区",
]

# ---------------------------------------------------------------------------
# KEYWORDS
# ---------------------------------------------------------------------------
# Anti-false-positive rule: any ASCII acronym of 4 uppercase letters or fewer
# (e.g. CIT, VAT, IIT, SAT, MOF, NDRC, FTZ, CRS, BEPS, APA, RMB, PIPL) is
# matched with a strict word boundary \b...\b to avoid e.g. "ANA" matching
# inside "China" or "BRI" matching inside "Bristol". All other keywords
# (phrases, words >4 letters, Chinese characters) are matched as a
# case-insensitive substring.

KEYWORDS = [
    # Tax - English
    "corporate income tax", "CIT", "value-added tax", "VAT",
    "individual income tax", "IIT", "withholding tax", "tax incentive",
    "tax rebate", "export rebate", "tax treaty", "double taxation",
    "transfer pricing", "APA", "advance pricing arrangement",
    "anti-avoidance", "BEPS", "CRS", "common reporting standard",
    "golden tax system", "tax filing", "annual tax reconciliation",
    "preferential tax policy", "super deduction",
    # Corporate law / regulation - English
    "company law", "foreign investment law", "FIE", "WFOE",
    "joint venture regulation", "negative list", "market access",
    "business license", "annual compliance", "beneficial owner",
    "data security law", "PIPL", "personal information protection",
    "cybersecurity law", "anti-monopoly", "SAMR",
    # Customs / labor
    "customs duty", "tariff", "export control", "social security contribution",
    "labor law", "labor contract law",
    # Institutions
    "State Taxation Administration", "SAT", "Ministry of Finance", "MOF",
    "MOFCOM", "NDRC", "State Council", "free trade zone", "FTZ", "RMB",
    # Chinese
    "企业所得税", "增值税", "个人所得税", "转让定价", "外商投资法",
    "公司法", "国家税务总局", "财政部", "市场监管总局", "商务部",
    "自由贸易区", "自贸区", "数据安全法", "个人信息保护法", "关税",
    "社保", "劳动合同法", "反垄断",
]

ACRONYM_PATTERN = re.compile(r"^[A-Z]{1,4}$")


def _build_keyword_patterns():
    patterns = []
    for kw in KEYWORDS:
        if ACRONYM_PATTERN.match(kw):
            patterns.append(re.compile(r"\b" + re.escape(kw) + r"\b"))
        else:
            patterns.append(re.compile(re.escape(kw), re.IGNORECASE))
    return patterns


KEYWORD_PATTERNS = _build_keyword_patterns()


def keyword_match(text: Optional[str]) -> bool:
    if not text:
        return False
    return any(p.search(text) for p in KEYWORD_PATTERNS)


# ---------------------------------------------------------------------------
# RETRY / BACKOFF
# ---------------------------------------------------------------------------

def retry_with_backoff(max_retries=3, base_delay=1.5, max_delay=20.0):
    def decorator(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            delay = base_delay
            last_exc = None
            for attempt in range(1, max_retries + 1):
                try:
                    return func(*args, **kwargs)
                except (requests.RequestException, ValueError) as exc:
                    last_exc = exc
                    logger.warning(
                        "%s failed (attempt %d/%d): %s",
                        func.__name__, attempt, max_retries, exc,
                    )
                    if attempt < max_retries:
                        sleep_time = min(delay, max_delay) + random.uniform(0, 0.75)
                        time.sleep(sleep_time)
                        delay *= 2
            logger.error("%s gave up after %d attempts: %s", func.__name__, max_retries, last_exc)
            return None
        return wrapper
    return decorator


@retry_with_backoff(max_retries=3, base_delay=1.5)
def fetch_url(url: str, timeout: int = 15) -> Optional[str]:
    resp = requests.get(url, headers=REQUEST_HEADERS, timeout=timeout)
    resp.raise_for_status()
    return resp.text


@retry_with_backoff(max_retries=3, base_delay=2.0)
def post_json(url: str, headers: dict, payload: dict, timeout: int = 90) -> Optional[dict]:
    resp = requests.post(url, headers=headers, json=payload, timeout=timeout)
    resp.raise_for_status()
    return resp.json()


# ---------------------------------------------------------------------------
# STATIC SCRAPING
# ---------------------------------------------------------------------------

def scrape_source(source_cfg: dict) -> list[dict]:
    html = fetch_url(source_cfg["url"])
    if not html:
        logger.warning("Source unreachable (scrape): %s", source_cfg["name"])
        return []

    soup = BeautifulSoup(html, "lxml")
    articles, seen_local = [], set()

    for a_tag in soup.find_all("a", href=True):
        text = a_tag.get_text(strip=True)
        href = a_tag["href"]
        if not text or len(text) < source_cfg.get("min_text_len", 20):
            continue
        if not keyword_match(text):
            continue
        full_url = urljoin(source_cfg["url"], href)
        if full_url in seen_local or full_url == source_cfg["url"]:
            continue
        seen_local.add(full_url)
        articles.append({
            "title": text,
            "url": full_url,
            "source": source_cfg["name"],
            "date": None,
            "snippet": "",
        })

    max_items = source_cfg.get("max_items", 15)
    logger.info("Scrape [%s]: %d relevant article(s)", source_cfg["name"], len(articles[:max_items]))
    return articles[:max_items]


def scrape_all_static_sources() -> list[dict]:
    all_articles = []
    sources = STATIC_SOURCES[:3] if TEST_MODE else STATIC_SOURCES
    for src in sources:
        all_articles.extend(scrape_source(src))
    return all_articles


# ---------------------------------------------------------------------------
# TAVILY SEARCH
# ---------------------------------------------------------------------------

def tavily_search_all() -> list[dict]:
    if not TAVILY_API_KEY or TavilyClient is None:
        logger.warning("TAVILY_API_KEY missing or tavily package not installed: skipping Tavily search")
        return []

    client = TavilyClient(api_key=TAVILY_API_KEY)
    results = []
    queries = TAVILY_QUERIES[:3] if TEST_MODE else TAVILY_QUERIES

    for query in queries:
        try:
            resp = client.search(
                query=query,
                search_depth="advanced",
                topic="news",
                days=9,
                max_results=6,
                include_answer=False,
            )
        except Exception as exc:  # noqa: BLE001 - log and continue
            logger.warning("Tavily failed for query '%s': %s", query, exc)
            continue

        for item in resp.get("results", []):
            results.append({
                "title": item.get("title", "").strip(),
                "url": item.get("url", ""),
                "source": f"Tavily ({query})",
                "date": item.get("published_date"),
                "snippet": (item.get("content") or "")[:600],
            })
        logger.info("Tavily [%s]: %d result(s)", query, len(resp.get("results", [])))

    return results


# ---------------------------------------------------------------------------
# DEDUPLICATION / PERSISTENT STATE
# ---------------------------------------------------------------------------

def load_seen_urls() -> dict:
    if not SEEN_URLS_FILE.exists():
        return {}
    try:
        return json.loads(SEEN_URLS_FILE.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return {}


def save_seen_urls(seen: dict) -> None:
    cutoff = datetime.now(timezone.utc) - timedelta(days=SEEN_URLS_RETENTION_DAYS)
    pruned = {}
    for url, date_str in seen.items():
        try:
            if datetime.fromisoformat(date_str) >= cutoff:
                pruned[url] = date_str
        except ValueError:
            continue
    SEEN_URLS_FILE.write_text(json.dumps(pruned, ensure_ascii=False, indent=2), encoding="utf-8")


def dedupe_and_filter(articles: list[dict], seen_urls: dict) -> list[dict]:
    deduped, seen_local = [], set()
    for art in articles:
        url = art.get("url")
        if not url or url in seen_local or url in seen_urls:
            continue
        if not keyword_match(art.get("title", "") + " " + art.get("snippet", "")):
            continue
        seen_local.add(url)
        deduped.append(art)
    return deduped


# ---------------------------------------------------------------------------
# ENRICHMENT
# ---------------------------------------------------------------------------

def enrich_article(article: dict) -> dict:
    html = fetch_url(article["url"])
    if not html:
        article["body"] = article.get("snippet", "")
        return article
    try:
        soup = BeautifulSoup(html, "lxml")
        paragraphs = soup.find_all("p")
        text = " ".join(p.get_text(strip=True) for p in paragraphs if p.get_text(strip=True))
        article["body"] = text[:2000] if text else article.get("snippet", "")
    except Exception as exc:  # noqa: BLE001
        logger.warning("Enrichment failed for %s: %s", article["url"], exc)
        article["body"] = article.get("snippet", "")
    return article


def enrich_all(articles: list[dict]) -> list[dict]:
    enriched = []
    for art in articles:
        enriched.append(enrich_article(art))
        time.sleep(0.5)  # courtesy delay towards target servers
    return enriched


# ---------------------------------------------------------------------------
# DEEPSEEK - API CALL
# ---------------------------------------------------------------------------

DEEPSEEK_URL = "https://api.deepseek.com/chat/completions"


def call_deepseek(messages: list[dict], max_tokens: int = 4000, temperature: float = 0.3):
    """Returns (text, truncated: bool). text is None on total failure."""
    if not DEEPSEEK_API_KEY:
        logger.error("DEEPSEEK_API_KEY missing: cannot call DeepSeek")
        return None, False

    headers = {
        "Authorization": f"Bearer {DEEPSEEK_API_KEY}",
        "Content-Type": "application/json",
    }
    payload = {
        "model": "deepseek-chat",
        "messages": messages,
        "max_tokens": max_tokens,
        "temperature": temperature,
    }
    data = post_json(DEEPSEEK_URL, headers, payload)
    if not data:
        return None, False

    try:
        choice = data["choices"][0]
        text = choice["message"]["content"]
        truncated = choice.get("finish_reason") == "length"
        return text, truncated
    except (KeyError, IndexError) as exc:
        logger.error("Unexpected DeepSeek response shape: %s", exc)
        return None, False


# ---------------------------------------------------------------------------
# WEEKLY STRUCTURAL BRIEF (DeepSeek training knowledge)
# ---------------------------------------------------------------------------

WEEKLY_BRIEF_PROMPT = """You are a tax lawyer and corporate law specialist for China.
Write, in English and in Markdown, a structural background note (not recent news,
only your background knowledge) for the APAC CFO of a Western manufacturing group
operating a WFOE (Wholly Foreign-Owned Enterprise) in Shanghai and Wuxi. The note
should cover, in 500-700 words:

1. The architecture of direct and indirect taxes applicable to a WFOE (CIT, VAT,
   withholding taxes) and typical reference rates.
2. Key legal framework: Foreign Investment Law, Company Law, negative list, main
   annual compliance obligations.
3. Supervisory authorities and their respective roles (SAT, MOF, SAMR, MOFCOM,
   NDRC, local tax bureaus).
4. Recurring risk areas for a manufacturing WFOE (transfer pricing, export VAT,
   dividend repatriation, data/PIPL, labor law).

This note serves as a background reading grid; it will be combined each week with
recently analyzed news articles. Do not fabricate any recent news or precise
figures you are not sure of."""


def get_weekly_brief() -> str:
    if WEEKLY_BRIEF_CACHE_FILE.exists():
        try:
            cache = json.loads(WEEKLY_BRIEF_CACHE_FILE.read_text(encoding="utf-8"))
            cached_date = datetime.fromisoformat(cache["date"])
            if datetime.now(timezone.utc) - cached_date < timedelta(days=WEEKLY_BRIEF_MAX_AGE_DAYS):
                logger.info("Weekly structural brief: valid cache (generated on %s)", cache["date"])
                return cache["brief"]
        except (json.JSONDecodeError, KeyError, ValueError) as exc:
            logger.warning("Unreadable weekly brief cache, regenerating: %s", exc)

    logger.info("Weekly structural brief: calling DeepSeek (cache expired or missing)")
    text, truncated = call_deepseek(
        messages=[{"role": "user", "content": WEEKLY_BRIEF_PROMPT}],
        max_tokens=1600,
        temperature=0.2,
    )
    if not text:
        logger.warning("Could not generate weekly brief, using a fallback text")
        text = ("Structural brief unavailable for this run (API failure). "
                "Refer to the last known version or a primary tax source.")
    if truncated:
        logger.warning("The weekly structural brief appears to be truncated")

    WEEKLY_BRIEF_CACHE_FILE.write_text(
        json.dumps({"date": datetime.now(timezone.utc).isoformat(), "brief": text}, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    return text


# ---------------------------------------------------------------------------
# SIGNAL ANALYSIS (delimiter-based structured output)
# ---------------------------------------------------------------------------

SIGNAL_BLOCK_RE = re.compile(r"===SIGNAL_START===(.*?)===SIGNAL_END===", re.DOTALL)
EXEC_SUMMARY_RE = re.compile(r"===EXEC_SUMMARY_START===(.*?)===EXEC_SUMMARY_END===", re.DOTALL)
TOP_RISK_RE = re.compile(r"===TOP_RISK_START===(.*?)===TOP_RISK_END===", re.DOTALL)

SIGNAL_FIELD_RE = re.compile(r"^(TITLE|IMPACT|CATEGORY|SUMMARY|IMPLICATIONS|SOURCE|URL|DATE):\s*(.*)$")

VALID_IMPACTS = {"CRITICAL", "IMPORTANT", "WATCH", "INFO"}


def build_analysis_prompt(weekly_brief: str, articles: list[dict]) -> str:
    articles_block = []
    for i, art in enumerate(articles, start=1):
        articles_block.append(
            f"[Article {i}]\n"
            f"Title: {art['title']}\n"
            f"Source: {art['source']}\n"
            f"Date: {art.get('date') or 'unknown'}\n"
            f"URL: {art['url']}\n"
            f"Excerpt: {art.get('body', art.get('snippet',''))[:1200]}\n"
        )
    articles_text = "\n".join(articles_block)

    return f"""You are a tax/legal analyst for {ORG_NAME} ({ORG_CONTEXT}), scope: {REGION_LABEL}.

STRUCTURAL CONTEXT (background reading grid):
{weekly_brief}

PRIORITY ENTITIES/TOPICS UNDER WATCH:
{chr(10).join('- ' + e for e in ENTITIES_TO_WATCH)}

RECENT ARTICLES TO ANALYZE:
{articles_text}

INSTRUCTIONS:
For each article that is GENUINELY relevant to a manufacturing WFOE in China
(ignore off-topic or overly generic articles), produce a block in the EXACT
following format (nothing before or after the delimiters):

===SIGNAL_START===
TITLE: <short, clear title in English>
IMPACT: <CRITICAL|IMPORTANT|WATCH|INFO>
CATEGORY: <Tax|Corporate Law|Customs|Labor|Compliance|Other>
SUMMARY: <2-3 factual sentences in English>
IMPLICATIONS: <concrete impact for a WFOE in Shanghai/Wuxi and for an APAC CFO, in English>
SOURCE: <source name>
URL: <original url>
DATE: <date if known, otherwise "unknown">
===SIGNAL_END===

Impact scale:
- CRITICAL: binding regulatory/tax change with short-term effect, legal deadline, or direct non-compliance/sanction risk.
- IMPORTANT: significant development requiring action or close monitoring in the coming months.
- WATCH: weak signal or reform proposal to monitor, no immediate action required.
- INFO: useful contextual information, no action required.

Then, add EXACTLY one executive summary block:
===EXEC_SUMMARY_START===
<4-6 sentences in English summarizing the situation for the week>
===EXEC_SUMMARY_END===

Then EXACTLY one top risk block:
===TOP_RISK_START===
<2-4 sentences identifying the single most important risk or watch point>
===TOP_RISK_END===

If no article is relevant, produce only the EXEC_SUMMARY and TOP_RISK blocks
stating that no significant signal was detected."""


def parse_signals(raw_text: str) -> tuple[list[dict], str, str, bool]:
    """Returns (signals, executive_summary, top_risk, truncation_detected)."""
    signals = []
    for block in SIGNAL_BLOCK_RE.findall(raw_text):
        fields = {}
        for line in block.strip().splitlines():
            match = SIGNAL_FIELD_RE.match(line.strip())
            if match:
                fields[match.group(1)] = match.group(2).strip()
        if fields.get("TITLE") and fields.get("IMPACT") in VALID_IMPACTS:
            signals.append(fields)
        elif fields.get("TITLE"):
            fields["IMPACT"] = "INFO"
            signals.append(fields)

    exec_summary_match = EXEC_SUMMARY_RE.search(raw_text)
    top_risk_match = TOP_RISK_RE.search(raw_text)
    exec_summary = exec_summary_match.group(1).strip() if exec_summary_match else ""
    top_risk = top_risk_match.group(1).strip() if top_risk_match else ""

    # Truncation detection: a START delimiter without a matching END, or a
    # last block clearly cut off mid-field.
    truncation_suspected = raw_text.count("===SIGNAL_START===") > raw_text.count("===SIGNAL_END===")
    if not exec_summary_match and "===EXEC_SUMMARY_START===" in raw_text:
        truncation_suspected = True
    if not top_risk_match and "===TOP_RISK_START===" in raw_text:
        truncation_suspected = True

    return signals, exec_summary, top_risk, truncation_suspected


def analyze_articles(weekly_brief: str, articles: list[dict]):
    if not articles:
        return [], "No relevant article detected this week.", "No particular risk identified.", False

    prompt = build_analysis_prompt(weekly_brief, articles)
    raw_text, api_truncated = call_deepseek(
        messages=[{"role": "user", "content": prompt}],
        max_tokens=4000,
        temperature=0.3,
    )
    if not raw_text:
        logger.error("DeepSeek analysis unavailable: generating a degraded report from raw articles")
        fallback_signals = [{
            "TITLE": art["title"],
            "IMPACT": "WATCH",
            "CATEGORY": "Unclassified (AI analysis unavailable)",
            "SUMMARY": (art.get("body") or art.get("snippet") or "")[:300],
            "IMPLICATIONS": "To be assessed manually (DeepSeek call failed).",
            "SOURCE": art["source"],
            "URL": art["url"],
            "DATE": art.get("date") or "unknown",
        } for art in articles]
        return fallback_signals, "AI analysis unavailable for this run.", "N/A", False

    signals, exec_summary, top_risk, parse_truncated = parse_signals(raw_text)
    truncated = api_truncated or parse_truncated
    if truncated:
        logger.warning("Truncation detected in DeepSeek response: some signals may be missing")
    return signals, exec_summary, top_risk, truncated


# ---------------------------------------------------------------------------
# HTML REPORT
# ---------------------------------------------------------------------------

IMPACT_ORDER = ["CRITICAL", "IMPORTANT", "WATCH", "INFO"]
IMPACT_STYLE = {
    "CRITICAL": {"color": "#b91c1c", "bg": "#fee2e2", "label": "CRITICAL"},
    "IMPORTANT": {"color": "#c2410c", "bg": "#ffedd5", "label": "IMPORTANT"},
    "WATCH": {"color": "#a16207", "bg": "#fef9c3", "label": "WATCH"},
    "INFO": {"color": "#1d4ed8", "bg": "#dbeafe", "label": "INFO"},
}

HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>China Tax & Corporate Law Watch - {run_date}</title>
<style>
  body {{ font-family: -apple-system, Segoe UI, Arial, sans-serif; background:#f3f4f6; color:#111827; margin:0; padding:0; }}
  .container {{ max-width: 900px; margin: 0 auto; padding: 24px; }}
  header {{ background:#111827; color:#fff; padding: 28px 24px; }}
  header h1 {{ margin:0 0 6px 0; font-size: 22px; }}
  header p {{ margin:0; color:#d1d5db; font-size: 14px; }}
  .card {{ background:#fff; border-radius: 10px; padding: 20px; margin-bottom: 18px; box-shadow: 0 1px 3px rgba(0,0,0,0.08); }}
  .badge {{ display:inline-block; padding: 3px 10px; border-radius: 999px; font-size: 12px; font-weight:600; letter-spacing:.03em; }}
  .signal {{ border-left: 5px solid #9ca3af; padding: 14px 18px; margin-bottom: 14px; border-radius: 6px; }}
  .signal h3 {{ margin: 4px 0 8px 0; font-size: 16px; }}
  .signal .meta {{ font-size: 12px; color:#6b7280; margin-bottom: 8px; }}
  .signal p {{ margin: 6px 0; font-size: 14px; line-height: 1.5; }}
  .signal a {{ color:#1d4ed8; text-decoration:none; }}
  .signal a:hover {{ text-decoration:underline; }}
  h2.section-title {{ font-size: 15px; text-transform: uppercase; letter-spacing:.04em; color:#374151; margin: 28px 0 12px 0; }}
  .top-risk {{ background:#fff7ed; border:1px solid #fdba74; border-radius: 10px; padding: 18px; }}
  .brief {{ font-size: 13px; color:#374151; }}
  .footer-note {{ font-size: 12px; color:#9ca3af; margin-top: 24px; }}
  .truncation-warning {{ background:#fee2e2; color:#991b1b; padding: 10px 16px; border-radius: 8px; font-size: 13px; margin-bottom: 16px; }}
</style>
</head>
<body>
<header>
  <h1>China Tax & Corporate Law Watch</h1>
  <p>{org_name} - {org_context} | Scope: {region_label}</p>
  <p>Report generated on {run_date} UTC</p>
</header>
<div class="container">

  {truncation_html}

  <div class="card">
    <h2 class="section-title">Executive summary</h2>
    <p>{exec_summary}</p>
  </div>

  <div class="top-risk">
    <h2 class="section-title" style="margin-top:0;">Top risk to watch</h2>
    <p>{top_risk}</p>
  </div>

  {signals_html}

  <div class="card">
    <h2 class="section-title">Structural brief (background context, updated weekly)</h2>
    <div class="brief">{weekly_brief_html}</div>
  </div>

  <p class="footer-note">
    Automatically generated by china_tax_law_agent.py &middot;
    {nb_signals} signal(s) detected across {nb_articles} article(s) analyzed &middot;
    Sources: direct scraping + Tavily search.
  </p>
</div>
</body>
</html>"""

SIGNAL_TEMPLATE = """<div class="signal" style="border-left-color:{color}; background:{bg}22;">
  <span class="badge" style="background:{bg}; color:{color};">{impact_label}</span>
  <span class="badge" style="background:#e5e7eb; color:#374151;">{category}</span>
  <h3>{title}</h3>
  <div class="meta">{source} &middot; {date}</div>
  <p>{summary}</p>
  <p><strong>Implication:</strong> {implications}</p>
  <p><a href="{url}" target="_blank" rel="noopener">View original source &rarr;</a></p>
</div>"""


def html_escape(text: str) -> str:
    if not text:
        return ""
    return (
        text.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
    )


def generate_html_report(signals: list[dict], exec_summary: str, top_risk: str,
                          weekly_brief: str, nb_articles: int, truncated: bool) -> str:
    grouped = {impact: [] for impact in IMPACT_ORDER}
    for sig in signals:
        grouped.setdefault(sig.get("IMPACT", "INFO"), []).append(sig)

    signals_html_parts = []
    for impact in IMPACT_ORDER:
        items = grouped.get(impact, [])
        if not items:
            continue
        style = IMPACT_STYLE[impact]
        signals_html_parts.append(f'<h2 class="section-title">{style["label"]} ({len(items)})</h2>')
        for sig in items:
            signals_html_parts.append(SIGNAL_TEMPLATE.format(
                color=style["color"],
                bg=style["bg"],
                impact_label=style["label"],
                category=html_escape(sig.get("CATEGORY", "Other")),
                title=html_escape(sig.get("TITLE", "")),
                source=html_escape(sig.get("SOURCE", "")),
                date=html_escape(sig.get("DATE", "unknown")),
                summary=html_escape(sig.get("SUMMARY", "")),
                implications=html_escape(sig.get("IMPLICATIONS", "")),
                url=sig.get("URL", "#"),
            ))

    if not signals_html_parts:
        signals_html_parts.append('<div class="card"><p>No significant signal detected this week.</p></div>')

    truncation_html = ""
    if truncated:
        truncation_html = (
            '<div class="truncation-warning">Warning: the AI analysis response appears to have '
            "been truncated. Some signals or sections may be incomplete.</div>"
        )

    return HTML_TEMPLATE.format(
        run_date=datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M"),
        org_name=ORG_NAME,
        org_context=ORG_CONTEXT,
        region_label=REGION_LABEL,
        truncation_html=truncation_html,
        exec_summary=html_escape(exec_summary) or "No summary available.",
        top_risk=html_escape(top_risk) or "No particular risk identified.",
        signals_html="\n".join(signals_html_parts),
        weekly_brief_html=markdown_lib.markdown(weekly_brief),
        nb_signals=len(signals),
        nb_articles=nb_articles,
    )


# ---------------------------------------------------------------------------
# ORCHESTRATION
# ---------------------------------------------------------------------------

def main():
    logger.info("=== Starting china_tax_law_agent.py (TEST_MODE=%s) ===", TEST_MODE)

    if not DEEPSEEK_API_KEY:
        logger.error("DEEPSEEK_API_KEY missing: the report will be degraded (no AI analysis).")
    if not TAVILY_API_KEY:
        logger.warning("TAVILY_API_KEY missing: Tavily search will be skipped.")

    weekly_brief = get_weekly_brief()

    scraped = scrape_all_static_sources()
    tavily_results = tavily_search_all()
    logger.info("Raw total: %d scraped article(s), %d Tavily result(s)", len(scraped), len(tavily_results))

    seen_urls = load_seen_urls()
    candidates = dedupe_and_filter(scraped + tavily_results, seen_urls)
    logger.info("%d article(s) retained after keyword filtering and deduplication", len(candidates))

    if TEST_MODE:
        candidates = candidates[:8]

    enriched = enrich_all(candidates)

    signals, exec_summary, top_risk, truncated = analyze_articles(weekly_brief, enriched)

    html_report = generate_html_report(
        signals=signals,
        exec_summary=exec_summary,
        top_risk=top_risk,
        weekly_brief=weekly_brief,
        nb_articles=len(enriched),
        truncated=truncated,
    )

    run_date_str = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    report_path = REPORTS_DIR / f"china_tax_law_report_{run_date_str}.html"
    report_path.write_text(html_report, encoding="utf-8")
    (REPORTS_DIR / "latest.html").write_text(html_report, encoding="utf-8")
    logger.info("Report written: %s", report_path)

    now_iso = datetime.now(timezone.utc).isoformat()
    for art in enriched:
        seen_urls[art["url"]] = now_iso
    save_seen_urls(seen_urls)

    logger.info("=== Done: %d signal(s) across %d article(s) analyzed ===", len(signals), len(enriched))


if __name__ == "__main__":
    main()
