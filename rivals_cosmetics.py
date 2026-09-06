#!/usr/bin/env python3
"""
Marvel Rivals Cosmetic Equity
=============================

One file. It collects Marvel Rivals cosmetic and match data from four public
sources, keeps them in a local SQLite database, and renders a dashboard that
compares how many skins each hero gets against how much people actually play
them.

    python3 rivals_cosmetics.py                 # collect if needed, then serve
    python3 rivals_cosmetics.py --collect       # refresh the database, exit
    python3 rivals_cosmetics.py --build         # write a shareable index.html
    python3 rivals_cosmetics.py --init-repo DIR # scaffold auto-updating site

SOURCES
    rivalskins.com      every costume: rarity, season, release date, source,
                        bundle, price in Units, in-game item id, chroma links,
                        and each hero's role (read from the site's own role
                        menu, so heroes added later classify themselves)
    rivalsmeta.com      per-skin usage share and match counts; per-hero win,
                        pick and ban rate
    marvelrivals.fandom.com
                        character gender, from the structured field in each
                        hero's infobox

WHAT IS MEASURED, AND WHAT IS ESTIMATED
    Skin counts, rarity, chromas, prices, release dates and pick rates are
    observed values.  Money is not: nobody publishes real revenue. The spend
    figures here are modelled -- skin price multiplied by the number of
    matches that skin is seen in -- and are labelled as estimates throughout.
    They are good for ranking heroes against each other, not for dollars.

Dependencies: requests, beautifulsoup4, lxml
    pip install requests beautifulsoup4 lxml
"""

import argparse
import json
import re
import sqlite3
import sys
import threading
import time
import webbrowser
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

try:
    import requests
    from bs4 import BeautifulSoup
except ImportError:
    sys.exit("Missing dependencies. Run:\n\n    pip install requests beautifulsoup4 lxml\n")

HERE = Path(__file__).resolve().parent
DB_PATH = HERE / "rivals_cosmetics.sqlite3"
PORT_DEFAULT = 8765

RS = "https://rivalskins.com"
RM = "https://rivalsmeta.com"

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36")

HERO_URL_RE = re.compile(r"^https?://rivalskins\.com/hero/([\w\-]+)/?$")
ITEM_URL_RE = re.compile(r"^https?://rivalskins\.com/item/(\d+)/([\w\-]+)/?$")
RARITY_RE = re.compile(r"\b(Default|Rare|Epic|Legendary)\s+Rarity Icon\b", re.I)
SEASON_RE = re.compile(r"Introduced in:\s*Season\s*([\d.]+)", re.I)
DATE_RE = re.compile(r"Release Date:\s*([A-Za-z]+ \d{1,2},\s*\d{4})", re.I)
SKIN_IMG_RE = re.compile(r"img_skin_(\d+)\.png")
HERO_IMG_RE = re.compile(r"img_selecthero_(\d+)\.png")
ROLE_NAMES = {"Vanguard", "Duelist", "Strategist", "Triple-role"}

RIVALS_WIKI_API = "https://marvelrivals.fandom.com/api.php"

# Gender comes from the Marvel Rivals wiki, which carries a structured
# "gender" field in every hero infobox. That field was checked against the
# whole 53-hero roster and agreed on every one, so new heroes classify
# themselves with no edit here.
#
# The general Marvel Database is deliberately NOT used: searching it by
# codename lands on the wrong character (it reports Black Cat as male) and
# "Phoenix" resolves to the Phoenix Force rather than Jean Grey. Skin lore
# text is not used either -- the quotes are in-character dialogue about
# whoever the hero is talking about, which reads Elsa Bloodstone as male.
#
# Overrides are for calls the wiki cannot make for us:
#   Cloak & Dagger is one hero slot holding two people, and Loki is
#   genderfluid in the source material. Both are recorded as "Male/Female"
#   so they group together.
GENDER_OVERRIDES = {
    "cloak-and-dagger": "Male/Female",
    "loki": "Male/Female",
}

GENDER_FIELD_RE = re.compile(r"\|\s*gender\s*=\s*([^\n|]+)", re.I)
GENDER_WORD_RE = re.compile(r"\b(Male|Female|Genderfluid|Non[- ]Binary|Agender)\b", re.I)


def wiki_gender(session, hero_name):
    """Read the gender field from the hero's Marvel Rivals wiki infobox."""
    for title in (hero_name, hero_name.replace("&", "and")):
        try:
            data = session.get(RIVALS_WIKI_API, timeout=30, params={
                "action": "parse", "page": title, "prop": "wikitext",
                "redirects": 1, "format": "json"}).json()
        except Exception:
            continue
        if "error" in data:
            continue
        m = GENDER_FIELD_RE.search(data.get("parse", {})
                                       .get("wikitext", {}).get("*", ""))
        if not m:
            continue
        # The value may be a bare word or an icon such as [[File:Male.svg...]],
        # and a dual-gender hero carries one icon per person.
        found = [w.title().replace(" ", "-") for w in GENDER_WORD_RE.findall(m.group(1))]
        seen = list(dict.fromkeys(found))
        if not seen:
            continue
        if {"Male", "Female"} <= set(seen):
            return "Male/Female"
        return seen[0]
    return None


SCHEMA = """
CREATE TABLE IF NOT EXISTS heroes (
    slug TEXT PRIMARY KEY, name TEXT NOT NULL, role TEXT, gender TEXT,
    game_hero_id TEXT, url TEXT,
    win_rate REAL, pick_rate REAL, ban_rate REAL, matches INTEGER, tier TEXT,
    scraped_at TEXT
);
CREATE TABLE IF NOT EXISTS skins (
    item_id INTEGER PRIMARY KEY, hero_slug TEXT NOT NULL, game_id TEXT,
    name TEXT, rarity TEXT, season TEXT, release_date TEXT, source TEXT,
    bundle TEXT, first_appears TEXT, price INTEGER, currency TEXT,
    is_chroma INTEGER DEFAULT 0, usage_share REAL, usage_matches INTEGER,
    url TEXT, scraped_at TEXT,
    FOREIGN KEY (hero_slug) REFERENCES heroes(slug)
);
CREATE INDEX IF NOT EXISTS idx_skins_hero ON skins(hero_slug);
CREATE INDEX IF NOT EXISTS idx_skins_game ON skins(game_id);
CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT);
"""


def now_iso():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def norm_name(s):
    return re.sub(r"[^a-z0-9]", "", (s or "").lower().replace("&", "and"))


# ===========================================================================
# Progress reporting -- shared by the CLI and the browser's refresh button
# ===========================================================================

class Progress:
    def __init__(self):
        self.lock = threading.Lock()
        self.lines = []
        self.running = False
        self.done = False
        self.error = None

    def say(self, msg):
        stamp = datetime.now().strftime("%H:%M:%S")
        line = f"[{stamp}] {msg}"
        with self.lock:
            self.lines.append(line)
            self.lines = self.lines[-400:]
        print(line, flush=True)

    def snapshot(self):
        with self.lock:
            return {"running": self.running, "done": self.done,
                    "error": self.error, "lines": self.lines[-200:]}


PROGRESS = Progress()


# ===========================================================================
# HTTP helper
# ===========================================================================

def make_session():
    s = requests.Session()
    s.headers.update({"User-Agent": UA, "Accept-Language": "en-US,en;q=0.9"})
    return s


def fetch(session, url, delay=0.35, tries=3):
    last = None
    for attempt in range(tries):
        try:
            r = session.get(url, timeout=45)
            r.raise_for_status()
            if delay:
                time.sleep(delay)
            return r.text
        except Exception as exc:
            last = exc
            time.sleep(1.5 * (attempt + 1))
    raise last


# ===========================================================================
# rivalskins.com -- the cosmetic catalogue
# ===========================================================================

def scrape_roster(session):
    """Heroes and their roles, read from the site's own role menu."""
    soup = BeautifulSoup(fetch(session, f"{RS}/heroes/"), "lxml")
    roster = {}
    for group in soup.select("li.role-group"):
        # Single-role groups name the role only in the icon's alt text; the
        # multi-role group carries a literal <span> label and several icons.
        span = group.select_one(".role-header span")
        icons = [i.get("alt", "").strip()
                 for i in group.select(".role-header img.submenu-role-icon")]
        icons = [i for i in icons if i in ROLE_NAMES]
        if span and span.get_text(strip=True) in ROLE_NAMES:
            role = span.get_text(strip=True)
        elif len(set(icons)) == 1:
            role = icons[0]
        elif len(set(icons)) > 1:
            role = "Triple-role"
        else:
            continue
        lists = group.select("ul.role-heroes")
        sibling = group.find_next_sibling("ul", class_="role-heroes")
        if sibling is not None:
            lists = list(lists) + [sibling]
        for ul in lists:
            for a in ul.select("a[href]"):
                m = HERO_URL_RE.match(a["href"].strip())
                if m and a.get_text(strip=True):
                    roster.setdefault(m.group(1), {
                        "slug": m.group(1), "name": a.get_text(strip=True),
                        "role": role, "url": a["href"].strip()})
    # Anything the menu missed still gets picked up, just without a role.
    for a in soup.select("a[href]"):
        m = HERO_URL_RE.match(a["href"].strip())
        if m and m.group(1) not in roster and a.get_text(strip=True):
            roster[m.group(1)] = {"slug": m.group(1), "name": a.get_text(strip=True),
                                  "role": None, "url": a["href"].strip()}
    return roster


def scrape_hero_item_links(session, hero_url):
    soup = BeautifulSoup(fetch(session, hero_url), "lxml")
    links = {}
    for a in soup.select("a[href]"):
        m = ITEM_URL_RE.match(a["href"].strip())
        if m and "-costume-" in m.group(2):
            links[int(m.group(1))] = a["href"].strip()
    return links


def parse_item_page(html, item_id, hero_slug, url):
    soup = BeautifulSoup(html, "lxml")
    for tag in soup(["script", "style", "noscript"]):
        tag.decompose()
    text = soup.get_text("\n")

    h1 = soup.find("h1")
    name = h1.get_text(strip=True) if h1 else None

    rarity = None
    img = soup.find("img", alt=RARITY_RE)
    if img:
        rarity = RARITY_RE.search(img["alt"]).group(1).title()
    else:
        m = RARITY_RE.search(text)
        if m:
            rarity = m.group(1).title()

    m = SEASON_RE.search(text)
    season = f"Season {m.group(1)}" if m else None

    m = DATE_RE.search(text)
    raw_date = m.group(1) if m else None
    release_date = None
    if raw_date:
        try:
            release_date = datetime.strptime(raw_date, "%B %d, %Y").date().isoformat()
        except ValueError:
            pass

    price = None
    node = soup.select_one(".item-price .price-normal")
    if node:
        digits = re.sub(r"[^\d]", "", node.get_text())
        price = int(digits) if digits else None

    currency = None
    icon = soup.select_one(".item-price .price-icon img")
    if icon and icon.get("src"):
        m = re.search(r"currency_(\w+?)\.(?:png|webp|jpg)", icon["src"])
        if m:
            currency = m.group(1)

    # The in-game id. A "ps" prefix marks a recolor (chroma) of a base skin.
    game_id, is_chroma = None, 0
    cell = soup.select_one("tr.item-details-marvel-id td")
    if cell:
        parts = cell.get_text(strip=True).split()
        m = re.match(r"^(ps)?(\d+)$", parts[0]) if parts else None
        if m:
            is_chroma = 1 if m.group(1) else 0
            game_id = m.group(2)

    source = None
    for tr in soup.select("table.item-details-table tr"):
        th = tr.find("th")
        if th and th.get_text(strip=True).lower().startswith("source"):
            td = tr.find("td")
            source = (td.get_text(strip=True) or None) if td else None
            break

    bundle = None
    links = soup.select(".bundle-section .bundle-link a")
    if links:
        bundle = "; ".join(a.get_text(strip=True) for a in links)

    first_appears = None
    node = soup.select_one(".item-appears-in")
    if node:
        first_appears = re.sub(r"^First Appears in\s*", "", node.get_text(strip=True)) or None

    return dict(item_id=item_id, hero_slug=hero_slug, game_id=game_id, name=name,
                rarity=rarity, season=season, release_date=release_date,
                source=source, bundle=bundle, first_appears=first_appears,
                price=price, currency=currency, is_chroma=is_chroma, url=url)


# ===========================================================================
# rivalsmeta.com -- what people actually play and wear
# ===========================================================================

def scrape_skin_usage(session):
    """Per-skin share of its hero's matches, keyed by in-game skin id."""
    soup = BeautifulSoup(fetch(session, f"{RM}/skins", delay=0.8), "lxml")
    rows, hero_name, hero_id = [], None, None
    for node in soup.select("h2, div.skin"):
        if node.name == "h2":
            hero_name = re.sub(r"\s*Skins$", "", node.get_text(strip=True))
            img = node.find_previous("img", src=HERO_IMG_RE)
            hero_id = HERO_IMG_RE.search(img["src"]).group(1) if img else None
            continue
        img = node.select_one("img[src*=img_skin_]")
        if not img:
            continue
        text = node.get_text(" ", strip=True)
        pct = re.search(r"([\d.]+)%", text)
        seen = re.search(r"seen in ([\d,]+) matches", text)
        rows.append(dict(
            skin_id=SKIN_IMG_RE.search(img["src"]).group(1),
            hero_name=hero_name, hero_id=hero_id,
            share=float(pct.group(1)) if pct else None,
            matches=int(seen.group(1).replace(",", "")) if seen else None))
    return rows


def scrape_hero_rates(session):
    soup = BeautifulSoup(fetch(session, f"{RM}/characters", delay=0.8), "lxml")
    table = soup.find("table")
    rows = []
    if not table:
        return rows

    def num(s):
        s = (s or "").replace("%", "").replace(",", "").strip()
        try:
            return float(s)
        except ValueError:
            return None

    for tr in table.select("tr"):
        cells = [td.get_text(" ", strip=True) for td in tr.find_all("td")]
        if len(cells) < 7:
            continue
        rows.append(dict(name=cells[1], tier=cells[2] or None,
                         win_rate=num(cells[3]), pick_rate=num(cells[4]),
                         ban_rate=num(cells[5]), matches=num(cells[6])))
    return rows


def merge_role_variants(hero_rows, usage_rows):
    """rivalsmeta lists Deadpool once per role. Fold those back into one hero.

    Rates are averaged in proportion to matches; matches and pick rates are
    summed, because the three entries are three different hero slots that a
    player can pick."""
    base = {}
    for row in hero_rows:
        key = norm_name(re.sub(r"\s*\(.*\)\s*$", "", row["name"]))
        base.setdefault(key, []).append(row)

    merged = []
    for key, group in base.items():
        if len(group) == 1:
            merged.append(group[0])
            continue
        total = sum(g["matches"] or 0 for g in group) or 1

        def weighted(field):
            vals = [(g[field] or 0) * (g["matches"] or 0) for g in group]
            return round(sum(vals) / total, 3)

        merged.append(dict(
            name=re.sub(r"\s*\(.*\)\s*$", "", group[0]["name"]),
            tier=group[0]["tier"],
            win_rate=weighted("win_rate"),
            pick_rate=round(sum(g["pick_rate"] or 0 for g in group), 3),
            ban_rate=weighted("ban_rate"),
            matches=sum(g["matches"] or 0 for g in group)))

    # Same skin id can appear under each role variant; add the match counts.
    by_skin = {}
    for row in usage_rows:
        sid = row["skin_id"]
        if sid in by_skin:
            prev = by_skin[sid]
            prev["matches"] = (prev["matches"] or 0) + (row["matches"] or 0)
            prev["_dupes"] = prev.get("_dupes", 1) + 1
            prev["share"] = round(((prev["share"] or 0) * (prev["_dupes"] - 1)
                                   + (row["share"] or 0)) / prev["_dupes"], 3)
        else:
            by_skin[sid] = dict(row)
    return merged, list(by_skin.values())



# ===========================================================================
# Database
# ===========================================================================

def connect():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    conn.executescript(SCHEMA)
    return conn


def collect(full=False, skip_gender=False):
    """Refresh everything. Incremental by default: item pages already stored
    are not re-fetched, which makes a routine refresh take about a minute
    instead of about eight."""
    PROGRESS.running, PROGRESS.done, PROGRESS.error = True, False, None
    session = make_session()
    conn = connect()
    stamp = now_iso()
    try:
        PROGRESS.say("Reading hero roster and roles from rivalskins.com")
        roster = scrape_roster(session)
        PROGRESS.say(f"  {len(roster)} heroes")

        known = {r["item_id"] for r in conn.execute("SELECT item_id FROM skins")}
        PROGRESS.say("Listing costumes for each hero")
        wanted = {}
        for i, (slug, hero) in enumerate(sorted(roster.items()), 1):
            for item_id, url in scrape_hero_item_links(session, hero["url"]).items():
                wanted[item_id] = (slug, url)
            if i % 10 == 0 or i == len(roster):
                PROGRESS.say(f"  {i}/{len(roster)} heroes, {len(wanted)} costumes found")

        todo = sorted(wanted) if full else sorted(set(wanted) - known)
        PROGRESS.say(f"Fetching {len(todo)} costume pages"
                     f"{' (full refresh)' if full else ' (new since last run)'}")
        for n, item_id in enumerate(todo, 1):
            slug, url = wanted[item_id]
            try:
                row = parse_item_page(fetch(session, url), item_id, slug, url)
                conn.execute("""
                    INSERT INTO skins (item_id, hero_slug, game_id, name, rarity, season,
                        release_date, source, bundle, first_appears, price, currency,
                        is_chroma, url, scraped_at)
                    VALUES (:item_id,:hero_slug,:game_id,:name,:rarity,:season,
                        :release_date,:source,:bundle,:first_appears,:price,:currency,
                        :is_chroma,:url,:scraped_at)
                    ON CONFLICT(item_id) DO UPDATE SET
                        hero_slug=excluded.hero_slug, game_id=excluded.game_id,
                        name=excluded.name, rarity=excluded.rarity, season=excluded.season,
                        release_date=excluded.release_date, source=excluded.source,
                        bundle=excluded.bundle, first_appears=excluded.first_appears,
                        price=excluded.price, currency=excluded.currency,
                        is_chroma=excluded.is_chroma, url=excluded.url,
                        scraped_at=excluded.scraped_at
                """, {**row, "scraped_at": stamp})
            except Exception as exc:
                PROGRESS.say(f"  skipped item {item_id}: {type(exc).__name__}")
            if n % 50 == 0:
                conn.commit()
                PROGRESS.say(f"  {n}/{len(todo)} costume pages")
        conn.commit()

        PROGRESS.say("Reading play rates and skin usage from rivalsmeta.com")
        try:
            usage = scrape_skin_usage(session)
            rates = scrape_hero_rates(session)
            rates, usage = merge_role_variants(rates, usage)
            PROGRESS.say(f"  {len(rates)} heroes rated, {len(usage)} skins with usage")
        except Exception as exc:
            usage, rates = [], []
            PROGRESS.say(f"  rivalsmeta.com unavailable ({type(exc).__name__});"
                         " keeping previous play data")

        by_name = {norm_name(h["name"]): h for h in roster.values()}
        hero_game_id = {}
        for row in usage:
            hero = by_name.get(norm_name(re.sub(r"\s*\(.*\)\s*$", "", row["hero_name"] or "")))
            if hero and row["hero_id"]:
                hero_game_id[hero["slug"]] = row["hero_id"]

        rate_by_slug = {}
        unmatched = []
        for row in rates:
            hero = by_name.get(norm_name(row["name"]))
            if hero:
                rate_by_slug[hero["slug"]] = row
            else:
                unmatched.append(row["name"])
        if unmatched:
            PROGRESS.say(f"  no catalogue match for: {', '.join(unmatched)}")

        PROGRESS.say("Writing heroes")
        unknown_gender = []
        for slug, hero in sorted(roster.items()):
            existing = conn.execute(
                "SELECT gender, win_rate, pick_rate, ban_rate, matches, tier"
                " FROM heroes WHERE slug=?", (slug,)).fetchone()
            gender = GENDER_OVERRIDES.get(slug)
            if not gender:
                gender = existing["gender"] if existing else None
                if gender in (None, "", "Unknown") and not skip_gender:
                    gender = wiki_gender(session, hero["name"])
                if not gender:
                    gender = "Unknown"
                    unknown_gender.append(hero["name"])
            rate = rate_by_slug.get(slug)
            if rate is None and existing is not None:
                rate = {k: existing[k] for k in
                        ("win_rate", "pick_rate", "ban_rate", "matches", "tier")}
            rate = rate or {}
            conn.execute("""
                INSERT INTO heroes (slug, name, role, gender, game_hero_id, url,
                    win_rate, pick_rate, ban_rate, matches, tier, scraped_at)
                VALUES (?,?,?,?,?,?,?,?,?,?,?,?)
                ON CONFLICT(slug) DO UPDATE SET
                    name=excluded.name, role=excluded.role, gender=excluded.gender,
                    game_hero_id=excluded.game_hero_id, url=excluded.url,
                    win_rate=excluded.win_rate, pick_rate=excluded.pick_rate,
                    ban_rate=excluded.ban_rate, matches=excluded.matches,
                    tier=excluded.tier, scraped_at=excluded.scraped_at
            """, (slug, hero["name"], hero["role"], gender,
                  hero_game_id.get(slug), hero["url"],
                  rate.get("win_rate"), rate.get("pick_rate"), rate.get("ban_rate"),
                  rate.get("matches"), rate.get("tier"), stamp))
        conn.commit()
        if unknown_gender:
            PROGRESS.say("  gender not resolved for: " + ", ".join(unknown_gender)
                         + " -- add them to GENDER_BY_SLUG")

        if usage:
            PROGRESS.say("Matching skin usage onto the catalogue")
            usage_by_id = {u["skin_id"]: u for u in usage}
            conn.execute("UPDATE skins SET usage_share=NULL, usage_matches=NULL")
            hits = 0
            for row in conn.execute("SELECT item_id, game_id FROM skins").fetchall():
                u = usage_by_id.get(row["game_id"])
                if u:
                    conn.execute("UPDATE skins SET usage_share=?, usage_matches=?"
                                 " WHERE item_id=?",
                                 (u["share"], u["matches"], row["item_id"]))
                    hits += 1
            conn.commit()
            PROGRESS.say(f"  {hits} costumes matched to usage data")

        conn.execute("INSERT INTO meta (key,value) VALUES ('last_collect',?)"
                     " ON CONFLICT(key) DO UPDATE SET value=excluded.value", (stamp,))
        conn.commit()
        PROGRESS.say("Collection complete")
        PROGRESS.done = True
    except Exception as exc:
        PROGRESS.error = f"{type(exc).__name__}: {exc}"
        PROGRESS.say(f"Stopped: {PROGRESS.error}")
    finally:
        PROGRESS.running = False
        conn.close()


# ===========================================================================
# Shaping the data for the page
# ===========================================================================

def build_payload():
    if not DB_PATH.exists():
        return {"heroes": [], "skins": [], "collected_at": None}
    conn = connect()
    heroes = [dict(r) for r in conn.execute("""
        SELECT slug, name, role, gender, win_rate, pick_rate, ban_rate,
               matches, tier FROM heroes ORDER BY name""")]
    skins = [dict(r) for r in conn.execute("""
        SELECT item_id, hero_slug, name, rarity, season, release_date, source,
               bundle, price, currency, is_chroma, usage_share, usage_matches, url
        FROM skins ORDER BY release_date, item_id""")]
    row = conn.execute("SELECT value FROM meta WHERE key='last_collect'").fetchone()
    conn.close()
    for s in skins:
        s["is_chroma"] = bool(s["is_chroma"])
    return {"heroes": heroes, "skins": skins,
            "collected_at": row["value"] if row else None}


# ===========================================================================
# Web server
# ===========================================================================

class Handler(BaseHTTPRequestHandler):
    def log_message(self, *_):
        pass

    def _send(self, body, ctype):
        raw = body.encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)

    def do_GET(self):
        if self.path in ("/", "/index.html"):
            self._send(render_page(embed=None), "text/html; charset=utf-8")
        elif self.path == "/api/data":
            self._send(json.dumps(build_payload()), "application/json")
        elif self.path == "/api/status":
            self._send(json.dumps(PROGRESS.snapshot()), "application/json")
        else:
            self._send(json.dumps({"error": "not found"}), "application/json")

    def do_POST(self):
        if self.path.startswith("/api/collect"):
            if PROGRESS.running:
                self._send(json.dumps({"started": False, "reason": "already running"}),
                           "application/json")
                return
            full = "full=1" in self.path
            threading.Thread(target=collect, kwargs={"full": full}, daemon=True).start()
            self._send(json.dumps({"started": True}), "application/json")
        else:
            self._send(json.dumps({"error": "not found"}), "application/json")


def render_page(embed=None):
    """embed=None -> page fetches /api/data. embed=payload -> fully standalone."""
    if embed is None:
        boot = "const EMBEDDED = null;"
    else:
        blob = json.dumps(embed).replace("</", "<\\/")
        boot = f"const EMBEDDED = {blob};"
    return PAGE_HTML.replace("/*__BOOTSTRAP__*/", boot)


# ===========================================================================
# GitHub Pages scaffold -- the "share it with anyone" path
# ===========================================================================

WORKFLOW = """name: Refresh Marvel Rivals data
on:
  schedule:
    - cron: '0 7 * * *'     # every day at 07:00 UTC
  workflow_dispatch:         # or run it by hand from the Actions tab
permissions:
  contents: write
  pages: write
  id-token: write
concurrency:
  group: pages
  cancel-in-progress: false
jobs:
  refresh:
    runs-on: ubuntu-latest
    environment:
      name: github-pages
      url: ${{ steps.deployment.outputs.page_url }}
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with:
          python-version: '3.12'
      - run: pip install requests beautifulsoup4 lxml
      # If a source is temporarily down, keep going and publish the data we
      # already have rather than taking the site offline for the day.
      - name: Collect fresh data
        continue-on-error: true
        run: python rivals_cosmetics.py --collect
      - name: Build the page
        run: python rivals_cosmetics.py --build --out site/index.html
      - name: Save the refreshed database
        run: |
          git config user.name  "github-actions"
          git config user.email "github-actions@users.noreply.github.com"
          git add -A rivals_cosmetics.sqlite3 site
          git diff --quiet --staged || git commit -m "Refresh data"
          git push
      - uses: actions/configure-pages@v5
      - uses: actions/upload-pages-artifact@v3
        with:
          path: site
      - id: deployment
        uses: actions/deploy-pages@v4
"""

REPO_README = """# Marvel Rivals Cosmetic Equity

A dashboard comparing how many skins each Marvel Rivals hero receives
against how much people actually play them.

## Publishing it so anyone can open it

1. Create a new GitHub repository and push this folder to it.
2. In the repository, open **Settings -> Pages** and set **Source** to
   **GitHub Actions**.
3. Open the **Actions** tab, choose *Refresh Marvel Rivals data*, and click
   **Run workflow**.

When it finishes you get a public link -- `https://<you>.github.io/<repo>/` --
that anyone can open with no install. The workflow re-runs every morning, so
heroes and skins released later show up on their own.

## Running it on your own machine

    pip install requests beautifulsoup4 lxml
    python rivals_cosmetics.py

That opens the dashboard at http://127.0.0.1:8765/ with a Refresh data button.

## Making a file you can email

    python rivals_cosmetics.py --build

That writes `index.html` with the data baked in. It is one file, it needs no
server, and it opens by double-clicking.
"""


def init_repo(target):
    target = Path(target).expanduser().resolve()
    (target / ".github" / "workflows").mkdir(parents=True, exist_ok=True)
    (target / "site").mkdir(exist_ok=True)
    (target / ".github" / "workflows" / "refresh.yml").write_text(WORKFLOW)
    (target / "README.md").write_text(REPO_README)
    (target / "rivals_cosmetics.py").write_text(Path(__file__).read_text())
    if DB_PATH.exists():
        (target / DB_PATH.name).write_bytes(DB_PATH.read_bytes())
    print(f"Scaffolded {target}. Next steps are in its README.md.")


# ===========================================================================
# CLI
# ===========================================================================

def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--collect", action="store_true", help="refresh the database and exit")
    ap.add_argument("--full", action="store_true", help="re-read every costume page, not just new ones")
    ap.add_argument("--skip-gender", action="store_true", help="don't look up gender for new heroes")
    ap.add_argument("--build", action="store_true", help="write a standalone index.html and exit")
    ap.add_argument("--out", default="index.html", help="where --build writes to")
    ap.add_argument("--init-repo", metavar="DIR", help="scaffold an auto-updating GitHub Pages site")
    ap.add_argument("--port", type=int, default=PORT_DEFAULT)
    ap.add_argument("--no-browser", action="store_true")
    args = ap.parse_args()

    if args.init_repo:
        init_repo(args.init_repo)
        return

    if args.collect:
        collect(full=args.full, skip_gender=args.skip_gender)
        sys.exit(1 if PROGRESS.error else 0)

    if args.build:
        payload = build_payload()
        if not payload["skins"]:
            sys.exit("No data yet. Run:  python3 rivals_cosmetics.py --collect")
        out = Path(args.out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(render_page(embed=payload), encoding="utf-8")
        size = out.stat().st_size / 1024
        print(f"Wrote {out} ({size:.0f} KB) -- {len(payload['heroes'])} heroes, "
              f"{len(payload['skins'])} costumes. Share this one file with anyone.")
        return

    if not DB_PATH.exists():
        print("No database yet -- collecting first. This takes about eight minutes.")
        collect()

    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    url = f"http://127.0.0.1:{args.port}/"
    print(f"Marvel Rivals Cosmetic Equity is running at {url}")
    print("Press Ctrl+C to stop.")
    if not args.no_browser:
        threading.Timer(0.5, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")
        server.shutdown()


PAGE_HTML = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Marvel Rivals Cosmetic Equity</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Archivo:wght@400;500;600;800&display=swap" rel="stylesheet">
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.1/dist/chart.umd.min.js"></script>
<style>
:root{
  --ink:#0E1220; --panel:#151B2B; --raise:#1C2338; --line:#28304A;
  --text:#E2E7F3; --dim:#818CAB; --faint:#5A6480;
  --rare:#4FA3E3; --epic:#A56BE8; --legend:#F0A32B; --plain:#69738F;
  --over:#FF5C7A; --under:#3DD6A0;
  --vanguard:#5B8DEF; --duelist:#E4565F; --strategist:#37C79A; --triple:#C9A227;
}
*{box-sizing:border-box}
html,body{margin:0;padding:0}
body{
  background:var(--ink); color:var(--text);
  font-family:Archivo,system-ui,sans-serif; font-size:15px; line-height:1.5;
  font-variant-numeric:tabular-nums;
}
a{color:var(--rare)}
.wrap{max-width:1320px;margin:0 auto;padding:28px 22px 80px}

header.top{display:flex;flex-wrap:wrap;gap:20px;align-items:flex-end;
  justify-content:space-between;border-bottom:1px solid var(--line);padding-bottom:20px}
h1{font-size:clamp(30px,4.4vw,50px);font-weight:800;letter-spacing:-.022em;
  margin:0;line-height:1.02;max-width:13ch}
h1 .thin{font-weight:400;color:var(--dim);display:block}
.status{font-size:13px;color:var(--dim);text-align:right;min-width:220px}
.status b{color:var(--text);font-weight:600}
.controls{display:flex;gap:10px;align-items:center;margin-top:10px;justify-content:flex-end;flex-wrap:wrap}
button{font-family:inherit;font-size:13px;font-weight:600;color:var(--text);
  background:var(--raise);border:1px solid var(--line);border-radius:7px;
  padding:8px 13px;cursor:pointer}
button:hover{border-color:var(--faint)}
button.go{background:var(--rare);border-color:var(--rare);color:#07101C}
button:focus-visible,input:focus-visible,select:focus-visible{outline:2px solid var(--rare);outline-offset:2px}
.log{display:none;margin-top:14px;background:#080B14;border:1px solid var(--line);
  border-radius:8px;padding:12px;max-height:190px;overflow:auto;
  font-size:12px;line-height:1.65;color:#9FB0CF;white-space:pre-wrap}

.layout{display:grid;grid-template-columns:236px 1fr;gap:26px;margin-top:26px;align-items:start}
@media(max-width:940px){.layout{grid-template-columns:1fr}}
aside{position:sticky;top:20px;background:var(--panel);border:1px solid var(--line);
  border-radius:11px;padding:16px}
@media(max-width:940px){aside{position:static}}
aside h2{font-size:12px;font-weight:600;color:var(--dim);margin:0 0 12px}
fieldset{border:0;border-top:1px solid var(--line);margin:14px 0 0;padding:13px 0 0}
fieldset:first-of-type{border-top:0;margin-top:0;padding-top:0}
legend{font-size:12px;color:var(--dim);padding:0;margin-bottom:7px}
label.chk{display:flex;align-items:center;gap:8px;font-size:13.5px;padding:3px 0;cursor:pointer}
label.chk input{accent-color:var(--rare);width:14px;height:14px;flex:none}
.swatch{width:9px;height:9px;border-radius:2px;flex:none}
.reset{width:100%;margin-top:16px}
select,input[type=search]{width:100%;font-family:inherit;font-size:13.5px;color:var(--text);
  background:var(--raise);border:1px solid var(--line);border-radius:7px;padding:7px 9px}

nav.tabs{display:flex;gap:4px;border-bottom:1px solid var(--line);margin-bottom:20px;flex-wrap:wrap}
nav.tabs button{background:none;border:0;border-bottom:2px solid transparent;border-radius:0;
  padding:9px 14px;color:var(--dim);font-size:14px}
nav.tabs button[aria-selected=true]{color:var(--text);border-bottom-color:var(--rare)}
section[hidden]{display:none}

.lede{color:var(--dim);font-size:14px;max-width:74ch;margin:0 0 18px}
.plot{position:relative;height:520px;background:var(--panel);border:1px solid var(--line);
  border-radius:11px;padding:14px}
@media(max-width:700px){.plot{height:420px}}

.cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(190px,1fr));gap:12px;margin:18px 0}
.card{background:var(--panel);border:1px solid var(--line);border-radius:11px;padding:14px 15px}
.card .n{font-size:26px;font-weight:800;letter-spacing:-.02em;line-height:1.15}
.card .k{font-size:12.5px;color:var(--dim);margin-top:2px}
.card .sub{font-size:12px;color:var(--faint);margin-top:6px}

table{width:100%;border-collapse:collapse;font-size:13.5px}
th,td{text-align:right;padding:8px 10px;border-bottom:1px solid var(--line);white-space:nowrap}
th:first-child,td:first-child,th.l,td.l{text-align:left}
thead th{position:sticky;top:0;background:var(--ink);color:var(--dim);font-weight:600;
  font-size:12px;cursor:pointer;z-index:2}
thead th:hover{color:var(--text)}
thead th[data-dir]{color:var(--text)}
tbody tr:hover{background:var(--raise)}
.tablewrap{max-height:640px;overflow:auto;border:1px solid var(--line);border-radius:11px;
  background:var(--panel)}
.pill{display:inline-block;padding:1px 7px;border-radius:20px;font-size:11.5px;font-weight:600}
.bar{height:5px;border-radius:3px;background:var(--rare);display:inline-block;vertical-align:middle}
.muted{color:var(--faint)}
.note{font-size:12.5px;color:var(--faint);margin-top:12px;max-width:76ch}
.empty{padding:50px 20px;text-align:center;color:var(--dim)}
.viewtoggle{display:inline-flex;gap:0;border:1px solid var(--line);border-radius:8px;
  overflow:hidden;margin-bottom:16px}
.viewtoggle button{border:0;border-radius:0;background:none;color:var(--dim);padding:7px 16px}
.viewtoggle button[aria-selected=true]{background:var(--raise);color:var(--text)}
.pickerbar{display:flex;gap:8px;align-items:center;flex-wrap:wrap;margin-bottom:10px}
.pickerbar input[type=search]{max-width:230px}
.pickerbar .count{font-size:12.5px;color:var(--dim)}
.heropicker{display:grid;grid-template-columns:repeat(auto-fill,minmax(178px,1fr));
  gap:2px 12px;max-height:172px;overflow:auto;background:var(--panel);
  border:1px solid var(--line);border-radius:9px;padding:11px 13px;margin-bottom:14px}
.heropicker label{display:flex;align-items:center;gap:7px;font-size:13px;cursor:pointer;padding:2px 0}
.heropicker input{accent-color:var(--rare);width:13px;height:13px;flex:none}
.heropicker .dash{width:13px;height:3px;border-radius:2px;flex:none}
.heropicker .ct{color:var(--faint);font-size:12px;margin-left:auto}
footer{margin-top:44px;padding-top:18px;border-top:1px solid var(--line);
  font-size:12.5px;color:var(--faint);max-width:80ch}
@media(prefers-reduced-motion:reduce){*{transition:none!important;animation:none!important}}
</style>
</head>
<body>
<div class="wrap">

<header class="top">
  <h1>Cosmetic equity<span class="thin">Which Marvel Rivals heroes get the skins, and which get the players</span></h1>
  <div>
    <div class="status">
      <div><b id="sHeroes">–</b> heroes · <b id="sSkins">–</b> costumes</div>
      <div id="sWhen">Loading…</div>
    </div>
    <div class="controls">
      <button id="btnRefresh" class="go">Refresh data</button>
      <button id="btnLog">Show log</button>
    </div>
  </div>
</header>
<div class="log" id="log"></div>

<div class="layout">
<aside>
  <h2>Filters</h2>
  <fieldset><legend>Role</legend><div id="fRole"></div></fieldset>
  <fieldset><legend>Rarity</legend><div id="fRarity"></div></fieldset>
  <fieldset><legend>How it was obtained</legend><div id="fSource"></div></fieldset>
  <fieldset><legend>Gender</legend><div id="fGender"></div></fieldset>
  <fieldset><legend>Recolors</legend>
    <label class="chk"><input type="checkbox" id="fChroma"> Count chromas as skins</label>
  </fieldset>
  <fieldset><legend>Released from</legend>
    <select id="fSeason"></select>
  </fieldset>
  <button class="reset" id="btnReset">Reset filters</button>
</aside>

<main>
<nav class="tabs" role="tablist">
  <button role="tab" aria-selected="true"  data-tab="balance">Supply vs demand</button>
  <button role="tab" aria-selected="false" data-tab="heroes">Heroes</button>
  <button role="tab" aria-selected="false" data-tab="skins">Costumes</button>
  <button role="tab" aria-selected="false" data-tab="money">Spending</button>
  <button role="tab" aria-selected="false" data-tab="time">Over time</button>
</nav>

<section id="tab-balance">
  <p class="lede">Each hero is a point. Right means people play them; up means they
  get skins. Heroes above the line get more cosmetic attention than their share of
  play would predict, heroes below it get less.</p>
  <div class="plot"><canvas id="cScatter"></canvas></div>
  <div class="cards" id="balanceCards"></div>
  <p class="note" id="balanceNote"></p>
</section>

<section id="tab-heroes" hidden>
  <div class="viewtoggle" role="tablist">
    <button data-hview="list"  aria-selected="true">List</button>
    <button data-hview="graph" aria-selected="false">Graph</button>
  </div>

  <div id="heroesList">
    <p class="lede">Equity is a hero's share of all skins divided by their share of all
    play. Above 1.00 means more skins than their play share accounts for.</p>
    <div class="tablewrap"><table id="tHeroes"></table></div>
  </div>

  <div id="heroesGraph" hidden>
    <p class="lede">Each line is one hero's running total of costumes, counted weekly.
    A flat stretch is a hero going without. The filters on the left apply here too, so
    you can watch legendaries alone, or one season onwards.</p>
    <div class="pickerbar">
      <input type="search" id="qHeroPick" placeholder="Find a hero">
      <button id="pickTop">Top 8</button>
      <button id="pickAll">Select all</button>
      <button id="pickNone">Clear</button>
      <span class="count" id="pickCount"></span>
    </div>
    <div class="heropicker" id="heroPicker"></div>
    <div class="plot"><canvas id="cHeroTime"></canvas></div>
  </div>
</section>

<section id="tab-skins" hidden>
  <p class="lede">Every costume, with how often it turns up in matches on that hero.</p>
  <input type="search" id="qSkin" placeholder="Search a costume or hero" style="max-width:340px;margin-bottom:12px">
  <div class="tablewrap"><table id="tSkins"></table></div>
</section>

<section id="tab-money" hidden>
  <p class="lede">Nobody publishes real revenue, so this is a model: each costume's
  price in Units multiplied by the number of matches it is seen in. Treat it as a
  ranking of where money goes, not as an amount of money.</p>
  <div class="plot" style="height:560px"><canvas id="cMoney"></canvas></div>
  <div class="cards" id="moneyCards"></div>
</section>

<section id="tab-time" hidden>
  <p class="lede">Costumes released per month, and the running total by rarity.</p>
  <div class="plot"><canvas id="cTime"></canvas></div>
  <div class="cards" id="timeCards"></div>
</section>
</main>
</div>

<footer>
  Catalogue, prices and release dates from rivalskins.com. Play rates and skin usage
  from rivalsmeta.com. Character gender from the Marvel Database on marvel.fandom.com.
  All three are community projects and unaffiliated with NetEase or Marvel. Usage
  figures cover matches those trackers observe, not every match played.
</footer>
</div>

<script>
/*__BOOTSTRAP__*/

const RARITY_ORDER = ["Legendary","Epic","Rare","Default"];
const RARITY_COLOR = {Legendary:"var(--legend)",Epic:"var(--epic)",Rare:"var(--rare)",Default:"var(--plain)"};
const RARITY_HEX   = {Legendary:"#F0A32B",Epic:"#A56BE8",Rare:"#4FA3E3",Default:"#69738F"};
const ROLE_HEX = {Vanguard:"#5B8DEF",Duelist:"#E4565F",Strategist:"#37C79A","Triple-role":"#C9A227"};

let DATA = {heroes:[],skins:[],collected_at:null};
let heroBySlug = new Map();
const filters = {role:new Set(),rarity:new Set(),source:new Set(),gender:new Set(),
                 chroma:false, since:""};
const charts = {};

const $ = s => document.querySelector(s);
const fmt = n => n==null ? "–" : n.toLocaleString("en-US");
const fmt1 = n => n==null ? "–" : n.toFixed(1);
const fmt2 = n => n==null ? "–" : n.toFixed(2);

/* ---------------------------------------------------------------- loading */
async function load(){
  if (EMBEDDED){ DATA = EMBEDDED; }
  else {
    try { DATA = await (await fetch("/api/data")).json(); }
    catch(e){ DATA = {heroes:[],skins:[],collected_at:null}; }
  }
  heroBySlug = new Map(DATA.heroes.map(h=>[h.slug,h]));
  $("#sHeroes").textContent = fmt(DATA.heroes.length);
  $("#sSkins").textContent  = fmt(DATA.skins.length);
  $("#sWhen").textContent = DATA.collected_at
    ? "Data collected " + new Date(DATA.collected_at).toLocaleString()
    : "No data collected yet";
  buildFilters();
  render();
}

function uniq(list){ return [...new Set(list.filter(Boolean))]; }

function buildFilters(){
  const roles   = uniq(DATA.heroes.map(h=>h.role)).sort();
  const genders = uniq(DATA.heroes.map(h=>h.gender)).sort();
  const rarities= RARITY_ORDER.filter(r=>DATA.skins.some(s=>s.rarity===r));
  const sources = uniq(DATA.skins.map(s=>s.source)).sort();

  group("#fRole", roles, filters.role, v=>ROLE_HEX[v]||"var(--faint)");
  group("#fRarity", rarities, filters.rarity, v=>RARITY_COLOR[v]);
  group("#fSource", sources, filters.source, ()=>null);
  group("#fGender", genders, filters.gender, ()=>null);

  const seasons = uniq(DATA.skins.map(s=>s.season))
    .sort((a,b)=>seasonNum(a)-seasonNum(b));
  const sel = $("#fSeason");
  sel.innerHTML = `<option value="">Every season</option>` +
    seasons.map(s=>`<option value="${s}">${s} onwards</option>`).join("");
  sel.value = filters.since;
  sel.onchange = ()=>{ filters.since = sel.value; render(); };
  $("#fChroma").checked = filters.chroma;
  $("#fChroma").onchange = e => { filters.chroma = e.target.checked; render(); };
}

function seasonNum(s){ const m=/([\d.]+)/.exec(s||""); return m?parseFloat(m[1]):-1; }

function group(sel, values, state, colorFn){
  if(!state.size) values.forEach(v=>state.add(v));
  $(sel).innerHTML = values.map(v=>{
    const c = colorFn(v);
    const dot = c ? `<span class="swatch" style="background:${c}"></span>` : "";
    return `<label class="chk"><input type="checkbox" value="${v}" ${state.has(v)?"checked":""}>${dot}${v}</label>`;
  }).join("");
  $(sel).querySelectorAll("input").forEach(cb=>{
    cb.onchange = ()=>{ cb.checked ? state.add(cb.value) : state.delete(cb.value); render(); };
  });
}

/* ---------------------------------------------------------------- filtering */
function heroPasses(h){
  return (!h.role   || filters.role.has(h.role)) &&
         (!h.gender || filters.gender.has(h.gender) || filters.gender.size===0);
}
function skinPasses(s){
  const h = heroBySlug.get(s.hero_slug);
  if(!h || !heroPasses(h)) return false;
  if(s.rarity && !filters.rarity.has(s.rarity)) return false;
  if(s.source && filters.source.size && !filters.source.has(s.source)) return false;
  if(!filters.chroma && s.is_chroma) return false;
  if(filters.since && seasonNum(s.season) < seasonNum(filters.since)) return false;
  return true;
}

/* Everything the views need, computed once per render. */
function computeRows(){
  const skins = DATA.skins.filter(skinPasses);
  const byHero = new Map();
  for(const s of skins){
    if(!byHero.has(s.hero_slug)) byHero.set(s.hero_slug,[]);
    byHero.get(s.hero_slug).push(s);
  }
  const heroes = DATA.heroes.filter(heroPasses);
  const totalSkins = skins.length || 1;
  const totalPick  = heroes.reduce((a,h)=>a+(h.pick_rate||0),0) || 1;

  const rows = heroes.map(h=>{
    const mine = byHero.get(h.slug) || [];
    const paid = mine.filter(s=>s.price && s.currency==="unit");
    const spend = mine.reduce((a,s)=>a + ((s.price||0) * (s.usage_matches||0)), 0);
    const supply = mine.length / totalSkins;
    const demand = (h.pick_rate||0) / totalPick;
    const top = mine.filter(s=>s.usage_share!=null)
                    .sort((a,b)=>b.usage_share-a.usage_share)[0] || null;
    return {
      slug:h.slug, name:h.name, role:h.role, gender:h.gender, tier:h.tier,
      pick:h.pick_rate, win:h.win_rate, ban:h.ban_rate, matches:h.matches,
      skins:mine.length,
      legendary: mine.filter(s=>s.rarity==="Legendary").length,
      chromas:   mine.filter(s=>s.is_chroma).length,
      catalogue: paid.reduce((a,s)=>a+s.price,0),
      spend, perMatch: h.matches ? spend/h.matches : null,
      equity: demand>0 ? supply/demand : null,
      topSkin: top ? top.name : null, topShare: top ? top.usage_share : null,
    };
  });
  return {skins, rows};
}

/* ---------------------------------------------------------------- rendering */
function render(){
  const {skins, rows} = computeRows();
  if(!DATA.skins.length){
    document.querySelectorAll("section").forEach(s=>{
      if(!s.querySelector(".empty"))
        s.insertAdjacentHTML("afterbegin",
          `<div class="empty">No data yet. Click <b>Refresh data</b> to collect it.</div>`);
    });
    return;
  }
  drawScatter(rows);
  balanceCards(rows, skins);
  heroTable(rows);
  heroGraphView(rows, skins);
  skinTable(skins);
  moneyView(rows);
  timeView(skins);
}

function drawScatter(rows){
  const pts = rows.filter(r=>r.pick!=null && r.pick>0);
  const byRole = {};
  for(const r of pts){ (byRole[r.role||"Other"] ||= []).push(r); }
  const datasets = Object.entries(byRole).map(([role,list])=>({
    label: role,
    data: list.map(r=>({x:r.pick, y:r.skins, r:5, row:r})),
    backgroundColor: (ROLE_HEX[role]||"#69738F") + "CC",
    borderColor: ROLE_HEX[role]||"#69738F",
    pointRadius:6, pointHoverRadius:9,
  }));

  // Least-squares line through the origin: the "expected" skins for a pick rate.
  const sx = pts.reduce((a,r)=>a+r.pick*r.pick,0);
  const sy = pts.reduce((a,r)=>a+r.pick*r.skins,0);
  const slope = sx ? sy/sx : 0;
  const maxX = Math.max(...pts.map(r=>r.pick), 1);
  datasets.push({label:"Expected", type:"line", parsing:false,
    data:[{x:0,y:0},{x:maxX,y:slope*maxX}], borderColor:"#4A5573",
    borderDash:[6,5], borderWidth:1.5, pointRadius:0, fill:false, order:99});

  charts.scatter?.destroy();
  charts.scatter = new Chart($("#cScatter"), {
    type:"scatter",
    data:{datasets},
    options:{
      maintainAspectRatio:false,
      scales:{
        x:{title:{display:true,text:"Pick rate (% of matches)",color:"#818CAB"},
           grid:{color:"#242C44"},ticks:{color:"#818CAB"}},
        y:{title:{display:true,text:"Costumes released",color:"#818CAB"},
           grid:{color:"#242C44"},ticks:{color:"#818CAB"},beginAtZero:true},
      },
      plugins:{
        legend:{labels:{color:"#C8D1E6",usePointStyle:true,boxWidth:8,
          filter:i=>i.text!=="Expected"}},
        tooltip:{callbacks:{label:c=>{
          const r=c.raw.row; if(!r) return "";
          return [`${r.name} — ${r.role||"?"}`,
                  `${r.skins} costumes · ${fmt1(r.pick)}% pick rate`,
                  `Equity ${fmt2(r.equity)}${r.equity>1?" (over-served)":" (under-served)"}`];
        }}}
      }
    }
  });
}

function balanceCards(rows, skins){
  const rated = rows.filter(r=>r.equity!=null).sort((a,b)=>b.equity-a.equity);
  if(!rated.length){ $("#balanceCards").innerHTML=""; return; }
  const over = rated[0], under = rated[rated.length-1];
  const most = [...rows].sort((a,b)=>b.skins-a.skins)[0];
  const played = rows.filter(r=>r.pick!=null).sort((a,b)=>b.pick-a.pick)[0];
  $("#balanceCards").innerHTML = [
    card(over.name, "Most over-served", `${over.skins} costumes · ${fmt1(over.pick)}% pick · equity ${fmt2(over.equity)}`),
    card(under.name, "Most under-served", `${under.skins} costumes · ${fmt1(under.pick)}% pick · equity ${fmt2(under.equity)}`),
    card(String(most.skins), `Most costumes — ${most.name}`, `${most.legendary} legendary, ${most.chromas} chromas`),
    card(fmt1(played.pick)+"%", `Most played — ${played.name}`, `${played.skins} costumes`),
  ].join("");
  const noRate = rows.filter(r=>r.pick==null).length;
  $("#balanceNote").textContent = noRate
    ? `${noRate} hero${noRate>1?"es have":" has"} no play data yet and sit outside the plot.` : "";
}
function card(n,k,sub){
  return `<div class="card"><div class="n">${n}</div><div class="k">${k}</div>
          <div class="sub">${sub||""}</div></div>`;
}

/* ------------------------------------------------------------ sortable tables */
function makeTable(el, cols, rows, initial){
  let sortKey = el._sortKey || initial, dir = el._dir ?? -1;
  function paint(){
    const sorted = [...rows].sort((a,b)=>{
      const x=a[sortKey], y=b[sortKey];
      if(x==null && y==null) return 0;
      if(x==null) return 1;
      if(y==null) return -1;
      return (typeof x==="string" ? x.localeCompare(y) : x-y) * dir;
    });
    el.innerHTML =
      `<thead><tr>${cols.map(c=>
        `<th class="${c.left?"l":""}" data-k="${c.key}" ${c.key===sortKey?`data-dir="${dir}"`:""}
           title="${c.help||""}">${c.label}${c.key===sortKey?(dir<0?" ▾":" ▴"):""}</th>`).join("")}</tr></thead>` +
      `<tbody>${sorted.map(r=>`<tr>${cols.map(c=>
        `<td class="${c.left?"l":""}">${c.cell(r)}</td>`).join("")}</tr>`).join("")}</tbody>`;
    el.querySelectorAll("th").forEach(th=>{
      th.onclick = ()=>{
        const k = th.dataset.k;
        if(k===sortKey) dir = -dir; else { sortKey = k; dir = -1; }
        el._sortKey = sortKey; el._dir = dir; paint();
      };
    });
  }
  paint();
}

function roleTag(role){
  if(!role) return `<span class="muted">–</span>`;
  return `<span class="pill" style="background:${(ROLE_HEX[role]||"#69738F")}22;color:${ROLE_HEX[role]||"#818CAB"}">${role}</span>`;
}

const WEEK_MS = 7*24*60*60*1000;
let heroView = "list";
let pickedHeroes = null;          // null = not chosen yet, seed with the top few
let pickerQuery = "";

function hueFor(slug){
  let h = 0;
  for(let i=0;i<slug.length;i++) h = (h*31 + slug.charCodeAt(i)) % 360;
  return h;
}
function heroColor(slug){ return `hsl(${hueFor(slug)} 68% 62%)`; }

/* Running costume count per hero, one point per week. */
function weeklySeries(skins, slugs){
  const dated = skins.filter(s=>s.release_date);
  if(!dated.length) return {labels:[], series:new Map()};
  const times = dated.map(s=>Date.parse(s.release_date+"T00:00:00Z"));
  const first = Math.min(...times);
  // start the axis on the Monday of the first release week
  const d0 = new Date(first);
  const start = first - ((d0.getUTCDay()+6)%7)*24*60*60*1000;
  const end = Math.max(Date.now(), ...times);
  const n = Math.floor((end-start)/WEEK_MS)+1;
  const labels = Array.from({length:n},(_,i)=>
    new Date(start+i*WEEK_MS).toISOString().slice(0,10));

  const week = iso => Math.min(n-1, Math.max(0,
    Math.floor((Date.parse(iso+"T00:00:00Z")-start)/WEEK_MS)));

  const series = new Map();
  for(const slug of slugs) series.set(slug, new Array(n).fill(0));
  for(const s of dated){
    const arr = series.get(s.hero_slug);
    if(arr) arr[week(s.release_date)]++;
  }
  // A hero's default costume carries no release date -- it has simply existed
  // since they launched. Seat it in the week of their first dated costume so
  // the line ends on the same number the list view shows.
  const debut = new Map();
  for(const s of dated){
    const cur = debut.get(s.hero_slug);
    if(cur === undefined || s.release_date < cur) debut.set(s.hero_slug, s.release_date);
  }
  for(const s of skins){
    if(s.release_date) continue;
    const arr = series.get(s.hero_slug);
    if(!arr) continue;
    const d = debut.get(s.hero_slug);
    arr[d ? week(d) : 0]++;
  }
  for(const arr of series.values()){
    for(let i=1;i<arr.length;i++) arr[i] += arr[i-1];
  }
  return {labels, series};
}

function heroGraphView(rows, skins){
  const ranked = [...rows].sort((a,b)=>b.skins-a.skins);
  const available = new Set(ranked.map(r=>r.slug));
  if(pickedHeroes === null){
    pickedHeroes = new Set(ranked.slice(0,8).map(r=>r.slug));
  } else {
    // drop anything the current filters removed
    for(const slug of [...pickedHeroes]) if(!available.has(slug)) pickedHeroes.delete(slug);
  }

  const q = pickerQuery.toLowerCase().trim();
  document.querySelector("#heroPicker").innerHTML = ranked
    .filter(r=>!q || r.name.toLowerCase().includes(q))
    .map(r=>`<label><input type="checkbox" value="${r.slug}" ${pickedHeroes.has(r.slug)?"checked":""}>
      <span class="dash" style="background:${heroColor(r.slug)}"></span>${r.name}
      <span class="ct">${r.skins}</span></label>`).join("")
    || `<div class="muted" style="padding:6px">No hero matches that.</div>`;
  document.querySelector("#heroPicker").querySelectorAll("input").forEach(cb=>{
    cb.onchange = ()=>{
      cb.checked ? pickedHeroes.add(cb.value) : pickedHeroes.delete(cb.value);
      heroGraphView(rows, skins);
    };
  });
  document.querySelector("#pickCount").textContent =
    `${pickedHeroes.size} of ${ranked.length} shown`;

  const slugs = ranked.filter(r=>pickedHeroes.has(r.slug)).map(r=>r.slug);
  const {labels, series} = weeklySeries(skins, slugs);
  const nameOf = Object.fromEntries(ranked.map(r=>[r.slug,r.name]));
  const datasets = slugs.map(slug=>({
    label: nameOf[slug], data: series.get(slug) || [],
    borderColor: heroColor(slug), backgroundColor: heroColor(slug),
    borderWidth:2, pointRadius:0, pointHoverRadius:4, tension:.15, fill:false,
  }));

  charts.heroTime?.destroy();
  charts.heroTime = new Chart(document.querySelector("#cHeroTime"), {
    type:"line",
    data:{labels, datasets},
    options:{
      maintainAspectRatio:false, animation:false,
      interaction:{mode:"nearest", axis:"x", intersect:false},
      scales:{
        x:{grid:{color:"#242C44"},
           ticks:{color:"#818CAB",maxTicksLimit:12,autoSkip:true,
                  callback(v){ const d=this.getLabelForValue(v);
                    return new Date(d+"T00:00:00Z").toLocaleDateString("en-US",
                      {month:"short",year:"2-digit",timeZone:"UTC"}); }}},
        y:{beginAtZero:true,grid:{color:"#242C44"},ticks:{color:"#818CAB",precision:0},
           title:{display:true,text:"Costumes released, running total",color:"#818CAB"}},
      },
      plugins:{
        legend:{display: slugs.length<=16,
          labels:{color:"#C8D1E6",usePointStyle:true,boxWidth:8,padding:9}},
        tooltip:{callbacks:{title:i=>i.length?
          "Week of "+new Date(i[0].label+"T00:00:00Z").toLocaleDateString("en-US",
            {month:"short",day:"numeric",year:"numeric",timeZone:"UTC"}):"",
          label:c=>`${c.dataset.label}: ${c.parsed.y} costume${c.parsed.y===1?"":"s"}`}},
      }
    }
  });
}

function heroTable(rows){
  makeTable($("#tHeroes"), [
    {key:"name", label:"Hero", left:true, cell:r=>r.name},
    {key:"role", label:"Role", left:true, cell:r=>roleTag(r.role)},
    {key:"skins", label:"Costumes", cell:r=>fmt(r.skins)},
    {key:"legendary", label:"Legendary", cell:r=>fmt(r.legendary)},
    {key:"chromas", label:"Chromas", cell:r=>fmt(r.chromas)},
    {key:"pick", label:"Pick rate", cell:r=>r.pick==null?"–":fmt1(r.pick)+"%"},
    {key:"win", label:"Win rate", cell:r=>r.win==null?"–":fmt1(r.win)+"%"},
    {key:"equity", label:"Equity",
     help:"Share of all costumes divided by share of all play",
     cell:r=>{
       if(r.equity==null) return `<span class="muted">–</span>`;
       const c = r.equity>1 ? "var(--over)" : "var(--under)";
       return `<span style="color:${c};font-weight:600">${fmt2(r.equity)}</span>`;
     }},
    {key:"catalogue", label:"Catalogue cost",
     help:"Units to buy every purchasable costume for this hero",
     cell:r=>fmt(r.catalogue)},
    {key:"topSkin", label:"Most worn", left:true,
     cell:r=>r.topSkin ? `${r.topSkin} <span class="muted">${fmt1(r.topShare)}%</span>`
                       : `<span class="muted">–</span>`},
  ], rows, "skins");
}

function skinTable(skins){
  const q = ($("#qSkin").value||"").toLowerCase().trim();
  const rows = skins.map(s=>({
    name:s.name||"—", hero:(heroBySlug.get(s.hero_slug)||{}).name||s.hero_slug,
    rarity:s.rarity, source:s.source, season:s.season, date:s.release_date,
    price:(s.currency==="unit"?s.price:null), share:s.usage_share,
    matches:s.usage_matches, chroma:s.is_chroma, url:s.url,
    seasonN:seasonNum(s.season),
  })).filter(r=>!q || r.name.toLowerCase().includes(q) || r.hero.toLowerCase().includes(q));

  makeTable($("#tSkins"), [
    {key:"name", label:"Costume", left:true,
     cell:r=>`<a href="${r.url}" target="_blank" rel="noopener">${r.name}</a>` +
             (r.chroma?` <span class="muted">chroma</span>`:"")},
    {key:"hero", label:"Hero", left:true, cell:r=>r.hero},
    {key:"rarity", label:"Rarity", left:true, cell:r=>r.rarity
      ? `<span class="pill" style="background:${RARITY_HEX[r.rarity]}22;color:${RARITY_HEX[r.rarity]}">${r.rarity}</span>`
      : `<span class="muted">–</span>`},
    {key:"source", label:"Obtained from", left:true, cell:r=>r.source||`<span class="muted">–</span>`},
    {key:"seasonN", label:"Season", cell:r=>r.season||`<span class="muted">–</span>`},
    {key:"date", label:"Released", cell:r=>r.date||`<span class="muted">–</span>`},
    {key:"price", label:"Units", cell:r=>r.price?fmt(r.price):`<span class="muted">–</span>`},
    {key:"share", label:"Worn in",
     help:"Share of that hero's tracked matches using this costume",
     cell:r=>{
       if(r.share==null) return `<span class="muted">–</span>`;
       return `<span class="bar" style="width:${Math.max(2,r.share*1.6)}px"></span> ${fmt1(r.share)}%`;
     }},
  ], rows, "share");
}
$("#qSkin")?.addEventListener("input", ()=>skinTable(computeRows().skins));

function moneyView(rows){
  const rated = rows.filter(r=>r.spend>0).sort((a,b)=>b.spend-a.spend).slice(0,25);
  charts.money?.destroy();
  charts.money = new Chart($("#cMoney"), {
    type:"bar",
    data:{labels:rated.map(r=>r.name),
      datasets:[{label:"Estimated Units in play",
        data:rated.map(r=>r.spend),
        backgroundColor:rated.map(r=>(ROLE_HEX[r.role]||"#69738F")+"CC")}]},
    options:{indexAxis:"y",maintainAspectRatio:false,
      scales:{x:{grid:{color:"#242C44"},ticks:{color:"#818CAB",
                 callback:v=>v>=1e9?(v/1e9).toFixed(1)+"B":v>=1e6?(v/1e6).toFixed(0)+"M":v}},
              y:{grid:{display:false},ticks:{color:"#C8D1E6"}}},
      plugins:{legend:{display:false},
        tooltip:{callbacks:{label:c=>{
          const r=rated[c.dataIndex];
          return [`${fmt(Math.round(r.spend))} Units in play (estimated)`,
                  `${fmt(Math.round(r.perMatch||0))} Units on the average player`,
                  `${fmt(r.catalogue)} Units to own everything`];
        }}}}}
  });
  const byPer = rows.filter(r=>r.perMatch).sort((a,b)=>b.perMatch-a.perMatch);
  const byCat = [...rows].sort((a,b)=>b.catalogue-a.catalogue);
  const total = rows.reduce((a,r)=>a+r.catalogue,0);
  $("#moneyCards").innerHTML = [
    card(rated[0]?rated[0].name:"–", "Most money in play", "Highest price × matches worn"),
    card(byPer[0]?byPer[0].name:"–", "Priciest average player",
         byPer[0]?`${fmt(Math.round(byPer[0].perMatch))} Units equipped per match`:""),
    card(byCat[0]?fmt(byCat[0].catalogue):"–", `Costliest catalogue — ${byCat[0]?byCat[0].name:""}`,
         "Units to own every purchasable costume"),
    card(fmt(total), "Every costume, every hero", "Units, at current filters"),
  ].join("");
}

function timeView(skins){
  const dated = skins.filter(s=>s.release_date).sort((a,b)=>a.release_date<b.release_date?-1:1);
  const months = [...new Set(dated.map(s=>s.release_date.slice(0,7)))].sort();
  const rarities = RARITY_ORDER.filter(r=>dated.some(s=>s.rarity===r));
  const running = Object.fromEntries(rarities.map(r=>[r,0]));
  const series = Object.fromEntries(rarities.map(r=>[r,[]]));
  for(const m of months){
    for(const r of rarities){
      running[r] += dated.filter(s=>s.release_date.slice(0,7)===m && s.rarity===r).length;
      series[r].push(running[r]);
    }
  }
  charts.time?.destroy();
  charts.time = new Chart($("#cTime"), {
    type:"line",
    data:{labels:months, datasets:rarities.map(r=>({
      label:r, data:series[r], borderColor:RARITY_HEX[r],
      backgroundColor:RARITY_HEX[r]+"33", fill:true, tension:.25,
      pointRadius:0, pointHoverRadius:4, borderWidth:2}))},
    options:{maintainAspectRatio:false, interaction:{mode:"index",intersect:false},
      scales:{x:{grid:{color:"#242C44"},ticks:{color:"#818CAB",maxTicksLimit:14}},
              y:{stacked:true,grid:{color:"#242C44"},ticks:{color:"#818CAB"},
                 title:{display:true,text:"Costumes released, running total",color:"#818CAB"}}},
      plugins:{legend:{labels:{color:"#C8D1E6",usePointStyle:true,boxWidth:8}}}}
  });

  const perMonth = months.map(m=>dated.filter(s=>s.release_date.slice(0,7)===m).length);
  const busiest = months[perMonth.indexOf(Math.max(...perMonth))];
  const recent = perMonth.slice(-6);
  const avg = recent.length ? recent.reduce((a,b)=>a+b,0)/recent.length : 0;
  $("#timeCards").innerHTML = [
    card(fmt(dated.length), "Costumes with a release date", months.length+" months of releases"),
    card(fmt1(avg), "Per month, last six months", "At current filters"),
    card(busiest||"–", "Busiest month", busiest?fmt(Math.max(...perMonth))+" costumes":""),
    card(fmt(dated.filter(s=>s.is_chroma).length), "Chromas in view",
         filters.chroma?"Counted as skins":"Excluded from counts"),
  ].join("");
}

/* ---------------------------------------------------------------- chrome */
document.querySelectorAll("nav.tabs button").forEach(b=>{
  b.onclick = ()=>{
    document.querySelectorAll("nav.tabs button").forEach(x=>x.setAttribute("aria-selected", x===b));
    document.querySelectorAll("main section").forEach(s=>{
      s.hidden = s.id !== "tab-"+b.dataset.tab;
    });
  };
});
document.querySelectorAll(".viewtoggle button").forEach(b=>{
  b.onclick = ()=>{
    heroView = b.dataset.hview;
    document.querySelectorAll(".viewtoggle button").forEach(x=>
      x.setAttribute("aria-selected", x===b));
    $("#heroesList").hidden  = heroView!=="list";
    $("#heroesGraph").hidden = heroView!=="graph";
    if(heroView==="graph"){ const {rows,skins}=computeRows(); heroGraphView(rows,skins); }
  };
});
$("#qHeroPick").addEventListener("input", e=>{
  pickerQuery = e.target.value;
  const {rows,skins}=computeRows(); heroGraphView(rows,skins);
});
$("#pickTop").onclick = ()=>{
  const {rows,skins}=computeRows();
  pickedHeroes = new Set([...rows].sort((a,b)=>b.skins-a.skins).slice(0,8).map(r=>r.slug));
  heroGraphView(rows,skins);
};
$("#pickAll").onclick = ()=>{
  const {rows,skins}=computeRows();
  pickedHeroes = new Set(rows.map(r=>r.slug)); heroGraphView(rows,skins);
};
$("#pickNone").onclick = ()=>{
  const {rows,skins}=computeRows();
  pickedHeroes = new Set(); heroGraphView(rows,skins);
};
$("#btnReset").onclick = ()=>{
  [filters.role,filters.rarity,filters.source,filters.gender].forEach(s=>s.clear());
  filters.chroma=false; filters.since="";
  buildFilters(); render();
};
$("#btnLog").onclick = ()=>{
  const el = $("#log");
  const open = el.style.display==="block";
  el.style.display = open ? "none" : "block";
  $("#btnLog").textContent = open ? "Show log" : "Hide log";
};

const btn = $("#btnRefresh");
if (EMBEDDED){
  btn.disabled = true;
  btn.title = "This is a shared snapshot. Run the app yourself to collect fresh data.";
  btn.textContent = "Snapshot";
} else {
  btn.onclick = async ()=>{
    btn.disabled = true; btn.textContent = "Collecting…";
    $("#log").style.display="block"; $("#btnLog").textContent="Hide log";
    await fetch("/api/collect", {method:"POST"});
    poll();
  };
}
async function poll(){
  try{
    const s = await (await fetch("/api/status")).json();
    $("#log").textContent = s.lines.join("\n");
    $("#log").scrollTop = $("#log").scrollHeight;
    if(s.running){ setTimeout(poll, 1200); return; }
    btn.disabled=false; btn.textContent="Refresh data";
    await load();
  }catch(e){ btn.disabled=false; btn.textContent="Refresh data"; }
}

load();
</script>
</body>
</html>
"""

if __name__ == "__main__":
    main()
