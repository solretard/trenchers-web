"""
Trenchers API — leaderboard + faction-war backend.

Runs in two modes:
  * In-memory (default) — no database needed, great for local dev/testing.
  * Supabase — set SUPABASE_URL + SUPABASE_KEY and it persists to Postgres.

Deploy target: Railway (see Procfile + README).
Identity: handle-based for now; wallet-signature hook is stubbed in verify_wallet().
Anti-cheat: validate_run() is a deliberate placeholder — harden before real rewards.
"""

import os
import re
import time
import hmac
import hashlib
import secrets
from collections import defaultdict
from typing import Optional, List, Dict

import httpx                      # outbound calls to the Xaman platform
from fastapi import FastAPI, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel, Field

# --------------------------------------------------------------------------- #
# Config
# --------------------------------------------------------------------------- #
SUPABASE_URL = os.environ.get("SUPABASE_URL")
SUPABASE_KEY = os.environ.get("SUPABASE_KEY")          # use the SERVICE ROLE key (server-only!)
SEASON = os.environ.get("TRENCHERS_SEASON", "0")
TABLE = os.environ.get("TRENCHERS_TABLE", "trenchers_runs")
PLAYERS_TABLE = os.environ.get("TRENCHERS_PLAYERS_TABLE", "trenchers_players")
ALLOWED_ORIGINS = os.environ.get("ALLOWED_ORIGINS", "*").split(",")

# Xaman (XUMM) — sign-in via the user's Xaman app. Secret stays server-side.
XAMAN_API_KEY = os.environ.get("XAMAN_API_KEY")
XAMAN_API_SECRET = os.environ.get("XAMAN_API_SECRET")
XAMAN_ENABLED = bool(XAMAN_API_KEY and XAMAN_API_SECRET)
XAMAN_BASE = "https://xumm.app/api/v1/platform"

# Proof-of-wallet tokens. Minted when Xaman confirms the connect the player already
# does; the browser then sends it silently with every run, so nobody is ever asked
# to sign again after a game. If unset, wallet auth is disabled (dev mode).
WALLET_TOKEN_SECRET = os.environ.get("WALLET_TOKEN_SECRET", "").strip()
WALLET_TOKEN_TTL = int(os.environ.get("WALLET_TOKEN_TTL", str(30 * 24 * 3600)))   # 30 days

# NFT gating — does a wallet hold a Trenchers NFT? (issuer + optional taxon)
# Set these once your XRPL collection exists. Empty = feature dormant (nobody is a holder).
NFT_ISSUER = os.environ.get("NFT_ISSUER", "").strip()
NFT_TAXON = os.environ.get("NFT_TAXON", "").strip()          # optional; blank = any taxon from issuer
XRPL_RPC = os.environ.get("XRPL_RPC", "https://s1.ripple.com:51234/")
NFT_ENABLED = bool(NFT_ISSUER)
_nft_cache: Dict[str, tuple] = {}                            # wallet -> (checked_at, count)
NFT_CACHE_TTL = 120.0                                        # seconds

# --------------------------------------------------------------------------- #
# XP economy
#   XP = (scars * 0.3 + pvp_wins * 100) * nft_multiplier
#   nft_multiplier = 1 + 0.10 per NFT held, capped at 2.0 (i.e. +100% at 10 NFTs)
# XP accrues into WEEKLY buckets: each week's airdrop is based on XP earned that
# week, so holders can't idle their way into the top 30 — you have to play.
# --------------------------------------------------------------------------- #
XP_PER_SCAR = float(os.environ.get("XP_PER_SCAR", "0.3"))
XP_PER_PVP_WIN = float(os.environ.get("XP_PER_PVP_WIN", "100"))
XP_NFT_BONUS_EACH = float(os.environ.get("XP_NFT_BONUS_EACH", "0.10"))   # +10% per NFT
XP_NFT_BONUS_MAX = float(os.environ.get("XP_NFT_BONUS_MAX", "1.00"))     # cap at +100%
XP_TABLE = os.environ.get("TRENCHERS_XP_TABLE", "trenchers_xp")

# Shared secret so ONLY the realtime PvP server can report wins.
# If unset, /pvp/win is closed (fails shut) — no free XP for anyone.
PVP_SECRET = os.environ.get("PVP_SECRET", "").strip()

# Admin-only actions (taking/paying snapshots). Fails shut if unset.
ADMIN_SECRET = os.environ.get("ADMIN_SECRET", "").strip()
SNAPSHOT_TABLE = os.environ.get("TRENCHERS_SNAPSHOT_TABLE", "trenchers_snapshots")

# --- Token + vesting (fill these in after the First Ledger launch) ---
TOKEN_CURRENCY = os.environ.get("TOKEN_CURRENCY", "").strip()      # e.g. "TRENCH" or 40-char hex
TOKEN_ISSUER = os.environ.get("TOKEN_ISSUER", "").strip()          # the CA (blackholed after launch)
TOKEN_SUPPLY = float(os.environ.get("TOKEN_SUPPLY", "0") or 0)     # total supply, for % -> amount math
TREASURY_WALLET = os.environ.get("TREASURY_WALLET", "").strip()    # YOUR wallet that sends the escrows

# Each winner's weekly prize vests over a month: 25% unlocks per week for 4 weeks.
VEST_TRANCHES = int(os.environ.get("VEST_TRANCHES", "4"))
VEST_INTERVAL_DAYS = float(os.environ.get("VEST_INTERVAL_DAYS", "7"))
# Token escrows MUST have an expiry. Give a long window so nobody loses their tokens
# by claiming late — if it expires unclaimed, the tokens return to the treasury.
VEST_CANCEL_AFTER_DAYS = float(os.environ.get("VEST_CANCEL_AFTER_DAYS", "365"))

# XRPL epoch (2000-01-01) — escrow times are seconds since then, not Unix time.
RIPPLE_EPOCH = 946684800

# Airdrop: 5% of supply spread over 3 weekly snapshots, top 30 each week,
# split proportionally by that week's XP.
AIRDROP_TOTAL_PCT = float(os.environ.get("AIRDROP_TOTAL_PCT", "5.0"))
AIRDROP_WEEKS = int(os.environ.get("AIRDROP_WEEKS", "3"))
AIRDROP_TOP_N = int(os.environ.get("AIRDROP_TOP_N", "30"))
AIRDROP_WEEKLY_PCT = AIRDROP_TOTAL_PCT / max(1, AIRDROP_WEEKS)          # 1.666…% per week


def nft_multiplier(nft_count: int) -> float:
    """+10% XP per NFT held, capped at +100% (10 NFTs)."""
    return 1.0 + min(nft_count * XP_NFT_BONUS_EACH, XP_NFT_BONUS_MAX)


def compute_xp(scars: int, pvp_wins: int, nft_count: int) -> float:
    base = scars * XP_PER_SCAR + pvp_wins * XP_PER_PVP_WIN
    return round(base * nft_multiplier(nft_count), 2)


def week_key(ts: Optional[float] = None) -> str:
    """ISO week bucket, e.g. '2026-W28'. Weekly reset for airdrop fairness."""
    t = time.gmtime(ts if ts is not None else time.time())
    iso = time.strftime("%G-W%V", t)
    return iso


def wallet_nft_count(wallet: str) -> int:
    """How many Trenchers NFTs this wallet holds (issuer + optional taxon match).
    Reads live from an XRPL node. Cached briefly. Fails closed (0) on error."""
    if not NFT_ENABLED or not valid_wallet(wallet):
        return 0
    now = time.time()
    hit = _nft_cache.get(wallet)
    if hit and now - hit[0] < NFT_CACHE_TTL:
        return hit[1]
    count, marker, pages = 0, None, 0
    try:
        with httpx.Client(timeout=12) as client:
            while pages < 3:
                params = {"account": wallet, "ledger_index": "validated", "limit": 400}
                if marker:
                    params["marker"] = marker
                r = client.post(XRPL_RPC, json={"method": "account_nfts", "params": [params]})
                r.raise_for_status()
                res = r.json().get("result", {})
                for n in res.get("account_nfts", []):
                    if n.get("Issuer") == NFT_ISSUER and (not NFT_TAXON or str(n.get("NFTokenTaxon")) == NFT_TAXON):
                        count += 1
                marker = res.get("marker")
                pages += 1
                if not marker:
                    break
    except Exception:
        return 0   # fail closed: no perks/eligibility if we can't verify
    _nft_cache[wallet] = (now, count)
    return count

USE_SUPABASE = bool(SUPABASE_URL and SUPABASE_KEY)
if USE_SUPABASE:
    # Imported lazily so the app still boots in memory mode without the package.
    from supabase import create_client, Client
    sb: "Client" = create_client(SUPABASE_URL, SUPABASE_KEY)

# In-memory store (used when Supabase isn't configured)
_mem_runs: List[Dict] = []
_mem_players: Dict[str, Dict] = {}          # wallet -> {"wallet","data","updated_at"}
_mem_xp: Dict[tuple, Dict] = {}             # (wallet, week) -> {"scars","pvp_wins","runs"}

_WALLET_RE = re.compile(r"^r[1-9A-HJ-NP-Za-km-z]{24,34}$")


def valid_wallet(w: Optional[str]) -> bool:
    return bool(w) and isinstance(w, str) and bool(_WALLET_RE.match(w))

# The three playable classes double as the faction-war teams for now.
FACTIONS = {"APER", "DIAMOND", "SNIPER"}

# --------------------------------------------------------------------------- #
# Anti-cheat tunables (raise the cost of faking; not bulletproof by design)
# --------------------------------------------------------------------------- #
MAX_SCARS_PER_SEC = 500        # a run can't earn more scars/sec than this
MIN_SEC_PER_DEPTH = 3.0        # each room takes at least this long to clear
MIN_SESSION_SEC = 8.0          # a real run lasts at least this long
SESSION_TTL_SEC = 3 * 3600     # a session token is submittable for this long
SESSION_START_COOLDOWN = 6.0   # min seconds between a subject's session starts
MAX_SUBMITS_PER_HOUR = 40      # per subject (wallet/handle) and per IP

# Ephemeral server-side sessions: {sid: {"sub": str, "iat": float, "ip": str, "used": bool}}
_sessions: Dict[str, Dict] = {}
_last_start: Dict[str, float] = {}                 # subject -> last session-start time
_submit_log: Dict[str, List[float]] = defaultdict(list)   # key -> recent submit timestamps


def _client_ip(req: Request) -> str:
    fwd = req.headers.get("x-forwarded-for")
    if fwd:
        return fwd.split(",")[0].strip()
    return req.client.host if req.client else "unknown"


def _rate_ok(key: str) -> bool:
    now = time.time()
    log = [t for t in _submit_log[key] if now - t < 3600]
    _submit_log[key] = log
    return len(log) < MAX_SUBMITS_PER_HOUR


def _rate_hit(key: str):
    _submit_log[key].append(time.time())


def _prune_sessions():
    now = time.time()
    dead = [s for s, v in _sessions.items() if now - v["iat"] > SESSION_TTL_SEC]
    for s in dead:
        _sessions.pop(s, None)

# --------------------------------------------------------------------------- #
# Models
# --------------------------------------------------------------------------- #
class RunIn(BaseModel):
    handle: str = Field(min_length=1, max_length=24)
    faction: str
    scars: int = Field(ge=0, le=10_000_000)
    depth: int = Field(ge=1, le=100_000)
    kills: int = Field(ge=0, le=10_000_000)
    session: str = Field(min_length=8, max_length=64)   # required — issued by /session/start
    wallet: Optional[str] = None
    # Proof the player owns `wallet` (from the Xaman connect). Required when a wallet
    # is claimed, so XP can't be farmed into someone else's account.
    signature: Optional[str] = None


class SessionIn(BaseModel):
    handle: Optional[str] = Field(default=None, max_length=24)
    wallet: Optional[str] = None


class SessionOut(BaseModel):
    session: str
    issued_at: int


class PlayerSaveIn(BaseModel):
    wallet: str
    data: Dict = Field(default_factory=dict)


class PlayerOut(BaseModel):
    wallet: str
    data: Dict


class RunOut(BaseModel):
    ok: bool
    rank: Optional[int] = None
    best: Optional[int] = None
    season: str


class LeaderRow(BaseModel):
    rank: int
    handle: str
    faction: str
    scars: int
    depth: int


class FactionRow(BaseModel):
    faction: str
    total_scars: int
    players: int
    top_scars: int


# --------------------------------------------------------------------------- #
# App
# --------------------------------------------------------------------------- #
app = FastAPI(title="Trenchers API", version="0.1.0")
app.add_middleware(
    CORSMiddleware,
    allow_origins=ALLOWED_ORIGINS,
    allow_methods=["*"],
    allow_headers=["*"],
)


# --------------------------------------------------------------------------- #
# Hooks to harden later
# --------------------------------------------------------------------------- #
def _issue_wallet_token(wallet: str) -> str:
    """Signed proof that this browser controls `wallet`.

    Minted once, when Xaman confirms the sign-in the player already does to connect.
    The client stores it and sends it silently with each run — so players are never
    asked to sign again after a game. Format: wallet.expiry.hmac
    """
    exp = int(time.time()) + WALLET_TOKEN_TTL
    msg = f"{wallet}.{exp}"
    sig = hmac.new(WALLET_TOKEN_SECRET.encode(), msg.encode(), hashlib.sha256).hexdigest()
    return f"{msg}.{sig}"


def verify_wallet(wallet: Optional[str], token: Optional[str]) -> bool:
    """True only if `token` is a valid, unexpired proof for `wallet`.

    Without this, anyone could POST a run claiming someone else's wallet and farm
    XP into it. With XP now worth real tokens, that has to be shut.
    """
    if not wallet:
        return True                      # anonymous run: no wallet, no XP, nothing to steal
    if not WALLET_TOKEN_SECRET:
        return True                      # unset secret => auth disabled (dev only)
    if not token:
        return False
    try:
        addr, exp_s, sig = token.rsplit(".", 2)
    except ValueError:
        return False
    if addr != wallet:
        return False
    try:
        if int(exp_s) < time.time():
            return False
    except ValueError:
        return False
    expected = hmac.new(WALLET_TOKEN_SECRET.encode(),
                        f"{addr}.{exp_s}".encode(), hashlib.sha256).hexdigest()
    return hmac.compare_digest(expected, sig)


def validate_run(run: RunIn) -> bool:
    """Structural plausibility: faction valid and score not exceeding what
    depth + kills could yield. The *timing* gate (in submit_run) is the real
    teeth — this just rejects obviously-inconsistent numbers."""
    if run.faction not in FACTIONS:
        return False
    ceiling = 60 * run.depth + 35 * run.kills + 500
    if run.scars > ceiling:
        return False
    return True


def min_seconds_for(scars: int, depth: int) -> float:
    """Least wall-clock time a legit run of this size could take."""
    return max(MIN_SESSION_SEC, scars / MAX_SCARS_PER_SEC, depth * MIN_SEC_PER_DEPTH)


def sanitize_handle(h: str) -> str:
    cleaned = "".join(c for c in h if c.isalnum() or c in "_-").strip()
    return (cleaned or "anon")[:24]


# --------------------------------------------------------------------------- #
# XP accrual / lookup
#
# We store the RAW earned counters per (wallet, week) — scars and pvp_wins —
# and compute XP on read. Storing raw counters (not XP) means the NFT multiplier
# is always evaluated against the wallet's CURRENT holdings, and lets us change
# the formula later without corrupting history.
# --------------------------------------------------------------------------- #
def _xp_add(wallet: str, week: str, scars: int = 0, pvp_wins: int = 0, runs: int = 0):
    """Add raw earnings to this wallet's weekly bucket."""
    if not valid_wallet(wallet):
        return
    if USE_SUPABASE:
        try:
            existing = (
                sb.table(XP_TABLE).select("*")
                .eq("wallet", wallet).eq("week", week).eq("season", SEASON)
                .limit(1).execute().data
            )
            if existing:
                row = existing[0]
                sb.table(XP_TABLE).update({
                    "scars": int(row.get("scars", 0)) + scars,
                    "pvp_wins": int(row.get("pvp_wins", 0)) + pvp_wins,
                    "runs": int(row.get("runs", 0)) + runs,
                    "updated_at": int(time.time()),
                }).eq("id", row["id"]).execute()
            else:
                sb.table(XP_TABLE).insert({
                    "wallet": wallet, "week": week, "season": SEASON,
                    "scars": scars, "pvp_wins": pvp_wins, "runs": runs,
                    "updated_at": int(time.time()),
                }).execute()
        except Exception as e:
            print("xp_add error:", repr(e))
        return
    k = (wallet, week)
    cur = _mem_xp.setdefault(k, {"scars": 0, "pvp_wins": 0, "runs": 0})
    cur["scars"] += scars
    cur["pvp_wins"] += pvp_wins
    cur["runs"] += runs


def _xp_rows(week: str) -> List[Dict]:
    """All raw weekly rows for a given week."""
    if USE_SUPABASE:
        try:
            return (
                sb.table(XP_TABLE).select("*")
                .eq("week", week).eq("season", SEASON)
                .execute().data or []
            )
        except Exception as e:
            print("xp_rows error:", repr(e))
            return []
    return [
        {"wallet": w, "week": wk, **vals}
        for (w, wk), vals in _mem_xp.items() if wk == week
    ]


def _xp_totals(wallet: str) -> Dict:
    """Lifetime raw totals for a wallet (all weeks, current season)."""
    if USE_SUPABASE:
        try:
            rows = (
                sb.table(XP_TABLE).select("scars,pvp_wins,runs")
                .eq("wallet", wallet).eq("season", SEASON)
                .execute().data or []
            )
        except Exception as e:
            print("xp_totals error:", repr(e))
            rows = []
    else:
        rows = [v for (w, _wk), v in _mem_xp.items() if w == wallet]
    return {
        "scars": sum(int(r.get("scars", 0)) for r in rows),
        "pvp_wins": sum(int(r.get("pvp_wins", 0)) for r in rows),
        "runs": sum(int(r.get("runs", 0)) for r in rows),
    }


def weekly_board(week: str, top_n: int = AIRDROP_TOP_N) -> List[Dict]:
    """Top wallets for a week, ranked by XP (with each wallet's live NFT multiplier)."""
    out = []
    for r in _xp_rows(week):
        w = r.get("wallet")
        if not valid_wallet(w):
            continue
        scars = int(r.get("scars", 0))
        wins = int(r.get("pvp_wins", 0))
        n = wallet_nft_count(w)
        out.append({
            "wallet": w,
            "scars": scars,
            "pvp_wins": wins,
            "nfts": n,
            "multiplier": round(nft_multiplier(n), 2),
            "xp": compute_xp(scars, wins, n),
        })
    out.sort(key=lambda x: x["xp"], reverse=True)
    for i, row in enumerate(out):
        row["rank"] = i + 1
    return out[:top_n]


# --------------------------------------------------------------------------- #
# Routes
# --------------------------------------------------------------------------- #
@app.get("/")
def root():
    return {"name": "Trenchers API", "season": SEASON, "ok": True}


@app.get("/health")
def health():
    return {
        "ok": True,
        "season": SEASON,
        "store": "supabase" if USE_SUPABASE else "memory",
    }


@app.post("/session/start", response_model=SessionOut)
def session_start(body: SessionIn, request: Request):
    _prune_sessions()
    ip = _client_ip(request)
    sub = (body.wallet or sanitize_handle(body.handle or "") or ip)
    now = time.time()

    # simple per-subject cooldown so you can't spin up sessions in a tight loop
    last = _last_start.get(sub, 0.0)
    if now - last < SESSION_START_COOLDOWN:
        raise HTTPException(status_code=429, detail="slow down")
    if not _rate_ok("ip:" + ip):
        raise HTTPException(status_code=429, detail="too many sessions from this network")
    _last_start[sub] = now

    sid = secrets.token_urlsafe(24)
    _sessions[sid] = {"sub": sub, "iat": now, "ip": ip, "used": False}
    return SessionOut(session=sid, issued_at=int(now))


@app.post("/runs", response_model=RunOut)
def submit_run(run: RunIn, request: Request):
    run.faction = run.faction.upper()
    ip = _client_ip(request)

    # 1) must present a live, unused session token
    sess = _sessions.get(run.session)
    if not sess:
        raise HTTPException(status_code=401, detail="no active session — start a run first")
    if sess["used"]:
        raise HTTPException(status_code=409, detail="session already submitted")
    now = time.time()
    elapsed = now - sess["iat"]
    if elapsed > SESSION_TTL_SEC:
        _sessions.pop(run.session, None)
        raise HTTPException(status_code=410, detail="session expired")

    # 2) structural plausibility
    if not validate_run(run):
        raise HTTPException(status_code=400, detail="run failed validation")

    # 2b) reward model is wallet-based — a scoring run must carry a valid wallet
    if not valid_wallet(run.wallet):
        raise HTTPException(status_code=400, detail="connect a wallet to post a score")

    # 3) timing gate — the score can't have been earned faster than physically possible
    if elapsed + 1.0 < min_seconds_for(run.scars, run.depth):
        raise HTTPException(status_code=400, detail="run too fast to be real")

    # 4) rate limits (per subject and per network)
    sub = sess["sub"]
    if not _rate_ok("sub:" + sub) or not _rate_ok("ip:" + ip):
        raise HTTPException(status_code=429, detail="rate limit — try again later")

    if run.wallet and not verify_wallet(run.wallet, run.signature):
        raise HTTPException(status_code=401, detail="bad wallet signature")

    # consume the session and count against the rate windows
    sess["used"] = True
    _rate_hit("sub:" + sub)
    _rate_hit("ip:" + ip)

    handle = sanitize_handle(run.handle)
    is_holder = bool(run.wallet and wallet_nft_count(run.wallet) > 0)

    # XP: this run's scars go into the wallet's weekly bucket. This sits AFTER the
    # session/timing/rate gates above, so only runs that passed anti-cheat earn XP.
    if run.wallet:
        _xp_add(run.wallet, week_key(), scars=int(run.scars), runs=1)

    record = {
        "handle": handle,
        "faction": run.faction,
        "scars": run.scars,
        "depth": run.depth,
        "kills": run.kills,
        "wallet": run.wallet,
        "holder": is_holder,
        "season": SEASON,
        "created_at": int(time.time()),
    }

    if USE_SUPABASE:
        sb.table(TABLE).insert(record).execute()
        higher = (
            sb.table(TABLE)
            .select("id", count="exact")
            .eq("season", SEASON)
            .gt("scars", run.scars)
            .execute()
        )
        rank = (higher.count or 0) + 1
        best_res = (
            sb.table(TABLE)
            .select("scars")
            .eq("season", SEASON)
            .eq("handle", handle)
            .order("scars", desc=True)
            .limit(1)
            .execute()
        )
        best = best_res.data[0]["scars"] if best_res.data else run.scars
    else:
        _mem_runs.append(record)
        rank = sum(
            1 for r in _mem_runs
            if r["season"] == SEASON and r["scars"] > run.scars
        ) + 1
        best = max(
            (r["scars"] for r in _mem_runs
             if r["season"] == SEASON and r["handle"] == handle),
            default=run.scars,
        )

    return RunOut(ok=True, rank=rank, best=best, season=SEASON)


def _xaman_headers():
    return {"X-API-Key": XAMAN_API_KEY, "X-API-Secret": XAMAN_API_SECRET,
            "Content-Type": "application/json"}


@app.post("/xaman/signin")
def xaman_signin():
    """Create a Xaman SignIn request. Returns a QR image URL + deeplink the
    client shows; the user approves in their Xaman app (no payment, no keys)."""
    if not XAMAN_ENABLED:
        raise HTTPException(status_code=503, detail="Xaman not configured")
    try:
        with httpx.Client(timeout=15) as client:
            r = client.post(XAMAN_BASE + "/payload", headers=_xaman_headers(),
                            json={"txjson": {"TransactionType": "SignIn"}})
        r.raise_for_status()
        d = r.json()
    except Exception:
        raise HTTPException(status_code=502, detail="Xaman request failed")
    return {
        "uuid": d.get("uuid"),
        "next": (d.get("next") or {}).get("always"),
        "qr": (d.get("refs") or {}).get("qr_png"),
    }


@app.get("/xaman/status/{uuid}")
def xaman_status(uuid: str):
    if not XAMAN_ENABLED:
        raise HTTPException(status_code=503, detail="Xaman not configured")
    try:
        with httpx.Client(timeout=15) as client:
            r = client.get(XAMAN_BASE + "/payload/" + uuid, headers=_xaman_headers())
        r.raise_for_status()
        d = r.json()
    except Exception:
        raise HTTPException(status_code=502, detail="Xaman status failed")
    meta = d.get("meta") or {}
    resp = d.get("response") or {}
    signed = bool(meta.get("signed"))
    address = resp.get("account")

    out = {
        "resolved": bool(meta.get("resolved")),
        "signed": signed,
        "expired": bool(meta.get("expired")),
        "address": address,
    }
    # Xaman has cryptographically verified the user controls this wallet. Mint a
    # short-lived proof token — run submissions must present it, so nobody can post
    # a score (and earn XP) under a wallet they don't own.
    if signed and valid_wallet(address):
        out["wallet_token"] = _issue_wallet_token(address)
    return out


@app.get("/nft/list/{wallet}")
def nft_list(wallet: str, limit: int = 12):
    """The wallet's actual Trenchers NFTs, so the record page can show them.

    XRPL stores each NFT's metadata pointer as a hex-encoded URI, so we decode it
    here and hand the client a usable link. The client resolves ipfs:// and reads
    the `image` field itself — keeps this endpoint cheap and avoids fetching
    hundreds of metadata files server-side.
    """
    if not valid_wallet(wallet):
        raise HTTPException(status_code=400, detail="invalid wallet address")
    if not NFT_ENABLED:
        return {"enabled": False, "count": 0, "nfts": []}

    limit = max(1, min(int(limit or 12), 40))
    out: List[Dict] = []
    marker, pages = None, 0
    try:
        with httpx.Client(timeout=12) as client:
            while pages < 3:
                params = {"account": wallet, "ledger_index": "validated", "limit": 400}
                if marker:
                    params["marker"] = marker
                r = client.post(XRPL_RPC, json={"method": "account_nfts", "params": [params]})
                r.raise_for_status()
                res = r.json().get("result", {})
                for n in res.get("account_nfts", []):
                    if n.get("Issuer") != NFT_ISSUER:
                        continue
                    if NFT_TAXON and str(n.get("NFTokenTaxon")) != NFT_TAXON:
                        continue
                    uri_hex = n.get("URI") or ""
                    try:
                        uri = bytes.fromhex(uri_hex).decode("utf-8", "ignore") if uri_hex else ""
                    except ValueError:
                        uri = ""
                    out.append({
                        "id": n.get("NFTokenID"),
                        "serial": n.get("nft_serial"),
                        "uri": uri,
                    })
                marker = res.get("marker")
                pages += 1
                if not marker:
                    break
    except Exception:
        return {"enabled": True, "count": 0, "nfts": [], "error": "lookup failed"}

    out.sort(key=lambda d: d.get("serial") or 0)
    return {"enabled": True, "count": len(out), "nfts": out[:limit]}


_nft_list_cache: Dict[str, tuple] = {}
_meta_cache: Dict[str, Optional[str]] = {}


def _ipfs_http(uri: str) -> str:
    """ipfs://CID/path -> a public gateway URL the browser can load."""
    if uri.startswith("ipfs://"):
        return "https://ipfs.io/ipfs/" + uri[len("ipfs://"):]
    return uri


def _resolve_image(meta_uri: str) -> Optional[str]:
    """Fetch an NFT's metadata JSON and return a loadable image URL.

    Metadata usually stores a relative filename ("12.webp"), so it has to be
    resolved against the metadata's own folder.
    """
    if meta_uri in _meta_cache:
        return _meta_cache[meta_uri]
    img = None
    try:
        url = _ipfs_http(meta_uri)
        with httpx.Client(timeout=10, follow_redirects=True) as c:
            m = c.get(url).json()
        raw = (m.get("image") or "").strip()
        if raw:
            if raw.startswith("ipfs://") or raw.startswith("http"):
                img = _ipfs_http(raw)
            else:
                base = meta_uri.rsplit("/", 1)[0]          # strip the filename
                img = _ipfs_http(base + "/" + raw.lstrip("/"))
    except Exception:
        img = None
    _meta_cache[meta_uri] = img
    return img


@app.get("/nft/list/{wallet}")
def nft_list(wallet: str, limit: int = 12):
    """The wallet's Trenchers NFTs with image URLs, for showing on the record page."""
    if not valid_wallet(wallet):
        raise HTTPException(status_code=400, detail="invalid wallet address")
    if not NFT_ENABLED:
        return {"count": 0, "items": [], "enabled": False}

    limit = max(1, min(24, limit))
    now = time.time()
    hit = _nft_list_cache.get(wallet)
    if hit and now - hit[0] < NFT_CACHE_TTL:
        rows = hit[1]
        return {"count": len(rows), "items": rows[:limit], "enabled": True}

    found = []
    marker, pages = None, 0
    try:
        with httpx.Client(timeout=12) as client:
            while pages < 3:
                params = {"account": wallet, "ledger_index": "validated", "limit": 400}
                if marker:
                    params["marker"] = marker
                r = client.post(XRPL_RPC, json={"method": "account_nfts", "params": [params]})
                r.raise_for_status()
                res = r.json().get("result", {})
                for n in res.get("account_nfts", []):
                    if n.get("Issuer") != NFT_ISSUER:
                        continue
                    if NFT_TAXON and str(n.get("NFTokenTaxon")) != NFT_TAXON:
                        continue
                    uri_hex = n.get("URI") or ""
                    try:
                        meta_uri = bytes.fromhex(uri_hex).decode("utf-8", "ignore") if uri_hex else ""
                    except ValueError:
                        meta_uri = ""
                    found.append({
                        "id": n.get("NFTokenID"),
                        "serial": n.get("nft_serial"),
                        "meta": meta_uri,
                    })
                marker = res.get("marker")
                pages += 1
                if not marker:
                    break
    except Exception:
        return {"count": 0, "items": [], "enabled": True}

    found.sort(key=lambda x: x.get("serial") or 0)
    # only resolve images for the ones actually being displayed — each is a network hop
    for row in found[:limit]:
        row["image"] = _resolve_image(row["meta"]) if row["meta"] else None
    _nft_list_cache[wallet] = (now, found)
    return {"count": len(found), "items": found[:limit], "enabled": True}


@app.get("/nft/holder/{wallet}")
def nft_holder(wallet: str):
    """Does this wallet hold a Trenchers NFT? The bridge for perks, faction, and
    reward eligibility. Returns holder=False for everyone until the collection is set."""
    if not valid_wallet(wallet):
        raise HTTPException(status_code=400, detail="invalid wallet address")
    n = wallet_nft_count(wallet)
    return {"holder": n > 0, "count": n, "enabled": NFT_ENABLED}


@app.post("/player/save")
def player_save(body: PlayerSaveIn, request: Request):
    """Save a player's data under their wallet address (their account).
    NOTE: ownership isn't verified yet — anyone who knows a wallet address can
    write to it. Fine for non-sensitive game progress; add a signed-nonce check
    before storing anything that matters. Keep the blob small."""
    if not valid_wallet(body.wallet):
        raise HTTPException(status_code=400, detail="invalid wallet address")
    if len(str(body.data)) > 20_000:
        raise HTTPException(status_code=413, detail="data too large")
    ip = _client_ip(request)
    if not _rate_ok("save:" + ip):
        raise HTTPException(status_code=429, detail="slow down")
    _rate_hit("save:" + ip)

    record = {"wallet": body.wallet, "data": body.data,
              "season": SEASON, "updated_at": int(time.time())}
    if USE_SUPABASE:
        sb.table(PLAYERS_TABLE).upsert(record, on_conflict="wallet").execute()
    else:
        _mem_players[body.wallet] = record
    return {"ok": True}


@app.get("/player/{wallet}", response_model=PlayerOut)
def player_get(wallet: str):
    if not valid_wallet(wallet):
        raise HTTPException(status_code=400, detail="invalid wallet address")
    if USE_SUPABASE:
        res = sb.table(PLAYERS_TABLE).select("wallet,data").eq("wallet", wallet).limit(1).execute()
        row = res.data[0] if res.data else None
    else:
        row = _mem_players.get(wallet)
    return PlayerOut(wallet=wallet, data=(row["data"] if row else {}))


@app.get("/leaderboard", response_model=List[LeaderRow])
def leaderboard(limit: int = 20, faction: Optional[str] = None):
    limit = max(1, min(limit, 100))

    if USE_SUPABASE:
        q = sb.table(TABLE).select("handle,faction,scars,depth").eq("season", SEASON)
        if faction:
            q = q.eq("faction", faction.upper())
        # Over-fetch so we can keep only each player's best run after dedupe.
        rows = q.order("scars", desc=True).limit(limit * 5).execute().data
    else:
        rows = [r for r in _mem_runs if r["season"] == SEASON]
        if faction:
            rows = [r for r in rows if r["faction"] == faction.upper()]
        rows = sorted(rows, key=lambda r: r["scars"], reverse=True)

    best_per_handle: Dict[str, Dict] = {}
    for r in rows:
        h = r["handle"]
        if h not in best_per_handle or r["scars"] > best_per_handle[h]["scars"]:
            best_per_handle[h] = r

    top = sorted(best_per_handle.values(), key=lambda r: r["scars"], reverse=True)[:limit]
    return [
        LeaderRow(rank=i + 1, handle=r["handle"], faction=r["faction"],
                  scars=r["scars"], depth=r["depth"])
        for i, r in enumerate(top)
    ]


@app.get("/factions", response_model=List[FactionRow])
def factions():
    """Faction war standings. Each player's BEST run counts once toward their
    faction's total, so it rewards a faction's spread of strong players rather
    than letting one grinder submit a thousand runs."""
    if USE_SUPABASE:
        rows = sb.table(TABLE).select("handle,faction,scars").eq("season", SEASON).execute().data
    else:
        rows = [r for r in _mem_runs if r["season"] == SEASON]

    best_by_handle: Dict[tuple, int] = {}
    for r in rows:
        key = (r["faction"], r["handle"])
        if key not in best_by_handle or r["scars"] > best_by_handle[key]:
            best_by_handle[key] = r["scars"]

    agg: Dict[str, Dict] = {}
    for (fac, _handle), sc in best_by_handle.items():
        a = agg.setdefault(fac, {"total": 0, "players": 0, "top": 0})
        a["total"] += sc
        a["players"] += 1
        a["top"] = max(a["top"], sc)

    out = [
        FactionRow(faction=f, total_scars=v["total"], players=v["players"], top_scars=v["top"])
        for f, v in agg.items()
    ]
    out.sort(key=lambda x: x.total_scars, reverse=True)
    return out


# --------------------------------------------------------------------------- #
# XP / airdrop endpoints
# --------------------------------------------------------------------------- #
class PvpWinIn(BaseModel):
    wallet: str
    secret: str


@app.post("/pvp/win")
def pvp_win(body: PvpWinIn):
    """Called by the REALTIME server when a match is won — never by a browser.

    PvP results are server-authoritative on the realtime side, so a win reported
    here is trustworthy. The shared secret stops anyone from curl-ing themselves
    free wins. If PVP_SECRET isn't set, the endpoint stays closed.
    """
    if not PVP_SECRET or body.secret != PVP_SECRET:
        raise HTTPException(status_code=401, detail="unauthorized")
    if not valid_wallet(body.wallet):
        raise HTTPException(status_code=400, detail="bad wallet")
    _xp_add(body.wallet, week_key(), pvp_wins=1)
    return {"ok": True}


@app.get("/profile/{wallet}")
def profile(wallet: str):
    """Everything the profile page needs: lifetime totals, this week's XP,
    rank, and the projected share of this week's airdrop."""
    if not valid_wallet(wallet):
        raise HTTPException(status_code=400, detail="bad wallet")

    wk = week_key()
    totals = _xp_totals(wallet)
    nfts = wallet_nft_count(wallet)
    mult = nft_multiplier(nfts)

    board = weekly_board(wk, top_n=AIRDROP_TOP_N)
    me = next((r for r in board if r["wallet"] == wallet), None)

    # this week's raw earnings for this wallet (even if outside the top N)
    wk_rows = [r for r in _xp_rows(wk) if r.get("wallet") == wallet]
    wk_scars = sum(int(r.get("scars", 0)) for r in wk_rows)
    wk_wins = sum(int(r.get("pvp_wins", 0)) for r in wk_rows)
    wk_xp = compute_xp(wk_scars, wk_wins, nfts)

    pool_xp = sum(r["xp"] for r in board)
    share = (wk_xp / pool_xp) if (pool_xp > 0 and me) else 0.0
    projected_pct = round(share * AIRDROP_WEEKLY_PCT, 6)   # % of TOTAL supply

    return {
        "wallet": wallet,
        "week": wk,
        "nfts": nfts,
        "multiplier": round(mult, 2),
        "lifetime": {
            "scars": totals["scars"],
            "pvp_wins": totals["pvp_wins"],
            "runs": totals["runs"],
            "xp": compute_xp(totals["scars"], totals["pvp_wins"], nfts),
        },
        "week_stats": {
            "scars": wk_scars,
            "pvp_wins": wk_wins,
            "xp": wk_xp,
        },
        "rank": me["rank"] if me else None,
        "in_top_n": bool(me),
        "airdrop": {
            "top_n": AIRDROP_TOP_N,
            "weekly_pct_of_supply": round(AIRDROP_WEEKLY_PCT, 4),
            "your_share_of_pool": round(share, 6),
            "your_projected_pct_of_supply": projected_pct,
            "pool_xp": round(pool_xp, 2),
        },
        "formula": {
            "xp_per_scar": XP_PER_SCAR,
            "xp_per_pvp_win": XP_PER_PVP_WIN,
            "nft_bonus_each": XP_NFT_BONUS_EACH,
            "nft_bonus_max": XP_NFT_BONUS_MAX,
        },
    }


@app.get("/leaderboard/weekly")
def leaderboard_weekly(limit: int = AIRDROP_TOP_N):
    """This week's XP leaderboard — the set that shares this week's airdrop."""
    wk = week_key()
    board = weekly_board(wk, top_n=max(1, min(limit, 100)))
    pool_xp = sum(r["xp"] for r in board)
    for r in board:
        share = (r["xp"] / pool_xp) if pool_xp > 0 else 0.0
        r["share_of_pool"] = round(share, 6)
        r["projected_pct_of_supply"] = round(share * AIRDROP_WEEKLY_PCT, 6)
    return {
        "week": wk,
        "top_n": AIRDROP_TOP_N,
        "weekly_pct_of_supply": round(AIRDROP_WEEKLY_PCT, 4),
        "pool_xp": round(pool_xp, 2),
        "rows": board,
    }


# --------------------------------------------------------------------------- #
# SNAPSHOTS — freeze a week's results so a payout can't move under your feet
#
# Why this exists: the live leaderboard recomputes XP from CURRENT NFT holdings.
# If a player sells their NFTs after the week ends, their multiplier — and their
# rank — would change before you paid them. A snapshot freezes everything at the
# moment you take it: XP, NFT count, rank, share, and the exact % of supply owed.
# That frozen row is what you review, dispute against, and pay from.
# --------------------------------------------------------------------------- #
_mem_snapshots: Dict[str, Dict] = {}     # week -> snapshot dict (memory mode)


class AdminIn(BaseModel):
    secret: str


def _require_admin(secret: str):
    if not ADMIN_SECRET or secret != ADMIN_SECRET:
        raise HTTPException(status_code=401, detail="unauthorized")


def _snapshot_get(week: str) -> Optional[Dict]:
    if USE_SUPABASE:
        try:
            rows = (
                sb.table(SNAPSHOT_TABLE).select("*")
                .eq("week", week).eq("season", SEASON).limit(1).execute().data
            )
            if rows:
                r = rows[0]
                payload = r.get("payload")
                if isinstance(payload, str):
                    payload = json.loads(payload)
                return payload
        except Exception as e:
            print("snapshot_get error:", repr(e))
        return None
    return _mem_snapshots.get(week)


def _snapshot_put(week: str, payload: Dict):
    if USE_SUPABASE:
        try:
            sb.table(SNAPSHOT_TABLE).insert({
                "week": week, "season": SEASON,
                "payload": json.dumps(payload),
                "taken_at": int(time.time()),
            }).execute()
        except Exception as e:
            print("snapshot_put error:", repr(e))
        return
    _mem_snapshots[week] = payload


@app.post("/admin/snapshot/{week}")
def take_snapshot(week: str, body: AdminIn):
    """Freeze a week's top-N board. Idempotent: refuses to overwrite an existing
    snapshot, so you can't accidentally change a payout you've already published."""
    _require_admin(body.secret)

    if _snapshot_get(week):
        raise HTTPException(status_code=409, detail="snapshot already exists for that week")

    board = weekly_board(week, top_n=AIRDROP_TOP_N)
    pool_xp = sum(r["xp"] for r in board)

    rows = []
    for r in board:
        share = (r["xp"] / pool_xp) if pool_xp > 0 else 0.0
        rows.append({
            **r,
            "share_of_pool": round(share, 8),
            "pct_of_supply": round(share * AIRDROP_WEEKLY_PCT, 8),
        })

    payload = {
        "week": week,
        "season": SEASON,
        "taken_at": int(time.time()),
        "top_n": AIRDROP_TOP_N,
        "weekly_pct_of_supply": round(AIRDROP_WEEKLY_PCT, 6),
        "pool_xp": round(pool_xp, 2),
        "winners": len(rows),
        "rows": rows,
        "paid": False,
    }
    _snapshot_put(week, payload)
    return payload


@app.get("/admin/snapshot/{week}")
def read_snapshot(week: str, secret: str = ""):
    """Read a frozen snapshot — this is the list you review before paying."""
    _require_admin(secret)
    snap = _snapshot_get(week)
    if not snap:
        raise HTTPException(status_code=404, detail="no snapshot for that week")
    return snap


# --------------------------------------------------------------------------- #
# VESTING — turn a frozen snapshot into escrow transactions
#
# Each winner's prize is split into VEST_TRANCHES (default 4) equal parts that
# unlock one week apart. We hand back ready-to-sign EscrowCreate transactions;
# you sign them from the TREASURY wallet (never the issuer — the ledger rejects
# escrows sent by a token's own issuer).
#
# Times are in RIPPLE EPOCH seconds (since 2000-01-01), which is what XRPL wants.
# Every token escrow needs a CancelAfter; if it's never claimed, the tokens come
# back to the treasury rather than being stuck forever.
# --------------------------------------------------------------------------- #
def _ripple_time(unix_ts: float) -> int:
    return int(unix_ts - RIPPLE_EPOCH)


@app.post("/admin/vesting/{week}")
def vesting_plan(week: str, body: AdminIn):
    """Build the escrow transactions for a snapshotted week.

    Returns one EscrowCreate per (winner x tranche). Sign + submit them from the
    treasury wallet. Nothing is sent here — this only prepares the transactions.
    """
    _require_admin(body.secret)

    snap = _snapshot_get(week)
    if not snap:
        raise HTTPException(status_code=404, detail="take a snapshot for that week first")

    missing = [k for k, v in {
        "TOKEN_CURRENCY": TOKEN_CURRENCY,
        "TOKEN_ISSUER": TOKEN_ISSUER,
        "TREASURY_WALLET": TREASURY_WALLET,
    }.items() if not v]
    if missing or TOKEN_SUPPLY <= 0:
        raise HTTPException(
            status_code=400,
            detail=("set these env vars after launch: "
                    + ", ".join(missing + ([] if TOKEN_SUPPLY > 0 else ["TOKEN_SUPPLY"]))),
        )

    now = time.time()
    txs, plan = [], []
    total_tokens = 0.0

    for r in snap["rows"]:
        wallet = r["wallet"]
        pct = float(r["pct_of_supply"])              # % of TOTAL supply owed to this winner
        amount = TOKEN_SUPPLY * (pct / 100.0)        # -> token amount
        if amount <= 0:
            continue
        per = amount / VEST_TRANCHES
        total_tokens += amount

        tranches = []
        for i in range(1, VEST_TRANCHES + 1):
            finish_at = now + (VEST_INTERVAL_DAYS * 86400 * i)
            cancel_at = finish_at + (VEST_CANCEL_AFTER_DAYS * 86400)
            tx = {
                "TransactionType": "EscrowCreate",
                "Account": TREASURY_WALLET,
                "Destination": wallet,
                "Amount": {
                    "currency": TOKEN_CURRENCY,
                    "issuer": TOKEN_ISSUER,
                    "value": f"{per:.6f}",
                },
                "FinishAfter": _ripple_time(finish_at),
                "CancelAfter": _ripple_time(cancel_at),
            }
            txs.append(tx)
            tranches.append({
                "tranche": i,
                "amount": round(per, 6),
                "unlocks_at": int(finish_at),
                "expires_at": int(cancel_at),
            })

        plan.append({
            "wallet": wallet,
            "rank": r["rank"],
            "xp": r["xp"],
            "pct_of_supply": pct,
            "total_tokens": round(amount, 6),
            "tranches": tranches,
        })

    return {
        "week": week,
        "winners": len(plan),
        "tranches_each": VEST_TRANCHES,
        "interval_days": VEST_INTERVAL_DAYS,
        "total_tokens": round(total_tokens, 6),
        "treasury": TREASURY_WALLET,
        "note": ("Sign each EscrowCreate from the TREASURY wallet (not the issuer). "
                 "Winners need a trustline to the token before an escrow can be finished."),
        "plan": plan,
        "transactions": txs,
    }


@app.get("/vesting/{wallet}")
def my_vesting(wallet: str):
    """What a player is owed and when — powers the 'Your vesting' panel on the profile page."""
    if not valid_wallet(wallet):
        raise HTTPException(status_code=400, detail="bad wallet")

    out, total = [], 0.0
    weeks = list(_mem_snapshots.keys())
    if USE_SUPABASE:
        try:
            rows = sb.table(SNAPSHOT_TABLE).select("week").eq("season", SEASON).execute().data or []
            weeks = [r["week"] for r in rows]
        except Exception as e:
            print("vesting weeks error:", repr(e))
            weeks = []

    now = time.time()
    for wk in weeks:
        snap = _snapshot_get(wk)
        if not snap:
            continue
        row = next((r for r in snap["rows"] if r["wallet"] == wallet), None)
        if not row:
            continue
        amount = TOKEN_SUPPLY * (float(row["pct_of_supply"]) / 100.0) if TOKEN_SUPPLY > 0 else 0.0
        per = amount / VEST_TRANCHES if amount else 0.0
        taken = snap.get("taken_at", now)
        tranches = []
        for i in range(1, VEST_TRANCHES + 1):
            unlocks = taken + (VEST_INTERVAL_DAYS * 86400 * i)
            tranches.append({
                "tranche": i,
                "amount": round(per, 6),
                "unlocks_at": int(unlocks),
                "unlocked": now >= unlocks,
            })
        total += amount
        out.append({
            "week": wk,
            "rank": row["rank"],
            "pct_of_supply": row["pct_of_supply"],
            "total_tokens": round(amount, 6),
            "tranches": tranches,
        })

    return {"wallet": wallet, "total_tokens": round(total, 6), "weeks": out}
