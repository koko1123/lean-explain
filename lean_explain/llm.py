"""Minimal client for any OpenAI-compatible chat completions endpoint."""

import json
import os
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from pathlib import Path


@dataclass(frozen=True)
class LLMConfig:
    base_url: str
    model: str
    api_key: str | None = None
    extra_body: dict = field(default_factory=dict)


def load_env_file(path: Path) -> None:
    """Load KEY=VALUE lines into the environment without overriding existing variables."""
    if not path.exists():
        return
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        os.environ.setdefault(key.strip(), value.strip().strip("'\""))


VENICE_BASE_URL = "https://api.venice.ai/api/v1"
VENICE_MODEL = "deepseek-v4-1-flash-1017-ultrafast"
# Venice adds its own system prompt unless told not to.
VENICE_EXTRA_BODY = {"venice_parameters": {"include_venice_system_prompt": False}}


def make_config(
    base_url: str | None = None, model: str | None = None, extra_body: dict | None = None
) -> LLMConfig:
    """Build the config from explicit values, then the environment and .env.local, then Venice.

    VENICE_API_KEY is only ever sent to Venice. Other endpoints use LEAN_EXPLAIN_API_KEY,
    which is optional because local servers do not need one.
    """
    load_env_file(Path(".env.local"))
    base_url = (base_url or os.environ.get("LEAN_EXPLAIN_BASE_URL") or VENICE_BASE_URL).rstrip("/")
    is_venice = base_url == VENICE_BASE_URL
    model = model or os.environ.get("LEAN_EXPLAIN_MODEL") or (VENICE_MODEL if is_venice else None)
    if not model:
        raise SystemExit("Set the model with --model or LEAN_EXPLAIN_MODEL (see .env.example)")
    api_key = os.environ.get("LEAN_EXPLAIN_API_KEY")
    if not api_key and is_venice:
        api_key = os.environ.get("VENICE_API_KEY")
    if extra_body is None:
        from_env = os.environ.get("LEAN_EXPLAIN_EXTRA_BODY")
        extra_body = json.loads(from_env) if from_env else (VENICE_EXTRA_BODY if is_venice else {})
    return LLMConfig(base_url=base_url, model=model, api_key=api_key or None, extra_body=extra_body)


class BudgetExceeded(Exception):
    """Raised before a request that would start after the spending cap is reached."""


class Budget:
    """A spending cap in US dollars, enforced before each request.

    Prices are per million tokens. A model without a price is treated as free, which is
    right for a local server and means the cap only binds on priced endpoints.
    """

    def __init__(self, limit_usd: float, prices: dict[str, tuple[float, float]]):
        self.limit_usd = limit_usd
        self.prices = prices
        self.spent_usd = 0.0
        self.by_model: dict[str, dict] = {}

    def check(self) -> None:
        if self.spent_usd >= self.limit_usd:
            raise BudgetExceeded(
                f"Spending cap reached: ${self.spent_usd:.2f} of ${self.limit_usd:.2f}. "
                "Finished requests are cached, so a rerun with a higher --budget resumes."
            )

    def charge(self, model: str, usage: dict) -> None:
        price_in, price_out = self.prices.get(model, (0.0, 0.0))
        tokens_in, tokens_out = usage.get("prompt_tokens", 0), usage.get("completion_tokens", 0)
        cost = (tokens_in * price_in + tokens_out * price_out) / 1e6
        self.spent_usd += cost
        row = self.by_model.setdefault(model, {"calls": 0, "in": 0, "out": 0, "usd": 0.0})
        row["calls"] += 1
        row["in"] += tokens_in
        row["out"] += tokens_out
        row["usd"] += cost

    def report(self) -> str:
        """One line per model: calls, tokens in and out, and cost."""
        lines = [
            f"  {model}: {row['calls']} calls, {row['in']:,} tokens in, "
            f"{row['out']:,} out, ${row['usd']:.2f}"
            for model, row in self.by_model.items()
        ]
        return "\n".join([f"spent ${self.spent_usd:.2f} of ${self.limit_usd:.2f}", *lines])


def venice_prices() -> dict[str, tuple[float, float]]:
    """Input and output prices per million tokens for every Venice text model."""
    with urllib.request.urlopen(f"{VENICE_BASE_URL}/models", timeout=30) as response:
        models = json.load(response)["data"]
    prices = {}
    for model in models:
        pricing = model.get("model_spec", {}).get("pricing", {})
        if "input" in pricing and "output" in pricing:
            prices[model["id"]] = (pricing["input"]["usd"], pricing["output"]["usd"])
    return prices


def make_budget(limit_usd: float, configs: list[LLMConfig]) -> Budget:
    priced = any(config.base_url == VENICE_BASE_URL for config in configs)
    return Budget(limit_usd, venice_prices() if priced else {})


def chat(
    config: LLMConfig,
    system: str,
    user: str,
    schema: dict,
    budget: Budget | None = None,
    timeout: float = 3600.0,
) -> str:
    """Send one request and return the reply text, constrained to `schema` by the server."""
    if budget:
        budget.check()
    body = {
        **config.extra_body,
        "model": config.model,
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ],
        "response_format": {
            "type": "json_schema",
            "json_schema": {"name": "reply", "strict": True, "schema": schema},
        },
    }
    headers = {"Content-Type": "application/json"}
    if config.api_key:
        headers["Authorization"] = f"Bearer {config.api_key}"
    request = urllib.request.Request(
        f"{config.base_url}/chat/completions", data=json.dumps(body).encode(), headers=headers
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            payload = json.load(response)
    except urllib.error.HTTPError as error:
        detail = error.read().decode(errors="replace")[:500]
        raise SystemExit(f"{config.base_url} returned HTTP {error.code}: {detail}") from error
    if budget:
        budget.charge(config.model, payload.get("usage", {}))
    return payload["choices"][0]["message"]["content"]
