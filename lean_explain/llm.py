"""Minimal client for any OpenAI-compatible chat completions endpoint."""

import json
import os
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


def make_config(
    base_url: str | None = None, model: str | None = None, extra_body: dict | None = None
) -> LLMConfig:
    """Build the config from explicit values, falling back to the environment and .env.local.

    The API key is optional because local servers do not need one.
    """
    load_env_file(Path(".env.local"))
    base_url = base_url or os.environ.get("LEAN_EXPLAIN_BASE_URL")
    model = model or os.environ.get("LEAN_EXPLAIN_MODEL")
    if not base_url or not model:
        raise SystemExit(
            "Set the endpoint and model with --base-url and --model, or with "
            "LEAN_EXPLAIN_BASE_URL and LEAN_EXPLAIN_MODEL (see .env.example)"
        )
    return LLMConfig(
        base_url=base_url.rstrip("/"),
        model=model,
        api_key=os.environ.get("LEAN_EXPLAIN_API_KEY") or None,
        extra_body=extra_body or json.loads(os.environ.get("LEAN_EXPLAIN_EXTRA_BODY") or "{}"),
    )


def chat(config: LLMConfig, system: str, user: str, timeout: float = 3600.0) -> str:
    body = {
        **config.extra_body,
        "model": config.model,
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ],
    }
    headers = {"Content-Type": "application/json"}
    if config.api_key:
        headers["Authorization"] = f"Bearer {config.api_key}"
    request = urllib.request.Request(
        f"{config.base_url}/chat/completions", data=json.dumps(body).encode(), headers=headers
    )
    with urllib.request.urlopen(request, timeout=timeout) as response:
        payload = json.load(response)
    return payload["choices"][0]["message"]["content"]
