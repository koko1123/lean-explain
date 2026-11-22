"""Minimal client for any OpenAI-compatible chat completions endpoint."""

import json
import os
import urllib.request
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class LLMConfig:
    base_url: str
    model: str
    api_key: str


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


def config_from_env() -> LLMConfig:
    load_env_file(Path(".env.local"))
    missing = [
        name
        for name in ("LEAN_EXPLAIN_BASE_URL", "LEAN_EXPLAIN_MODEL", "LEAN_EXPLAIN_API_KEY")
        if not os.environ.get(name)
    ]
    if missing:
        raise SystemExit(f"Missing environment variables: {', '.join(missing)} (see .env.example)")
    return LLMConfig(
        base_url=os.environ["LEAN_EXPLAIN_BASE_URL"].rstrip("/"),
        model=os.environ["LEAN_EXPLAIN_MODEL"],
        api_key=os.environ["LEAN_EXPLAIN_API_KEY"],
    )


def chat(config: LLMConfig, system: str, user: str, timeout: float = 300.0) -> str:
    body = {
        "model": config.model,
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ],
    }
    request = urllib.request.Request(
        f"{config.base_url}/chat/completions",
        data=json.dumps(body).encode(),
        headers={
            "Authorization": f"Bearer {config.api_key}",
            "Content-Type": "application/json",
        },
    )
    with urllib.request.urlopen(request, timeout=timeout) as response:
        payload = json.load(response)
    return payload["choices"][0]["message"]["content"]
