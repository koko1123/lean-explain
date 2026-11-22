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
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            payload = json.load(response)
    except urllib.error.HTTPError as error:
        detail = error.read().decode(errors="replace")[:500]
        raise SystemExit(f"{config.base_url} returned HTTP {error.code}: {detail}") from error
    return payload["choices"][0]["message"]["content"]
