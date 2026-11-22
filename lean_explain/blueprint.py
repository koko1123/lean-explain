"""Read reference statements and proofs from a leanblueprint LaTeX source.

A blueprint tags each informal result with the Lean declarations that formalize it:

    \\begin{lemma}[Title]\\label{foo}\\lean{decl_name}\\leanok
      statement
    \\end{lemma}
    \\begin{proof}\\uses{bar}\\leanok
      proof
    \\end{proof}
"""

import re
from dataclasses import dataclass
from pathlib import Path

RESULT = re.compile(
    r"\\begin\{(lemma|theorem|proposition|corollary)\}(.*?)\\end\{\1\}"
    r"(?:\s*\\begin\{proof\}(.*?)\\end\{proof\})?",
    re.DOTALL,
)
LEAN_TAG = re.compile(r"\\lean\{([^}]*)\}")
MARKUP = re.compile(r"\\(?:label|lean|uses|proves)\{[^}]*\}|\\leanok|\\notready|\\mathlibok")


@dataclass
class Entry:
    kind: str
    lean: list[str]
    statement: str
    proof: str | None


def clean(text: str) -> str:
    text = MARKUP.sub("", text)
    text = re.sub(r"\A\s*\[[^\]]*\]", "", text)
    return "\n".join(line.strip() for line in text.strip().splitlines() if line.strip())


def parse(text: str) -> list[Entry]:
    text = re.sub(r"(?<!\\)%.*", "", text)
    entries = []
    for match in RESULT.finditer(text):
        kind, body, proof = match.groups()
        names = [n.strip() for tag in LEAN_TAG.findall(body) for n in tag.split(",") if n.strip()]
        if names:
            entries.append(Entry(kind, names, clean(body), clean(proof) if proof else None))
    return entries


def load(path: Path) -> dict[str, Entry]:
    """Map each Lean declaration name to the first blueprint result that cites it."""
    files = sorted(path.rglob("*.tex")) if path.is_dir() else [path]
    by_name: dict[str, Entry] = {}
    for file in files:
        for entry in parse(file.read_text()):
            for name in entry.lean:
                by_name.setdefault(name, entry)
    return by_name
