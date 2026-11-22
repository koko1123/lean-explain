"""Ground term-mode proofs with term goals from the Lean language server.

A proof written as a term has no tactics, so the REPL's tactic record is empty for it. The
language server can still say what type Lean expected at any position in the term. This
module asks for that at the start of each line of the proof body, through leanclient, and
stores the answers as steps so the rest of the pipeline treats them like a tactic record.
"""

import hashlib
import json
import os
from pathlib import Path
from typing import Protocol

from lean_explain.extract import Decl, Step, lake_env, module_path

OPENERS, CLOSERS = "([{⟨", ")]}⟩"


class FileClient(Protocol):
    def get_term_goal(self, line: int, character: int) -> dict | None: ...


def body_start(decl: Decl) -> tuple[int, int] | None:
    """Line and column where the proof body begins: just after the first top-level `:=`.

    Binders such as `(h : a := b)` are skipped by tracking bracket depth, and a leading
    doc comment is skipped because it can contain anything.
    """
    depth = 0
    in_doc = False
    for offset, text in enumerate(decl.source.splitlines()):
        index = 0
        while index < len(text):
            if in_doc:
                end = text.find("-/", index)
                if end < 0:
                    break
                in_doc, index = False, end + 2
                continue
            if text.startswith("/-", index):
                in_doc, index = True, index + 2
                continue
            if text.startswith("--", index):
                break
            char = text[index]
            if char in OPENERS:
                depth += 1
            elif char in CLOSERS:
                depth -= 1
            elif depth == 0 and text.startswith(":=", index):
                rest = text[index + 2 :]
                if rest.strip():
                    return decl.line + offset, index + 2 + len(rest) - len(rest.lstrip())
                return decl.line + offset + 1, 0
            index += 1
    return None


def term_steps(client: FileClient, decl: Decl) -> list[Step]:
    """One step per line of the proof body, holding the type Lean expected at its start."""
    start = body_start(decl)
    if start is None:
        return []
    lines = decl.source.splitlines()
    steps = []
    for line in range(start[0], decl.end_line + 1):
        text = lines[line - decl.line]
        col = start[1] if line == start[0] and start[1] else len(text) - len(text.lstrip())
        if not text[col:].strip():
            continue
        reply = client.get_term_goal(line - 1, col)
        if reply and reply.get("goal"):
            steps.append(
                Step(
                    tactic=text[col:].rstrip(),
                    goals=reply["goal"],
                    line=line,
                    col=col,
                    end_line=line,
                    end_col=len(text),
                )
            )
    return steps


def fill(project: Path, decls: list[Decl], cache_dir: Path) -> None:
    """Give every term-mode theorem in `decls` its term goals, opening each file once."""
    by_module: dict[str, list[Decl]] = {}
    for decl in decls:
        if decl.kind == "theorem" and not decl.steps:
            by_module.setdefault(decl.module, []).append(decl)
    for module, wanted in by_module.items():
        source = module_path(project, module)
        digest = hashlib.sha256(source.read_bytes()).hexdigest()[:16]
        cached = cache_dir / f"{module}.{digest}.termgoals.json"
        known: dict[str, list[dict]] = json.loads(cached.read_text()) if cached.exists() else {}
        missing = [decl for decl in wanted if decl.name not in known]
        if missing:
            import leanclient

            os.environ["PATH"] = lake_env()["PATH"]
            client = leanclient.LeanLSPClient(str(project.resolve()), initial_build=False)
            try:
                file_client = client.create_file_client(str(source.relative_to(project)))
                file_client.open_file()
                for decl in missing:
                    known[decl.name] = [vars(step) for step in term_steps(file_client, decl)]
            finally:
                client.close()
            cache_dir.mkdir(parents=True, exist_ok=True)
            cached.write_text(json.dumps(known))
        for decl in wanted:
            decl.steps = [Step(**step) for step in known[decl.name]]
            decl.term_mode = bool(decl.steps)
