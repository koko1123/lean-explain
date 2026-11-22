"""Command line entry point."""

import argparse
import json
import subprocess
from pathlib import Path

from lean_explain import assemble, explain, extract, llm


def fetch(url: str, rev: str | None, workspace: Path) -> None:
    """Clone a Lean project, fetch its Mathlib cache, and build the REPL for its toolchain."""
    env = extract.lake_env()
    project = workspace / url.rstrip("/").removesuffix(".git").split("/")[-1]
    if not project.exists():
        subprocess.run(["git", "clone", url, str(project)], check=True)
    if rev:
        subprocess.run(["git", "checkout", rev], cwd=project, check=True)
    manifest = project / "lake-manifest.json"
    if manifest.exists() and '"mathlib"' in manifest.read_text():
        subprocess.run(["lake", "exe", "cache", "get"], cwd=project, env=env, check=True)
    toolchain = (project / "lean-toolchain").read_text().strip().split(":")[-1]
    repl = workspace / f"repl-{toolchain}"
    if not repl.exists():
        subprocess.run(
            [
                "git",
                "clone",
                "--depth",
                "1",
                "--branch",
                toolchain,
                "https://github.com/leanprover-community/repl",
                str(repl),
            ],
            check=True,
        )
    subprocess.run(["lake", "build"], cwd=repl, env=env, check=True)
    print(f"project: {project}\nrepl:    {repl / '.lake/build/bin/repl'}")


def main() -> None:
    parser = argparse.ArgumentParser(prog="lean-explain")
    commands = parser.add_subparsers(dest="command", required=True)

    fetch_cmd = commands.add_parser("fetch", help="clone a Lean project and build its REPL")
    fetch_cmd.add_argument("url")
    fetch_cmd.add_argument("--rev")
    fetch_cmd.add_argument("--workspace", type=Path, default=Path("workspace"))

    for name, text in (
        ("extract", "list a module's declarations, tactic counts, and project dependencies"),
        ("explain", "explain one declaration and the project lemmas it uses"),
    ):
        cmd = commands.add_parser(name, help=text)
        cmd.add_argument("--project", type=Path, required=True)
        cmd.add_argument("--repl", type=Path, required=True)
        cmd.add_argument("--module", required=True)
    explain_cmd = commands.choices["explain"]
    explain_cmd.add_argument("--decl", required=True)
    explain_cmd.add_argument("--depth", type=int, default=1)
    explain_cmd.add_argument("--out", type=Path, default=Path("out"))
    explain_cmd.add_argument(
        "--dry-run", action="store_true", help="print the plan and stop before calling the model"
    )

    args = parser.parse_args()
    if args.command == "fetch":
        fetch(args.url, args.rev, args.workspace)
        return

    cache = args.project / ".lean-explain"
    root = args.module.split(".")[0]
    if args.command == "extract":
        for decl in extract.extract_module(args.project, args.repl, args.module, cache):
            deps = sorted({d.name for d in decl.deps if d.module.split(".")[0] == root})
            print(
                f"{decl.kind:8} {decl.name}  lines {decl.line}-{decl.end_line}  "
                f"tactics={len(decl.steps)}  project deps={len(deps)}"
            )
        return

    plan = explain.make_plan(
        args.decl,
        args.module,
        args.depth,
        lambda module: extract.extract_module(args.project, args.repl, module, cache),
        lambda module: extract.statements(args.project, module, cache),
    )
    print(f"explain ({len(plan.order)}): {', '.join(d.name for d in plan.order)}")
    print(f"cite    ({len(plan.cited)}): {', '.join(plan.cited)}")
    if args.dry_run:
        return

    config = llm.config_from_env()
    chat = explain.cached_chat(
        lambda system, user: llm.chat(config, system, user), config.model, cache / "llm"
    )
    explanations = explain.explain_plan(plan, chat)
    args.out.mkdir(parents=True, exist_ok=True)
    stem = args.decl.replace("/", "_")
    (args.out / f"{stem}.md").write_text(assemble.render_markdown(plan, explanations))
    side = assemble.sidecar(plan, explanations, config.model)
    (args.out / f"{stem}.json").write_text(json.dumps(side, ensure_ascii=False, indent=2))
    with (args.out / "pairs.jsonl").open("a") as handle:
        handle.write(assemble.pairs_jsonl(plan, explanations))
    print(f"wrote {args.out / f'{stem}.md'} (grounding {side['grounding']:.0%})")
