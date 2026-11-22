"""Command line entry point."""

import argparse
import json
import subprocess
from dataclasses import asdict
from pathlib import Path

from lean_explain import assemble, blueprint, evaluate, explain, extract, html, llm

VENICE_JUDGE_MODEL = "gemini-4-carbon"


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


def make_chat(config: llm.LLMConfig, cache: Path) -> explain.Chat:
    return explain.cached_chat(
        lambda system, user, schema: llm.chat(config, system, user, schema),
        config.model,
        cache / "llm",
    )


def run_explain(args: argparse.Namespace, cache: Path) -> None:
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

    config = llm.make_config(args.base_url, args.model, args.extra_body)
    explanations = explain.explain_plan(plan, make_chat(config, cache), args.max_chars)
    # One directory per model, so a run with another model never overwrites this one.
    out = args.out / config.model.replace("/", "_")
    out.mkdir(parents=True, exist_ok=True)
    (out / f"{args.decl}.md").write_text(assemble.render_markdown(plan, explanations))
    (out / f"{args.decl}.html").write_text(html.render_html(plan, explanations))
    side = assemble.sidecar(plan, explanations, config.model)
    (out / f"{args.decl}.json").write_text(json.dumps(side, ensure_ascii=False, indent=2))
    with (out / "pairs.jsonl").open("a") as handle:
        handle.write(assemble.pairs_jsonl(plan, explanations))
    print(f"wrote {out / f'{args.decl}.md'} and .html (grounding {side['grounding']:.0%})")


def run_eval(args: argparse.Namespace, cache: Path) -> None:
    """Explain every theorem of a module that the blueprint covers, then judge each one."""
    reference = blueprint.load(args.blueprint)
    decls = extract.extract_module(args.project, args.repl, args.module, cache)
    targets = [d for d in decls if d.kind == "theorem" and d.name in reference]
    if not targets:
        raise SystemExit(f"no theorem in {args.module} is tagged in {args.blueprint}")
    print(f"evaluating {len(targets)}: {', '.join(d.name for d in targets)}")

    def cited_for(decl: extract.Decl) -> dict[str, dict]:
        plan = explain.make_plan(
            decl.name,
            args.module,
            0,
            lambda module: decls if module == args.module else [],
            lambda module: extract.statements(args.project, module, cache),
        )
        return plan.cited

    config = llm.make_config(args.base_url, args.model, args.extra_body)
    explanations = explain.explain_in_order(
        targets, cited_for, make_chat(config, cache), args.max_chars
    )
    judge_config = llm.make_config(args.base_url, args.judge_model, args.extra_body)
    judge_chat = make_chat(judge_config, cache)
    verdicts = [evaluate.judge(reference[e.name], e, judge_chat) for e in explanations]

    for verdict, explanation in zip(verdicts, explanations, strict=True):
        coverage = "n/a" if verdict.coverage is None else f"{verdict.coverage:.0%}"
        print(
            f"  {verdict.name}: statement {verdict.statement_verdict}, coverage {coverage}, "
            f"errors {len(verdict.errors)}, grounding {explanation.grounding:.0%}"
        )
    summary = evaluate.summarize(verdicts, explanations)
    report = {
        "module": args.module,
        "generator": config.model,
        "judge": judge_config.model,
        "prompt_version": explain.PROMPT_VERSION,
        "judge_version": evaluate.JUDGE_VERSION,
        "summary": summary,
        "results": [
            {**asdict(v), "coverage": v.coverage, "explanation": asdict(e)}
            for v, e in zip(verdicts, explanations, strict=True)
        ],
    }
    out = args.out / config.model.replace("/", "_")
    out.mkdir(parents=True, exist_ok=True)
    path = out / f"eval-{args.module}.json"
    path.write_text(json.dumps(report, ensure_ascii=False, indent=2))
    print(json.dumps(summary))
    print(f"wrote {path}")


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
        ("eval", "explain a module's blueprint-tagged theorems and score them with a judge"),
    ):
        cmd = commands.add_parser(name, help=text)
        cmd.add_argument("--project", type=Path, required=True)
        cmd.add_argument("--repl", type=Path, required=True)
        cmd.add_argument("--module", required=True)
        if name == "extract":
            continue
        cmd.add_argument("--out", type=Path, default=Path("out"))
        cmd.add_argument("--base-url", help="OpenAI-compatible endpoint, e.g. a local server")
        cmd.add_argument("--model")
        cmd.add_argument("--extra-body", type=json.loads, help="JSON merged into each request body")
        cmd.add_argument(
            "--max-chars",
            type=int,
            default=200_000,
            help="tactic record size per request; lower it for small context windows",
        )
    explain_cmd = commands.choices["explain"]
    explain_cmd.add_argument("--decl", required=True)
    explain_cmd.add_argument("--depth", type=int, default=1)
    explain_cmd.add_argument(
        "--dry-run", action="store_true", help="print the plan and stop before calling the model"
    )
    eval_cmd = commands.choices["eval"]
    eval_cmd.add_argument(
        "--blueprint", type=Path, required=True, help="a blueprint .tex file or directory"
    )
    eval_cmd.add_argument("--judge-model", default=VENICE_JUDGE_MODEL)

    args = parser.parse_args()
    if args.command == "fetch":
        fetch(args.url, args.rev, args.workspace)
        return

    cache = args.project / ".lean-explain"
    if args.command == "extract":
        root = args.module.split(".")[0]
        for decl in extract.extract_module(args.project, args.repl, args.module, cache):
            deps = sorted({d.name for d in decl.deps if d.module.split(".")[0] == root})
            print(
                f"{decl.kind:8} {decl.name}  lines {decl.line}-{decl.end_line}  "
                f"tactics={len(decl.steps)}  project deps={len(deps)}"
            )
    elif args.command == "explain":
        run_explain(args, cache)
    else:
        run_eval(args, cache)
