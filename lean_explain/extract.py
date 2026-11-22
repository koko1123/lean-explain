"""Extract declarations, dependencies, and per-tactic goal states from a built Lean module."""

import hashlib
import json
import os
import shutil
import subprocess
import tempfile
from dataclasses import asdict, dataclass, field
from importlib import resources
from pathlib import Path


@dataclass
class Step:
    tactic: str
    goals: str
    line: int
    col: int
    end_line: int
    end_col: int


@dataclass
class Dep:
    name: str
    module: str


@dataclass
class Decl:
    name: str
    kind: str
    type: str
    doc: str | None
    module: str
    line: int
    end_line: int
    source: str
    deps: list[Dep] = field(default_factory=list)
    steps: list[Step] = field(default_factory=list)


def decl_from_dict(data: dict) -> Decl:
    return Decl(
        **{k: v for k, v in data.items() if k not in ("deps", "steps")},
        deps=[Dep(**d) for d in data["deps"]],
        steps=[Step(**s) for s in data["steps"]],
    )


def lake_env() -> dict[str, str]:
    """The process environment with elan's bin directory on PATH."""
    env = dict(os.environ)
    if shutil.which("lake") is None:
        env["PATH"] = f"{Path.home() / '.elan' / 'bin'}{os.pathsep}{env.get('PATH', '')}"
    return env


def module_path(project: Path, module: str) -> Path:
    return project / (module.replace(".", "/") + ".lean")


def run_repl(project: Path, repl: Path, source: Path) -> list[dict]:
    """Elaborate `source` in the project's environment and return one record per tactic."""
    command = json.dumps({"path": str(source.resolve()), "allTactics": True})
    result = subprocess.run(
        ["lake", "env", str(repl.resolve())],
        input=command,
        capture_output=True,
        text=True,
        cwd=project,
        env=lake_env(),
        check=True,
    )
    response = json.loads(result.stdout)
    errors = [m for m in response.get("messages", []) if m.get("severity") == "error"]
    if errors:
        raise RuntimeError(f"{source} does not compile: {errors[0].get('data', '')[:500]}")
    return response.get("tactics", [])


def dump_declarations(project: Path, module: str) -> list[dict]:
    """Return name, kind, statement, source range, and dependencies for a module's declarations."""
    template = resources.files("lean_explain").joinpath("Dump.lean.tmpl").read_text()
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / "decls.json"
        script = Path(tmp) / "Dump.lean"
        script.write_text(template.replace("__MODULE__", module).replace("__OUT__", str(out)))
        result = subprocess.run(
            ["lake", "env", "lean", str(script)],
            capture_output=True,
            text=True,
            cwd=project,
            env=lake_env(),
        )
        if result.returncode != 0 or not out.exists():
            raise RuntimeError(f"declaration dump failed for {module}:\n{result.stdout[-2000:]}")
        return json.loads(out.read_text())


def assign_steps(decls: list[dict], tactics: list[dict]) -> dict[str, list[Step]]:
    """Attach each tactic to the innermost declaration whose source range contains it."""
    steps: dict[str, list[Step]] = {d["name"]: [] for d in decls}
    for tactic in sorted(tactics, key=lambda t: (t["pos"]["line"], t["pos"]["column"])):
        line = tactic["pos"]["line"]
        owners = [d for d in decls if d["line"] <= line <= d["endLine"]]
        if not owners:
            continue
        owner = min(owners, key=lambda d: d["endLine"] - d["line"])
        steps[owner["name"]].append(
            Step(
                tactic=tactic["tactic"],
                goals=tactic["goals"],
                line=line,
                col=tactic["pos"]["column"],
                end_line=tactic["endPos"]["line"],
                end_col=tactic["endPos"]["column"],
            )
        )
    return steps


def build_decls(
    module: str, source_text: str, decls: list[dict], tactics: list[dict]
) -> list[Decl]:
    lines = source_text.splitlines()
    steps = assign_steps(decls, tactics)
    return [
        Decl(
            name=d["name"],
            kind=d["kind"],
            type=d["type"],
            doc=d["doc"],
            module=module,
            line=d["line"],
            end_line=d["endLine"],
            source="\n".join(lines[d["line"] - 1 : d["endLine"]]),
            deps=[Dep(**dep) for dep in d["deps"]],
            steps=steps[d["name"]],
        )
        for d in sorted(decls, key=lambda d: d["line"])
    ]


def dump_cached(project: Path, module: str, cache_dir: Path) -> list[dict]:
    """Declarations of a module without tactic steps; fast, and enough to cite a result."""
    digest = hashlib.sha256(module_path(project, module).read_bytes()).hexdigest()[:16]
    cached = cache_dir / f"{module}.{digest}.decls.json"
    if cached.exists():
        return json.loads(cached.read_text())
    subprocess.run(["lake", "build", module], cwd=project, env=lake_env(), check=True)
    decls = dump_declarations(project, module)
    cache_dir.mkdir(parents=True, exist_ok=True)
    cached.write_text(json.dumps(decls))
    return decls


def statements(project: Path, module: str, cache_dir: Path) -> list[dict]:
    """Declarations of a module with their source text attached, for citing by statement."""
    lines = module_path(project, module).read_text().splitlines()
    return [
        {**d, "source": "\n".join(lines[d["line"] - 1 : d["endLine"]])}
        for d in dump_cached(project, module, cache_dir)
    ]


def extract_module(project: Path, repl: Path, module: str, cache_dir: Path) -> list[Decl]:
    """Extract one module, reusing the cached record when the source file is unchanged."""
    source = module_path(project, module)
    source_text = source.read_text()
    digest = hashlib.sha256(source_text.encode()).hexdigest()[:16]
    cached = cache_dir / f"{module}.{digest}.json"
    if cached.exists():
        return [decl_from_dict(d) for d in json.loads(cached.read_text())]
    raw = dump_cached(project, module, cache_dir)
    decls = build_decls(module, source_text, raw, run_repl(project, repl, source))
    cached.write_text(json.dumps([asdict(d) for d in decls]))
    return decls
