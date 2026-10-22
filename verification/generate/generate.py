#!/usr/bin/env python3
"""Regenerate the statement specification `verification/Spec*` and `comparator.json`.

Run from the repository root after `lake build`:

    python3 verification/generate/generate.py

Steps:
1. `TrustedBase.lean` lists the declarations the checked results depend on (the checked results
   are every theorem in a `Theorems` module and in `ParabolicRectifiability.Main`). The seeds
   are extended, repeatedly, by the owner of every auxiliary proof or matcher (`foo._proof_1`, `foo.match_1`) that a listed declaration
   uses: Lean shares such auxiliary constants within a file, so their owner must be present for
   the copies to elaborate to identical terms.
2. For every library module containing a listed declaration, `verification/Spec/<same path>` is
   written: the module's Mathlib imports, the scoping commands (`namespace`, `section`, `open`,
   `variable`, ...), and the source of each listed declaration with its docstring, in the original
   order; proofs of theorems and of `Prop`-valued instances are replaced by `sorry`.
3. `verification/Spec.lean` imports them all, and `comparator.json` lists every theorem of the
   specification.

The command used to run Lean can be changed with the environment variable `SPEC_LEAN`
(default: `lake env lean`).
"""
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
from collections import defaultdict

ROOT = os.getcwd()
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = shlex.split(os.environ.get("SPEC_LEAN", "lake env lean"))
AUX = re.compile(r"\._(proof|match|eq|unfold|sunfold|cstage|spec)|\.match_\d|\.proof_\d")
SCOPE = re.compile(r"^(noncomputable section|section\b|namespace\b|end\b|open\b|variable\b|universe\b|"
                   r"local notation\b|notation\b|scoped notation\b|local infix|infix|"
                   r"attribute \[local|attribute \[scoped|set_option\b(?!.*\bin\s*$))")


def path(mod):
    return os.path.join(ROOT, mod.replace(".", "/") + ".lean")


def imports(mod):
    return [m.group(1) for l in open(path(mod), encoding="utf-8")
            if (m := re.match(r"\s*import\s+(\S+)", l))]


def closure(mods):
    seen, stack = set(), list(mods)
    while stack:
        m = stack.pop()
        if m not in seen:
            seen.add(m)
            stack += [i for i in imports(m) if i.startswith("ParabolicRectifiability")]
    return seen


def trusted_base(seeds_file):
    env = dict(os.environ, TRUSTED_EXTRA_SEEDS=seeds_file)
    out = subprocess.run(LEAN + [os.path.join(HERE, "TrustedBase.lean")], env=env, cwd=ROOT,
                         capture_output=True, text=True)
    if out.returncode != 0:
        sys.exit("TrustedBase.lean failed:\n" + out.stderr[-2000:] + out.stdout[-2000:])
    return [l.split("\t") for l in out.stdout.splitlines() if l.count("\t") == 4]


def compute_trusted():
    tmp = tempfile.mkdtemp()
    seeds = os.path.join(tmp, "seeds.txt")
    open(seeds, "w").close()
    seed_list = []
    while True:
        open(seeds, "w").write("\n".join(seed_list) + "\n")
        rows = trusted_base(seeds)
        names = {r[0] for r in rows}
        owners = sorted({m.group(1) for r in rows if (m := re.match(r"(.*?)\.(_proof_\d+|match_\d+)$", r[0]))
                         and m.group(1) not in names and m.group(1) not in seed_list})
        if not owners:
            break
        seed_list += owners
    return [r for r in rows if not AUX.search(r[0]) and r[3] != "0"]


def spec_name(mod):
    return "Spec." + mod[len("ParabolicRectifiability."):]


def write_spec(rows):
    by_mod = defaultdict(list)
    for name, kind, mod, a, b in rows:
        by_mod[mod].append((int(a), int(b), name, kind))
    order, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for i in imports(m):
            if i.startswith("ParabolicRectifiability"):
                visit(i)
        if m in by_mod:
            order.append(m)

    for m in sorted(by_mod):
        visit(m)
    for d, _, fs in os.walk(os.path.join(ROOT, "verification/Spec"), topdown=False):
        for f in fs:
            os.remove(os.path.join(d, f))
        os.rmdir(d)
    for mod in order:
        clo = closure([mod])
        spec_imports = sorted(spec_name(x) for x in clo if x in by_mod and x != mod)
        mlib = sorted({i for x in clo if x not in by_mod or x == mod for i in imports(x)
                       if not i.startswith("ParabolicRectifiability")})
        parts = [f"import {i}" for i in mlib + spec_imports]
        parts.append(f"\n/-! Specification: the definitions of `{mod}` used by the headline statements. -/\n")
        lines = open(path(mod), encoding="utf-8").read().split("\n")
        starts = {a: (b, name, kind) for a, b, name, kind in sorted(by_mod[mod])}
        i = 0
        while i < len(lines):
            line = lines[i]
            if i + 1 in starts:
                b, name, kind = starts[i + 1]
                j = i
                if i > 0 and lines[i - 1].rstrip().endswith("-/"):
                    j = i - 1
                    while j > 0 and not lines[j].lstrip().startswith("/--"):
                        j -= 1
                text = "\n".join(lines[j:b])
                kw = re.search(r"^(@\[[^\]]*\]\s*)?(theorem|lemma|instance) ", text, re.M)
                if kind == "theorem" and kw:
                    m = re.compile(r":=|\swhere[ \t]*$", re.M).search(text, kw.start())
                    text = text[:m.start()].rstrip() + " := by\n  sorry"
                parts += text.split("\n") + [""]
                i = b
                continue
            if SCOPE.match(line):
                parts.append(line)
                while i + 1 < len(lines) and lines[i + 1].startswith((" ", "\t")) and lines[i + 1].strip():
                    i += 1
                    parts.append(lines[i])
            i += 1
        f = os.path.join(ROOT, "verification", *spec_name(mod).split(".")) + ".lean"
        os.makedirs(os.path.dirname(f), exist_ok=True)
        open(f, "w", encoding="utf-8").write("\n".join(parts) + "\n")
    return [spec_name(m) for m in order]


ROOT_DOC = """
/-!
# Statement specification

Every definition that the public results of the library depend on, and the statements of
those results (every theorem in a `Theorems/` folder and in `Main.lean`), copied from the
library with proofs replaced by `sorry`. One file in `Spec/` per library module, so that Lean
elaborates them exactly as in the library. `lake comparator` (see `comparator.json`) checks
that the library proves exactly these statements, using only the standard axioms.
Generated by `verification/generate/generate.py`.
-/
"""


def main():
    rows = compute_trusted()
    mods = write_spec(rows)
    open(os.path.join(ROOT, "verification/Spec.lean"), "w").write(
        "\n".join("import " + m for m in mods) + "\n" + ROOT_DOC)
    theorems = sorted(r[0] for r in rows if r[1] == "theorem")
    cfg = {"challenge_module": "Spec", "solution_module": "ParabolicRectifiability",
           "theorem_names": theorems, "definition_names": [],
           "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
           "external_kernels": {"nanoda": ["nanoda_bin"]}}
    json.dump(cfg, open(os.path.join(ROOT, "comparator.json"), "w"), indent=2)
    if os.environ.get("SPEC_TRUSTED_OUT"):
        open(os.environ["SPEC_TRUSTED_OUT"], "w").write("".join("\t".join(r) + "\n" for r in rows))
    print(f"{len(rows)} declarations in {len(mods)} specification modules; {len(theorems)} theorems")


if __name__ == "__main__":
    main()
