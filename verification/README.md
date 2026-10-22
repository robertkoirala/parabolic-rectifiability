# Verification

This folder contains the statement specification of the library and an axiom audit. Together with
an ordinary build they give three independent checks. All commands are run from the repository
root after building (see the main [README](../README.md#building)).

## 1. Build

```sh
lake build
```

Compiles every module of the library; Lean's kernel checks every proof. The build produces no
errors and no warnings.

## 2. Axiom audit

```sh
lake env lean verification/AxiomAudit.lean
```

[`AxiomAudit.lean`](AxiomAudit.lean) computes the axioms used by every declaration defined in a
`ParabolicRectifiability` module (all of them, not only the public results) and fails if any
declaration uses an axiom other than `propext`, `Classical.choice` and `Quot.sound`. A `sorry`
anywhere in the library would appear as the axiom `sorryAx` and make the audit fail. Expected
output:

```
Axiom audit passed: 14534 declarations; all axioms among [propext, Classical.choice, Quot.sound].
```

## 3. Comparator

The audit shows that the proofs are complete; it does not show that the theorems say what they are
claimed to say. For that, a reader has to read the statements and the definitions they use. The
specification collects exactly that material:

- [`Spec.lean`](Spec.lean) imports [`Spec/`](Spec), which has one file per library module that
  contains a definition or a result needed, at the same relative path (for example
  `ParabolicRectifiability/Foundations/ADR.lean` and `verification/Spec/Foundations/ADR.lean`).
- Each file contains, copied from the library module, the definitions that the checked results
  depend on (unchanged), and the statements of the checked results with their proofs replaced by
  `sorry`. The checked results are every theorem in a `Theorems/` folder and in `Main.lean`; see
  [docs/theorems.md](../docs/theorems.md). A few instances and elementary facts needed for the
  definitions to elaborate (for example second-countability of model spaces) are also stated with
  `sorry`.
- The specification imports only Mathlib, never the library.

[Comparator](https://github.com/leanprover/comparator) is built into Lake. With the configuration
[`comparator.json`](../comparator.json) it builds the specification (the *challenge*) and the
library (the *solution*), exports both, and checks that

1. every statement listed in `comparator.json` has exactly the same type in both;
2. every definition those statements depend on is identical in both, so the library proves the
   statements about the same objects that the specification defines;
3. the library's proofs use only `propext`, `Classical.choice` and `Quot.sound`;
4. the exported proofs are accepted by Lean's kernel and by the independent type checker
   [nanoda](https://github.com/ammkrn/nanoda_lib) (listed under `external_kernels`).

```sh
lake comparator                            # Linux
lake comparator --inadvisably-no-sandbox   # macOS
```

A successful run ends with

```
nanoda kernel accepts the solution
Lean default kernel accepts the solution
Your solution is okay!
```

On Linux, Comparator builds and exports the code inside a `bubblewrap` sandbox (install the
`bubblewrap` package), so that the code being judged cannot interfere with the checker. The sandbox
does not exist on macOS; there the flag `--inadvisably-no-sandbox` runs the same checks without that
isolation. The [Comparator workflow](../.github/workflows/comparator.yml) runs the sandboxed check on Linux.

Comparator detects changes: altering a hypothesis of a statement in the specification (for example
`1 ≤ n` to `2 ≤ n` in `rectifiable_reifenberg`) or the definition of parabolic Hausdorff measure
makes it reject the library.

## What the checks do not establish

- That the definitions formalize the intended mathematics. This is the part a reader must review;
  [docs/definitions.md](../docs/definitions.md) lists the definitions with their meaning, and
  [docs/overview.md](../docs/overview.md) discusses the conventions.
- Anything about Lean, Mathlib or the checkers themselves, which are trusted.

## Pinned versions

Lean `leanprover/lean4:v4.35.0-rc4` (see [`lean-toolchain`](../lean-toolchain)) and Mathlib at the
revision in [`lakefile.toml`](../lakefile.toml) and [`lake-manifest.json`](../lake-manifest.json).
Comparator, `leanexport` and `nanoda_bin` ship with this Lean toolchain.
