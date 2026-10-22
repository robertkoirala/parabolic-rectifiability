import ParabolicRectifiability

/-!
# Axiom audit

Checks every declaration of the library (every constant defined in a
`ParabolicRectifiability` module, not only the public theorems) and fails if any of them
depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. In
particular it fails on any use of `sorry`, which appears as the axiom `sorryAx`.

Run from the repository root, after `lake build`:

    lake env lean verification/AxiomAudit.lean
-/

open Lean

namespace AxiomAudit

def permitted : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def run : CoreM Unit := do
  let env ← getEnv
  let mut count := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless (`ParabolicRectifiability).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    count := count + 1
    let axs ← collectAxioms n
    let extra := axs.filter (!permitted.contains ·)
    unless extra.isEmpty do bad := bad.push (n, extra)
  if bad.isEmpty then
    IO.println s!"Axiom audit passed: {count} declarations; all axioms among {permitted}."
  else
    for (n, axs) in bad.toList.take 20 do
      IO.eprintln s!"{n} depends on {axs}"
    throwError s!"Axiom audit failed: {bad.size} of {count} declarations use other axioms."

end AxiomAudit

#eval AxiomAudit.run
