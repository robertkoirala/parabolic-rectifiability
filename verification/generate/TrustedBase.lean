import ParabolicRectifiability

/-!
# The trusted base of the checked results

Prints, as tab-separated rows `name  kind  module  startLine  endLine`, every library
declaration that the checked results depend on: starting from every theorem in a `Theorems`
module or in `ParabolicRectifiability.Main` (and from the extra names listed in the file named by
the environment variable `TRUSTED_EXTRA_SEEDS`), it follows the types of all reached
constants, the bodies of definitions, and the proofs of the auxiliary obligations inside
definitions (`foo._proof_1`), but never the proofs of theorems. Auxiliary names are printed too.

Used by `generate.py`; run from the repository root as

    lake env lean verification/generate/TrustedBase.lean
-/

open Lean

namespace TrustedBase

def isOwn (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`ParabolicRectifiability).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  let some ci := env.find? n | return
  let mut todo := ci.type.getUsedConstants
  match ci with
  | .defnInfo d => todo := todo ++ d.value.getUsedConstants
  -- proof obligations inside definitions are abstracted into auxiliary theorems
  -- (`foo._proof_1`); follow their proofs to find the lemmas they cite
  | .thmInfo t =>
    if (n.components.any fun c => c.toString.startsWith "_proof") then
      todo := todo ++ t.value.getUsedConstants
  | .inductInfo i =>
    for c in i.ctors do
      if let some cc := env.find? c then todo := todo ++ cc.type.getUsedConstants
  | _ => pure ()
  for m in todo do
    if isOwn env m then visit env m

def run : CoreM Unit := do
  let env ← getEnv
  -- Extra seeds (owners of shared auxiliary constants) come from the file named by
  -- TRUSTED_EXTRA_SEEDS, one name per line.
  let extra ← match (← IO.getEnv "TRUSTED_EXTRA_SEEDS") with
    | some f => pure ((← IO.FS.lines f).toList.filter (· ≠ "") |>.map String.toName)
    | none => pure []
  let targets := env.constants.toList.filterMap fun (n, ci) =>
    match ci, env.getModuleIdxFor? n with
    | .thmInfo _, some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if !n.isInternal && ((mod.components.contains `Theorems && isOwn env n) ||
          mod == `ParabolicRectifiability.Main) then some n else none
    | _, _ => none
  let (_, seen) := ((targets ++ extra).forM (visit env)).run {}
  let mut rows : Array (String × Nat × String) := #[]
  for n in seen.toList do
    let some ci := env.find? n | continue
    -- auxiliary names are printed too (the spec builder uses them to find their owners)
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    let (line, endLine) := match (← findDeclarationRanges? n) with
      | some r => (r.range.pos.line, r.range.endPos.line)
      | none => (0, 0)
    let kind := match ci with
      | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .defnInfo _ => "def"
      | .thmInfo _ => "theorem"
      | .recInfo _ => "rec" | _ => "other"
    if kind == "ctor" || kind == "rec" then continue
    rows := rows.push (mod.toString, line, s!"{(privateToUserName? n).getD n}\t{kind}\t{mod}\t{line}\t{endLine}")
  let sorted := rows.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  for r in sorted do IO.println r.2.2

end TrustedBase

#eval TrustedBase.run
