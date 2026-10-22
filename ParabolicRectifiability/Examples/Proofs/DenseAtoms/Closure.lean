import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Composition
import ParabolicRectifiability.Examples.Proofs.AtomsAndPatches.AmbientNull
import ParabolicRectifiability.Examples.Proofs.AtomsAndPatches.AtomDensity

/-! # The dense-atoms example

The composition `e2_dense_atoms_of` is closed using the ambient-nullity and atom-density
proofs.
-/

namespace ParabolicRectifiability.Examples

/-- The dense-atoms bundle with the ambient-nullity and atom-density inputs supplied by their proofs. -/
theorem e2_dense_atoms : DenseAtomsStatement :=
  e2_dense_atoms_of e2_ambientNull_proof e2_atom_density_proof

end ParabolicRectifiability.Examples
