import ParabolicRectifiability.Examples.Statements.DensityExamples
import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Closure
import ParabolicRectifiability.Examples.Assembly.DensityExamples

/-! # Density, mass, and support examples

`dense_atoms_density_support` constructs a finite nonzero atomic source with finite
integrated square energy and infinite densities at its atoms, whose actual support is a
closed parabolic ball of infinite `H_P^k` measure and is not regularly rectifiable as a set.
This distinguishes energy and mass conclusions from conclusions about the whole support.

`density_tests` collects the flat, diffuse, and atomic tests. The diffuse example has zero
`k`-density and finite positive integrated energy but gives zero mass to every sigma-finite
`H_P^k` set; the atom has zero energy yet fails absolute continuity. Thus the structural
conditions in the characterization have content beyond square finiteness alone.

The exact hypotheses and amplitude quantifiers are in `DenseAtomsStatement` and
`DensityTestsStatement`; the proofs are `e2_dense_atoms` and `density_tests_skeleton`.
-/

namespace ParabolicRectifiability.Examples

/-- For `1 ≤ k < n + 2`, distinct points dense in `D = closedBall 0 (1/4)` give the
finite nonzero source `denseAtomMeasure k z`. It has finite pair and integrated square
energy, infinite densities at every atom, and support exactly `D`, while
`H_P^k(D) = ∞` and `D` is not regularly rectifiable as a set. -/
theorem dense_atoms_density_support : DenseAtomsStatement := by
  exact e2_dense_atoms

/-- The flat, diffuse, and atomic tests. Flat patches and atoms have zero square
energy; atoms fail Hausdorff absolute continuity. In `k < n + 2`, diffuse amplitudes
`μ_c = c L^{n+1}⌊P(0,1/4)` have zero density, square bounded by `C c`, integrated square
exactly `κ c² > 0`, and no nonzero good submeasure with a finite-Hausdorff carrier. -/
theorem density_tests : DensityTestsStatement := by
  exact ParabolicRectifiability.Examples.density_tests_skeleton

end ParabolicRectifiability.Examples
