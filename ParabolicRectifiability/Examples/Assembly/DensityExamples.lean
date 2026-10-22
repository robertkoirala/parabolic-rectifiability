import ParabolicRectifiability.Examples.Assembly.IntermediateStatements

/-! # The density and mass test examples

The dense-atom example and the density tests do not depend on other results of the
library; each statement is obtained directly from its proof bundle
(`dense_atoms_bundle`, `density_tests_bundle`).
-/

namespace ParabolicRectifiability.Examples

/-- The dense-atom example `DenseAtomsStatement`, from `dense_atoms_bundle`. -/
theorem dense_atoms_skeleton : DenseAtomsStatement :=
  dense_atoms_bundle

/-- The flat, diffuse and atomic density tests `DensityTestsStatement`, from
`density_tests_bundle`. -/
theorem density_tests_skeleton : DensityTestsStatement :=
  density_tests_bundle

end ParabolicRectifiability.Examples
