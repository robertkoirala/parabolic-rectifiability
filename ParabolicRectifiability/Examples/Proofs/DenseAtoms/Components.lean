import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Statements
import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTestStatements
import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Weights
import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Measure
import ParabolicRectifiability.Examples.Proofs.DenseAtoms.AtomicSquareBound
import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Energy
import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Density
import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Support
import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Volume
import ParabolicRectifiability.Examples.Proofs.DenseAtoms.NotRectifiable


/-! # Component lemmas for the dense-atoms example

Each component statement `E2Dense…Statement` is discharged by its proof.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

theorem e2_dense_weights : E2DenseWeightStatement := by
  exact e2_dense_weights_proof

theorem e2_dense_measure : E2DenseWeightStatement → E2DenseMeasureStatement := by
  exact e2_dense_measure_proof

theorem e2_atomic_squareBound : E2AtomicSquareBoundStatement := by
  exact e2_atomic_squareBound_proof

theorem e2_dense_energy :
    E2AtomicSquareBoundStatement → E2DenseWeightStatement → E2DenseEnergyStatement := by
  exact e2_dense_energy_proof

theorem e2_dense_density :
    E2AtomDensityStatement → E2DenseWeightStatement → E2DenseDensityStatement := by
  exact e2_dense_density_proof

theorem e2_dense_support : E2DenseWeightStatement → E2DenseSupportStatement := by
  exact e2_dense_support_proof

theorem e2_dense_volume : E2DenseVolumeStatement := by
  exact e2_dense_volume_proof

theorem e2_dense_notRectifiable :
    E2AmbientNullStatement → E2DenseVolumeStatement → E2DenseNotRectifiableStatement := by
  exact e2_dense_notRectifiable_proof

end ParabolicRectifiability.Examples
