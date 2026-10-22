import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Statements
import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTestStatements

/-! # Densities of the dense atomic source

Each positive weighted Dirac measure is dominated by the sum. Monotonicity of
ball-mass ratios and their lower and upper limits transfers the supplied atom
density statement to the sum. The sum is carried by the range of its atoms.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- Both densities are infinite at every atom, hence every finite upper-density
threshold holds almost everywhere for the dense atomic measure. -/
theorem e2_dense_density_proof :
    E2AtomDensityStatement → E2DenseWeightStatement → E2DenseDensityStatement := by
  intro hAtom hWeight n k hk z
  have hAt : ∀ j, lowerDensity (denseAtomMeasure k z) k (z j) = ⊤ ∧
      upperDensity (denseAtomMeasure k z) k (z j) = ⊤ := by
    intro j
    have hDom : ENNReal.ofReal (denseAtomWeight k z j) • Measure.dirac (z j) ≤
        denseAtomMeasure k z :=
      Measure.le_sum (fun i => ENNReal.ofReal (denseAtomWeight k z i) • Measure.dirac (z i)) j
    have hRatio : ∀ r : ℝ,
        densityRatio (ENNReal.ofReal (denseAtomWeight k z j) • Measure.dirac (z j)) k (z j) r ≤
          densityRatio (denseAtomMeasure k z) k (z j) r := by
      intro r
      unfold densityRatio
      gcongr
    obtain ⟨hLower, hUpper⟩ := hAtom n k hk (z j) (denseAtomWeight k z j) ((hWeight n k z).1 j)
    constructor
    · apply top_unique
      rw [← hLower]
      exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hRatio)
    · apply top_unique
      rw [← hUpper]
      exact Filter.limsup_le_limsup (Filter.Eventually.of_forall hRatio)
  refine ⟨hAt, ?_⟩
  intro a _ha
  have hCarried : (denseAtomMeasure k z) (range z)ᶜ = 0 := by
    rw [denseAtomMeasure, Measure.sum_apply_eq_zero]
    intro j
    simp [Measure.smul_apply, Measure.dirac_apply', (Set.countable_range z).measurableSet.compl]
  have hRange : ∀ᵐ x ∂(denseAtomMeasure k z), x ∈ range z := hCarried
  filter_upwards [hRange] with x hx
  obtain ⟨j, rfl⟩ := hx
  rw [(hAt j).2]
  exact le_top

end ParabolicRectifiability.Examples
