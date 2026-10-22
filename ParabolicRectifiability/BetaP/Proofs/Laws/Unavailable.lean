import ParabolicRectifiability.BetaP.Statements.Laws
import ParabolicRectifiability.Foundations.Proofs.SquareEnergyBounds
import ParabolicRectifiability.Foundations.BetaPow

/-! # The unavailable-family convention

For an empty family `B_p = ⊤` at every positive radius, and both energies are `⊤` at every
positive endpoint, for every source (including the zero measure). The infimum over the empty
model type is `⊤`; the radius normalization is finite and nonzero; the scale measure of
`(0, a)` is nonzero. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- The scale measure of `(0, a)` is nonzero for `a > 0`. -/
theorem c2_scaleMeasure_Ioo_ne_zero {a : ℝ} (ha : 0 < a) : scaleMeasure (Ioo 0 a) ≠ 0 := by
  rw [scaleMeasure_apply _ measurableSet_Ioo]
  apply ne_of_gt
  rw [setLIntegral_pos_iff measurable_scaleDensity]
  have hsupp : Function.support (fun r : ℝ => ENNReal.ofReal (1 / r)) ∩
      (Ioo 0 a ∩ Ioi 0) = Ioo 0 a := by
    ext r
    simp only [Function.mem_support, mem_inter_iff, mem_Ioo, mem_Ioi, ne_eq,
      ENNReal.ofReal_eq_zero, not_le, one_div, inv_pos]
    tauto
  rw [hsupp, Real.volume_Ioo]
  simpa using ha

/-- For an empty family `B_p = ⊤` at every positive radius. -/
theorem c2_betaPow_eq_top {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    [IsEmpty (Models n k T)] (p : ℝ) (z : Space n) {r : ℝ} (hr : 0 < r) :
    betaPow μ k T p z r = ⊤ := by
  unfold betaPow
  rw [ite_eq_left hr, iInf_of_empty]
  apply ENNReal.mul_top
  intro h
  rcases (ENNReal.rpow_eq_zero_iff).1 h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top) h1
  · exact (ENNReal.ofReal_pos.2 hr).ne' (ENNReal.inv_eq_top.1 h1)

theorem c2_unavailableFamily_proof : UnavailableFamilyStatement := by
  intro n _ k _ _ T hT μ p hp z
  have hB : ∀ r : ℝ, 0 < r → betaPow μ k T p z r = ⊤ := fun r hr =>
    c2_betaPow_eq_top μ k T p z hr
  refine ⟨hB, fun a ha => ⟨?_, ?_⟩⟩
  · unfold energyS
    have hq : (0 : ℝ) < 2 / p := by positivity
    rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => (⊤ : ℝ≥0∞))
      (fun r hr => by rw [hB r hr.1, ENNReal.top_rpow_of_pos hq]),
      setLIntegral_const, ENNReal.top_mul (c2_scaleMeasure_Ioo_ne_zero ha)]
  · unfold energyT
    rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => (⊤ : ℝ≥0∞))
      (fun r hr => hB r hr.1),
      setLIntegral_const, ENNReal.top_mul (c2_scaleMeasure_Ioo_ne_zero ha)]

end ParabolicRectifiability.BetaP
