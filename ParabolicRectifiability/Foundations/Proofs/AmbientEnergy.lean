import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # Proof of `AmbientEnergyZeroArbitrarySourceStatement`

At `k = n + 2` the horizontal family is empty and every vertical or mixed model is all of
`X`, so every available fitting cost vanishes; hence `β² = 0` at positive radii and the
energy integrand vanishes on `Ioo 0 R`. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

theorem bf1m2a1_modelCost_eq_zero {n : ℕ} {T : FamilyKind}
    (h : Nonempty (Models n (n + 2) T)) (L : Models n (n + 2) T) (z : Space n) :
    modelCost L z = 0 := by
  cases T with
  | horizontal =>
    have e : IsEmpty (Models n (n + 2) .horizontal) := HorizontalModel.ambient_isEmpty
    exact (e.false h.some).elim
  | vertical =>
    have hs : modelSet (T := .vertical) L = Set.univ := VerticalModel.ambient_toSet L
    change (Metric.infEDist z (modelSet (T := .vertical) L)) ^ 2 = 0
    rw [hs, Metric.infEDist_zero_of_mem (Set.mem_univ z)]
    norm_num
  | mixed => exact ambient_modelCost L z

theorem bf1m2a1_betaSq_eq_zero {n : ℕ} {T : FamilyKind} (μ : Measure (Space n))
    (h : Nonempty (Models n (n + 2) T)) (z : Space n) {r : ℝ} (hr : 0 < r) :
    betaSq μ (n + 2) T z r = 0 := by
  rw [betaSq_of_pos μ _ T z hr]
  have : ∀ L : Models n (n + 2) T, fit μ L z r = 0 := by
    intro L
    simp [fit, bf1m2a1_modelCost_eq_zero h L]
  simp [this]

theorem ambient_betaSq_squareEnergy_eq_zero_proof :
    AmbientEnergyZeroArbitrarySourceStatement := by
  intro n _ μ T h
  refine ⟨fun z r hr => bf1m2a1_betaSq_eq_zero μ h z hr, ?_⟩
  intro R _ z
  unfold squareEnergy
  have : ∀ r ∈ Ioo (0 : ℝ) R, betaSq μ (n + 2) T z r = 0 :=
    fun r hr => bf1m2a1_betaSq_eq_zero μ h z hr.1
  rw [setLIntegral_congr_fun measurableSet_Ioo this]
  simp

end ParabolicRectifiability.Foundations
