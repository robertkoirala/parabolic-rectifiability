import ParabolicRectifiability.Characterization.Proofs.Replacement.Statements

/-! # Domination and mass preservation for the replaced source

Proof of `RpAssemblyStatement`. The domination `ν⌊G_A ≤ (5^k/c) A σ` of the good part enters as
the statement's own hypothesis.

* denominators: `σ(Γᶜ) = 0`, so lower and upper ADR at `z_i ∈ Γ` give
  `0 < c r_i^k ≤ σ(B_i) ≤ C r_i^k < ∞` for `B_i = Γ ∩ P(z_i, r_i)`;
* density: `m_i / σ(B_i) ≤ 205^k A / c` from the piece bound `m_i ≤ 205^k A r_i^k`;
* domination (`Measure.le_iff`, Borel `S`):
  `Σ_i (m_i/σ(B_i)) σ(S ∩ B_i) ≤ (205^k A/c) σ(⋃_i S ∩ B_i) ≤ (205^k A/c) σ(S)` (disjoint Borel
  `B_i`), plus `ν⌊G_A(S) ≤ (5^k/c) A σ(S)`; then `(5^k + 205^k)/c ≤ max ((5^k + 205^k)/c) 1`
  and `A > 0`;
* mass: `ν_A(Γ) = ν(Γ ∩ G_A) + Σ_i m_i = ν(Γ ∩ G_A) + ν(Γ \ G_A) = ν(Γ)`
  (`ENNReal.div_mul_cancel` with `0 < σ(B_i) < ∞`, `measure_iUnion` over the disjoint `E_i`).
-/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.ReplacementTree

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.Characterization.SourceTransferTree

/-- `σ(Γᶜ) = 0` for an ADR carrier (inner regularity and `supp σ = Γ`). -/
theorem b3rps_compl_null {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hΓ : IsADRCarrier k c C Γ σ) : σ Γᶜ = 0 := by
  have := hΓ.innerRegular
  rw [← hΓ.support_eq]
  exact Measure.measure_compl_support_of_innerRegular

/-- The ambient ball has the reference mass of the relative ball. -/
theorem b3rps_ball_le {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hΓ : IsADRCarrier k c C Γ σ) (x : Space n) (r : ℝ) :
    σ (Metric.ball x r) ≤ σ (Γ ∩ Metric.ball x r) := by
  have h0 : σ (Metric.ball x r \ Γ) = 0 :=
    measure_mono_null (fun y hy => hy.2) (b3rps_compl_null hΓ)
  calc σ (Metric.ball x r)
      = σ (Metric.ball x r ∩ Γ) + σ (Metric.ball x r \ Γ) :=
        (measure_inter_add_sdiff _ hΓ.isClosed.measurableSet).symm
    _ = σ (Γ ∩ Metric.ball x r) := by rw [h0, add_zero, inter_comm]
    _ ≤ σ (Γ ∩ Metric.ball x r) := le_rfl

/-- Lower ADR for the relative ball: `c r^k ≤ σ(Γ ∩ P(x,r))`. -/
theorem b3rps_lower {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hΓ : IsADRCarrier k c C Γ σ) {x : Space n} (hx : x ∈ Γ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (c * r ^ k) ≤ σ (Γ ∩ Metric.ball x r) :=
  (hΓ.lower x hx r hr).trans (b3rps_ball_le hΓ x r)

/-- The relative ball has positive reference mass. -/
theorem b3rps_ne_zero {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hΓ : IsADRCarrier k c C Γ σ) {x : Space n} (hx : x ∈ Γ) {r : ℝ} (hr : 0 < r) :
    σ (Γ ∩ Metric.ball x r) ≠ 0 := by
  have hpos : 0 < ENNReal.ofReal (c * r ^ k) :=
    ENNReal.ofReal_pos.2 (mul_pos hΓ.lower_pos (pow_pos hr k))
  exact (hpos.trans_le (b3rps_lower hΓ hx hr)).ne'

/-- The relative ball has finite reference mass. -/
theorem b3rps_ne_top {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hΓ : IsADRCarrier k c C Γ σ) {x : Space n} (hx : x ∈ Γ) {r : ℝ} (hr : 0 < r) :
    σ (Γ ∩ Metric.ball x r) ≠ ⊤ :=
  ((measure_mono inter_subset_right).trans (hΓ.upper x hx r hr)).trans_lt
    ENNReal.ofReal_lt_top |>.ne

/-- Density bound: `m ≤ a r^k` and `c r^k ≤ s` give `m / s ≤ a / c`. -/
theorem b3rps_density {m s : ℝ≥0∞} {c a r : ℝ} (k : ℕ) (hc : 0 < c) (hr : 0 < r)
    (hm : m ≤ ENNReal.ofReal (a * r ^ k)) (hs : ENNReal.ofReal (c * r ^ k) ≤ s) :
    m / s ≤ ENNReal.ofReal (a / c) := by
  apply ENNReal.div_le_of_le_mul
  have hcr : 0 ≤ c * r ^ k := (mul_pos hc (pow_pos hr k)).le
  have hc0 : c ≠ 0 := hc.ne'
  have heq : a * r ^ k = a / c * (c * r ^ k) := by
    field_simp
  calc m ≤ ENNReal.ofReal (a * r ^ k) := hm
    _ = ENNReal.ofReal (a / c) * ENNReal.ofReal (c * r ^ k) := by
        rw [heq, ENNReal.ofReal_mul' hcr]
    _ ≤ ENNReal.ofReal (a / c) * s := by gcongr

/-- Domination of the replaced part: `Σ_i (m_i/σ(B_i)) σ(S ∩ B_i) ≤ (205^k A / c) σ(S)`. -/
theorem b3rps_sum_le {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hΓ : IsADRCarrier k c C Γ σ) (ν : Measure (Space n)) (A : ℝ)
    (I : Set ℕ) (z : I → Space n) (r : I → ℝ) (E : I → Set (Space n))
    (hzr : ∀ i, z i ∈ Γ ∧ 0 < r i)
    (hB : Pairwise (Disjoint on fun i => Γ ∩ Metric.ball (z i) (r i)))
    (hpiece : ∀ i, ν (E i) ≤ ENNReal.ofReal (205 ^ k * A * r i ^ k))
    (S : Set (Space n)) (hS : MeasurableSet S) :
    ∑' i : I, ν (E i) / σ (Γ ∩ Metric.ball (z i) (r i)) *
        σ (S ∩ (Γ ∩ Metric.ball (z i) (r i))) ≤
      ENNReal.ofReal (205 ^ k * A / c) * σ S := by
  have hmeas : ∀ i : I, MeasurableSet (S ∩ (Γ ∩ Metric.ball (z i) (r i))) := fun i =>
    hS.inter (hΓ.isClosed.measurableSet.inter Metric.isOpen_ball.measurableSet)
  have hdisj : Pairwise (Disjoint on fun i : I => S ∩ (Γ ∩ Metric.ball (z i) (r i))) :=
    fun i j hij => (hB hij).mono inter_subset_right inter_subset_right
  calc ∑' i : I, ν (E i) / σ (Γ ∩ Metric.ball (z i) (r i)) *
          σ (S ∩ (Γ ∩ Metric.ball (z i) (r i)))
      ≤ ∑' i : I, ENNReal.ofReal (205 ^ k * A / c) *
          σ (S ∩ (Γ ∩ Metric.ball (z i) (r i))) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        gcongr
        exact b3rps_density k hΓ.lower_pos (hzr i).2 (hpiece i)
          (b3rps_lower hΓ (hzr i).1 (hzr i).2)
    _ = ENNReal.ofReal (205 ^ k * A / c) *
          σ (⋃ i : I, S ∩ (Γ ∩ Metric.ball (z i) (r i))) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion hdisj hmeas]
    _ ≤ ENNReal.ofReal (205 ^ k * A / c) * σ S := by
        gcongr
        exact iUnion_subset fun i => inter_subset_left

/-- Domination `ν_A ≤ max ((5^k + 205^k)/c) 1 · A · σ`
and mass preservation `ν_A(Γ) = ν(Γ)` of the replaced source. -/
theorem b3_rp_assembly_proof : RpAssemblyStatement := by
  intro n k c C Γ σ hΓ ν _hν _hνΓ A hA hG hdom I z r E hzr hB hEm hE hEU hpiece
  have hΓm : MeasurableSet Γ := hΓ.isClosed.measurableSet
  have hc : 0 < c := hΓ.lower_pos
  refine ⟨?_, ?_⟩
  · -- domination
    rw [Measure.le_iff]
    intro S hS
    have hdomS := Measure.le_iff'.1 hdom S
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS] at hdomS
    rw [b3_replacedSource, Measure.add_apply, Measure.sum_apply _ hS, Measure.smul_apply,
      smul_eq_mul]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS]
    have hsum := b3rps_sum_le hΓ ν A I z r E hzr hB hpiece S hS
    have h5 : (0 : ℝ) ≤ 5 ^ k / c * A :=
      mul_nonneg (div_nonneg (pow_nonneg (by norm_num) k) hc.le) hA.le
    have h205 : (0 : ℝ) ≤ 205 ^ k * A / c :=
      div_nonneg (mul_nonneg (pow_nonneg (by norm_num) k) hA.le) hc.le
    have hreal : 5 ^ k / c * A + 205 ^ k * A / c ≤ max ((5 ^ k + 205 ^ k) / c) 1 * A := by
      calc 5 ^ k / c * A + 205 ^ k * A / c = (5 ^ k + 205 ^ k) / c * A := by ring
        _ ≤ max ((5 ^ k + 205 ^ k) / c) 1 * A :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hA.le
    calc ν (S ∩ adrGoodSet Γ ν k A) +
          ∑' i : I, ν (E i) / σ (Γ ∩ Metric.ball (z i) (r i)) *
            σ (S ∩ (Γ ∩ Metric.ball (z i) (r i)))
        ≤ ENNReal.ofReal (5 ^ k / c * A) * σ S +
            ENNReal.ofReal (205 ^ k * A / c) * σ S := add_le_add hdomS hsum
      _ = ENNReal.ofReal (5 ^ k / c * A + 205 ^ k * A / c) * σ S := by
          rw [ENNReal.ofReal_add h5 h205, add_mul]
      _ ≤ ENNReal.ofReal (max ((5 ^ k + 205 ^ k) / c) 1 * A) * σ S :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hreal) zero_le
  · -- mass preservation
    rw [b3_replacedSource, Measure.add_apply, Measure.sum_apply _ hΓm]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hΓm]
    have hterm : ∀ i : I, ν (E i) / σ (Γ ∩ Metric.ball (z i) (r i)) *
        σ (Γ ∩ (Γ ∩ Metric.ball (z i) (r i))) = ν (E i) := by
      intro i
      rw [← inter_assoc, inter_self]
      exact ENNReal.div_mul_cancel (b3rps_ne_zero hΓ (hzr i).1 (hzr i).2)
        (b3rps_ne_top hΓ (hzr i).1 (hzr i).2)
    rw [tsum_congr hterm, ← measure_iUnion hE hEm, hEU]
    exact measure_inter_add_sdiff Γ hG

end ParabolicRectifiability.Characterization.ReplacementTree
