import ParabolicRectifiability.QuantitativeCharacterization.Statements.ReverseBound
import Mathlib.Analysis.MeanInequalitiesPow

/-! # The pointwise comparison

Proof of `d2_comparison`, with its type `ComparisonStatement`.

Proof idea. Put `θ = C_disp (1 + L)` and `Λ = 1 + 2θ`. For `y ∈ P(z,r)`,
`h(y) = C_disp d(y) ≤ C_disp (d(z) + r) ≤ θ r` and `d(z,v) ≤ h(z) ≤ θ r`, so `κ_y`-a.e.
`v' ∈ P(v, Λ r)`. For one fixed fitting model `V`,
`cost_V(y) ≤ 2 cost_V(v') + 2 d(y,v')²`; averaging over the probability `κ_y`, integrating over
`μ⌊P(z,r)`, enlarging to `μ⌊P(c,2ρ)` and using `(μ⌊P(c,2ρ)).bind κ ≤ D₀ σ` gives
`fit_μ(V;z,r) ≤ 2 D₀ fit_σ(V;v,Λr) + 2 ∫_{P(z,r)} h² dμ`. Only then the infimum over `V` is
taken (`ENNReal.mul_iInf_of_ne`, `ENNReal.iInf_add`; the coefficient `2 D₀` is positive and
finite, so an unavailable family gives `⊤ ≤ ⊤`), and the radius factors are rearranged with
`r^{-k-2} = Λ^{k+2} (Λ r)^{-k-2}`. No regularity of `μ` or `σ` is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization.ReverseTree

open ParabolicRectifiability.Foundations

/-- `(a + b)² ≤ 2 (a² + b²)` in `[0,∞]`. -/
theorem d2cmp_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) one_le_two
  have h1 : (2 : ℝ) - 1 = 1 := by norm_num
  rw [h1, ENNReal.rpow_one, ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two] at h
  exact h

/-- The squared model distance at `y` is at most twice the one at `v'` plus twice `d(y,v')²`. -/
theorem d2cmp_cost_le {n k : ℕ} {T : FamilyKind} (V : Models n k T) (y v' : Space n) :
    modelCost V y ≤ 2 * (modelCost V v' + edist y v' ^ 2) := by
  unfold modelCost
  calc Metric.infEDist y (modelSet V) ^ 2
      ≤ (Metric.infEDist v' (modelSet V) + edist y v') ^ 2 :=
        pow_le_pow_left' Metric.infEDist_le_infEDist_add_edist 2
    _ ≤ _ := d2cmp_add_sq_le _ _

/-- The cost at `y` against the kernel average at the transported points. -/
theorem d2cmp_cost_le_kernel {n k : ℕ} {T : FamilyKind} (V : Models n k T)
    (κ : ProbabilityTheory.Kernel (Space n) (Space n)) [ProbabilityTheory.IsMarkovKernel κ]
    (S : Set (Space n)) (y : Space n) (H : ℝ)
    (hS : ∀ᵐ v' ∂(κ y), v' ∈ S ∧ dist y v' ≤ H) :
    modelCost V y ≤
      2 * ∫⁻ v', S.indicator (modelCost V) v' ∂(κ y) + 2 * ENNReal.ofReal H ^ 2 := by
  calc modelCost V y = ∫⁻ _v', modelCost V y ∂(κ y) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ v', (2 * S.indicator (modelCost V) v' + 2 * ENNReal.ofReal H ^ 2) ∂(κ y) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hS] with v' hv
        rw [indicator_of_mem hv.1, ← mul_add]
        refine (d2cmp_cost_le V y v').trans ?_
        gcongr
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal hv.2
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' 2 _ (by simp),
          lintegral_const, measure_univ, mul_one]

/-- The fixed-model comparison, integrated before the infimum. -/
theorem d2cmp_fit_le {n k : ℕ} {T : FamilyKind} (V : Models n k T) (L Cdisp D₀ : ℝ)
    (hL : 1 ≤ L) (hC : 1 ≤ Cdisp) (μ σ : Measure (Space n)) (Γ : Set (Space n))
    (κ : ProbabilityTheory.Kernel (Space n) (Space n)) [ProbabilityTheory.IsMarkovKernel κ]
    (hdisp : ∀ y, ∀ᵐ v ∂(κ y), dist y v ≤ Cdisp * Metric.infDist y Γ)
    (c : Space n) (ρ : ℝ)
    (hbind : (μ.restrict (Metric.ball c (2 * ρ))).bind κ ≤ ENNReal.ofReal D₀ • σ)
    (z : Space n) (r : ℝ) (hz : z ∈ Metric.ball c ρ) (hr : 0 < r) (hrρ : r < ρ)
    (hzΓ : L⁻¹ * Metric.infDist z Γ ≤ r)
    (v : Space n) (hv : dist z v ≤ Cdisp * Metric.infDist z Γ) :
    fit μ V z r ≤
      2 * ENNReal.ofReal D₀ * fit σ V v ((1 + 2 * Cdisp * (1 + L)) * r) +
        2 * ∫⁻ y in Metric.ball z r, ENNReal.ofReal (Cdisp * Metric.infDist y Γ) ^ 2 ∂μ := by
  set Λ := 1 + 2 * Cdisp * (1 + L) with hΛ
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hC0 : 0 ≤ Cdisp := le_trans zero_le_one hC
  -- the reference distance of `z`
  have hdz : Metric.infDist z Γ ≤ L * r := by
    have h := mul_le_mul_of_nonneg_left hzΓ hL0.le
    rwa [← mul_assoc, mul_inv_cancel₀ hL0.ne', one_mul] at h
  have hvz : dist z v ≤ Cdisp * ((1 + L) * r) := by
    refine hv.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    linarith
  -- : every transported point lies in `P(v, Λ r)`
  have hmove : ∀ y ∈ Metric.ball z r, ∀ᵐ v' ∂(κ y),
      v' ∈ Metric.ball v (Λ * r) ∧ dist y v' ≤ Cdisp * Metric.infDist y Γ := by
    intro y hy
    have hyz : dist y z < r := Metric.mem_ball.mp hy
    have hdy : Metric.infDist y Γ ≤ (1 + L) * r := by
      have := Metric.infDist_le_infDist_add_dist (x := y) (y := z) (s := Γ)
      linarith
    have hhy : Cdisp * Metric.infDist y Γ ≤ Cdisp * ((1 + L) * r) :=
      mul_le_mul_of_nonneg_left hdy hC0
    filter_upwards [hdisp y] with v' hv'
    refine ⟨?_, hv'⟩
    rw [Metric.mem_ball]
    have h1 := dist_triangle v' y v
    have h2 := dist_triangle y z v
    rw [dist_comm v' y] at h1
    rw [hΛ]
    linarith
  -- the transported cost integrand
  set f : Space n → ℝ≥0∞ := (Metric.ball v (Λ * r)).indicator (modelCost V) with hf
  have hfm : Measurable f := (measurable_modelCost V).indicator measurableSet_ball
  set G : Space n → ℝ≥0∞ := fun y => ∫⁻ v', f v' ∂(κ y) with hG
  have hhsq : Measurable fun y : Space n => ENNReal.ofReal (Cdisp * Metric.infDist y Γ) ^ 2 :=
    ((measurable_const.mul (Metric.continuous_infDist_pt Γ).measurable).ennreal_ofReal).pow_const 2
  have hsub : Metric.ball z r ⊆ Metric.ball c (2 * ρ) := by
    apply Metric.ball_subset_ball'
    have := Metric.mem_ball.mp hz
    linarith
  -- second marginal: the kernel average is dominated by `D₀ σ`
  have hGle : ∫⁻ y in Metric.ball z r, G y ∂μ ≤ ENNReal.ofReal D₀ * fit σ V v (Λ * r) := by
    calc ∫⁻ y in Metric.ball z r, G y ∂μ ≤ ∫⁻ y in Metric.ball c (2 * ρ), G y ∂μ :=
          lintegral_mono_set hsub
      _ = ∫⁻ v', f v' ∂((μ.restrict (Metric.ball c (2 * ρ))).bind κ) :=
          (Measure.lintegral_bind κ.measurable.aemeasurable hfm.aemeasurable).symm
      _ ≤ ∫⁻ v', f v' ∂(ENNReal.ofReal D₀ • σ) := lintegral_mono' hbind le_rfl
      _ = ENNReal.ofReal D₀ * fit σ V v (Λ * r) := by
          rw [lintegral_smul_measure, smul_eq_mul, hf, lintegral_indicator measurableSet_ball, fit]
  calc fit μ V z r = ∫⁻ y in Metric.ball z r, modelCost V y ∂μ := rfl
    _ ≤ ∫⁻ y in Metric.ball z r,
          (2 * G y + 2 * ENNReal.ofReal (Cdisp * Metric.infDist y Γ) ^ 2) ∂μ :=
        setLIntegral_mono' measurableSet_ball fun y hy =>
          d2cmp_cost_le_kernel V κ _ y _ (hmove y hy)
    _ = 2 * ∫⁻ y in Metric.ball z r, G y ∂μ +
          2 * ∫⁻ y in Metric.ball z r, ENNReal.ofReal (Cdisp * Metric.infDist y Γ) ^ 2 ∂μ := by
        rw [lintegral_add_right _ (hhsq.const_mul 2), lintegral_const_mul' 2 _ (by simp),
          lintegral_const_mul' 2 _ (by simp)]
    _ ≤ 2 * (ENNReal.ofReal D₀ * fit σ V v (Λ * r)) +
          2 * ∫⁻ y in Metric.ball z r, ENNReal.ofReal (Cdisp * Metric.infDist y Γ) ^ 2 ∂μ := by
        gcongr
    _ = _ := by rw [mul_assoc]

/-- **The pointwise comparison**: the type of the statement
`d2_comparison`. -/
theorem d2_comparison_proof : ComparisonStatement := by
  unfold ComparisonStatement
  intro n k T L Cdisp D₀ hL hC hD₀ μ σ Γ κ hκ hdisp c ρ hbind z r hz hr hrρ hzΓ v hv
  set Λ := 1 + 2 * Cdisp * (1 + L) with hΛ
  have hC0 : 0 ≤ Cdisp := le_trans zero_le_one hC
  have hΛpos : 0 < Λ := by
    have : 0 ≤ 2 * Cdisp * (1 + L) := mul_nonneg (mul_nonneg zero_le_two hC0) (by linarith)
    linarith
  have hΛr : 0 < Λ * r := mul_pos hΛpos hr
  set E := ∫⁻ y in Metric.ball z r, ENNReal.ofReal (Cdisp * Metric.infDist y Γ) ^ 2 ∂μ with hE
  have hfit : ∀ V : Models n k T,
      fit μ V z r ≤ 2 * ENNReal.ofReal D₀ * fit σ V v (Λ * r) + 2 * E := fun V =>
    d2cmp_fit_le V L Cdisp D₀ hL hC μ σ Γ κ hdisp c ρ hbind z r hz hr hrρ hzΓ v hv
  have h0 : (2 : ℝ≥0∞) * ENNReal.ofReal D₀ ≠ 0 :=
    mul_ne_zero two_ne_zero (ENNReal.ofReal_pos.mpr hD₀).ne'
  have htop : (2 : ℝ≥0∞) * ENNReal.ofReal D₀ ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  -- only now the infimum over the models (both sides `⊤` for an unavailable family)
  have hinf : ⨅ V : Models n k T, fit μ V z r ≤
      2 * ENNReal.ofReal D₀ * (⨅ V : Models n k T, fit σ V v (Λ * r)) + 2 * E := by
    rw [ENNReal.mul_iInf_of_ne h0 htop, ENNReal.iInf_add]
    exact iInf_mono hfit
  -- the radius factors: `2 D₀ Λ^{k+2} (Λ r)^{-k-2} = r^{-k-2} · 2 D₀`
  have hreal : 2 * D₀ * Λ ^ (k + 2) * ((Λ * r)⁻¹) ^ (k + 2) = (r⁻¹) ^ (k + 2) * (2 * D₀) := by
    rw [mul_inv, mul_pow]
    have h1 : Λ ^ (k + 2) * Λ⁻¹ ^ (k + 2) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hΛpos.ne', one_pow]
    calc 2 * D₀ * Λ ^ (k + 2) * (Λ⁻¹ ^ (k + 2) * r⁻¹ ^ (k + 2))
        = 2 * D₀ * (Λ ^ (k + 2) * Λ⁻¹ ^ (k + 2)) * r⁻¹ ^ (k + 2) := by ring
      _ = _ := by rw [h1]; ring
  have hcoef : ENNReal.ofReal (2 * D₀ * Λ ^ (k + 2)) * (ENNReal.ofReal (Λ * r))⁻¹ ^ (k + 2) =
      (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (2 * ENNReal.ofReal D₀) := by
    have hD0' : 0 ≤ 2 * D₀ * Λ ^ (k + 2) :=
      mul_nonneg (mul_nonneg zero_le_two hD₀.le) (pow_nonneg hΛpos.le _)
    rw [← ENNReal.ofReal_inv_of_pos hΛr, ← ENNReal.ofReal_inv_of_pos hr,
      ← ENNReal.ofReal_pow (inv_nonneg.mpr hΛr.le), ← ENNReal.ofReal_pow (inv_nonneg.mpr hr.le),
      ← ENNReal.ofReal_mul hD0', hreal,
      ENNReal.ofReal_mul (p := r⁻¹ ^ (k + 2)) (pow_nonneg (inv_nonneg.mpr hr.le) _),
      ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
  rw [betaSq_of_pos μ k T z hr, betaSq_of_pos σ k T v hΛr]
  calc (ENNReal.ofReal r)⁻¹ ^ (k + 2) * ⨅ V : Models n k T, fit μ V z r
      ≤ (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          (2 * ENNReal.ofReal D₀ * (⨅ V : Models n k T, fit σ V v (Λ * r)) + 2 * E) := by
        gcongr
    _ = (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (2 * ENNReal.ofReal D₀) *
            (⨅ V : Models n k T, fit σ V v (Λ * r)) +
          2 * ((ENNReal.ofReal r)⁻¹ ^ (k + 2) * E) := by ring
    _ = ENNReal.ofReal (2 * D₀ * Λ ^ (k + 2)) *
            ((ENNReal.ofReal (Λ * r))⁻¹ ^ (k + 2) * ⨅ V : Models n k T, fit σ V v (Λ * r)) +
          2 * d2_transportError k Cdisp Γ μ z r := by
        rw [d2_transportError, ← hE, ← hcoef, mul_assoc]

end ParabolicRectifiability.QuantitativeCharacterization.ReverseTree
