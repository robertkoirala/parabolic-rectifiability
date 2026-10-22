import ParabolicRectifiability.Characterization.Proofs.Fourier.EstimateStatements
import ParabolicRectifiability.Characterization.Proofs.Fourier.BMOGrowthApriori

/-! # Growth of parabolic BMO functions

This file proves `ba1_bmo_growth_proof : BMOGrowthStatement` without further hypotheses: a
function with bounded mean oscillation on parabolic balls is locally square integrable, satisfies
an `L²` oscillation estimate on balls, and its ball means grow at most logarithmically.

* Clause 2 (`b1bmo_ball_sq`): enclose `P(p,r)` in the root cell of side `2r` (volume ratio
  `2^(m+2) / (2 ω_m)`), use the cell estimate `b1bmo_cellSq_bound` with the cell oscillation
  `2 K_c B` obtained from the ball oscillation (`b1bmo_cellOsc_of_ballOsc`), and compare the
  two means. The case `B = 0` is direct.
* Clause 3 (`b1bmo_concentric`): `|g_{P(p,R')} - g_{P(p,ρ')}| ≤ 2^(m+2) B` for
  `ρ' ≤ R' ≤ 2ρ'` and telescoping over `⌈log₂(R/ρ)⌉ ≤ 2 (1 + log(R/ρ))` steps.
* Clause 1 (`b1bmo_memLp_ball`): from clause 2 on a ball of radius `max r 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

variable {m : ℕ}

theorem b1bmo_standardBallAverage_eq (g : Space m → ℝ) (p : Space m) (r : ℝ) :
    standardBallAverage m g p r = b1bmo_avg (parabolicVolume m) (Metric.ball p r) g := by
  rw [standardBallAverage, b1bmo_avg, smul_eq_mul]

/-- The volume ratio between the root cell of a ball and the ball. -/
def b1bmo_KQ (m : ℕ) : ℝ≥0∞ := 2 ^ (m + 2) * (2 * omega m)⁻¹

theorem b1bmo_two_omega_ne_zero (m : ℕ) : 2 * omega m ≠ 0 :=
  mul_ne_zero two_ne_zero (omega_pos m).ne'

theorem b1bmo_two_omega_ne_top (m : ℕ) : 2 * omega m ≠ ∞ :=
  ENNReal.mul_ne_top (by simp) (omega_lt_top m).ne

theorem b1bmo_KQ_ne_top (m : ℕ) : b1bmo_KQ m ≠ ∞ :=
  ENNReal.mul_ne_top (by simp) (ENNReal.inv_ne_top.mpr (b1bmo_two_omega_ne_zero m))

theorem b1bmo_volume_root_eq (p : Space m) {r : ℝ} (hr : 0 < r) :
    parabolicVolume m (b1bmo_cell (b1bmo_rootA p r) (b1bmo_rootS p r) (2 * r) p) =
      b1bmo_KQ m * parabolicVolume m (Metric.ball p r) := by
  rw [b1bmo_volume_root p hr, parabolicVolume_ball p r hr, b1bmo_KQ]
  have h : (2 * omega m)⁻¹ * (2 * omega m) = 1 :=
    ENNReal.inv_mul_cancel (b1bmo_two_omega_ne_zero m) (b1bmo_two_omega_ne_top m)
  calc (2 : ℝ≥0∞) ^ (m + 2) * ENNReal.ofReal r ^ (m + 2)
      = 2 ^ (m + 2) * ((2 * omega m)⁻¹ * (2 * omega m)) * ENNReal.ofReal r ^ (m + 2) := by
        rw [h, mul_one]
    _ = 2 ^ (m + 2) * (2 * omega m)⁻¹ * (2 * omega m * ENNReal.ofReal r ^ (m + 2)) := by ring

/-- The constant of the ball `L²` oscillation estimate. -/
def b1bmo_C2 (m : ℕ) : ℝ≥0∞ :=
  2 * b1bmo_A m * (2 * (2 * b1bmo_Kc m)) ^ 2 * b1bmo_KQ m + 2 * (2 * b1bmo_Kc m * b1bmo_KQ m) ^ 2

theorem b1bmo_A_ne_top (m : ℕ) : b1bmo_A m ≠ ∞ := by
  unfold b1bmo_A
  exact ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top (by simp)
    (ENNReal.pow_ne_top (ENNReal.pow_ne_top (by simp)))⟩

theorem b1bmo_C2_ne_top (m : ℕ) : b1bmo_C2 m ≠ ∞ := by
  have hK := b1bmo_Kc_ne_top m
  have hQ := b1bmo_KQ_ne_top m
  have hA := b1bmo_A_ne_top m
  unfold b1bmo_C2
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hA)
      (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp) hK)))) hQ
  · exact ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hK) hQ))

/-- **Clause 2 of `BMOGrowthStatement`**: the `L²` oscillation estimate on parabolic balls. -/
theorem b1bmo_ball_sq {g : Space m → ℝ} {B : ℝ} (hg : HasStandardParabolicBMOBound m g B)
    (p : Space m) {r : ℝ} (hr : 0 < r) :
    ∫⁻ q in Metric.ball p r,
        ‖g q - b1bmo_avg (parabolicVolume m) (Metric.ball p r) g‖ₑ ^ 2 ∂parabolicVolume m ≤
      b1bmo_C2 m * ENNReal.ofReal B ^ 2 * parabolicVolume m (Metric.ball p r) := by
  set μ := parabolicVolume m with hμ
  have hloc := hg.2.1
  have hball := b1bmo_ballOsc_of_bound hg
  set β := ENNReal.ofReal B with hβdef
  set P := Metric.ball p r with hPdef
  have hP0 : μ P ≠ 0 := b1bmo_volume_ball_ne_zero p hr
  have hPt : μ P ≠ ∞ := MeasureTheory.measure_ball_lt_top.ne
  rcases eq_or_ne β 0 with hβ0 | hβ0
  · -- zero oscillation: `g` equals its mean almost everywhere on the ball
    have h0 : ∫⁻ q in P, ‖g q - b1bmo_avg μ P g‖ₑ ∂μ = 0 := by
      refine le_antisymm ?_ (zero_le)
      have := hball p r hr
      rwa [hβ0, zero_mul] at this
    have hm : AEMeasurable (fun q => ‖g q - b1bmo_avg μ P g‖ₑ) (μ.restrict P) :=
      ((b1bmo_integrableOn_ball hloc p r).aestronglyMeasurable.sub
        aestronglyMeasurable_const).enorm
    have hae := (lintegral_eq_zero_iff' hm).mp h0
    have hsq : ∫⁻ q in P, ‖g q - b1bmo_avg μ P g‖ₑ ^ 2 ∂μ = 0 := by
      rw [lintegral_eq_zero_iff' (hm.pow_const 2)]
      filter_upwards [hae] with q hq
      simp [hq]
    rw [hsq]
    exact zero_le
  · have hβt : β ≠ ∞ := ENNReal.ofReal_ne_top
    have hosc := b1bmo_cellOsc_of_ballOsc hloc hball
    set β₀ := 2 * b1bmo_Kc m * β with hβ₀def
    have hβ₀0 : β₀ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (b1bmo_Kc_ne_zero m)) hβ0
    have hβ₀t : β₀ ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (b1bmo_Kc_ne_top m)) hβt
    have h2r : 0 < 2 * r := by positivity
    set Q := b1bmo_cell (b1bmo_rootA p r) (b1bmo_rootS p r) (2 * r) p with hQdef
    have hPQ : P ⊆ Q := b1bmo_ball_subset_root p hr
    have hQ := b1bmo_cellSq_bound hloc hβ₀0 hβ₀t hosc (b1bmo_rootA p r) (b1bmo_rootS p r) h2r p
    have hQosc : ∫⁻ w in Q, ‖g w - b1bmo_avg μ Q g‖ₑ ∂μ ≤ β₀ * μ Q :=
      hosc (b1bmo_rootA p r) (b1bmo_rootS p r) (2 * r) h2r p
    have hμQ : μ Q = b1bmo_KQ m * μ P := b1bmo_volume_root_eq p hr
    have hshift : ‖b1bmo_avg μ Q g - b1bmo_avg μ P g‖ₑ ≤ β₀ * b1bmo_KQ m := by
      rw [enorm_sub_rev]
      calc ‖b1bmo_avg μ P g - b1bmo_avg μ Q g‖ₑ
          ≤ (μ P)⁻¹ * ∫⁻ w in P, ‖g w - b1bmo_avg μ Q g‖ₑ ∂μ :=
            b1bmo_enorm_avg_sub_le μ hP0 hPt (b1bmo_integrableOn_ball hloc p r) _
        _ ≤ (μ P)⁻¹ * (β₀ * μ Q) := by
            gcongr
            exact (lintegral_mono_set hPQ).trans hQosc
        _ = β₀ * b1bmo_KQ m * ((μ P)⁻¹ * μ P) := by
            rw [hμQ]
            ring
        _ = β₀ * b1bmo_KQ m := by rw [ENNReal.inv_mul_cancel hP0 hPt, mul_one]
    have hPsq : ∫⁻ w in P, ‖g w - b1bmo_avg μ Q g‖ₑ ^ 2 ∂μ ≤
        b1bmo_A m * (2 * β₀) ^ 2 * μ Q := (lintegral_mono_set hPQ).trans hQ
    calc ∫⁻ q in P, ‖g q - b1bmo_avg μ P g‖ₑ ^ 2 ∂μ
        ≤ 2 * ∫⁻ w in P, ‖g w - b1bmo_avg μ Q g‖ₑ ^ 2 ∂μ +
            2 * ‖b1bmo_avg μ Q g - b1bmo_avg μ P g‖ₑ ^ 2 * μ P :=
          b1bmo_setLIntegral_sq_shift μ P g _ _
      _ ≤ 2 * (b1bmo_A m * (2 * β₀) ^ 2 * μ Q) + 2 * (β₀ * b1bmo_KQ m) ^ 2 * μ P := by
          gcongr
      _ = b1bmo_C2 m * β ^ 2 * μ P := by
          rw [hμQ, hβ₀def, b1bmo_C2]
          ring

/-- One step of concentric mean comparison: `ρ' ≤ R' ≤ 2ρ'`. -/
theorem b1bmo_avg_step {g : Space m → ℝ} {B : ℝ} (hg : HasStandardParabolicBMOBound m g B)
    (p : Space m) {ρ' R' : ℝ} (hρ' : 0 < ρ') (h1 : ρ' ≤ R') (h2 : R' ≤ 2 * ρ') :
    ‖b1bmo_avg (parabolicVolume m) (Metric.ball p R') g -
        b1bmo_avg (parabolicVolume m) (Metric.ball p ρ') g‖ₑ ≤
      2 ^ (m + 2) * ENNReal.ofReal B := by
  set μ := parabolicVolume m with hμ
  have hball := b1bmo_ballOsc_of_bound hg
  have hP0 : μ (Metric.ball p ρ') ≠ 0 := b1bmo_volume_ball_ne_zero p hρ'
  have hPt : μ (Metric.ball p ρ') ≠ ∞ := MeasureTheory.measure_ball_lt_top.ne
  rw [enorm_sub_rev]
  calc ‖b1bmo_avg μ (Metric.ball p ρ') g - b1bmo_avg μ (Metric.ball p R') g‖ₑ
      ≤ (μ (Metric.ball p ρ'))⁻¹ *
          ∫⁻ w in Metric.ball p ρ', ‖g w - b1bmo_avg μ (Metric.ball p R') g‖ₑ ∂μ :=
        b1bmo_enorm_avg_sub_le μ hP0 hPt (b1bmo_integrableOn_ball hg.2.1 p ρ') _
    _ ≤ (μ (Metric.ball p ρ'))⁻¹ * (ENNReal.ofReal B * μ (Metric.ball p R')) := by
        gcongr
        exact (lintegral_mono_set (Metric.ball_subset_ball h1)).trans
          (hball p R' (lt_of_lt_of_le hρ' h1))
    _ ≤ (μ (Metric.ball p ρ'))⁻¹ *
          (ENNReal.ofReal B * (2 ^ (m + 2) * μ (Metric.ball p ρ'))) := by
        gcongr
        exact (measure_mono (Metric.ball_subset_ball h2)).trans
          (parabolicVolume_ball_two_mul p ρ' hρ').le
    _ = 2 ^ (m + 2) * ENNReal.ofReal B * ((μ (Metric.ball p ρ'))⁻¹ * μ (Metric.ball p ρ')) := by
        ring
    _ = 2 ^ (m + 2) * ENNReal.ofReal B := by rw [ENNReal.inv_mul_cancel hP0 hPt, mul_one]

/-- Telescoping over `j` doublings. -/
theorem b1bmo_avg_tele {g : Space m → ℝ} {B : ℝ} (hg : HasStandardParabolicBMOBound m g B)
    (p : Space m) {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) :
    ∀ R' : ℝ, ρ ≤ R' → R' ≤ 2 ^ j * ρ →
      ‖b1bmo_avg (parabolicVolume m) (Metric.ball p R') g -
          b1bmo_avg (parabolicVolume m) (Metric.ball p ρ) g‖ₑ ≤
        (j : ℝ≥0∞) * (2 ^ (m + 2) * ENNReal.ofReal B) := by
  induction j with
  | zero =>
    intro R' h1 h2
    have : R' = ρ := le_antisymm (by simpa using h2) h1
    subst this
    simp
  | succ j ih =>
    intro R' h1 h2
    by_cases h3 : R' ≤ 2 ^ j * ρ
    · calc _ ≤ (j : ℝ≥0∞) * (2 ^ (m + 2) * ENNReal.ofReal B) := ih R' h1 h3
        _ ≤ ((j + 1 : ℕ) : ℝ≥0∞) * (2 ^ (m + 2) * ENNReal.ofReal B) := by
            gcongr
            exact_mod_cast Nat.le_succ j
    · set R'' := max ρ (R' / 2) with hR''def
      have hR''1 : ρ ≤ R'' := le_max_left _ _
      have hpow : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ, mul_comm]
      have hR''2 : R'' ≤ 2 ^ j * ρ := by
        refine max_le ?_ ?_
        · exact le_mul_of_one_le_left hρ.le (one_le_pow₀ one_le_two)
        · rw [hpow] at h2
          linarith
      have hR''3 : R'' ≤ R' := max_le h1 (by linarith)
      have hR''4 : R' ≤ 2 * R'' := by
        have := le_max_right ρ (R' / 2)
        linarith
      set A₁ := b1bmo_avg (parabolicVolume m) (Metric.ball p R') g
      set A₂ := b1bmo_avg (parabolicVolume m) (Metric.ball p R'') g
      set A₃ := b1bmo_avg (parabolicVolume m) (Metric.ball p ρ) g
      calc ‖A₁ - A₃‖ₑ = ‖(A₁ - A₂) + (A₂ - A₃)‖ₑ := by congr 1; ring
        _ ≤ ‖A₁ - A₂‖ₑ + ‖A₂ - A₃‖ₑ := enorm_add_le _ _
        _ ≤ 2 ^ (m + 2) * ENNReal.ofReal B + (j : ℝ≥0∞) * (2 ^ (m + 2) * ENNReal.ofReal B) :=
            add_le_add (b1bmo_avg_step hg p (lt_of_lt_of_le hρ hR''1) hR''3 hR''4)
              (ih R'' hR''1 hR''2)
        _ = ((j + 1 : ℕ) : ℝ≥0∞) * (2 ^ (m + 2) * ENNReal.ofReal B) := by
            push_cast
            ring

/-- The number of doublings: `R ≤ 2^j ρ` with `j ≤ 2 (1 + log(R/ρ))`. -/
theorem b1bmo_exists_doublings {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    ∃ j : ℕ, R ≤ 2 ^ j * ρ ∧ (j : ℝ) ≤ 2 * (1 + Real.log (R / ρ)) := by
  have hx : 1 ≤ R / ρ := (one_le_div hρ).mpr hρR
  have hx0 : 0 < R / ρ := lt_of_lt_of_le one_pos hx
  have hlog : 0 ≤ Real.log (R / ρ) := Real.log_nonneg hx
  have hlb : 0 ≤ Real.logb 2 (R / ρ) := Real.logb_nonneg one_lt_two hx
  refine ⟨⌈Real.logb 2 (R / ρ)⌉₊, ?_, ?_⟩
  · have h1 : R / ρ ≤ (2 : ℝ) ^ (⌈Real.logb 2 (R / ρ)⌉₊ : ℝ) := by
      calc R / ρ = (2 : ℝ) ^ Real.logb 2 (R / ρ) := (Real.rpow_logb two_pos (by norm_num) hx0).symm
        _ ≤ (2 : ℝ) ^ (⌈Real.logb 2 (R / ρ)⌉₊ : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)
    rw [Real.rpow_natCast] at h1
    rwa [div_le_iff₀ hρ] at h1
  · have h1 := Nat.ceil_lt_add_one hlb
    have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hlogb : Real.logb 2 (R / ρ) ≤ 2 * Real.log (R / ρ) := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
      nlinarith [mul_nonneg hlog (by linarith : (0 : ℝ) ≤ 2 * Real.log 2 - 1)]
    linarith

/-- **Clause 3 of `BMOGrowthStatement`**: concentric growth relative to the inner mean. -/
theorem b1bmo_concentric {g : Space m → ℝ} {B : ℝ} (hg : HasStandardParabolicBMOBound m g B)
    (p : Space m) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    ∫⁻ q in Metric.ball p R,
        ‖g q - b1bmo_avg (parabolicVolume m) (Metric.ball p ρ) g‖ₑ ^ 2 ∂parabolicVolume m ≤
      (2 * b1bmo_C2 m + 8 * (2 ^ (m + 2)) ^ 2) * ENNReal.ofReal B ^ 2 *
        ENNReal.ofReal ((1 + Real.log (R / ρ)) ^ 2) * parabolicVolume m (Metric.ball p R) := by
  set μ := parabolicVolume m with hμ
  have hR : 0 < R := lt_of_lt_of_le hρ hρR
  obtain ⟨j, hj1, hj2⟩ := b1bmo_exists_doublings hρ hρR
  set L := Real.log (R / ρ) with hLdef
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_div hρ).mpr hρR)
  have hshift := b1bmo_avg_tele hg p hρ j R hρR hj1
  have hj : (j : ℝ≥0∞) ≤ 2 * ENNReal.ofReal (1 + L) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hj2
  have hT : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + L) ^ 2) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hT' : ENNReal.ofReal ((1 + L) ^ 2) = ENNReal.ofReal (1 + L) ^ 2 :=
    ENNReal.ofReal_pow (by linarith) 2
  calc ∫⁻ q in Metric.ball p R, ‖g q - b1bmo_avg μ (Metric.ball p ρ) g‖ₑ ^ 2 ∂μ
      ≤ 2 * ∫⁻ q in Metric.ball p R, ‖g q - b1bmo_avg μ (Metric.ball p R) g‖ₑ ^ 2 ∂μ +
          2 * ‖b1bmo_avg μ (Metric.ball p R) g - b1bmo_avg μ (Metric.ball p ρ) g‖ₑ ^ 2 *
            μ (Metric.ball p R) :=
        b1bmo_setLIntegral_sq_shift μ _ g _ _
    _ ≤ 2 * (b1bmo_C2 m * ENNReal.ofReal B ^ 2 * μ (Metric.ball p R)) +
          2 * ((2 * ENNReal.ofReal (1 + L)) * (2 ^ (m + 2) * ENNReal.ofReal B)) ^ 2 *
            μ (Metric.ball p R) := by
        refine add_le_add ?_ ?_
        · gcongr
          exact b1bmo_ball_sq hg p hR
        · gcongr
          exact hshift.trans (by gcongr)
    _ ≤ 2 * (b1bmo_C2 m * ENNReal.ofReal B ^ 2 * ENNReal.ofReal ((1 + L) ^ 2) *
            μ (Metric.ball p R)) +
          2 * ((2 * ENNReal.ofReal (1 + L)) * (2 ^ (m + 2) * ENNReal.ofReal B)) ^ 2 *
            μ (Metric.ball p R) := by
        gcongr 2 * ?_ + _
        calc b1bmo_C2 m * ENNReal.ofReal B ^ 2 * μ (Metric.ball p R)
            = b1bmo_C2 m * ENNReal.ofReal B ^ 2 * 1 * μ (Metric.ball p R) := by ring
          _ ≤ _ := by gcongr
    _ = (2 * b1bmo_C2 m + 8 * (2 ^ (m + 2)) ^ 2) * ENNReal.ofReal B ^ 2 *
          ENNReal.ofReal ((1 + L) ^ 2) * μ (Metric.ball p R) := by
        rw [hT']
        ring

/-- **Clause 1 of `BMOGrowthStatement`**: local square integrability on every ball. -/
theorem b1bmo_memLp_ball {g : Space m → ℝ} {B : ℝ} (hg : HasStandardParabolicBMOBound m g B)
    (p : Space m) (r : ℝ) :
    MemLp g 2 ((parabolicVolume m).restrict (Metric.ball p r)) := by
  set μ := parabolicVolume m with hμ
  set r' := max r 1 with hr'def
  have hr' : 0 < r' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine MemLp.mono_measure
    (Measure.restrict_mono (Metric.ball_subset_ball (le_max_left r 1)) le_rfl) ?_
  set P := Metric.ball p r' with hPdef
  set c := b1bmo_avg μ P g with hc
  have : IsFiniteMeasure (μ.restrict P) :=
    isFiniteMeasure_restrict.mpr MeasureTheory.measure_ball_lt_top.ne
  have hae : AEStronglyMeasurable g (μ.restrict P) :=
    (b1bmo_integrableOn_ball hg.2.1 p r').aestronglyMeasurable
  have hfin : ∫⁻ q in P, ‖g q - c‖ₑ ^ 2 ∂μ < ∞ :=
    (b1bmo_ball_sq hg p hr').trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (b1bmo_C2_ne_top m)) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top))
      MeasureTheory.measure_ball_lt_top)
  have hae' : AEStronglyMeasurable (fun q => g q - c) (μ.restrict P) :=
    hae.sub aestronglyMeasurable_const
  have h1 : MemLp (fun q => g q - c) 2 (μ.restrict P) := by
    rw [memLp_two_iff_integrable_sq hae']
    refine ⟨hae'.pow 2, ?_⟩
    show ∫⁻ q, ‖(g q - c) ^ 2‖ₑ ∂(μ.restrict P) < ∞
    simp only [enorm_pow]
    exact hfin
  have h2 := h1.add (memLp_const c)
  convert h2 using 1
  ext q
  simp

/-- **Growth of parabolic BMO functions** (`BMOGrowthStatement`). No hypothesis is needed: the dyadic differentiation step is
mathlib's Lebesgue differentiation theorem for the doubling measure `parabolicVolume m`. -/
theorem ba1_bmo_growth_proof : BMOGrowthStatement := by
  intro m
  set Cfin : ℝ≥0∞ := 2 * b1bmo_C2 m + 8 * (2 ^ (m + 2)) ^ 2 with hCfindef
  have hCfin : Cfin ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) (b1bmo_C2_ne_top m),
      ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.pow_ne_top (by simp)))⟩
  refine ⟨Cfin.toReal + 1, by positivity, ?_⟩
  intro g B hg
  have hB : 0 ≤ B := hg.1
  have hC0 : 0 ≤ Cfin.toReal + 1 := by positivity
  have hofC : Cfin ≤ ENNReal.ofReal (Cfin.toReal + 1) := by
    calc Cfin = ENNReal.ofReal Cfin.toReal := (ENNReal.ofReal_toReal hCfin).symm
      _ ≤ ENNReal.ofReal (Cfin.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  have hC2 : b1bmo_C2 m ≤ Cfin := by
    have h1 : b1bmo_C2 m ≤ 2 * b1bmo_C2 m := le_mul_of_one_le_left zero_le one_le_two
    rw [hCfindef]
    exact le_add_right h1
  refine ⟨fun p r => b1bmo_memLp_ball hg p r, fun p r hr => ?_, fun p ρ R hρ hρR => ?_⟩
  · rw [b1bmo_standardBallAverage_eq]
    calc _ ≤ b1bmo_C2 m * ENNReal.ofReal B ^ 2 * parabolicVolume m (Metric.ball p r) :=
          b1bmo_ball_sq hg p hr
      _ ≤ ENNReal.ofReal ((Cfin.toReal + 1) * B ^ 2) * parabolicVolume m (Metric.ball p r) := by
          rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_pow hB]
          gcongr
          exact hC2.trans hofC
  · rw [b1bmo_standardBallAverage_eq]
    calc _ ≤ Cfin * ENNReal.ofReal B ^ 2 * ENNReal.ofReal ((1 + Real.log (R / ρ)) ^ 2) *
            parabolicVolume m (Metric.ball p R) := b1bmo_concentric hg p hρ hρR
      _ ≤ ENNReal.ofReal ((Cfin.toReal + 1) * B ^ 2 * (1 + Real.log (R / ρ)) ^ 2) *
            parabolicVolume m (Metric.ball p R) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hC0, ENNReal.ofReal_pow hB]
          gcongr

end ParabolicRectifiability.Characterization
