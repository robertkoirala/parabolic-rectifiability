import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Characterization.Proofs.Fourier.BMOGrowth

/-! # BMO growth on translated fixed cylinders: `fhpbc_c1_logGrowth_proof`

Proof of `fhpbc_c1_logGrowth : FhpbcBMOLogGrowthStatement`, without hypotheses.

The concentric mean step and telescoping (`b1bmo_avg_step`, `b1bmo_avg_tele`), the doubling
count (`b1bmo_exists_doublings`) and the ball oscillation / average helpers are existing
lemmas, used unchanged. New here:

* `fhpbc1g_avg_offcentre`: the different-centre comparison. If `dist q p ≤ r` then
  `B(q, r) ⊆ B(p, 2r)` and `|f_{B(q,r)} - f_{B(p,2r)}| ≤ 2^(m+2) B`.
* `fhpbc1g_avg_compare`: if `dist q p ≤ 2^k R₀` then
  `|f_{B(q,R₀)} - f_{B(p,R₀)}| ≤ (2k + 2) 2^(m+2) B` (concentric doublings on both sides and
  one nested-ball comparison).
* `fhpbc1g_lintegral_ball_le`: `∫_{B} |f| ≤ (B + |f_B|) |B|`.
* The assembly: with `f = g ∘ Ψ⁻¹`, `Ψ = fourierToParabolic m` measure preserving, the cylinder
  `A × [a+j, b+j]` lies in `Ψ⁻¹ B(point 0 (c + j), R₀)` with `c = (a+b)/2` and
  `R₀ = |ρ_A| + |b - a| + 1` (`A ⊆ closedBall 0 ρ_A`). The centres are at distance `√|j|`, and
  `k ≤ 2 (1 + log((R₀ + √|j|)/R₀)) ≤ 2 (1 + log(2 + |j|))` doublings suffice. The constant is
  `C = ((B + |f_{B_0}| + 6 · 2^(m+2) B) · |B_0|).toReal`, `B_0 = B(point 0 c, R₀)`.
  If `a > b` the cylinder is empty and the same bound holds trivially.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.Characterization

variable {m : ℕ}

/-- Parabolic balls of equal radius have equal volume. -/
theorem fhpbc1g_volume_ball_eq (p q : Space m) {r : ℝ} (hr : 0 < r) :
    parabolicVolume m (Metric.ball p r) = parabolicVolume m (Metric.ball q r) := by
  rw [parabolicVolume_ball p r hr, parabolicVolume_ball q r hr]

/-- **The different-centre comparison**: if `dist q p ≤ r`, then `B(q,r) ⊆ B(p,2r)` and the
means differ by at most `2^(m+2) B`. -/
theorem fhpbc1g_avg_offcentre {f : Space m → ℝ} {B : ℝ}
    (hf : HasStandardParabolicBMOBound m f B) {p q : Space m} {r : ℝ} (hr : 0 < r)
    (hqp : dist q p ≤ r) :
    ‖b1bmo_avg (parabolicVolume m) (Metric.ball q r) f -
        b1bmo_avg (parabolicVolume m) (Metric.ball p (2 * r)) f‖ₑ ≤
      2 ^ (m + 2) * ENNReal.ofReal B := by
  set μ := parabolicVolume m with hμ
  have hball := b1bmo_ballOsc_of_bound hf
  have hP0 : μ (Metric.ball q r) ≠ 0 := b1bmo_volume_ball_ne_zero q hr
  have hPt : μ (Metric.ball q r) ≠ ∞ := MeasureTheory.measure_ball_lt_top.ne
  have hsub : Metric.ball q r ⊆ Metric.ball p (2 * r) := by
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    calc dist w p ≤ dist w q + dist q p := dist_triangle _ _ _
      _ < r + r := add_lt_add_of_lt_of_le hw hqp
      _ = 2 * r := by ring
  have hvol : μ (Metric.ball p (2 * r)) = 2 ^ (m + 2) * μ (Metric.ball q r) := by
    rw [hμ, parabolicVolume_ball_two_mul p r hr, fhpbc1g_volume_ball_eq p q hr]
  calc ‖b1bmo_avg μ (Metric.ball q r) f - b1bmo_avg μ (Metric.ball p (2 * r)) f‖ₑ
      ≤ (μ (Metric.ball q r))⁻¹ *
          ∫⁻ w in Metric.ball q r, ‖f w - b1bmo_avg μ (Metric.ball p (2 * r)) f‖ₑ ∂μ :=
        b1bmo_enorm_avg_sub_le μ hP0 hPt (b1bmo_integrableOn_ball hf.2.1 q r) _
    _ ≤ (μ (Metric.ball q r))⁻¹ * (ENNReal.ofReal B * μ (Metric.ball p (2 * r))) := by
        gcongr
        exact (lintegral_mono_set hsub).trans (hball p (2 * r) (by positivity))
    _ = 2 ^ (m + 2) * ENNReal.ofReal B * ((μ (Metric.ball q r))⁻¹ * μ (Metric.ball q r)) := by
        rw [hvol]
        ring
    _ = 2 ^ (m + 2) * ENNReal.ofReal B := by rw [ENNReal.inv_mul_cancel hP0 hPt, mul_one]

/-- **Means of equal-radius balls at distance at most `2^k R₀`**: concentric doublings on both
sides (`b1bmo_avg_tele`) and one nested-ball comparison (`fhpbc1g_avg_offcentre`). -/
theorem fhpbc1g_avg_compare {f : Space m → ℝ} {B : ℝ}
    (hf : HasStandardParabolicBMOBound m f B) {R₀ : ℝ} (hR₀ : 0 < R₀) (p q : Space m) {k : ℕ}
    (hqp : dist q p ≤ 2 ^ k * R₀) :
    ‖b1bmo_avg (parabolicVolume m) (Metric.ball q R₀) f -
        b1bmo_avg (parabolicVolume m) (Metric.ball p R₀) f‖ₑ ≤
      (2 * (k : ℝ≥0∞) + 2) * (2 ^ (m + 2) * ENNReal.ofReal B) := by
  set μ := parabolicVolume m with hμ
  set S : ℝ≥0∞ := 2 ^ (m + 2) * ENNReal.ofReal B with hS
  have hpow : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
  have hr : 0 < 2 ^ k * R₀ := by positivity
  have h1 := b1bmo_avg_tele hf q hR₀ k (2 ^ k * R₀) (le_mul_of_one_le_left hR₀.le hpow) le_rfl
  have h2 := fhpbc1g_avg_offcentre hf hr hqp
  have h3 := b1bmo_avg_tele hf p hR₀ (k + 1) (2 * (2 ^ k * R₀)) (by nlinarith)
    (le_of_eq (by ring))
  set X := b1bmo_avg μ (Metric.ball q R₀) f
  set Y := b1bmo_avg μ (Metric.ball q (2 ^ k * R₀)) f
  set Z := b1bmo_avg μ (Metric.ball p (2 * (2 ^ k * R₀))) f
  set W := b1bmo_avg μ (Metric.ball p R₀) f
  calc ‖X - W‖ₑ = ‖-(Y - X) + (Y - Z) + (Z - W)‖ₑ := by congr 1; ring
    _ ≤ ‖-(Y - X)‖ₑ + ‖Y - Z‖ₑ + ‖Z - W‖ₑ :=
        (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)
    _ = ‖Y - X‖ₑ + ‖Y - Z‖ₑ + ‖Z - W‖ₑ := by rw [enorm_neg]
    _ ≤ (k : ℝ≥0∞) * S + S + ((k + 1 : ℕ) : ℝ≥0∞) * S := add_le_add (add_le_add h1 h2) h3
    _ = (2 * (k : ℝ≥0∞) + 2) * S := by
        push_cast
        ring

/-- **Oscillation plus mean** on one ball: `∫_B |f| ≤ (B + |f_B|) |B|`. -/
theorem fhpbc1g_lintegral_ball_le {f : Space m → ℝ} {B : ℝ}
    (hf : HasStandardParabolicBMOBound m f B) (p : Space m) {r : ℝ} (hr : 0 < r) :
    ∫⁻ z in Metric.ball p r, ‖f z‖ₑ ∂parabolicVolume m ≤
      (ENNReal.ofReal B + ‖b1bmo_avg (parabolicVolume m) (Metric.ball p r) f‖ₑ) *
        parabolicVolume m (Metric.ball p r) := by
  set μ := parabolicVolume m with hμ
  set c := b1bmo_avg μ (Metric.ball p r) f with hc
  calc ∫⁻ z in Metric.ball p r, ‖f z‖ₑ ∂μ
      ≤ ∫⁻ z in Metric.ball p r, (‖f z - c‖ₑ + ‖c‖ₑ) ∂μ := by
        refine lintegral_mono fun z => ?_
        calc ‖f z‖ₑ = ‖(f z - c) + c‖ₑ := by rw [sub_add_cancel]
          _ ≤ ‖f z - c‖ₑ + ‖c‖ₑ := enorm_add_le _ _
    _ = ∫⁻ z in Metric.ball p r, ‖f z - c‖ₑ ∂μ + ‖c‖ₑ * μ (Metric.ball p r) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ ENNReal.ofReal B * μ (Metric.ball p r) + ‖c‖ₑ * μ (Metric.ball p r) := by
        gcongr
        exact b1bmo_ballOsc_of_bound hf p r hr
    _ = (ENNReal.ofReal B + ‖c‖ₑ) * μ (Metric.ball p r) := by ring

/-- The cylinder `A × [a+j, b+j]` lies in the preimage of one parabolic ball of fixed radius. -/
theorem fhpbc1g_cylinder_subset {A : Set (Spatial m)} {ρA : ℝ}
    (hρA : A ⊆ Metric.closedBall 0 ρA) (a b : ℝ) (j : ℤ) :
    fhp_cylinder A (Icc (a + j) (b + j)) ⊆
      (fourierToParabolicMeasurableEquiv m) ⁻¹'
        Metric.ball (point (0 : Spatial m) ((a + b) / 2 + j)) (|ρA| + |b - a| + 1) := by
  have hR₀1 : 1 ≤ |ρA| + |b - a| + 1 := by linarith [abs_nonneg ρA, abs_nonneg (b - a)]
  have hR₀ : 0 < |ρA| + |b - a| + 1 := by linarith
  have hsq : |ρA| + |b - a| + 1 ≤ (|ρA| + |b - a| + 1) ^ 2 := by nlinarith
  intro x hx
  have hx' : (WithLp.ofLp x).1 ∈ A ∧ (WithLp.ofLp x).2 ∈ Icc (a + j) (b + j) := hx
  obtain ⟨hxA, ht1, ht2⟩ := hx'
  rw [mem_preimage, fourierToParabolicMeasurableEquiv_apply, mem_ball_point _ _ _ _ _ hR₀]
  constructor
  · have h := hρA hxA
    rw [Metric.mem_closedBall, dist_zero_right] at h
    rw [sub_zero]
    linarith [le_abs_self ρA, abs_nonneg (b - a)]
  · rw [abs_lt]
    constructor <;> linarith [le_abs_self (b - a), neg_abs_le (b - a), abs_nonneg ρA]

/-- `log((R₀ + √|j|)/R₀) ≤ log(2 + |j|)` for `R₀ ≥ 1`. -/
theorem fhpbc1g_log_le {R₀ : ℝ} (hR₀1 : 1 ≤ R₀) (j : ℝ) :
    Real.log ((R₀ + Real.sqrt |j|) / R₀) ≤ Real.log (2 + |j|) := by
  have hR₀ : 0 < R₀ := by linarith
  have hs := Real.sqrt_nonneg |j|
  have hs2 : Real.sqrt |j| ^ 2 = |j| := Real.sq_sqrt (abs_nonneg j)
  refine Real.log_le_log (div_pos (by linarith) hR₀) ?_
  rw [div_le_iff₀ hR₀]
  nlinarith [mul_nonneg (sub_nonneg.mpr hR₀1) (by positivity : (0 : ℝ) ≤ 1 + |j|),
    sq_nonneg (Real.sqrt |j| - 1)]

/-- **BMO growth on translated fixed cylinders** (`fhpbc_c1_logGrowth`), of type
`FhpbcBMOLogGrowthStatement`. No hypothesis is needed. -/
theorem fhpbc_c1_logGrowth_proof : FhpbcBMOLogGrowthStatement := by
  intro m g hg A hA _hAm a b
  obtain ⟨B, hf⟩ := hg
  set f : Space m → ℝ := g ∘ (fourierToParabolic m).symm with hfdef
  set μ := parabolicVolume m with hμ
  obtain ⟨ρA, hρA⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Spatial m)).mp hA
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = |ρA| + |b - a| + 1 := ⟨_, rfl⟩
  have hR₀1 : 1 ≤ R₀ := by rw [hR₀def]; linarith [abs_nonneg ρA, abs_nonneg (b - a)]
  have hR₀ : 0 < R₀ := by linarith
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : Space m, p₀ = point (0 : Spatial m) ((a + b) / 2) := ⟨_, rfl⟩
  set S : ℝ≥0∞ := 2 ^ (m + 2) * ENNReal.ofReal B with hS
  set K : ℝ≥0∞ := ENNReal.ofReal B + ‖b1bmo_avg μ (Metric.ball p₀ R₀) f‖ₑ + 6 * S with hK
  set V : ℝ≥0∞ := μ (Metric.ball p₀ R₀) with hV
  have hKt : K ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, enorm_ne_top⟩,
      ENNReal.mul_ne_top (by simp)
        (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) ENNReal.ofReal_ne_top)⟩
  have hVt : V ≠ ∞ := MeasureTheory.measure_ball_lt_top.ne
  refine ⟨(K * V).toReal, fun j => ?_⟩
  set L : ℝ := 1 + Real.log (2 + |(j : ℝ)|) with hL
  have hL0 : 0 ≤ Real.log (2 + |(j : ℝ)|) :=
    Real.log_nonneg (by linarith [abs_nonneg (j : ℝ)])
  obtain ⟨pj, hpj⟩ : ∃ pj : Space m, pj = point (0 : Spatial m) ((a + b) / 2 + j) := ⟨_, rfl⟩
  -- transport to the parabolic side and enclose the cylinder in one ball
  have hcyl : fhp_cylinder A (Icc (a + j) (b + j)) ⊆
      (fourierToParabolicMeasurableEquiv m) ⁻¹' Metric.ball pj R₀ := by
    rw [hpj, hR₀def]
    exact fhpbc1g_cylinder_subset hρA a b j
  have htrans : ∫⁻ x in fhp_cylinder A (Icc (a + j) (b + j)), ‖g x‖ₑ ≤
      ∫⁻ z in Metric.ball pj R₀, ‖f z‖ₑ ∂μ := by
    calc ∫⁻ x in fhp_cylinder A (Icc (a + j) (b + j)), ‖g x‖ₑ
        ≤ ∫⁻ x in (fourierToParabolicMeasurableEquiv m) ⁻¹' Metric.ball pj R₀, ‖g x‖ₑ :=
          lintegral_mono_set hcyl
      _ = ∫⁻ x in (fourierToParabolicMeasurableEquiv m) ⁻¹' Metric.ball pj R₀,
            ‖f (fourierToParabolicMeasurableEquiv m x)‖ₑ := by
          refine lintegral_congr fun x => ?_
          show ‖g x‖ₑ = ‖g ((fourierToParabolic m).symm (fourierToParabolic m x))‖ₑ
          rw [Homeomorph.symm_apply_apply]
      _ = ∫⁻ z in Metric.ball pj R₀, ‖f z‖ₑ ∂μ :=
          (fourierToParabolic_measurePreserving m).setLIntegral_comp_preimage_emb
            (fourierToParabolicMeasurableEquiv m).measurableEmbedding (fun z => ‖f z‖ₑ) _
  have hball := fhpbc1g_lintegral_ball_le hf pj hR₀
  have hVj : μ (Metric.ball pj R₀) = V := fhpbc1g_volume_ball_eq pj p₀ hR₀
  -- the number of doublings
  obtain ⟨k, hk1, hk2⟩ := b1bmo_exists_doublings hR₀
    (le_add_of_nonneg_right (Real.sqrt_nonneg |(j : ℝ)|) : R₀ ≤ R₀ + Real.sqrt |(j : ℝ)|)
  have hdist : dist pj p₀ ≤ 2 ^ k * R₀ := by
    rw [hpj, hp₀, dist_point, sub_self, norm_zero,
      show (a + b) / 2 + (j : ℝ) - (a + b) / 2 = j by ring,
      max_eq_right (Real.sqrt_nonneg _)]
    linarith
  have hcomp := fhpbc1g_avg_compare hf hR₀ p₀ pj hdist
  have hkL : (k : ℝ≥0∞) ≤ 2 * ENNReal.ofReal L := by
    have hlog := fhpbc1g_log_le hR₀1 (j : ℝ)
    have hkr : (k : ℝ) ≤ 2 * L := by rw [hL]; linarith
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hkr
  have hL1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal L := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by rw [hL]; linarith)
  -- the mean of the far ball
  set Aj := b1bmo_avg μ (Metric.ball pj R₀) f with hAj
  set A0 := b1bmo_avg μ (Metric.ball p₀ R₀) f with hA0
  have havg : ENNReal.ofReal B + ‖Aj‖ₑ ≤ K * ENNReal.ofReal L := by
    have h1 : ‖Aj‖ₑ ≤ ‖A0‖ₑ + (2 * (k : ℝ≥0∞) + 2) * S := by
      calc ‖Aj‖ₑ = ‖A0 + (Aj - A0)‖ₑ := by rw [add_sub_cancel]
        _ ≤ ‖A0‖ₑ + ‖Aj - A0‖ₑ := enorm_add_le _ _
        _ ≤ ‖A0‖ₑ + (2 * (k : ℝ≥0∞) + 2) * S := by gcongr
    have h2 : 2 * (k : ℝ≥0∞) + 2 ≤ 6 * ENNReal.ofReal L := by
      calc 2 * (k : ℝ≥0∞) + 2 = 2 * (k : ℝ≥0∞) + 2 * 1 := by rw [mul_one]
        _ ≤ 2 * (2 * ENNReal.ofReal L) + 2 * ENNReal.ofReal L := by gcongr
        _ = 6 * ENNReal.ofReal L := by ring
    calc ENNReal.ofReal B + ‖Aj‖ₑ
        ≤ ENNReal.ofReal B + (‖A0‖ₑ + (2 * (k : ℝ≥0∞) + 2) * S) := by gcongr
      _ = (ENNReal.ofReal B + ‖A0‖ₑ) * 1 + (2 * (k : ℝ≥0∞) + 2) * S := by ring
      _ ≤ (ENNReal.ofReal B + ‖A0‖ₑ) * ENNReal.ofReal L + (6 * ENNReal.ofReal L) * S := by
          gcongr
      _ = K * ENNReal.ofReal L := by rw [hK]; ring
  calc ∫⁻ x in fhp_cylinder A (Icc (a + j) (b + j)), ‖g x‖ₑ
      ≤ ∫⁻ z in Metric.ball pj R₀, ‖f z‖ₑ ∂μ := htrans
    _ ≤ (ENNReal.ofReal B + ‖Aj‖ₑ) * μ (Metric.ball pj R₀) := hball
    _ ≤ K * ENNReal.ofReal L * V := by
        rw [hVj]
        gcongr
    _ = ENNReal.ofReal ((K * V).toReal * L) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (ENNReal.mul_ne_top hKt hVt)]
        ring

/-- The proof has exactly the type of the statement. -/
example : FhpbcBMOLogGrowthStatement := fhpbc_c1_logGrowth_proof

end ParabolicRectifiability.Foundations
