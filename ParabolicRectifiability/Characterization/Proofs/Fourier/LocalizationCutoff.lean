import ParabolicRectifiability.Characterization.Proofs.Fourier.LocalizationPlancherel

/-! # Critical Sobolev localization: the cutoff, the localized function and its easy energies

Part of the proof of `ba1_critical_sobolev_localization_proof`. With `Ψ = fourierToParabolic m` and `x₀ = Ψ⁻¹ p₀`, the localized function is
`H = χ_{x₀} · (F ∘ Ψ - F(p₀))` on `FourierSpace m`, with the `1`-Lipschitz Euclidean cutoff
`χ_{x₀}(x) = max 0 (min 1 (6 - ‖x - x₀‖))`: it is `1` on `B(x₀,5) ⊇ Ψ⁻¹ P(p₀,2)` and `0` off
`B(x₀,6)`. No smoothness of the cutoff is needed, because every energy is computed through
difference quotients (`b1loc_lintegral_inner_sq_fourier_le`).

This file proves the parts of the energy bound that use only the Lipschitz bound:
* agreement `H = F ∘ Ψ - F(p₀)` on `Ψ⁻¹ P(p₀,2)`, and `H ∈ L²` (continuous, compact support);
* `∫ |H|² ≤ 49 V L²` and `∫ |ξ|² |Ĥ|² ≤ 4 m V L²`, `V = |B(0,7)|` (Euclidean volume in
  `FourierSpace m`), through the spatial difference quotients `|H(x + s e_i) - H(x)| ≤ 8 L s` on
  `B(x₀,7)`, `0 < s ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.HalfTimeDerivative

attribute [local instance] FourierAffine.continuousSMul_fourierSpace

variable {m : ℕ}

/-! ## Coordinates -/

theorem b1loc_norm_fst_le (z : FourierSpace m) : ‖(WithLp.ofLp z).1‖ ≤ ‖z‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 z
  have h1 := norm_nonneg (WithLp.ofLp z).1
  have h2 := norm_nonneg z
  have h3 := sq_nonneg ‖(WithLp.ofLp z).2‖
  change ‖z‖ ^ 2 = ‖(WithLp.ofLp z).1‖ ^ 2 + ‖(WithLp.ofLp z).2‖ ^ 2 at h
  nlinarith

theorem b1loc_abs_snd_le (z : FourierSpace m) : |(WithLp.ofLp z).2| ≤ ‖z‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 z
  have h1 := norm_nonneg (WithLp.ofLp z).2
  have h2 := norm_nonneg z
  have h3 := sq_nonneg ‖(WithLp.ofLp z).1‖
  change ‖z‖ ^ 2 = ‖(WithLp.ofLp z).1‖ ^ 2 + ‖(WithLp.ofLp z).2‖ ^ 2 at h
  rw [← Real.norm_eq_abs]
  nlinarith

/-- The parabolic distance in ordinary coordinates. -/
theorem b1loc_dist_fourierToParabolic (x y : FourierSpace m) :
    dist (fourierToParabolic m x) (fourierToParabolic m y) =
      max ‖(WithLp.ofLp (x - y)).1‖ (Real.sqrt |(WithLp.ofLp (x - y)).2|) := by
  rw [fourierToParabolic_apply, fourierToParabolic_apply, dist_point, WithLp.ofLp_sub,
    Prod.fst_sub, Prod.snd_sub]

theorem b1loc_dist_fourierToParabolic_le {x y : FourierSpace m} {r : ℝ} (hr : 1 ≤ r)
    (hxy : ‖x - y‖ ≤ r) : dist (fourierToParabolic m x) (fourierToParabolic m y) ≤ r := by
  rw [b1loc_dist_fourierToParabolic]
  apply max_le ((b1loc_norm_fst_le _).trans hxy)
  rw [Real.sqrt_le_left (by linarith)]
  calc |(WithLp.ofLp (x - y)).2| ≤ ‖x - y‖ := b1loc_abs_snd_le _
    _ ≤ r := hxy
    _ ≤ r ^ 2 := by nlinarith

/-! ## The cutoff -/

/-- The localization cutoff around `x₀`. -/
def b1loc_cut (x₀ x : FourierSpace m) : ℝ := max 0 (min 1 (6 - ‖x - x₀‖))

theorem b1loc_cut_nonneg (x₀ x : FourierSpace m) : 0 ≤ b1loc_cut x₀ x := le_max_left _ _

theorem b1loc_cut_le_one (x₀ x : FourierSpace m) : b1loc_cut x₀ x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem b1loc_cut_eq_one {x₀ x : FourierSpace m} (h : ‖x - x₀‖ ≤ 5) : b1loc_cut x₀ x = 1 := by
  unfold b1loc_cut
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem b1loc_cut_eq_zero {x₀ x : FourierSpace m} (h : 6 ≤ ‖x - x₀‖) : b1loc_cut x₀ x = 0 := by
  unfold b1loc_cut
  exact max_eq_left (min_le_of_right_le (by linarith))

theorem b1loc_abs_cut_sub_le (x₀ x y : FourierSpace m) :
    |b1loc_cut x₀ x - b1loc_cut x₀ y| ≤ ‖x - y‖ := by
  unfold b1loc_cut
  calc |max 0 (min 1 (6 - ‖x - x₀‖)) - max 0 (min 1 (6 - ‖y - x₀‖))|
      ≤ |min 1 (6 - ‖x - x₀‖) - min 1 (6 - ‖y - x₀‖)| := by
        rw [max_comm 0 (min 1 (6 - ‖x - x₀‖)), max_comm 0 (min 1 (6 - ‖y - x₀‖))]
        exact abs_max_sub_max_le_abs _ _ _
    _ ≤ max |1 - 1| |(6 - ‖x - x₀‖) - (6 - ‖y - x₀‖)| := abs_min_sub_min_le_max _ _ _ _
    _ = |‖y - x₀‖ - ‖x - x₀‖| := by
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
        congr 1
        ring
    _ ≤ ‖(y - x₀) - (x - x₀)‖ := abs_norm_sub_norm_le _ _
    _ = ‖x - y‖ := by rw [sub_sub_sub_cancel_right, norm_sub_rev]

theorem b1loc_continuous_cut (x₀ : FourierSpace m) : Continuous (b1loc_cut x₀) :=
  continuous_const.max (continuous_const.min (continuous_const.sub
    (continuous_id.sub continuous_const).norm))

/-! ## The localized function -/

/-- `H = χ_{x₀} · (F ∘ Ψ - F(p₀))` with `x₀ = Ψ⁻¹ p₀`. -/
def b1loc_localized (m : ℕ) (F : Space m → ℝ) (p₀ : Space m) (x : FourierSpace m) : ℝ :=
  b1loc_cut ((fourierToParabolic m).symm p₀) x * (F (fourierToParabolic m x) - F p₀)

/-- `|F(Ψ x) - F(p₀)| ≤ r L` when `‖x - x₀‖ ≤ r`, `r ≥ 1`. -/
theorem b1loc_abs_sub_le {F : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F) (p₀ : Space m)
    {x : FourierSpace m} {r : ℝ} (hr : 1 ≤ r)
    (hx : ‖x - (fourierToParabolic m).symm p₀‖ ≤ r) :
    |F (fourierToParabolic m x) - F p₀| ≤ r * L := by
  have hd := b1loc_dist_fourierToParabolic_le hr hx
  rw [Homeomorph.apply_symm_apply] at hd
  have h := hL.dist_le_mul (fourierToParabolic m x) p₀
  rw [Real.dist_eq] at h
  calc |F (fourierToParabolic m x) - F p₀| ≤ L * dist (fourierToParabolic m x) p₀ := h
    _ ≤ L * r := mul_le_mul_of_nonneg_left hd L.2
    _ = r * L := mul_comm _ _

theorem b1loc_localized_eq {F : Space m → ℝ} (p₀ : Space m) (x : FourierSpace m)
    (hx : fourierToParabolic m x ∈ Metric.ball p₀ 2) :
    b1loc_localized m F p₀ x = F (fourierToParabolic m x) - F p₀ := by
  unfold b1loc_localized
  rw [b1loc_cut_eq_one, one_mul]
  set x₀ := (fourierToParabolic m).symm p₀ with hx₀
  have hp₀ : p₀ = fourierToParabolic m x₀ := by rw [hx₀, Homeomorph.apply_symm_apply]
  rw [Metric.mem_ball, hp₀, b1loc_dist_fourierToParabolic, max_lt_iff] at hx
  obtain ⟨h1, h2⟩ := hx
  have h2' : |(WithLp.ofLp (x - x₀)).2| < 4 := by
    have := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).1 h2
    linarith
  have hsq := WithLp.prod_norm_sq_eq_of_L2 (x - x₀)
  change ‖x - x₀‖ ^ 2 = ‖(WithLp.ofLp (x - x₀)).1‖ ^ 2 + ‖(WithLp.ofLp (x - x₀)).2‖ ^ 2 at hsq
  rw [Real.norm_eq_abs (WithLp.ofLp (x - x₀)).2] at hsq
  have hn1 := norm_nonneg (WithLp.ofLp (x - x₀)).1
  have hn2 := abs_nonneg (WithLp.ofLp (x - x₀)).2
  have hn := norm_nonneg (x - x₀)
  nlinarith

theorem b1loc_localized_eq_zero {F : Space m → ℝ} (p₀ : Space m) {x : FourierSpace m}
    (hx : 6 ≤ ‖x - (fourierToParabolic m).symm p₀‖) : b1loc_localized m F p₀ x = 0 := by
  unfold b1loc_localized
  rw [b1loc_cut_eq_zero hx, zero_mul]

theorem b1loc_abs_localized_le {F : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F)
    (p₀ : Space m) (x : FourierSpace m) : |b1loc_localized m F p₀ x| ≤ 6 * L := by
  by_cases hx : 6 ≤ ‖x - (fourierToParabolic m).symm p₀‖
  · rw [b1loc_localized_eq_zero p₀ hx, abs_zero]
    positivity
  · unfold b1loc_localized
    rw [abs_mul, abs_of_nonneg (b1loc_cut_nonneg _ _)]
    calc b1loc_cut _ x * |F (fourierToParabolic m x) - F p₀| ≤ 1 * (6 * L) :=
          mul_le_mul (b1loc_cut_le_one _ _) (b1loc_abs_sub_le hL p₀ (by norm_num) (by linarith))
            (abs_nonneg _) zero_le_one
      _ = 6 * L := one_mul _

theorem b1loc_continuous_localized {F : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F)
    (p₀ : Space m) : Continuous (b1loc_localized m F p₀) :=
  (b1loc_continuous_cut _).mul
    ((hL.continuous.comp (fourierToParabolic m).continuous).sub continuous_const)

theorem b1loc_hasCompactSupport_localized (F : Space m → ℝ) (p₀ : Space m) :
    HasCompactSupport (b1loc_localized m F p₀) := by
  refine HasCompactSupport.intro (isCompact_closedBall ((fourierToParabolic m).symm p₀) 6)
    fun x hx => b1loc_localized_eq_zero p₀ ?_
  rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hx
  exact hx.le

theorem b1loc_memLp_localized {F : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F)
    (p₀ : Space m) : MemLp (b1loc_localized m F p₀) 2 volume :=
  (b1loc_continuous_localized hL p₀).memLp_of_hasCompactSupport
    (b1loc_hasCompactSupport_localized F p₀)

/-! ## The `L²` bound -/

/-- `V = |B(0,7)|` in `FourierSpace m`. -/
def b1loc_ballVolume (m : ℕ) : ℝ :=
  (volume (Metric.ball (0 : FourierSpace m) 7)).toReal

theorem b1loc_ballVolume_nonneg (m : ℕ) : 0 ≤ b1loc_ballVolume m := ENNReal.toReal_nonneg

theorem b1loc_volume_ball_seven (x₀ : FourierSpace m) :
    volume (Metric.ball x₀ 7) = ENNReal.ofReal (b1loc_ballVolume m) := by
  rw [b1loc_ballVolume, ENNReal.ofReal_toReal (MeasureTheory.measure_ball_lt_top).ne,
    Measure.addHaar_ball_center]

/-- A pointwise bound `|f| ≤ c` on `B(x₀,7)`, with `f = 0` off it, gives `∫ |f|² ≤ c² V`. -/
theorem b1loc_lintegral_sq_le_of_ball {f : FourierSpace m → ℝ} (x₀ : FourierSpace m) {c : ℝ}
    (hf : ∀ x, ‖x - x₀‖ < 7 → |f x| ≤ c) (hf0 : ∀ x, 7 ≤ ‖x - x₀‖ → f x = 0) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ≤ ENNReal.ofReal (c ^ 2 * b1loc_ballVolume m) := by
  calc ∫⁻ x, ‖f x‖ₑ ^ 2 ≤ ∫⁻ x, (Metric.ball x₀ 7).indicator
        (fun _ => ENNReal.ofReal (c ^ 2)) x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : ‖x - x₀‖ < 7
        · have hmem : x ∈ Metric.ball x₀ 7 := by rwa [Metric.mem_ball, dist_eq_norm]
          rw [indicator_of_mem hmem, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          rw [Real.norm_eq_abs, sq_abs]
          have h1 := hf x hx
          have h2 := abs_nonneg (f x)
          nlinarith [sq_abs (f x)]
        · rw [hf0 x (not_lt.mp hx), enorm_zero]
          simp
    _ = ENNReal.ofReal (c ^ 2 * b1loc_ballVolume m) := by
        rw [lintegral_indicator_const measurableSet_ball, b1loc_volume_ball_seven,
          ← ENNReal.ofReal_mul (sq_nonneg c)]

theorem b1loc_lintegral_localized_sq_le {F : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F)
    (p₀ : Space m) :
    ∫⁻ x, ‖b1loc_localized m F p₀ x‖ₑ ^ 2 ≤
      ENNReal.ofReal (49 * b1loc_ballVolume m * (L : ℝ) ^ 2) := by
  have h := b1loc_lintegral_sq_le_of_ball (f := b1loc_localized m F p₀)
    ((fourierToParabolic m).symm p₀) (c := 7 * L)
    (fun x _ => (b1loc_abs_localized_le hL p₀ x).trans (by nlinarith [L.2]))
    (fun x hx => b1loc_localized_eq_zero p₀ (by linarith))
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

/-! ## Spatial difference quotients and the spatial energy -/

/-- The spatial unit vector `e_i = (single i 1, 0)`. -/
def b1loc_spatialVector (i : Fin m) : FourierSpace m :=
  WithLp.toLp 2 (EuclideanSpace.single i (1 : ℝ), 0)

theorem b1loc_inner_spatialVector (i : Fin m) (ζ : FourierSpace m) :
    inner ℝ (b1loc_spatialVector i) ζ = (WithLp.ofLp ζ).1 i := by
  rw [b1loc_spatialVector, WithLp.prod_inner_apply]
  simp [EuclideanSpace.inner_single_left]

theorem b1loc_norm_single (i : Fin m) : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
  rw [EuclideanSpace.single, PiLp.norm_single, norm_one]

theorem b1loc_norm_spatialVector (i : Fin m) : ‖b1loc_spatialVector i‖ = 1 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (b1loc_spatialVector i)
  change ‖b1loc_spatialVector i‖ ^ 2 = ‖EuclideanSpace.single i (1 : ℝ)‖ ^ 2 + ‖(0 : ℝ)‖ ^ 2 at h
  rw [b1loc_norm_single, norm_zero] at h
  have hn := norm_nonneg (b1loc_spatialVector i)
  nlinarith

/-- A spatial shift moves `Ψ x` by exactly its length. -/
theorem b1loc_dist_spatial_shift (x : FourierSpace m) (i : Fin m) {s : ℝ} (hs : 0 ≤ s) :
    dist (fourierToParabolic m (x + s • b1loc_spatialVector i)) (fourierToParabolic m x) = s := by
  rw [b1loc_dist_fourierToParabolic, add_sub_cancel_left]
  have h1 : (WithLp.ofLp (s • b1loc_spatialVector i)).1 = s • EuclideanSpace.single i (1 : ℝ) := rfl
  have h2 : (WithLp.ofLp (s • b1loc_spatialVector i)).2 = s * 0 := rfl
  rw [h1, h2, mul_zero, abs_zero, Real.sqrt_zero, norm_smul, b1loc_norm_single,
    mul_one, Real.norm_eq_abs, abs_of_nonneg hs, max_eq_left hs]

theorem b1loc_localized_spatial_diff {F : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F)
    (p₀ : Space m) (i : Fin m) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∫⁻ x, ‖b1loc_localized m F p₀ (x + s • b1loc_spatialVector i) -
        b1loc_localized m F p₀ x‖ₑ ^ 2 ≤
      ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (64 * b1loc_ballVolume m * (L : ℝ) ^ 2) := by
  set x₀ := (fourierToParabolic m).symm p₀ with hx₀
  have hv : ‖s • b1loc_spatialVector i‖ = s := by
    rw [norm_smul, b1loc_norm_spatialVector, mul_one, Real.norm_eq_abs, abs_of_pos hs0]
  have h := b1loc_lintegral_sq_le_of_ball
    (f := fun x => b1loc_localized m F p₀ (x + s • b1loc_spatialVector i) -
      b1loc_localized m F p₀ x) x₀ (c := 8 * L * s) ?_ ?_
  · refine h.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (sq_nonneg s)]
    congr 1
    ring
  · intro x hx
    have hshift : ‖x + s • b1loc_spatialVector i - x₀‖ ≤ 8 := by
      calc ‖x + s • b1loc_spatialVector i - x₀‖ = ‖(x - x₀) + s • b1loc_spatialVector i‖ := by
            congr 1
            abel
        _ ≤ ‖x - x₀‖ + ‖s • b1loc_spatialVector i‖ := norm_add_le _ _
        _ ≤ 8 := by rw [hv]; linarith
    have hG : |F (fourierToParabolic m x) - F p₀| ≤ 7 * L :=
      b1loc_abs_sub_le hL p₀ (by norm_num) hx.le
    have hGG : |F (fourierToParabolic m (x + s • b1loc_spatialVector i)) -
        F (fourierToParabolic m x)| ≤ L * s := by
      have h' := hL.dist_le_mul (fourierToParabolic m (x + s • b1loc_spatialVector i))
        (fourierToParabolic m x)
      rwa [Real.dist_eq, b1loc_dist_spatial_shift x i hs0.le] at h'
    have hχ : |b1loc_cut x₀ (x + s • b1loc_spatialVector i) - b1loc_cut x₀ x| ≤ s := by
      have := b1loc_abs_cut_sub_le x₀ (x + s • b1loc_spatialVector i) x
      rwa [add_sub_cancel_left, hv] at this
    have hc1 := b1loc_cut_le_one x₀ (x + s • b1loc_spatialVector i)
    have hc0 := b1loc_cut_nonneg x₀ (x + s • b1loc_spatialVector i)
    unfold b1loc_localized
    rw [← hx₀]
    have hdecomp : b1loc_cut x₀ (x + s • b1loc_spatialVector i) *
          (F (fourierToParabolic m (x + s • b1loc_spatialVector i)) - F p₀) -
        b1loc_cut x₀ x * (F (fourierToParabolic m x) - F p₀) =
        b1loc_cut x₀ (x + s • b1loc_spatialVector i) *
            (F (fourierToParabolic m (x + s • b1loc_spatialVector i)) -
              F (fourierToParabolic m x)) +
          (b1loc_cut x₀ (x + s • b1loc_spatialVector i) - b1loc_cut x₀ x) *
            (F (fourierToParabolic m x) - F p₀) := by ring
    rw [hdecomp]
    calc |_ + _| ≤ |b1loc_cut x₀ (x + s • b1loc_spatialVector i) *
            (F (fourierToParabolic m (x + s • b1loc_spatialVector i)) -
              F (fourierToParabolic m x))| +
          |(b1loc_cut x₀ (x + s • b1loc_spatialVector i) - b1loc_cut x₀ x) *
            (F (fourierToParabolic m x) - F p₀)| := abs_add_le _ _
      _ ≤ 1 * (L * s) + s * (7 * L) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hc0]
          exact add_le_add (mul_le_mul hc1 hGG (abs_nonneg _) zero_le_one)
            (mul_le_mul hχ hG (abs_nonneg _) hs0.le)
      _ = 8 * L * s := by ring
  · intro x hx
    have h1 : b1loc_localized m F p₀ x = 0 := b1loc_localized_eq_zero p₀ (by linarith)
    have h2 : b1loc_localized m F p₀ (x + s • b1loc_spatialVector i) = 0 := by
      apply b1loc_localized_eq_zero p₀
      calc (6 : ℝ) ≤ ‖x - x₀‖ - ‖s • b1loc_spatialVector i‖ := by rw [hv]; linarith
        _ ≤ ‖x + s • b1loc_spatialVector i - x₀‖ := by
            have := norm_sub_norm_le (x - x₀) (-(s • b1loc_spatialVector i))
            rw [norm_neg, sub_neg_eq_add] at this
            calc ‖x - x₀‖ - ‖s • b1loc_spatialVector i‖ ≤ ‖x - x₀ + s • b1loc_spatialVector i‖ :=
                  this
              _ = _ := by congr 1; abel
    simp only [h1, h2, sub_zero]

/-- `|ξ|² = ∑_i ⟨e_i, ζ⟩²`. -/
theorem b1loc_norm_sq_spatial (ζ : FourierSpace m) :
    ‖(WithLp.ofLp ζ).1‖ ^ 2 = ∑ i : Fin m, inner ℝ (b1loc_spatialVector i) ζ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [b1loc_inner_spatialVector, Real.norm_eq_abs, sq_abs]

/-- **Spatial energy.** `∫ |ξ|² |Ĥ|² ≤ 4 m V L²`. -/
theorem b1loc_spatial_energy_le {F : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F)
    (p₀ : Space m) :
    ∫⁻ ζ, ENNReal.ofReal (‖(WithLp.ofLp ζ).1‖ ^ 2) *
        ‖(𝓕 (realLp (b1loc_memLp_localized hL p₀)) :
          Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * m * b1loc_ballVolume m * (L : ℝ) ^ 2) := by
  set hH := b1loc_memLp_localized hL p₀
  have hmeas : ∀ i : Fin m, Measurable fun ζ : FourierSpace m =>
      ENNReal.ofReal (inner ℝ (b1loc_spatialVector i) ζ ^ 2) *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := fun i =>
    ((continuous_const.inner continuous_id).pow 2).measurable.ennreal_ofReal.mul
      ((Lp.stronglyMeasurable _).measurable.enorm.pow_const 2)
  have hi : ∀ i : Fin m, ∫⁻ ζ, ENNReal.ofReal (inner ℝ (b1loc_spatialVector i) ζ ^ 2) *
      ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 ≤
        ENNReal.ofReal (4 * b1loc_ballVolume m * (L : ℝ) ^ 2) := by
    intro i
    have h := b1loc_lintegral_inner_sq_fourier_le hH (b1loc_spatialVector i)
      (ENNReal.ofReal (64 * b1loc_ballVolume m * (L : ℝ) ^ 2))
      (fun s hs0 hs1 => b1loc_localized_spatial_diff hL p₀ i hs0 hs1)
    have h64 : ENNReal.ofReal (64 * b1loc_ballVolume m * (L : ℝ) ^ 2) =
        ENNReal.ofReal 16 * ENNReal.ofReal (4 * b1loc_ballVolume m * (L : ℝ) ^ 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    rw [h64] at h
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) ENNReal.ofReal_ne_top).1 h
  calc ∫⁻ ζ, ENNReal.ofReal (‖(WithLp.ofLp ζ).1‖ ^ 2) *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2
      = ∫⁻ ζ, ∑ i : Fin m, ENNReal.ofReal (inner ℝ (b1loc_spatialVector i) ζ ^ 2) *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
        refine lintegral_congr fun ζ => ?_
        rw [b1loc_norm_sq_spatial, ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _),
          Finset.sum_mul]
    _ = ∑ i : Fin m, ∫⁻ ζ, ENNReal.ofReal (inner ℝ (b1loc_spatialVector i) ζ ^ 2) *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 :=
        lintegral_finsetSum _ fun i _ => hmeas i
    _ ≤ ∑ _i : Fin m, ENNReal.ofReal (4 * b1loc_ballVolume m * (L : ℝ) ^ 2) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = ENNReal.ofReal (4 * m * b1loc_ballVolume m * (L : ℝ) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        ring

end ParabolicRectifiability.Characterization
