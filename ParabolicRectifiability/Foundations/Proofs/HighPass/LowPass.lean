import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements

/-! # The low-pass side of (c2)

Proof of `fhpbc_c2_lowPass`, of type `FhpbcLowPassStatement`.

Route (a direct absolute-Fubini estimate, no separate tail theorem). Write
`Ψ = fourierToParabolic m` and `e = timeVector m`.
* The time shift moves `Ψ x` by `√|s|` (`dist_point`), so `|G(x - s e)| ≤ |G x| + L √|s|
  ≤ (|G x| + L)(1 + |s|)`; with `(1 + |s|) |η s|` integrable (Schwartz decay) this gives the
  absolute convergence of `η *_t G` at every point.
* The time shift is a parabolic isometry, so `|η *_t G(x) - η *_t G(y)| ≤ L ‖η‖₁ d_P(Ψx, Ψy)`:
  `(η *_t G) ∘ Ψ⁻¹` is Lipschitz, hence `η *_t G` is continuous.
* For a compact smooth `φ`, the function `(s, y) ↦ G(y - s e) η(s) φ(y)` on `ℝ × ℝ^{m+1}` is
  dominated by `(1 + |s|) |η s| · (|G y| + L) |φ y|`, a product of integrable functions. The
  measure-preserving involution `(s, y) ↦ (-s, y - s e)` and the evenness of `η` carry it to
  `(s, x) ↦ G(x) η(s) φ(x - s e)`, which is therefore integrable with the same integral. Fubini
  (`integral_prod_symm`) on both sides gives integrability of `G (η *_t φ)` and
  `∫ G (η *_t φ) = ∫ (η *_t G) φ`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap FourierTransform

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- Scalar multiplication on the Euclidean product is continuous (as in the construction of
`testKernel`). -/
local instance (m : ℕ) : ContinuousSMul ℝ (FourierSpace m) :=
  IsBoundedSMul.continuousSMul

/-- The coordinates of a time shift: `Ψ(x - s e) = (u, t - s)`. -/
theorem fhpbc2l_toParabolic_shift {m : ℕ} (x : FourierSpace m) (s : ℝ) :
    fourierToParabolic m (x - s • timeVector m) =
      point (WithLp.ofLp x).1 ((WithLp.ofLp x).2 - s) := by
  rw [fourierToParabolic_apply, coordinates_sub_timeVector]

/-- The time shift is a parabolic isometry. -/
theorem fhpbc2l_dist_shift {m : ℕ} (x y : FourierSpace m) (s : ℝ) :
    dist (fourierToParabolic m (x - s • timeVector m))
        (fourierToParabolic m (y - s • timeVector m)) =
      dist (fourierToParabolic m x) (fourierToParabolic m y) := by
  rw [fhpbc2l_toParabolic_shift, fhpbc2l_toParabolic_shift, fourierToParabolic_apply x,
    fourierToParabolic_apply y, dist_point, dist_point, sub_sub_sub_cancel_right]

/-- A parabolic Lipschitz function changes by at most `L √|s|` under a time shift by `s`. -/
theorem fhpbc2l_abs_sub_le {m : ℕ} {G : FourierSpace m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) (x : FourierSpace m) (s : ℝ) :
    |G (x - s • timeVector m) - G x| ≤ L * Real.sqrt |s| := by
  have hd := hL.dist_le_mul (fourierToParabolic m (x - s • timeVector m))
    (fourierToParabolic m x)
  have hts : (WithLp.ofLp x).2 - s - (WithLp.ofLp x).2 = -s := by ring
  rw [Function.comp_apply, Function.comp_apply, Homeomorph.symm_apply_apply,
    Homeomorph.symm_apply_apply, Real.dist_eq, fhpbc2l_toParabolic_shift,
    fourierToParabolic_apply x, dist_point, sub_self, norm_zero, hts, abs_neg,
    max_eq_right (Real.sqrt_nonneg _)] at hd
  exact hd

/-- Shifting two points by the same time changes the difference of `G` by at most
`L d_P(Ψx, Ψy)`. -/
theorem fhpbc2l_abs_sub_shift_le {m : ℕ} {G : FourierSpace m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) (x y : FourierSpace m) (s : ℝ) :
    |G (x - s • timeVector m) - G (y - s • timeVector m)| ≤
      L * dist (fourierToParabolic m x) (fourierToParabolic m y) := by
  have hd := hL.dist_le_mul (fourierToParabolic m (x - s • timeVector m))
    (fourierToParabolic m (y - s • timeVector m))
  rw [Function.comp_apply, Function.comp_apply, Homeomorph.symm_apply_apply,
    Homeomorph.symm_apply_apply, Real.dist_eq, fhpbc2l_dist_shift] at hd
  exact hd

/-- Growth along the time direction: `|G(x - s e)| ≤ (|G x| + L)(1 + |s|)`. -/
theorem fhpbc2l_abs_le {m : ℕ} {G : FourierSpace m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) (x : FourierSpace m) (s : ℝ) :
    |G (x - s • timeVector m)| ≤ (|G x| + L) * (1 + |s|) := by
  have h := fhpbc2l_abs_sub_le hL x s
  have hab := abs_sub_abs_le_abs_sub (G (x - s • timeVector m)) (G x)
  have hs0 := abs_nonneg s
  have hq := Real.sq_sqrt hs0
  have hsq : Real.sqrt |s| ≤ 1 + |s| := by
    nlinarith [sq_nonneg (Real.sqrt |s| - 1), Real.sqrt_nonneg |s|]
  have hL0 : (0 : ℝ) ≤ L := L.2
  nlinarith [mul_le_mul_of_nonneg_left hsq hL0, mul_nonneg (abs_nonneg (G x)) hs0]

/-- A parabolic Lipschitz function is continuous on ordinary coordinates. -/
theorem fhpbc2l_continuous {m : ℕ} {G : FourierSpace m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) : Continuous G := by
  have h := hL.continuous.comp (fourierToParabolic m).continuous
  convert h using 1
  funext x
  simp only [Function.comp_apply, Homeomorph.symm_apply_apply]

/-- The Schwartz weight `(1 + |s|) |η s|` is integrable. -/
theorem fhpbc2l_integrable_weight (η : 𝓢(ℝ, ℝ)) :
    Integrable (fun s : ℝ => (1 + |s|) * |η s|) := by
  have h0 : Integrable (fun s : ℝ => ‖η s‖) := η.integrable.norm
  have h1 := η.integrable_pow_mul volume 1
  refine (h0.add h1).congr (Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, pow_one]
  ring

/-- Absolute convergence of the low-pass integral at every point. -/
theorem fhpbc2l_integrable_conv {m : ℕ} {G : FourierSpace m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) (η : 𝓢(ℝ, ℝ))
    (x : FourierSpace m) :
    Integrable (fun s : ℝ => η s * G (x - s • timeVector m)) := by
  have hGc := fhpbc2l_continuous hL
  have hc : Continuous (fun s : ℝ => η s * G (x - s • timeVector m)) :=
    η.continuous.mul (hGc.comp (continuous_const.sub (continuous_id.smul continuous_const)))
  refine Integrable.mono' ((fhpbc2l_integrable_weight η).const_mul (|G x| + L))
    hc.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |η s| * |G (x - s • timeVector m)| ≤ |η s| * ((|G x| + L) * (1 + |s|)) :=
        mul_le_mul_of_nonneg_left (fhpbc2l_abs_le hL x s) (abs_nonneg _)
    _ = (|G x| + L) * ((1 + |s|) * |η s|) := by ring

/-- The low-pass convolution of a parabolic Lipschitz function is continuous: its transport to
parabolic space is Lipschitz with constant `L ‖η‖₁`. -/
theorem fhpbc2l_continuous_conv {m : ℕ} {G : FourierSpace m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) (η : 𝓢(ℝ, ℝ)) :
    Continuous (fhp_timeConvolution η G) := by
  have hηabs : Integrable (fun s : ℝ => |η s|) := η.integrable.abs
  have hLip : LipschitzWith (Real.toNNReal ((L : ℝ) * ∫ s, |η s|))
      (fun p : Space m => fhp_timeConvolution η G ((fourierToParabolic m).symm p)) := by
    refine LipschitzWith.of_dist_le' fun p q => ?_
    have hb : ∀ s : ℝ,
        ‖η s * G ((fourierToParabolic m).symm p - s • timeVector m) -
            η s * G ((fourierToParabolic m).symm q - s • timeVector m)‖ ≤
          |η s| * (L * dist p q) := by
      intro s
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have h := fhpbc2l_abs_sub_shift_le hL ((fourierToParabolic m).symm p)
        ((fourierToParabolic m).symm q) s
      rwa [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at h
    rw [Real.dist_eq, ← Real.norm_eq_abs]
    unfold fhp_timeConvolution
    rw [← integral_sub (fhpbc2l_integrable_conv hL η _) (fhpbc2l_integrable_conv hL η _)]
    refine (norm_integral_le_of_norm_le (hηabs.mul_const _) (Eventually.of_forall hb)).trans
      (le_of_eq ?_)
    rw [integral_mul_const]
    ring
  have he : fhp_timeConvolution η G =
      (fun p : Space m => fhp_timeConvolution η G ((fourierToParabolic m).symm p)) ∘
        fourierToParabolic m := by
    funext x
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
  rw [he]
  exact hLip.continuous.comp (fourierToParabolic m).continuous

/-- The measure-preserving involution `(s, y) ↦ (-s, y - s e)` of `ℝ × ℝ^{m+1}`. -/
theorem fhpbc2l_measurePreserving_reflect (m : ℕ) :
    MeasurePreserving (fun p : ℝ × FourierSpace m => (-p.1, p.2 - p.1 • timeVector m))
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m)))
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).skew_product
    (g := fun s y => y - s • timeVector m)
    (continuous_snd.sub (continuous_fst.smul continuous_const)).measurable
    (Eventually.of_forall fun s => (measurePreserving_sub_right volume (s • timeVector m)).map_eq)

/-- The shifted product integrand `(s, y) ↦ G(y - s e) η(s) φ(y)` is integrable. -/
theorem fhpbc2l_integrable_shifted {m : ℕ} {G : FourierSpace m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) (η : 𝓢(ℝ, ℝ))
    {φ : FourierSpace m → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun p : ℝ × FourierSpace m => G (p.2 - p.1 • timeVector m) * (η p.1 * φ p.2))
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) := by
  have hGc := fhpbc2l_continuous hL
  have h2 : Integrable (fun y : FourierSpace m => (|G y| + L) * ‖φ y‖) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hφc.norm.mul_left
    exact (hGc.abs.add continuous_const).mul hφ.norm
  have hc : Continuous
      (fun p : ℝ × FourierSpace m => G (p.2 - p.1 • timeVector m) * (η p.1 * φ p.2)) :=
    (hGc.comp (continuous_snd.sub (continuous_fst.smul continuous_const))).mul
      ((η.continuous.comp continuous_fst).mul (hφ.comp continuous_snd))
  refine Integrable.mono' ((fhpbc2l_integrable_weight η).mul_prod h2) hc.aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  calc |G (p.2 - p.1 • timeVector m)| * (|η p.1| * |φ p.2|) ≤
        ((|G p.2| + L) * (1 + |p.1|)) * (|η p.1| * |φ p.2|) :=
        mul_le_mul_of_nonneg_right (fhpbc2l_abs_le hL _ _) (by positivity)
    _ = (1 + |p.1|) * |η p.1| * ((|G p.2| + L) * |φ p.2|) := by ring

/-- The direct product integrand `(s, x) ↦ G(x) η(s) φ(x - s e)` is integrable, with the same
integral as the shifted one (substitution `(s, y) ↦ (-s, y - s e)`, evenness of `η`). -/
theorem fhpbc2l_direct {m : ℕ} {G : FourierSpace m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) (η : 𝓢(ℝ, ℝ))
    (hηe : ∀ t : ℝ, η (-t) = η t)
    {φ : FourierSpace m → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun p : ℝ × FourierSpace m => G p.2 * (η p.1 * φ (p.2 - p.1 • timeVector m)))
        ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) ∧
      ∫ p : ℝ × FourierSpace m, G p.2 * (η p.1 * φ (p.2 - p.1 • timeVector m))
          ∂((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) =
        ∫ p : ℝ × FourierSpace m, G (p.2 - p.1 • timeVector m) * (η p.1 * φ p.2)
          ∂((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) := by
  have hT := fhpbc2l_measurePreserving_reflect m
  have hFg := fhpbc2l_integrable_shifted hL η hφ hφc
  have hcomp : ∀ p : ℝ × FourierSpace m,
      G p.2 * (η p.1 * φ (p.2 - p.1 • timeVector m)) =
        (fun p : ℝ × FourierSpace m => G (p.2 - p.1 • timeVector m) * (η p.1 * φ p.2))
          ((fun p : ℝ × FourierSpace m => (-p.1, p.2 - p.1 • timeVector m)) p) := by
    intro p
    simp only [neg_smul, sub_neg_eq_add, sub_add_cancel, hηe]
  constructor
  · exact ((hT.integrable_comp hFg.aestronglyMeasurable).2 hFg).congr
      (Eventually.of_forall fun p => (hcomp p).symm)
  · rw [integral_congr_ae (Eventually.of_forall hcomp)]
    have hm : AEStronglyMeasurable
        (fun p : ℝ × FourierSpace m => G (p.2 - p.1 • timeVector m) * (η p.1 * φ p.2))
        (Measure.map (fun p : ℝ × FourierSpace m => (-p.1, p.2 - p.1 • timeVector m))
          ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m)))) := by
      rw [hT.map_eq]
      exact hFg.aestronglyMeasurable
    have h := integral_map hT.measurable.aemeasurable hm
    rw [hT.map_eq] at h
    exact h.symm

/-- **The low-pass side**: `FhpbcLowPassStatement`. -/
theorem fhpbc_c2_lowPass_proof : FhpbcLowPassStatement := by
  intro m G hG η hηe
  obtain ⟨L, hL⟩ := hG
  refine ⟨fun x => fhpbc2l_integrable_conv hL η x, fhpbc2l_continuous_conv hL η, ?_⟩
  intro φ hφ hφc
  obtain ⟨hFf, heq⟩ := fhpbc2l_direct hL η hηe hφ.continuous hφc
  have hFg := fhpbc2l_integrable_shifted hL η hφ.continuous hφc
  constructor
  · refine hFf.integral_prod_right.congr (Eventually.of_forall fun x => ?_)
    simp only [fhp_timeConvolution]
    exact integral_const_mul (G x) _
  · calc ∫ x, G x * fhp_timeConvolution η φ x
          = ∫ x, ∫ s, G x * (η s * φ (x - s • timeVector m)) := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_)
            simp only [fhp_timeConvolution]
            exact (integral_const_mul (G x) _).symm
      _ = ∫ p : ℝ × FourierSpace m, G p.2 * (η p.1 * φ (p.2 - p.1 • timeVector m))
            ∂((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) :=
            (integral_prod_symm _ hFf).symm
      _ = ∫ p : ℝ × FourierSpace m, G (p.2 - p.1 • timeVector m) * (η p.1 * φ p.2)
            ∂((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) := heq
      _ = ∫ y, ∫ s, G (y - s • timeVector m) * (η s * φ y) := integral_prod_symm _ hFg
      _ = ∫ y, fhp_timeConvolution η G y * φ y := by
            refine integral_congr_ae (Eventually.of_forall fun y => ?_)
            simp only [fhp_timeConvolution]
            rw [← integral_mul_const]
            refine integral_congr_ae (Eventually.of_forall fun s => ?_)
            simp only
            ring

end ParabolicRectifiability.Foundations
