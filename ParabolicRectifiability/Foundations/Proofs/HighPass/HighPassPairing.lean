import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements

/-! # The high-pass side of (c2)

Proof of `fhpbc_c2_highPassPairing`, with exactly its type
`HighPassBMOLogStatement → FhpbcKernelFactsStatement → FhpbcHighPassPairingStatement`.

Route. On `ℝ × (ℝ^m × ℝ)` put `F(s, x) = g(x) K(s) φ(x - s e_t)` and
`H(r, y) = φ(y) K(r) g(y - r e_t)`. The involution `T(s, x) = (-s, x - s e_t)` is measure
preserving (reflection in `s`, skewed by the time translation) and, `K` being even, `F = H ∘ T`.
`H` is absolutely integrable: by Tonelli, `∫⁻ |H| = ∫⁻_y |φ(y)| ∫⁻_r |K(r)| |g(y - r e_t)|`, which is
at most `‖φ‖_∞ ∫⁻_{tsupport φ} ∫⁻ |K| |g(· - r e_t)| < ∞` by the local bound of (c1). Hence `F` is
integrable, and Fubini on `F` and on `H` gives the integrability of `g (K *_t φ)` and
`∫ g (K *_t φ) = ∫ F = ∫ H = ∫ (K *_t g) φ`.

Only the second clause of (c1) (its first conjunct, the local double-integral bound) and the
evenness and integrability clauses of the kernel facts are used.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- Proof-local shortcut (as in the construction of `testKernel`): the default instance search for
`ContinuousSMul ℝ (FourierSpace m)` times out. -/
local instance fhpbc2h_continuousSMul (m : ℕ) : ContinuousSMul ℝ (FourierSpace m) :=
  IsBoundedSMul.continuousSMul

/-! ## The shear-and-reflection substitution -/

/-- Undoing the time shift: `(x - s e_t) - (-s) e_t = x`. -/
theorem fhpbc2h_sub_neg_smul {m : ℕ} (x : FourierSpace m) (s : ℝ) :
    x - s • timeVector m - (-s) • timeVector m = x := by
  rw [neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- The involution `(s, x) ↦ (-s, x - s e_t)` of `ℝ × (ℝ^m × ℝ)`: the shear by the time
translation followed by `s ↦ -s`. -/
def fhpbc2h_shearNeg (m : ℕ) : (ℝ × FourierSpace m) ≃ᵐ (ℝ × FourierSpace m) where
  toFun p := (-p.1, p.2 - p.1 • timeVector m)
  invFun p := (-p.1, p.2 - p.1 • timeVector m)
  left_inv p := by
    rcases p with ⟨s, x⟩
    simp only [neg_neg, fhpbc2h_sub_neg_smul]
  right_inv p := by
    rcases p with ⟨s, x⟩
    simp only [neg_neg, fhpbc2h_sub_neg_smul]
  measurable_toFun := measurable_fst.neg.prodMk
    (continuous_snd.sub (continuous_fst.smul continuous_const)).measurable
  measurable_invFun := measurable_fst.neg.prodMk
    (continuous_snd.sub (continuous_fst.smul continuous_const)).measurable

theorem fhpbc2h_shearNeg_apply {m : ℕ} (p : ℝ × FourierSpace m) :
    fhpbc2h_shearNeg m p = (-p.1, p.2 - p.1 • timeVector m) := rfl

/-- The substitution `(s, x) ↦ (-s, x - s e_t)` preserves Lebesgue measure on `ℝ × (ℝ^m × ℝ)`. -/
theorem fhpbc2h_measurePreserving_shearNeg (m : ℕ) :
    MeasurePreserving (fhpbc2h_shearNeg m)
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m)))
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).skew_product
    (continuous_snd.sub (continuous_fst.smul continuous_const)).measurable
    (Eventually.of_forall fun h => (measurePreserving_sub_right volume (h • timeVector m)).map_eq)

/-! ## Measurability of a function of finite parabolic BMO seminorm -/

/-- A function of finite parabolic BMO seminorm (read through `fourierToParabolic m`) is
a.e. strongly measurable for the volume of `ℝ^m × ℝ`. -/
theorem fhpbc2h_aestronglyMeasurable_of_bmo {m : ℕ} {g : FourierSpace m → ℝ}
    (hB : ∃ B : ℝ, HasStandardParabolicBMOBound m (g ∘ (fourierToParabolic m).symm) B) :
    AEStronglyMeasurable g (volume : Measure (FourierSpace m)) := by
  obtain ⟨B, -, hloc, -⟩ := hB
  have h1 := hloc.aestronglyMeasurable.comp_measurePreserving
    (fourierToParabolic_measurePreserving m)
  have h2 : (g ∘ (fourierToParabolic m).symm) ∘ (fourierToParabolicMeasurableEquiv m) = g := by
    funext x
    exact congrArg g ((fourierToParabolic m).symm_apply_apply x)
  rwa [h2] at h1

/-! ## The absolute pairing -/

/-- Tonelli bound: the reflected absolute integrand `|φ(y)| |K(r)| |g(y - r e_t)|` has finite
integral over `ℝ × (ℝ^m × ℝ)`, from the local double-integral bound on `tsupport φ` and a bound
`|φ| ≤ M`. -/
theorem fhpbc2h_lintegral_lt_top {m : ℕ} {K : ℝ → ℝ} {g φ : FourierSpace m → ℝ} {M : ℝ}
    (hM : ∀ y, ‖φ y‖ ≤ M)
    (hHm : AEStronglyMeasurable
      (fun p : ℝ × FourierSpace m => φ p.2 * (K p.1 * g (p.2 - p.1 • timeVector m)))
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))))
    (hloc : ∫⁻ x in tsupport φ, ∫⁻ s : ℝ, ‖K s‖ₑ * ‖g (x - s • timeVector m)‖ₑ < ⊤) :
    ∫⁻ p, ‖φ p.2 * (K p.1 * g (p.2 - p.1 • timeVector m))‖ₑ
        ∂((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) < ⊤ := by
  rw [lintegral_prod_symm _ hHm.enorm]
  set J : FourierSpace m → ℝ≥0∞ := fun y => ∫⁻ s : ℝ, ‖K s‖ₑ * ‖g (y - s • timeVector m)‖ₑ
    with hJ
  have hpt : ∀ y : FourierSpace m,
      ∫⁻ r : ℝ, ‖φ (r, y).2 * (K (r, y).1 * g ((r, y).2 - (r, y).1 • timeVector m))‖ₑ ≤
        (tsupport φ).indicator (fun y => ENNReal.ofReal M * J y) y := by
    intro y
    have he : ∫⁻ r : ℝ, ‖φ (r, y).2 * (K (r, y).1 * g ((r, y).2 - (r, y).1 • timeVector m))‖ₑ =
        ‖φ y‖ₑ * J y := by
      simp only [enorm_mul, hJ]
      exact lintegral_const_mul' _ _ enorm_ne_top
    rw [he]
    by_cases hy : y ∈ tsupport φ
    · rw [Set.indicator_of_mem hy]
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hM y)
    · simp [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport hy]
  calc
    ∫⁻ y, ∫⁻ r : ℝ, ‖φ (r, y).2 * (K (r, y).1 * g ((r, y).2 - (r, y).1 • timeVector m))‖ₑ
        ≤ ∫⁻ y, (tsupport φ).indicator (fun y => ENNReal.ofReal M * J y) y :=
      lintegral_mono hpt
    _ = ∫⁻ y in tsupport φ, ENNReal.ofReal M * J y :=
      lintegral_indicator (isClosed_tsupport φ).measurableSet _
    _ = ENNReal.ofReal M * ∫⁻ y in tsupport φ, J y :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hloc

/-- **The pairing for a general even kernel.** For an even, a.e. strongly measurable kernel `K`,
an a.e. strongly measurable `g`, and a continuous compactly supported `φ` such that the absolute
convolution integral of `g` is integrable over `tsupport φ`, the function `g (K *_t φ)` is
integrable and `∫ g (K *_t φ) = ∫ (K *_t g) φ`. -/
theorem fhpbc2h_pairing_of_local {m : ℕ} {K : ℝ → ℝ} (hKeven : ∀ t, K (-t) = K t)
    (hKm : AEStronglyMeasurable K (volume : Measure ℝ)) {g : FourierSpace m → ℝ}
    (hgm : AEStronglyMeasurable g (volume : Measure (FourierSpace m)))
    {φ : FourierSpace m → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hloc : ∫⁻ x in tsupport φ, ∫⁻ s : ℝ, ‖K s‖ₑ * ‖g (x - s • timeVector m)‖ₑ < ⊤) :
    Integrable (fun x => g x * fhp_timeConvolution K φ x) ∧
      ∫ x, g x * fhp_timeConvolution K φ x = ∫ x, fhp_timeConvolution K g x * φ x := by
  set F : ℝ × FourierSpace m → ℝ := fun p => g p.2 * (K p.1 * φ (p.2 - p.1 • timeVector m))
    with hF
  set H : ℝ × FourierSpace m → ℝ := fun p => φ p.2 * (K p.1 * g (p.2 - p.1 • timeVector m))
    with hH
  have hT : MeasurePreserving (fhpbc2h_shearNeg m)
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m)))
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) :=
    fhpbc2h_measurePreserving_shearNeg m
  -- `F = H ∘ T`, by evenness of `K`.
  have hFH : F = H ∘ fhpbc2h_shearNeg m := by
    funext p
    simp only [hF, hH, Function.comp_apply, fhpbc2h_shearNeg_apply, hKeven,
      fhpbc2h_sub_neg_smul]
    ring
  -- Measurability of `H`.
  have hg2 : AEStronglyMeasurable (fun p : ℝ × FourierSpace m => g (p.2 - p.1 • timeVector m))
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) :=
    (hgm.comp_snd (μ := (volume : Measure ℝ))).comp_measurePreserving hT
  have hK1 : AEStronglyMeasurable (fun p : ℝ × FourierSpace m => K p.1)
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) :=
    hKm.comp_fst
  have hφ2 : AEStronglyMeasurable (fun p : ℝ × FourierSpace m => φ p.2)
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) :=
    (hφ.comp continuous_snd).aestronglyMeasurable
  have hHm : AEStronglyMeasurable H
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) :=
    hφ2.mul (hK1.mul hg2)
  -- Absolute integrability of `H` (Tonelli and the local bound of (c1)).
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφc
  have hHint : Integrable H
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) :=
    ⟨hHm, fhpbc2h_lintegral_lt_top hM hHm hloc⟩
  have hFint : Integrable F
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) := by
    rw [hFH]
    exact (hT.integrable_comp hHm).2 hHint
  -- The fibre integrals.
  have hFfib : (fun x => ∫ s : ℝ, F (s, x)) = fun x => g x * fhp_timeConvolution K φ x := by
    funext x
    simp only [hF, fhp_timeConvolution]
    exact integral_const_mul (g x) _
  have hHfib : (fun y => ∫ r : ℝ, H (r, y)) = fun y => fhp_timeConvolution K g y * φ y := by
    funext y
    simp only [hH, fhp_timeConvolution]
    rw [integral_const_mul, mul_comm]
  refine ⟨?_, ?_⟩
  · rw [← hFfib]
    exact hFint.integral_prod_right
  · calc
      ∫ x, g x * fhp_timeConvolution K φ x = ∫ x, ∫ s : ℝ, F (s, x) := by rw [hFfib]
      _ = ∫ p, F p ∂((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) :=
        (integral_prod_symm F hFint).symm
      _ = ∫ p, H (fhpbc2h_shearNeg m p)
          ∂((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) := by
        simp only [hFH, Function.comp_apply]
      _ = ∫ q, H q ∂((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) :=
        hT.integral_comp' H
      _ = ∫ y, ∫ r : ℝ, H (r, y) := integral_prod_symm H hHint
      _ = ∫ x, fhp_timeConvolution K g x * φ x := by rw [hHfib]

/-! ## The statement -/

/-- **The high-pass side** (`fhpbc_c2_highPassPairing`). For `g` of finite parabolic
BMO seminorm, an admissible cutoff `η` with kernel `K = I - η * I`, and a real compact smooth `φ`,
`g (K *_t φ)` is integrable and `∫ g (K *_t φ) = ∫ (K *_t g) φ`. Hypotheses: the public (c1)
(only the local double-integral bound of its second clause is used) and the kernel facts
(evenness and integrability of `K`). -/
theorem fhpbc_c2_highPassPairing_proof : HighPassBMOLogStatement → FhpbcKernelFactsStatement →
    FhpbcHighPassPairingStatement := by
  intro hc1 hKF m g hB η hη φ hφ hφc
  have hKeven : ∀ t, fhp_highPassKernel η (-t) = fhp_highPassKernel η t := (hKF η hη).1
  have hKint : Integrable (fhp_highPassKernel η) := (hKF η hη).2.1
  have hloc := ((hc1 m g hB).2 η hη).1 (tsupport φ) hφc.isCompact
  exact fhpbc2h_pairing_of_local hKeven hKint.aestronglyMeasurable
    (fhpbc2h_aestronglyMeasurable_of_bmo hB) hφ.continuous hφc hloc

end ParabolicRectifiability.Foundations
