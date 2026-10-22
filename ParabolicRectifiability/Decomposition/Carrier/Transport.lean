import ParabolicRectifiability.Decomposition.Carrier.Definitions
import ParabolicRectifiability.Measure.BetaLaws
import ParabolicRectifiability.Analysis.HalfTimeDerivative.TestKernel

/-! # Similarity transport for the regular vertical carrier

Invariance of the objects of the carrier construction under parabolic similarities,
and the normalization of a bounded partial graph. Each theorem `<name>_proof` proves
the intermediate statement `<name>`.

* Hausdorff scaling (`hausdorffP_restrict_image_similarity_proof`). `Θ = similarity q a` is `a⁻¹`-Lipschitz and `Θ⁻¹` is
  `a`-Lipschitz, so `H^k(Θ A) = a^{-k} H^k(A)` for every set `A`; the two restricted
  measures then agree on Borel sets.
* Volume scaling. The base similarity `θ = baseSimilarity W p₀ a` and its version in
  ordinary Fourier coordinates are conjugate to `Θ` by measure preserving coordinate
  maps, so both push the reference volume to `a^{m+2}` times itself, `m = rank W`.
* Half-time derivative (`representsHalfTimeDerivative_baseSimilarity_proof`). On Schwartz tests `D_t^{1/2}` agrees almost everywhere
  with the absolutely convergent kernel `κ ∫ |h|^{-3/2} (ψ(x) - ψ(x - h e_t)) dh`
  (`testKernel_ae_halfTimeDeriv`). The substitution `h ↦ a² h` gives
  `K(ψ ∘ θ) = a⁻¹ (Kψ) ∘ θ`; the factor `a⁻¹` cancels the output factor `a`, and the
  Jacobian `a^{m+2}` appears on both sides of the test identity.
* BMO (`hasParabolicBMOBound_baseSimilarity_proof`). `θ⁻¹ P(θ p, r/a) = P(p, r)`, and ball integrals and ball volumes scale
  by the same constant, so averages and normalized oscillations are unchanged.
* Normalization (`normalize_partial_graph_proof`). Translate by the base projection
  of `z₀`, dilate by `2ρ`, and use the Hausdorff scaling with `betaSq_rescaledSource` and the invariance of `dr/r`.

The lemmas marked "local copy" repeat, under private names, similarity lemmas proved
in the trace-extension part of the library, so that this module does not depend on it.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal SchwartzMap

/-! ## Exact Hausdorff scaling under a parabolic similarity -/

private theorem coe_toNNReal_inv_of_pos {a : ℝ} (ha : 0 < a) :
    (((Real.toNNReal a)⁻¹ : ℝ≥0) : ℝ≥0∞) = (ENNReal.ofReal a)⁻¹ := by
  rw [ENNReal.coe_inv (Real.toNNReal_pos.mpr ha).ne']
  rfl

/-- `Θ = similarity q a` is `a⁻¹`-Lipschitz. -/
theorem lipschitzWith_similarity {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a) :
    LipschitzWith (Real.toNNReal a)⁻¹ (similarity q a ha) := by
  intro z w
  exact (edist_similarity q a ha z w).le.trans
    (le_of_eq (by rw [coe_toNNReal_inv_of_pos ha]))

theorem edist_similarity_symm {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a) (z w : Space n) :
    edist ((similarity q a ha).symm z) ((similarity q a ha).symm w) =
      ENNReal.ofReal a * edist z w := by
  have h := edist_similarity q a ha ((similarity q a ha).symm z) ((similarity q a ha).symm w)
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at h
  rw [h, ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr ha).ne'
    ENNReal.ofReal_ne_top, one_mul]

/-- `Θ⁻¹` is `a`-Lipschitz. -/
theorem lipschitzWith_similarity_symm {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a) :
    LipschitzWith (Real.toNNReal a) (similarity q a ha).symm := by
  intro z w
  exact (edist_similarity_symm q a ha z w).le

theorem hausdorffP_image_similarity_le {n : ℕ} (k : ℕ) (q : Space n) (a : ℝ) (ha : 0 < a)
    (A : Set (Space n)) :
    hausdorffP n k (similarity q a ha '' A) ≤ (ENNReal.ofReal a)⁻¹ ^ k * hausdorffP n k A := by
  have h := (lipschitzWith_similarity q a ha).hausdorffMeasure_image_le
    (Nat.cast_nonneg (α := ℝ) k) A
  rw [coe_toNNReal_inv_of_pos ha, ENNReal.rpow_natCast] at h
  rw [hausdorffP_eq]
  exact h

theorem hausdorffP_image_similarity_symm_le {n : ℕ} (k : ℕ) (q : Space n) (a : ℝ)
    (ha : 0 < a) (A : Set (Space n)) :
    hausdorffP n k ((similarity q a ha).symm '' A) ≤
      ENNReal.ofReal a ^ k * hausdorffP n k A := by
  have h := (lipschitzWith_similarity_symm q a ha).hausdorffMeasure_image_le
    (Nat.cast_nonneg (α := ℝ) k) A
  rw [ENNReal.rpow_natCast] at h
  rw [hausdorffP_eq]
  exact h

/-- Exact scaling `H^k(Θ A) = a^{-k} H^k(A)` for every set `A`. -/
theorem hausdorffP_image_similarity {n : ℕ} (k : ℕ) (q : Space n) (a : ℝ) (ha : 0 < a)
    (A : Set (Space n)) :
    hausdorffP n k (similarity q a ha '' A) = (ENNReal.ofReal a)⁻¹ ^ k * hausdorffP n k A := by
  refine le_antisymm (hausdorffP_image_similarity_le k q a ha A) ?_
  have h := hausdorffP_image_similarity_symm_le k q a ha (similarity q a ha '' A)
  rw [Homeomorph.image_symm, Homeomorph.preimage_image] at h
  calc (ENNReal.ofReal a)⁻¹ ^ k * hausdorffP n k A
      ≤ (ENNReal.ofReal a)⁻¹ ^ k *
          (ENNReal.ofReal a ^ k * hausdorffP n k (similarity q a ha '' A)) := by
        gcongr
    _ = hausdorffP n k (similarity q a ha '' A) := by
        rw [← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr ha).ne'
          ENNReal.ofReal_ne_top, one_pow, one_mul]

/-- `H^k_P ⌞ Θ(S)` is the rescaled source of `H^k_P ⌞ S`. -/
theorem hausdorffP_restrict_image_similarity_proof {n : ℕ} (k : ℕ) (S : Set (Space n))
    (q : Space n) (a : ℝ) (ha : 0 < a) :
    (hausdorffP n k).restrict (similarity q a ha '' S) =
      rescaledSource ((hausdorffP n k).restrict S) k q a ha := by
  ext E hE
  rw [rescaledSource, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (similarity q a ha).measurable hE, Measure.restrict_apply hE,
    Measure.restrict_apply ((similarity q a ha).measurable hE),
    ← hausdorffP_image_similarity k q a ha, image_preimage_inter]

/-! ## Volume transport -/

/-- Translations preserve the parabolic volume (local copy). -/
private theorem map_translation_parabolicVolume_aux {n : ℕ} (q : Space n) :
    Measure.map (translationHomeomorph q) (parabolicVolume n) = parabolicVolume n := by
  have hfun : (translationHomeomorph q : Space n → Space n) ∘ (coordinatesHomeomorph n).symm =
      (coordinatesHomeomorph n).symm ∘ (fun y : Coordinates n => y + (-q.1, -q.2.val)) := by
    funext y
    show point (y.1 - q.1) (y.2 - q.2.val) = point (y.1 + -q.1) (y.2 + -q.2.val)
    rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [parabolicVolume, Measure.map_map (translationHomeomorph q).measurable
      (coordinatesHomeomorph n).symm.measurable, hfun,
    ← Measure.map_map (coordinatesHomeomorph n).symm.measurable (measurable_add_const _),
    coordinateVolume, map_add_right_eq_self]

/-- `Θ_* dp = a^(n+2) dp` for `Θ = similarity q a` (local copy). -/
private theorem map_similarity_parabolicVolume_aux {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a) :
    Measure.map (similarity q a ha) (parabolicVolume n) =
      ENNReal.ofReal a ^ (n + 2) • parabolicVolume n := by
  have hfun : (similarity q a ha : Space n → Space n) = dilate a⁻¹ ∘ translationHomeomorph q :=
    rfl
  rw [hfun, ← Measure.map_map (measurable_dilate a⁻¹) (translationHomeomorph q).measurable,
    map_translation_parabolicVolume_aux, map_dilate_parabolicVolume a⁻¹ (inv_pos.2 ha),
    ENNReal.ofReal_inv_of_pos ha, inv_inv]

/-- A map conjugate to a volume-scaling map by a measure preserving equivalence scales
the volume by the same constant. -/
private theorem map_conj_eq_smul {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (F : X ≃ᵐ Y) (hF : MeasurePreserving F μ ν)
    {T : Y → Y} (hT : Measurable T) {c : ℝ≥0∞} (hmap : Measure.map T ν = c • ν)
    (G : X → X) (hG : ∀ x, G x = F.symm (T (F x))) :
    Measure.map G μ = c • μ := by
  have h1 : G = F.symm ∘ (T ∘ F) := funext hG
  rw [h1, ← Measure.map_map F.symm.measurable (hT.comp F.measurable),
    ← Measure.map_map hT F.measurable, hF.map_eq, hmap, Measure.map_smul, hF.symm.map_eq]
  exact F.symm.measurable.aemeasurable

private theorem locallyIntegrable_smul_measure_aux {X E : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [NormedAddCommGroup E] {f : X → E} {μ : Measure X}
    (hf : LocallyIntegrable f μ) {c : ℝ≥0∞} (hc : c ≠ ⊤) : LocallyIntegrable f (c • μ) := by
  intro x
  obtain ⟨U, hU, h⟩ := hf x
  refine ⟨U, hU, ?_⟩
  change Integrable f ((c • μ).restrict U)
  rw [Measure.restrict_smul]
  exact h.smul_measure hc

/-! ## The similarity in ordinary Fourier coordinates and the test kernel -/

/-- The parabolic similarity `Θ = similarity q a` written in ordinary Fourier coordinates:
`x ↦ (a⁻¹ (x_s - q_x), a⁻² (x_t - q_t))`. -/
def fourierSimilarity {m : ℕ} (q : Space m) (a : ℝ) (ha : 0 < a) :
    FourierSpace m ≃ₜ FourierSpace m :=
  ((fourierToParabolic m).trans (similarity q a ha)).trans (fourierToParabolic m).symm

theorem fourierSimilarity_apply {m : ℕ} (q : Space m) (a : ℝ) (ha : 0 < a)
    (x : FourierSpace m) :
    fourierSimilarity q a ha x =
      WithLp.toLp 2 (a⁻¹ • ((WithLp.ofLp x).1 - q.1), a⁻¹ ^ 2 * ((WithLp.ofLp x).2 - q.2.val)) :=
  rfl

theorem fourierSimilarity_symm_apply {m : ℕ} (q : Space m) (a : ℝ) (ha : 0 < a)
    (y : FourierSpace m) :
    (fourierSimilarity q a ha).symm y =
      WithLp.toLp 2 (a • (WithLp.ofLp y).1 + q.1, a ^ 2 * (WithLp.ofLp y).2 + q.2.val) := by
  change (fourierToParabolic m).symm ((similarity q a ha).symm (fourierToParabolic m y)) = _
  rw [similarity_symm_apply]
  rfl

theorem measurePreserving_fourierSimilarity {m : ℕ} (q : Space m) (a : ℝ) (ha : 0 < a) :
    MeasurePreserving (fourierSimilarity q a ha) (volume : Measure (FourierSpace m))
      (ENNReal.ofReal a ^ (m + 2) • volume) :=
  ⟨(fourierSimilarity q a ha).measurable,
    map_conj_eq_smul (fourierToParabolicMeasurableEquiv m) (fourierToParabolic_measurePreserving m)
      (similarity q a ha).measurable (map_similarity_parabolicVolume_aux q a ha) _
      fun _ => rfl⟩

open scoped ContDiff in
theorem contDiff_fourierSimilarity_symm {m : ℕ} (q : Space m) (a : ℝ) (ha : 0 < a) :
    ContDiff ℝ ∞ (fourierSimilarity q a ha).symm := by
  have h : ⇑(fourierSimilarity q a ha).symm = fun y : FourierSpace m =>
      WithLp.toLp 2 (a • (WithLp.ofLp y).1 + q.1, a ^ 2 * (WithLp.ofLp y).2 + q.2.val) :=
    funext (fourierSimilarity_symm_apply q a ha)
  rw [h]
  have h1 : ContDiff ℝ ∞ (fun p : Spatial m × ℝ => (a • p.1 + q.1, a ^ 2 * p.2 + q.2.val)) :=
    ((contDiff_fst.const_smul a).add contDiff_const).prodMk
      ((contDiff_const.mul contDiff_snd).add contDiff_const)
  exact WithLp.contDiff_toLp.comp (h1.comp WithLp.contDiff_ofLp)

/-- The time shift commutes with `Θ` up to the time scaling `a⁻²`. -/
theorem fourierSimilarity_sub_timeVector {m : ℕ} (q : Space m) (a : ℝ) (ha : 0 < a)
    (x : FourierSpace m) (h : ℝ) :
    fourierSimilarity q a ha (x - h • HalfTimeDerivative.timeVector m) =
      fourierSimilarity q a ha x - (a⁻¹ ^ 2 * h) • HalfTimeDerivative.timeVector m := by
  apply WithLp.ofLp_injective
  simp only [HalfTimeDerivative.coordinates_sub_timeVector, fourierSimilarity_apply,
    WithLp.ofLp_toLp, Prod.mk.injEq, true_and]
  ring

/-- Scaling of the physical half-time kernel: if `φ = ψ ∘ Θ`, then
`K φ = a⁻¹ (K ψ) ∘ Θ`, by the substitution `h ↦ a² h` in the time increment. -/
theorem testKernel_comp_fourierSimilarity {m : ℕ} (q : Space m) (a : ℝ) (ha : 0 < a)
    (φ ψ : 𝓢(FourierSpace m, ℂ)) (hφψ : ∀ x, φ x = ψ (fourierSimilarity q a ha x))
    (x : FourierSpace m) :
    HalfTimeDerivative.testKernel φ x =
      (a : ℂ)⁻¹ * HalfTimeDerivative.testKernel ψ (fourierSimilarity q a ha x) := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hK : (a⁻¹ ^ 2) ^ (-3 / 2 : ℝ) = a ^ 3 := by
    have hx : (0 : ℝ) ≤ a⁻¹ := inv_nonneg.mpr ha.le
    rw [← Real.rpow_two, ← Real.rpow_mul hx,
      show (2 : ℝ) * (-3 / 2) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx,
      Real.rpow_natCast, inv_pow, inv_inv]
  have hpt : ∀ h : ℝ, HalfTimeDerivative.testKernelIntegrand φ x h =
      ((a : ℂ) ^ 3)⁻¹ *
        HalfTimeDerivative.testKernelIntegrand ψ (fourierSimilarity q a ha x) (a⁻¹ ^ 2 * h) := by
    intro h
    have habs : |a⁻¹ ^ 2 * h| ^ (-3 / 2 : ℝ) = a ^ 3 * |h| ^ (-3 / 2 : ℝ) := by
      rw [abs_mul, abs_of_pos (pow_pos (inv_pos.mpr ha) 2),
        Real.mul_rpow (pow_nonneg (inv_nonneg.mpr ha.le) 2) (abs_nonneg h), hK]
    simp only [HalfTimeDerivative.testKernelIntegrand, hφψ, fourierSimilarity_sub_timeVector,
      habs, Complex.ofReal_mul, Complex.ofReal_pow]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 ha'), one_mul]
  have hint : (∫ h, HalfTimeDerivative.testKernelIntegrand φ x h) =
      ((a : ℂ) ^ 3)⁻¹ * (((a ^ 2 : ℝ) : ℂ) *
        ∫ s, HalfTimeDerivative.testKernelIntegrand ψ (fourierSimilarity q a ha x) s) := by
    simp_rw [hpt]
    rw [integral_const_mul, Measure.integral_comp_mul_left
      (HalfTimeDerivative.testKernelIntegrand ψ (fourierSimilarity q a ha x)) (a⁻¹ ^ 2),
      inv_pow, inv_inv, abs_of_pos (pow_pos ha 2), Complex.real_smul]
  have hsc : ((a : ℂ) ^ 3)⁻¹ * (a : ℂ) ^ 2 = (a : ℂ)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 3 ha'), show (a : ℂ) ^ 3 = (a : ℂ) ^ 2 * a by ring,
      mul_assoc, mul_inv_cancel₀ ha', mul_one]
  rw [HalfTimeDerivative.testKernel, HalfTimeDerivative.testKernel, hint, Complex.ofReal_pow,
    ← mul_assoc ((a : ℂ) ^ 3)⁻¹, hsc]
  ring

open scoped ContDiff in
/-- Transport of the real compact-test representation of `D_t^{1/2}` under `Θ`:
if `g` represents `D_t^{1/2} H`, then `g ∘ Θ` represents `D_t^{1/2} (a H ∘ Θ)`. -/
theorem repHalf_comp_fourierSimilarity {m : ℕ} (q : Space m) (a : ℝ) (ha : 0 < a)
    {H g : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (hrep : HalfTimeDerivative.RepHalf hH g univ) :
    ∃ hH' : MemLp (fun x => a * H (fourierSimilarity q a ha x)) 2 volume,
      HalfTimeDerivative.RepHalf hH' (fun x => g (fourierSimilarity q a ha x)) univ := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hc : ENNReal.ofReal a ^ (m + 2) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hMP := measurePreserving_fourierSimilarity q a ha
  have hemb : MeasurableEmbedding (fourierSimilarity q a ha) :=
    (fourierSimilarity q a ha).measurableEmbedding
  have hHe : MemLp (fun x => H (fourierSimilarity q a ha x)) 2 volume :=
    (hH.smul_measure hc).comp_measurePreserving hMP
  refine ⟨hHe.const_mul a, isOpen_univ, ?_, ?_⟩
  · have hg : LocallyIntegrable g volume := locallyIntegrableOn_univ.mp hrep.2.1
    have hg' : LocallyIntegrable g (Measure.map (fourierSimilarity q a ha) volume) := by
      rw [hMP.map_eq]
      exact locallyIntegrable_smul_measure_aux hg hc
    exact locallyIntegrableOn_univ.mpr ((locallyIntegrable_map_homeomorph _).mp hg')
  · intro φ hφ hcφ _
    obtain ⟨φ', hφ'def⟩ : ∃ φ' : FourierSpace m → ℝ,
        φ' = fun y => φ ((fourierSimilarity q a ha).symm y) := ⟨_, rfl⟩
    have hφ' : ContDiff ℝ ∞ φ' := by
      rw [hφ'def]
      exact hφ.comp (contDiff_fourierSimilarity_symm q a ha)
    have hφ'c : HasCompactSupport φ' := by
      rw [hφ'def]
      exact hcφ.comp_homeomorph _
    have hφ'e : ∀ x, φ' (fourierSimilarity q a ha x) = φ x := by
      intro x
      simp only [hφ'def, Homeomorph.symm_apply_apply]
    have hrep' := hrep.2.2 φ' hφ' hφ'c (subset_univ _)
    have hker : ∀ x, HalfTimeDerivative.testKernel (HalfTimeDerivative.realCompactTest φ hφ hcφ) x =
        (a : ℂ)⁻¹ * HalfTimeDerivative.testKernel (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c)
          (fourierSimilarity q a ha x) := by
      refine testKernel_comp_fourierSimilarity q a ha _ _ fun x => ?_
      rw [HalfTimeDerivative.realCompactTest_apply, HalfTimeDerivative.realCompactTest_apply,
        hφ'e]
    calc (∫ x, (((a * H (fourierSimilarity q a ha x) : ℝ)) : ℂ) *
          HalfTimeDerivative.halfTimeDeriv m (HalfTimeDerivative.realCompactTest φ hφ hcφ) x)
        = ∫ x, ((H (fourierSimilarity q a ha x) : ℝ) : ℂ) *
            HalfTimeDerivative.testKernel (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c)
              (fourierSimilarity q a ha x) := by
          refine integral_congr_ae ?_
          filter_upwards [HalfTimeDerivative.testKernel_ae_halfTimeDeriv
            (HalfTimeDerivative.realCompactTest φ hφ hcφ)] with x hx
          rw [← hx, hker x, Complex.ofReal_mul, mul_mul_mul_comm, mul_inv_cancel₀ ha', one_mul]
      _ = ∫ y, ((H y : ℝ) : ℂ) *
            HalfTimeDerivative.testKernel (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c) y
              ∂(ENNReal.ofReal a ^ (m + 2) • volume) :=
          hMP.integral_comp hemb (fun y => ((H y : ℝ) : ℂ) *
            HalfTimeDerivative.testKernel (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c) y)
      _ = (ENNReal.ofReal a ^ (m + 2)).toReal • ∫ y, ((H y : ℝ) : ℂ) *
            HalfTimeDerivative.testKernel (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c) y :=
          integral_smul_measure _ _
      _ = (ENNReal.ofReal a ^ (m + 2)).toReal • ∫ y, ((H y : ℝ) : ℂ) *
            HalfTimeDerivative.halfTimeDeriv m (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c) y := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [HalfTimeDerivative.testKernel_ae_halfTimeDeriv
            (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c)] with y hy
          rw [hy]
      _ = (ENNReal.ofReal a ^ (m + 2)).toReal • ∫ y, ((g y : ℝ) : ℂ) * ((φ' y : ℝ) : ℂ) := by
          rw [hrep']
      _ = ∫ y, ((g y : ℝ) : ℂ) * ((φ' y : ℝ) : ℂ) ∂(ENNReal.ofReal a ^ (m + 2) • volume) :=
          (integral_smul_measure _ _).symm
      _ = ∫ x, ((g (fourierSimilarity q a ha x) : ℝ) : ℂ) *
            ((φ' (fourierSimilarity q a ha x) : ℝ) : ℂ) :=
          (hMP.integral_comp hemb (fun y => ((g y : ℝ) : ℂ) * ((φ' y : ℝ) : ℂ))).symm
      _ = ∫ x, ((g (fourierSimilarity q a ha x) : ℝ) : ℂ) * ((φ x : ℝ) : ℂ) := by
          simp only [hφ'e]

/-! ## Similarity transport of the half-time derivative -/

theorem subspaceFourierToParabolic_fourierSimilarity {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) (x : FourierSpace (Module.finrank ℝ W)) :
    subspaceFourierToParabolic W (fourierSimilarity (subspaceParabolicIsometry W p₀) a ha x) =
      baseSimilarity W p₀ a (subspaceFourierToParabolic W x) := by
  refine Prod.ext ?_ rfl
  change (subspaceCoordinates W).symm
      (a⁻¹ • ((WithLp.ofLp x).1 - subspaceCoordinates W p₀.1)) =
    a⁻¹ • ((subspaceCoordinates W).symm (WithLp.ofLp x).1 - p₀.1)
  rw [map_smul, map_sub, LinearIsometryEquiv.symm_apply_apply]

private theorem normalCoordinates_smul_apply {n : ℕ} (W : Submodule ℝ (Spatial n)) (a : ℝ)
    (v : W.orthogonal) (i : Fin (Module.finrank ℝ W.orthogonal)) :
    normalCoordinates W (a • v) i = a * normalCoordinates W v i := by
  rw [map_smul, PiLp.smul_apply, smul_eq_mul]

/-- Similarity transport of the half-time derivative. -/
theorem representsHalfTimeDerivative_baseSimilarity_proof {n : ℕ}
    (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) {H g : SubspaceSpace W → W.orthogonal}
    (h : RepresentsHalfTimeDerivative W H g) :
    RepresentsHalfTimeDerivative W (fun p => a • H (baseSimilarity W p₀ a p))
      (fun p => g (baseSimilarity W p₀ a p)) := by
  intro i
  obtain ⟨hH, hrep⟩ := h i
  have hH' : normalFourierComponent W (fun p => a • H (baseSimilarity W p₀ a p)) i =
      fun x => a * normalFourierComponent W H i
        (fourierSimilarity (subspaceParabolicIsometry W p₀) a ha x) := by
    funext x
    show normalCoordinates W (a • H (baseSimilarity W p₀ a (subspaceFourierToParabolic W x))) i =
      a * normalCoordinates W (H (subspaceFourierToParabolic W
        (fourierSimilarity (subspaceParabolicIsometry W p₀) a ha x))) i
    rw [subspaceFourierToParabolic_fourierSimilarity, normalCoordinates_smul_apply]
  have hg' : normalFourierComponent W (fun p => g (baseSimilarity W p₀ a p)) i =
      fun x => normalFourierComponent W g i
        (fourierSimilarity (subspaceParabolicIsometry W p₀) a ha x) := by
    funext x
    show normalCoordinates W (g (baseSimilarity W p₀ a (subspaceFourierToParabolic W x))) i =
      normalCoordinates W (g (subspaceFourierToParabolic W
        (fourierSimilarity (subspaceParabolicIsometry W p₀) a ha x))) i
    rw [subspaceFourierToParabolic_fourierSimilarity]
  rw [hH', hg']
  exact repHalf_comp_fourierSimilarity _ a ha hH hrep

/-! ## The base similarity as a homeomorphism -/

/-- The base similarity `θ = baseSimilarity W p₀ a` as a homeomorphism: the conjugate of
`similarity` by the orthonormal coordinates of the base. -/
def baseSimilarityHomeomorph {n : ℕ} (W : Submodule ℝ (Spatial n)) (p₀ : SubspaceSpace W)
    (a : ℝ) (ha : 0 < a) : SubspaceSpace W ≃ₜ SubspaceSpace W :=
  ((subspaceParabolicIsometry W).toHomeomorph.trans
    (similarity (subspaceParabolicIsometry W p₀) a ha)).trans
      (subspaceParabolicIsometry W).symm.toHomeomorph

theorem baseSimilarityHomeomorph_apply {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) (p : SubspaceSpace W) :
    baseSimilarityHomeomorph W p₀ a ha p = baseSimilarity W p₀ a p := by
  refine Prod.ext ?_ rfl
  change (subspaceCoordinates W).symm
      (a⁻¹ • (subspaceCoordinates W p.1 - subspaceCoordinates W p₀.1)) = a⁻¹ • (p.1 - p₀.1)
  rw [← map_sub, ← map_smul, LinearIsometryEquiv.symm_apply_apply]

theorem dist_baseSimilarityHomeomorph {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) (p p' : SubspaceSpace W) :
    dist (baseSimilarityHomeomorph W p₀ a ha p) (baseSimilarityHomeomorph W p₀ a ha p') =
      a⁻¹ * dist p p' := by
  change dist ((subspaceParabolicIsometry W).symm
      (similarity (subspaceParabolicIsometry W p₀) a ha (subspaceParabolicIsometry W p)))
    ((subspaceParabolicIsometry W).symm
      (similarity (subspaceParabolicIsometry W p₀) a ha (subspaceParabolicIsometry W p'))) = _
  rw [IsometryEquiv.dist_eq, dist_similarity, IsometryEquiv.dist_eq]

theorem dist_baseSimilarity {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) (p p' : SubspaceSpace W) :
    dist (baseSimilarity W p₀ a p) (baseSimilarity W p₀ a p') = a⁻¹ * dist p p' := by
  rw [← baseSimilarityHomeomorph_apply W p₀ a ha, ← baseSimilarityHomeomorph_apply W p₀ a ha,
    dist_baseSimilarityHomeomorph]

theorem preimage_ball_baseSimilarityHomeomorph {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) (p : SubspaceSpace W) (r : ℝ) :
    baseSimilarityHomeomorph W p₀ a ha ⁻¹'
        Metric.ball (baseSimilarityHomeomorph W p₀ a ha p) (r / a) = Metric.ball p r := by
  ext x
  rw [mem_preimage, Metric.mem_ball, Metric.mem_ball, dist_baseSimilarityHomeomorph,
    inv_mul_lt_iff₀ ha, mul_div_cancel₀ r ha.ne']

/-- `θ_* (intrinsic volume) = a^(m+2) (intrinsic volume)`, `m = rank W`. -/
theorem map_baseSimilarityHomeomorph {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) :
    Measure.map (baseSimilarityHomeomorph W p₀ a ha) (intrinsicParabolicVolume W) =
      ENNReal.ofReal a ^ (Module.finrank ℝ W + 2) • intrinsicParabolicVolume W :=
  map_conj_eq_smul (subspaceParabolicMeasurableEquiv W) (subspaceParabolic_measurePreserving W)
    (similarity (subspaceParabolicIsometry W p₀) a ha).measurable
    (map_similarity_parabolicVolume_aux _ a ha) _ fun _ => rfl

theorem measurePreserving_baseSimilarityHomeomorph {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) :
    MeasurePreserving (baseSimilarityHomeomorph W p₀ a ha) (intrinsicParabolicVolume W)
      (ENNReal.ofReal a ^ (Module.finrank ℝ W + 2) • intrinsicParabolicVolume W) :=
  ⟨(baseSimilarityHomeomorph W p₀ a ha).measurable, map_baseSimilarityHomeomorph W p₀ a ha⟩

theorem intrinsicParabolicVolume_ball_baseSimilarity {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) (p : SubspaceSpace W) (r : ℝ) :
    intrinsicParabolicVolume W (Metric.ball p r) =
      ENNReal.ofReal a ^ (Module.finrank ℝ W + 2) *
        intrinsicParabolicVolume W (Metric.ball (baseSimilarityHomeomorph W p₀ a ha p) (r / a)) := by
  rw [← preimage_ball_baseSimilarityHomeomorph W p₀ a ha p r,
    (measurePreserving_baseSimilarityHomeomorph W p₀ a ha).measure_preimage_emb
      (baseSimilarityHomeomorph W p₀ a ha).measurableEmbedding,
    Measure.smul_apply, smul_eq_mul]

theorem setIntegral_ball_baseSimilarity {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : SubspaceSpace W → E) (p : SubspaceSpace W) (r : ℝ) :
    ∫ x in Metric.ball p r, f (baseSimilarityHomeomorph W p₀ a ha x) ∂intrinsicParabolicVolume W =
      (ENNReal.ofReal a ^ (Module.finrank ℝ W + 2)).toReal •
        ∫ y in Metric.ball (baseSimilarityHomeomorph W p₀ a ha p) (r / a), f y
          ∂intrinsicParabolicVolume W := by
  rw [← preimage_ball_baseSimilarityHomeomorph W p₀ a ha p r,
    (measurePreserving_baseSimilarityHomeomorph W p₀ a ha).setIntegral_preimage_emb
      (baseSimilarityHomeomorph W p₀ a ha).measurableEmbedding,
    Measure.restrict_smul, integral_smul_measure]

/-! ## Similarity invariance of the vector parabolic BMO bound -/

/-- The parabolic BMO bound is invariant under `θ`. -/
theorem hasParabolicBMOBound_baseSimilarity_proof {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) {g : SubspaceSpace W → W.orthogonal}
    {B : ℝ} (h : HasParabolicBMOBound W g B) :
    HasParabolicBMOBound W (fun p => g (baseSimilarity W p₀ a p)) B := by
  obtain ⟨hB, hloc, hosc⟩ := h
  have hfun : (fun p => g (baseSimilarity W p₀ a p)) =
      fun p => g (baseSimilarityHomeomorph W p₀ a ha p) := by
    funext p
    rw [baseSimilarityHomeomorph_apply]
  rw [hfun]
  have hc : ENNReal.ofReal a ^ (Module.finrank ℝ W + 2) ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hc0 : (ENNReal.ofReal a ^ (Module.finrank ℝ W + 2)).toReal ≠ 0 := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal ha.le]
    exact pow_ne_zero _ ha.ne'
  refine ⟨hB, ?_, fun p r hr => ?_⟩
  · refine (locallyIntegrable_map_homeomorph (baseSimilarityHomeomorph W p₀ a ha)).mp ?_
    rw [map_baseSimilarityHomeomorph]
    exact locallyIntegrable_smul_measure_aux hloc hc
  · have havg : parabolicBallAverage W (fun x => g (baseSimilarityHomeomorph W p₀ a ha x)) p r =
        parabolicBallAverage W g (baseSimilarityHomeomorph W p₀ a ha p) (r / a) := by
      rw [parabolicBallAverage, parabolicBallAverage,
        intrinsicParabolicVolume_ball_baseSimilarity W p₀ a ha p r,
        setIntegral_ball_baseSimilarity W p₀ a ha g p r, ENNReal.toReal_mul, smul_smul,
        mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
    have hI : (∫ x in Metric.ball p r, ‖g (baseSimilarityHomeomorph W p₀ a ha x) -
          parabolicBallAverage W g (baseSimilarityHomeomorph W p₀ a ha p) (r / a)‖
          ∂intrinsicParabolicVolume W) =
        (ENNReal.ofReal a ^ (Module.finrank ℝ W + 2)).toReal *
          ∫ y in Metric.ball (baseSimilarityHomeomorph W p₀ a ha p) (r / a),
            ‖g y - parabolicBallAverage W g (baseSimilarityHomeomorph W p₀ a ha p) (r / a)‖
            ∂intrinsicParabolicVolume W :=
      setIntegral_ball_baseSimilarity W p₀ a ha
        (fun y => ‖g y - parabolicBallAverage W g (baseSimilarityHomeomorph W p₀ a ha p) (r / a)‖)
        p r
    have hV : (intrinsicParabolicVolume W (Metric.ball p r)).toReal =
        (ENNReal.ofReal a ^ (Module.finrank ℝ W + 2)).toReal *
          (intrinsicParabolicVolume W
            (Metric.ball (baseSimilarityHomeomorph W p₀ a ha p) (r / a))).toReal := by
      rw [intrinsicParabolicVolume_ball_baseSimilarity W p₀ a ha p r, ENNReal.toReal_mul]
    calc (∫ x in Metric.ball p r, ‖g (baseSimilarityHomeomorph W p₀ a ha x) -
            parabolicBallAverage W (fun x => g (baseSimilarityHomeomorph W p₀ a ha x)) p r‖
            ∂intrinsicParabolicVolume W) / (intrinsicParabolicVolume W (Metric.ball p r)).toReal
        = ((ENNReal.ofReal a ^ (Module.finrank ℝ W + 2)).toReal *
            ∫ y in Metric.ball (baseSimilarityHomeomorph W p₀ a ha p) (r / a),
              ‖g y - parabolicBallAverage W g (baseSimilarityHomeomorph W p₀ a ha p) (r / a)‖
              ∂intrinsicParabolicVolume W) /
          ((ENNReal.ofReal a ^ (Module.finrank ℝ W + 2)).toReal *
            (intrinsicParabolicVolume W
              (Metric.ball (baseSimilarityHomeomorph W p₀ a ha p) (r / a))).toReal) := by
          rw [havg, hI, hV]
      _ = (∫ y in Metric.ball (baseSimilarityHomeomorph W p₀ a ha p) (r / a),
              ‖g y - parabolicBallAverage W g (baseSimilarityHomeomorph W p₀ a ha p) (r / a)‖
              ∂intrinsicParabolicVolume W) /
            (intrinsicParabolicVolume W
              (Metric.ball (baseSimilarityHomeomorph W p₀ a ha p) (r / a))).toReal :=
          mul_div_mul_left _ _ hc0
      _ ≤ B := hosc _ _ (div_pos hr ha)

/-! ## Similarity invariance of regular vertical functions -/

/-- Regular vertical functions are invariant under `p ↦ a G(θ p)`. -/
theorem isRegularVerticalFunction_baseSimilarity_proof {n : ℕ}
    (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) {G : SubspaceSpace W → W.orthogonal}
    {ε : ℝ} (hG : IsRegularVerticalFunction W G ε) :
    IsRegularVerticalFunction W (fun p => a • G (baseSimilarity W p₀ a p)) ε := by
  obtain ⟨c, H, g, L, B, rfl, hH, hL, hB, hrep, hsum⟩ := hG
  refine ⟨a • c, fun p => a • H (baseSimilarity W p₀ a p), fun p => g (baseSimilarity W p₀ a p),
    L, B, ?_, ?_, ?_, hasParabolicBMOBound_baseSimilarity_proof W p₀ a ha hB,
    representsHalfTimeDerivative_baseSimilarity_proof W p₀ a ha hrep, hsum⟩
  · funext p
    simp only [smul_add]
  · have hfun : (fun p => a • H (baseSimilarity W p₀ a p)) =
        (fun v : W.orthogonal => a • v) ∘ (H ∘ baseSimilarityHomeomorph W p₀ a ha) := by
      funext p
      simp only [Function.comp_apply, baseSimilarityHomeomorph_apply]
    rw [hfun]
    exact (hH.comp_homeomorph _).comp_left (smul_zero a)
  · refine LipschitzWith.of_dist_le_mul fun p p' => ?_
    have h1 : dist (c + H (baseSimilarity W p₀ a p)) (c + H (baseSimilarity W p₀ a p')) ≤
        L * dist (baseSimilarity W p₀ a p) (baseSimilarity W p₀ a p') := hL.dist_le_mul _ _
    rw [dist_baseSimilarity W p₀ a ha] at h1
    show dist (a • (c + H (baseSimilarity W p₀ a p))) (a • (c + H (baseSimilarity W p₀ a p'))) ≤
      L * dist p p'
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos ha]
    calc a * dist (c + H (baseSimilarity W p₀ a p)) (c + H (baseSimilarity W p₀ a p'))
        ≤ a * (L * (a⁻¹ * dist p p')) := mul_le_mul_of_nonneg_left h1 ha.le
      _ = L * dist p p' := by
        rw [mul_left_comm, ← mul_assoc a, mul_inv_cancel₀ ha.ne', one_mul]

/-! ## Inverse similarities of regular vertical graph covers -/

/-- The inverse similarity maps the full graph `(o + u + F(u,t), t)` onto the full graph
with offset `a o + q_x` and function `p ↦ a F(θ p)`, `θ = baseSimilarity V (0, q_t) a`. -/
theorem range_similarity_symm_graph {n : ℕ} (V : Submodule ℝ (Spatial n)) (o : Spatial n)
    (F : SubspaceSpace V → V.orthogonal) (q : Space n) (a : ℝ) (ha : 0 < a) :
    Set.range (fun p : SubspaceSpace V =>
      ((a • o + q.1 + (p.1 : Spatial n) +
        ((a • F (baseSimilarity V ((0 : V), q.2) a p) : V.orthogonal) : Spatial n), p.2) :
          Space n)) =
      (similarity q a ha).symm ''
        Set.range (fun p : SubspaceSpace V =>
          ((o + (p.1 : Spatial n) + (F p : Spatial n), p.2) : Space n)) := by
  have hfun : (fun p : SubspaceSpace V =>
      ((a • o + q.1 + (p.1 : Spatial n) +
        ((a • F (baseSimilarity V ((0 : V), q.2) a p) : V.orthogonal) : Spatial n), p.2) :
          Space n)) =
      ((similarity q a ha).symm ∘ (fun p : SubspaceSpace V =>
          ((o + (p.1 : Spatial n) + (F p : Spatial n), p.2) : Space n))) ∘
        baseSimilarityHomeomorph V ((0 : V), q.2) a ha := by
    funext p
    rcases p with ⟨u, ⟨t⟩⟩
    rw [Function.comp_apply, Function.comp_apply, baseSimilarityHomeomorph_apply,
      similarity_symm_apply]
    refine Prod.ext ?_ ?_
    · show a • o + q.1 + (u : Spatial n) +
          ((a • F (baseSimilarity V ((0 : V), q.2) a (u, Metric.Snowflaking.toSnowflaking t)) :
            V.orthogonal) : Spatial n) =
        a • (o + ((a⁻¹ • (u - 0) : V) : Spatial n) +
          (F (baseSimilarity V ((0 : V), q.2) a (u, Metric.Snowflaking.toSnowflaking t)) :
            Spatial n)) + q.1
      simp only [sub_zero, Submodule.coe_smul, smul_add, smul_smul, mul_inv_cancel₀ ha.ne',
        one_smul]
      abel
    · show (Metric.Snowflaking.toSnowflaking t : Time) =
        Metric.Snowflaking.toSnowflaking (a ^ 2 * (a⁻¹ ^ 2 * (t - q.2.val)) + q.2.val)
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ ha.ne', one_pow, one_mul, sub_add_cancel]
  rw [hfun, (baseSimilarityHomeomorph V ((0 : V), q.2) a ha).surjective.range_comp, range_comp]

/-- The image of a full regular vertical graph under the inverse similarity
`Θ⁻¹ = (similarity q a)⁻¹`: same direction, offset `a o + q_x`, function `p ↦ a F(θ p)`
with `θ = baseSimilarity V (0, q_t) a` (regular by `isRegularVerticalFunction_baseSimilarity_proof`). -/
def RegularVerticalGraph.similaritySymm {n k : ℕ} {ε : ℝ} (q : Space n) (a : ℝ) (ha : 0 < a)
    (G : RegularVerticalGraph n k ε) : RegularVerticalGraph n k ε :=
  ⟨G.vertical_dimension, G.direction, G.rank_eq, a • G.offset + q.1,
    fun p => a • G.function (baseSimilarity G.direction ((0 : G.direction), q.2) a p),
    isRegularVerticalFunction_baseSimilarity_proof _ _ a ha G.regular⟩

theorem RegularVerticalGraph.image_similaritySymm {n k : ℕ} {ε : ℝ} (q : Space n) (a : ℝ)
    (ha : 0 < a) (G : RegularVerticalGraph n k ε) :
    (G.similaritySymm q a ha).image = (similarity q a ha).symm '' G.image :=
  range_similarity_symm_graph G.direction G.offset G.function q a ha

/-- Regular vertical graph covers are invariant under `Θ⁻¹`. -/
theorem hasRegularVerticalGraphCover_similarity_symm_proof {n k : ℕ} {S : Set (Space n)}
    {ε : ℝ} (q : Space n) (a : ℝ) (ha : 0 < a) (h : HasRegularVerticalGraphCover k S ε) :
    HasRegularVerticalGraphCover k ((similarity q a ha).symm '' S) ε := by
  obtain ⟨I, G, hnull⟩ := h
  refine ⟨I, fun i => (G i).similaritySymm q a ha, ?_⟩
  have hset : (similarity q a ha).symm '' S \ ⋃ i, ((G i).similaritySymm q a ha).image =
      (similarity q a ha).symm '' (S \ ⋃ i, (G i).image) := by
    rw [image_sdiff (similarity q a ha).symm.injective, image_iUnion]
    simp only [RegularVerticalGraph.image_similaritySymm]
  rw [hset]
  refine le_antisymm ?_ zero_le
  calc hausdorffP n k ((similarity q a ha).symm '' (S \ ⋃ i, (G i).image))
      ≤ ENNReal.ofReal a ^ k * hausdorffP n k (S \ ⋃ i, (G i).image) :=
        hausdorffP_image_similarity_symm_le k q a ha _
    _ = 0 := by rw [hnull, mul_zero]

/-! ## Normalization of a bounded partial graph -/

/-- The scale measure `dr/r` is invariant under `r ↦ c r`, `c > 0` (local copy). -/
private theorem scaleMeasure_map_mul_left_aux {c : ℝ} (hc : 0 < c) :
    Measure.map (fun s => c * s) scaleMeasure = scaleMeasure := by
  ext A hA
  have hA' : MeasurableSet (A ∩ Ioi 0) := hA.inter measurableSet_Ioi
  have hpre : MeasurableSet ((fun s => c * s) ⁻¹' A) := measurable_const_mul c hA
  rw [Measure.map_apply (measurable_const_mul c) hA, scaleMeasure_apply _ hpre,
    scaleMeasure_apply _ hA]
  have hset : (fun s => c * s) ⁻¹' A ∩ Ioi 0 = (fun s => c * s) ⁻¹' (A ∩ Ioi 0) := by
    ext r
    simp only [mem_inter_iff, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, mul_pos hc h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, pos_of_mul_pos_right h2 hc.le⟩
  rw [hset, ← lintegral_indicator (measurable_const_mul c hA'), ← lintegral_indicator hA']
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ≥0∞,
      G = (A ∩ Ioi 0).indicator (fun t => ENNReal.ofReal (1 / t)) := ⟨_, rfl⟩
  rw [← hG]
  have hfun : ∀ r, ((fun s => c * s) ⁻¹' (A ∩ Ioi 0)).indicator
      (fun r => ENNReal.ofReal (1 / r)) r = ENNReal.ofReal c * G (c * r) := by
    intro r
    rw [hG]
    by_cases hr : c * r ∈ A ∩ Ioi 0
    · rw [indicator_of_mem (show r ∈ (fun s => c * s) ⁻¹' (A ∩ Ioi 0) from hr),
        indicator_of_mem hr, ← ENNReal.ofReal_mul hc.le, mul_one_div,
        div_mul_cancel_left₀ hc.ne', one_div]
    · rw [indicator_of_notMem (show r ∉ (fun s => c * s) ⁻¹' (A ∩ Ioi 0) from hr),
        indicator_of_notMem hr, mul_zero]
  have hmap : ∫⁻ r, G (c * r) = ENNReal.ofReal |c⁻¹| * ∫⁻ t, G t := by
    calc
      ∫⁻ r, G (c * r) = ∫⁻ t, G t ∂(Measure.map (fun s => c * s) volume) :=
        (lintegral_map_equiv G (MeasurableEquiv.mulLeft₀ c hc.ne')).symm
      _ = ∫⁻ t, G t ∂(ENNReal.ofReal |c⁻¹| • volume) := by
        rw [Real.map_volume_mul_left hc.ne']
      _ = ENNReal.ofReal |c⁻¹| * ∫⁻ t, G t := by
        rw [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_congr hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmap, ← mul_assoc,
    ← ENNReal.ofReal_mul hc.le, abs_of_pos (inv_pos.mpr hc), mul_inv_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]

/-- Change of scale `t = c s` for `ds/s` (local copy). -/
private theorem setLIntegral_scaleMeasure_comp_mul_left_aux {c : ℝ} (hc : 0 < c)
    (f : ℝ → ℝ≥0∞) (T : Set ℝ) :
    ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure = ∫⁻ t in T, f t ∂scaleMeasure := by
  set e := MeasurableEquiv.mulLeft₀ c hc.ne' with he_def
  have he : ⇑e = fun s => c * s := MeasurableEquiv.coe_mulLeft₀ hc.ne'
  symm
  calc
    ∫⁻ t in T, f t ∂scaleMeasure = ∫⁻ t in T, f t ∂(Measure.map e scaleMeasure) := by
      rw [he, scaleMeasure_map_mul_left_aux hc]
    _ = ∫⁻ t, f t ∂((scaleMeasure.restrict (e ⁻¹' T)).map e) := by
      rw [e.measurableEmbedding.restrict_map]
    _ = ∫⁻ s, f (e s) ∂(scaleMeasure.restrict (e ⁻¹' T)) := lintegral_map_equiv f e
    _ = ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure := by
      rw [he]

private theorem setLIntegral_Ioi_scaleMeasure_comp_mul {c : ℝ} (hc : 0 < c)
    (f : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioi 0, f (c * r) ∂scaleMeasure = ∫⁻ s in Ioi 0, f s ∂scaleMeasure := by
  have hpre : (fun s => c * s) ⁻¹' Ioi (0 : ℝ) = Ioi 0 := by
    ext s
    simp only [mem_preimage, mem_Ioi]
    exact ⟨fun h => pos_of_mul_pos_right h hc.le, fun h => mul_pos hc h⟩
  rw [← setLIntegral_scaleMeasure_comp_mul_left_aux hc f (Ioi 0), hpre]

/-- The base projection `(x, t) ↦ (P_W x, t)` of space-time onto the intrinsic base. -/
private def baseProjection {n : ℕ} (W : Submodule ℝ (Spatial n)) (z : Space n) :
    SubspaceSpace W :=
  (W.orthogonalProjectionOnto z.1, z.2)

private theorem baseProjection_verticalLift {n : ℕ} (W : Submodule ℝ (Spatial n))
    (g : SubspaceSpace W → W.orthogonal) (p : SubspaceSpace W) :
    baseProjection W (verticalLift W g p) = p := by
  refine Prod.ext ?_ rfl
  change W.orthogonalProjectionOnto ((p.1 : Spatial n) + (g p : Spatial n)) = p.1
  rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (g p).2, add_zero]

private theorem dist_baseProjection_le {n : ℕ} (W : Submodule ℝ (Spatial n)) (z w : Space n) :
    dist (baseProjection W z) (baseProjection W w) ≤ dist z w := by
  rw [Prod.dist_eq, Prod.dist_eq]
  refine max_le_max ?_ le_rfl
  change dist (W.orthogonalProjectionOnto z.1) (W.orthogonalProjectionOnto w.1) ≤ dist z.1 w.1
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact Submodule.norm_orthogonalProjectionOnto_apply_le W _

private theorem continuous_baseProjection {n : ℕ} (W : Submodule ℝ (Spatial n)) :
    Continuous (baseProjection W) :=
  (W.orthogonalProjectionOnto.continuous.comp continuous_fst).prodMk continuous_snd

/-- The normal map `p' ↦ a⁻¹ g(θ⁻¹ p')` of the normalized graph. -/
private def normalizedNormal {n : ℕ} (W : Submodule ℝ (Spatial n)) (p₀ : SubspaceSpace W)
    (a : ℝ) (ha : 0 < a) (g : SubspaceSpace W → W.orthogonal) :
    SubspaceSpace W → W.orthogonal :=
  fun p' => a⁻¹ • g ((baseSimilarityHomeomorph W p₀ a ha).symm p')

private theorem normalizedNormal_baseSimilarity {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) (g : SubspaceSpace W → W.orthogonal)
    (p : SubspaceSpace W) :
    normalizedNormal W p₀ a ha g (baseSimilarity W p₀ a p) = a⁻¹ • g p := by
  show a⁻¹ • g ((baseSimilarityHomeomorph W p₀ a ha).symm (baseSimilarity W p₀ a p)) = a⁻¹ • g p
  rw [← baseSimilarityHomeomorph_apply W p₀ a ha p, Homeomorph.symm_apply_apply]

private theorem verticalLift_normalizedNormal {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) (g : SubspaceSpace W → W.orthogonal)
    (p : SubspaceSpace W) :
    verticalLift W (normalizedNormal W p₀ a ha g) (baseSimilarity W p₀ a p) =
      similarity (subspaceInclusion W p₀) a ha (verticalLift W g p) := by
  refine Prod.ext ?_ rfl
  change ((baseSimilarity W p₀ a p).1 : Spatial n) +
      (normalizedNormal W p₀ a ha g (baseSimilarity W p₀ a p) : Spatial n) =
    a⁻¹ • ((p.1 : Spatial n) + (g p : Spatial n) - (p₀.1 : Spatial n))
  rw [normalizedNormal_baseSimilarity]
  simp only [baseSimilarity, Submodule.coe_smul, Submodule.coe_sub, smul_sub, smul_add]
  abel

private theorem normalize_partial_graph_aux {n : ℕ} (k : ℕ) (W : Submodule ℝ (Spatial n))
    (D : Set (SubspaceSpace W)) (g : SubspaceSpace W → W.orthogonal) (ℓ : ℝ≥0) (B₀ : ℝ)
    (p₀ : SubspaceSpace W) (a : ℝ) (ha : 0 < a) (hD : IsCompact D)
    (hDa : ∀ p ∈ D, dist p p₀ ≤ a) (hg : LipschitzOnWith ℓ g D)
    (hB : ∀ p ∈ D, ∫⁻ s in Ioi 0,
      betaSq ((hausdorffP n k).restrict (verticalLift W g '' D)) k .vertical
        (verticalLift W g p) s ∂scaleMeasure ≤ ENNReal.ofReal B₀) :
    ∃ (D' : Set (SubspaceSpace W)) (g' : SubspaceSpace W → W.orthogonal),
      IsCompact D' ∧
      D' ⊆ Metric.closedBall
        (((0 : W), Metric.Snowflaking.toSnowflaking (0 : ℝ)) : SubspaceSpace W) 1 ∧
      LipschitzOnWith ℓ g' D' ∧
      verticalLift W g' '' D' =
        similarity (subspaceInclusion W p₀) a ha '' (verticalLift W g '' D) ∧
      ∀ p ∈ D', ∫⁻ r in Ioo 0 2,
        betaSq ((hausdorffP n k).restrict (verticalLift W g' '' D')) k .vertical
          (verticalLift W g' p) r ∂scaleMeasure ≤ ENNReal.ofReal B₀ := by
  have himg : verticalLift W (normalizedNormal W p₀ a ha g) '' (baseSimilarity W p₀ a '' D) =
      similarity (subspaceInclusion W p₀) a ha '' (verticalLift W g '' D) := by
    rw [image_image, image_image]
    exact image_congr fun p _ => verticalLift_normalizedNormal W p₀ a ha g p
  refine ⟨baseSimilarity W p₀ a '' D, normalizedNormal W p₀ a ha g, ?_, ?_, ?_, himg, ?_⟩
  · have hθ : baseSimilarity W p₀ a = baseSimilarityHomeomorph W p₀ a ha :=
      (funext (baseSimilarityHomeomorph_apply W p₀ a ha)).symm
    rw [hθ]
    exact hD.image (baseSimilarityHomeomorph W p₀ a ha).continuous
  · rintro _ ⟨p, hp, rfl⟩
    have h0 : baseSimilarity W p₀ a p₀ =
        (((0 : W), Metric.Snowflaking.toSnowflaking (0 : ℝ)) : SubspaceSpace W) := by
      simp [baseSimilarity]
    rw [Metric.mem_closedBall, ← h0, dist_baseSimilarity W p₀ a ha, inv_mul_le_iff₀ ha, mul_one]
    exact hDa p hp
  · refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [normalizedNormal_baseSimilarity, normalizedNormal_baseSimilarity, dist_smul₀,
      dist_baseSimilarity W p₀ a ha, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    calc a⁻¹ * dist (g u) (g v) ≤ a⁻¹ * (ℓ * dist u v) :=
          mul_le_mul_of_nonneg_left (hg.dist_le_mul u hu v hv) (inv_pos.mpr ha).le
      _ = ℓ * (a⁻¹ * dist u v) := by ring
  · rintro _ ⟨p, hp, rfl⟩
    rw [himg, hausdorffP_restrict_image_similarity_proof, verticalLift_normalizedNormal]
    calc ∫⁻ r in Ioo 0 2,
          betaSq (rescaledSource ((hausdorffP n k).restrict (verticalLift W g '' D)) k
            (subspaceInclusion W p₀) a ha) k .vertical
            (similarity (subspaceInclusion W p₀) a ha (verticalLift W g p)) r ∂scaleMeasure
        ≤ ∫⁻ r in Ioi 0,
          betaSq (rescaledSource ((hausdorffP n k).restrict (verticalLift W g '' D)) k
            (subspaceInclusion W p₀) a ha) k .vertical
            (similarity (subspaceInclusion W p₀) a ha (verticalLift W g p)) r ∂scaleMeasure :=
          lintegral_mono_set Ioo_subset_Ioi_self
      _ = ∫⁻ r in Ioi 0, betaSq ((hausdorffP n k).restrict (verticalLift W g '' D)) k .vertical
            (verticalLift W g p) (a * r) ∂scaleMeasure :=
          setLIntegral_congr_fun measurableSet_Ioi fun r hr =>
            betaSq_rescaledSource _ k .vertical _ a ha _ hr
      _ = ∫⁻ s in Ioi 0, betaSq ((hausdorffP n k).restrict (verticalLift W g '' D)) k .vertical
            (verticalLift W g p) s ∂scaleMeasure :=
          setLIntegral_Ioi_scaleMeasure_comp_mul ha _
      _ ≤ ENNReal.ofReal B₀ := hB p hp

/-- Normalization of a bounded partial graph into the unit base cylinder:
translate by the base projection of `z₀` and dilate by `2ρ`. -/
theorem normalize_partial_graph_proof {n : ℕ} (k : ℕ) (W : Submodule ℝ (Spatial n))
    (D : Set (SubspaceSpace W)) (g : SubspaceSpace W → W.orthogonal) (ℓ : ℝ≥0) (B₀ : ℝ)
    (z₀ : Space n) (ρ : ℝ) (hρ : 0 < ρ) (hS : IsCompact (verticalLift W g '' D))
    (hSρ : verticalLift W g '' D ⊆ Metric.ball z₀ ρ) (hg : LipschitzOnWith ℓ g D)
    (hB : ∀ p ∈ D, ∫⁻ s in Ioi 0,
      betaSq ((hausdorffP n k).restrict (verticalLift W g '' D)) k .vertical
        (verticalLift W g p) s ∂scaleMeasure ≤ ENNReal.ofReal B₀) :
    ∃ (q : Space n) (a : ℝ) (ha : 0 < a) (D' : Set (SubspaceSpace W))
      (g' : SubspaceSpace W → W.orthogonal),
      IsCompact D' ∧
      D' ⊆ Metric.closedBall
        (((0 : W), Metric.Snowflaking.toSnowflaking (0 : ℝ)) : SubspaceSpace W) 1 ∧
      LipschitzOnWith ℓ g' D' ∧
      verticalLift W g' '' D' = similarity q a ha '' (verticalLift W g '' D) ∧
      ∀ p ∈ D', ∫⁻ r in Ioo 0 2,
        betaSq ((hausdorffP n k).restrict (verticalLift W g' '' D')) k .vertical
          (verticalLift W g' p) r ∂scaleMeasure ≤ ENNReal.ofReal B₀ := by
  have hDeq : D = baseProjection W '' (verticalLift W g '' D) := by
    rw [image_image]
    simp only [baseProjection_verticalLift, image_id']
  have hDc : IsCompact D := by
    rw [hDeq]
    exact hS.image (continuous_baseProjection W)
  have hDa : ∀ p ∈ D, dist p (baseProjection W z₀) ≤ 2 * ρ := by
    intro p hp
    have hmem : verticalLift W g p ∈ Metric.ball z₀ ρ := hSρ (mem_image_of_mem _ hp)
    calc dist p (baseProjection W z₀)
        = dist (baseProjection W (verticalLift W g p)) (baseProjection W z₀) := by
          rw [baseProjection_verticalLift]
      _ ≤ dist (verticalLift W g p) z₀ := dist_baseProjection_le W _ _
      _ ≤ 2 * ρ := by linarith [Metric.mem_ball.mp hmem]
  obtain ⟨D', g', h1, h2, h3, h4, h5⟩ := normalize_partial_graph_aux k W D g ℓ B₀
    (baseProjection W z₀) (2 * ρ) (by positivity) hDc hDa hg hB
  exact ⟨_, 2 * ρ, _, D', g', h1, h2, h3, h4, h5⟩

end ParabolicRectifiability
