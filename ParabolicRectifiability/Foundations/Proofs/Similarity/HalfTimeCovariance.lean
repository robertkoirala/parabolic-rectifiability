import ParabolicRectifiability.Foundations.Statements.HighPassBracket
import ParabolicRectifiability.Decomposition.Carrier.Transport

/-! # Similarity covariance of the homogeneous half-time representative

Proofs, under the names `<name>_proof`, of
`fsim_representsHomogeneousHalfTimeDerivative_dilation` and
`fsim_representsHomogeneousHalfTimeDerivative_timeShift`.

Both statements are instances of one affine map in ordinary coordinates,
`Θ = fourierSimilarity (0, t₀) a`, `Θ(u,t) = (a⁻¹ u, a⁻² (t - t₀))`
(dilation: `a = R`, `t₀ = 0`; time shift: `a = 1`). For a test `φ` put `φ' = φ ∘ Θ⁻¹`, a compact
smooth test of total integral zero. Then:

* the test kernel is covariant pointwise, `K φ = a⁻¹ (K φ') ∘ Θ`
  (`testKernel_comp_fourierSimilarity`); since `halfTimeDeriv` agrees with the kernel only
  almost everywhere, the identity
  `(a G ∘ Θ) · D φ = (G · D φ') ∘ Θ` holds a.e. on `ℝ^m × ℝ`, the null set being pulled back
  through the nonsingular map `Θ`, and it is then sliced: for a.e. `t`, for a.e. `u`;
* hence the spatial integrand of `(a G ∘ Θ, φ)` at `(t, u)` is that of `(G, φ')` at
  `(a⁻²(t - t₀), a⁻¹ u)`, the spatial bracket is `a^m` times the bracket of `(G, φ')` at
  `a⁻²(t - t₀)` (a.e. `t`), and the window pairing at `T` is `a^{m+2}` times the integral of
  that bracket over `[a⁻²(-T - t₀), a⁻²(T - t₀)]`. The a.e. inner integrability and the
  finite-window integrability are transferred before any limit is taken;
* `∫ (g ∘ Θ) φ = a^{m+2} ∫ g φ'` (change of variables).

For the dilation the window is the symmetric window `[-a⁻²T, a⁻²T]`, and `T ↦ a⁻²T → ∞`. For
the time shift the window is `[-T - t₀, T - t₀]`; `HalfTimeBracketIntegrableStatement` (the
hypothesis `hhp`) puts the bracket in `L¹(dt)`, so both the shifted and the symmetric windows
converge to its integral (symmetric convergence alone would not suffice).

All helpers carry the part prefix `fsimb1_`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-! ## The affine time map on `ℝ` -/

theorem fsimb1_measurePreserving_affine {c : ℝ} (hc : 0 < c) (t₀ : ℝ) :
    MeasurePreserving (fun t : ℝ => c * (t - t₀)) volume (ENNReal.ofReal c⁻¹ • volume) := by
  have h2 : MeasurePreserving (fun t : ℝ => c * t) volume (ENNReal.ofReal c⁻¹ • volume) := by
    refine ⟨measurable_const_mul c, ?_⟩
    rw [Real.map_volume_mul_left hc.ne', abs_of_pos (inv_pos.mpr hc)]
  exact h2.comp (measurePreserving_sub_right volume t₀)

theorem fsimb1_measurableEmbedding_affine {c : ℝ} (hc : 0 < c) (t₀ : ℝ) :
    MeasurableEmbedding (fun t : ℝ => c * (t - t₀)) :=
  (measurableEmbedding_mulLeft₀ hc.ne').comp (measurableEmbedding_subRight t₀)

theorem fsimb1_preimage_affine {c : ℝ} (hc : 0 < c) (t₀ T : ℝ) :
    (fun t : ℝ => c * (t - t₀)) ⁻¹' Icc (c * (-T - t₀)) (c * (T - t₀)) = Icc (-T) T := by
  ext t
  simp only [mem_preimage, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith [le_of_mul_le_mul_left h1 hc], by linarith [le_of_mul_le_mul_left h2 hc]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_le_mul_of_nonneg_left (by linarith) hc.le,
      mul_le_mul_of_nonneg_left (by linarith) hc.le⟩

/-- Null sets of times pull back through the affine map `t ↦ c (t - t₀)`, `c > 0`. -/
theorem fsimb1_ae_comp_affine {c : ℝ} (hc : 0 < c) (t₀ : ℝ) {P : ℝ → Prop}
    (h : ∀ᵐ s : ℝ, P s) : ∀ᵐ t : ℝ, P (c * (t - t₀)) :=
  (fsimb1_measurePreserving_affine hc t₀).quasiMeasurePreserving.ae (Measure.ae_smul_measure h _)

/-- The window pairing of a bracket transported by the affine time map. -/
theorem fsimb1_window {c : ℝ} (hc : 0 < c) (t₀ : ℝ) (K : ℂ) (b b' : ℝ → ℂ)
    (hb : ∀ᵐ t : ℝ, b' t = K * b (c * (t - t₀))) (T : ℝ) :
    (∫ t in Icc (-T) T, b' t) =
      K * (c⁻¹ • ∫ s in Icc (c * (-T - t₀)) (c * (T - t₀)), b s) := by
  have h2 : (∫ t in Icc (-T) T, b (c * (t - t₀))) =
      ∫ s in Icc (c * (-T - t₀)) (c * (T - t₀)), b s ∂(ENNReal.ofReal c⁻¹ • volume) := by
    have := (fsimb1_measurePreserving_affine hc t₀).setIntegral_preimage_emb
      (fsimb1_measurableEmbedding_affine hc t₀) b (Icc (c * (-T - t₀)) (c * (T - t₀)))
    rwa [fsimb1_preimage_affine hc t₀ T] at this
  rw [integral_congr_ae (ae_restrict_of_ae hb), integral_const_mul, h2, Measure.restrict_smul,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hc.le)]

/-- Finite-window integrability of a bracket transported by the affine time map. -/
theorem fsimb1_window_integrableOn {c : ℝ} (hc : 0 < c) (t₀ : ℝ) (K : ℂ) (b b' : ℝ → ℂ)
    (hb : ∀ᵐ t : ℝ, b' t = K * b (c * (t - t₀)))
    (hint : ∀ R : ℝ, IntegrableOn b (Icc (-R) R)) (T : ℝ) : IntegrableOn b' (Icc (-T) T) := by
  have hS : IntegrableOn b (Icc (c * (-T - t₀)) (c * (T - t₀))) (ENNReal.ofReal c⁻¹ • volume) := by
    have h0 : IntegrableOn b (Icc (c * (-T - t₀)) (c * (T - t₀))) :=
      (hint (|c * (-T - t₀)| + |c * (T - t₀)|)).mono_set (Icc_subset_Icc
        (by linarith [neg_abs_le (c * (-T - t₀)), abs_nonneg (c * (T - t₀))])
        (by linarith [le_abs_self (c * (T - t₀)), abs_nonneg (c * (-T - t₀))]))
    rw [IntegrableOn, Measure.restrict_smul]
    exact h0.smul_measure ENNReal.ofReal_ne_top
  have h1 : IntegrableOn (fun t => b (c * (t - t₀))) (Icc (-T) T) := by
    rw [← fsimb1_preimage_affine hc t₀ T]
    exact ((fsimb1_measurePreserving_affine hc t₀).integrableOn_comp_preimage
      (fsimb1_measurableEmbedding_affine hc t₀)).mpr hS
  exact IntegrableOn.congr_fun_ae (f := fun t => K * b (c * (t - t₀))) (Integrable.const_mul h1 K)
    ((ae_restrict_of_ae hb).mono fun t ht => ht.symm)

/-- Integrals over increasing shifted windows of an `L¹` function converge to its integral. -/
theorem fsimb1_tendsto_shifted {b : ℝ → ℂ} (hb : Integrable b) (t₀ : ℝ) :
    Tendsto (fun T : ℝ => ∫ s in Icc (-T - t₀) (T - t₀), b s) atTop (𝓝 (∫ s, b s)) := by
  have hmono : Monotone (fun T : ℝ => Icc (-T - t₀) (T - t₀)) := fun T T' hTT' =>
    Icc_subset_Icc (by linarith) (by linarith)
  have hU : (⋃ T : ℝ, Icc (-T - t₀) (T - t₀)) = univ := by
    refine eq_univ_of_forall fun s => mem_iUnion.mpr ⟨|s| + |t₀|, ?_, ?_⟩
    · linarith [neg_abs_le s, neg_le_abs t₀]
    · linarith [le_abs_self s, le_abs_self t₀]
  have hint : IntegrableOn b (⋃ T : ℝ, Icc (-T - t₀) (T - t₀)) := by
    rw [hU]
    exact hb.integrableOn
  have h := tendsto_setIntegral_of_monotone (μ := volume) (fun T : ℝ => measurableSet_Icc) hmono
    hint
  rwa [hU, setIntegral_univ] at h

/-! ## Slicing and the spatial change of variables -/

/-- An almost-everywhere statement on `ℝ^m × ℝ` holds for a.e. time `t`, for a.e. `u`. -/
theorem fsimb1_ae_slice {m : ℕ} {P : FourierSpace m → Prop} (h : ∀ᵐ x, P x) :
    ∀ᵐ t : ℝ, ∀ᵐ u : Spatial m, P (WithLp.toLp 2 (u, t)) := by
  have h1 : ∀ᵐ p ∂((volume : Measure (Spatial m)).prod (volume : Measure ℝ)),
      P (WithLp.toLp 2 p) :=
    (fourierCoordinates_symm_measurePreserving_prod m).quasiMeasurePreserving.ae h
  have h2 : ∀ᵐ q ∂((volume : Measure ℝ).prod (volume : Measure (Spatial m))),
      P (WithLp.toLp 2 q.swap) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae h1
  exact Measure.ae_ae_of_ae_prod h2

theorem fsimb1_integrable_ae {m : ℕ} {a : ℝ} (ha : 0 < a) (σ : ℝ → ℝ)
    (I I' : ℝ → Spatial m → ℂ) (h : ∀ᵐ t : ℝ, ∀ᵐ u : Spatial m, I' t u = I (σ t) (a⁻¹ • u))
    (hI : ∀ᵐ t : ℝ, Integrable (I (σ t))) : ∀ᵐ t : ℝ, Integrable (I' t) := by
  filter_upwards [h, hI] with t ht hit
  exact (hit.comp_smul (inv_ne_zero ha.ne')).congr (ht.mono fun u hu => hu.symm)

theorem fsimb1_bracket_ae {m : ℕ} {a : ℝ} (ha : 0 < a) (σ : ℝ → ℝ)
    (I I' : ℝ → Spatial m → ℂ) (h : ∀ᵐ t : ℝ, ∀ᵐ u : Spatial m, I' t u = I (σ t) (a⁻¹ • u)) :
    ∀ᵐ t : ℝ, (∫ u, I' t u) = ((a ^ m : ℝ) : ℂ) * ∫ v, I (σ t) v := by
  filter_upwards [h] with t ht
  rw [integral_congr_ae ht, Measure.integral_comp_smul (volume : Measure (Spatial m)) (I (σ t)) a⁻¹,
    finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_pos (pow_pos ha m), Complex.real_smul]

/-! ## The affine map `Θ` in ordinary coordinates -/

theorem fsimb1_theta_apply {m : ℕ} (a : ℝ) (ha : 0 < a) (t₀ : ℝ) (x : FourierSpace m) :
    fourierSimilarity (point (0 : Spatial m) t₀) a ha x =
      WithLp.toLp 2 (a⁻¹ • (WithLp.ofLp x).1, a⁻¹ ^ 2 * ((WithLp.ofLp x).2 - t₀)) := by
  rw [fourierSimilarity_apply]
  have h1 : (point (0 : Spatial m) t₀).1 = 0 := rfl
  have h2 : (point (0 : Spatial m) t₀).2.val = t₀ := rfl
  rw [h1, h2, sub_zero]

theorem fsimb1_theta_toLp {m : ℕ} (a : ℝ) (ha : 0 < a) (t₀ : ℝ) (u : Spatial m) (t : ℝ) :
    fourierSimilarity (point (0 : Spatial m) t₀) a ha (WithLp.toLp 2 (u, t)) =
      WithLp.toLp 2 (a⁻¹ • u, a⁻¹ ^ 2 * (t - t₀)) := by
  rw [fsimb1_theta_apply]

/-- Change of variables under `Θ`: `∫ F ∘ Θ = a^{m+2} ∫ F`. -/
theorem fsimb1_integral_comp {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (ha : 0 < a) (t₀ : ℝ) (F : FourierSpace m → E) :
    (∫ x, F (fourierSimilarity (point (0 : Spatial m) t₀) a ha x)) = (a ^ (m + 2)) • ∫ y, F y := by
  rw [(measurePreserving_fourierSimilarity (point (0 : Spatial m) t₀) a ha).integral_comp
      (fourierSimilarity (point (0 : Spatial m) t₀) a ha).measurableEmbedding F,
    integral_smul_measure, ENNReal.toReal_pow, ENNReal.toReal_ofReal ha.le]

private theorem fsimb1_locallyIntegrable_smul {X E : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [NormedAddCommGroup E] {f : X → E} {μ : Measure X}
    (hf : LocallyIntegrable f μ) {c : ℝ≥0∞} (hc : c ≠ ⊤) : LocallyIntegrable f (c • μ) := by
  intro x
  obtain ⟨U, hU, h⟩ := hf x
  refine ⟨U, hU, ?_⟩
  change Integrable f ((c • μ).restrict U)
  rw [Measure.restrict_smul]
  exact h.smul_measure hc

theorem fsimb1_locallyIntegrable {m : ℕ} (a : ℝ) (ha : 0 < a) (t₀ : ℝ)
    {g : FourierSpace m → ℝ} (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun x => g (fourierSimilarity (point (0 : Spatial m) t₀) a ha x)) volume := by
  have hc : ENNReal.ofReal a ^ (m + 2) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hg' : LocallyIntegrable g
      (Measure.map (fourierSimilarity (point (0 : Spatial m) t₀) a ha) volume) := by
    rw [(measurePreserving_fourierSimilarity (point (0 : Spatial m) t₀) a ha).map_eq]
    exact fsimb1_locallyIntegrable_smul hg hc
  exact (locallyIntegrable_map_homeomorph _).mp hg'

/-- The transformed test `φ' = φ ∘ Θ⁻¹`, built in ordinary coordinates. -/
theorem fsimb1_test {m : ℕ} (a : ℝ) (ha : 0 < a) (t₀ : ℝ) (φ : FourierSpace m → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (h0 : ∫ x, φ x = 0) :
    ∃ (φ' : FourierSpace m → ℝ) (_ : ContDiff ℝ ∞ φ') (_ : HasCompactSupport φ'),
      (∫ x, φ' x = 0) ∧ ∀ x, φ x = φ' (fourierSimilarity (point (0 : Spatial m) t₀) a ha x) := by
  refine ⟨fun y => φ ((fourierSimilarity (point (0 : Spatial m) t₀) a ha).symm y),
    hφ.comp (contDiff_fourierSimilarity_symm _ a ha),
    hc.comp_homeomorph (fourierSimilarity (point (0 : Spatial m) t₀) a ha).symm, ?_,
    fun x => by simp only [Homeomorph.symm_apply_apply]⟩
  have h1 := fsimb1_integral_comp a ha t₀
    (fun y => φ ((fourierSimilarity (point (0 : Spatial m) t₀) a ha).symm y))
  simp only [Homeomorph.symm_apply_apply] at h1
  rw [h0, smul_eq_mul] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ ha.ne')

theorem fsimb1_integral_pairing {m : ℕ} (a : ℝ) (ha : 0 < a) (t₀ : ℝ)
    (g g' φ φ' : FourierSpace m → ℝ)
    (hg' : ∀ x, g' x = g (fourierSimilarity (point (0 : Spatial m) t₀) a ha x))
    (hφφ' : ∀ x, φ x = φ' (fourierSimilarity (point (0 : Spatial m) t₀) a ha x)) :
    (∫ x, (g' x : ℂ) * (φ x : ℂ)) = ((a ^ (m + 2) : ℝ) : ℂ) * ∫ y, (g y : ℂ) * (φ' y : ℂ) := by
  calc (∫ x, (g' x : ℂ) * (φ x : ℂ))
      = ∫ x, (fun y => (g y : ℂ) * (φ' y : ℂ))
          (fourierSimilarity (point (0 : Spatial m) t₀) a ha x) := by
        simp only [hg', hφφ']
    _ = (a ^ (m + 2)) • ∫ y, (g y : ℂ) * (φ' y : ℂ) :=
        fsimb1_integral_comp a ha t₀ (fun y => (g y : ℂ) * (φ' y : ℂ))
    _ = _ := Complex.real_smul

/-! ## Kernel covariance, almost everywhere, and its slices -/

/-- The a.e. integrand identity on `ℝ^m × ℝ`: `(a G ∘ Θ) · D φ = (G · D φ') ∘ Θ`. The kernel
identity is pointwise; the two passages to `halfTimeDeriv` are a.e., the second pulled back
through `Θ`. -/
theorem fsimb1_ae_integrand {m : ℕ} (a : ℝ) (ha : 0 < a) (t₀ : ℝ) (G G' : FourierSpace m → ℝ)
    (hG' : ∀ x, G' x = a * G (fourierSimilarity (point (0 : Spatial m) t₀) a ha x))
    (φ φ' : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφ' : ContDiff ℝ ∞ φ') (hc' : HasCompactSupport φ')
    (hφφ' : ∀ x, φ x = φ' (fourierSimilarity (point (0 : Spatial m) t₀) a ha x)) :
    ∀ᵐ x : FourierSpace m, (G' x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x =
      (G (fourierSimilarity (point (0 : Spatial m) t₀) a ha x) : ℂ) *
        halfTimeDeriv m (realCompactTest φ' hφ' hc')
          (fourierSimilarity (point (0 : Spatial m) t₀) a ha x) := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hker : ∀ x, testKernel (realCompactTest φ hφ hc) x =
      (a : ℂ)⁻¹ * testKernel (realCompactTest φ' hφ' hc')
        (fourierSimilarity (point (0 : Spatial m) t₀) a ha x) :=
    testKernel_comp_fourierSimilarity (point (0 : Spatial m) t₀) a ha _ _ fun x => by
      rw [realCompactTest_apply, realCompactTest_apply, hφφ']
  have h2 : ∀ᵐ x : FourierSpace m,
      testKernel (realCompactTest φ' hφ' hc') (fourierSimilarity (point (0 : Spatial m) t₀) a ha x) =
        halfTimeDeriv m (realCompactTest φ' hφ' hc')
          (fourierSimilarity (point (0 : Spatial m) t₀) a ha x) :=
    (measurePreserving_fourierSimilarity (point (0 : Spatial m) t₀) a ha).quasiMeasurePreserving.ae
      (Measure.ae_smul_measure (testKernel_ae_halfTimeDeriv (realCompactTest φ' hφ' hc')) _)
  filter_upwards [testKernel_ae_halfTimeDeriv (realCompactTest φ hφ hc), h2] with x hx1 hx2
  rw [← hx1, hker x, hx2, hG' x, Complex.ofReal_mul]
  calc (a : ℂ) * (G (fourierSimilarity (point (0 : Spatial m) t₀) a ha x) : ℂ) *
        ((a : ℂ)⁻¹ * halfTimeDeriv m (realCompactTest φ' hφ' hc')
          (fourierSimilarity (point (0 : Spatial m) t₀) a ha x))
      = ((a : ℂ) * (a : ℂ)⁻¹) * ((G (fourierSimilarity (point (0 : Spatial m) t₀) a ha x) : ℂ) *
          halfTimeDeriv m (realCompactTest φ' hφ' hc')
            (fourierSimilarity (point (0 : Spatial m) t₀) a ha x)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ ha', one_mul]

/-- Transfer of the three representation clauses for one test, before any limit:
a.e. inner integrability, finite-window integrability, and the exact window-pairing identity
`P_{G'}(φ)(T) = a^m a² ∫_{[a⁻²(-T-t₀), a⁻²(T-t₀)]} b_{G,φ'}`. -/
theorem fsimb1_test_transfer {m : ℕ} (a : ℝ) (ha : 0 < a) (t₀ : ℝ) (G G' : FourierSpace m → ℝ)
    (hG' : ∀ x, G' x = a * G (fourierSimilarity (point (0 : Spatial m) t₀) a ha x))
    (φ φ' : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφ' : ContDiff ℝ ∞ φ') (hc' : HasCompactSupport φ')
    (hφφ' : ∀ x, φ x = φ' (fourierSimilarity (point (0 : Spatial m) t₀) a ha x)) :
    ((∀ᵐ s : ℝ, Integrable (halfTimeSpatialIntegrand G (realCompactTest φ' hφ' hc') s)) →
        ∀ᵐ t : ℝ, Integrable (halfTimeSpatialIntegrand G' (realCompactTest φ hφ hc) t)) ∧
    ((∀ R : ℝ, IntegrableOn (halfTimeSpatialBracket G (realCompactTest φ' hφ' hc')) (Icc (-R) R)) →
        ∀ T : ℝ, IntegrableOn (halfTimeSpatialBracket G' (realCompactTest φ hφ hc)) (Icc (-T) T)) ∧
    ∀ T : ℝ, halfTimeWindowPairing G' (realCompactTest φ hφ hc) T =
      ((a ^ m : ℝ) : ℂ) * ((a⁻¹ ^ 2)⁻¹ • ∫ s in Icc (a⁻¹ ^ 2 * (-T - t₀)) (a⁻¹ ^ 2 * (T - t₀)),
        halfTimeSpatialBracket G (realCompactTest φ' hφ' hc') s) := by
  have hc0 : (0 : ℝ) < a⁻¹ ^ 2 := by positivity
  have hslice : ∀ᵐ t : ℝ, ∀ᵐ u : Spatial m,
      halfTimeSpatialIntegrand G' (realCompactTest φ hφ hc) t u =
        halfTimeSpatialIntegrand G (realCompactTest φ' hφ' hc') (a⁻¹ ^ 2 * (t - t₀)) (a⁻¹ • u) := by
    filter_upwards [fsimb1_ae_slice
      (fsimb1_ae_integrand a ha t₀ G G' hG' φ φ' hφ hc hφ' hc' hφφ')] with t ht
    filter_upwards [ht] with u hu
    simpa only [halfTimeSpatialIntegrand, fsimb1_theta_toLp] using hu
  have hbr : ∀ᵐ t : ℝ, halfTimeSpatialBracket G' (realCompactTest φ hφ hc) t =
      ((a ^ m : ℝ) : ℂ) *
        halfTimeSpatialBracket G (realCompactTest φ' hφ' hc') (a⁻¹ ^ 2 * (t - t₀)) :=
    fsimb1_bracket_ae ha _ _ _ hslice
  exact ⟨fun hin => fsimb1_integrable_ae ha _ _ _ hslice (fsimb1_ae_comp_affine hc0 t₀ hin),
    fun hwin T => fsimb1_window_integrableOn hc0 t₀ _ _ _ hbr hwin T,
    fun T => fsimb1_window hc0 t₀ _ _ _ hbr T⟩

/-! ## Dilation -/

theorem fsimb1_dilation_core {m : ℕ} (R : ℝ) (hR : 0 < R) (G g G' g' : FourierSpace m → ℝ)
    (hG' : ∀ x, G' x = R * G (fourierSimilarity (point (0 : Spatial m) 0) R hR x))
    (hg' : ∀ x, g' x = g (fourierSimilarity (point (0 : Spatial m) 0) R hR x))
    (h : RepresentsHomogeneousHalfTimeDerivative G g) :
    RepresentsHomogeneousHalfTimeDerivative G' g' := by
  unfold RepresentsHomogeneousHalfTimeDerivative at h ⊢
  obtain ⟨hg, hrep⟩ := h
  refine ⟨?_, fun φ hφ hc h0 => ?_⟩
  · rw [show g' = fun x => g (fourierSimilarity (point (0 : Spatial m) 0) R hR x) from funext hg']
    exact fsimb1_locallyIntegrable R hR 0 hg
  obtain ⟨φ', hφ', hc', h0', hφφ'⟩ := fsimb1_test R hR 0 φ hφ hc h0
  obtain ⟨hin, hwin, hlim⟩ := hrep φ' hφ' hc' h0'
  obtain ⟨hin', hwin', hP⟩ := fsimb1_test_transfer R hR 0 G G' hG' φ φ' hφ hc hφ' hc' hφφ'
  refine ⟨hin' hin, hwin' hwin, ?_⟩
  rw [fsimb1_integral_pairing R hR 0 g g' φ φ' hg' hφφ']
  have hc2 : (0 : ℝ) < R⁻¹ ^ 2 := by positivity
  have hT : Tendsto (fun T : ℝ => R⁻¹ ^ 2 * T) atTop atTop := tendsto_id.const_mul_atTop hc2
  refine ((hlim.comp hT).const_mul ((R ^ (m + 2) : ℝ) : ℂ)).congr fun T => ?_
  have e1 : R⁻¹ ^ 2 * (-T - 0) = -(R⁻¹ ^ 2 * T) := by ring
  have e2 : R⁻¹ ^ 2 * (T - 0) = R⁻¹ ^ 2 * T := by ring
  have e3 : (R⁻¹ ^ 2)⁻¹ = R ^ 2 := by rw [inv_pow, inv_inv]
  rw [Function.comp_apply, hP T, e1, e2, e3, Complex.real_smul]
  simp only [halfTimeWindowPairing]
  push_cast
  ring

/-- **Dilation covariance.** Exact type of
`fsim_representsHomogeneousHalfTimeDerivative_dilation`. -/
theorem fsim_representsHomogeneousHalfTimeDerivative_dilation_proof {m : ℕ} (R : ℝ) (hR : 0 < R)
    (G g : FourierSpace m → ℝ) (h : RepresentsHomogeneousHalfTimeDerivative G g) :
    RepresentsHomogeneousHalfTimeDerivative
      (fun x => R * G (WithLp.toLp 2 (R⁻¹ • (WithLp.ofLp x).1, R⁻¹ ^ 2 * (WithLp.ofLp x).2)))
      (fun x => g (WithLp.toLp 2 (R⁻¹ • (WithLp.ofLp x).1, R⁻¹ ^ 2 * (WithLp.ofLp x).2))) :=
  fsimb1_dilation_core R hR G g _ _ (fun x => by rw [fsimb1_theta_apply, sub_zero])
    (fun x => by rw [fsimb1_theta_apply, sub_zero]) h

/-! ## Time translation -/

theorem fsimb1_timeShift_core (hhp : HalfTimeBracketIntegrableStatement) {m : ℕ} (t₀ : ℝ)
    (G g G' g' : FourierSpace m → ℝ)
    (hG : ∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm))
    (hG' : ∀ x, G' x = G (fourierSimilarity (point (0 : Spatial m) t₀) 1 one_pos x))
    (hg' : ∀ x, g' x = g (fourierSimilarity (point (0 : Spatial m) t₀) 1 one_pos x))
    (h : RepresentsHomogeneousHalfTimeDerivative G g) :
    RepresentsHomogeneousHalfTimeDerivative G' g' := by
  unfold RepresentsHomogeneousHalfTimeDerivative at h ⊢
  obtain ⟨hg, hrep⟩ := h
  refine ⟨?_, fun φ hφ hc h0 => ?_⟩
  · rw [show g' = fun x => g (fourierSimilarity (point (0 : Spatial m) t₀) 1 one_pos x)
      from funext hg']
    exact fsimb1_locallyIntegrable 1 one_pos t₀ hg
  obtain ⟨φ', hφ', hc', h0', hφφ'⟩ := fsimb1_test 1 one_pos t₀ φ hφ hc h0
  obtain ⟨hin, hwin, hlim⟩ := hrep φ' hφ' hc' h0'
  obtain ⟨hin', hwin', hP⟩ := fsimb1_test_transfer 1 one_pos t₀ G G'
    (fun x => by rw [hG', one_mul]) φ φ' hφ hc hφ' hc' hφφ'
  refine ⟨hin' hin, hwin' hwin, ?_⟩
  -- The bracket of `(G, φ')` is in `L¹(dt)`.
  have hb : Integrable (halfTimeSpatialBracket G (realCompactTest φ' hφ' hc')) :=
    (hhp m G hG φ' hφ' hc' h0').2
  -- The symmetric windows converge to `∫ b`, and by `h` to `∫ g φ'`.
  have h1 := fsimb1_tendsto_shifted hb 0
  simp only [sub_zero] at h1
  have heq : (∫ s, halfTimeSpatialBracket G (realCompactTest φ' hφ' hc') s) =
      ∫ x, (g x : ℂ) * (φ' x : ℂ) := tendsto_nhds_unique h1 hlim
  rw [fsimb1_integral_pairing 1 one_pos t₀ g g' φ φ' hg' hφφ', ← heq, one_pow,
    Complex.ofReal_one, one_mul]
  -- The shifted windows converge to the same `∫ b`.
  refine (fsimb1_tendsto_shifted hb t₀).congr fun T => ?_
  rw [hP T]
  simp only [inv_one, one_pow, Complex.ofReal_one, one_mul, one_smul]

/-- **Time-translation covariance.** Exact type of
`fsim_representsHomogeneousHalfTimeDerivative_timeShift`, with
`HalfTimeBracketIntegrableStatement` kept as the hypothesis `hhp`. -/
theorem fsim_representsHomogeneousHalfTimeDerivative_timeShift_proof
    (hhp : HalfTimeBracketIntegrableStatement) {m : ℕ} (t₀ : ℝ) (G g : FourierSpace m → ℝ)
    (hG : ∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm))
    (h : RepresentsHomogeneousHalfTimeDerivative G g) :
    RepresentsHomogeneousHalfTimeDerivative
      (fun x => G (WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2 - t₀)))
      (fun x => g (WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2 - t₀))) :=
  fsimb1_timeShift_core hhp t₀ G g _ _ hG
    (fun x => by rw [fsimb1_theta_apply, inv_one, one_smul, one_pow, one_mul])
    (fun x => by rw [fsimb1_theta_apply, inv_one, one_smul, one_pow, one_mul]) h

end ParabolicRectifiability.Foundations
