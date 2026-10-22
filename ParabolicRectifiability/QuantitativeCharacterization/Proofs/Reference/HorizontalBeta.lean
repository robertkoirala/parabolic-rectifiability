import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry
import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Characterization.Proofs.Fourier.EstimateStatements
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # The horizontal beta bound

Proof of `ba1_horizontal_beta`. The actual parabolic time restriction `|T(v) - T(u)| < r²` is
kept in the temporal term.

For a horizontal `L`-reference `H` (`σ = (F,T)_# L^k`), a centre `u`, a radius `r > 0` and an
affine competitor `A(v) = a + B v` for `F`:

* `b1hbeta_exists_le_finrank_eq`: the range of `B` (rank at most `k ≤ n`) lies in a spatial
  subspace of rank exactly `k`; `b1hbeta_model` is the horizontal model `(a + W) × {T(u)}`.
* `b1hbeta_modelCost_le`: for every `v`,
  `d_P((F(v),T(v)), model)² ≤ |F(v) - A(v)|² + |T(v) - T(u)|` (test at `(A(v), T(u))`).
* `b1hbeta_preimage_ball_subset`: `(F,T)⁻¹ P((F(u),T(u)), r) ⊆
  {v : |v - u| < L r, |T(v) - T(u)| < r²}` (lower Lipschitz bound of `F`).
* `b1hbeta_fit_le`: the fit of that model is at most the spatial integral over `B(u, L r)` plus
  the time-restricted temporal integral.
* `b1hbeta_scale`: `L^{k+2} (L r)^{-k-2} = r^{-k-2}`.

The hypothesis `hbasic` (the conclusion of `ba1_horizontal_basic`) is used only for the
measurability of `(F,T)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

open Module in
/-- Every subspace of a finite-dimensional real space is contained in a subspace of any larger
rank up to the full rank. -/
theorem b1hbeta_exists_le_finrank_eq {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] :
    ∀ (d : ℕ) (p : Submodule ℝ E), finrank ℝ p + d ≤ finrank ℝ E →
      ∃ q : Submodule ℝ E, p ≤ q ∧ finrank ℝ q = finrank ℝ p + d
  | 0, p, _ => ⟨p, le_rfl, (add_zero _).symm⟩
  | d + 1, p, h => by
    have hne : p ≠ ⊤ := by
      rintro rfl
      rw [finrank_top] at h
      omega
    obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
    have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0]; exact p.zero_mem)
    have hdisj : p ⊓ (ℝ ∙ x) = ⊥ :=
      disjoint_iff.1 (Submodule.disjoint_span_singleton.2 fun h => absurd h hx)
    have hrank : finrank ℝ (p ⊔ (ℝ ∙ x) : Submodule ℝ E) = finrank ℝ p + 1 := by
      have := Submodule.finrank_sup_add_finrank_inf_eq p (ℝ ∙ x)
      rw [hdisj, finrank_bot, finrank_span_singleton hx0] at this
      omega
    obtain ⟨q, hq, hqr⟩ := b1hbeta_exists_le_finrank_eq d (p ⊔ (ℝ ∙ x)) (by rw [hrank]; omega)
    exact ⟨q, le_sup_left.trans hq, by rw [hqr, hrank]; ring⟩

open Module in
/-- A spatial subspace of rank exactly `k` containing the range of `B : ℝ^k → ℝ^n`, `k ≤ n`. -/
theorem b1hbeta_exists_range_le {n k : ℕ} (hkn : k ≤ n) (B : Spatial k →L[ℝ] Spatial n) :
    ∃ W : Submodule ℝ (Spatial n),
      LinearMap.range (B : Spatial k →ₗ[ℝ] Spatial n) ≤ W ∧ finrank ℝ W = k := by
  set p := LinearMap.range (B : Spatial k →ₗ[ℝ] Spatial n)
  have hp : finrank ℝ p ≤ k := by
    have := LinearMap.finrank_range_le (B : Spatial k →ₗ[ℝ] Spatial n)
    simpa only [finrank_euclideanSpace_fin] using this
  obtain ⟨q, hq, hqr⟩ := b1hbeta_exists_le_finrank_eq (k - finrank ℝ p) p
    (by rw [finrank_euclideanSpace_fin]; omega)
  exact ⟨q, hq, by rw [hqr]; omega⟩

/-- The horizontal model `(a + W) × {t}` through the affine competitor `v ↦ a + B v`. -/
def b1hbeta_model {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (a : Spatial n)
    (B : Spatial k →L[ℝ] Spatial n) (t : ℝ) : HorizontalModel n k :=
  ⟨hk, AffineSpatialPlane.ofTranslate (b1hbeta_exists_range_le hkn B).choose
    (b1hbeta_exists_range_le hkn B).choose_spec.2 a, t⟩

theorem b1hbeta_point_mem_model {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (a : Spatial n)
    (B : Spatial k →L[ℝ] Spatial n) (t : ℝ) (v : Spatial k) :
    point (a + B v) t ∈ (b1hbeta_model hk hkn a B t).toSet := by
  rw [HorizontalModel.mem_toSet_point]
  refine ⟨?_, rfl⟩
  change a + B v ∈ (AffineSpatialPlane.ofTranslate _ _ a).toSet
  rw [AffineSpatialPlane.ofTranslate_toSet]
  change a + B v - a ∈ (b1hbeta_exists_range_le hkn B).choose
  rw [add_sub_cancel_left]
  exact (b1hbeta_exists_range_le hkn B).choose_spec.1 (LinearMap.mem_range_self _ v)

/-- `max(x, √|y|)² ≤ x² + |y|`, in `ℝ≥0∞`. -/
theorem b1hbeta_ofReal_max_sq_le (x y : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal (max x (Real.sqrt |y|)) ^ 2 ≤ ENNReal.ofReal x ^ 2 + ENNReal.ofReal |y| := by
  rw [← ENNReal.ofReal_pow (le_max_of_le_left hx : 0 ≤ max x (Real.sqrt |y|)), ← ENNReal.ofReal_pow hx,
    ← ENNReal.ofReal_add (sq_nonneg _) (abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rcases le_total x (Real.sqrt |y|) with h | h
  · rw [max_eq_right h, Real.sq_sqrt (abs_nonneg _)]
    nlinarith [sq_nonneg x]
  · rw [max_eq_left h]
    linarith [abs_nonneg y]

/-- The squared parabolic distance from `(F(v),T(v))` to the model through `A` at time `T(u)`
is at most `|F(v) - A(v)|² + |T(v) - T(u)|`. -/
theorem b1hbeta_modelCost_le {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L) (u : Spatial k)
    (a : Spatial n) (B : Spatial k →L[ℝ] Spatial n) (v : Spatial k) :
    modelCost (T := .horizontal)
        (b1hbeta_model H.available.1 H.available.2 a B (H.height u)) (H.map v) ≤
      ‖H.spatialMap v - (a + B v)‖ₑ ^ 2 + ENNReal.ofReal |H.height v - H.height u| := by
  have hmem := b1hbeta_point_mem_model H.available.1 H.available.2 a B (H.height u) v
  refine (modelCost_le_edist_sq (T := .horizontal)
    (b1hbeta_model H.available.1 H.available.2 a B (H.height u)) hmem (H.map v)).trans ?_
  rw [edist_dist, HorizontalReference.map, dist_point, ← ofReal_norm]
  exact b1hbeta_ofReal_max_sq_le _ _ (norm_nonneg _)

/-- The preimage of the parabolic ball keeps the time restriction and lies in `B(u, L r)`. -/
theorem b1hbeta_preimage_ball_subset {n k : ℕ} {L : ℝ} (hL : 0 < L)
    (H : HorizontalReference n k L) (u : Spatial k) {r : ℝ} (hr : 0 < r) :
    H.map ⁻¹' Metric.ball (H.map u) r ⊆
      {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2} := by
  intro v hv
  rw [mem_preimage, HorizontalReference.map, HorizontalReference.map, mem_ball_point _ _ _ _ _ hr]
    at hv
  refine ⟨?_, hv.2⟩
  calc dist v u ≤ L * dist (H.spatialMap v) (H.spatialMap u) :=
        (H.spatialMap_bilipschitz v u).1
    _ = L * ‖H.spatialMap v - H.spatialMap u‖ := by rw [dist_eq_norm]
    _ < L * r := mul_lt_mul_of_pos_left hv.1 hL

theorem b1hbeta_continuous_spatialMap {n k : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (H : HorizontalReference n k L) : Continuous H.spatialMap := by
  have hlip : LipschitzWith ⟨L, hL⟩ H.spatialMap :=
    LipschitzWith.of_dist_le_mul fun u v => (H.spatialMap_bilipschitz u v).2
  exact hlip.continuous

/-- The fit of the model through `A` at the centre's time. -/
theorem b1hbeta_fit_le {n k : ℕ} {L : ℝ} (hL : 0 < L) (H : HorizontalReference n k L)
    (hmap : Measurable H.map) (u : Spatial k) {r : ℝ} (hr : 0 < r)
    (a : Spatial n) (B : Spatial k →L[ℝ] Spatial n) :
    fit (T := .horizontal) H.measure
        (b1hbeta_model H.available.1 H.available.2 a B (H.height u)) (H.map u) r ≤
      (∫⁻ v in Metric.ball u (L * r), ‖H.spatialMap v - (a + B v)‖ₑ ^ 2) +
        ∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
          ENNReal.ofReal |H.height v - H.height u| := by
  set M := b1hbeta_model H.available.1 H.available.2 a B (H.height u)
  set S := {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2}
  have hsub := b1hbeta_preimage_ball_subset hL H u hr
  have hF := b1hbeta_continuous_spatialMap hL.le H
  have hmeasA : Measurable fun v : Spatial k => ‖H.spatialMap v - (a + B v)‖ₑ ^ 2 :=
    (hF.sub (continuous_const.add B.continuous)).enorm.measurable.pow_const 2
  unfold fit HorizontalReference.measure
  rw [setLIntegral_map measurableSet_ball (measurable_modelCost (T := .horizontal) M) hmap]
  calc
    (∫⁻ v in H.map ⁻¹' Metric.ball (H.map u) r, modelCost (T := .horizontal) M (H.map v)) ≤
        ∫⁻ v in H.map ⁻¹' Metric.ball (H.map u) r,
          (‖H.spatialMap v - (a + B v)‖ₑ ^ 2 + ENNReal.ofReal |H.height v - H.height u|) :=
      lintegral_mono fun v => b1hbeta_modelCost_le H u a B v
    _ = (∫⁻ v in H.map ⁻¹' Metric.ball (H.map u) r, ‖H.spatialMap v - (a + B v)‖ₑ ^ 2) +
          ∫⁻ v in H.map ⁻¹' Metric.ball (H.map u) r,
            ENNReal.ofReal |H.height v - H.height u| :=
      lintegral_add_left hmeasA _
    _ ≤ _ := by
      gcongr ?_ + ?_
      · exact lintegral_mono_set (hsub.trans fun v hv => Metric.mem_ball.2 hv.1)
      · exact lintegral_mono_set hsub

/-- `L^{k+2} (L r)^{-k-2} = r^{-k-2}` in `ℝ≥0∞`. -/
theorem b1hbeta_scale {L r : ℝ} (hL : 0 < L) (k : ℕ) :
    ENNReal.ofReal (L ^ (k + 2)) * (ENNReal.ofReal (L * r))⁻¹ ^ (k + 2) =
      (ENNReal.ofReal r)⁻¹ ^ (k + 2) := by
  have h0 : ENNReal.ofReal L ≠ 0 := (ENNReal.ofReal_pos.2 hL).ne'
  rw [ENNReal.ofReal_mul hL.le, ENNReal.ofReal_pow hL.le,
    ENNReal.mul_inv (Or.inl h0) (Or.inl ENNReal.ofReal_ne_top), mul_pow, ← mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top, one_pow, one_mul]

/-- **`ba1_horizontal_beta`** (the temporal term), implication form over the
conclusion of `ba1_horizontal_basic`; the statement type. -/
theorem ba1_horizontal_beta_proof
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      Measurable H.map ∧ IsClosed H.carrier ∧ IsFiniteMeasureOnCompacts H.measure ∧
        H.measure.InnerRegular) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L →
      ∀ (H : HorizontalReference n k L) (u : Spatial k) (r : ℝ), 0 < r →
        betaSq H.measure k .horizontal (H.map u) r ≤
          ENNReal.ofReal (L ^ (k + 2)) *
              Characterization.spatialAffineErrorSq H.spatialMap u (L * r) +
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) := by
  intro n k L hL H u r hr
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hmap : Measurable H.map := (hbasic n k L hL H).1
  rw [betaSq_of_pos _ _ _ _ hr, Characterization.spatialAffineErrorSq,
    ite_eq_left (mul_pos hL0 hr), ← mul_assoc, b1hbeta_scale hL0, ← mul_add]
  gcongr
  rw [ENNReal.iInf_add]
  refine le_iInf fun a => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun B => ?_
  exact (iInf_le _ (b1hbeta_model H.available.1 H.available.2 a B (H.height u))).trans
    (b1hbeta_fit_le hL0 H hmap u hr a B)

end ParabolicRectifiability.QuantitativeCharacterization
