import ParabolicRectifiability.Measure.Neck.ConstructionConclusions
import ParabolicRectifiability.Measure.Neck.Selection.ModelFit

/-!
# The normalized root of the source construction

Proof of `exists_normalizedRoot`.

The finite source `ν` is carried by `S ⊆ P(q,R)`, so the global fitting error of type `T`
is attained (`exists_globalFittingError_minimizer`, compact carrier `closure P(q,R)`).
The minimizer is then normalized without increasing its cost at any point of `P(q,R)`:

* spatially, if the plane `L` lies at distance `d > R` from `x_q`, translate it by
  `(1 - R/d) e`, `e = x_q - π_L x_q`. For `|x - x_q| ≤ R` the normal residual `w` of `x`
  satisfies `|w - e| ≤ R`, hence `2⟨w,e⟩ ≥ d² - R² ≥ (1 - R/d) d²`, and
  `|w - (1 - R/d) e| ≤ |w|`; the translated plane is at distance `R` from `x_q`;
* in time (horizontal case), clamp `τ` to `[t_q - R², t_q + R²]`, which contains every
  source time.

The root is the nearest point of the normalized model to `q` (at time `τ'`, or at the
time of `q` in the vertical case); its parabolic distance to `q` is at most `R`. The zero
source needs no separate treatment: any minimizer is normalized in the same way.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace NeckSelection

/-- Spatial normalization: a translate of `L` within distance `R` of `c` whose distance
to every point of the closed ball `B(c,R)` is not larger than that of `L`. -/
theorem exists_spatial_normalization {n m : ℕ} (L : AffineSpatialPlane n m) (c : Spatial n)
    {R : ℝ} (hR : 0 < R) :
    ∃ L' : AffineSpatialPlane n m, ‖c - L'.projection c‖ ≤ R ∧
      ∀ x : Spatial n, ‖x - c‖ ≤ R → ‖x - L'.projection x‖ ≤ ‖x - L.projection x‖ := by
  by_cases hdR : ‖c - L.projection c‖ ≤ R
  · exact ⟨L, hdR, fun x _ => le_rfl⟩
  push Not at hdR
  set e : Spatial n := c - L.projection c with he
  set d : ℝ := ‖e‖ with hd
  have hd0 : 0 < d := hR.trans hdR
  set μ : ℝ := 1 - R / d with hμ
  have hRd : R / d < 1 := (div_lt_one hd0).mpr hdR
  have hμ0 : 0 ≤ μ := by linarith
  set v : Spatial n := μ • e with hv
  set L' : AffineSpatialPlane n m :=
    AffineSpatialPlane.ofTranslate L.direction L.rank_eq (L.anchor + v) with hL'
  have hmem : ∀ y ∈ L.toSet, y + v ∈ L'.toSet := by
    intro y hy
    rw [hL', AffineSpatialPlane.ofTranslate_toSet]
    show y + v - (L.anchor + v) ∈ L.direction
    rw [show y + v - (L.anchor + v) = y - L.anchor by abel]
    exact hy
  refine ⟨L', ?_, ?_⟩
  · refine (L'.nearest c (hmem _ (L.projection_mem c))).trans (le_of_eq ?_)
    have h1 : c - (L.projection c + v) = (R / d) • e := by
      rw [show c - (L.projection c + v) = e - v by rw [he]; abel, hv, hμ, sub_smul, one_smul]
      abel
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hd0), ← hd]
    exact div_mul_cancel₀ R hd0.ne'
  · intro x hx
    refine (L'.nearest x (hmem _ (L.projection_mem x))).trans ?_
    set w : Spatial n := x - L.projection x with hw
    have hwe : x - (L.projection x + v) = w - μ • e := by rw [hw, hv]; abel
    rw [hwe]
    -- `w - e` is the normal part of `x - c`
    have hperp : w - e ∈ L.directionᗮ :=
      L.directionᗮ.sub_mem (L.residual_orthogonal x) (L.residual_orthogonal c)
    have hpar : L.projection x - L.projection c ∈ L.direction := by
      have h1 := L.projection_mem x
      have h2 := L.projection_mem c
      rw [AffineSpatialPlane.mem_toSet] at h1 h2
      have := L.direction.sub_mem h1 h2
      rwa [show L.projection x - L.anchor - (L.projection c - L.anchor) =
        L.projection x - L.projection c by abel] at this
    have hsplit : x - c = (w - e) + (L.projection x - L.projection c) := by
      rw [hw, he]; abel
    have hinner : ⟪w - e, L.projection x - L.projection c⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal hpar hperp
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real hinner
    rw [← hsplit] at hpyth
    have hwe2 : ‖w - e‖ ^ 2 ≤ R ^ 2 := by
      have h1 : ‖w - e‖ ^ 2 ≤ ‖x - c‖ ^ 2 := by
        nlinarith [mul_self_nonneg ‖L.projection x - L.projection c‖]
      exact h1.trans (pow_le_pow_left₀ (norm_nonneg _) hx 2)
    -- expand both squares
    have e1 : ‖w - e‖ ^ 2 = ‖w‖ ^ 2 - 2 * ⟪w, e⟫ + d ^ 2 := by
      rw [norm_sub_sq_real, ← hd]
    have e2 : ‖w - μ • e‖ ^ 2 = ‖w‖ ^ 2 - 2 * (μ * ⟪w, e⟫) + μ ^ 2 * d ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hμ0, ← hd, mul_pow]
    have hRd2 : R / d * d ^ 2 = R * d := by
      rw [sq, ← mul_assoc, div_mul_cancel₀ R hd0.ne']
    have hμd : μ * d ^ 2 = d ^ 2 - R * d := by
      rw [hμ, sub_mul, one_mul, hRd2]
    have hRR : R * R ≤ R * d := mul_le_mul_of_nonneg_left hdR.le hR.le
    have hA : μ * d ^ 2 ≤ 2 * ⟪w, e⟫ := by
      nlinarith [sq_nonneg ‖w‖]
    have hkey : μ ^ 2 * d ^ 2 ≤ 2 * (μ * ⟪w, e⟫) := by
      have := mul_le_mul_of_nonneg_left hA hμ0
      nlinarith
    have hsq : ‖w - μ • e‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [e2]
      linarith
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Clamping a time level to `[c - R², c + R²]` does not increase its distance to any time
in that interval. -/
theorem exists_time_clamp (c τ R2 : ℝ) (hR2 : 0 ≤ R2) :
    ∃ τ' : ℝ, |τ' - c| ≤ R2 ∧ ∀ t, |t - c| ≤ R2 → |t - τ'| ≤ |t - τ| := by
  by_cases h1 : τ < c - R2
  · refine ⟨c - R2, abs_le.mpr ⟨by linarith, by linarith⟩, fun t ht => ?_⟩
    have ht' := abs_le.mp ht
    exact abs_le_abs (by linarith) (by linarith)
  by_cases h2 : c + R2 < τ
  · refine ⟨c + R2, abs_le.mpr ⟨by linarith, by linarith⟩, fun t ht => ?_⟩
    have ht' := abs_le.mp ht
    rw [abs_sub_comm t (c + R2), abs_sub_comm t τ]
    exact abs_le_abs (by linarith) (by linarith)
  push Not at h1 h2
  exact ⟨τ, abs_le.mpr ⟨by linarith, by linarith⟩, fun t _ => le_rfl⟩

theorem sqrt_le_of_abs_le {a R : ℝ} (hR : 0 ≤ R) (h : |a| ≤ R ^ 2) : Real.sqrt |a| ≤ R :=
  (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq hR)

/-- Normalization of a horizontal model. -/
theorem horizontal_normalization {n k : ℕ} (M : HorizontalModel n k) (q : Space n) {R : ℝ}
    (hR : 0 < R) :
    ∃ M' : HorizontalModel n k,
      (∀ y ∈ Metric.ball q R,
        modelCost (T := .horizontal) M' y ≤ modelCost (T := .horizontal) M y) ∧
      ∃ z ∈ M'.toSet, dist z q ≤ R := by
  rcases q with ⟨qx, ⟨qt⟩⟩
  obtain ⟨L', hL'c, hL'⟩ := exists_spatial_normalization M.spatial qx hR
  obtain ⟨τ', hτ'c, hτ'⟩ := exists_time_clamp qt M.time (R ^ 2) (sq_nonneg R)
  refine ⟨⟨M.positive, L', τ'⟩, ?_, point (L'.projection qx) τ', ?_, ?_⟩
  · rintro ⟨x, ⟨t⟩⟩ hy
    change point x t ∈ Metric.ball (point qx qt) R at hy
    rw [mem_ball_point _ _ _ _ _ hR] at hy
    change modelCost (T := .horizontal) (⟨M.positive, L', τ'⟩ : HorizontalModel n k) (point x t) ≤
      modelCost (T := .horizontal) M (point x t)
    rw [HorizontalModel.modelCost_point, HorizontalModel.modelCost_point]
    try dsimp only
    refine ENNReal.ofReal_le_ofReal (max_le_max ?_ (hτ' t hy.2.le))
    rw [← L'.residual, ← M.spatial.residual]
    exact pow_le_pow_left₀ (norm_nonneg _) (hL' x hy.1.le) 2
  · exact ⟨L'.projection_mem qx, rfl⟩
  · change dist (point (L'.projection qx) τ') (point qx qt) ≤ R
    rw [dist_point]
    refine max_le ?_ (sqrt_le_of_abs_le hR.le hτ'c)
    rw [norm_sub_rev]
    exact hL'c

/-- Normalization of a vertical model. -/
theorem vertical_normalization {n k : ℕ} (M : VerticalModel n k) (q : Space n) {R : ℝ}
    (hR : 0 < R) :
    ∃ M' : VerticalModel n k,
      (∀ y ∈ Metric.ball q R,
        modelCost (T := .vertical) M' y ≤ modelCost (T := .vertical) M y) ∧
      ∃ z ∈ M'.toSet, dist z q ≤ R := by
  rcases q with ⟨qx, ⟨qt⟩⟩
  obtain ⟨L', hL'c, hL'⟩ := exists_spatial_normalization M.spatial qx hR
  refine ⟨⟨M.spatialRank, M.two_le, M.rank_eq, L'⟩, ?_, point (L'.projection qx) qt, ?_, ?_⟩
  · rintro ⟨x, ⟨t⟩⟩ hy
    change point x t ∈ Metric.ball (point qx qt) R at hy
    rw [mem_ball_point _ _ _ _ _ hR] at hy
    change modelCost (T := .vertical)
        (⟨M.spatialRank, M.two_le, M.rank_eq, L'⟩ : VerticalModel n k) (point x t) ≤
      modelCost (T := .vertical) M (point x t)
    rw [VerticalModel.modelCost_point, VerticalModel.modelCost_point]
    try dsimp only
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← L'.residual, ← M.spatial.residual]
    exact pow_le_pow_left₀ (norm_nonneg _) (hL' x hy.1.le) 2
  · exact L'.projection_mem qx
  · change dist (point (L'.projection qx) qt) (point qx qt) ≤ R
    rw [dist_point, sub_self, abs_zero, Real.sqrt_zero]
    refine max_le ?_ hR.le
    rw [norm_sub_rev]
    exact hL'c

end NeckSelection

open NeckSelection

/-- **`exists_normalizedRoot`**: existence of a normalized root. -/
theorem exists_normalizedRoot_proof (n : ℕ) :
    ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n), T.Available n k → k < n + 2 →
      P.IsAdmissible → ∃ (L : AffineSpatialPlane n (T.rank k)) (τ : ℝ) (z : Space n),
        P.IsRootChoice k T L τ z := by
  intro k T P hT _ hP
  have := P.finite
  have hF := nonempty_models hT
  have haeS : ∀ᵐ y ∂P.ν, y ∈ P.S := mem_ae_iff.mpr hP.carried
  have hae : ∀ᵐ y ∂P.ν, y ∈ Metric.ball P.q P.R := haeS.mono fun y hy => hP.S_subset hy
  obtain ⟨M, hM, -⟩ := exists_globalFittingError_minimizer P.ν hF
    (isCompact_closedBall P.q P.R) (hae.mono fun y hy => Metric.ball_subset_closedBall hy)
  cases T with
  | horizontal =>
    obtain ⟨M', hcost, z, hzM, hzq⟩ := horizontal_normalization M P.q hP.R_pos
    refine ⟨M'.spatial, M'.time, z, fun M₀ => ?_, hzM.1, fun _ => hzM.2, hzq⟩
    calc ∫⁻ y, Metric.infEDist y (NeckType.horizontal.lowerModelSet M'.spatial M'.time) ^ 2 ∂P.ν
        = ∫⁻ y, modelCost (T := .horizontal) M' y ∂P.ν := rfl
      _ ≤ ∫⁻ y, modelCost (T := .horizontal) M y ∂P.ν :=
          lintegral_mono_ae (hae.mono fun y hy => hcost y hy)
      _ = globalFittingError P.ν k FamilyKind.horizontal := hM
      _ ≤ ∫⁻ y, modelCost M₀ y ∂P.ν := iInf_le _ M₀
  | vertical =>
    obtain ⟨M', hcost, z, hzM, hzq⟩ := vertical_normalization M P.q hP.R_pos
    refine ⟨modelPlane .vertical M', 0, z, ?_, ?_, ?_, hzq⟩
    · intro M₀
      rw [show NeckType.vertical.lowerModelSet (modelPlane .vertical M') 0 =
          modelSet (T := .vertical) M' from lowerModelSet_modelPlane .vertical M']
      calc ∫⁻ y, Metric.infEDist y (modelSet (T := .vertical) M') ^ 2 ∂P.ν
          = ∫⁻ y, modelCost (T := .vertical) M' y ∂P.ν := rfl
        _ ≤ ∫⁻ y, modelCost (T := .vertical) M y ∂P.ν :=
            lintegral_mono_ae (hae.mono fun y hy => hcost y hy)
        _ = globalFittingError P.ν k FamilyKind.vertical := hM
        _ ≤ ∫⁻ y, modelCost M₀ y ∂P.ν := iInf_le _ M₀
    · have h := lowerModelSet_modelPlane .vertical M'
      have hz : z ∈ NeckType.vertical.lowerModelSet (modelPlane .vertical M') 0 := by
        rw [show NeckType.vertical.lowerModelSet (modelPlane .vertical M') 0 =
          modelSet (T := .vertical) M' from h]
        exact hzM
      exact hz
    · intro h
      cases h

end ParabolicRectifiability
