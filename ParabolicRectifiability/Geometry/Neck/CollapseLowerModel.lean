import ParabolicRectifiability.Geometry.Neck.Collapse
import ParabolicRectifiability.Measure.Beta

/-!
# The covariance identity at a failed continuation test

`collapsed_lowerModel_error_proof` has the type of `ChargeCollapse.collapsed_lowerModel_error`.

Let `S = μ ⌞ P(g,ρ)` be the covariance source of the test and `d = T.rank k ≥ 1`.
The top spectral plane of rank `d - 1` attains `I_{d-1}`, and
`I_{d-1} = I_d + λ_d` (`SpatialSource.minimumError_step`). The spatial plane of the
model `Pm` has rank `d`, so `I_d` is at most its spatial fitting error, which is at
most `fit μ Pm g ρ` because the parabolic distance to `Pm` dominates the spatial
residual. For the lower model `L × {τ}` (horizontal, `τ` the time of `Pm`) or
`L × ℝ` (vertical), the squared parabolic distance is at most the squared spatial
residual about `L` plus `|t - τ|`, and `|t - τ|` is at most the cost of `Pm`
(vertical: `t - τ = 0` for the point with the same time). Integrating gives
`∫ d_P(z, lower)^2 ≤ I_{d-1} + fit ≤ λ_d + I_d + fit < a ρ^{k+2} + 2 fit`.
All integrals use the original source restricted to the open ball.
-/

noncomputable section

namespace ParabolicRectifiability

namespace ChargeCollapse

open MeasureTheory Set
open scoped ENNReal

/-- The parabolic distance in coordinates. -/
theorem gm2_dist_eq {n : ℕ} (z w : Space n) :
    dist z w = max ‖z.1 - w.1‖ (Real.sqrt |z.2.val - w.2.val|) := by
  rcases z with ⟨x, ⟨t⟩⟩
  rcases w with ⟨y, ⟨s⟩⟩
  exact dist_point x y t s

/-- `max(a, √b)^2 ≤ a^2 + b`. -/
theorem gm2_max_sqrt_sq_le {a b : ℝ} (hb : 0 ≤ b) :
    max a (Real.sqrt b) ^ 2 ≤ a ^ 2 + b := by
  rcases le_total a (Real.sqrt b) with h | h
  · rw [max_eq_right h, Real.sq_sqrt hb]
    exact le_add_of_nonneg_left (sq_nonneg a)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right hb

/-- The squared distance to a set containing `point x s` is at most the squared spatial
distance to `x` plus the time distance to `s`. -/
theorem gm2_infEDist_sq_le {n : ℕ} (M : Set (Space n)) (z : Space n) (x : Spatial n) (s : ℝ)
    (hw : point x s ∈ M) :
    Metric.infEDist z M ^ 2 ≤
      ENNReal.ofReal (‖z.1 - x‖ ^ 2) + ENNReal.ofReal |z.2.val - s| := by
  have h1 : Metric.infEDist z M ≤ ENNReal.ofReal (dist z (point x s)) :=
    (Metric.infEDist_le_edist_of_mem hw).trans_eq (edist_dist _ _)
  have h2 : dist z (point x s) = max ‖z.1 - x‖ (Real.sqrt |z.2.val - s|) :=
    gm2_dist_eq z (point x s)
  calc Metric.infEDist z M ^ 2 ≤ ENNReal.ofReal (dist z (point x s)) ^ 2 :=
        pow_le_pow_left₀ zero_le h1 2
    _ = ENNReal.ofReal (dist z (point x s) ^ 2) := (ENNReal.ofReal_pow dist_nonneg 2).symm
    _ ≤ ENNReal.ofReal (‖z.1 - x‖ ^ 2 + |z.2.val - s|) := by
        apply ENNReal.ofReal_le_ofReal
        rw [h2]
        exact gm2_max_sqrt_sq_le (abs_nonneg _)
    _ = _ := ENNReal.ofReal_add (sq_nonneg _) (abs_nonneg _)

/-- The squared spatial residual about a plane is measurable. -/
theorem gm2_measurable_residual {n l : ℕ} (L : AffineSpatialPlane n l) :
    Measurable fun z : Space n => ENNReal.ofReal (‖z.1 - L.projection z.1‖ ^ 2) := by
  have hc : Continuous fun z : Space n => ‖z.1 - L.projection z.1‖ ^ 2 :=
    ((continuous_fst.sub (L.continuous_projection.comp continuous_fst)).norm).pow 2
  exact ENNReal.measurable_ofReal.comp hc.measurable

/-- The integral of the squared spatial residual on the ball is the covariance fitting
error of the ball source `μ ⌞ P(g,ρ)`. -/
theorem gm2_lintegral_residual {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ]
    (g : Space n) {ρ : ℝ} (hρ : 0 < ρ) {l : ℕ} (P : AffineSpatialPlane n l) :
    ∫⁻ z in Metric.ball g ρ, ENNReal.ofReal (‖z.1 - P.projection z.1‖ ^ 2) ∂μ =
      ENNReal.ofReal ((SpatialSource.ofBall μ g ρ hρ).fittingError P) := by
  rw [SpatialSource.fittingError, ofReal_integral_eq_lintegral_ofReal
    ((SpatialSource.ofBall μ g ρ hρ).integrable_fittingError P)
    (ae_of_all _ fun z => sq_nonneg _)]
  rfl

/-- The spatial residual about the plane of a horizontal model is at most its cost. -/
theorem gm2_spatial_le_cost_horizontal {n k : ℕ} (P : HorizontalModel n k) (z : Space n) :
    ENNReal.ofReal (‖z.1 - P.spatial.projection z.1‖ ^ 2) ≤
      modelCost (T := .horizontal) P z := by
  rw [HorizontalModel.modelCost_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  unfold HorizontalModel.realCost AffineSpatialPlane.spatialCost
  rw [coordinatesHomeomorph_apply, AffineSpatialPlane.residual]
  exact le_max_left _ _

/-- The time distance to a horizontal model is at most its cost. -/
theorem gm2_time_le_cost_horizontal {n k : ℕ} (P : HorizontalModel n k) (z : Space n) :
    ENNReal.ofReal |z.2.val - P.time| ≤ modelCost (T := .horizontal) P z := by
  rw [HorizontalModel.modelCost_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  unfold HorizontalModel.realCost
  exact le_max_right _ _

/-- The spatial residual about the plane of a vertical model is at most its cost. -/
theorem gm2_spatial_le_cost_vertical {n k : ℕ} (P : VerticalModel n k) (z : Space n) :
    ENNReal.ofReal (‖z.1 - P.spatial.projection z.1‖ ^ 2) ≤
      modelCost (T := .vertical) P z := by
  rw [VerticalModel.modelCost_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  unfold VerticalModel.realCost AffineSpatialPlane.spatialCost
  rw [coordinatesHomeomorph_apply, AffineSpatialPlane.residual]

/-- `I_d` is at most the fitting error of every plane of rank `d`. -/
theorem gm2_minimumError_le {n : ℕ} (S : SpatialSource n) {d l : ℕ} (hdn : d ≤ n)
    (P : AffineSpatialPlane n l) (hl : l = d) : S.minimumError d ≤ S.fittingError P := by
  have hln : l ≤ n := by omega
  calc S.minimumError d = S.minimumError l := by rw [hl]
    _ = S.spectralTail l := S.minimumError_eq_tail l hln
    _ ≤ S.fittingError P := S.spectralTail_le_fittingError hln P

/-- The covariance identity: the top spectral plane of rank `d - 1` has fitting error
`I_d + λ_d`. -/
theorem gm2_lowerPlane {n : ℕ} (S : SpatialSource n) {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n)
    {X E : ℝ} (hsmall : S.rankEigenvalue d < X) (hE : S.minimumError d ≤ E) :
    S.fittingError (S.topPlane (d - 1) (by omega)) ≤ X + E := by
  have heig : S.rankEigenvalue d = S.eigenvalue ⟨d - 1, by omega⟩ := by
    unfold SpatialSource.rankEigenvalue
    split_ifs with h
    · rfl
    · exact absurd ⟨hd1, hdn⟩ h
  rw [heig] at hsmall
  rw [S.minimumError_attained, S.minimumError_step d hd1 hdn]
  linarith

/-- The final integration, common to both types. -/
theorem gm2_collapse_calc {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ] (g : Space n)
    {ρ : ℝ} (hρ : 0 < ρ) {l : ℕ} (L : AffineSpatialPlane n l) (M : Set (Space n))
    (cost : Space n → ℝ≥0∞) {X E : ℝ}
    (hpt : ∀ z, Metric.infEDist z M ^ 2 ≤
      ENNReal.ofReal (‖z.1 - L.projection z.1‖ ^ 2) + cost z)
    (hL : (SpatialSource.ofBall μ g ρ hρ).fittingError L ≤ X + E)
    (hE : ENNReal.ofReal E ≤ ∫⁻ z in Metric.ball g ρ, cost z ∂μ) :
    ∫⁻ z in Metric.ball g ρ, Metric.infEDist z M ^ 2 ∂μ ≤
      ENNReal.ofReal X + 2 * ∫⁻ z in Metric.ball g ρ, cost z ∂μ := by
  calc ∫⁻ z in Metric.ball g ρ, Metric.infEDist z M ^ 2 ∂μ
      ≤ ∫⁻ z in Metric.ball g ρ,
          (ENNReal.ofReal (‖z.1 - L.projection z.1‖ ^ 2) + cost z) ∂μ := lintegral_mono hpt
    _ = ∫⁻ z in Metric.ball g ρ, ENNReal.ofReal (‖z.1 - L.projection z.1‖ ^ 2) ∂μ +
          ∫⁻ z in Metric.ball g ρ, cost z ∂μ := lintegral_add_left (gm2_measurable_residual L) _
    _ = ENNReal.ofReal ((SpatialSource.ofBall μ g ρ hρ).fittingError L) +
          ∫⁻ z in Metric.ball g ρ, cost z ∂μ := by rw [gm2_lintegral_residual μ g hρ L]
    _ ≤ ENNReal.ofReal (X + E) + ∫⁻ z in Metric.ball g ρ, cost z ∂μ := by
        gcongr ?_ + _
        exact ENNReal.ofReal_le_ofReal hL
    _ ≤ ENNReal.ofReal X + ENNReal.ofReal E + ∫⁻ z in Metric.ball g ρ, cost z ∂μ := by
        gcongr ?_ + _
        exact ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal X + ∫⁻ z in Metric.ball g ρ, cost z ∂μ +
          ∫⁻ z in Metric.ball g ρ, cost z ∂μ := by
        gcongr
    _ = ENNReal.ofReal X + 2 * ∫⁻ z in Metric.ball g ρ, cost z ∂μ := by
        rw [two_mul, add_assoc]

/-- The horizontal case (`d = k`, lower model `L × {τ}` with `τ` the time of
`Pm`). -/
theorem gm2_lowerModel_horizontal {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (μ : Measure (Space n)) [IsFiniteMeasure μ] (g : Space n) {ρ : ℝ} (hρ : 0 < ρ) (a : ℝ)
    (hsmall : (SpatialSource.ofBall μ g ρ hρ).rankEigenvalue k < a * ρ ^ (k + 2))
    (Pm : HorizontalModel n k) :
    ∃ (L : AffineSpatialPlane n (k - 1)) (τ : ℝ),
      ∫⁻ z in Metric.ball g ρ,
          Metric.infEDist z (NeckType.horizontal.collapseModelSet L τ) ^ 2 ∂μ ≤
        ENNReal.ofReal (a * ρ ^ (k + 2)) + 2 * fit (T := .horizontal) μ Pm g ρ := by
  have hfitP : ENNReal.ofReal ((SpatialSource.ofBall μ g ρ hρ).fittingError Pm.spatial) ≤
      ∫⁻ z in Metric.ball g ρ, modelCost (T := .horizontal) Pm z ∂μ := by
    rw [← gm2_lintegral_residual μ g hρ Pm.spatial]
    exact lintegral_mono fun z => gm2_spatial_le_cost_horizontal Pm z
  have hE := gm2_minimumError_le (SpatialSource.ofBall μ g ρ hρ) hkn Pm.spatial rfl
  have hL := gm2_lowerPlane (SpatialSource.ofBall μ g ρ hρ) hk1 hkn hsmall hE
  refine ⟨(SpatialSource.ofBall μ g ρ hρ).topPlane (k - 1) (by omega), Pm.time, ?_⟩
  refine gm2_collapse_calc μ g hρ _ _ (fun z => modelCost (T := .horizontal) Pm z) ?_ hL hfitP
  intro z
  set L := (SpatialSource.ofBall μ g ρ hρ).topPlane (k - 1) (by omega)
  have hmem : point (L.projection z.1) Pm.time ∈ NeckType.horizontal.collapseModelSet L Pm.time := by
    show _ ∧ _
    exact ⟨L.projection_mem _, rfl⟩
  refine (gm2_infEDist_sq_le _ z _ _ hmem).trans ?_
  gcongr _ + ?_
  exact gm2_time_le_cost_horizontal Pm z

/-- The vertical case (`d = k - 2`, lower model `L × ℝ`). -/
theorem gm2_lowerModel_vertical {n k : ℕ} (hd1 : 1 ≤ k - 2) (hkn : k ≤ n + 2)
    (μ : Measure (Space n)) [IsFiniteMeasure μ] (g : Space n) {ρ : ℝ} (hρ : 0 < ρ) (a : ℝ)
    (hsmall : (SpatialSource.ofBall μ g ρ hρ).rankEigenvalue (k - 2) < a * ρ ^ (k + 2))
    (Pm : VerticalModel n k) :
    ∃ (L : AffineSpatialPlane n (k - 2 - 1)) (τ : ℝ),
      ∫⁻ z in Metric.ball g ρ,
          Metric.infEDist z (NeckType.vertical.collapseModelSet L τ) ^ 2 ∂μ ≤
        ENNReal.ofReal (a * ρ ^ (k + 2)) + 2 * fit (T := .vertical) μ Pm g ρ := by
  have hdn : k - 2 ≤ n := by omega
  have hfitP : ENNReal.ofReal ((SpatialSource.ofBall μ g ρ hρ).fittingError Pm.spatial) ≤
      ∫⁻ z in Metric.ball g ρ, modelCost (T := .vertical) Pm z ∂μ := by
    rw [← gm2_lintegral_residual μ g hρ Pm.spatial]
    exact lintegral_mono fun z => gm2_spatial_le_cost_vertical Pm z
  have hE := gm2_minimumError_le (SpatialSource.ofBall μ g ρ hρ) hdn Pm.spatial
    (by have := Pm.rank_eq; omega)
  have hL := gm2_lowerPlane (SpatialSource.ofBall μ g ρ hρ) hd1 hdn hsmall hE
  refine ⟨(SpatialSource.ofBall μ g ρ hρ).topPlane (k - 2 - 1) (by omega), 0, ?_⟩
  refine gm2_collapse_calc μ g hρ _ _ (fun z => modelCost (T := .vertical) Pm z) ?_ hL hfitP
  intro z
  set L := (SpatialSource.ofBall μ g ρ hρ).topPlane (k - 2 - 1) (by omega)
  have hmem : point (L.projection z.1) z.2.val ∈ NeckType.vertical.collapseModelSet L 0 := by
    show _ ∈ L.toSet
    exact L.projection_mem _
  refine (gm2_infEDist_sq_le _ z _ _ hmem).trans ?_
  rw [sub_self, abs_zero, ENNReal.ofReal_zero, add_zero]
  exact le_self_add

/-- **The covariance identity at a failed continuation test.** The type of
`ChargeCollapse.collapsed_lowerModel_error`. -/
theorem collapsed_lowerModel_error_proof {n k : ℕ} {T : NeckType} (hT : T.Available n k)
    (hrank : 1 ≤ T.rank k) (μ : Measure (Space n)) [IsFiniteMeasure μ] (g : Space n)
    {ρ : ℝ} (hρ : 0 < ρ) (a : ℝ)
    (hsmall : (SpatialSource.ofBall μ g ρ hρ).rankEigenvalue (T.rank k) < a * ρ ^ (k + 2))
    (Pm : Models n k T.toFamilyKind) :
    ∃ (L : AffineSpatialPlane n (T.rank k - 1)) (τ : ℝ),
      ∫⁻ z in Metric.ball g ρ, Metric.infEDist z (T.collapseModelSet L τ) ^ 2 ∂μ ≤
        ENNReal.ofReal (a * ρ ^ (k + 2)) + 2 * fit μ Pm g ρ := by
  cases T with
  | horizontal =>
    obtain ⟨_, hkn⟩ := hT
    exact gm2_lowerModel_horizontal hrank hkn μ g hρ a hsmall Pm
  | vertical =>
    obtain ⟨_, hkn⟩ := hT
    exact gm2_lowerModel_vertical hrank hkn μ g hρ a hsmall Pm

end ChargeCollapse

end ParabolicRectifiability
