import ParabolicRectifiability.Geometry.Chart.Construction
import ParabolicRectifiability.Geometry.PartitionHessianAdapter

/-!
# Recurrence estimates and finite metric estimates for the coherent chart

Two auxiliary statements used in the proof of `vertical_coherent_chart`, named
`recurrences_proof` and `finite_metric_proof`. The induction estimates
(`induction_estimates_proof`) enter as the hypothesis `hA4`.

* `recurrences_proof` (speed, curvature and time recurrences). The actual first
  and second Fréchet derivatives and the time derivative of the recursion
  `F_{j+1} = σ_j(F_j, t)` satisfy
  `D_u F_{j+1} = D_x σ_j ∘ D_u F_j`,
  `D_u² F_{j+1}[v,w] = D_xσ_j D_u²F_j[v,w] + D_x²σ_j[D_uF_j v, D_uF_j w]` and
  `∂_t F_{j+1} = D_xσ_j ∂_tF_j + ∂_tσ_j`.
  The one-step bounds are `CoherentProjection.one_step` and
  `CoherentProjection.hessian_norm_le`, applied to the actual partition weights through
  `PartitionAdapter` and `PartitionHessianAdapter`. The induction estimates supply the active
  projection and height bounds, with two separate maxima `α + H ≤ A h⁻¹ e_j(q_j) ≤ ε`.
  The speed bound uses the path square sum through `log(1 + s) ≤ s` and
  `log(1 - s) ≥ -2s`; for `E < 0` the path bound means zero path energy, and the proof
  uses `max E 0`. Curvature and time speed both satisfy
  `Z_{j+1} ≤ (1 + C₂ε) Z_j + C₂ε/r_j`, and `h(1 + C₂ε) ≤ 1/2` gives `r_j Z_j ≤ C_a ε`.
* `finite_metric_proof` (time modulus and global noncollapse), from the recurrences and the
  displacement clause of the induction estimates. For a separation `b` (spatial `|u - v|` or temporal
  `√|t - s|`) the comparison stage `J` has `r_{J+1} < b ≤ r_J`: at stage `J` the scale-free
  bounds of the recurrences (Taylor comparison with `‖D_u²F_J‖ ≤ C_a ε/r_J`, or the time speed
  `C_a ε/r_J`) cost at most `C_a ε b`, and the displacement tails after `J` cost at most
  `2ε r_J/(1-h) ≤ 2ε b/(h(1-h))`. For `b > r_0` the isometric initial chart and the total
  displacement are used. This is global noncollapse across transition regions, not
  derivative injectivity alone. The margins use `C_a ≥ 16` and `1.2 C_a ε/h ≤ 0.01`
  (so `C_a ε ≤ 1/1200`, `ε ≤ 1/19200`); the bi-Lipschitz bounds then follow from
  `C_t ε ≤ 0.09`.
-/

noncomputable section

namespace ParabolicRectifiability

namespace CoherentChart

open scoped ENNReal ContDiff

variable {n m : ℕ} {ι : Type*}

namespace HardLeaves2

open CoherentProjection

/-! ## Elementary facts -/

theorem real_le_of_sq_le_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith

/-- `log(1 - s) ≥ -2s` on `[0, 1/2]`, in exponential form. -/
theorem exp_neg_two_mul_le_one_sub {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1 / 2) :
    Real.exp (-2 * a) ≤ 1 - a := by
  have hE := Real.exp_pos (-2 * a)
  have hadd := Real.add_one_le_exp (2 * a)
  have hmul : Real.exp (-2 * a) * Real.exp (2 * a) = 1 := by
    rw [← Real.exp_add, show -2 * a + 2 * a = 0 by ring, Real.exp_zero]
  have hle : Real.exp (-2 * a) * (2 * a + 1) ≤ 1 :=
    calc Real.exp (-2 * a) * (2 * a + 1) ≤ Real.exp (-2 * a) * Real.exp (2 * a) :=
          mul_le_mul_of_nonneg_left hadd hE.le
      _ = 1 := hmul
  have h2 : 0 < 2 * a + 1 := by linarith
  nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - 2 * a)]

/-- Two quantities bounded jointly at all pairs of indices satisfying `p` are bounded by two
separate maxima with the same total. -/
theorem exists_split_le {β : Type*} (I : Finset β) (p : β → Prop) (f g : β → ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ a, 0 ≤ f a) (hg : ∀ b, 0 ≤ g b)
    (h : ∀ a ∈ I, ∀ b ∈ I, p a → p b → f a + g b ≤ K) :
    ∃ α H : ℝ, 0 ≤ α ∧ 0 ≤ H ∧ α + H ≤ K ∧ (∀ a ∈ I, p a → f a ≤ α) ∧
      (∀ b ∈ I, p b → g b ≤ H) := by
  classical
  by_cases hS : (I.filter p).Nonempty
  · obtain ⟨a₀, ha₀, hmax⟩ := (I.filter p).exists_max_image f hS
    obtain ⟨b₀, hb₀, hmax'⟩ := (I.filter p).exists_max_image g hS
    rw [Finset.mem_filter] at ha₀ hb₀
    exact ⟨f a₀, g b₀, hf a₀, hg b₀, h a₀ ha₀.1 b₀ hb₀.1 ha₀.2 hb₀.2,
      fun a ha hpa => hmax a (Finset.mem_filter.mpr ⟨ha, hpa⟩),
      fun b hb hpb => hmax' b (Finset.mem_filter.mpr ⟨hb, hpb⟩)⟩
  · refine ⟨0, 0, le_rfl, le_rfl, by rwa [add_zero], fun a ha hpa => ?_, fun b hb hpb => ?_⟩
    · exact absurd ⟨a, Finset.mem_filter.mpr ⟨ha, hpa⟩⟩ hS
    · exact absurd ⟨b, Finset.mem_filter.mpr ⟨hb, hpb⟩⟩ hS

/-- The affine residual is at most the distance to the plane. -/
theorem norm_projection_sub_le_infDist {k : ℕ} (L : AffineSpatialPlane n k) (x : Spatial n) :
    ‖L.projection x - x‖ ≤ Metric.infDist x L.toSet := by
  rw [Metric.le_infDist L.nonempty]
  intro y hy
  rw [norm_sub_rev, dist_eq_norm]
  exact L.nearest x hy

theorem chartC₀_le_chartC₂ {σ : ℝ} (hσ : 0 < σ) : chartC₀ n σ ≤ chartC₂ n σ := by
  have h0 := one_le_chartC₀ n hσ
  unfold chartC₂ chartC₁
  nlinarith [sq_nonneg (chartC₀ n σ)]

/-- The common step of the curvature and time recurrences:
`(1 + C₂ε) C_a ε/r + C₂ε/r ≤ C_a ε/(h r)`, from `h(1 + C₂ε) ≤ 1/2` and `C_a = 2hC₂`. -/
theorem step_arith {σ : ℝ} (hσ : 0 < σ) {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 < r)
    (hcon : ratio * (1 + chartC₂ n σ * ε) ≤ 1 / 2) :
    (1 + chartC₂ n σ * ε) * (chartCa n σ * ε / r) + chartC₂ n σ * ε / r ≤
      chartCa n σ * ε / (ratio * r) := by
  have hc2 : 0 ≤ chartC₂ n σ := (chartConsts_bounds (n := n) hσ).2.2.1
  have hc : 0 ≤ chartC₂ n σ * ε := mul_nonneg hc2 hε
  have hq : chartCa n σ * ε / ratio = 2 * (chartC₂ n σ * ε) := by unfold chartCa ratio; ring
  have hca : chartCa n σ * ε = 1 / 5 * (chartC₂ n σ * ε) := by unfold chartCa ratio; ring
  have key : (1 + chartC₂ n σ * ε) * (chartCa n σ * ε) + chartC₂ n σ * ε ≤
      chartCa n σ * ε / ratio := by
    rw [hq, hca]
    have hm := mul_le_mul_of_nonneg_left hcon hc
    unfold ratio at hm
    nlinarith
  calc (1 + chartC₂ n σ * ε) * (chartCa n σ * ε / r) + chartC₂ n σ * ε / r
      = ((1 + chartC₂ n σ * ε) * (chartCa n σ * ε) + chartC₂ n σ * ε) / r := by ring
    _ ≤ chartCa n σ * ε / ratio / r := div_le_div_of_nonneg_right key hr.le
    _ = chartCa n σ * ε / (ratio * r) := by rw [div_div]

/-! ## The local comparison coefficient along a path -/

/-- Line 1523: under finite coherence, `e_j ≤ δ` for `j ≤ N` (the pairs in `e_j` are
within `16 r_{j-1} ≤ 20 r_{j-1}`). -/
theorem localError_le_ofReal {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ}
    (hF : F.IsCoherentUpTo σ δ N) {j : ℕ} (hj : j ≤ N) (q : Space n) :
    localError F j q ≤ ENNReal.ofReal δ := by
  cases j with
  | zero =>
    simp only [localError]
    refine iSup_le fun _ => iSup₂_le fun a ha => iSup_le fun _ => ?_
    exact ENNReal.ofReal_le_ofReal (hF.root a ha)
  | succ j =>
    have hr := scale_pos F j
    simp only [localError]
    refine iSup_le fun _ => max_le ?_ ?_
    · refine iSup₂_le fun a ha => iSup₂_le fun b hb => iSup_le fun h => ?_
      refine ENNReal.ofReal_le_ofReal (hF.same j (by omega) a ha b hb ?_)
      calc dist (F.center j a) (F.center j b)
          ≤ dist (F.center j a) q + dist (F.center j b) q := dist_triangle_right _ _ _
        _ ≤ 8 * F.scale j + 8 * F.scale j := add_le_add h.1 h.2
        _ ≤ 20 * F.scale j := by linarith
    · refine iSup₂_le fun a ha => iSup₂_le fun b hb => iSup_le fun h => ?_
      refine ENNReal.ofReal_le_ofReal (hF.adjacent j (by omega) a ha b hb ?_)
      calc dist (F.center (j + 1) a) (F.center j b)
          ≤ dist (F.center (j + 1) a) q + dist (F.center j b) q := dist_triangle_right _ _ _
        _ ≤ 8 * F.scale j + 8 * F.scale j := add_le_add h.1 h.2
        _ ≤ 20 * F.scale j := by linarith

/-- The real value `e_j(q_j)` of the local comparison coefficient at the path point. -/
def pathCoeff (F : CoherentFamily n m ι) (P : InitialChart F) (j : ℕ) (u : Spatial m)
    (t : ℝ) : ℝ :=
  (localError F j (pathPoint F P j u t)).toReal

section PathCoeff

variable {F : CoherentFamily n m ι} {P : InitialChart F} {σ δ E : ℝ} {N : ℕ}

theorem pathCoeff_nonneg (j : ℕ) (u : Spatial m) (t : ℝ) : 0 ≤ pathCoeff F P j u t :=
  ENNReal.toReal_nonneg

theorem ofReal_pathCoeff (hF : F.IsCoherentUpTo σ δ N) {j : ℕ} (hj : j ≤ N) (u : Spatial m)
    (t : ℝ) : ENNReal.ofReal (pathCoeff F P j u t) = localError F j (pathPoint F P j u t) :=
  ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (localError_le_ofReal hF hj _))

theorem pathCoeff_le (hδ : 0 ≤ δ) (hF : F.IsCoherentUpTo σ δ N) {j : ℕ} (hj : j ≤ N)
    (u : Spatial m) (t : ℝ) : pathCoeff F P j u t ≤ δ :=
  ENNReal.toReal_le_of_le_ofReal hδ (localError_le_ofReal hF hj _)

/-- The path bound in real form; for `E < 0` it means zero path energy. -/
theorem sum_sq_pathCoeff_le (hF : F.IsCoherentUpTo σ δ N) (hpath : PathBoundUpTo F P E N)
    (u : Spatial m) (t : ℝ) :
    ∑ i ∈ Finset.range (N + 1), pathCoeff F P i u t ^ 2 ≤ max E 0 := by
  have h := hpath u t
  unfold pathSquareSum at h
  have hsum : ∑ i ∈ Finset.range (N + 1), localError F i (pathPoint F P i u t) ^ 2 =
      ENNReal.ofReal (∑ i ∈ Finset.range (N + 1), pathCoeff F P i u t ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [ENNReal.ofReal_pow (pathCoeff_nonneg i u t), ofReal_pathCoeff hF hi']
  rw [hsum, ENNReal.ofReal_le_ofReal_iff'] at h
  rcases h with h | h
  · exact h.trans (le_max_left _ _)
  · exact h.trans (le_max_right _ _)

end PathCoeff

/-- The second conclusion of the induction estimates (tangent and height bounds for two independent active indices),
for one family and one initial parametrization. -/
def ActiveBound (F : CoherentFamily n m ι) (P : InitialChart F) (σ : ℝ) (N : ℕ) : Prop :=
  ∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ), ∀ a ∈ F.index j, ∀ b ∈ F.index j,
    IsActive F j a (stage F P j u t) t → IsActive F j b (stage F P j u t) t →
      ENNReal.ofReal (‖(tangent F P j u t).starProjection - (F.plane j a).linearProjection‖ +
          (F.scale j)⁻¹ * Metric.infDist (stage F P j u t) (F.plane j b).toSet) ≤
        ENNReal.ofReal (chartA n σ / ratio) * localError F j (pathPoint F P j u t)

/-- **The one-step data at a path point.** From the induction estimates, the separate maxima `α` (tangent
discrepancy) and `H` (height) over the active indices satisfy `α + H ≤ A h⁻¹ e_j ≤ ε`, and
they are the geometric inputs `hc`, `he` of `one_step` and `hessian_norm_le`. -/
theorem exists_alpha_height {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ} {P : InitialChart F}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hF : F.IsCoherentUpTo σ δ N) (hact : ActiveBound F P σ N)
    {j : ℕ} (hj : j ≤ N) (u : Spatial m) (t : ℝ) :
    ∃ α H : ℝ, 0 ≤ α ∧ 0 ≤ H ∧ α + H ≤ chartA n σ / ratio * pathCoeff F P j u t ∧
      α + H ≤ chartEps n σ δ ∧
      (∀ a ∈ F.index j, IsActive F j a (stage F P j u t) t →
        ‖(F.plane j a).projection (stage F P j u t) - stage F P j u t‖ ≤ H * F.scale j) ∧
      (∀ a ∈ F.index j, IsActive F j a (stage F P j u t) t →
        ‖(tangent F P j u t).starProjection - (F.plane j a).linearProjection‖ ≤ α) := by
  have hr := scale_pos F j
  have hA : 0 ≤ chartA n σ := le_trans (by norm_num) (chartConsts_bounds (n := n) hσ).2.2.2.2.2.2.2
  have hAh : 0 ≤ chartA n σ / ratio := div_nonneg hA ratio_pos.le
  have hK : 0 ≤ chartA n σ / ratio * pathCoeff F P j u t :=
    mul_nonneg hAh (pathCoeff_nonneg j u t)
  obtain ⟨α, H, hα, hH, hsum, hfa, hgb⟩ := exists_split_le (F.index j)
    (fun a => IsActive F j a (stage F P j u t) t)
    (fun a => ‖(tangent F P j u t).starProjection - (F.plane j a).linearProjection‖)
    (fun b => (F.scale j)⁻¹ * Metric.infDist (stage F P j u t) (F.plane j b).toSet) hK
    (fun a => norm_nonneg _) (fun b => mul_nonneg (inv_nonneg.mpr hr.le) Metric.infDist_nonneg)
    (by
      intro a ha b hb hpa hpb
      have h := hact j hj u t a ha b hb hpa hpb
      rw [← ofReal_pathCoeff hF hj, ← ENNReal.ofReal_mul hAh, ENNReal.ofReal_le_ofReal_iff hK] at h
      exact h)
  refine ⟨α, H, hα, hH, hsum, ?_, fun a ha hpa => ?_, hfa⟩
  · calc α + H ≤ chartA n σ / ratio * pathCoeff F P j u t := hsum
      _ ≤ chartA n σ / ratio * δ := mul_le_mul_of_nonneg_left (pathCoeff_le hδ hF hj u t) hAh
      _ = chartEps n σ δ := by unfold chartEps; ring
  · have h1 := hgb a ha hpa
    have h2 : Metric.infDist (stage F P j u t) (F.plane j a).toSet ≤ H * F.scale j := by
      rw [inv_mul_le_iff₀ hr] at h1
      linarith
    exact (norm_projection_sub_le_infDist _ _).trans h2

/-- **The one-step bounds at a level `j ≤ N`** (`CoherentProjection.one_step` and `CoherentProjection.hessian_norm_le` for the actual weights): the
spatial derivative bound `1 + C₀H`, the time derivative bound `C₀H/r_j`, the quadratic
distortion on the tangent space and the Hessian bound on the tangent space. -/
theorem level_bounds {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ} (hσ : 0 < σ)
    (hF : F.IsCoherentUpTo σ δ N) {j : ℕ} (hj : j ≤ N) (x : Spatial n) (t : ℝ)
    (T : Submodule ℝ (Spatial n)) (α H : ℝ) (hα : 0 ≤ α) (hH : 0 ≤ H)
    (he : ∀ a ∈ F.index j, IsActive F j a x t →
      ‖(F.plane j a).projection x - x‖ ≤ H * F.scale j)
    (hc : ∀ a ∈ F.index j, IsActive F j a x t →
      ‖T.starProjection - (F.plane j a).linearProjection‖ ≤ α) :
    ‖fderiv ℝ (fun y => stageMap F j y t) x‖ ≤ 1 + chartC₀ n σ * H ∧
    ‖deriv (fun s => stageMap F j x s) t‖ ≤ chartC₀ n σ * H / F.scale j ∧
    (∀ v ∈ T, |‖fderiv ℝ (fun y => stageMap F j y t) x v‖ ^ 2 - ‖v‖ ^ 2| ≤
      chartC₁ n σ * (α ^ 2 + H ^ 2) * ‖v‖ ^ 2) ∧
    (∀ v ∈ T, ∀ w ∈ T, ‖fderiv ℝ (fderiv ℝ (fun y => stageMap F j y t)) x v w‖ ≤
      chartC₁ n σ * (α + H) / F.scale j * ‖v‖ * ‖w‖) := by
  have hdisj : (F.index j : Set ι).PairwiseDisjoint
      (fun a => Metric.ball (F.center j a) (σ * F.scale j / 3)) := by
    intro a ha b hb hab
    have hsep := hF.separated j hj a ha b hb hab
    have hpos : 0 < σ * F.scale j := mul_pos hσ (scale_pos F j)
    exact Metric.ball_disjoint_ball (by linarith)
  have hr := scale_pos F j
  obtain ⟨-, h1, h2, h3⟩ := one_step_parabolicWeight hσ hr (F.index j) (F.center j) hdisj
    (F.plane j) x t H α hH hα he T hc
  exact ⟨h1, h2, h3, fun v hv w hw => hessian_norm_le_parabolicWeight hσ hr (F.index j)
    (F.center j) hdisj (F.plane j) x t H α hH hα he T hc v w hv hw⟩

/-! ## Smoothness and the chain rules for the recursion -/

theorem smooth_differentiable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G} (h : ContDiff ℝ ∞ f) :
    Differentiable ℝ f :=
  h.differentiable (by simp)

theorem smooth_differentiable_fderiv {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G} (h : ContDiff ℝ ∞ f) :
    Differentiable ℝ (fderiv ℝ f) :=
  ((h.of_le (m := 2) (by simp)).fderiv_right (m := 1) (by norm_num)).differentiable_one

section Chain

variable (F : CoherentFamily n m ι) (P : InitialChart F)

/-- The stage map is jointly smooth in `(x, t)`. -/
theorem contDiff_stageMap_uncurry (j : ℕ) :
    ContDiff ℝ ∞ (fun p : Spatial n × ℝ => stageMap F j p.1 p.2) := by
  unfold stageMap CoherentProjection.sigma
  refine contDiff_fst.add (ContDiff.sum fun a _ => ?_)
  refine (contDiff_weight F j a).smul ?_
  unfold AffineSpatialPlane.projection
  exact (contDiff_const.add ((F.plane j a).linearProjection.contDiff.comp contDiff_fst)).sub
    contDiff_fst

theorem contDiff_stageMap_left (j : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (fun x : Spatial n => stageMap F j x t) :=
  (contDiff_stageMap_uncurry F j).comp (contDiff_id.prodMk contDiff_const)

theorem contDiff_stage_left (j : ℕ) (t : ℝ) : ContDiff ℝ ∞ (fun w : Spatial m => stage F P j w t) :=
  (contDiff_stage F P j).comp (contDiff_id.prodMk contDiff_const)

theorem contDiff_stage_right (j : ℕ) (u : Spatial m) : ContDiff ℝ ∞ (fun s : ℝ => stage F P j u s) :=
  (contDiff_stage F P j).comp (contDiff_const.prodMk contDiff_id)

theorem fderiv_stage_zero (u : Spatial m) (t : ℝ) :
    fderiv ℝ (fun w => stage F P 0 w t) u = P.isometry.toContinuousLinearMap := by
  have h : HasFDerivAt (fun w => P.origin + P.isometry.toContinuousLinearMap w)
      P.isometry.toContinuousLinearMap u :=
    P.isometry.toContinuousLinearMap.hasFDerivAt.const_add P.origin
  exact h.fderiv

theorem fderiv_fderiv_stage_zero (u : Spatial m) (t : ℝ) :
    fderiv ℝ (fun y => fderiv ℝ (fun w => stage F P 0 w t) y) u = 0 := by
  have h : (fun y => fderiv ℝ (fun w => stage F P 0 w t) y) =
      fun _ => P.isometry.toContinuousLinearMap :=
    funext fun y => fderiv_stage_zero F P y t
  rw [h]
  exact fderiv_const_apply _

theorem deriv_stage_zero (u : Spatial m) (t : ℝ) :
    deriv (fun s => stage F P 0 u s) t = 0 := by
  show deriv (fun _ => P.origin + P.isometry u) t = 0
  exact deriv_const _ _

/-- First chain rule: `D_u F_{j+1} = D_x σ_j(F_j) ∘ D_u F_j`. -/
theorem fderiv_stage_succ (j : ℕ) (u : Spatial m) (t : ℝ) :
    fderiv ℝ (fun w => stage F P (j + 1) w t) u =
      (fderiv ℝ (fun x => stageMap F j x t) (stage F P j u t)).comp
        (fderiv ℝ (fun w => stage F P j w t) u) :=
  (((smooth_differentiable (contDiff_stageMap_left F j t)) _).hasFDerivAt.comp u
    ((smooth_differentiable (contDiff_stage_left F P j t)) u).hasFDerivAt).fderiv

/-- Second chain rule:
`D_u² F_{j+1}[v,w] = D_xσ_j D_u²F_j[v,w] + D_x²σ_j[D_uF_j v, D_uF_j w]`. -/
theorem fderiv_fderiv_stage_succ_apply (j : ℕ) (u : Spatial m) (t : ℝ) (v w : Spatial m) :
    fderiv ℝ (fun y => fderiv ℝ (fun w => stage F P (j + 1) w t) y) u v w =
      fderiv ℝ (fun x => stageMap F j x t) (stage F P j u t)
          (fderiv ℝ (fun y => fderiv ℝ (fun w => stage F P j w t) y) u v w) +
        fderiv ℝ (fderiv ℝ (fun x => stageMap F j x t)) (stage F P j u t)
          (fderiv ℝ (fun w => stage F P j w t) u v) (fderiv ℝ (fun w => stage F P j w t) u w) := by
  have hs := contDiff_stageMap_left F j t
  have hg := contDiff_stage_left F P j t
  have h1 : (fun y => fderiv ℝ (fun w => stage F P (j + 1) w t) y) =
      fun y => (fderiv ℝ (fun x => stageMap F j x t) (stage F P j y t)).comp
        (fderiv ℝ (fun w => stage F P j w t) y) :=
    funext fun y => fderiv_stage_succ F P j y t
  have hc : HasFDerivAt (fun y => fderiv ℝ (fun x => stageMap F j x t) (stage F P j y t))
      ((fderiv ℝ (fderiv ℝ (fun x => stageMap F j x t)) (stage F P j u t)).comp
        (fderiv ℝ (fun w => stage F P j w t) u)) u :=
    ((smooth_differentiable_fderiv hs) _).hasFDerivAt.comp u
      ((smooth_differentiable hg) u).hasFDerivAt
  have hd : HasFDerivAt (fun y => fderiv ℝ (fun w => stage F P j w t) y)
      (fderiv ℝ (fun y => fderiv ℝ (fun w => stage F P j w t) y) u) u :=
    ((smooth_differentiable_fderiv hg) u).hasFDerivAt
  rw [h1, (hc.clm_comp hd).fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]

/-- Time chain rule: `∂_t F_{j+1} = D_xσ_j(F_j) ∂_t F_j + ∂_t σ_j(F_j)`. -/
theorem deriv_stage_succ (j : ℕ) (u : Spatial m) (t : ℝ) :
    deriv (fun s => stage F P (j + 1) u s) t =
      fderiv ℝ (fun x => stageMap F j x t) (stage F P j u t)
          (deriv (fun s => stage F P j u s) t) +
        deriv (fun s => stageMap F j (stage F P j u t) s) t := by
  obtain ⟨D, hD⟩ : ∃ D, HasFDerivAt (fun p : Spatial n × ℝ => stageMap F j p.1 p.2) D
      (stage F P j u t, t) :=
    ⟨_, ((smooth_differentiable (contDiff_stageMap_uncurry F j)) _).hasFDerivAt⟩
  have hl : HasFDerivAt (fun e : Spatial n => (e, t)) (ContinuousLinearMap.inl ℝ (Spatial n) ℝ)
      (stage F P j u t) :=
    hasFDerivAt_prodMk_left _ _
  have hx' := hD.comp (stage F P j u t) hl
  have hx : fderiv ℝ (fun x => stageMap F j x t) (stage F P j u t) =
      D.comp (ContinuousLinearMap.inl ℝ (Spatial n) ℝ) := hx'.fderiv
  have ht : deriv (fun s => stageMap F j (stage F P j u t) s) t = D ((0 : Spatial n), (1 : ℝ)) :=
    (hD.comp_hasDerivAt t
      ((hasDerivAt_const _ _ : HasDerivAt (fun _ : ℝ => stage F P j u t) 0 t).prodMk
        (hasDerivAt_id t))).deriv
  have hτ : HasDerivAt (fun s => stage F P j u s) (deriv (fun s => stage F P j u s) t) t :=
    ((smooth_differentiable (contDiff_stage_right F P j u)) t).hasDerivAt
  have hγ : HasDerivAt (fun s => (stage F P j u s, s))
      (deriv (fun s => stage F P j u s) t, (1 : ℝ)) t :=
    hτ.prodMk (hasDerivAt_id' t)
  have hfull : deriv (fun s => stage F P (j + 1) u s) t =
      D (deriv (fun s => stage F P j u s) t, (1 : ℝ)) :=
    (HasFDerivAt.comp_hasDerivAt (f := fun s => (stage F P j u s, s)) t hD hγ).deriv
  have hsplit : ((deriv (fun s => stage F P j u s) t, (1 : ℝ)) : Spatial n × ℝ) =
      (deriv (fun s => stage F P j u s) t, 0) + (0, 1) := by simp
  rw [hfull, hsplit, map_add, hx, ht, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply]

end Chain

/-! ## The speed recurrence -/

/-- The partial sums `S_j = ∑_{i<j} C₁ (A h⁻¹ e_i)²` along the path through `(u, t)`. -/
def speedSum (F : CoherentFamily n m ι) (P : InitialChart F) (σ : ℝ) (j : ℕ) (u : Spatial m)
    (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range j, chartC₁ n σ * (chartA n σ / ratio * pathCoeff F P i u t) ^ 2

section Recurrences

variable {F : CoherentFamily n m ι} {P : InitialChart F} {σ δ E : ℝ} {N : ℕ}

/-- `e^{-2S_j}|v|² ≤ |D_uF_j v|² ≤ e^{S_j}|v|²`, by the quadratic distortion on the actual
tangent space and `1 + s ≤ e^s`, `1 - s ≥ e^{-2s}` for `0 ≤ s ≤ 1/2`. -/
theorem speed_exp (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
    (hF : F.IsCoherentUpTo σ δ N) (hact : ActiveBound F P σ N) :
    ∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ) (v : Spatial m),
      Real.exp (-2 * speedSum F P σ j u t) * ‖v‖ ^ 2 ≤
          ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ^ 2 ∧
        ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ^ 2 ≤
          Real.exp (speedSum F P σ j u t) * ‖v‖ ^ 2 := by
  have hC1 : 0 ≤ chartC₁ n σ := (chartConsts_bounds (n := n) hσ).2.1
  have hA : 0 ≤ chartA n σ := le_trans (by norm_num) (chartConsts_bounds (n := n) hσ).2.2.2.2.2.2.2
  have hAh : 0 ≤ chartA n σ / ratio := div_nonneg hA ratio_pos.le
  intro j
  induction j with
  | zero =>
    intro _ u t v
    rw [fderiv_stage_zero]
    simp [speedSum]
  | succ j ih =>
    intro hj u t v
    have hjN : j ≤ N := by omega
    obtain ⟨hlo, hhi⟩ := ih (by omega) u t v
    obtain ⟨α, H, hα, hH, hsum, hsumε, he, hc⟩ := exists_alpha_height hσ hδ hF hact hjN u t
    obtain ⟨-, -, hquad, -⟩ := level_bounds hσ hF hjN (stage F P j u t) t
      (tangent F P j u t) α H hα hH he hc
    have hwT : fderiv ℝ (fun w => stage F P j w t) u v ∈ tangent F P j u t :=
      LinearMap.mem_range_self _ v
    have hq := hquad _ hwT
    -- the step coefficient `a_j = C₁ (A h⁻¹ e_j)²`
    have he0 := pathCoeff_nonneg (F := F) (P := P) j u t
    have hk0 : 0 ≤ chartA n σ / ratio * pathCoeff F P j u t := mul_nonneg hAh he0
    have hkε : chartA n σ / ratio * pathCoeff F P j u t ≤ chartEps n σ δ := by
      calc chartA n σ / ratio * pathCoeff F P j u t ≤ chartA n σ / ratio * δ :=
            mul_le_mul_of_nonneg_left (pathCoeff_le hδ hF hjN u t) hAh
        _ = chartEps n σ δ := by unfold chartEps; ring
    have hqa : chartC₁ n σ * (α ^ 2 + H ^ 2) ≤
        chartC₁ n σ * (chartA n σ / ratio * pathCoeff F P j u t) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hC1
      have h1 : α ^ 2 + H ^ 2 ≤ (α + H) ^ 2 := by nlinarith [mul_nonneg hα hH]
      exact h1.trans (pow_le_pow_left₀ (add_nonneg hα hH) hsum 2)
    have ha0 : 0 ≤ chartC₁ n σ * (chartA n σ / ratio * pathCoeff F P j u t) ^ 2 :=
      mul_nonneg hC1 (sq_nonneg _)
    have ha_half : chartC₁ n σ * (chartA n σ / ratio * pathCoeff F P j u t) ^ 2 ≤ 1 / 2 :=
      calc chartC₁ n σ * (chartA n σ / ratio * pathCoeff F P j u t) ^ 2
          ≤ chartC₁ n σ * chartEps n σ δ ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk0 hkε 2) hC1
        _ ≤ 1 / 2 := hsmall.quadratic
    have hS : speedSum F P σ (j + 1) u t =
        speedSum F P σ j u t + chartC₁ n σ * (chartA n σ / ratio * pathCoeff F P j u t) ^ 2 :=
      Finset.sum_range_succ _ _
    rw [fderiv_stage_succ, ContinuousLinearMap.comp_apply, hS]
    have hw2 := sq_nonneg ‖fderiv ℝ (fun w => stage F P j w t) u v‖
    have hqa' := mul_le_mul_of_nonneg_right hqa hw2
    obtain ⟨hq1, hq2⟩ := abs_le.mp hq
    constructor
    · have hlo1 := exp_neg_two_mul_le_one_sub ha0 ha_half
      have hprod := mul_le_mul hlo1 hlo (by positivity) (by linarith)
      rw [show -2 * (speedSum F P σ j u t +
          chartC₁ n σ * (chartA n σ / ratio * pathCoeff F P j u t) ^ 2) =
          -2 * (chartC₁ n σ * (chartA n σ / ratio * pathCoeff F P j u t) ^ 2) +
            -2 * speedSum F P σ j u t by ring, Real.exp_add]
      linarith
    · have hup1 := Real.add_one_le_exp
        (chartC₁ n σ * (chartA n σ / ratio * pathCoeff F P j u t) ^ 2)
      have hprod := mul_le_mul (show 1 + chartC₁ n σ *
          (chartA n σ / ratio * pathCoeff F P j u t) ^ 2 ≤
          Real.exp (chartC₁ n σ * (chartA n σ / ratio * pathCoeff F P j u t) ^ 2) by linarith)
        hhi hw2 (Real.exp_pos _).le
      rw [Real.exp_add]
      linarith

/-- The path square sum gives `S_j ≤ C₁ A² max(E,0)/h² ≤ log(1.01)` for `j ≤ N + 1`. -/
theorem speedSum_le_log (hσ : 0 < σ) (hEsmall : EnergySmall n σ E) (hF : F.IsCoherentUpTo σ δ N)
    (hpath : PathBoundUpTo F P E N) {j : ℕ} (hj : j ≤ N + 1) (u : Spatial m) (t : ℝ) :
    speedSum F P σ j u t ≤ Real.log (101 / 100) := by
  have hC1 : 0 ≤ chartC₁ n σ := (chartConsts_bounds (n := n) hσ).2.1
  have hmono : speedSum F P σ j u t ≤ speedSum F P σ (N + 1) u t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hj)
      (fun i _ _ => mul_nonneg hC1 (sq_nonneg _))
  have heq : speedSum F P σ (N + 1) u t = chartC₁ n σ * (chartA n σ / ratio) ^ 2 *
      ∑ i ∈ Finset.range (N + 1), pathCoeff F P i u t ^ 2 := by
    unfold speedSum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hk : 0 ≤ chartC₁ n σ * (chartA n σ / ratio) ^ 2 := mul_nonneg hC1 (sq_nonneg _)
  have hS := sum_sq_pathCoeff_le hF hpath u t
  refine hmono.trans ?_
  rw [heq]
  refine (mul_le_mul_of_nonneg_left hS hk).trans ?_
  rcases le_total 0 E with hE | hE
  · rw [max_eq_left hE]
    have h := hEsmall
    unfold EnergySmall at h
    calc chartC₁ n σ * (chartA n σ / ratio) ^ 2 * E =
        chartC₁ n σ * chartA n σ ^ 2 * E / ratio ^ 2 := by ring
      _ ≤ Real.log (101 / 100) := h
  · rw [max_eq_right hE, mul_zero]
    exact Real.log_nonneg (by norm_num)

/-- **Speed bound.** `0.99|v| ≤ |D_uF_j v| ≤ 1.01|v|` for every stage `j ≤ N + 1`. -/
theorem speed_bounds (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
    (hEsmall : EnergySmall n σ E) (hF : F.IsCoherentUpTo σ δ N) (hact : ActiveBound F P σ N)
    (hpath : PathBoundUpTo F P E N) :
    ∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ) (v : Spatial m),
      99 / 100 * ‖v‖ ≤ ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ∧
        ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ≤ 101 / 100 * ‖v‖ := by
  intro j hj u t v
  have hC1 : 0 ≤ chartC₁ n σ := (chartConsts_bounds (n := n) hσ).2.1
  obtain ⟨hlo, hhi⟩ := speed_exp hσ hδ hsmall hF hact j hj u t v
  have hSL := speedSum_le_log hσ hEsmall hF hpath hj u t
  have hexpL : Real.exp (Real.log (101 / 100)) = 101 / 100 := Real.exp_log (by norm_num)
  have hup : Real.exp (speedSum F P σ j u t) ≤ 101 / 100 :=
    hexpL ▸ Real.exp_le_exp.mpr hSL
  have hlow : 9801 / 10000 ≤ Real.exp (-2 * speedSum F P σ j u t) := by
    have h1 : Real.exp (-2 * Real.log (101 / 100)) ≤ Real.exp (-2 * speedSum F P σ j u t) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-2 * Real.log (101 / 100)) *
        (Real.exp (Real.log (101 / 100)) * Real.exp (Real.log (101 / 100))) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add,
        show -2 * Real.log (101 / 100) + (Real.log (101 / 100) + Real.log (101 / 100)) = 0 by ring,
        Real.exp_zero]
    rw [hexpL] at h2
    linarith
  have hv2 := sq_nonneg ‖v‖
  have hl := mul_le_mul_of_nonneg_right hlow hv2
  have hu := mul_le_mul_of_nonneg_right hup hv2
  constructor
  · exact real_le_of_sq_le_sq (norm_nonneg _) (by linarith)
  · exact real_le_of_sq_le_sq (by positivity) (by linarith)

/-- **Curvature bound, Hessian part.** `‖D_u²F_j‖ ≤ C_a ε / r_j` for `j ≤ N + 1`. -/
theorem hessian_bounds (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
    (hEsmall : EnergySmall n σ E) (hF : F.IsCoherentUpTo σ δ N) (hact : ActiveBound F P σ N)
    (hpath : PathBoundUpTo F P E N) :
    ∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
      ‖fderiv ℝ (fun v => fderiv ℝ (fun w => stage F P j w t) v) u‖ ≤
        chartCa n σ * chartEps n σ δ / F.scale j := by
  obtain ⟨h0, hC1, hC2, -, hCa, -, -, -⟩ := chartConsts_bounds (n := n) hσ
  have hε := chartEps_nonneg (n := n) hσ hδ
  have hC02 := chartC₀_le_chartC₂ (n := n) hσ
  have hspeed := speed_bounds hσ hδ hsmall hEsmall hF hact hpath
  intro j
  induction j with
  | zero =>
    intro _ u t
    rw [fderiv_fderiv_stage_zero]
    exact (le_of_eq ContinuousLinearMap.opNorm_zero).trans
      (div_nonneg (mul_nonneg hCa hε) (scale_pos F 0).le)
  | succ j ih =>
    intro hj u t
    have hjN : j ≤ N := by omega
    have hr := scale_pos F j
    obtain ⟨α, H, hα, hH, -, hsumε, he, hc⟩ := exists_alpha_height hσ hδ hF hact hjN u t
    obtain ⟨hDs, -, -, hhess⟩ := level_bounds hσ hF hjN (stage F P j u t) t
      (tangent F P j u t) α H hα hH he hc
    have hIH := ih (by omega) u t
    have hHε : H ≤ chartEps n σ δ := by linarith
    have hDs' : ‖fderiv ℝ (fun x => stageMap F j x t) (stage F P j u t)‖ ≤
        1 + chartC₂ n σ * chartEps n σ δ :=
      hDs.trans (by linarith [mul_le_mul hC02 hHε hH hC2])
    have hcoef : chartC₁ n σ * (α + H) / F.scale j ≤ chartC₁ n σ * chartEps n σ δ / F.scale j :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsumε hC1) hr.le
    have hX : 0 ≤ chartC₁ n σ * chartEps n σ δ / F.scale j :=
      div_nonneg (mul_nonneg hC1 hε) hr.le
    have hY : 0 ≤ chartCa n σ * chartEps n σ δ / F.scale j :=
      div_nonneg (mul_nonneg hCa hε) hr.le
    have hC2eq : chartC₂ n σ * chartEps n σ δ / F.scale j =
        2 * (chartC₁ n σ * chartEps n σ δ / F.scale j) := by unfold chartC₂; ring
    have hstep := step_arith (n := n) hσ hε hr hsmall.contraction
    rw [scale_succ]
    refine ContinuousLinearMap.opNorm_le_bound₂ _
      (div_nonneg (mul_nonneg hCa hε) (mul_pos ratio_pos hr).le) fun v w => ?_
    rw [fderiv_fderiv_stage_succ_apply]
    have hv := norm_nonneg v
    have hw := norm_nonneg w
    have hvw := mul_nonneg hv hw
    -- the propagated term
    have hA1 : ‖fderiv ℝ (fun x => stageMap F j x t) (stage F P j u t)
        (fderiv ℝ (fun y => fderiv ℝ (fun w => stage F P j w t) y) u v w)‖ ≤
        (1 + chartC₂ n σ * chartEps n σ δ) *
          (chartCa n σ * chartEps n σ δ / F.scale j * ‖v‖ * ‖w‖) := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hDs' ?_ (norm_nonneg _)
        (add_nonneg zero_le_one (mul_nonneg hC2 hε)))
      refine (ContinuousLinearMap.le_opNorm₂ _ v w).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hIH hv) hw
    -- the forcing term
    have hA2 : ‖fderiv ℝ (fderiv ℝ (fun x => stageMap F j x t)) (stage F P j u t)
        (fderiv ℝ (fun w => stage F P j w t) u v) (fderiv ℝ (fun w => stage F P j w t) u w)‖ ≤
        chartC₂ n σ * chartEps n σ δ / F.scale j * ‖v‖ * ‖w‖ := by
      have h : ‖fderiv ℝ (fderiv ℝ (fun x => stageMap F j x t)) (stage F P j u t)
          (fderiv ℝ (fun w => stage F P j w t) u v) (fderiv ℝ (fun w => stage F P j w t) u w)‖ ≤
          chartC₁ n σ * (α + H) / F.scale j * ‖fderiv ℝ (fun w => stage F P j w t) u v‖ *
            ‖fderiv ℝ (fun w => stage F P j w t) u w‖ :=
        hhess _ (LinearMap.mem_range_self _ v) _ (LinearMap.mem_range_self _ w)
      obtain ⟨-, hpv⟩ := hspeed j (by omega) u t v
      obtain ⟨-, hpw⟩ := hspeed j (by omega) u t w
      have hpq : ‖fderiv ℝ (fun w => stage F P j w t) u v‖ *
          ‖fderiv ℝ (fun w => stage F P j w t) u w‖ ≤
          101 / 100 * ‖v‖ * (101 / 100 * ‖w‖) :=
        mul_le_mul hpv hpw (norm_nonneg _) (by positivity)
      have h2 : chartC₁ n σ * (α + H) / F.scale j * ‖fderiv ℝ (fun w => stage F P j w t) u v‖ *
            ‖fderiv ℝ (fun w => stage F P j w t) u w‖ ≤
          chartC₁ n σ * chartEps n σ δ / F.scale j * (101 / 100 * ‖v‖ * (101 / 100 * ‖w‖)) :=
        (mul_assoc _ _ _).trans_le (mul_le_mul hcoef hpq (by positivity) hX)
      have h3 := mul_nonneg hX hvw
      rw [hC2eq]
      linarith
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (1 + chartC₂ n σ * chartEps n σ δ) *
            (chartCa n σ * chartEps n σ δ / F.scale j * ‖v‖ * ‖w‖) +
          chartC₂ n σ * chartEps n σ δ / F.scale j * ‖v‖ * ‖w‖ := add_le_add hA1 hA2
      _ = ((1 + chartC₂ n σ * chartEps n σ δ) * (chartCa n σ * chartEps n σ δ / F.scale j) +
            chartC₂ n σ * chartEps n σ δ / F.scale j) * ‖v‖ * ‖w‖ := by ring
      _ ≤ chartCa n σ * chartEps n σ δ / (ratio * F.scale j) * ‖v‖ * ‖w‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep hv) hw

/-- **Curvature bound, time part.** `|∂_t F_j| ≤ C_a ε / r_j` for `j ≤ N + 1`. -/
theorem time_bounds (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
    (hF : F.IsCoherentUpTo σ δ N) (hact : ActiveBound F P σ N) :
    ∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
      ‖deriv (fun s => stage F P j u s) t‖ ≤ chartCa n σ * chartEps n σ δ / F.scale j := by
  obtain ⟨h0, hC1, hC2, -, hCa, -, -, -⟩ := chartConsts_bounds (n := n) hσ
  have hε := chartEps_nonneg (n := n) hσ hδ
  have hC02 := chartC₀_le_chartC₂ (n := n) hσ
  intro j
  induction j with
  | zero =>
    intro _ u t
    rw [deriv_stage_zero, norm_zero]
    exact div_nonneg (mul_nonneg hCa hε) (scale_pos F 0).le
  | succ j ih =>
    intro hj u t
    have hjN : j ≤ N := by omega
    have hr := scale_pos F j
    obtain ⟨α, H, hα, hH, -, hsumε, he, hc⟩ := exists_alpha_height hσ hδ hF hact hjN u t
    obtain ⟨hDs, hdt, -, -⟩ := level_bounds hσ hF hjN (stage F P j u t) t
      (tangent F P j u t) α H hα hH he hc
    have hIH := ih (by omega) u t
    have hHε : H ≤ chartEps n σ δ := by linarith
    have hCH : chartC₀ n σ * H ≤ chartC₂ n σ * chartEps n σ δ := mul_le_mul hC02 hHε hH hC2
    have hDs' : ‖fderiv ℝ (fun x => stageMap F j x t) (stage F P j u t)‖ ≤
        1 + chartC₂ n σ * chartEps n σ δ := hDs.trans (by linarith)
    have hdt' : ‖deriv (fun s => stageMap F j (stage F P j u t) s) t‖ ≤
        chartC₂ n σ * chartEps n σ δ / F.scale j :=
      hdt.trans (div_le_div_of_nonneg_right hCH hr.le)
    have hstep := step_arith (n := n) hσ hε hr hsmall.contraction
    rw [scale_succ, deriv_stage_succ]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (1 + chartC₂ n σ * chartEps n σ δ) * (chartCa n σ * chartEps n σ δ / F.scale j) +
          chartC₂ n σ * chartEps n σ δ / F.scale j :=
          add_le_add ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul hDs' hIH (norm_nonneg _) (add_nonneg zero_le_one (mul_nonneg hC2 hε))))
            hdt'
      _ ≤ _ := hstep

/-- **Increment bound, time part.** `|∂_t(F_{j+1} - F_j)| ≤ C_Δ ε / r_j` for `j ≤ N`, from
`∂_t(F_{j+1} - F_j) = (D_xσ_j - I)∂_tF_j + ∂_tσ_j` and `C₀ε ≤ C₂ε ≤ 4`. -/
theorem increment_bounds (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
    (hF : F.IsCoherentUpTo σ δ N) (hact : ActiveBound F P σ N) :
    ∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
      ‖deriv (fun s => stage F P (j + 1) u s - stage F P j u s) t‖ ≤
        chartCΔ n σ * chartEps n σ δ / F.scale j := by
  obtain ⟨h0, hC1, hC2, -, hCa, -, -, -⟩ := chartConsts_bounds (n := n) hσ
  have hε := chartEps_nonneg (n := n) hσ hδ
  have hC02 := chartC₀_le_chartC₂ (n := n) hσ
  intro j hjN u t
  have hr := scale_pos F j
  obtain ⟨α, H, hα, hH, -, hsumε, he, hc⟩ := exists_alpha_height hσ hδ hF hact hjN u t
  obtain ⟨hDs, hdt, -, -⟩ := level_bounds hσ hF hjN (stage F P j u t) t
    (tangent F P j u t) α H hα hH he hc
  have hτ := time_bounds hσ hδ hsmall hF hact j (by omega) u t
  have hHε : H ≤ chartEps n σ δ := by linarith
  have hCH0 : chartC₀ n σ * H ≤ chartC₀ n σ * chartEps n σ δ :=
    mul_le_mul_of_nonneg_left hHε (by linarith)
  have hC0ε : chartC₀ n σ * chartEps n σ δ ≤ 4 := by
    have hcon := hsmall.contraction
    have : chartC₀ n σ * chartEps n σ δ ≤ chartC₂ n σ * chartEps n σ δ :=
      mul_le_mul_of_nonneg_right hC02 hε
    unfold ratio at hcon
    linarith
  have hd1 := (smooth_differentiable (contDiff_stage_right F P (j + 1) u)) t
  have hd0 := (smooth_differentiable (contDiff_stage_right F P j u)) t
  rw [deriv_fun_sub hd1 hd0, deriv_stage_succ]
  have hY : 0 ≤ chartCa n σ * chartEps n σ δ / F.scale j :=
    div_nonneg (mul_nonneg hCa hε) hr.le
  have hC0ε0 : 0 ≤ chartC₀ n σ * chartEps n σ δ := mul_nonneg (by linarith) hε
  have hT1 : ‖fderiv ℝ (fun x => stageMap F j x t) (stage F P j u t)
      (deriv (fun s => stage F P j u s) t)‖ ≤
      (1 + chartC₀ n σ * chartEps n σ δ) * (chartCa n σ * chartEps n σ δ / F.scale j) :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hDs.trans (by linarith)) hτ (norm_nonneg _) (by linarith))
  have hT2 : ‖deriv (fun s => stageMap F j (stage F P j u t) s) t‖ ≤
      chartC₀ n σ * chartEps n σ δ / F.scale j :=
    hdt.trans (div_le_div_of_nonneg_right hCH0 hr.le)
  calc _ = ‖fderiv ℝ (fun x => stageMap F j x t) (stage F P j u t)
          (deriv (fun s => stage F P j u s) t) - deriv (fun s => stage F P j u s) t +
        deriv (fun s => stageMap F j (stage F P j u t) s) t‖ := by congr 1; abel
    _ ≤ ‖fderiv ℝ (fun x => stageMap F j x t) (stage F P j u t)
          (deriv (fun s => stage F P j u s) t)‖ + ‖deriv (fun s => stage F P j u s) t‖ +
        ‖deriv (fun s => stageMap F j (stage F P j u t) s) t‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (1 + chartC₀ n σ * chartEps n σ δ) * (chartCa n σ * chartEps n σ δ / F.scale j) +
          chartCa n σ * chartEps n σ δ / F.scale j + chartC₀ n σ * chartEps n σ δ / F.scale j :=
        add_le_add (add_le_add hT1 hτ) hT2
    _ ≤ chartCΔ n σ * chartEps n σ δ / F.scale j := by
        have hk : (1 + chartC₀ n σ * chartEps n σ δ) * (chartCa n σ * chartEps n σ δ / F.scale j)
            ≤ 5 * (chartCa n σ * chartEps n σ δ / F.scale j) :=
          mul_le_mul_of_nonneg_right (by linarith) hY
        have hsplit : chartCΔ n σ * chartEps n σ δ / F.scale j =
            6 * (chartCa n σ * chartEps n σ δ / F.scale j) +
              chartC₀ n σ * chartEps n σ δ / F.scale j := by unfold chartCΔ; ring
        rw [hsplit]
        linarith

end Recurrences

end HardLeaves2

/-! ## Speed, curvature and time recurrences -/

-- The hypothesis keeps the binder names of the statement it encodes.
set_option linter.unusedVariables false in
/-- **Recurrence estimates.** The hypothesis `hA4` is the statement of the induction
estimates; only its second conclusion (the active tangent and height bound for two
independent active indices) is used. The path bound enters only
through the speed estimate. -/
theorem recurrences_proof
    (hA4 : ∀ {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ} (hσ : 0 < σ)
      (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) (hF : F.IsCoherentUpTo σ δ N)
      (P : InitialChart F),
      (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
        Function.Injective (fderiv ℝ (fun v => stage F P j v t) u)) ∧
      (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ), ∀ a ∈ F.index j, ∀ b ∈ F.index j,
        IsActive F j a (stage F P j u t) t → IsActive F j b (stage F P j u t) t →
          ENNReal.ofReal (‖(tangent F P j u t).starProjection - (F.plane j a).linearProjection‖ +
              (F.scale j)⁻¹ * Metric.infDist (stage F P j u t) (F.plane j b).toSet) ≤
            ENNReal.ofReal (chartA n σ / ratio) * localError F j (pathPoint F P j u t)) ∧
      (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
        ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ chartEps n σ δ * F.scale j))
    {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ} (hσ : 0 < σ)
    (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) (hEsmall : EnergySmall n σ E)
    (hF : F.IsCoherentUpTo σ δ N) (P : InitialChart F) (hpath : PathBoundUpTo F P E N) :
    (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ) (v : Spatial m),
      99 / 100 * ‖v‖ ≤ ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ∧
        ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ≤ 101 / 100 * ‖v‖) ∧
    (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
      ‖fderiv ℝ (fun v => fderiv ℝ (fun w => stage F P j w t) v) u‖ ≤
          chartCa n σ * chartEps n σ δ / F.scale j ∧
        ‖deriv (fun s => stage F P j u s) t‖ ≤ chartCa n σ * chartEps n σ δ / F.scale j) ∧
    (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
      ‖deriv (fun s => stage F P (j + 1) u s - stage F P j u s) t‖ ≤
        chartCΔ n σ * chartEps n σ δ / F.scale j) := by
  have hact : HardLeaves2.ActiveBound F P σ N := (hA4 hσ hδ hsmall hF P).2.1
  exact ⟨HardLeaves2.speed_bounds hσ hδ hsmall hEsmall hF hact hpath,
    fun j hj u t => ⟨HardLeaves2.hessian_bounds hσ hδ hsmall hEsmall hF hact hpath j hj u t,
      HardLeaves2.time_bounds hσ hδ hsmall hF hact j hj u t⟩,
    HardLeaves2.increment_bounds hσ hδ hsmall hF hact⟩

namespace HardLeaves2

/-! ## Uniform metric control -/

theorem sixteen_le_chartCa {σ : ℝ} (hσ : 0 < σ) : 16 ≤ chartCa n σ := by
  have h0 := one_le_chartC₀ n hσ
  unfold chartCa chartC₂ chartC₁ ratio
  nlinarith

/-- `C_a ≤ C_t`, `C_a + 2/(h(1-h)) ≤ C_t` and `2/(1-h) ≤ C_t`. -/
theorem chartCt_bounds {σ : ℝ} (hσ : 0 < σ) :
    chartCa n σ ≤ chartCt n σ ∧ chartCa n σ + 200 / 9 ≤ chartCt n σ ∧ 20 / 9 ≤ chartCt n σ := by
  have h0 := one_le_chartC₀ n hσ
  have hCa := sixteen_le_chartCa (n := n) hσ
  have hct : chartCt n σ = 10 / 9 * (2 + 6 * chartCa n σ + chartC₀ n σ) := by
    unfold chartCt chartCΔ ratio; ring
  rw [hct]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The Hessian smallness condition `1.2 C_a ε/h ≤ 0.01` and `C_a ≥ 16` give
`C_a ε ≤ 1/1200` and `ε ≤ 1/19200`. -/
theorem eps_small {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) :
    chartCa n σ * chartEps n σ δ ≤ 1 / 1200 ∧ chartEps n σ δ ≤ 1 / 19200 := by
  have hh := hsmall.hessian
  have hCa := sixteen_le_chartCa (n := n) hσ
  have hε := chartEps_nonneg (n := n) hσ hδ
  have hq : 6 / 5 * chartCa n σ * chartEps n σ δ / ratio =
      12 * (chartCa n σ * chartEps n σ δ) := by
    unfold ratio; ring
  rw [hq] at hh
  have h16 := mul_le_mul_of_nonneg_right hCa hε
  exact ⟨by linarith, by linarith⟩

theorem geom_eq (x : ℝ) : x / (1 - ratio) = 10 / 9 * x := by unfold ratio; ring

/-- Choice of the comparison stage: for `b ≤ r_0` there is `J ≤ j` with `b ≤ r_J`, and
`r_{J+1} < b` unless `J = j`. -/
theorem exists_scale_index {F : CoherentFamily n m ι} {b : ℝ} (hb : b ≤ F.scale 0) (j : ℕ) :
    ∃ J, J ≤ j ∧ b ≤ F.scale J ∧ (J < j → F.scale (J + 1) < b) := by
  classical
  exact ⟨Nat.findGreatest (fun i => b ≤ F.scale i) j, Nat.findGreatest_le j,
    Nat.findGreatest_spec (P := fun i => b ≤ F.scale i) (Nat.zero_le j) hb,
    fun hlt => not_le.mp (Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hlt)⟩

section Metric

variable {F : CoherentFamily n m ι} {P : InitialChart F} {σ δ : ℝ} {N : ℕ}

theorem stage_zero_sub (u v : Spatial m) (t s : ℝ) :
    ‖stage F P 0 u t - stage F P 0 v s‖ = ‖u - v‖ := by
  show ‖P.origin + P.isometry u - (P.origin + P.isometry v)‖ = ‖u - v‖
  rw [add_sub_add_left_eq_sub, ← map_sub, LinearIsometry.norm_map]

/-- Displacement tails: `|F_j - F_J| ≤ ε r_J/(1 - h)` for `J ≤ j ≤ N + 1`. -/
theorem tail_le (hε : 0 ≤ chartEps n σ δ)
    (hdisp : ∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
      ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ chartEps n σ δ * F.scale j)
    {J j : ℕ} (hJj : J ≤ j) (hj : j ≤ N + 1) (u : Spatial m) (t : ℝ) :
    ‖stage F P j u t - stage F P J u t‖ ≤ 10 / 9 * (chartEps n σ δ * F.scale J) := by
  rw [← geom_eq]
  exact norm_sub_le_geometric F (fun i => stage F P i u t) _ hε hJj
    (fun i _ hi => hdisp i (by omega) u t)

/-- Mean value inequality in time at one stage. -/
theorem time_lipschitz {J : ℕ} {K : ℝ}
    (hτ : ∀ (u : Spatial m) (t : ℝ), ‖deriv (fun s => stage F P J u s) t‖ ≤ K)
    (u : Spatial m) (t s : ℝ) : ‖stage F P J u t - stage F P J u s‖ ≤ K * |t - s| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun s => stage F P J u s)
    (fun x _ => (smooth_differentiable (contDiff_stage_right F P J u)) x)
    (fun x _ => hτ u x) convex_univ (Set.mem_univ s) (Set.mem_univ t)
  rwa [Real.norm_eq_abs] at h

/-- Mean value inequality in space: `|F_j(u,t) - F_j(v,t)| ≤ 1.01|u - v|`. -/
theorem spatial_upper {j : ℕ}
    (hsp : ∀ (u : Spatial m) (t : ℝ) (v : Spatial m),
      ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ≤ 101 / 100 * ‖v‖)
    (u v : Spatial m) (t : ℝ) : ‖stage F P j u t - stage F P j v t‖ ≤ 101 / 100 * ‖u - v‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun w => stage F P j w t)
    (fun x _ => (smooth_differentiable (contDiff_stage_left F P j t)) x)
    (fun x _ => ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun y => hsp x t y))
    convex_univ (Set.mem_univ v) (Set.mem_univ u)

/-- Scale-free Taylor comparison: `|F_j(u,t) - F_j(v,t)| ≥ 0.99 d - K d²`, `d = |u - v|`,
when `|D_uF_j w| ≥ 0.99|w|` and `‖D_u²F_j‖ ≤ K` everywhere. -/
theorem taylor_lower {j : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hlo : ∀ (u : Spatial m) (t : ℝ) (v : Spatial m),
      99 / 100 * ‖v‖ ≤ ‖fderiv ℝ (fun w => stage F P j w t) u v‖)
    (hhess : ∀ (u : Spatial m) (t : ℝ),
      ‖fderiv ℝ (fun v => fderiv ℝ (fun w => stage F P j w t) v) u‖ ≤ K)
    (u v : Spatial m) (t : ℝ) :
    99 / 100 * ‖u - v‖ - K * ‖u - v‖ ^ 2 ≤ ‖stage F P j u t - stage F P j v t‖ := by
  have hs := contDiff_stage_left F P j t
  have hDD : ∀ w ∈ Metric.closedBall v ‖u - v‖,
      ‖fderiv ℝ (fun w => stage F P j w t) w - fderiv ℝ (fun w => stage F P j w t) v‖ ≤
        K * ‖u - v‖ := by
    intro w hw
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := fderiv ℝ (fun w => stage F P j w t))
      (fun x _ => (smooth_differentiable_fderiv hs) x) (fun x _ => hhess x t) convex_univ
      (Set.mem_univ v) (Set.mem_univ w)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hK)
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp hw
  have hg : ∀ w ∈ Metric.closedBall v ‖u - v‖,
      HasFDerivWithinAt (fun w => stage F P j w t - fderiv ℝ (fun w => stage F P j w t) v w)
        (fderiv ℝ (fun w => stage F P j w t) w - fderiv ℝ (fun w => stage F P j w t) v)
        (Metric.closedBall v ‖u - v‖) w := fun w _ =>
    (((smooth_differentiable hs) w).hasFDerivAt.sub
      (fderiv ℝ (fun w => stage F P j w t) v).hasFDerivAt).hasFDerivWithinAt
  have hmv := (convex_closedBall v ‖u - v‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hg hDD
    (Metric.mem_closedBall_self (norm_nonneg _))
    (Metric.mem_closedBall.mpr (dist_eq_norm u v).le)
  have heq : (stage F P j u t - fderiv ℝ (fun w => stage F P j w t) v u) -
      (stage F P j v t - fderiv ℝ (fun w => stage F P j w t) v v) =
      (stage F P j u t - stage F P j v t) - fderiv ℝ (fun w => stage F P j w t) v (u - v) := by
    rw [map_sub]; abel
  rw [heq] at hmv
  have h1 := hlo v t (u - v)
  have h2 := norm_sub_norm_le (fderiv ℝ (fun w => stage F P j w t) v (u - v))
    (stage F P j u t - stage F P j v t)
  rw [norm_sub_rev (fderiv ℝ (fun w => stage F P j w t) v (u - v))
    (stage F P j u t - stage F P j v t)] at h2
  linarith

/-- **Time modulus.** `|F_j(u,t) - F_j(u,s)| ≤ C_t ε √|t - s|`: compare with the stage `J`
with `r_{J+1} < √|t-s| ≤ r_J`, use the time speed `C_a ε/r_J` there and the displacement
tails after it. -/
theorem time_modulus (hσ : 0 < σ) (hδ : 0 ≤ δ)
    (hdisp : ∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
      ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ chartEps n σ δ * F.scale j)
    (htime : ∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
      ‖deriv (fun s => stage F P j u s) t‖ ≤ chartCa n σ * chartEps n σ δ / F.scale j)
    {j : ℕ} (hj : j ≤ N + 1) (u : Spatial m) (t s : ℝ) :
    ‖stage F P j u t - stage F P j u s‖ ≤ chartCt n σ * chartEps n σ δ * Real.sqrt |t - s| := by
  have hε := chartEps_nonneg (n := n) hσ hδ
  obtain ⟨hCt1, hCt2, hCt3⟩ := chartCt_bounds (n := n) hσ
  have hCa := sixteen_le_chartCa (n := n) hσ
  have hCaε0 : 0 ≤ chartCa n σ * chartEps n σ δ := mul_nonneg (by linarith) hε
  have htri : ∀ J ≤ j, ‖stage F P j u t - stage F P j u s‖ ≤
      ‖stage F P J u t - stage F P J u s‖ + 2 * (10 / 9 * (chartEps n σ δ * F.scale J)) := by
    intro J hJj
    have h1 := tail_le hε hdisp hJj hj u t
    have h2 := tail_le hε hdisp hJj hj u s
    have h3 : ‖stage F P j u t - stage F P j u s‖ ≤ ‖stage F P j u t - stage F P J u t‖ +
        ‖stage F P J u t - stage F P J u s‖ + ‖stage F P j u s - stage F P J u s‖ :=
      calc ‖stage F P j u t - stage F P j u s‖
          = ‖(stage F P j u t - stage F P J u t) + (stage F P J u t - stage F P J u s) -
              (stage F P j u s - stage F P J u s)‖ := by congr 1; abel
        _ ≤ ‖(stage F P j u t - stage F P J u t) + (stage F P J u t - stage F P J u s)‖ +
              ‖stage F P j u s - stage F P J u s‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
    linarith
  set b := Real.sqrt |t - s| with hbdef
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = |t - s| := Real.sq_sqrt (abs_nonneg _)
  have hεb := mul_nonneg hε hb
  by_cases h0 : b ≤ F.scale 0
  · obtain ⟨J, hJj, hJ, hnext⟩ := exists_scale_index h0 j
    have hrJ := scale_pos F J
    have hL := time_lipschitz (htime J (by omega)) u t s
    rw [← hb2] at hL
    have hK : chartCa n σ * chartEps n σ δ / F.scale J * b ^ 2 ≤
        chartCa n σ * chartEps n σ δ * b := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hrJ]
      nlinarith [mul_le_mul_of_nonneg_left hJ (mul_nonneg hCaε0 hb)]
    rcases Nat.lt_or_ge J j with hlt | hge
    · have hn := hnext hlt
      rw [scale_succ] at hn
      have hrJ10 : F.scale J ≤ 10 * b := by unfold ratio at hn; linarith
      have hT := htri J hJj
      have hεr := mul_le_mul_of_nonneg_left hrJ10 hε
      have p2 := mul_le_mul_of_nonneg_right hCt2 hεb
      linarith
    · have hJe : J = j := le_antisymm hJj hge
      subst hJe
      have p1 := mul_le_mul_of_nonneg_right hCt1 hεb
      linarith
  · rw [not_le] at h0
    have hT := htri 0 (Nat.zero_le j)
    have h00 : ‖stage F P 0 u t - stage F P 0 u s‖ = 0 := by
      rw [stage_zero_sub, sub_self, norm_zero]
    have hεr := mul_le_mul_of_nonneg_left h0.le hε
    have p3 := mul_le_mul_of_nonneg_right hCt3 hεb
    linarith

/-- **Global spatial noncollapse.** `0.9|u - v| ≤ |F_j(u,t) - F_j(v,t)|` on the whole
parameter space: Taylor comparison at the stage `J` with `r_{J+1} < |u - v| ≤ r_J` and the
displacement tails after it; for `|u - v| > r_0`, the isometric initial chart and the total
displacement. -/
theorem spatial_lower (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
    (hdisp : ∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
      ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ chartEps n σ δ * F.scale j)
    (hlo : ∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ) (v : Spatial m),
      99 / 100 * ‖v‖ ≤ ‖fderiv ℝ (fun w => stage F P j w t) u v‖)
    (hhess : ∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
      ‖fderiv ℝ (fun v => fderiv ℝ (fun w => stage F P j w t) v) u‖ ≤
        chartCa n σ * chartEps n σ δ / F.scale j)
    {j : ℕ} (hj : j ≤ N + 1) (u v : Spatial m) (t : ℝ) :
    9 / 10 * ‖u - v‖ ≤ ‖stage F P j u t - stage F P j v t‖ := by
  have hε := chartEps_nonneg (n := n) hσ hδ
  obtain ⟨hCaε, hε'⟩ := eps_small hσ hδ hsmall
  have hCa := sixteen_le_chartCa (n := n) hσ
  have hCaε0 : 0 ≤ chartCa n σ * chartEps n σ δ := mul_nonneg (by linarith) hε
  have hd := norm_nonneg (u - v)
  have p1 := mul_le_mul_of_nonneg_right hCaε hd
  have p2 := mul_le_mul_of_nonneg_right hε' hd
  have htri : ∀ J ≤ j, ‖stage F P J u t - stage F P J v t‖ ≤
      ‖stage F P j u t - stage F P J u t‖ + ‖stage F P j u t - stage F P j v t‖ +
        ‖stage F P j v t - stage F P J v t‖ := by
    intro J _
    calc ‖stage F P J u t - stage F P J v t‖
        = ‖-(stage F P j u t - stage F P J u t) + (stage F P j u t - stage F P j v t) +
            (stage F P j v t - stage F P J v t)‖ := by congr 1; abel
      _ ≤ ‖-(stage F P j u t - stage F P J u t)‖ + ‖stage F P j u t - stage F P j v t‖ +
            ‖stage F P j v t - stage F P J v t‖ := norm_add₃_le
      _ = _ := by rw [norm_neg]
  by_cases h0 : ‖u - v‖ ≤ F.scale 0
  · obtain ⟨J, hJj, hJ, hnext⟩ := exists_scale_index h0 j
    have hrJ := scale_pos F J
    have hT := taylor_lower (div_nonneg hCaε0 hrJ.le) (hlo J (by omega)) (hhess J (by omega))
      u v t
    have hK : chartCa n σ * chartEps n σ δ / F.scale J * ‖u - v‖ ^ 2 ≤
        chartCa n σ * chartEps n σ δ * ‖u - v‖ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hrJ]
      nlinarith [mul_le_mul_of_nonneg_left hJ (mul_nonneg hCaε0 hd)]
    rcases Nat.lt_or_ge J j with hlt | hge
    · have hn := hnext hlt
      rw [scale_succ] at hn
      have hrJ10 : F.scale J ≤ 10 * ‖u - v‖ := by unfold ratio at hn; linarith
      have hu := tail_le hε hdisp hJj hj u t
      have hv := tail_le hε hdisp hJj hj v t
      have hT' := htri J hJj
      have hεr := mul_le_mul_of_nonneg_left hrJ10 hε
      linarith
    · have hJe : J = j := le_antisymm hJj hge
      subst hJe
      linarith
  · rw [not_le] at h0
    have hu := tail_le hε hdisp (Nat.zero_le j) hj u t
    have hv := tail_le hε hdisp (Nat.zero_le j) hj v t
    have hT' := htri 0 (Nat.zero_le j)
    have h00 : ‖stage F P 0 u t - stage F P 0 v t‖ = ‖u - v‖ := stage_zero_sub u v t t
    have hεr := mul_le_mul_of_nonneg_left h0.le hε
    linarith

/-- **Bi-Lipschitz bounds** from the time modulus, the spatial bounds and `C_t ε ≤ 0.09`. -/
theorem bilip (hsmall : DeltaSmall n σ δ) {j : ℕ}
    (htm : ∀ (u : Spatial m) (t s : ℝ),
      ‖stage F P j u t - stage F P j u s‖ ≤ chartCt n σ * chartEps n σ δ * Real.sqrt |t - s|)
    (hsp : ∀ (u v : Spatial m) (t : ℝ),
      9 / 10 * ‖u - v‖ ≤ ‖stage F P j u t - stage F P j v t‖ ∧
        ‖stage F P j u t - stage F P j v t‖ ≤ 101 / 100 * ‖u - v‖)
    (u v : Spatial m) (t s : ℝ) :
    4 / 5 * dist (point u t) (point v s) ≤
        dist (point (stage F P j u t) t) (point (stage F P j v s) s) ∧
      dist (point (stage F P j u t) t) (point (stage F P j v s) s) ≤
        11 / 10 * dist (point u t) (point v s) := by
  simp only [dist_point]
  have hct := hsmall.time
  have hb := Real.sqrt_nonneg |t - s|
  have ha := norm_nonneg (u - v)
  obtain ⟨hlo, hup⟩ := hsp u v t
  have htv := htm v t s
  have hp := mul_le_mul_of_nonneg_right hct hb
  have htri1 := norm_sub_le_norm_sub_add_norm_sub (stage F P j u t) (stage F P j v t)
    (stage F P j v s)
  have htri2 := norm_sub_le_norm_sub_add_norm_sub (stage F P j u t) (stage F P j v s)
    (stage F P j v t)
  rw [norm_sub_rev (stage F P j v s) (stage F P j v t)] at htri2
  have hm1 := le_max_left ‖u - v‖ (Real.sqrt |t - s|)
  have hm2 := le_max_right ‖u - v‖ (Real.sqrt |t - s|)
  constructor
  · rcases le_total ‖u - v‖ (Real.sqrt |t - s|) with hab | hab
    · rw [max_eq_right hab]
      exact le_trans (by linarith) (le_max_right _ _)
    · rw [max_eq_left hab]
      exact le_trans (by linarith) (le_max_left _ _)
  · exact max_le (by linarith) (by linarith)

end Metric

end HardLeaves2

/-! ## Time modulus and global noncollapse -/

-- The hypothesis keeps the binder names of the statement it encodes.
set_option linter.unusedVariables false in
/-- **Finite metric estimates.** The hypothesis `hA4` is the statement of the induction
estimates; the recurrences are `recurrences_proof` above. Global noncollapse uses the
scale-dependent Taylor comparison at the stage matching `|u - v|` and the displacement
tails after it, not derivative injectivity alone. -/
theorem finite_metric_proof
    (hA4 : ∀ {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ} (hσ : 0 < σ)
      (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) (hF : F.IsCoherentUpTo σ δ N)
      (P : InitialChart F),
      (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
        Function.Injective (fderiv ℝ (fun v => stage F P j v t) u)) ∧
      (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ), ∀ a ∈ F.index j, ∀ b ∈ F.index j,
        IsActive F j a (stage F P j u t) t → IsActive F j b (stage F P j u t) t →
          ENNReal.ofReal (‖(tangent F P j u t).starProjection - (F.plane j a).linearProjection‖ +
              (F.scale j)⁻¹ * Metric.infDist (stage F P j u t) (F.plane j b).toSet) ≤
            ENNReal.ofReal (chartA n σ / ratio) * localError F j (pathPoint F P j u t)) ∧
      (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
        ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ chartEps n σ δ * F.scale j))
    {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ} (hσ : 0 < σ)
    (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) (hEsmall : EnergySmall n σ E)
    (hF : F.IsCoherentUpTo σ δ N) (P : InitialChart F) (hpath : PathBoundUpTo F P E N) :
    ∀ j ≤ N + 1,
      (∀ (u : Spatial m) (t s : ℝ),
        ‖stage F P j u t - stage F P j u s‖ ≤
          chartCt n σ * chartEps n σ δ * Real.sqrt |t - s|) ∧
      (∀ (u v : Spatial m) (t : ℝ),
        9 / 10 * ‖u - v‖ ≤ ‖stage F P j u t - stage F P j v t‖ ∧
          ‖stage F P j u t - stage F P j v t‖ ≤ 101 / 100 * ‖u - v‖) ∧
      (∀ (u v : Spatial m) (t s : ℝ),
        4 / 5 * dist (point u t) (point v s) ≤
            dist (point (stage F P j u t) t) (point (stage F P j v s) s) ∧
          dist (point (stage F P j u t) t) (point (stage F P j v s) s) ≤
            11 / 10 * dist (point u t) (point v s)) := by
  obtain ⟨hsp, hcurv, -⟩ := recurrences_proof hA4 hσ hδ hsmall hEsmall hF P hpath
  have hdisp := (hA4 hσ hδ hsmall hF P).2.2
  intro j hj
  have htm : ∀ (u : Spatial m) (t s : ℝ), ‖stage F P j u t - stage F P j u s‖ ≤
      chartCt n σ * chartEps n σ δ * Real.sqrt |t - s| := fun u t s =>
    HardLeaves2.time_modulus hσ hδ hdisp (fun i hi u t => (hcurv i hi u t).2) hj u t s
  have hspat : ∀ (u v : Spatial m) (t : ℝ),
      9 / 10 * ‖u - v‖ ≤ ‖stage F P j u t - stage F P j v t‖ ∧
        ‖stage F P j u t - stage F P j v t‖ ≤ 101 / 100 * ‖u - v‖ := fun u v t =>
    ⟨HardLeaves2.spatial_lower hσ hδ hsmall hdisp (fun i hi u t v => (hsp i hi u t v).1)
        (fun i hi u t => (hcurv i hi u t).1) hj u v t,
      HardLeaves2.spatial_upper (fun u t v => (hsp j hj u t v).2) u v t⟩
  exact ⟨htm, hspat, HardLeaves2.bilip hsmall htm hspat⟩

end CoherentChart

end ParabolicRectifiability
