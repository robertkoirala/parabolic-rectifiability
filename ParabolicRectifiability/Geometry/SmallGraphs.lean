import ParabolicRectifiability.Metric.BaseVolume

/-! # Small partial graphs from a spatially bi-Lipschitz chart

Let `F : ℝ^m × ℝ → ℝ^n` be continuous with `c|u-v| ≤ |F(u,t)-F(v,t)| ≤ L|u-v|`
and `|F(u,t)-F(u,s)| ≤ H|t-s|^{1/2}`, and put `Ψ(u,t) = (F(u,t),t)`. A
measurable parameter set is covered, up to a null set, by countably many compact
pieces whose `Ψ`-images are partial graphs over vertical planes with graph
constant `8δ/c + H` (`smallPartialGraphs`).

Measurability is organized without a Borel differential: we use the closed sets
`approxSet F δ D r = {z : |F(z.1+h,z.2) - F z - D h| ≤ 2δ|h| for |h| < r}`
for operators `D` in a countable dense subset of the operators with lower
bound `c`. Their countable union is `F_σ`; its complement is a Borel set whose
time slices consist of points of spatial non-differentiability, hence are null
by Rademacher's theorem (`LipschitzWith.ae_differentiableAt`), so it is null by
Tonelli (`Measure.prod_apply_symm`). Grouping by small spatial balls gives the
two-point estimate `(c-2δ)d ≤ b + Hh`, `h ≤ b`, which yields `8δ/c + H`.
Compact pieces come from inner regularity
(`MeasurableSet.exists_isCompact_sdiff_lt`), and the null exception has
Hausdorff-null image by `parabolic_hausdorff_comparison` and the Lipschitz image
bound `LipschitzWith.hausdorffMeasure_image_le`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

namespace SmallGraphs

variable {m n : ℕ}

/-- The snowflaked time distance. -/
theorem dist_time (τ σ : Time) : dist τ σ = Real.sqrt |τ.val - σ.val| := by
  change dist (Metric.Snowflaking.toSnowflaking τ.val : Time)
    (Metric.Snowflaking.toSnowflaking σ.val) = _
  simp only [Metric.Snowflaking.dist_toSnowflaking_toSnowflaking, dist_eq_norm,
    Real.norm_eq_abs, Real.sqrt_eq_rpow]

theorem dist_space (z z' : Space m) :
    dist z z' = max ‖z.1 - z'.1‖ (Real.sqrt |z.2.val - z'.2.val|) := by
  rw [Prod.dist_eq, dist_time, dist_eq_norm]

/-! ### Re-indexing a countable family by a subset of `ℕ` -/

theorem exists_nat_reindex {X ι : Type*} [Countable ι] (P : ι → Set X) :
    ∃ (I : Set ℕ) (Q : I → Set X), (∀ j, ∃ i, Q j = P i) ∧ ⋃ j, Q j = ⋃ i, P i := by
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  refine ⟨range e, fun j => P (Classical.choose j.2), fun j => ⟨_, rfl⟩, ?_⟩
  apply Subset.antisymm
  · exact iUnion_subset fun j => subset_iUnion P _
  · refine iUnion_subset fun i => ?_
    have hi : Classical.choose (⟨i, rfl⟩ : e i ∈ range e) = i :=
      he (Classical.choose_spec (⟨i, rfl⟩ : e i ∈ range e))
    intro x hx
    refine mem_iUnion.mpr ⟨⟨e i, i, rfl⟩, ?_⟩
    change x ∈ P (Classical.choose (⟨i, rfl⟩ : e i ∈ range e))
    rwa [hi]

/-! ### The two-point graph estimate -/

/-- The scalar core of the two-point estimate: `(c-2δ)d ≤ b + Hh` and `h ≤ b`
give a normal displacement at most `(8δ/c + H) b`. -/
theorem normal_le_of_tangential {c H δ d h T N b : ℝ} (hc : 0 < c) (hH₀ : 0 ≤ H)
    (hH₁ : H ≤ 1) (hδ : 0 < δ) (hδc : δ ≤ c / 4) (hd : 0 ≤ d) (hh : 0 ≤ h)
    (hTb : T ≤ b) (hhb : h ≤ b) (htan : c * d ≤ T + (2 * δ * d + H * h))
    (hnor : N ≤ 2 * δ * d + H * h) :
    N ≤ (8 * δ / c + H) * b := by
  have hHh : H * h ≤ h := by nlinarith
  have hcd : c * d ≤ 4 * b := by nlinarith
  have h2 : 2 * δ * d ≤ 8 * δ / c * b := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith
  have h3 : H * h ≤ H * b := mul_le_mul_of_nonneg_left hhb hH₀
  nlinarith

/-- The two-point property of a set of parameters with respect to one operator. -/
def TwoPoint (F : Space m → Spatial n) (δ : ℝ) (D : Spatial m →L[ℝ] Spatial n)
    (P : Set (Space m)) : Prop :=
  ∀ z ∈ P, ∀ z' ∈ P, ‖F (z'.1, z.2) - F z - D (z'.1 - z.1)‖ ≤ 2 * δ * ‖z'.1 - z.1‖

section Graph

variable (F : Space m → Spatial n) {c H δ : ℝ}

/-- The range of an operator with lower bound `c > 0` has full rank `m`. -/
theorem finrank_range_eq (D : Spatial m →L[ℝ] Spatial n) (hc : 0 < c)
    (hD : ∀ w, c * ‖w‖ ≤ ‖D w‖) :
    Module.finrank ℝ (LinearMap.range (D : Spatial m →ₗ[ℝ] Spatial n)) = m := by
  have hinj : Function.Injective (D : Spatial m →ₗ[ℝ] Spatial n) := by
    intro w w' hww'
    have h := hD (w - w')
    have h0 : D (w - w') = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hww'
    rw [h0, norm_zero] at h
    have : ‖w - w'‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (w - w')]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]

/-- Normal displacement is at most `(8δ/c + H)` times base displacement. -/
theorem normal_le_base (hc : 0 < c) (hH₀ : 0 ≤ H) (hH₁ : H ≤ 1) (hδ : 0 < δ)
    (hδc : δ ≤ c / 4)
    (htime : ∀ (u : Spatial m) (t s : ℝ),
      ‖F (point u t) - F (point u s)‖ ≤ H * Real.sqrt |t - s|)
    (D : Spatial m →L[ℝ] Spatial n) (hD : ∀ w, c * ‖w‖ ≤ ‖D w‖)
    {P : Set (Space m)} (hP : TwoPoint F δ D P) {z z' : Space m} (hz : z ∈ P)
    (hz' : z' ∈ P) :
    let W := LinearMap.range (D : Spatial m →ₗ[ℝ] Spatial n)
    ‖Wᗮ.starProjection (F z') - Wᗮ.starProjection (F z)‖ ≤
      (8 * δ / c + H) *
        max ‖W.starProjection (F z') - W.starProjection (F z)‖
          (Real.sqrt |z'.2.val - z.2.val|) := by
  intro W
  set d := ‖z'.1 - z.1‖
  set h := Real.sqrt |z'.2.val - z.2.val|
  set Δ := F z' - F z
  set e := Δ - D (z'.1 - z.1)
  have hDW : D (z'.1 - z.1) ∈ W := LinearMap.mem_range_self _ _
  have he : ‖e‖ ≤ 2 * δ * d + H * h := by
    have h1 : ‖F z' - F (z'.1, z.2)‖ ≤ H * h := htime z'.1 z'.2.val z.2.val
    have h2 := hP z hz z' hz'
    have : e = (F z' - F (z'.1, z.2)) + (F (z'.1, z.2) - F z - D (z'.1 - z.1)) := by
      simp only [e, Δ]; abel
    rw [this]
    exact (norm_add_le _ _).trans (by linarith)
  have hsplitW : W.starProjection Δ = D (z'.1 - z.1) + W.starProjection e := by
    have : Δ = D (z'.1 - z.1) + e := by simp only [e]; abel
    rw [this, map_add, (Submodule.starProjection_eq_self_iff).mpr hDW]
  have hsplitN : Wᗮ.starProjection Δ = Wᗮ.starProjection e := by
    have : Δ = D (z'.1 - z.1) + e := by simp only [e]; abel
    rw [this, map_add, Submodule.starProjection_orthogonal_val, (Submodule.starProjection_eq_self_iff).mpr hDW, sub_self, zero_add]
  have hT : c * d ≤ ‖W.starProjection Δ‖ + (2 * δ * d + H * h) := by
    have h1 : c * d ≤ ‖D (z'.1 - z.1)‖ := hD _
    have h2 : ‖D (z'.1 - z.1)‖ ≤ ‖W.starProjection Δ‖ + ‖W.starProjection e‖ := by
      rw [hsplitW]
      calc ‖D (z'.1 - z.1)‖ = ‖(D (z'.1 - z.1) + W.starProjection e) - W.starProjection e‖ := by
            rw [add_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    have h3 : ‖W.starProjection e‖ ≤ ‖e‖ := Submodule.norm_starProjection_apply_le _ _
    linarith
  have hN : ‖Wᗮ.starProjection Δ‖ ≤ 2 * δ * d + H * h := by
    rw [hsplitN]
    exact (Submodule.norm_starProjection_apply_le _ _).trans he
  rw [← map_sub, ← map_sub]
  exact normal_le_of_tangential hc hH₀ hH₁ hδ hδc (norm_nonneg _) (Real.sqrt_nonneg _)
    (le_max_left _ _) (le_max_right _ _) hT hN

/-- A two-point set is mapped by `Ψ` onto a partial graph with constant `8δ/c + H`. -/
theorem exists_partial_graph (hc : 0 < c) (hH₀ : 0 ≤ H) (hH₁ : H ≤ 1) (hδ : 0 < δ)
    (hδc : δ ≤ c / 4)
    (htime : ∀ (u : Spatial m) (t s : ℝ),
      ‖F (point u t) - F (point u s)‖ ≤ H * Real.sqrt |t - s|)
    (D : Spatial m →L[ℝ] Spatial n) (hD : ∀ w, c * ‖w‖ ≤ ‖D w‖)
    {P : Set (Space m)} (hP : TwoPoint F δ D P) :
    ∃ (W : Submodule ℝ (Spatial n)) (D : Set (SubspaceSpace W))
      (g : SubspaceSpace W → W.orthogonal),
      Module.finrank ℝ W = m ∧
      (∀ p ∈ D, ∀ q ∈ D, dist (g p) (g q) ≤ (8 * δ / c + H) * dist p q) ∧
      (fun z : Space m => ((F z, z.2) : Space n)) '' P =
        (fun q : SubspaceSpace W =>
          (((q.1 : Spatial n) + (g q : Spatial n), q.2) : Space n)) '' D := by
  classical
  have : Nonempty (Space m) := ⟨point 0 0⟩
  set W := LinearMap.range (D : Spatial m →ₗ[ℝ] Spatial n) with hWdef
  let β : Space m → SubspaceSpace W := fun z => (W.orthogonalProjectionOnto (F z), z.2)
  let g : SubspaceSpace W → W.orthogonal := fun q =>
    Wᗮ.orthogonalProjectionOnto (F (Function.invFunOn β P q))
  -- The key estimate in metric form.
  have key : ∀ z ∈ P, ∀ z' ∈ P,
      dist (Wᗮ.orthogonalProjectionOnto (F z')) (Wᗮ.orthogonalProjectionOnto (F z)) ≤
        (8 * δ / c + H) * dist (β z') (β z) := by
    intro z hz z' hz'
    have H0 := normal_le_base F hc hH₀ hH₁ hδ hδc htime D hD hP hz hz'
    simp only at H0
    rw [Subtype.dist_eq, dist_eq_norm, Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.coe_orthogonalProjectionOnto_apply, Prod.dist_eq, Subtype.dist_eq,
      dist_eq_norm, Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.coe_orthogonalProjectionOnto_apply, dist_time]
    exact H0
  have hg : ∀ z ∈ P, g (β z) = Wᗮ.orthogonalProjectionOnto (F z) := by
    intro z hz
    have hmem : β z ∈ β '' P := mem_image_of_mem β hz
    have h1 := Function.invFunOn_mem hmem
    have h2 : β (Function.invFunOn β P (β z)) = β z := Function.invFunOn_eq hmem
    have h3 := key _ h1 z hz
    rw [h2, dist_self, mul_zero] at h3
    exact (dist_le_zero.mp h3).symm
  refine ⟨W, β '' P, g, finrank_range_eq D hc hD, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
    rw [hg z hz, hg z' hz', dist_comm, dist_comm (β z)]
    exact key z hz z' hz'
  · rw [image_image]
    apply image_congr
    intro z hz
    rw [hg z hz]
    simp only [β, Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.starProjection_add_starProjection_orthogonal]

end Graph

/-! ### Closed approximation sets and the differentiability cover -/

/-- Points where `D` approximates the spatial increments of `F` to `2δ` at scales below `r`. -/
def approxSet (F : Space m → Spatial n) (δ : ℝ) (D : Spatial m →L[ℝ] Spatial n) (r : ℝ) :
    Set (Space m) :=
  {z | ∀ h : Spatial m, ‖h‖ < r → ‖F (z.1 + h, z.2) - F z - D h‖ ≤ 2 * δ * ‖h‖}

theorem isClosed_approxSet {F : Space m → Spatial n} (hF : Continuous F) (δ : ℝ)
    (D : Spatial m →L[ℝ] Spatial n) (r : ℝ) : IsClosed (approxSet F δ D r) := by
  have : approxSet F δ D r = ⋂ h : Spatial m, ⋂ (_ : ‖h‖ < r),
      {z : Space m | ‖F (z.1 + h, z.2) - F z - D h‖ ≤ 2 * δ * ‖h‖} := by
    ext z; simp [approxSet]
  rw [this]
  refine isClosed_iInter fun h => isClosed_iInter fun _ => isClosed_le ?_ continuous_const
  have h1 : Continuous fun z : Space m => F (z.1 + h, z.2) :=
    hF.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  exact ((h1.sub hF).sub continuous_const).norm

/-- Two points of one approximation set in one small spatial ball satisfy the
two-point property. -/
theorem twoPoint_of_subset {F : Space m → Spatial n} {δ : ℝ} {D : Spatial m →L[ℝ] Spatial n}
    {r : ℝ} {x : Spatial m} {P : Set (Space m)}
    (hP : P ⊆ approxSet F δ D r ∩ {z | z.1 ∈ ball x (r / 2)}) : TwoPoint F δ D P := by
  intro z hz z' hz'
  have h1 := (hP hz).1
  have hzx : dist z.1 x < r / 2 := (hP hz).2
  have hz'x : dist z'.1 x < r / 2 := (hP hz').2
  have hlt : ‖z'.1 - z.1‖ < r := by
    rw [← dist_eq_norm]
    linarith [dist_triangle_right z'.1 z.1 x]
  have := h1 (z'.1 - z.1) hlt
  rwa [add_sub_cancel] at this

/-- The derivative of a spatial slice inherits the lower bound `c`. -/
theorem lower_bound_of_hasFDerivAt {f : Spatial m → Spatial n} {c : ℝ}
    {D : Spatial m →L[ℝ] Spatial n} {u : Spatial m} (hf : HasFDerivAt f D u)
    (hlower : ∀ v, c * ‖v - u‖ ≤ ‖f v - f u‖) (w : Spatial m) : c * ‖w‖ ≤ ‖D w‖ := by
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hf
  apply le_of_forall_pos_le_add
  intro ε hε
  have hε' : 0 < ε / (‖w‖ + 1) := by positivity
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp (hlo.def hε')
  set s := ρ / (2 * (‖w‖ + 1)) with hs
  have hspos : 0 < s := by positivity
  have hsw : ‖s • w‖ < ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos, hs]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  have hb := hball (y := s • w) (by rwa [dist_zero_right])
  have hl := hlower (u + s • w)
  rw [add_sub_cancel_left] at hl
  have hD : ‖f (u + s • w) - f u‖ ≤ ‖D (s • w)‖ + ε / (‖w‖ + 1) * ‖s • w‖ := by
    calc ‖f (u + s • w) - f u‖ = ‖(f (u + s • w) - f u - D (s • w)) + D (s • w)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖f (u + s • w) - f u - D (s • w)‖ + ‖D (s • w)‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  rw [map_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hspos] at hD
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos] at hl
  have hmain : c * ‖w‖ ≤ ‖D w‖ + ε / (‖w‖ + 1) * ‖w‖ := by
    have : s * (c * ‖w‖) ≤ s * (‖D w‖ + ε / (‖w‖ + 1) * ‖w‖) := by nlinarith
    exact le_of_mul_le_mul_left this hspos
  have hfrac : ε / (‖w‖ + 1) * ‖w‖ ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  linarith

/-- The operators with lower bound `c`. -/
def lowerBoundedOps (m n : ℕ) (c : ℝ) : Set (Spatial m →L[ℝ] Spatial n) :=
  {D | ∀ w, c * ‖w‖ ≤ ‖D w‖}

/-- A point of spatial differentiability lies in one of the countably many
approximation sets. -/
theorem mem_approxSet_of_differentiableAt {F : Space m → Spatial n} {c δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ (u v : Spatial m) (t : ℝ),
      c * ‖u - v‖ ≤ ‖F (point u t) - F (point v t)‖)
    {T : Set (Spatial m →L[ℝ] Spatial n)} (hT : lowerBoundedOps m n c ⊆ closure T)
    (z : Space m) (hz : DifferentiableAt ℝ (fun u => F (u, z.2)) z.1) :
    ∃ D ∈ T, ∃ j : ℕ, z ∈ approxSet F δ D (1 / ((j : ℝ) + 1)) := by
  set f := fun u => F (u, z.2)
  have hf := hz.hasFDerivAt
  set D₀ := fderiv ℝ f z.1
  have hD₀ : D₀ ∈ lowerBoundedOps m n c :=
    lower_bound_of_hasFDerivAt hf fun v => hlower v z.1 z.2.val
  obtain ⟨D, hDT, hdist⟩ := Metric.mem_closure_iff.mp (hT hD₀) δ hδ
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hf
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp (hlo.def hδ)
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hρ
  refine ⟨D, hDT, j, fun h hh => ?_⟩
  have hb := hball (y := h) (by rw [dist_zero_right]; linarith)
  have hop : ‖(D₀ - D) h‖ ≤ δ * ‖h‖ := by
    refine ((D₀ - D).le_opNorm h).trans ?_
    rw [← dist_eq_norm]
    exact mul_le_mul_of_nonneg_right hdist.le (norm_nonneg h)
  have heq : F (z.1 + h, z.2) - F z - D h =
      (f (z.1 + h) - f z.1 - D₀ h) + (D₀ - D) h := by
    simp only [f, sub_apply]; abel
  rw [heq]
  calc _ ≤ ‖f (z.1 + h) - f z.1 - D₀ h‖ + ‖(D₀ - D) h‖ := norm_add_le _ _
    _ ≤ δ * ‖h‖ + δ * ‖h‖ := add_le_add hb hop
    _ = 2 * δ * ‖h‖ := by ring

/-- Spatial non-differentiability is null for parabolic volume, by Rademacher and Tonelli,
once it is enclosed in a Borel set. -/
theorem parabolicVolume_compl_iUnion_approxSet {F : Space m → Spatial n} (hF : Continuous F)
    {c L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hlower : ∀ (u v : Spatial m) (t : ℝ),
      c * ‖u - v‖ ≤ ‖F (point u t) - F (point v t)‖)
    (hupper : ∀ (u v : Spatial m) (t : ℝ),
      ‖F (point u t) - F (point v t)‖ ≤ L * ‖u - v‖)
    {T : Set (Spatial m →L[ℝ] Spatial n)} (hTc : T.Countable)
    (hT : lowerBoundedOps m n c ⊆ closure T) :
    parabolicVolume m (⋃ D : T, ⋃ j : ℕ, approxSet F δ D (1 / ((j : ℝ) + 1)))ᶜ = 0 := by
  have : Countable T := hTc.to_subtype
  set U := ⋃ D : T, ⋃ j : ℕ, approxSet F δ D (1 / ((j : ℝ) + 1))
  have hUm : MeasurableSet U :=
    MeasurableSet.iUnion fun D => MeasurableSet.iUnion fun j =>
      (isClosed_approxSet hF δ D _).measurableSet
  rw [parabolicVolume_apply, coordinateVolume,
    Measure.prod_apply_symm ((coordinatesMeasurableEquiv m).symm.measurable hUm.compl)]
  refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun t => ?_)
  have hlip : LipschitzWith (Real.toNNReal L) (fun u : Spatial m => F (point u t)) := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL]
    exact hupper u v t
  have hae := hlip.ae_differentiableAt (μ := (volume : Measure (Spatial m)))
  rw [ae_iff] at hae
  refine measure_mono_null (fun u hu => ?_) hae
  simp only [mem_preimage, coordinatesMeasurableEquiv_symm_apply, mem_compl_iff] at hu
  intro hdiff
  apply hu
  obtain ⟨D, hD, j, hj⟩ := mem_approxSet_of_differentiableAt hδ hlower hT (point u t) hdiff
  exact mem_iUnion.mpr ⟨⟨D, hD⟩, mem_iUnion.mpr ⟨j, hj⟩⟩

/-! ### Compact pieces by inner regularity -/

theorem exists_compact_cover {S : Set (Space m)} (hS : NullMeasurableSet S (parabolicVolume m)) :
    ∃ K : ℕ × ℕ → Set (Space m), (∀ i, IsCompact (K i) ∧ K i ⊆ S) ∧
      parabolicVolume m (S \ ⋃ i, K i) = 0 := by
  obtain ⟨S', hS'S, hS'm, hS'ae⟩ := hS.exists_measurable_subset_ae_eq
  have hB : ∀ N : ℕ, parabolicVolume m (S' ∩ closedBall (point 0 0) ((N : ℝ) + 1)) ≠ ∞ :=
    fun N => ((measure_mono inter_subset_right).trans_lt
      (isCompact_closedBall _ _).measure_lt_top).ne
  have hK : ∀ p : ℕ × ℕ, ∃ K, K ⊆ S' ∩ closedBall (point 0 0) ((p.1 : ℝ) + 1) ∧
      IsCompact K ∧ parabolicVolume m
        ((S' ∩ closedBall (point 0 0) ((p.1 : ℝ) + 1)) \ K) < ((p.2 : ℝ≥0∞))⁻¹ :=
    fun p => (hS'm.inter measurableSet_closedBall).exists_isCompact_sdiff_lt (hB p.1)
      (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top p.2))
  choose K hKsub hKc hKlt using hK
  refine ⟨K, fun p => ⟨hKc p, (hKsub p).trans (inter_subset_left.trans hS'S)⟩, ?_⟩
  have hnull : parabolicVolume m (S \ S') = 0 := by
    have := (ae_eq_set.mp hS'ae).2
    exact this
  have hpiece : ∀ N : ℕ, parabolicVolume m
      ((S' ∩ closedBall (point 0 0) ((N : ℝ) + 1)) \ ⋃ p, K p) = 0 := by
    intro N
    by_contra hne
    obtain ⟨i, hi⟩ := ENNReal.exists_inv_nat_lt hne
    have := (measure_mono (sdiff_subset_sdiff_right (subset_iUnion K (N, i)))).trans_lt
      (hKlt (N, i))
    exact absurd (hi.trans this) (lt_irrefl _)
  have hcover : S \ ⋃ p, K p ⊆
      (S \ S') ∪ ⋃ N : ℕ, (S' ∩ closedBall (point 0 0) ((N : ℝ) + 1)) \ ⋃ p, K p := by
    intro z ⟨hzS, hzK⟩
    by_cases hz : z ∈ S'
    · right
      obtain ⟨N, hN⟩ := exists_nat_ge (dist z (point (0 : Spatial m) 0))
      exact mem_iUnion.mpr ⟨N, ⟨hz, mem_closedBall.mpr (by linarith)⟩, hzK⟩
    · exact Or.inl ⟨hzS, hz⟩
  refine measure_mono_null hcover (measure_union_null hnull ?_)
  exact measure_iUnion_null hpiece

/-! ### The Lipschitz lift -/

theorem lipschitz_lift {F : Space m → Spatial n} {L H : ℝ} (hL : 0 ≤ L) (hH₁ : H ≤ 1)
    (hupper : ∀ (u v : Spatial m) (t : ℝ),
      ‖F (point u t) - F (point v t)‖ ≤ L * ‖u - v‖)
    (htime : ∀ (u : Spatial m) (t s : ℝ),
      ‖F (point u t) - F (point u s)‖ ≤ H * Real.sqrt |t - s|) :
    LipschitzWith (Real.toNNReal (L + 1)) (fun z : Space m => ((F z, z.2) : Space n)) := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [Real.coe_toNNReal _ (by linarith)]
  have hd := dist_space z z'
  have h1 : ‖z.1 - z'.1‖ ≤ dist z z' := hd ▸ le_max_left _ _
  have h2 : Real.sqrt |z.2.val - z'.2.val| ≤ dist z z' := hd ▸ le_max_right _ _
  have hF : dist (F z) (F z') ≤ (L + 1) * dist z z' := by
    rw [dist_eq_norm]
    have e1 : ‖F z - F (z'.1, z.2)‖ ≤ L * ‖z.1 - z'.1‖ := hupper z.1 z'.1 z.2.val
    have e2 : ‖F (z'.1, z.2) - F z'‖ ≤ H * Real.sqrt |z.2.val - z'.2.val| :=
      htime z'.1 z.2.val z'.2.val
    have hH : H * Real.sqrt |z.2.val - z'.2.val| ≤ dist z z' := by
      rcases le_or_gt 0 H with hH0 | hH0
      · nlinarith [Real.sqrt_nonneg |z.2.val - z'.2.val|]
      · nlinarith [Real.sqrt_nonneg |z.2.val - z'.2.val|, dist_nonneg (x := z) (y := z')]
    calc ‖F z - F z'‖ = ‖(F z - F (z'.1, z.2)) + (F (z'.1, z.2) - F z')‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖F z - F (z'.1, z.2)‖ + ‖F (z'.1, z.2) - F z'‖ := norm_add_le _ _
      _ ≤ L * dist z z' + dist z z' := by nlinarith
      _ = (L + 1) * dist z z' := by ring
  rw [Prod.dist_eq, max_le_iff]
  refine ⟨hF, ?_⟩
  rw [dist_time]
  nlinarith [dist_nonneg (x := z) (y := z')]

end SmallGraphs

open SmallGraphs in
/-- **Small partial graphs.** A measurable parameter set of a spatially bi-Lipschitz,
time-Hölder chart is covered, up to a null set with Hausdorff-null image, by countably
many compact pieces whose images are partial graphs over vertical planes with graph
constant `8δ/c + H`. -/
theorem smallPartialGraphs {m n : ℕ} (hm : 1 ≤ m) (F : Space m → Spatial n)
    (hF : Continuous F) (c L H : ℝ) (hc : 0 < c) (hcL : c ≤ L) (hH₀ : 0 ≤ H)
    (hH₁ : H ≤ 1)
    (hlower : ∀ (u v : Spatial m) (t : ℝ),
      c * ‖u - v‖ ≤ ‖F (point u t) - F (point v t)‖)
    (hupper : ∀ (u v : Spatial m) (t : ℝ),
      ‖F (point u t) - F (point v t)‖ ≤ L * ‖u - v‖)
    (htime : ∀ (u : Spatial m) (t s : ℝ),
      ‖F (point u t) - F (point u s)‖ ≤ H * Real.sqrt |t - s|)
    (A : Set (Space m)) (hA : NullMeasurableSet A (parabolicVolume m))
    (δ : ℝ) (hδ : 0 < δ) (hδc : δ ≤ c / 4) :
    ∃ (I : Set ℕ) (P : I → Set (Space m)),
      (∀ j, IsCompact (P j) ∧ P j ⊆ A ∧
        ∃ (W : Submodule ℝ (Spatial n)) (D : Set (SubspaceSpace W))
          (g : SubspaceSpace W → W.orthogonal),
          Module.finrank ℝ W = m ∧
          (∀ p ∈ D, ∀ q ∈ D, dist (g p) (g q) ≤ (8 * δ / c + H) * dist p q) ∧
          (fun z : Space m => ((F z, z.2) : Space n)) '' P j =
            (fun q : SubspaceSpace W =>
              (((q.1 : Spatial n) + (g q : Spatial n), q.2) : Space n)) '' D) ∧
      parabolicVolume m (A \ ⋃ j, P j) = 0 ∧
      hausdorffP n (m + 2)
        ((fun z : Space m => ((F z, z.2) : Space n)) '' (A \ ⋃ j, P j)) = 0 := by
  have _ := hm
  have hL : 0 ≤ L := hc.le.trans hcL
  -- A countable dense family of operators with lower bound `c`.
  obtain ⟨T, hTsub, hTc, hT⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (lowerBoundedOps m n c)).exists_countable_dense_subset
  have : Countable T := hTc.to_subtype
  -- A dense sequence of spatial centers.
  obtain ⟨x, hx⟩ := TopologicalSpace.exists_dense_seq (Spatial m)
  -- The groups and their compact pieces.
  let r : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let S : T × ℕ × ℕ → Set (Space m) := fun i =>
    A ∩ (approxSet F δ i.1 (r i.2.1) ∩ {z | z.1 ∈ ball (x i.2.2) (r i.2.1 / 2)})
  have hSm : ∀ i, NullMeasurableSet (S i) (parabolicVolume m) := fun i =>
    hA.inter (((isClosed_approxSet hF δ i.1 _).measurableSet).inter
      (measurableSet_ball.preimage measurable_fst)).nullMeasurableSet
  choose K hK hKnull using fun i => exists_compact_cover (hSm i)
  let Pc : (T × ℕ × ℕ) × (ℕ × ℕ) → Set (Space m) := fun p => K p.1 p.2
  have hPc : ∀ p, IsCompact (Pc p) ∧ Pc p ⊆ A ∧
      ∃ (W : Submodule ℝ (Spatial n)) (D : Set (SubspaceSpace W))
        (g : SubspaceSpace W → W.orthogonal),
        Module.finrank ℝ W = m ∧
        (∀ p ∈ D, ∀ q ∈ D, dist (g p) (g q) ≤ (8 * δ / c + H) * dist p q) ∧
        (fun z : Space m => ((F z, z.2) : Space n)) '' Pc p =
          (fun q : SubspaceSpace W =>
            (((q.1 : Spatial n) + (g q : Spatial n), q.2) : Space n)) '' D := by
    intro p
    have hsub : Pc p ⊆ S p.1 := (hK p.1 p.2).2
    refine ⟨(hK p.1 p.2).1, hsub.trans inter_subset_left, ?_⟩
    exact exists_partial_graph F hc hH₀ hH₁ hδ hδc htime p.1.1 (hTsub p.1.1.2)
      (twoPoint_of_subset (hsub.trans inter_subset_right))
  -- The exceptional set.
  have hnull : parabolicVolume m (A \ ⋃ p, Pc p) = 0 := by
    have hN := parabolicVolume_compl_iUnion_approxSet hF hL hδ hlower hupper hTc hT
    have hcover : A \ ⋃ p, Pc p ⊆
        (⋃ D : T, ⋃ j : ℕ, approxSet F δ D (1 / ((j : ℝ) + 1)))ᶜ ∪
          ⋃ i : T × ℕ × ℕ, (S i \ ⋃ q, K i q) := by
      intro z ⟨hzA, hzP⟩
      by_cases hz : z ∈ ⋃ D : T, ⋃ j : ℕ, approxSet F δ D (1 / ((j : ℝ) + 1))
      · right
        obtain ⟨D, hD⟩ := mem_iUnion.mp hz
        obtain ⟨j, hj⟩ := mem_iUnion.mp hD
        obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hx z.1 (r j / 2) (by positivity)
        refine mem_iUnion.mpr ⟨(D, j, k), ⟨hzA, hj, hk⟩, fun hzK => hzP ?_⟩
        obtain ⟨q, hq⟩ := mem_iUnion.mp hzK
        exact mem_iUnion.mpr ⟨((D, j, k), q), hq⟩
      · exact Or.inl hz
    exact measure_mono_null hcover (measure_union_null hN (measure_iUnion_null hKnull))
  -- Re-index by a subset of the naturals.
  obtain ⟨I, P, hP, hPU⟩ := exists_nat_reindex Pc
  refine ⟨I, P, fun j => ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hP j
    rw [hp]
    exact hPc p
  · rw [hPU]; exact hnull
  · rw [hPU]
    have hH := (parabolic_hausdorff_comparison m (A \ ⋃ p, Pc p)).2
    rw [hnull, mul_zero] at hH
    have hzero : hausdorffP m (m + 2) (A \ ⋃ p, Pc p) = 0 := le_antisymm hH zero_le
    have himg : hausdorffP n (m + 2)
        ((fun z : Space m => ((F z, z.2) : Space n)) '' (A \ ⋃ p, Pc p)) ≤
        ((Real.toNNReal (L + 1) : ℝ≥0) : ℝ≥0∞) ^ (((m + 2 : ℕ)) : ℝ) *
          hausdorffP m (m + 2) (A \ ⋃ p, Pc p) :=
      (lipschitz_lift hL hH₁ hupper htime).hausdorffMeasure_image_le
        (Nat.cast_nonneg (m + 2)) (A \ ⋃ p, Pc p)
    rw [hzero, mul_zero] at himg
    exact le_antisymm himg zero_le

end ParabolicRectifiability
