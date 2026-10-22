import ParabolicRectifiability.Geometry.Neck.ComparisonEnergy

/-!
# The synthetic family of the horizontal reduction

The horizontal chart lemma reduces the
spatial construction to the vertical one by a *synthetic* coherent family: every
center occurrence `z_{j,a} = (x_{j,a}, t_{j,a})` is replaced by `ẑ_{j,a} = (x_{j,a}, 0)`,
while the index sets, planes, parent maps, initial radius (hence all scales `r_j`) and
initial plane are kept.

* `CoherentFamily.synthetic` is this family.
* `CoherentFamily.IsCoherentUpTo.synthetic`, `CoherentFamily.isCoherent_synthetic`:
  if the original family is coherent and time-compatible with
  `0 ≤ γ ≤ min(σ², 1)/4`, then the synthetic family is coherent with the same `σ, δ`
  Time compatibility at a fixed level turns parabolic `σ r_j`-separation into
  spatial separation, and (with `γ ≤ 1`) spatial neighbors within `20 r` into
  parabolic neighbors, so every comparison needed is one of the original family.
* `CoherentFamily.verticalEnergy_synthetic_le`: the vertical comparison function of
  the synthetic family at `(w,t)` is at most the horizontal function `E_j^H(w)` of the
  original family; hence the horizontal square bound gives the vertical square bound
  of the synthetic family. This uses no time compatibility.
* Center heights transfer unchanged; level limits and stopping parents transfer to the
  flattened points `(x_z, 0)` and `(x_c, 0)`.

The plane rank `m` is arbitrary, so rank zero and full rank `m = n` are included.
-/

noncomputable section

namespace ParabolicRectifiability

open Filter Topology

variable {n m : ℕ} {ι : Type*}

/-! ### The parabolic distance in coordinates -/

/-- The parabolic distance is `max(|x - y|, √|t - s|)`. -/
theorem dist_space_eq (z w : Space n) :
    dist z w = max ‖z.1 - w.1‖ (Real.sqrt |z.2.val - w.2.val|) := by
  obtain ⟨x, ⟨t⟩⟩ := z
  obtain ⟨y, ⟨s⟩⟩ := w
  exact dist_point x y t s

/-- The spatial distance is at most the parabolic distance. -/
theorem dist_fst_le_dist_space (z w : Space n) : dist z.1 w.1 ≤ dist z w := by
  rw [Prod.dist_eq]
  exact le_max_left _ _

/-- Two points at time zero have parabolic distance equal to their spatial distance. -/
theorem dist_point_zero (x y : Spatial n) : dist (point x 0) (point y 0) = dist x y := by
  rw [dist_point, sub_self, abs_zero, Real.sqrt_zero, dist_eq_norm]
  exact max_eq_left (norm_nonneg _)

/-- The spatial distance of `point x 0` to any point is at most the parabolic distance. -/
theorem dist_le_dist_point_zero (x : Spatial n) (w : Space n) :
    dist x w.1 ≤ dist (point x 0) w :=
  dist_fst_le_dist_space (point x 0) w

theorem continuous_point_zero : Continuous (fun z : Space n => point z.1 0) := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun z w => ?_)
  show dist (point z.1 0) (point w.1 0) ≤ ((1 : NNReal) : ℝ) * dist z w
  rw [dist_point_zero, NNReal.coe_one, one_mul]
  exact dist_fst_le_dist_space z w

namespace CoherentFamily

variable (F : CoherentFamily n m ι)

theorem scale_pos (j : ℕ) : 0 < F.scale j := by
  have := F.initialRadius_pos
  unfold scale coherentScale
  positivity

theorem scale_succ_le (j : ℕ) : F.scale (j + 1) ≤ F.scale j := by
  unfold scale coherentScale
  exact div_le_div_of_nonneg_left F.initialRadius_pos.le (pow_pos (by norm_num) j)
    (pow_le_pow_right₀ (by norm_num) (Nat.le_succ j))

/-! ### The synthetic family -/

/-- The synthetic family of the horizontal reduction: centers `(x_{j,a}, 0)`, with the same index
sets, planes, parents, initial radius and initial plane. -/
def synthetic : CoherentFamily n m ι where
  initialRadius := F.initialRadius
  initialRadius_pos := F.initialRadius_pos
  index := F.index
  center j a := point (F.center j a).1 0
  plane := F.plane
  parent := F.parent
  initialPlane := F.initialPlane

@[simp] theorem synthetic_initialRadius : F.synthetic.initialRadius = F.initialRadius := rfl
@[simp] theorem synthetic_index : F.synthetic.index = F.index := rfl
@[simp] theorem synthetic_center (j : ℕ) (a : ι) :
    F.synthetic.center j a = point (F.center j a).1 0 := rfl
@[simp] theorem synthetic_center_fst (j : ℕ) (a : ι) :
    (F.synthetic.center j a).1 = (F.center j a).1 := rfl
@[simp] theorem synthetic_plane : F.synthetic.plane = F.plane := rfl
@[simp] theorem synthetic_parent : F.synthetic.parent = F.parent := rfl
@[simp] theorem synthetic_initialPlane : F.synthetic.initialPlane = F.initialPlane := rfl
@[simp] theorem synthetic_scale : F.synthetic.scale = F.scale := rfl

/-- Synthetic centers have parabolic distance equal to the spatial distance of the
original centers. -/
theorem dist_synthetic_center (i j : ℕ) (a b : ι) :
    dist (F.synthetic.center i a) (F.synthetic.center j b) =
      dist (F.center i a).1 (F.center j b).1 :=
  dist_point_zero _ _

/-- Spatial projection decreases distance between centers. -/
theorem dist_synthetic_center_le (i j : ℕ) (a b : ι) :
    dist (F.synthetic.center i a) (F.synthetic.center j b) ≤
      dist (F.center i a) (F.center j b) := by
  rw [dist_synthetic_center]
  exact dist_fst_le_dist_space _ _

/-! ### Coherence of the synthetic family -/

/-- Time compatibility and `γ ≤ min(σ², 1)/4` turn the parabolic `σ r_j`-separation of
two level-`j` centers into spatial separation. -/
theorem le_dist_fst_of_timeCompatible {σ γ : ℝ} {N : ℕ} (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ min (σ ^ 2) 1 / 4) (ht : F.IsTimeCompatibleUpTo γ N) {j : ℕ} (hj : j ≤ N)
    {a b : ι} (ha : a ∈ F.index j) (hb : b ∈ F.index j)
    (hsep : σ * F.scale j ≤ dist (F.center j a) (F.center j b)) :
    σ * F.scale j ≤ dist (F.center j a).1 (F.center j b).1 := by
  by_contra hlt
  rw [not_le] at hlt
  have hr := F.scale_pos j
  have hx := dist_nonneg (x := (F.center j a).1) (y := (F.center j b).1)
  have hσr : 0 < σ * F.scale j := hx.trans_lt hlt
  rw [dist_eq_norm] at hlt hx
  -- the time difference is at most `σ² r_j² / 4`
  have hM : max (‖(F.center j a).1 - (F.center j b).1‖ ^ 2)
      (max (F.scale j ^ 2) (F.scale j ^ 2)) ≤ max (σ ^ 2) 1 * F.scale j ^ 2 := by
    rw [max_self]
    refine max_le ?_ ?_
    · calc ‖(F.center j a).1 - (F.center j b).1‖ ^ 2 ≤ (σ * F.scale j) ^ 2 :=
            pow_le_pow_left₀ hx hlt.le 2
        _ = σ ^ 2 * F.scale j ^ 2 := mul_pow _ _ _
        _ ≤ max (σ ^ 2) 1 * F.scale j ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    · calc F.scale j ^ 2 = 1 * F.scale j ^ 2 := (one_mul _).symm
        _ ≤ max (σ ^ 2) 1 * F.scale j ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  have hγmax : γ * max (σ ^ 2) 1 ≤ σ ^ 2 / 4 := by
    calc γ * max (σ ^ 2) 1 ≤ min (σ ^ 2) 1 / 4 * max (σ ^ 2) 1 :=
          mul_le_mul_of_nonneg_right hγ (le_max_of_le_right zero_le_one)
      _ = σ ^ 2 / 4 := by rw [div_mul_eq_mul_div, min_mul_max, mul_one]
  have htime := ht j hj j hj a ha b hb
  have htime' : |(F.center j a).2.val - (F.center j b).2.val| < (σ * F.scale j) ^ 2 := by
    calc |(F.center j a).2.val - (F.center j b).2.val|
        ≤ γ * (max (σ ^ 2) 1 * F.scale j ^ 2) :=
          htime.trans (mul_le_mul_of_nonneg_left hM hγ₀)
      _ = γ * max (σ ^ 2) 1 * F.scale j ^ 2 := (mul_assoc _ _ _).symm
      _ ≤ σ ^ 2 / 4 * F.scale j ^ 2 := mul_le_mul_of_nonneg_right hγmax (sq_nonneg _)
      _ < σ ^ 2 * F.scale j ^ 2 := by
          have : 0 < σ ^ 2 * F.scale j ^ 2 := by rw [← mul_pow]; exact pow_pos hσr 2
          linarith
      _ = (σ * F.scale j) ^ 2 := (mul_pow _ _ _).symm
  have hsqrt : Real.sqrt |(F.center j a).2.val - (F.center j b).2.val| < σ * F.scale j :=
    (Real.sqrt_lt' hσr).2 htime'
  rw [dist_space_eq] at hsep
  exact absurd hsep (not_le.2 (max_lt hlt hsqrt))

/-- Time compatibility with `γ ≤ 1` turns spatial neighbors within `20 r` into
parabolic neighbors within `20 r`, when both recorded scales are at most `r`. -/
theorem dist_le_of_timeCompatible {γ r : ℝ} {N : ℕ} (hγ : γ ≤ 1)
    (ht : F.IsTimeCompatibleUpTo γ N) {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) {a b : ι}
    (ha : a ∈ F.index i) (hb : b ∈ F.index j) (hri : F.scale i ≤ r) (hrj : F.scale j ≤ r)
    (hx : dist (F.center i a).1 (F.center j b).1 ≤ 20 * r) :
    dist (F.center i a) (F.center j b) ≤ 20 * r := by
  have hr : 0 ≤ r := (F.scale_pos i).le.trans hri
  have h20 : 0 ≤ 20 * r := by positivity
  rw [dist_eq_norm] at hx
  have hM : max (‖(F.center i a).1 - (F.center j b).1‖ ^ 2)
      (max (F.scale i ^ 2) (F.scale j ^ 2)) ≤ (20 * r) ^ 2 := by
    refine max_le (pow_le_pow_left₀ (norm_nonneg _) hx 2) (max_le ?_ ?_)
    · exact pow_le_pow_left₀ (F.scale_pos i).le (hri.trans (by linarith)) 2
    · exact pow_le_pow_left₀ (F.scale_pos j).le (hrj.trans (by linarith)) 2
  have hM₀ : 0 ≤ max (‖(F.center i a).1 - (F.center j b).1‖ ^ 2)
      (max (F.scale i ^ 2) (F.scale j ^ 2)) := le_max_of_le_left (sq_nonneg _)
  have htime : |(F.center i a).2.val - (F.center j b).2.val| ≤ (20 * r) ^ 2 :=
    (ht i hi j hj a ha b hb).trans
      ((mul_le_of_le_one_left hM₀ hγ).trans hM)
  rw [dist_space_eq]
  exact max_le hx (Real.sqrt_le_iff.2 ⟨h20, htime⟩)

/-- Finite truncations: if the original family is coherent and time-compatible
through level `N`, with `0 ≤ γ ≤ min(σ², 1)/4`, then so is the synthetic family. -/
theorem IsCoherentUpTo.synthetic {σ δ γ : ℝ} {N : ℕ} (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ min (σ ^ 2) 1 / 4) (hF : F.IsCoherentUpTo σ δ N)
    (ht : F.IsTimeCompatibleUpTo γ N) : F.synthetic.IsCoherentUpTo σ δ N := by
  have hγ1 : γ ≤ 1 := hγ.trans (by
    have := min_le_right (σ ^ 2) (1 : ℝ)
    linarith)
  refine
    { separated := ?_
      parent_mem := hF.parent_mem
      parent_dist := ?_
      root := hF.root
      same := ?_
      adjacent := ?_ }
  · intro j hj a ha b hb hab
    rw [dist_synthetic_center, synthetic_scale]
    exact F.le_dist_fst_of_timeCompatible hγ₀ hγ ht hj ha hb (hF.separated j hj a ha b hb hab)
  · intro j hj a ha
    exact (F.dist_synthetic_center_le _ _ _ _).trans (hF.parent_dist j hj a ha)
  · intro j hj a ha b hb hab
    rw [dist_synthetic_center, synthetic_scale] at hab
    exact hF.same j hj a ha b hb
      (F.dist_le_of_timeCompatible hγ1 ht hj hj ha hb le_rfl le_rfl hab)
  · intro j hj a ha b hb hab
    rw [dist_synthetic_center, synthetic_scale] at hab
    exact hF.adjacent j hj a ha b hb
      (F.dist_le_of_timeCompatible hγ1 ht hj (Nat.le_of_succ_le hj) ha hb
        (F.scale_succ_le j) le_rfl hab)

/-- If the original family is coherent and time-compatible at every level, with
`0 ≤ γ ≤ min(σ², 1)/4`, then the synthetic family is coherent. -/
theorem isCoherent_synthetic {σ δ γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ : γ ≤ min (σ ^ 2) 1 / 4)
    (hF : F.IsCoherent σ δ) (ht : F.IsTimeCompatible γ) : F.synthetic.IsCoherent σ δ :=
  fun N => (hF N).synthetic F hγ₀ hγ (ht N)

/-! ### The comparison energies -/

theorem rootComparisonTerm_synthetic_le (w : Space n) :
    F.synthetic.rootComparisonTerm (fun z : Space n => z) w ≤
      F.rootComparisonTerm (fun z : Space n => z.1) w.1 := by
  unfold rootComparisonTerm
  refine iSup₂_mono fun a _ => iSup_mono' fun h => ⟨?_, le_rfl⟩
  exact (dist_le_dist_point_zero _ w).trans h

theorem sameLevelComparisonTerm_synthetic_le (j : ℕ) (w : Space n) :
    F.synthetic.sameLevelComparisonTerm (fun z : Space n => z) j w ≤
      F.sameLevelComparisonTerm (fun z : Space n => z.1) j w.1 := by
  unfold sameLevelComparisonTerm
  refine iSup₂_mono fun a _ => iSup₂_mono fun b _ => iSup_mono' fun h => ⟨?_, le_rfl⟩
  obtain ⟨hab, ha, hb⟩ := h
  exact ⟨(F.dist_synthetic_center j j a b).symm.le.trans hab,
    (dist_le_dist_point_zero _ w).trans ha, (dist_le_dist_point_zero _ w).trans hb⟩

theorem adjacentComparisonTerm_synthetic_le (j : ℕ) (w : Space n) :
    F.synthetic.adjacentComparisonTerm (fun z : Space n => z) j w ≤
      F.adjacentComparisonTerm (fun z : Space n => z.1) j w.1 := by
  unfold adjacentComparisonTerm
  refine iSup₂_mono fun a _ => iSup₂_mono fun b _ => iSup_mono' fun h => ⟨?_, le_rfl⟩
  obtain ⟨hab, ha, hb⟩ := h
  exact ⟨(F.dist_synthetic_center (j + 1) j a b).symm.le.trans hab,
    (dist_le_dist_point_zero _ w).trans ha, (dist_le_dist_point_zero _ w).trans hb⟩

/-- The vertical comparison function of the synthetic family at `(w,t)` is at most
the horizontal comparison function `E_j^H(w)` of the original family: every pair in the
synthetic maximum also occurs in the horizontal maximum at `w`. -/
theorem verticalEnergy_synthetic_le (j : ℕ) (w : Space n) :
    F.synthetic.verticalEnergy j w ≤ F.horizontalEnergy j w.1 := by
  cases j with
  | zero =>
    simp only [verticalEnergy, horizontalEnergy, comparisonEnergy]
    exact F.rootComparisonTerm_synthetic_le w
  | succ j =>
    simp only [verticalEnergy, horizontalEnergy, comparisonEnergy]
    exact max_le_max (F.sameLevelComparisonTerm_synthetic_le j w)
      (F.adjacentComparisonTerm_synthetic_le j w)

/-- The horizontal square bound of the original family gives the vertical square
bound of the synthetic family, `sup_{(w,t)} ∑_j Ê_j(w,t)² ≤ E`. -/
theorem verticalSquareBound_synthetic {E : ℝ} (h : F.HorizontalSquareBound E) :
    F.synthetic.VerticalSquareBound E := fun w =>
  (ENNReal.tsum_le_tsum fun j => pow_le_pow_left₀ zero_le
    (F.verticalEnergy_synthetic_le j w) 2).trans (h w.1)

/-- The same for the levels `0, …, N` of a finite truncation. -/
theorem verticalSquareBoundUpTo_synthetic {E : ℝ} {N : ℕ}
    (h : F.HorizontalSquareBoundUpTo E N) : F.synthetic.VerticalSquareBoundUpTo E N :=
  fun w => (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ zero_le
    (F.verticalEnergy_synthetic_le j w) 2).trans (h w.1)

/-! ### Center heights, level limits and stopping parents -/

/-- The center-height bound is unchanged. -/
theorem hasCenterHeight_synthetic_iff {κ : ℝ} :
    F.synthetic.HasCenterHeight κ ↔ F.HasCenterHeight κ := Iff.rfl

/-- The center-height bound through level `N` is unchanged. -/
theorem hasCenterHeightUpTo_synthetic_iff {κ : ℝ} {N : ℕ} :
    F.synthetic.HasCenterHeightUpTo κ N ↔ F.HasCenterHeightUpTo κ N := Iff.rfl

/-- A limit `z` of original centers at levels tending to infinity gives the limit
`(x_z, 0)` of the corresponding synthetic centers. -/
theorem IsLevelLimit.synthetic {z : Space n} (hz : F.IsLevelLimit z) :
    F.synthetic.IsLevelLimit (point z.1 0) := by
  obtain ⟨level, idx, hmem, hlevel, hlim⟩ := hz
  exact ⟨level, idx, hmem, hlevel, (continuous_point_zero.tendsto z).comp hlim⟩

/-- A stopping parent of `c` for the original family is a stopping parent of
`(x_c, 0)` for the synthetic family, with the same spatial tube and no greater parent
distance. -/
theorem IsStoppingParent.synthetic {θ d : ℝ} {c : Space n} {p : Option (ℕ × ι)}
    (hp : F.IsStoppingParent θ c d p) : F.synthetic.IsStoppingParent θ (point c.1 0) d p := by
  cases p with
  | none => exact hp
  | some ja =>
    obtain ⟨j, a⟩ := ja
    simp only [IsStoppingParent] at hp ⊢
    obtain ⟨ha, hdist, htube, hd⟩ := hp
    refine ⟨ha, ?_, htube, hd⟩
    calc dist (point c.1 0) (F.synthetic.center j a) = dist c.1 (F.center j a).1 :=
          dist_point_zero _ _
      _ ≤ dist c (F.center j a) := dist_fst_le_dist_space _ _
      _ ≤ F.scale j := hdist

end CoherentFamily

end ParabolicRectifiability
