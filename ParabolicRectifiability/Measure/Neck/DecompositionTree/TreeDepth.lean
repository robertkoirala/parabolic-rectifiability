import ParabolicRectifiability.Measure.Neck.Construction

/-!
# Depth bounds for the decomposition tree

Proofs of three statements about the decomposition tree:

* `StepTree.depth_content_le_proof` (`StepTree.depth_content_le`):
  `∑_{|v| = j} R_v^k ≤ R^k / 2^j` and `R_v ≤ R / 2^{|v|}`;
* `StepTree.radius_total_le_proof` (`StepTree.radius_total_le`): `∑_v R_v^k ≤ 2 R^k`;
* `StepTree.closedContainer_null_proof` (`StepTree.closedContainer_null`): the
  closed-container intersection `⋂_j ⋃_{|v| = j} closure P(q_v, R_v)` is `H^k_P`-null.

It also proves the tree combinatorics used by the later results: prefix closure of the
vertex set, monotonicity of the sources along the tree, disjointness of the sources of
distinct vertices of equal depth and of the deeper sources from the local pieces, and the
descent of residual points to a child.

The depth sums are nonnegative countable sums; the inductive step regroups the depth
`j + 1` vertices by their parent (`v ++ [i] ↦ (v, i)` is onto) and uses the stored local
content bound `∑_{children} R_w^k ≤ R_v^k / 2`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

/-- `ofReal (x / 2) = ofReal x * 2⁻¹`. -/
theorem ms7_ofReal_div_two (x : ℝ) : ENNReal.ofReal (x / 2) = ENNReal.ofReal x * 2⁻¹ := by
  rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat, div_eq_mul_inv]

/-- `ofReal (x / 2^j) = ofReal x * 2⁻¹^j`. -/
theorem ms7_ofReal_div_two_pow (x : ℝ) (j : ℕ) :
    ENNReal.ofReal (x / 2 ^ j) = ENNReal.ofReal x * 2⁻¹ ^ j := by
  rw [ENNReal.ofReal_div_of_pos (pow_pos two_pos j : (0 : ℝ) < 2 ^ j),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, div_eq_mul_inv,
    ENNReal.inv_pow]

/-- Membership in the infinite-path residual set. -/
theorem ms7_mem_treeResidual {X : Type*} {V : Set (List ℕ)} {s : List ℕ → Set X} {z : X} :
    z ∈ treeResidual V s ↔ ∀ j, ∃ v ∈ V, v.length = j ∧ z ∈ s v := by
  simp only [treeResidual, mem_iInter, mem_iUnion, exists_prop]

namespace StepTree

variable {n k : ℕ} {F : FamilyKind} {S : Set (Space n)} {q : Space n} {R B Eerr ρ ε : ℝ}
  {ν : Measure (Space n)}

/-! ## Tree combinatorics -/

/-- The vertex set is closed under prefixes. -/
theorem ms7_mem_of_append_mem (Tr : StepTree ν k F S q R B Eerr ρ ε) (w : List ℕ) :
    ∀ u : List ℕ, u ++ w ∈ Tr.vertices → u ∈ Tr.vertices := by
  induction w using List.reverseRecOn with
  | nil => intro u h; simpa using h
  | append_singleton w i ih =>
    intro u h
    rw [← List.append_assoc] at h
    exact ih u (Tr.parent_mem _ i h)

theorem ms7_mem_of_prefix (Tr : StepTree ν k F S q R B Eerr ρ ε) {u v : List ℕ}
    (huv : u <+: v) (hv : v ∈ Tr.vertices) : u ∈ Tr.vertices := by
  obtain ⟨w, rfl⟩ := huv
  exact Tr.ms7_mem_of_append_mem w u hv

/-- Sources decrease along the tree. -/
theorem ms7_source_append_subset (Tr : StepTree ν k F S q R B Eerr ρ ε) (w : List ℕ) :
    ∀ u : List ℕ, u ++ w ∈ Tr.vertices → Tr.source (u ++ w) ⊆ Tr.source u := by
  induction w using List.reverseRecOn with
  | nil => intro u _; simp
  | append_singleton w i ih =>
    intro u h
    rw [← List.append_assoc] at h ⊢
    exact (Tr.child_subset _ i h).trans (ih u (Tr.parent_mem _ i h))

theorem ms7_source_subset_of_prefix (Tr : StepTree ν k F S q R B Eerr ρ ε) {u v : List ℕ}
    (huv : u <+: v) (hv : v ∈ Tr.vertices) : Tr.source v ⊆ Tr.source u := by
  obtain ⟨w, rfl⟩ := huv
  exact Tr.ms7_source_append_subset w u hv

/-- Every source lies in the root source `S`. -/
theorem ms7_source_subset_root (Tr : StepTree ν k F S q R B Eerr ρ ε) {v : List ℕ}
    (hv : v ∈ Tr.vertices) : Tr.source v ⊆ S := fun z hz => by
  have h := Tr.ms7_source_subset_of_prefix List.nil_prefix hv hz
  rwa [Tr.source_root] at h

/-- Radius decay along the tree: `R_v ≤ R / 2^{|v|}`. -/
theorem ms7_radius_le (Tr : StepTree ν k F S q R B Eerr ρ ε) (v : List ℕ) :
    v ∈ Tr.vertices → Tr.radius v ≤ R / 2 ^ v.length := by
  induction v using List.reverseRecOn with
  | nil => intro _; simp [Tr.radius_root]
  | append_singleton v i ih =>
    intro h
    have h1 := Tr.child_radius_le v i h
    have h2 := ih (Tr.parent_mem v i h)
    rw [List.length_append, List.length_singleton, pow_succ, ← div_div]
    linarith

/-- Distinct vertices of equal depth have disjoint sources. -/
theorem ms7_disjoint_source_of_length_eq (Tr : StepTree ν k F S q R B Eerr ρ ε) (m : ℕ) :
    ∀ v w : List ℕ, v ∈ Tr.vertices → w ∈ Tr.vertices → v.length = m → w.length = m →
      v ≠ w → Disjoint (Tr.source v) (Tr.source w) := by
  induction m with
  | zero =>
    intro v w _ _ hv hw hne
    exact absurd ((List.eq_nil_of_length_eq_zero hv).trans
      (List.eq_nil_of_length_eq_zero hw).symm) hne
  | succ m ih =>
    intro v w hvV hwV hv hw hne
    rcases List.eq_nil_or_concat' v with rfl | ⟨v', i, rfl⟩
    · simp at hv
    rcases List.eq_nil_or_concat' w with rfl | ⟨w', j, rfl⟩
    · simp at hw
    have hv' : v'.length = m := by simpa using hv
    have hw' : w'.length = m := by simpa using hw
    by_cases h : v' = w'
    · subst h
      have hij : i ≠ j := by rintro rfl; exact hne rfl
      exact Tr.disjoint_children v' i j hvV hwV hij
    · exact (ih v' w' (Tr.parent_mem _ _ hvV) (Tr.parent_mem _ _ hwV) hv' hw' h).mono
        (Tr.child_subset _ _ hvV) (Tr.child_subset _ _ hwV)

/-- A set inside `S_v` avoiding every child source of `v` avoids every source of
greater depth. -/
theorem ms7_disjoint_deeper (Tr : StepTree ν k F S q R B Eerr ρ ε) {v : List ℕ}
    (hv : v ∈ Tr.vertices) {X : Set (Space n)} (hX : X ⊆ Tr.source v)
    (hXc : ∀ i, v ++ [i] ∈ Tr.vertices → Disjoint X (Tr.source (v ++ [i])))
    {w : List ℕ} (hw : w ∈ Tr.vertices) (hlen : v.length < w.length) :
    Disjoint X (Tr.source w) := by
  have hu_pre : w.take (v.length + 1) <+: w := List.take_prefix _ _
  have huV : w.take (v.length + 1) ∈ Tr.vertices := Tr.ms7_mem_of_prefix hu_pre hw
  have hulen : (w.take (v.length + 1)).length = v.length + 1 := by
    rw [List.length_take]; omega
  have hsw : Tr.source w ⊆ Tr.source (w.take (v.length + 1)) :=
    Tr.ms7_source_subset_of_prefix hu_pre hw
  generalize w.take (v.length + 1) = u at huV hulen hsw
  rcases List.eq_nil_or_concat' u with rfl | ⟨u', i, rfl⟩
  · simp at hulen
  have hu'V : u' ∈ Tr.vertices := Tr.parent_mem u' i huV
  have hu'len : u'.length = v.length := by simpa using hulen
  by_cases h : u' = v
  · subst h
    exact (hXc i huV).mono_right hsw
  · have hd := Tr.ms7_disjoint_source_of_length_eq v.length v u' hv hu'V rfl hu'len (Ne.symm h)
    exact hd.mono hX (hsw.trans (Tr.child_subset u' i huV))

/-- A residual point of `S_v` lies in a child source of `v`. -/
theorem ms7_residual_descend (Tr : StepTree ν k F S q R B Eerr ρ ε) {v : List ℕ}
    (hv : v ∈ Tr.vertices) {z : Space n} (hzA : z ∈ treeResidual Tr.vertices Tr.source)
    (hzS : z ∈ Tr.source v) :
    ∃ i, v ++ [i] ∈ Tr.vertices ∧ z ∈ Tr.source (v ++ [i]) := by
  obtain ⟨w, hwV, hwlen, hzw⟩ := ms7_mem_treeResidual.mp hzA (v.length + 1)
  rcases List.eq_nil_or_concat' w with rfl | ⟨w', i, rfl⟩
  · simp at hwlen
  have hw'V : w' ∈ Tr.vertices := Tr.parent_mem w' i hwV
  have hw'len : w'.length = v.length := by simpa using hwlen
  by_cases h : w' = v
  · subst h; exact ⟨i, hwV, hzw⟩
  · exact absurd (Tr.child_subset w' i hwV hzw)
      (Set.disjoint_left.mp (Tr.ms7_disjoint_source_of_length_eq v.length v w' hv hw'V rfl
        hw'len (Ne.symm h)) hzS)

/-- The residual set lies in the root source. -/
theorem ms7_residual_subset_root (Tr : StepTree ν k F S q R B Eerr ρ ε) :
    treeResidual Tr.vertices Tr.source ⊆ Tr.source [] := by
  intro z hz
  obtain ⟨w, -, hwlen, hzw⟩ := ms7_mem_treeResidual.mp hz 0
  rwa [List.eq_nil_of_length_eq_zero hwlen] at hzw

/-! ## Depth content -/

/-- The depth-`j` content bound `∑_{|v| = j} R_v^k ≤ R^k / 2^j`. -/
theorem ms7_depth_sum_le (Tr : StepTree ν k F S q R B Eerr ρ ε) (j : ℕ) :
    ∑' v : {v : List ℕ // v ∈ Tr.vertices ∧ v.length = j},
      ENNReal.ofReal (Tr.radius v ^ k) ≤ ENNReal.ofReal (R ^ k / 2 ^ j) := by
  induction j with
  | zero =>
    have huniq : ∀ v : {v : List ℕ // v ∈ Tr.vertices ∧ v.length = 0},
        v = ⟨[], Tr.root_mem, rfl⟩ := fun v => Subtype.ext (List.eq_nil_of_length_eq_zero v.2.2)
    rw [tsum_eq_single ⟨[], Tr.root_mem, rfl⟩ (fun b hb => absurd (huniq b) hb)]
    simp [Tr.radius_root]
  | succ j ih =>
    let g : (Σ v : {v : List ℕ // v ∈ Tr.vertices ∧ v.length = j},
        {i : ℕ // v.1 ++ [i] ∈ Tr.vertices}) →
        {w : List ℕ // w ∈ Tr.vertices ∧ w.length = j + 1} :=
      fun p => ⟨p.1.1 ++ [p.2.1], p.2.2, by simp [p.1.2.2]⟩
    have hg : Function.Surjective g := by
      rintro ⟨w, hw, hlen⟩
      rcases List.eq_nil_or_concat' w with rfl | ⟨u, b, rfl⟩
      · simp at hlen
      · have hu : u ∈ Tr.vertices := Tr.parent_mem u b hw
        have hlu : u.length = j := by simpa using hlen
        exact ⟨⟨⟨u, hu, hlu⟩, ⟨b, hw⟩⟩, rfl⟩
    calc ∑' w : {w : List ℕ // w ∈ Tr.vertices ∧ w.length = j + 1},
          ENNReal.ofReal (Tr.radius w ^ k)
        ≤ ∑' p, ENNReal.ofReal (Tr.radius (g p).1 ^ k) :=
          ENNReal.tsum_le_tsum_comp_of_surjective hg
            (fun w => ENNReal.ofReal (Tr.radius w.1 ^ k))
      _ = ∑' (v : {v : List ℕ // v ∈ Tr.vertices ∧ v.length = j})
            (i : {i : ℕ // v.1 ++ [i] ∈ Tr.vertices}),
            ENNReal.ofReal (Tr.radius (v.1 ++ [i.1]) ^ k) :=
          ENNReal.tsum_sigma' (fun p => ENNReal.ofReal (Tr.radius (g p).1 ^ k))
      _ ≤ ∑' v : {v : List ℕ // v ∈ Tr.vertices ∧ v.length = j},
            ENNReal.ofReal (Tr.radius v ^ k / 2) :=
          ENNReal.tsum_le_tsum fun v => Tr.child_content_le v.1 v.2.1
      _ = (∑' v : {v : List ℕ // v ∈ Tr.vertices ∧ v.length = j},
            ENNReal.ofReal (Tr.radius v ^ k)) * 2⁻¹ := by
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun v => ms7_ofReal_div_two _
      _ ≤ ENNReal.ofReal (R ^ k / 2 ^ j) * 2⁻¹ := by gcongr
      _ = ENNReal.ofReal (R ^ k / 2 ^ (j + 1)) := by
          rw [pow_succ, ← div_div, ms7_ofReal_div_two]

/-- **`StepTree.depth_content_le`**: by induction on
the depth, `∑_{depth v = j} R_v^k ≤ 2^{-j} R^k` and `R_v ≤ 2^{-|v|} R`. -/
theorem depth_content_le_proof {n k : ℕ} {F : FamilyKind} {S : Set (Space n)} {q : Space n}
    {R B Eerr ρ ε : ℝ} {ν : Measure (Space n)} (Tr : StepTree ν k F S q R B Eerr ρ ε)
    (_hR : 0 < R) :
    (∀ j : ℕ, ∑' v : {v : List ℕ // v ∈ Tr.vertices ∧ v.length = j},
        ENNReal.ofReal (Tr.radius v ^ k) ≤ ENNReal.ofReal (R ^ k / 2 ^ j)) ∧
      ∀ v ∈ Tr.vertices, Tr.radius v ≤ R / 2 ^ v.length :=
  ⟨Tr.ms7_depth_sum_le, fun v hv => Tr.ms7_radius_le v hv⟩

/-! ## Total radius content -/

/-- **`StepTree.radius_total_le`**: summing the depth bounds:
`∑_v R_v^k ≤ ∑_j 2^{-j} R^k = 2 R^k`. -/
theorem radius_total_le_proof {n k : ℕ} {F : FamilyKind} {S : Set (Space n)} {q : Space n}
    {R B Eerr ρ ε : ℝ} {ν : Measure (Space n)} (Tr : StepTree ν k F S q R B Eerr ρ ε)
    (_hR : 0 < R) :
    ∑' v : Tr.vertices, ENNReal.ofReal (Tr.radius v ^ k) ≤ ENNReal.ofReal (2 * R ^ k) := by
  let e := Equiv.sigmaFiberEquiv (fun v : Tr.vertices => v.1.length)
  calc ∑' v : Tr.vertices, ENNReal.ofReal (Tr.radius v ^ k)
      = ∑' p : (Σ j : ℕ, {v : Tr.vertices // v.1.length = j}),
          ENNReal.ofReal (Tr.radius (e p).1 ^ k) :=
        (e.tsum_eq (fun v : Tr.vertices => ENNReal.ofReal (Tr.radius v ^ k))).symm
    _ = ∑' (j : ℕ) (v : {v : Tr.vertices // v.1.length = j}),
          ENNReal.ofReal (Tr.radius v.1.1 ^ k) :=
        ENNReal.tsum_sigma' (fun p => ENNReal.ofReal (Tr.radius (e p).1 ^ k))
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (R ^ k / 2 ^ j) := by
        refine ENNReal.tsum_le_tsum fun j => le_trans ?_ (Tr.ms7_depth_sum_le j)
        exact ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun v : {v : Tr.vertices // v.1.length = j} =>
            (⟨v.1.1, v.1.2, v.2⟩ : {v : List ℕ // v ∈ Tr.vertices ∧ v.length = j}))
          (fun a b h => by
            have h' := congrArg Subtype.val h
            exact Subtype.ext (Subtype.ext h'))
          (fun v => ENNReal.ofReal (Tr.radius v.1 ^ k))
    _ = ENNReal.ofReal (R ^ k) * 2 := by
        simp_rw [ms7_ofReal_div_two_pow]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    _ = ENNReal.ofReal (2 * R ^ k) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_comm]

/-! ## Closed-container nullity -/

/-- **`StepTree.closedContainer_null`**: the depth-`j` closed containers cover the closed-container intersection, have
diameters at most `2^{1-j} R` and total cost `∑ (2 R_v)^k ≤ 2^k 2^{-j} R^k → 0`. -/
theorem closedContainer_null_proof {n k : ℕ} {F : FamilyKind} {S : Set (Space n)}
    {q : Space n} {R B Eerr ρ ε : ℝ} {ν : Measure (Space n)}
    (Tr : StepTree ν k F S q R B Eerr ρ ε) (_hR : 0 < R) :
    hausdorffP n k
      (treeResidual Tr.vertices fun v => Metric.closedBall (Tr.center v) (Tr.radius v)) = 0 := by
  rw [hausdorffP_eq]
  set s := treeResidual Tr.vertices fun v => Metric.closedBall (Tr.center v) (Tr.radius v)
  -- the depth-`j` covers
  let t : ∀ j : ℕ, {v : List ℕ // v ∈ Tr.vertices ∧ v.length = j} → Set (Space n) :=
    fun _ v => Metric.closedBall (Tr.center v) (Tr.radius v)
  have hdiam : ∀ (j : ℕ) (v : {v : List ℕ // v ∈ Tr.vertices ∧ v.length = j}),
      Metric.ediam (t j v) ≤ ENNReal.ofReal (2 * Tr.radius v) := by
    intro j v
    refine Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_
    have hx' := Metric.mem_closedBall.mp hx
    have hy' := Metric.mem_closedBall.mp hy
    linarith [dist_triangle_right x y (Tr.center v)]
  have hr : Tendsto (fun j : ℕ => ENNReal.ofReal (2 * (R / 2 ^ j))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => R / 2 ^ j) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    have h2 := ENNReal.tendsto_ofReal (h1.const_mul 2)
    simpa using h2
  have ht : ∀ᶠ j in atTop, ∀ v, Metric.ediam (t j v) ≤ ENNReal.ofReal (2 * (R / 2 ^ j)) := by
    refine Eventually.of_forall fun j v => (hdiam j v).trans (ENNReal.ofReal_le_ofReal ?_)
    have := Tr.ms7_radius_le v.1 v.2.1
    rw [v.2.2] at this
    linarith
  have hst : ∀ᶠ j in atTop, s ⊆ ⋃ v, t j v := by
    refine Eventually.of_forall fun j z hz => ?_
    obtain ⟨v, hv, hlen, hzv⟩ := ms7_mem_treeResidual.mp hz j
    exact mem_iUnion.mpr ⟨⟨v, hv, hlen⟩, hzv⟩
  have key := Measure.hausdorffMeasure_le_liminf_tsum (k : ℝ) s _ hr t ht hst
  refine le_antisymm (key.trans ?_) zero_le
  -- bound each depth sum by `2^k * ofReal (R^k / 2^j)`, which tends to zero
  have hbound : ∀ j : ℕ, ∑' v, Metric.ediam (t j v) ^ (k : ℝ) ≤
      2 ^ k * ENNReal.ofReal (R ^ k / 2 ^ j) := by
    intro j
    calc ∑' v, Metric.ediam (t j v) ^ (k : ℝ)
        ≤ ∑' v : {v : List ℕ // v ∈ Tr.vertices ∧ v.length = j},
            2 ^ k * ENNReal.ofReal (Tr.radius v ^ k) := by
          refine ENNReal.tsum_le_tsum fun v => ?_
          have hpos : 0 ≤ Tr.radius v := (Tr.radius_pos v.1 v.2.1).le
          calc Metric.ediam (t j v) ^ (k : ℝ) ≤ ENNReal.ofReal (2 * Tr.radius v) ^ (k : ℝ) :=
                ENNReal.rpow_le_rpow (hdiam j v) (Nat.cast_nonneg k)
            _ = 2 ^ k * ENNReal.ofReal (Tr.radius v ^ k) := by
                rw [ENNReal.rpow_natCast, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
                  ENNReal.ofReal_ofNat,
                  mul_pow, ENNReal.ofReal_pow hpos]
      _ = 2 ^ k * ∑' v : {v : List ℕ // v ∈ Tr.vertices ∧ v.length = j},
            ENNReal.ofReal (Tr.radius v ^ k) := ENNReal.tsum_mul_left
      _ ≤ 2 ^ k * ENNReal.ofReal (R ^ k / 2 ^ j) := by gcongr; exact Tr.ms7_depth_sum_le j
  have hlim : Tendsto (fun j : ℕ => 2 ^ k * ENNReal.ofReal (R ^ k / 2 ^ j)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => R ^ k / 2 ^ j) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    have h2 := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal h1)
      (Or.inr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) : (ENNReal.ofReal 0) ≠ 0 ∨ (2 : ℝ≥0∞) ^ k ≠ ⊤)
    simpa using h2
  calc liminf (fun j => ∑' v, Metric.ediam (t j v) ^ (k : ℝ)) atTop
      ≤ liminf (fun j : ℕ => 2 ^ k * ENNReal.ofReal (R ^ k / 2 ^ j)) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = 0 := hlim.liminf_eq

end StepTree

end ParabolicRectifiability
