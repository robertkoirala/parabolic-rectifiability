import ParabolicRectifiability.Measure.Neck.DecompositionTree.TreeDepth
import ParabolicRectifiability.Measure.Neck.ConstructionConclusions
import ParabolicRectifiability.Measure.Neck.Certificates

/-!
# Closure identity and carrier facts of the decomposition tree

Proofs of three statements about the subtree sets of a decomposition tree:

* `StepTree.subtreeSet_closure_subset_proof` (`StepTree.subtreeSet_closure_subset`): the
  certificate `(ν|S_u)(P(z,r)) ≥ B r^k / L > 0` puts every core `C_u` in `closure S_u`,
  hence `K_v = closure D_v ⊆ closure S_v`;
* `StepTree.subtreeSet_closure_identity_proof` (`StepTree.subtreeSet_closure_identity`):
  `K_v ⊆ C_v ∪ ⋃_w K_w`;
* `StepTree.carrier_facts_of_subtree_proof` (`StepTree.carrier_facts_of_subtree`): compactness
  of the carrier, `K ⊆ closure P(q,R)`, and `H^k_P(K \ ⋃_v C_v) = 0`, taking the two
  statements above and the nullity of the closed container as hypotheses.

For the closure identity we use `D_v ⊆ C_v ∪ ⋃_w D_w` (set identity of the subtree sets; residual points of
`S_v` descend to a child source). If `z ∈ K_v \ C_v`, then `z` lies in the closure of the
union of the child sets, and a ball `P(z, η)` meets only the child sets of finitely many
stopping holes: if `z` is a stopping center, stopping separation forces nearby holes to have
radius `≥ c₀ d_z / 2`; if `z` is not a center, compactness of the center set forces radius
`≥ η`; the total content bound of the certificate allows only finitely many holes of radius
above a positive threshold, and each hole has finitely many children. Child subtree sets lie
in the closed parent holes (by the closure inclusion and parent-hole containment), so the closure of the union is
the finite union of the closures near `z`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

/-- Near a point outside the core of a neck, only finitely many stopping holes come close:
there are `η > 0` and a finite set `P` containing every stopping center `c` with
`d_P(z, c) < η + d_c`. -/
theorem ms7_near_stopping_finite {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n}
    {R c₀ Cd Cs σ δ E κ θ γ L : ℝ} (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ)
    (hcont : N.HasTotalContentBound L) {z : Space n} (hz : z ∉ N.core) :
    ∃ η > 0, ∃ P : Set (Space n), P.Finite ∧
      ∀ c ∈ N.stopping, dist z c < η + N.radius c → c ∈ P := by
  have hmem : ∀ c, c ∈ N.stopping ↔ c ∈ N.centers ∧ 0 < N.radius c := fun _ => Iff.rfl
  -- finitely many stopping centers have radius at least a positive threshold
  have hfin : ∀ t : ℝ, 0 < t → {c | c ∈ N.stopping ∧ t ≤ N.radius c}.Finite := by
    intro t ht
    have hsum : ∑' c : ↥N.stopping, ENNReal.ofReal (N.radius c ^ k) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_add_self hcont)
    have hf := ENNReal.finite_const_le_of_tsum_ne_top hsum
      (ENNReal.ofReal_pos.mpr (pow_pos ht k)).ne'
    refine (hf.image Subtype.val).subset ?_
    rintro c ⟨hc, htc⟩
    exact ⟨⟨c, hc⟩, ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht.le htc k), rfl⟩
  have hc₀ : 0 < c₀ := N.parameters.c₀_pos
  by_cases hzc : z ∈ N.centers
  · have hz0 : 0 < N.radius z := by
      rcases (N.radius_nonneg z hzc).lt_or_eq with h | h
      · exact h
      · exact absurd ⟨hzc, h.symm⟩ hz
    have ht : 0 < c₀ * N.radius z / 2 := by positivity
    refine ⟨c₀ * N.radius z / 2, ht,
      insert z {c | c ∈ N.stopping ∧ c₀ * N.radius z / 2 ≤ N.radius c}, (hfin _ ht).insert z, ?_⟩
    intro c hc hdist
    by_cases hcz : c = z
    · rw [hcz]; exact Set.mem_insert _ _
    refine Set.mem_insert_of_mem _ ⟨hc, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hc' := (hmem c).mp hc
    have hsep := N.stop_separation z hzc c hc'.1 hz0 hc'.2 (Ne.symm hcz)
    have hmax : c₀ * N.radius z ≤ c₀ * max (N.radius z) (N.radius c) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hc₀.le
    linarith
  · obtain ⟨r, hr, hball⟩ :=
      Metric.isOpen_iff.mp N.isCompact_centers.isClosed.isOpen_compl z hzc
    refine ⟨r / 2, by positivity, {c | c ∈ N.stopping ∧ r / 2 ≤ N.radius c},
      hfin _ (by positivity), ?_⟩
    intro c hc hdist
    refine ⟨hc, ?_⟩
    have hge : r ≤ dist z c := by
      by_contra hlt
      rw [not_le] at hlt
      exact hball (Metric.mem_ball'.mpr hlt) ((hmem c).mp hc).1
    linarith

namespace StepTree

variable {n k : ℕ} {F : FamilyKind} {S : Set (Space n)} {q : Space n} {R B Eerr ρ ε : ℝ}
  {ν : Measure (Space n)}

/-- A certified core lies in the closure of its vertex source. -/
theorem ms7_core_subset_closure_source (Tr : StepTree ν k F S q R B Eerr ρ ε) {L : ℝ}
    (hB : 0 < B) (hL : 0 < L)
    (hcert : ∀ v ∈ Tr.vertices,
      (Tr.vneck v).neck.IsCertified (ν.restrict (Tr.source v)) B B L)
    {u : List ℕ} (hu : u ∈ Tr.vertices) : (Tr.vneck u).neck.core ⊆ closure (Tr.source u) := by
  intro z hz
  rw [Metric.mem_closure_iff]
  intro δ hδ
  have hr : 0 < min δ (Tr.radius u) := lt_min hδ (Tr.radius_pos u hu)
  have hlow := (hcert u hu).core_lower z hz (min δ (Tr.radius u)) hr (min_le_right _ _)
  have hpos : 0 < ENNReal.ofReal (B * min δ (Tr.radius u) ^ k / L) :=
    ENNReal.ofReal_pos.mpr (div_pos (mul_pos hB (pow_pos hr k)) hL)
  have hne : ν.restrict (Tr.source u) (Metric.ball z (min δ (Tr.radius u))) ≠ 0 :=
    (hpos.trans_le hlow).ne'
  rw [Measure.restrict_apply measurableSet_ball] at hne
  obtain ⟨y, hyb, hys⟩ := nonempty_of_measure_ne_zero hne
  exact ⟨y, hys, lt_of_lt_of_le (Metric.mem_ball'.mp hyb) (min_le_left _ _)⟩

/-- `D_v ⊆ closure S_v`. -/
theorem ms7_subtreeSet_subset_closure (Tr : StepTree ν k F S q R B Eerr ρ ε) {L : ℝ}
    (hB : 0 < B) (hL : 0 < L)
    (hcert : ∀ v ∈ Tr.vertices,
      (Tr.vneck v).neck.IsCertified (ν.restrict (Tr.source v)) B B L)
    {v : List ℕ} (_hv : v ∈ Tr.vertices) : Tr.subtreeSet v ⊆ closure (Tr.source v) := by
  intro z hz
  simp only [StepTree.subtreeSet, mem_union, mem_iUnion, mem_inter_iff] at hz
  rcases hz with ⟨u, hu, hvu, hzu⟩ | ⟨-, hz⟩
  · exact closure_mono (Tr.ms7_source_subset_of_prefix hvu hu)
      (Tr.ms7_core_subset_closure_source hB hL hcert hu hzu)
  · exact subset_closure hz

/-- **`StepTree.subtreeSet_closure_subset`**:
`K_v = closure D_v ⊆ closure S_v`. -/
theorem subtreeSet_closure_subset_proof {n k : ℕ} {F : FamilyKind} {S : Set (Space n)}
    {q : Space n} {R B Eerr ρ ε L : ℝ} {ν : Measure (Space n)}
    (Tr : StepTree ν k F S q R B Eerr ρ ε) (_hR : 0 < R) (hB : 0 < B) (hL : 0 < L)
    (hcert : ∀ v ∈ Tr.vertices,
      (Tr.vneck v).neck.IsCertified (ν.restrict (Tr.source v)) B B L) :
    ∀ v ∈ Tr.vertices, closure (Tr.subtreeSet v) ⊆ closure (Tr.source v) :=
  fun _ hv => closure_minimal (Tr.ms7_subtreeSet_subset_closure hB hL hcert hv) isClosed_closure

/-- The subtree set of a child lies in the closed parent hole. -/
theorem ms7_closure_subtree_child_subset (Tr : StepTree ν k F S q R B Eerr ρ ε) {L : ℝ}
    (hB : 0 < B) (hL : 0 < L)
    (hcert : ∀ v ∈ Tr.vertices,
      (Tr.vneck v).neck.IsCertified (ν.restrict (Tr.source v)) B B L)
    {v : List ℕ} (hv : v ∈ Tr.vertices) {i : ℕ} (hi : v ++ [i] ∈ Tr.vertices) :
    closure (Tr.subtreeSet (v ++ [i])) ⊆ Metric.closedBall ((Tr.step v).childParent i)
      ((Tr.vneck v).neck.radius ((Tr.step v).childParent i)) := by
  have hiC : i ∈ (Tr.step v).childIndex := (Tr.child_mem_iff v hv i).mp hi
  refine closure_minimal ((Tr.ms7_subtreeSet_subset_closure hB hL hcert hi).trans ?_)
    Metric.isClosed_closedBall
  rw [Tr.child_source v hv i hiC]
  exact (closure_mono ((Tr.step v).childSource_subset_hole i hiC)).trans
    Metric.closure_ball_subset_closedBall

/-- The set identity `D_v ⊆ C_v ∪ ⋃_w D_w` over the tree children `w` of `v`. -/
theorem ms7_subtreeSet_subset (Tr : StepTree ν k F S q R B Eerr ρ ε) {v : List ℕ}
    (hv : v ∈ Tr.vertices) :
    Tr.subtreeSet v ⊆ (Tr.vneck v).neck.core ∪
      ⋃ (i : ℕ) (_ : v ++ [i] ∈ Tr.vertices), Tr.subtreeSet (v ++ [i]) := by
  intro z hz
  simp only [StepTree.subtreeSet, mem_union, mem_iUnion, mem_inter_iff] at hz
  rcases hz with ⟨u, hu, hvu, hzu⟩ | ⟨hzA, hzS⟩
  · obtain ⟨w, rfl⟩ := hvu
    rcases w with _ | ⟨i, w⟩
    · left; rwa [List.append_nil] at hzu
    · right
      have hpre : v ++ [i] <+: v ++ i :: w := ⟨w, by simp⟩
      refine mem_iUnion₂.mpr ⟨i, Tr.ms7_mem_of_prefix hpre hu, ?_⟩
      simp only [StepTree.subtreeSet, mem_union, mem_iUnion]
      exact Or.inl ⟨v ++ i :: w, hu, hpre, hzu⟩
  · right
    obtain ⟨i, hi, hzi⟩ := Tr.ms7_residual_descend hv hzA hzS
    refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    simp only [StepTree.subtreeSet, mem_union, mem_inter_iff]
    exact Or.inr ⟨hzA, hzi⟩

/-- **`StepTree.subtreeSet_closure_identity`**:
`K_v ⊆ C_v ∪ ⋃_w K_w` over the tree children `w` of `v`. -/
theorem subtreeSet_closure_identity_proof {n k : ℕ} {F : FamilyKind} {S : Set (Space n)}
    {q : Space n} {R B Eerr ρ ε L : ℝ} {ν : Measure (Space n)}
    (Tr : StepTree ν k F S q R B Eerr ρ ε) (_hR : 0 < R) (hB : 0 < B) (hL : 0 < L)
    (hcert : ∀ v ∈ Tr.vertices,
      (Tr.vneck v).neck.IsCertified (ν.restrict (Tr.source v)) B B L) :
    ∀ v ∈ Tr.vertices, closure (Tr.subtreeSet v) ⊆
      (Tr.vneck v).neck.core ∪
        ⋃ (i : ℕ) (_ : v ++ [i] ∈ Tr.vertices), closure (Tr.subtreeSet (v ++ [i])) := by
  intro v hv z hz
  by_cases hzc : z ∈ (Tr.vneck v).neck.core
  · exact Or.inl hzc
  right
  have hcore_closed : IsClosed (Tr.vneck v).neck.core := (hcert v hv).isCompact_core.isClosed
  -- `z` lies in the closure of the union of the child subtree sets
  have h1 : z ∈ closure (⋃ (i : ℕ) (_ : v ++ [i] ∈ Tr.vertices), Tr.subtreeSet (v ++ [i])) := by
    have h := closure_mono (Tr.ms7_subtreeSet_subset hv) hz
    rw [closure_union, hcore_closed.closure_eq] at h
    exact h.resolve_left hzc
  obtain ⟨η, hη, P, hPfin, hP⟩ :=
    ms7_near_stopping_finite (Tr.vneck v).neck (hcert v hv).totalContent hzc
  obtain ⟨I0, hI0mem⟩ : ∃ I0 : Set ℕ, ∀ i, i ∈ I0 ↔
      i ∈ (Tr.step v).childIndex ∧ (Tr.step v).childParent i ∈ P := ⟨_, fun _ => Iff.rfl⟩
  have hI0 : I0.Finite := by
    refine (hPfin.biUnion fun c _ => (Tr.step v).finite_children c).subset fun i hi => ?_
    obtain ⟨hiC, hiP⟩ := (hI0mem i).mp hi
    exact mem_iUnion₂.mpr ⟨_, hiP, hiC, rfl⟩
  -- the child sets of the other holes avoid `P(z, η)`
  have hfar : ∀ i, v ++ [i] ∈ Tr.vertices → i ∉ I0 →
      Disjoint (Tr.subtreeSet (v ++ [i])) (Metric.ball z η) := by
    intro i hi hiI
    have hiC : i ∈ (Tr.step v).childIndex := (Tr.child_mem_iff v hv i).mp hi
    have hc := (Tr.step v).childParent_mem i hiC
    have hsub := (subset_closure.trans (Tr.ms7_closure_subtree_child_subset hB hL hcert hv hi))
    rw [Set.disjoint_left]
    intro y hy hyb
    apply hiI
    refine (hI0mem i).mpr ⟨hiC, hP _ hc ?_⟩
    have h1 := Metric.mem_closedBall.mp (hsub hy)
    have h2 := Metric.mem_ball'.mp hyb
    linarith [dist_triangle z y ((Tr.step v).childParent i)]
  -- split into the finitely many near children and the far ones
  have hsplit : (⋃ (i : ℕ) (_ : v ++ [i] ∈ Tr.vertices), Tr.subtreeSet (v ++ [i])) ⊆
      (⋃ i ∈ I0, Tr.subtreeSet (v ++ [i])) ∪
        ⋃ (i : ℕ) (_ : v ++ [i] ∈ Tr.vertices ∧ i ∉ I0), Tr.subtreeSet (v ++ [i]) := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
    by_cases hiI : i ∈ I0
    · exact Or.inl (mem_iUnion₂.mpr ⟨i, hiI, hyi⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨i, ⟨hi, hiI⟩, hyi⟩)
  have h2 := closure_mono hsplit h1
  rw [closure_union] at h2
  rcases h2 with h2 | h2
  · rw [hI0.closure_biUnion] at h2
    obtain ⟨i, hiI, hzi⟩ := mem_iUnion₂.mp h2
    exact mem_iUnion₂.mpr ⟨i, (Tr.child_mem_iff v hv i).mpr ((hI0mem i).mp hiI).1, hzi⟩
  · exfalso
    obtain ⟨y, hy, hyz⟩ := Metric.mem_closure_iff.mp h2 η hη
    obtain ⟨i, ⟨hi, hiI⟩, hyi⟩ := mem_iUnion₂.mp hy
    exact Set.disjoint_left.mp (hfar i hi hiI) hyi (Metric.mem_ball'.mpr hyz)

/-- The carrier is the closure of the root subtree set (inclusion). -/
theorem ms7_carrier_subset_closure_subtree (Tr : StepTree ν k F S q R B Eerr ρ ε) :
    Tr.carrier ⊆ closure (Tr.subtreeSet []) := by
  unfold StepTree.carrier
  refine closure_mono ?_
  rintro z (hz | hz)
  · obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.mp hz
    simp only [StepTree.subtreeSet, mem_union, mem_iUnion, mem_inter_iff]
    exact Or.inl ⟨u, hu, List.nil_prefix, hzu⟩
  · simp only [StepTree.subtreeSet, mem_union, mem_iUnion, mem_inter_iff]
    exact Or.inr ⟨hz, Tr.ms7_residual_subset_root hz⟩

/-- **`StepTree.carrier_facts_of_subtree`**: the
carrier is `K_[] ⊆ closure S ⊆ closure P(q,R)`, hence compact; iterating the subtree
closure identity places every point of `K \ ⋃_v C_v` in a closed container at every depth,
where the closed-container intersection is null. -/
theorem carrier_facts_of_subtree_proof {n k : ℕ} {F : FamilyKind} {S : Set (Space n)}
    {q : Space n} {R B Eerr ρ ε : ℝ} {ν : Measure (Space n)}
    (Tr : StepTree ν k F S q R B Eerr ρ ε) (_hR : 0 < R)
    (hsub : ∀ v ∈ Tr.vertices, closure (Tr.subtreeSet v) ⊆ closure (Tr.source v))
    (hid : ∀ v ∈ Tr.vertices, closure (Tr.subtreeSet v) ⊆
      (Tr.vneck v).neck.core ∪
        ⋃ (i : ℕ) (_ : v ++ [i] ∈ Tr.vertices), closure (Tr.subtreeSet (v ++ [i])))
    (hnull : hausdorffP n k
      (treeResidual Tr.vertices fun v => Metric.closedBall (Tr.center v) (Tr.radius v)) = 0) :
    IsCompact Tr.carrier ∧ Tr.carrier ⊆ Metric.closedBall q R ∧
      hausdorffP n k (Tr.carrier \ ⋃ v ∈ Tr.vertices, (Tr.vneck v).neck.core) = 0 := by
  have hcar : Tr.carrier ⊆ closure (Tr.subtreeSet []) := Tr.ms7_carrier_subset_closure_subtree
  have hclosed : ∀ v ∈ Tr.vertices,
      closure (Tr.subtreeSet v) ⊆ Metric.closedBall (Tr.center v) (Tr.radius v) :=
    fun v hv => (hsub v hv).trans ((closure_mono (Tr.source_subset_ball v hv)).trans
      Metric.closure_ball_subset_closedBall)
  have hball : Tr.carrier ⊆ Metric.closedBall q R := by
    have h := hclosed [] Tr.root_mem
    rw [Tr.center_root, Tr.radius_root] at h
    exact hcar.trans h
  have hKclosed : IsClosed Tr.carrier := by
    unfold StepTree.carrier; exact isClosed_closure
  refine ⟨(isCompact_closedBall q R).of_isClosed_subset hKclosed hball, hball, ?_⟩
  refine measure_mono_null ?_ hnull
  rintro z ⟨hzK, hzc⟩
  have key : ∀ j, ∃ v ∈ Tr.vertices, v.length = j ∧ z ∈ closure (Tr.subtreeSet v) := by
    intro j
    induction j with
    | zero => exact ⟨[], Tr.root_mem, rfl, hcar hzK⟩
    | succ j ih =>
      obtain ⟨v, hv, hlen, hzv⟩ := ih
      rcases hid v hv hzv with h | h
      · exact absurd (mem_iUnion₂.mpr ⟨v, hv, h⟩) hzc
      · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp h
        exact ⟨v ++ [i], hi, by simp [hlen], hzi⟩
  rw [ms7_mem_treeResidual]
  intro j
  obtain ⟨v, hv, hlen, hzv⟩ := key j
  exact ⟨v, hv, hlen, hclosed v hv hzv⟩

end StepTree

end ParabolicRectifiability
