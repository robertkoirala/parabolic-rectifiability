import ParabolicRectifiability.Measure.Neck.Construction
import ParabolicRectifiability.Measure.Neck.Certificates

/-!
# The step tree by recursion

Given
a step function producing, for every admissible source `ν|S` in a container `P(q,R)`, a
neck, a contracting step with positive child radii, the step identity and the vertex
certificate, apply it at the root and recursively at every child source. The child
measure is the restriction of the original measure to the child source, so the original
bound `B` is inherited (`allScaleEnergy_restrict_le_original`).

Vertices are finite sequences of child indices. The data at a vertex `v` are computed by
structural recursion on the reversed list `v.reverse` (`(v ++ [i]).reverse = i :: v.reverse`),
and `v` is a vertex when every index of `v` is a child index of the step at the preceding
prefix. Off the vertex set the data are irrelevant (the step function is applied only to
admissible children; otherwise the parent datum is repeated).
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-- The step-function hypothesis of `exists_stepTree_of_positive_proof`. -/
def MS6StepFn (n : ℕ) (Eerr ρ ε L : ℝ) (k : ℕ) (F : FamilyKind) : Prop :=
  ∀ (q : Space n) (R B : ℝ) (ν : Measure (Space n)) (S : Set (Space n)),
    0 < R → 0 < B → IsFiniteMeasure ν → MeasurableSet S → S ⊆ Metric.ball q R →
    ν Sᶜ = 0 →
    (∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B) →
    ∃ (T : NeckType) (ι : Type) (Cd Cs σ δ E κ θ γ : ℝ)
      (N : NeckRegion n k T ι q R (1 / 20) Cd Cs σ δ E κ θ γ)
      (D : ContractingStep ν S N B Eerr ρ ε),
      (F = .mixed ∨ F = T.toFamilyKind) ∧
        ν = ν.restrict D.errorSet + ν.restrict D.coreSet +
          Measure.sum (fun w : D.childIndex => ν.restrict (D.childSource w)) ∧
        N.IsCertified ν B B L ∧
        (F ≠ .mixed →
          ∀ w ∈ D.childIndex, D.childRadius w = 3 * ρ * N.radius (D.childParent w)) ∧
        ∀ w ∈ D.childIndex, 0 < D.childRadius w

/-- One vertex datum: container, source, retained neck and contracting step for the
restricted source `ν|source`. -/
structure MS6Node (n k : ℕ) (ν : Measure (Space n)) (B Eerr ρ ε : ℝ) where
  center : Space n
  radius : ℝ
  source : Set (Space n)
  vneck : VertexNeck n k center radius
  step : ContractingStep (ν.restrict source) source vneck.neck B Eerr ρ ε

section Recursion

variable {n k : ℕ} {F : FamilyKind} {ν : Measure (Space n)} {B Eerr ρ ε L : ℝ}

/-- The hypotheses of the step function for the restricted source `ν|S'` in `P(q,R)`. -/
def ms6StepHyp (ν : Measure (Space n)) (k : ℕ) (F : FamilyKind) (B : ℝ) (q : Space n)
    (R : ℝ) (S' : Set (Space n)) : Prop :=
  0 < R ∧ 0 < B ∧ IsFiniteMeasure (ν.restrict S') ∧ MeasurableSet S' ∧
    S' ⊆ Metric.ball q R ∧ (ν.restrict S') S'ᶜ = 0 ∧
    ∀ z ∈ S', allScaleEnergy (ν.restrict S') k F z ≤ ENNReal.ofReal B

/-- The outputs of the step function retained at a node. -/
def MS6Node.Out (F : FamilyKind) (L : ℝ) (nd : MS6Node n k ν B Eerr ρ ε) : Prop :=
  (F = .mixed ∨ F = nd.vneck.type.toFamilyKind) ∧
    ν.restrict nd.source = (ν.restrict nd.source).restrict nd.step.errorSet +
      (ν.restrict nd.source).restrict nd.step.coreSet +
      Measure.sum (fun w : nd.step.childIndex =>
        (ν.restrict nd.source).restrict (nd.step.childSource w)) ∧
    nd.vneck.neck.IsCertified (ν.restrict nd.source) B B L ∧
    ∀ w ∈ nd.step.childIndex, 0 < nd.step.childRadius w

/-- The step function applied to an admissible restricted source gives a node. -/
theorem ms6_exists_node (hstep : MS6StepFn n Eerr ρ ε L k F) {q : Space n} {R : ℝ}
    {S' : Set (Space n)} (h : ms6StepHyp ν k F B q R S') :
    ∃ nd : MS6Node n k ν B Eerr ρ ε, nd.center = q ∧ nd.radius = R ∧ nd.source = S' ∧
      nd.Out F L := by
  obtain ⟨hR, hB, hfin, hSm, hSq, hSn, hSB⟩ := h
  obtain ⟨T, ι, Cd, Cs, σ, δ, E, κ, θ, γ, N, D, hFT, hid, hcert, -, hpos⟩ :=
    hstep q R B (ν.restrict S') S' hR hB hfin hSm hSq hSn hSB
  exact ⟨⟨q, R, S', ⟨T, ι, Cd, Cs, σ, δ, E, κ, θ, γ, N⟩, D⟩, rfl, rfl, rfl,
    hFT, hid, hcert, hpos⟩

open Classical in
/-- The datum of the child `i` of a node: the step function applied to the child source,
when it is admissible (otherwise the parent datum, never used on vertices). -/
def ms6Next (hstep : MS6StepFn n Eerr ρ ε L k F) (nd : MS6Node n k ν B Eerr ρ ε) (i : ℕ) :
    MS6Node n k ν B Eerr ρ ε :=
  if h : ms6StepHyp ν k F B (nd.step.childCenter i) (nd.step.childRadius i)
      (nd.step.childSource i) then
    Classical.choose (ms6_exists_node hstep h)
  else nd

/-- The datum at the vertex with reversed index list `l`. -/
def ms6NodeRev (hstep : MS6StepFn n Eerr ρ ε L k F) (root : MS6Node n k ν B Eerr ρ ε) :
    List ℕ → MS6Node n k ν B Eerr ρ ε
  | [] => root
  | i :: l => ms6Next hstep (ms6NodeRev hstep root l) i

/-- The reversed list `l` is a path of child indices from the root. -/
def ms6ValidRev (hstep : MS6StepFn n Eerr ρ ε L k F) (root : MS6Node n k ν B Eerr ρ ε) :
    List ℕ → Prop
  | [] => True
  | i :: l => ms6ValidRev hstep root l ∧ i ∈ (ms6NodeRev hstep root l).step.childIndex

/-- The invariant of the recursion at a node. -/
def MS6Node.Good (F : FamilyKind) (L : ℝ) (S : Set (Space n)) (nd : MS6Node n k ν B Eerr ρ ε) :
    Prop :=
  ms6StepHyp ν k F B nd.center nd.radius nd.source ∧ nd.source ⊆ S ∧ nd.Out F L

/-- The children of a good node are admissible, and their data are good. -/
theorem ms6_good_next (hstep : MS6StepFn n Eerr ρ ε L k F) {S : Set (Space n)}
    [IsFiniteMeasure ν] (hSB : ∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B)
    {nd : MS6Node n k ν B Eerr ρ ε} (hnd : nd.Good F L S) {i : ℕ}
    (hi : i ∈ nd.step.childIndex) :
    (ms6Next hstep nd i).Good F L S ∧
      (ms6Next hstep nd i).center = nd.step.childCenter i ∧
      (ms6Next hstep nd i).radius = nd.step.childRadius i ∧
      (ms6Next hstep nd i).source = nd.step.childSource i := by
  obtain ⟨⟨-, hB, -⟩, hsub, -, -, -, hpos⟩ := hnd
  have hm : MeasurableSet (nd.step.childSource i) := nd.step.measurableSet_childSource i hi
  have h : ms6StepHyp ν k F B (nd.step.childCenter i) (nd.step.childRadius i)
      (nd.step.childSource i) := by
    refine ⟨hpos i hi, hB, inferInstance, hm, nd.step.childSource_subset_ball i hi, ?_, ?_⟩
    · rw [Measure.restrict_apply hm.compl, Set.compl_inter_self, measure_empty]
    · intro z hz
      exact (allScaleEnergy_restrict_le_original ν _ k F z).trans
        (hSB z (hsub (nd.step.childSource_subset i hi hz)))
  have hnext : ms6Next hstep nd i = Classical.choose (ms6_exists_node hstep h) := by
    unfold ms6Next
    rw [dite_eq_left h]
  obtain ⟨hc, hr, hs, hout⟩ := Classical.choose_spec (ms6_exists_node hstep h)
  rw [hnext]
  refine ⟨⟨?_, ?_, hout⟩, hc, hr, hs⟩
  · rw [hc, hr, hs]
    exact h
  · rw [hs]
    exact (nd.step.childSource_subset i hi).trans hsub

/-- Every vertex datum is good. -/
theorem ms6_good_of_valid (hstep : MS6StepFn n Eerr ρ ε L k F) {S : Set (Space n)}
    [IsFiniteMeasure ν] (hSB : ∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B)
    {root : MS6Node n k ν B Eerr ρ ε} (hroot : root.Good F L S) :
    ∀ l : List ℕ, ms6ValidRev hstep root l → (ms6NodeRev hstep root l).Good F L S
  | [], _ => hroot
  | _ :: l, hv => (ms6_good_next hstep hSB (ms6_good_of_valid hstep hSB hroot l hv.1) hv.2).1

theorem ms6_reverse_append (v : List ℕ) (i : ℕ) : (v ++ [i]).reverse = i :: v.reverse := by
  simp

end Recursion

section Tree

variable {n k : ℕ} {F : FamilyKind} {ν : Measure (Space n)} {B Eerr ρ ε L : ℝ}
  {S : Set (Space n)} {q : Space n} {R : ℝ}

theorem ms6_valid_append (hstep : MS6StepFn n Eerr ρ ε L k F)
    (root : MS6Node n k ν B Eerr ρ ε) (v : List ℕ) (i : ℕ) :
    ms6ValidRev hstep root (v ++ [i]).reverse ↔
      ms6ValidRev hstep root v.reverse ∧
        i ∈ (ms6NodeRev hstep root v.reverse).step.childIndex := by
  rw [ms6_reverse_append]
  exact Iff.rfl

theorem ms6_node_append (hstep : MS6StepFn n Eerr ρ ε L k F)
    (root : MS6Node n k ν B Eerr ρ ε) (v : List ℕ) (i : ℕ) :
    ms6NodeRev hstep root (v ++ [i]).reverse =
      ms6Next hstep (ms6NodeRev hstep root v.reverse) i := by
  rw [ms6_reverse_append]
  rfl

/-- The datum of the vertex `v ++ [i]` is the child `i` of the step at `v`. -/
theorem ms6_child_facts (hstep : MS6StepFn n Eerr ρ ε L k F) [IsFiniteMeasure ν]
    (hSB : ∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B)
    {root : MS6Node n k ν B Eerr ρ ε} (hroot : root.Good F L S) {v : List ℕ}
    (hv : ms6ValidRev hstep root v.reverse) {i : ℕ}
    (hi : i ∈ (ms6NodeRev hstep root v.reverse).step.childIndex) :
    (ms6NodeRev hstep root (v ++ [i]).reverse).center =
        (ms6NodeRev hstep root v.reverse).step.childCenter i ∧
      (ms6NodeRev hstep root (v ++ [i]).reverse).radius =
        (ms6NodeRev hstep root v.reverse).step.childRadius i ∧
      (ms6NodeRev hstep root (v ++ [i]).reverse).source =
        (ms6NodeRev hstep root v.reverse).step.childSource i := by
  rw [ms6_node_append]
  exact (ms6_good_next hstep hSB (ms6_good_of_valid hstep hSB hroot _ hv) hi).2

theorem ms6_tree_cover (hstep : MS6StepFn n Eerr ρ ε L k F) [IsFiniteMeasure ν]
    (hSB : ∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B)
    {root : MS6Node n k ν B Eerr ρ ε} (hroot : root.Good F L S) {v : List ℕ}
    (hv : ms6ValidRev hstep root v.reverse) :
    (ms6NodeRev hstep root v.reverse).source ⊆
      (ms6NodeRev hstep root v.reverse).step.errorSet ∪
        (ms6NodeRev hstep root v.reverse).step.coreSet ∪
        ⋃ (i : ℕ) (_ : ms6ValidRev hstep root (v ++ [i]).reverse),
          (ms6NodeRev hstep root (v ++ [i]).reverse).source := by
  intro z hz
  rcases (ms6NodeRev hstep root v.reverse).step.cover hz with h | h
  · exact Or.inl h
  · obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp h
    refine Or.inr (Set.mem_iUnion₂.mpr ⟨w, (ms6_valid_append hstep root v w).mpr ⟨hv, hw⟩, ?_⟩)
    rw [(ms6_child_facts hstep hSB hroot hv hw).2.2]
    exact hzw

theorem ms6_tree_child_subset (hstep : MS6StepFn n Eerr ρ ε L k F) [IsFiniteMeasure ν]
    (hSB : ∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B)
    {root : MS6Node n k ν B Eerr ρ ε} (hroot : root.Good F L S) {v : List ℕ} {i : ℕ}
    (h : ms6ValidRev hstep root (v ++ [i]).reverse) :
    (ms6NodeRev hstep root (v ++ [i]).reverse).source ⊆
      (ms6NodeRev hstep root v.reverse).source := by
  obtain ⟨hv, hi⟩ := (ms6_valid_append hstep root v i).mp h
  rw [(ms6_child_facts hstep hSB hroot hv hi).2.2]
  exact (ms6NodeRev hstep root v.reverse).step.childSource_subset i hi

theorem ms6_tree_disjoint_error (hstep : MS6StepFn n Eerr ρ ε L k F) [IsFiniteMeasure ν]
    (hSB : ∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B)
    {root : MS6Node n k ν B Eerr ρ ε} (hroot : root.Good F L S) {v : List ℕ} {i : ℕ}
    (h : ms6ValidRev hstep root (v ++ [i]).reverse) :
    Disjoint (ms6NodeRev hstep root v.reverse).step.errorSet
      (ms6NodeRev hstep root (v ++ [i]).reverse).source := by
  obtain ⟨hv, hi⟩ := (ms6_valid_append hstep root v i).mp h
  rw [(ms6_child_facts hstep hSB hroot hv hi).2.2]
  exact (ms6NodeRev hstep root v.reverse).step.disjoint_errorSet_child i hi

theorem ms6_tree_disjoint_core (hstep : MS6StepFn n Eerr ρ ε L k F) [IsFiniteMeasure ν]
    (hSB : ∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B)
    {root : MS6Node n k ν B Eerr ρ ε} (hroot : root.Good F L S) {v : List ℕ} {i : ℕ}
    (h : ms6ValidRev hstep root (v ++ [i]).reverse) :
    Disjoint (ms6NodeRev hstep root v.reverse).step.coreSet
      (ms6NodeRev hstep root (v ++ [i]).reverse).source := by
  obtain ⟨hv, hi⟩ := (ms6_valid_append hstep root v i).mp h
  rw [(ms6_child_facts hstep hSB hroot hv hi).2.2]
  exact (ms6NodeRev hstep root v.reverse).step.disjoint_coreSet_child i hi

theorem ms6_tree_disjoint_children (hstep : MS6StepFn n Eerr ρ ε L k F) [IsFiniteMeasure ν]
    (hSB : ∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B)
    {root : MS6Node n k ν B Eerr ρ ε} (hroot : root.Good F L S) {v : List ℕ} {i j : ℕ}
    (h : ms6ValidRev hstep root (v ++ [i]).reverse)
    (h' : ms6ValidRev hstep root (v ++ [j]).reverse) (hij : i ≠ j) :
    Disjoint (ms6NodeRev hstep root (v ++ [i]).reverse).source
      (ms6NodeRev hstep root (v ++ [j]).reverse).source := by
  obtain ⟨hv, hi⟩ := (ms6_valid_append hstep root v i).mp h
  obtain ⟨-, hj⟩ := (ms6_valid_append hstep root v j).mp h'
  rw [(ms6_child_facts hstep hSB hroot hv hi).2.2, (ms6_child_facts hstep hSB hroot hv hj).2.2]
  exact (ms6NodeRev hstep root v.reverse).step.disjoint_children i hi j hj hij

theorem ms6_tree_errorSet_le (hstep : MS6StepFn n Eerr ρ ε L k F)
    (root : MS6Node n k ν B Eerr ρ ε) (v : List ℕ) :
    ν (ms6NodeRev hstep root v.reverse).step.errorSet ≤
      ENNReal.ofReal (Eerr * B * (ms6NodeRev hstep root v.reverse).radius ^ k) := by
  have h := (ms6NodeRev hstep root v.reverse).step.errorSet_le
  rw [Measure.restrict_apply (ms6NodeRev hstep root v.reverse).step.measurableSet_errorSet,
    Set.inter_eq_left.mpr (ms6NodeRev hstep root v.reverse).step.errorSet_subset] at h
  exact h

theorem ms6_tree_child_radius_le (hstep : MS6StepFn n Eerr ρ ε L k F) [IsFiniteMeasure ν]
    (hSB : ∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B)
    {root : MS6Node n k ν B Eerr ρ ε} (hroot : root.Good F L S) {v : List ℕ} {i : ℕ}
    (h : ms6ValidRev hstep root (v ++ [i]).reverse) :
    (ms6NodeRev hstep root (v ++ [i]).reverse).radius ≤
      (ms6NodeRev hstep root v.reverse).radius / 2 := by
  obtain ⟨hv, hi⟩ := (ms6_valid_append hstep root v i).mp h
  rw [(ms6_child_facts hstep hSB hroot hv hi).2.1]
  exact (ms6NodeRev hstep root v.reverse).step.childRadius_le i hi

theorem ms6_tree_child_content_le (hstep : MS6StepFn n Eerr ρ ε L k F) [IsFiniteMeasure ν]
    (hSB : ∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B)
    {root : MS6Node n k ν B Eerr ρ ε} (hroot : root.Good F L S) {v : List ℕ}
    (hv : ms6ValidRev hstep root v.reverse) :
    ∑' i : {i : ℕ // ms6ValidRev hstep root (v ++ [i]).reverse},
        ENNReal.ofReal ((ms6NodeRev hstep root (v ++ [i.1]).reverse).radius ^ k) ≤
      ENNReal.ofReal ((ms6NodeRev hstep root v.reverse).radius ^ k / 2) := by
  have hiff : ∀ i, ms6ValidRev hstep root (v ++ [i]).reverse ↔
      i ∈ (ms6NodeRev hstep root v.reverse).step.childIndex := fun i => by
    rw [ms6_valid_append]
    exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  calc ∑' i : {i : ℕ // ms6ValidRev hstep root (v ++ [i]).reverse},
        ENNReal.ofReal ((ms6NodeRev hstep root (v ++ [i.1]).reverse).radius ^ k)
      = ∑' i : {i : ℕ // ms6ValidRev hstep root (v ++ [i]).reverse},
          ENNReal.ofReal ((ms6NodeRev hstep root v.reverse).step.childRadius i.1 ^ k) := by
        refine tsum_congr fun i => ?_
        rw [(ms6_child_facts hstep hSB hroot hv ((hiff i.1).mp i.2)).2.1]
    _ = ∑' w : (ms6NodeRev hstep root v.reverse).step.childIndex,
          ENNReal.ofReal ((ms6NodeRev hstep root v.reverse).step.childRadius w ^ k) :=
        (Equiv.subtypeEquivRight hiff).tsum_eq
          (fun w : (ms6NodeRev hstep root v.reverse).step.childIndex =>
            ENNReal.ofReal ((ms6NodeRev hstep root v.reverse).step.childRadius w ^ k))
    _ ≤ ENNReal.ofReal ((ms6NodeRev hstep root v.reverse).radius ^ k / 2) :=
        (ms6NodeRev hstep root v.reverse).step.child_content_le

/-- The step tree generated from a good root datum. -/
def ms6Tree (hstep : MS6StepFn n Eerr ρ ε L k F) [IsFiniteMeasure ν]
    (hSB : ∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B)
    (root : MS6Node n k ν B Eerr ρ ε) (hroot : root.Good F L S) (hc : root.center = q)
    (hr : root.radius = R) (hs : root.source = S) : StepTree ν k F S q R B Eerr ρ ε where
  vertices := {v | ms6ValidRev hstep root v.reverse}
  root_mem := trivial
  parent_mem := fun v i h => ((ms6_valid_append hstep root v i).mp h).1
  source := fun v => (ms6NodeRev hstep root v.reverse).source
  center := fun v => (ms6NodeRev hstep root v.reverse).center
  radius := fun v => (ms6NodeRev hstep root v.reverse).radius
  vneck := fun v => (ms6NodeRev hstep root v.reverse).vneck
  step := fun v => (ms6NodeRev hstep root v.reverse).step
  source_root := hs
  center_root := hc
  radius_root := hr
  measurableSet_source := fun _ hv => (ms6_good_of_valid hstep hSB hroot _ hv).1.2.2.2.1
  radius_pos := fun _ hv => (ms6_good_of_valid hstep hSB hroot _ hv).1.1
  source_subset_ball := fun _ hv => (ms6_good_of_valid hstep hSB hroot _ hv).1.2.2.2.2.1
  energy_le := fun _ hv => (ms6_good_of_valid hstep hSB hroot _ hv).1.2.2.2.2.2.2
  family := fun _ hv => (ms6_good_of_valid hstep hSB hroot _ hv).2.2.1
  step_measure_eq := fun _ hv => (ms6_good_of_valid hstep hSB hroot _ hv).2.2.2.1
  child_mem_iff := fun v hv i => (ms6_valid_append hstep root v i).trans
    ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  child_source := fun _ hv _ hi => (ms6_child_facts hstep hSB hroot hv hi).2.2
  child_center := fun _ hv _ hi => (ms6_child_facts hstep hSB hroot hv hi).1
  child_radius := fun _ hv _ hi => (ms6_child_facts hstep hSB hroot hv hi).2.1
  child_subset := fun _ _ h => ms6_tree_child_subset hstep hSB hroot h
  cover := fun _ hv => ms6_tree_cover hstep hSB hroot hv
  disjoint_errorSet_child := fun _ _ h => ms6_tree_disjoint_error hstep hSB hroot h
  disjoint_coreSet_child := fun _ _ h => ms6_tree_disjoint_core hstep hSB hroot h
  disjoint_children := fun _ _ _ h h' hij => ms6_tree_disjoint_children hstep hSB hroot h h' hij
  errorSet_le := fun v _ => ms6_tree_errorSet_le hstep root v
  child_radius_le := fun _ _ h => ms6_tree_child_radius_le hstep hSB hroot h
  child_content_le := fun _ hv => ms6_tree_child_content_le hstep hSB hroot hv

end Tree

/-- **`exists_stepTree_of_positive`**: the step tree is obtained by recursion from a step
function with positive child radii. -/
theorem exists_stepTree_of_positive_proof (n : ℕ) :
    ∀ (Eerr ρ ε L : ℝ) (k : ℕ) (F : FamilyKind),
      (∀ (q : Space n) (R B : ℝ) (ν : Measure (Space n)) (S : Set (Space n)),
        0 < R → 0 < B → IsFiniteMeasure ν → MeasurableSet S → S ⊆ Metric.ball q R →
        ν Sᶜ = 0 →
        (∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B) →
        ∃ (T : NeckType) (ι : Type) (Cd Cs σ δ E κ θ γ : ℝ)
          (N : NeckRegion n k T ι q R (1 / 20) Cd Cs σ δ E κ θ γ)
          (D : ContractingStep ν S N B Eerr ρ ε),
          (F = .mixed ∨ F = T.toFamilyKind) ∧
            ν = ν.restrict D.errorSet + ν.restrict D.coreSet +
              Measure.sum (fun w : D.childIndex => ν.restrict (D.childSource w)) ∧
            N.IsCertified ν B B L ∧
            (F ≠ .mixed →
              ∀ w ∈ D.childIndex, D.childRadius w = 3 * ρ * N.radius (D.childParent w)) ∧
            ∀ w ∈ D.childIndex, 0 < D.childRadius w) →
      ∀ (q : Space n) (R B : ℝ) (ν : Measure (Space n)) (S : Set (Space n)),
        0 < R → 0 < B → IsFiniteMeasure ν → MeasurableSet S → S ⊆ Metric.ball q R →
        ν Sᶜ = 0 → (∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B) →
        ∃ Tr : StepTree ν k F S q R B Eerr ρ ε,
          ∀ v ∈ Tr.vertices, (Tr.vneck v).neck.IsCertified (ν.restrict (Tr.source v)) B B L := by
  intro Eerr ρ ε L k F hstep q R B ν S hR hB hν hSm hSq _ hSB
  have hroot : ms6StepHyp ν k F B q R S := by
    refine ⟨hR, hB, inferInstance, hSm, hSq, ?_, ?_⟩
    · rw [Measure.restrict_apply hSm.compl, Set.compl_inter_self, measure_empty]
    · intro z hz
      exact (allScaleEnergy_restrict_le_original ν S k F z).trans (hSB z hz)
  obtain ⟨root, hc, hr, hs, hout⟩ := ms6_exists_node (L := L) hstep hroot
  have hgood : root.Good F L S := ⟨by rw [hc, hr, hs]; exact hroot, hs.subset, hout⟩
  exact ⟨ms6Tree hstep hSB root hgood hc hr hs,
    fun v hv => (ms6_good_of_valid hstep hSB hgood _ hv).2.2.2.2.1⟩

end ParabolicRectifiability
