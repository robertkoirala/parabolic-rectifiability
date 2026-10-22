import ParabolicRectifiability.Measure.Neck.ConstructionConclusions

/-!
# Children of one contracting step

The children of a contracting step, in two parts. In `StepChildren` the origin map is
defined on the active children only.

* **Existence, `exists_stepChildren_proof`.** The stopping centers of a neck are countable: the
  open balls `P(c, c₀ d_c / 2)` are pairwise disjoint by stopping separation, and the space
  is separable. Each hole has finitely many children, so the pairs (hole, child) are
  countable and inject into `ℕ`. The step error set is `e ∪ ⋃_c discard_c`, the core set is
  the core assignment, and the source identity splits along the Borel hole covers into the
  step identity.
* **Estimates, `stepChildren_estimates_proof`.** With nonnegative constants each stopping center
  contributes discarded mass at most `Q B d_c^k`, `Q = 4 C₁ (A+1) C_b/ρ² + 2 C₂/ε² + A C_b`
  (terminal two tubes, positive-rank collapse, rank-zero discard with `k = 2`); the joint
  stopping content `∑_c d_c^k ≤ C₁ R^k` gives the error bound. The injective origin and the
  per-hole counts give `∑_w R_w^k ≤ C₁ (3^k C_col ρ + 2^k C_ter ε²) R^k ≤ R^k/2`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set Function
open scoped ENNReal NNReal BigOperators

/-! ## Generic reindexing of sums of measures -/

/-- A double sum of measures is the sum over the sigma type. -/
theorem ms6_sum_sigma {α : Type*} [MeasurableSpace α] {ι : Type*} {β : ι → Type*}
    (μ : ∀ i, β i → Measure α) :
    Measure.sum (fun i => Measure.sum (μ i)) = Measure.sum (fun p : Σ i, β i => μ p.1 p.2) := by
  ext s hs
  simp only [Measure.sum_apply _ hs]
  exact (ENNReal.tsum_sigma' (fun p : Σ i, β i => μ p.1 p.2 s)).symm

/-- A sum of measures is invariant under reindexing by an equivalence. -/
theorem ms6_sum_equiv {α : Type*} [MeasurableSpace α] {ι ι' : Type*} (e : ι ≃ ι')
    (μ : ι' → Measure α) : Measure.sum (fun i => μ (e i)) = Measure.sum μ := by
  ext s hs
  simp only [Measure.sum_apply _ hs]
  exact e.tsum_eq (fun i => μ i s)

/-! ## Elementary facts on neck regions -/

section NeckFacts

variable {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n}
  {R c₀ Cd Cs σ δ E κ θ γ : ℝ}

/-- The stopping centers of a neck region are countable: the balls `P(c, c₀ d_c / 2)` are
pairwise disjoint (stopping separation) and nonempty, in a separable space. -/
theorem ms6_stopping_countable (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ) :
    N.stopping.Countable := by
  have hc₀ : 0 < c₀ := N.parameters.c₀_pos
  refine Set.PairwiseDisjoint.countable_of_isOpen
    (s := fun c => Metric.ball c (c₀ * N.radius c / 2)) ?_
    (fun _ _ => Metric.isOpen_ball)
    (fun c hc => ⟨c, Metric.mem_ball_self (div_pos (mul_pos hc₀ hc.2) two_pos)⟩)
  intro c hc c' hc' hne
  have hsep := N.stop_separation c hc.1 c' hc'.1 hc.2 hc'.2 hne
  have h1 := mul_le_mul_of_nonneg_left (le_max_left (N.radius c) (N.radius c')) hc₀.le
  have h2 := mul_le_mul_of_nonneg_left (le_max_right (N.radius c) (N.radius c')) hc₀.le
  exact Metric.ball_disjoint_ball (by linarith)

/-- Every neck region has `1 ≤ k` (dimension guard of its available type). -/
theorem ms6_one_le_k (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ) : 1 ≤ k := by
  have hav := N.available
  cases T with
  | horizontal =>
    have h : 1 ≤ k ∧ k ≤ n := hav
    exact h.1
  | vertical =>
    have h : 2 ≤ k ∧ k ≤ n + 2 := hav
    omega

/-- Rank zero occurs only for vertical necks with `k = 2`. -/
theorem ms6_k_eq_two_of_rank_zero (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ)
    (h : T.rank k = 0) : k = 2 := by
  have hav := N.available
  cases T with
  | horizontal =>
    have h1 : 1 ≤ k ∧ k ≤ n := hav
    have h0 : k = 0 := h
    omega
  | vertical =>
    have h1 : 2 ≤ k ∧ k ≤ n + 2 := hav
    have h0 : k - 2 = 0 := h
    omega

end NeckFacts

/-! ## Indexing and Borel partition -/

section Indexing

variable {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n}
  {R c₀ Cd Cs σ δ E κ θ γ : ℝ} {N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ}
  {ν : Measure (Space n)} {S : Set (Space n)} {f : Space n → ℝ}
  {Pa : NeckSourcePartition S f N} {rad : N.stopping → ℝ}
  (H : ∀ c : N.stopping, HoleChildren ν (Pa.assignment c) (rad c))

/-- The pairs (stopping center, hole child). -/
abbrev MS6HoleIndex := Σ c : N.stopping, Fin (H c).count

open Classical in
/-- The partial inverse of an indexing `e` of the hole children by natural numbers. -/
def ms6Inv (e : MS6HoleIndex H → ℕ) (w : ℕ) : Option (MS6HoleIndex H) :=
  if h : w ∈ Set.range e then some (Classical.choose h) else none

theorem ms6Inv_of_mem (e : MS6HoleIndex H → ℕ) {w : ℕ} (h : w ∈ Set.range e) :
    ms6Inv H e w = some (Classical.choose h) := by
  unfold ms6Inv
  rw [dite_eq_left h]

theorem ms6Inv_apply {e : MS6HoleIndex H → ℕ} (he : Injective e) (p : MS6HoleIndex H) :
    ms6Inv H e (e p) = some p := by
  rw [ms6Inv_of_mem H e ⟨p, rfl⟩]
  congr 1
  exact he (Classical.choose_spec (⟨p, rfl⟩ : e p ∈ Set.range e))

/-- The child source set of index `w` (empty off the range of `e`). -/
def ms6ChildSource (e : MS6HoleIndex H → ℕ) (w : ℕ) : Set (Space n) :=
  (ms6Inv H e w).elim ∅ (fun p => (H p.1).childSet p.2)

/-- The child center of index `w`. -/
def ms6ChildCenter (e : MS6HoleIndex H → ℕ) (w : ℕ) : Space n :=
  (ms6Inv H e w).elim q (fun p => (H p.1).center p.2)

/-- The child radius of index `w`: the common radius of the parent hole's children. -/
def ms6ChildRadius (e : MS6HoleIndex H → ℕ) (w : ℕ) : ℝ :=
  (ms6Inv H e w).elim 0 (fun p => rad p.1)

/-- The parent stopping center of index `w`. -/
def ms6ChildParent (e : MS6HoleIndex H → ℕ) (w : ℕ) : Space n :=
  (ms6Inv H e w).elim q (fun p => (p.1 : Space n))

variable {H}

theorem ms6ChildSource_apply {e : MS6HoleIndex H → ℕ} (he : Injective e)
    (p : MS6HoleIndex H) : ms6ChildSource H e (e p) = (H p.1).childSet p.2 := by
  rw [ms6ChildSource, ms6Inv_apply H he p]
  rfl

theorem ms6ChildCenter_apply {e : MS6HoleIndex H → ℕ} (he : Injective e)
    (p : MS6HoleIndex H) : ms6ChildCenter H e (e p) = (H p.1).center p.2 := by
  rw [ms6ChildCenter, ms6Inv_apply H he p]
  rfl

theorem ms6ChildRadius_apply {e : MS6HoleIndex H → ℕ} (he : Injective e)
    (p : MS6HoleIndex H) : ms6ChildRadius H e (e p) = rad p.1 := by
  rw [ms6ChildRadius, ms6Inv_apply H he p]
  rfl

theorem ms6ChildParent_apply {e : MS6HoleIndex H → ℕ} (he : Injective e)
    (p : MS6HoleIndex H) : ms6ChildParent H e (e p) = (p.1 : Space n) := by
  rw [ms6ChildParent, ms6Inv_apply H he p]
  rfl

theorem ms6ChildRadius_of_mem (e : MS6HoleIndex H → ℕ) {w : ℕ} (h : w ∈ Set.range e) :
    ms6ChildRadius H e w = rad (Classical.choose h).1 := by
  rw [ms6ChildRadius, ms6Inv_of_mem H e h]
  rfl

theorem ms6ChildParent_of_mem (e : MS6HoleIndex H → ℕ) {w : ℕ} (h : w ∈ Set.range e) :
    ms6ChildParent H e w = ((Classical.choose h).1 : Space n) := by
  rw [ms6ChildParent, ms6Inv_of_mem H e h]
  rfl

/-- The step identity: the source identity of the partition splits along the hole covers. -/
theorem ms6_measure_eq {e : MS6HoleIndex H → ℕ} (he : Injective e)
    (hcount : N.stopping.Countable)
    (hid : ν = ν.restrict Pa.errorSet + ν.restrict Pa.coreSet +
      Measure.sum (fun c : N.stopping => ν.restrict (Pa.assignment c))) :
    ν = ν.restrict (Pa.errorSet ∪ ⋃ c : N.stopping, (H c).discard) + ν.restrict Pa.coreSet +
      Measure.sum (fun w : Set.range e => ν.restrict (ms6ChildSource H e w)) := by
  have : Countable N.stopping := hcount.to_subtype
  have hA : ∀ c : N.stopping, ν.restrict (Pa.assignment c) =
      ν.restrict (H c).discard + Measure.sum (fun i => ν.restrict ((H c).childSet i)) := by
    intro c
    have hset : Pa.assignment c = (H c).discard ∪ ⋃ i, (H c).childSet i :=
      Subset.antisymm (H c).cover
        (union_subset (H c).discard_subset (iUnion_subset (H c).childSet_subset))
    calc ν.restrict (Pa.assignment c)
        = ν.restrict ((H c).discard ∪ ⋃ i, (H c).childSet i) := congrArg ν.restrict hset
      _ = ν.restrict (H c).discard + Measure.sum (fun i => ν.restrict ((H c).childSet i)) := by
        rw [Measure.restrict_union (disjoint_iUnion_right.mpr (H c).disjoint_discard)
            (MeasurableSet.iUnion (H c).measurableSet_childSet),
          Measure.restrict_iUnion (fun i j hij => (H c).disjoint_childSet i j hij)
            (H c).measurableSet_childSet]
  have hE : ν.restrict (Pa.errorSet ∪ ⋃ c : N.stopping, (H c).discard) =
      ν.restrict Pa.errorSet + Measure.sum (fun c : N.stopping => ν.restrict (H c).discard) := by
    rw [Measure.restrict_union (disjoint_iUnion_right.mpr fun c : N.stopping =>
        (Pa.disjoint_errorSet_assignment c c.2).mono_right (H c).discard_subset)
      (MeasurableSet.iUnion fun c : N.stopping => (H c).measurableSet_discard),
      Measure.restrict_iUnion (fun (c c' : N.stopping) hcc' => (Pa.disjoint_assignment c c.2 c'
        c'.2 (fun h => hcc' (Subtype.ext h))).mono (H c).discard_subset (H c').discard_subset)
        (fun c : N.stopping => (H c).measurableSet_discard)]
  have hC : Measure.sum (fun c : N.stopping =>
        Measure.sum (fun i => ν.restrict ((H c).childSet i))) =
      Measure.sum (fun w : Set.range e => ν.restrict (ms6ChildSource H e w)) := by
    rw [ms6_sum_sigma, ← ms6_sum_equiv (Equiv.ofInjective e he)
      (fun w : Set.range e => ν.restrict (ms6ChildSource H e w))]
    congr 1
    funext p
    simp only [Equiv.ofInjective_apply, ms6ChildSource_apply he]
  have hsum : Measure.sum (fun c : N.stopping => ν.restrict (Pa.assignment c)) =
      Measure.sum (fun c : N.stopping => ν.restrict (H c).discard) +
        Measure.sum (fun w : Set.range e => ν.restrict (ms6ChildSource H e w)) := by
    rw [← hC, Measure.sum_add_sum]
    exact congrArg Measure.sum (funext hA)
  calc ν = ν.restrict Pa.errorSet + ν.restrict Pa.coreSet +
        Measure.sum (fun c : N.stopping => ν.restrict (Pa.assignment c)) := hid
    _ = ν.restrict (Pa.errorSet ∪ ⋃ c : N.stopping, (H c).discard) + ν.restrict Pa.coreSet +
        Measure.sum (fun w : Set.range e => ν.restrict (ms6ChildSource H e w)) := by
      rw [hsum, hE]
      abel

variable (H)

/-- The step children built from an injective indexing `e` of the hole children. -/
def ms6StepChildren (ρ ε : ℝ) (e : MS6HoleIndex H → ℕ) (he : Injective e)
    (hcount : N.stopping.Countable)
    (hrad : ∀ c : N.stopping, ((c : Space n) ∈ Pa.terminal → rad c = 2 * ε * N.radius c) ∧
      ((c : Space n) ∉ Pa.terminal → rad c = 3 * ρ * N.radius c))
    (hid : ν = ν.restrict Pa.errorSet + ν.restrict Pa.coreSet +
      Measure.sum (fun c : N.stopping => ν.restrict (Pa.assignment c))) :
    StepChildren Pa ρ ε rad H where
  errorSet := Pa.errorSet ∪ ⋃ c : N.stopping, (H c).discard
  coreSet := Pa.coreSet
  childIndex := Set.range e
  childSource := ms6ChildSource H e
  childCenter := ms6ChildCenter H e
  childRadius := ms6ChildRadius H e
  childParent := ms6ChildParent H e
  childOrigin := fun w => Classical.choose w.2
  measurableSet_errorSet := by
    have : Countable N.stopping := hcount.to_subtype
    exact Pa.measurableSet_errorSet.union
      (MeasurableSet.iUnion fun c => (H c).measurableSet_discard)
  measurableSet_coreSet := Pa.measurableSet_coreSet
  measurableSet_childSource := by
    rintro _ ⟨p, rfl⟩
    rw [ms6ChildSource_apply he]
    exact (H p.1).measurableSet_childSet p.2
  errorSet_subset := union_subset Pa.errorSet_subset
    (iUnion_subset fun c => (H c).discard_subset.trans (Pa.assignment_subset c c.2))
  coreSet_subset := Pa.coreSet_subset
  childSource_subset := by
    rintro _ ⟨p, rfl⟩
    rw [ms6ChildSource_apply he]
    exact ((H p.1).childSet_subset p.2).trans (Pa.assignment_subset _ p.1.2)
  cover := by
    intro z hz
    rcases Pa.cover hz with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr h)
    · obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp h
      rcases (H ⟨c, hc⟩).cover hzc with hd | hch
      · exact Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨c, hc⟩, hd⟩)))
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hch
        refine Or.inr (Set.mem_iUnion₂.mpr ⟨e ⟨⟨c, hc⟩, i⟩, ⟨_, rfl⟩, ?_⟩)
        rw [ms6ChildSource_apply he]
        exact hi
  disjoint_errorSet_coreSet := Disjoint.union_left Pa.disjoint_errorSet_coreSet
    (Set.disjoint_iUnion_left.mpr fun c =>
      (Pa.disjoint_coreSet_assignment c c.2).symm.mono_left (H c).discard_subset)
  disjoint_errorSet_child := by
    rintro _ ⟨p, rfl⟩
    rw [ms6ChildSource_apply he]
    refine Disjoint.union_left ((Pa.disjoint_errorSet_assignment _ p.1.2).mono_right
      ((H p.1).childSet_subset p.2)) (Set.disjoint_iUnion_left.mpr fun c => ?_)
    by_cases hc : c = p.1
    · subst hc
      exact (H p.1).disjoint_discard p.2
    · exact (Pa.disjoint_assignment c c.2 p.1 p.1.2 (fun h => hc (Subtype.ext h))).mono
        (H c).discard_subset ((H p.1).childSet_subset p.2)
  disjoint_coreSet_child := by
    rintro _ ⟨p, rfl⟩
    rw [ms6ChildSource_apply he]
    exact (Pa.disjoint_coreSet_assignment _ p.1.2).mono_right ((H p.1).childSet_subset p.2)
  disjoint_children := by
    rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩ hne
    rw [ms6ChildSource_apply he, ms6ChildSource_apply he]
    have hpp : p ≠ p' := fun h => hne (congrArg e h)
    obtain ⟨c, i⟩ := p
    obtain ⟨c', i'⟩ := p'
    by_cases hc : c = c'
    · subst hc
      have hii : i ≠ i' := fun h => hpp (by subst h; rfl)
      exact (H c).disjoint_childSet i i' hii
    · exact (Pa.disjoint_assignment c c.2 c' c'.2 (fun h => hc (Subtype.ext h))).mono
        ((H c).childSet_subset i) ((H c').childSet_subset i')
  coreSet_subset_core := Pa.coreSet_subset_core
  childParent_mem := by
    rintro _ ⟨p, rfl⟩
    rw [ms6ChildParent_apply he]
    exact p.1.2
  childSource_subset_hole := by
    rintro _ ⟨p, rfl⟩
    rw [ms6ChildSource_apply he, ms6ChildParent_apply he]
    exact ((H p.1).childSet_subset p.2).trans (Pa.assignment_subset_ball _ p.1.2)
  childSource_subset_ball := by
    rintro _ ⟨p, rfl⟩
    rw [ms6ChildSource_apply he, ms6ChildCenter_apply he, ms6ChildRadius_apply he]
    exact (H p.1).childSet_subset_ball p.2
  childRadius_eq := by
    rintro _ ⟨p, rfl⟩
    rw [ms6ChildRadius_apply he, ms6ChildParent_apply he]
    by_cases ht : (p.1 : Space n) ∈ Pa.terminal
    · exact Or.inr ((hrad p.1).1 ht)
    · exact Or.inl ((hrad p.1).2 ht)
  finite_children := by
    intro c
    by_cases hc : c ∈ N.stopping
    · refine (Set.finite_range (fun i : Fin (H ⟨c, hc⟩).count => e ⟨⟨c, hc⟩, i⟩)).subset ?_
      rintro _ ⟨⟨p, rfl⟩, hpar⟩
      rw [ms6ChildParent_apply he] at hpar
      obtain ⟨⟨c', hc'⟩, i⟩ := p
      have hpar' : c' = c := hpar
      subst hpar'
      exact ⟨i, rfl⟩
    · refine Set.finite_empty.subset ?_
      rintro _ ⟨⟨p, rfl⟩, hpar⟩
      rw [ms6ChildParent_apply he] at hpar
      exact hc (hpar ▸ p.1.2)
  errorSet_subset_discard := Subset.rfl
  childOrigin_injective := by
    intro w w' h
    exact Subtype.ext ((Classical.choose_spec w.2).symm.trans
      ((congrArg e h).trans (Classical.choose_spec w'.2)))
  childParent_origin := fun w => ms6ChildParent_of_mem e w.2
  childRadius_origin := fun w => ms6ChildRadius_of_mem e w.2
  childRadius_collapsed := by
    rintro _ ⟨p, rfl⟩ hnt
    rw [ms6ChildParent_apply he] at hnt
    rw [ms6ChildRadius_apply he, ms6ChildParent_apply he]
    exact (hrad p.1).2 hnt
  measure_eq := ms6_measure_eq he hcount hid

end Indexing

/-- **`exists_stepChildren`**: the step children exist, with the origin map defined on the
active children only. -/
theorem exists_stepChildren_proof (n : ℕ) :
    ∀ {k : ℕ} {T : NeckType} {ι : Type} {q : Space n} {R Cs σ δ E κ θ γ : ℝ}
      (N : NeckRegion n k T ι q R (1 / 20) 4 Cs σ δ E κ θ γ) (ν : Measure (Space n))
      (S : Set (Space n)) (f : Space n → ℝ) (Pa : NeckSourcePartition S f N) (ρ ε : ℝ)
      (rad : N.stopping → ℝ) (H : ∀ c : N.stopping, HoleChildren ν (Pa.assignment c) (rad c)),
      IsFiniteMeasure ν →
      (∀ c : N.stopping, ((c : Space n) ∈ Pa.terminal → rad c = 2 * ε * N.radius c) ∧
        ((c : Space n) ∉ Pa.terminal → rad c = 3 * ρ * N.radius c)) →
      ν = ν.restrict Pa.errorSet + ν.restrict Pa.coreSet +
        Measure.sum (fun c : N.stopping => ν.restrict (Pa.assignment c)) →
      Nonempty (StepChildren Pa ρ ε rad H) := by
  intro k T ι q R Cs σ δ E κ θ γ N ν S f Pa ρ ε rad H _ hrad hid
  have hcount := ms6_stopping_countable N
  have : Countable N.stopping := hcount.to_subtype
  obtain ⟨e, he⟩ := Countable.exists_injective_nat (MS6HoleIndex H)
  exact ⟨ms6StepChildren H ρ ε e he hcount hrad hid⟩

/-! ## Mass and content estimates -/

section Estimates

variable {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n}
  {R c₀ Cd Cs σ δ E κ θ γ : ℝ} {N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ}
  {ν : Measure (Space n)} {S : Set (Space n)} {f : Space n → ℝ}
  {Pa : NeckSourcePartition S f N}

/-- The discarded mass of one hole: at most `Q B d_c^k` with
`Q = 4 C₁ (A+1) C_b/ρ² + 2 C₂/ε² + A C_b` (terminal two tubes, positive-rank collapse,
rank-zero discard with `k = 2`). -/
theorem ms6_discard_le {B B' A C₁ C₂ Ccol Cter Cb ρ ε : ℝ} {c : N.stopping} {r : ℝ}
    {Hc : HoleChildren ν (Pa.assignment c) r}
    (hB : 0 < B) (hB'le : B' ≤ Cb * B) (hA : 0 < A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hCb : 0 ≤ Cb)
    (hH : HoleFacts Pa B B' (A * B') C₁ C₂ Ccol Cter ρ ε c r Hc) :
    ν Hc.discard ≤ ENNReal.ofReal
      ((4 * C₁ * (A + 1) * Cb / ρ ^ 2 + 2 * C₂ / ε ^ 2 + A * Cb) * (B * N.radius c ^ k)) := by
  have hd : 0 ≤ N.radius c := N.radius_nonneg c c.2.1
  have hdk : 0 ≤ N.radius c ^ k := pow_nonneg hd k
  have hBd : 0 ≤ B * N.radius c ^ k := mul_nonneg hB.le hdk
  have hX : 0 ≤ 4 * C₁ * (A + 1) * Cb / ρ ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁) (by linarith)) hCb)
      (sq_nonneg ρ)
  have hY : 0 ≤ 2 * C₂ / ε ^ 2 := div_nonneg (mul_nonneg (by norm_num) hC₂) (sq_nonneg ε)
  have hZ : 0 ≤ A * Cb := mul_nonneg hA.le hCb
  obtain ⟨hterm, hcoll⟩ := hH
  by_cases ht : (c : Space n) ∈ Pa.terminal
  · obtain ⟨-, -, -, hdis, -⟩ := hterm ht
    refine hdis.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 2 * (C₂ * B) * N.radius c ^ k / ε ^ 2 = (2 * C₂ / ε ^ 2) * (B * N.radius c ^ k) := by
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right (by linarith) hBd
  · obtain ⟨-, hcases⟩ := hcoll ht
    rcases hcases with ⟨-, hdis, -⟩ | ⟨hrk, -, hdis⟩
    · refine hdis.trans (ENNReal.ofReal_le_ofReal ?_)
      have hP : 0 ≤ 4 * C₁ * (A + 1) / ρ ^ 2 :=
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁) (by linarith)) (sq_nonneg ρ)
      have h1 : 4 * (C₁ * (A * B' + B')) * N.radius c ^ k / ρ ^ 2 =
          (4 * C₁ * (A + 1) / ρ ^ 2) * B' * N.radius c ^ k := by ring
      have h2 : (4 * C₁ * (A + 1) / ρ ^ 2) * B' * N.radius c ^ k ≤
          (4 * C₁ * (A + 1) / ρ ^ 2) * (Cb * B) * N.radius c ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB'le hP) hdk
      have h3 : (4 * C₁ * (A + 1) / ρ ^ 2) * (Cb * B) * N.radius c ^ k =
          (4 * C₁ * (A + 1) * Cb / ρ ^ 2) * (B * N.radius c ^ k) := by ring
      rw [h1]
      refine h2.trans ?_
      rw [h3]
      exact mul_le_mul_of_nonneg_right (by linarith) hBd
    · have hk2 : k = 2 := ms6_k_eq_two_of_rank_zero N hrk
      refine hdis.le.trans (ENNReal.ofReal_le_ofReal ?_)
      have hpow : ∀ x : ℝ, x ^ 2 = x ^ k := fun x => by rw [hk2]
      have h1 : A * B' * N.radius c ^ 2 = A * B' * N.radius c ^ k := by rw [hpow]
      have h2 : A * B' * N.radius c ^ k ≤ A * (Cb * B) * N.radius c ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB'le hA.le) hdk
      have h3 : A * (Cb * B) * N.radius c ^ k = (A * Cb) * (B * N.radius c ^ k) := by ring
      rw [h1]
      refine h2.trans ?_
      rw [h3]
      exact mul_le_mul_of_nonneg_right (by linarith) hBd

/-- The child content of one hole: `m_c r_c^k ≤ (3^k C_col ρ + 2^k C_ter ε²) d_c^k`. -/
theorem ms6_hole_content_le {B B' a C₁ C₂ Ccol Cter ρ ε : ℝ} {c : N.stopping} {r : ℝ}
    {Hc : HoleChildren ν (Pa.assignment c) r} (hCcol : 0 ≤ Ccol) (hCter : 0 ≤ Cter)
    (hρ : 0 < ρ) (hε : 0 < ε)
    (hH : HoleFacts Pa B B' a C₁ C₂ Ccol Cter ρ ε c r Hc) :
    (Hc.count : ℝ) * r ^ k ≤ (3 ^ k * Ccol * ρ + 2 ^ k * Cter * ε ^ 2) * N.radius c ^ k := by
  have hd : 0 ≤ N.radius c := N.radius_nonneg c c.2.1
  have hdk : 0 ≤ N.radius c ^ k := pow_nonneg hd k
  have hcol : 0 ≤ 3 ^ k * Ccol * ρ * N.radius c ^ k :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) k) hCcol) hρ.le) hdk
  have hter : 0 ≤ 2 ^ k * Cter * ε ^ 2 * N.radius c ^ k :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) k) hCter) (sq_nonneg ε)) hdk
  have hsplit : (3 ^ k * Ccol * ρ + 2 ^ k * Cter * ε ^ 2) * N.radius c ^ k =
      3 ^ k * Ccol * ρ * N.radius c ^ k + 2 ^ k * Cter * ε ^ 2 * N.radius c ^ k := by ring
  rw [hsplit]
  obtain ⟨hterm, hcoll⟩ := hH
  by_cases ht : (c : Space n) ∈ Pa.terminal
  · obtain ⟨hr, -, hk2, -, hm⟩ := hterm ht
    have hrk : r ^ k = (2 * ε * N.radius c) ^ k := by rw [hr]
    rw [hrk]
    have := Contraction.terminal_hole_content hk2 hε hd hm
    linarith
  · obtain ⟨hr, hcases⟩ := hcoll ht
    have hrk : r ^ k = (3 * ρ * N.radius c) ^ k := by rw [hr]
    rw [hrk]
    rcases hcases with ⟨-, -, hm⟩ | ⟨-, hm0, -⟩
    · have := Contraction.collapsed_hole_content (ms6_one_le_k N) hρ hd hm
      linarith
    · rw [hm0, Nat.cast_zero, zero_mul]
      linarith

end Estimates

/-- **`stepChildren_estimates`**: the discarded-mass and radius estimates for the step
children. -/
theorem stepChildren_estimates_proof (n : ℕ) :
    ∀ {k : ℕ} {T : NeckType} {ι : Type} {q : Space n} {R Cs σ δ E κ θ γ : ℝ}
      (N : NeckRegion n k T ι q R (1 / 20) 4 Cs σ δ E κ θ γ) (ν : Measure (Space n))
      (S : Set (Space n)) (f : Space n → ℝ) (Pa : NeckSourcePartition S f N)
      (B B' A C₁ C₂ Ccol Cter Cb ρ ε θ₀ Eerr : ℝ) (rad : N.stopping → ℝ)
      (H : ∀ c : N.stopping, HoleChildren ν (Pa.assignment c) (rad c))
      (SC : StepChildren Pa ρ ε rad H),
      IsFiniteMeasure ν → 0 < R → 0 < B → B ≤ B' → B' ≤ Cb * B → 0 < A → 0 < θ₀ →
      0 ≤ C₁ → 0 ≤ C₂ → 0 ≤ Ccol → 0 ≤ Cter →
      ν Pa.errorSet ≤ ENNReal.ofReal (C₁ * B' * R ^ k / θ₀ ^ 2) →
      N.HasTotalContentBound C₁ →
      0 < ρ → 12 * ρ ≤ 1 / 2 → 0 < ε → 2 * ε ≤ 1 / 2 →
      C₁ * (3 ^ k * Ccol * ρ + 2 ^ k * Cter * ε ^ 2) ≤ 1 / 2 →
      (∀ c : N.stopping, HoleFacts Pa B B' (A * B') C₁ C₂ Ccol Cter ρ ε c (rad c) (H c)) →
      C₁ * Cb / θ₀ ^ 2 + C₁ * (4 * C₁ * (A + 1) * Cb / ρ ^ 2 + 2 * C₂ / ε ^ 2 + A * Cb) ≤
        Eerr →
      ν SC.errorSet ≤ ENNReal.ofReal (Eerr * B * R ^ k) ∧
        (∀ w ∈ SC.childIndex, SC.childRadius w ≤ R / 2) ∧
        ∑' w : SC.childIndex, ENNReal.ofReal (SC.childRadius w ^ k) ≤
          ENNReal.ofReal (R ^ k / 2) := by
  intro k T ι q R Cs σ δ E κ θ γ N ν S f Pa B B' A C₁ C₂ Ccol Cter Cb ρ ε θ₀ Eerr rad H SC
    _ hR hB hBB' hB'le hA hθ₀ hC₁ hC₂ hCcol hCter herr htot hρ hρ12 hε hε2 hsmall hH hEerr
  have : Countable N.stopping := (ms6_stopping_countable N).to_subtype
  have hCb : 1 ≤ Cb := by
    by_contra hlt
    have : Cb * B < B := mul_lt_of_lt_one_left hB (not_le.mp hlt)
    linarith
  have hRk : 0 ≤ R ^ k := pow_nonneg hR.le k
  have hsumd : ∑' c : N.stopping, ENNReal.ofReal (N.radius c ^ k) ≤
      ENNReal.ofReal (C₁ * R ^ k) := le_trans le_add_self htot
  refine ⟨?_, ?_, ?_⟩
  · -- the error bound
    have hQ : 0 ≤ 4 * C₁ * (A + 1) * Cb / ρ ^ 2 + 2 * C₂ / ε ^ 2 + A * Cb := by
      have hX : 0 ≤ 4 * C₁ * (A + 1) * Cb / ρ ^ 2 :=
        div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁) (by linarith))
          (by linarith)) (sq_nonneg ρ)
      have hY : 0 ≤ 2 * C₂ / ε ^ 2 := div_nonneg (mul_nonneg (by norm_num) hC₂) (sq_nonneg ε)
      have hZ : 0 ≤ A * Cb := mul_nonneg hA.le (by linarith)
      linarith
    have hQB : 0 ≤ (4 * C₁ * (A + 1) * Cb / ρ ^ 2 + 2 * C₂ / ε ^ 2 + A * Cb) * B :=
      mul_nonneg hQ hB.le
    have hPe : ν Pa.errorSet ≤ ENNReal.ofReal (C₁ * (Cb * B) * R ^ k / θ₀ ^ 2) :=
      herr.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB'le hC₁) hRk) (sq_nonneg θ₀)))
    have h1 : 0 ≤ C₁ * (Cb * B) * R ^ k / θ₀ ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hC₁ (mul_nonneg (by linarith) hB.le)) hRk)
        (sq_nonneg θ₀)
    have h2 : 0 ≤ (4 * C₁ * (A + 1) * Cb / ρ ^ 2 + 2 * C₂ / ε ^ 2 + A * Cb) * B * (C₁ * R ^ k) :=
      mul_nonneg hQB (mul_nonneg hC₁ hRk)
    calc ν SC.errorSet ≤ ν (Pa.errorSet ∪ ⋃ c : N.stopping, (H c).discard) :=
          measure_mono SC.errorSet_subset_discard
      _ ≤ ν Pa.errorSet + ∑' c : N.stopping, ν (H c).discard :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_le _))
      _ ≤ ENNReal.ofReal (C₁ * (Cb * B) * R ^ k / θ₀ ^ 2) +
            ∑' c : N.stopping, ENNReal.ofReal
              ((4 * C₁ * (A + 1) * Cb / ρ ^ 2 + 2 * C₂ / ε ^ 2 + A * Cb) * B *
                N.radius c ^ k) := by
          refine add_le_add hPe (ENNReal.tsum_le_tsum fun c => ?_)
          refine (ms6_discard_le hB hB'le hA hC₁ hC₂ (by linarith) (hH c)).trans ?_
          exact le_of_eq (congrArg ENNReal.ofReal (by ring))
      _ = ENNReal.ofReal (C₁ * (Cb * B) * R ^ k / θ₀ ^ 2) +
            ENNReal.ofReal ((4 * C₁ * (A + 1) * Cb / ρ ^ 2 + 2 * C₂ / ε ^ 2 + A * Cb) * B) *
              ∑' c : N.stopping, ENNReal.ofReal (N.radius c ^ k) := by
          rw [← ENNReal.tsum_mul_left]
          congr 1
          refine tsum_congr fun c => ?_
          rw [ENNReal.ofReal_mul hQB]
      _ ≤ ENNReal.ofReal (C₁ * (Cb * B) * R ^ k / θ₀ ^ 2) +
            ENNReal.ofReal ((4 * C₁ * (A + 1) * Cb / ρ ^ 2 + 2 * C₂ / ε ^ 2 + A * Cb) * B) *
              ENNReal.ofReal (C₁ * R ^ k) := add_le_add le_rfl (mul_le_mul' le_rfl hsumd)
      _ = ENNReal.ofReal ((C₁ * Cb / θ₀ ^ 2 +
            C₁ * (4 * C₁ * (A + 1) * Cb / ρ ^ 2 + 2 * C₂ / ε ^ 2 + A * Cb)) * B * R ^ k) := by
          rw [← ENNReal.ofReal_mul hQB, ← ENNReal.ofReal_add h1 h2]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (Eerr * B * R ^ k) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hEerr hB.le) hRk)
  · -- the child radii
    intro w hw
    rw [show SC.childRadius w = rad (SC.childOrigin ⟨w, hw⟩).1 from
      SC.childRadius_origin ⟨w, hw⟩]
    obtain ⟨hterm, hcoll⟩ := hH (SC.childOrigin ⟨w, hw⟩).1
    have hd : 0 ≤ N.radius (SC.childOrigin ⟨w, hw⟩).1 :=
      N.radius_nonneg _ (SC.childOrigin ⟨w, hw⟩).1.2.1
    by_cases ht : ((SC.childOrigin ⟨w, hw⟩).1 : Space n) ∈ Pa.terminal
    · obtain ⟨hr, hdR, -⟩ := hterm ht
      rw [hr]
      have := mul_le_mul_of_nonneg_left hdR (by linarith : (0 : ℝ) ≤ 2 * ε)
      have := mul_le_mul_of_nonneg_right hε2 hR.le
      linarith
    · obtain ⟨hr, -⟩ := hcoll ht
      rw [hr]
      have hd4 : N.radius (SC.childOrigin ⟨w, hw⟩).1 ≤ 4 * R :=
        N.radius_le _ (SC.childOrigin ⟨w, hw⟩).1.2.1
      have := mul_le_mul_of_nonneg_left hd4 (by linarith : (0 : ℝ) ≤ 3 * ρ)
      have := mul_le_mul_of_nonneg_right hρ12 hR.le
      linarith
  · -- the child content
    have hK0 : 0 ≤ 3 ^ k * Ccol * ρ + 2 ^ k * Cter * ε ^ 2 :=
      add_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) k) hCcol) hρ.le)
        (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) k) hCter) (sq_nonneg ε))
    calc ∑' w : SC.childIndex, ENNReal.ofReal (SC.childRadius w ^ k)
        = ∑' w : SC.childIndex, ENNReal.ofReal (rad (SC.childOrigin w).1 ^ k) :=
          tsum_congr fun w => by rw [SC.childRadius_origin w]
      _ ≤ ∑' p : (Σ c : N.stopping, Fin (H c).count), ENNReal.ofReal (rad p.1 ^ k) :=
          ENNReal.tsum_comp_le_tsum_of_injective SC.childOrigin_injective
            (fun p => ENNReal.ofReal (rad p.1 ^ k))
      _ = ∑' c : N.stopping, ENNReal.ofReal (((H c).count : ℝ) * rad c ^ k) := by
          rw [ENNReal.tsum_sigma']
          refine tsum_congr fun c => ?_
          simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ∑' c : N.stopping, ENNReal.ofReal
            ((3 ^ k * Ccol * ρ + 2 ^ k * Cter * ε ^ 2) * N.radius c ^ k) :=
          ENNReal.tsum_le_tsum fun c =>
            ENNReal.ofReal_le_ofReal (ms6_hole_content_le hCcol hCter hρ hε (hH c))
      _ = ENNReal.ofReal (3 ^ k * Ccol * ρ + 2 ^ k * Cter * ε ^ 2) *
            ∑' c : N.stopping, ENNReal.ofReal (N.radius c ^ k) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun c => ?_
          rw [ENNReal.ofReal_mul hK0]
      _ ≤ ENNReal.ofReal (3 ^ k * Ccol * ρ + 2 ^ k * Cter * ε ^ 2) *
            ENNReal.ofReal (C₁ * R ^ k) := mul_le_mul' le_rfl hsumd
      _ = ENNReal.ofReal (C₁ * (3 ^ k * Ccol * ρ + 2 ^ k * Cter * ε ^ 2) * R ^ k) := by
          rw [← ENNReal.ofReal_mul hK0]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (R ^ k / 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := mul_le_mul_of_nonneg_right hsmall hRk
          linarith

end ParabolicRectifiability
