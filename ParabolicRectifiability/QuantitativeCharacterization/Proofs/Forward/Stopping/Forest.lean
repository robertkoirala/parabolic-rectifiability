import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Stopping

/-! # The combinatorial stopping forest exists

Proof of

`d1b_stoppingForest_proof : PartitionTreeStatement → StoppingForestStatement`.

Route. With `c Q = a_Q`, `H = b/2` and `B = b` (as `ℝ≥0∞`), the state
`d1bforest_state P c B H j w : Option (root × chain sum)` of the cell `(j, w)` is defined by
recursion on the level along the parent map `(j + 1, w) ↦ (j, P.parent j w)`:
* `none` if `H < c (j, w)` (a bad block);
* at level `0`, and below a bad parent, the cell itself with sum `c (j, w)` (a new root);
* otherwise the parent's root `S'` with sum `s' + c (j, w)` if `s' + c (j, w) ≤ B`, else the
  cell itself (a budget exit; then `s' > H`, since `c (j, w) ≤ H` and `H + H ≤ B`).

The bad blocks are the forest cells with `H < c Q`, the roots are the forest cells that are their
own root, and `members S` are the forest cells with root `S`. Part (a) proves the state invariants
(the root is a cell above the cell and its own root, the sum is at most `B`), heredity (a root is
only inherited from the parent, and ancestors at a given level are unique by `PartitionTree`) and
the classification. Part (b) proves the chain-sum identity
`chainSum P μ k Λ (members S) Q = s` (the members of the region of `S` above `Q` are the ancestors
of `Q` at the levels `S.1, …, Q.1`; strict ancestry is by generation, so single-child chains with
repeated cell sets cause no double counting), the budget and the three entries of a root. Only the
recorded sufficient properties are proved; the budget-exit charge is `> b/2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

variable {n : ℕ}

/-! ## (a) The recursive state -/

/-- One step of the level recursion at the cell `Q` with coefficient `cQ`, given the state `prev`
of its parent (`none` at level `0`): `none` for a bad block (`H < cQ`); otherwise a new root
`some (Q, cQ)` if there is no parent region or the budget `B` would be exceeded, and else the
parent's root `p.1` with chain sum `p.2 + cQ`. -/
def d1bforest_step (B H : ℝ≥0∞) (Q : ℕ × Space n) (cQ : ℝ≥0∞)
    (prev : Option ((ℕ × Space n) × ℝ≥0∞)) : Option ((ℕ × Space n) × ℝ≥0∞) :=
  if H < cQ then none
  else prev.elim (some (Q, cQ)) fun p =>
    if p.2 + cQ ≤ B then some (p.1, p.2 + cQ) else some (Q, cQ)

/-- The state of the cell `(j, w)`: `none` for a bad block, `some (S, s)` for a member of the
region of the root `S` with inclusive chain sum `s`. Recursion on the level along the parent map. -/
def d1bforest_state {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (c : ℕ × Space n → ℝ≥0∞) (B H : ℝ≥0∞) : ℕ → Space n → Option ((ℕ × Space n) × ℝ≥0∞)
  | 0, w => d1bforest_step B H (0, w) (c (0, w)) none
  | j + 1, w =>
      d1bforest_step B H (j + 1, w) (c (j + 1, w)) (d1bforest_state P c B H j (P.parent j w))

/-- The bad blocks: forest cells with `H < c Q`. -/
def d1bforest_bad {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (c : ℕ × Space n → ℝ≥0∞) (H : ℝ≥0∞) (a : Space n) (R : ℝ) : Set (ℕ × Space n) :=
  {Q | P.InForest a R Q ∧ H < c Q}

/-- The roots: forest cells that are their own region root. -/
def d1bforest_roots {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (c : ℕ × Space n → ℝ≥0∞) (B H : ℝ≥0∞) (a : Space n) (R : ℝ) : Set (ℕ × Space n) :=
  {S | P.InForest a R S ∧ ∃ s, d1bforest_state P c B H S.1 S.2 = some (S, s)}

/-- The members of the region of `S`: forest cells whose region root is `S`. -/
def d1bforest_members {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (c : ℕ × Space n → ℝ≥0∞) (B H : ℝ≥0∞) (a : Space n) (R : ℝ) (S : ℕ × Space n) :
    Set (ℕ × Space n) :=
  {Q | P.InForest a R Q ∧ ∃ s, d1bforest_state P c B H Q.1 Q.2 = some (S, s)}

/-- The inclusive chain sum with a general coefficient `c` (`chainSum` for `c = P.coeff μ k Λ`). -/
def d1bforest_csum {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (c : ℕ × Space n → ℝ≥0∞) (𝒮 : Set (ℕ × Space n)) (Q : ℕ × Space n) : ℝ≥0∞ :=
  ∑' Q' : ↥{Q' : ℕ × Space n | Q' ∈ 𝒮 ∧ P.IsBelow Q Q'}, c Q'

section Step

variable {B H : ℝ≥0∞} {Q : ℕ × Space n} {cQ : ℝ≥0∞}

theorem d1bforest_step_bad {prev : Option ((ℕ × Space n) × ℝ≥0∞)} (h : H < cQ) :
    d1bforest_step B H Q cQ prev = none := by
  simp only [d1bforest_step, ite_eq_left h]

theorem d1bforest_step_top (h : ¬ H < cQ) : d1bforest_step B H Q cQ none = some (Q, cQ) := by
  simp only [d1bforest_step, ite_eq_right h, Option.elim_none]

theorem d1bforest_step_keep {S' : ℕ × Space n} {s' : ℝ≥0∞} (h : ¬ H < cQ) (hb : s' + cQ ≤ B) :
    d1bforest_step B H Q cQ (some (S', s')) = some (S', s' + cQ) := by
  simp only [d1bforest_step, ite_eq_right h, Option.elim_some, ite_eq_left hb]

theorem d1bforest_step_exit {S' : ℕ × Space n} {s' : ℝ≥0∞} (h : ¬ H < cQ)
    (hb : ¬ s' + cQ ≤ B) : d1bforest_step B H Q cQ (some (S', s')) = some (Q, cQ) := by
  simp only [d1bforest_step, ite_eq_right h, Option.elim_some, ite_eq_right hb]

/-- The three ways a step produces `some (S, s)`. -/
theorem d1bforest_step_cases {prev : Option ((ℕ × Space n) × ℝ≥0∞)} {S : ℕ × Space n}
    {s : ℝ≥0∞} (h : d1bforest_step B H Q cQ prev = some (S, s)) :
    ¬ H < cQ ∧ ((S = Q ∧ s = cQ ∧ ∀ p, prev = some p → B < p.2 + cQ) ∨
      (∃ s', prev = some (S, s') ∧ s = s' + cQ ∧ s' + cQ ≤ B)) := by
  by_cases hc : H < cQ
  · rw [d1bforest_step_bad hc] at h
    exact absurd h.symm (Option.some_ne_none _)
  refine ⟨hc, ?_⟩
  rcases prev with _ | ⟨S', s'⟩
  · rw [d1bforest_step_top hc] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Or.inl ⟨rfl, rfl, fun p hp => absurd hp.symm (Option.some_ne_none p)⟩
  · by_cases hb : s' + cQ ≤ B
    · rw [d1bforest_step_keep hc hb] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact Or.inr ⟨s', rfl, rfl, hb⟩
    · rw [d1bforest_step_exit hc hb] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine Or.inl ⟨rfl, rfl, fun p hp => ?_⟩
      obtain rfl := Option.some.inj hp
      exact not_le.mp hb

theorem d1bforest_step_eq_none {prev : Option ((ℕ × Space n) × ℝ≥0∞)} :
    d1bforest_step B H Q cQ prev = none ↔ H < cQ := by
  refine ⟨fun h => ?_, fun h => d1bforest_step_bad h⟩
  by_contra hc
  rcases prev with _ | ⟨S', s'⟩
  · rw [d1bforest_step_top hc] at h
    exact Option.some_ne_none _ h
  · by_cases hb : s' + cQ ≤ B
    · rw [d1bforest_step_keep hc hb] at h
      exact Option.some_ne_none _ h
    · rw [d1bforest_step_exit hc hb] at h
      exact Option.some_ne_none _ h

end Step

section State

variable {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {c : ℕ × Space n → ℝ≥0∞}
  {B H : ℝ≥0∞}

theorem d1bforest_state_zero (w : Space n) :
    d1bforest_state P c B H 0 w = d1bforest_step B H (0, w) (c (0, w)) none := rfl

theorem d1bforest_state_succ (j : ℕ) (w : Space n) :
    d1bforest_state P c B H (j + 1) w =
      d1bforest_step B H (j + 1, w) (c (j + 1, w)) (d1bforest_state P c B H j (P.parent j w)) :=
  rfl

theorem d1bforest_state_eq_none (j : ℕ) (w : Space n) :
    d1bforest_state P c B H j w = none ↔ H < c (j, w) := by
  cases j with
  | zero => rw [d1bforest_state_zero]; exact d1bforest_step_eq_none
  | succ j => rw [d1bforest_state_succ]; exact d1bforest_step_eq_none

theorem d1bforest_state_not_bad {j : ℕ} {w : Space n} {x : (ℕ × Space n) × ℝ≥0∞}
    (h : d1bforest_state P c B H j w = some x) : ¬ H < c (j, w) := by
  intro hlt
  have h2 : d1bforest_state P c B H j w = none := (d1bforest_state_eq_none j w).mpr hlt
  rw [h2] at h
  exact absurd h.symm (Option.some_ne_none x)

/-- **State invariants**: the root of a cell is a cell above it, is its own root, and the chain
sum is within the budget. -/
theorem d1bforest_state_spec (hHB : H ≤ B) (j : ℕ) :
    ∀ w ∈ P.center j, ∀ (S : ℕ × Space n) (s : ℝ≥0∞), d1bforest_state P c B H j w = some (S, s) →
      P.IsCell S ∧ P.IsBelow (j, w) S ∧
        (∃ s₀, d1bforest_state P c B H S.1 S.2 = some (S, s₀)) ∧ s ≤ B := by
  induction j with
  | zero =>
    intro w hw S s h
    have h0 := h
    rw [d1bforest_state_zero] at h0
    obtain ⟨hc, ⟨rfl, rfl, -⟩ | ⟨s', hs', -⟩⟩ := d1bforest_step_cases h0
    · exact ⟨hw, ⟨hw, le_rfl, Set.Subset.rfl⟩, ⟨_, h⟩, (not_lt.mp hc).trans hHB⟩
    · exact absurd hs'.symm (Option.some_ne_none _)
  | succ j ih =>
    intro w hw S s h
    have h0 := h
    rw [d1bforest_state_succ] at h0
    have hp : P.parent j w ∈ P.center j := P.parent_mem j w hw
    obtain ⟨hc, ⟨rfl, rfl, -⟩ | ⟨s', hs', rfl, hle⟩⟩ := d1bforest_step_cases h0
    · exact ⟨hw, ⟨hw, le_rfl, Set.Subset.rfl⟩, ⟨_, h⟩, (not_lt.mp hc).trans hHB⟩
    · obtain ⟨hS, hbelow, hroot, -⟩ := ih (P.parent j w) hp S s' hs'
      exact ⟨hS, ⟨hw, hbelow.2.1.trans (Nat.le_succ j),
        Set.Subset.trans (P.cell_subset_parent j w hw) hbelow.2.2⟩, hroot, hle⟩

/-- A root other than the cell itself is inherited from the parent. -/
theorem d1bforest_state_inherit {j : ℕ} {w : Space n} {S : ℕ × Space n} {s : ℝ≥0∞}
    (h : d1bforest_state P c B H (j + 1) w = some (S, s)) (hS : S ≠ (j + 1, w)) :
    ∃ s', d1bforest_state P c B H j (P.parent j w) = some (S, s') ∧ s = s' + c (j + 1, w) ∧
      s' + c (j + 1, w) ≤ B := by
  rw [d1bforest_state_succ] at h
  obtain ⟨-, ⟨hSQ, -, -⟩ | h'⟩ := d1bforest_step_cases h
  · exact absurd hSQ hS
  · exact h'

/-- A new root below level `0`: its parent is bad, or the parent's chain sum plus its
coefficient exceeds the budget. -/
theorem d1bforest_state_new (hHB : H ≤ B) {j : ℕ} {w : Space n} (hw : w ∈ P.center (j + 1))
    {s : ℝ≥0∞} (h : d1bforest_state P c B H (j + 1) w = some ((j + 1, w), s)) :
    s = c (j + 1, w) ∧ ¬ H < c (j + 1, w) ∧
      (d1bforest_state P c B H j (P.parent j w) = none ∨
        ∃ (S' : ℕ × Space n) (s' : ℝ≥0∞),
          d1bforest_state P c B H j (P.parent j w) = some (S', s') ∧ B < s' + c (j + 1, w)) := by
  rw [d1bforest_state_succ] at h
  obtain ⟨hc, ⟨-, hs, hprev⟩ | ⟨s', hs', -, -⟩⟩ := d1bforest_step_cases h
  · refine ⟨hs, hc, ?_⟩
    rcases hσ : d1bforest_state P c B H j (P.parent j w) with _ | ⟨S', s'⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨S', s', rfl, hprev _ hσ⟩
  · exfalso
    have hb := (d1bforest_state_spec hHB j (P.parent j w) (P.parent_mem j w hw) _ s' hs').2.1
    exact Nat.not_succ_le_self j hb.2.1

/-- **Ancestry**: if the region root of `(i + d, w)` lies at a level `≤ i`, it is also the region
root of the ancestor `(i, z)` of `(i + d, w)`. -/
theorem d1bforest_state_ancestor (hT : PartitionTree P) {i : ℕ} {z : Space n}
    (hz : z ∈ P.center i) (d : ℕ) :
    ∀ w ∈ P.center (i + d), ∀ (S : ℕ × Space n) (s : ℝ≥0∞),
      d1bforest_state P c B H (i + d) w = some (S, s) → P.IsBelow (i + d, w) (i, z) → S.1 ≤ i →
        ∃ s', d1bforest_state P c B H i z = some (S, s') := by
  induction d with
  | zero =>
    intro w _ S s h hb _
    have heq : ((i + 0, w) : ℕ × Space n) = (i, z) := hT.eq_of_isBelow (i + 0, w) (i, z) hz hb rfl
    obtain ⟨-, rfl⟩ := Prod.mk.inj heq
    exact ⟨s, h⟩
  | succ d ih =>
    intro w hw S s h hb hSi
    have hw' : w ∈ P.center (i + d + 1) := hw
    have hp : P.parent (i + d) w ∈ P.center (i + d) := P.parent_mem (i + d) w hw'
    have hpar : P.IsBelow (i + d + 1, w) (i + d, P.parent (i + d) w) :=
      ⟨hw', Nat.le_succ _, P.cell_subset_parent (i + d) w hw'⟩
    have hS : S ≠ (i + d + 1, w) := by
      rintro rfl
      have h' : i + d + 1 ≤ i := hSi
      omega
    obtain ⟨s', hs', -, -⟩ := d1bforest_state_inherit (j := i + d) h hS
    have hb' : P.IsBelow (i + d, P.parent (i + d) w) (i, z) :=
      hT.isBelow_of_common (i + d + 1, w) (i, z) (i + d, P.parent (i + d) w) hz hp hb hpar
        (Nat.le_add_right i d)
    exact ih (P.parent (i + d) w) hp S s' hs' hb' hSi

/-! ## (a) Labels, heredity and classification -/

theorem d1bforest_mem_bad {a : Space n} {R : ℝ} {Q : ℕ × Space n} :
    Q ∈ d1bforest_bad P c H a R ↔ P.InForest a R Q ∧ H < c Q := Iff.rfl

theorem d1bforest_mem_roots {a : Space n} {R : ℝ} {S : ℕ × Space n} :
    S ∈ d1bforest_roots P c B H a R ↔
      P.InForest a R S ∧ ∃ s, d1bforest_state P c B H S.1 S.2 = some (S, s) := Iff.rfl

theorem d1bforest_mem_members {a : Space n} {R : ℝ} {S Q : ℕ × Space n} :
    Q ∈ d1bforest_members P c B H a R S ↔
      P.InForest a R Q ∧ ∃ s, d1bforest_state P c B H Q.1 Q.2 = some (S, s) := Iff.rfl

theorem d1bforest_isCell_of_inForest {a : Space n} {R : ℝ} {Q : ℕ × Space n}
    (h : P.InForest a R Q) : P.IsCell Q := by
  obtain ⟨_, _, _, hb⟩ := h
  exact hb.1

/-- The root forest is closed upward along cells. -/
theorem d1bforest_inForest_up (hT : PartitionTree P) {a : Space n} {R : ℝ} {Q T : ℕ × Space n}
    (hQ : P.InForest a R Q) (hQT : P.IsBelow Q T) (hTc : P.IsCell T) : P.InForest a R T := by
  obtain ⟨z₀, hz₀, hne, hb⟩ := hQ
  exact ⟨z₀, hz₀, hne, hT.isBelow_of_common Q (0, z₀) T hz₀ hTc hb hQT (Nat.zero_le _)⟩

theorem d1bforest_below_root (hHB : H ≤ B) {a : Space n} {R : ℝ} {S Q : ℕ × Space n}
    (hQ : Q ∈ d1bforest_members P c B H a R S) : P.IsBelow Q S := by
  obtain ⟨hf, s, hs⟩ := d1bforest_mem_members.mp hQ
  exact (d1bforest_state_spec hHB Q.1 Q.2 (d1bforest_isCell_of_inForest hf) S s hs).2.1

theorem d1bforest_member_coeff {a : Space n} {R : ℝ} {S Q : ℕ × Space n}
    (hQ : Q ∈ d1bforest_members P c B H a R S) : c Q ≤ H := by
  obtain ⟨-, s, hs⟩ := d1bforest_mem_members.mp hQ
  exact not_lt.mp (d1bforest_state_not_bad hs)

/-- **Heredity**: every cell between a member and its root is a member. -/
theorem d1bforest_hereditary (hT : PartitionTree P) {a : Space n} {R : ℝ} {S Q Q' : ℕ × Space n}
    (hS : S ∈ d1bforest_roots P c B H a R) (hQ : Q ∈ d1bforest_members P c B H a R S)
    (hQQ' : P.IsBelow Q Q') (hQ'S : P.IsBelow Q' S) : Q' ∈ d1bforest_members P c B H a R S := by
  obtain ⟨hQf, s, hs⟩ := d1bforest_mem_members.mp hQ
  refine d1bforest_mem_members.mpr
    ⟨hT.inForest_of_isBelow a R Q' S (d1bforest_mem_roots.mp hS).1 hQ'S, ?_⟩
  obtain ⟨q₁, q₂⟩ := Q
  obtain ⟨i, z⟩ := Q'
  obtain ⟨d, rfl⟩ : ∃ d, q₁ = i + d := Nat.exists_eq_add_of_le hQQ'.2.1
  exact d1bforest_state_ancestor hT hQ'S.1 d q₂ (d1bforest_isCell_of_inForest hQf) S s hs hQQ'
    hQ'S.2.1

/-- **Classification**: a forest cell is a bad block in no region, or a nonbad member of exactly
one region. -/
theorem d1bforest_classify (hT : PartitionTree P) (hHB : H ≤ B) {a : Space n} {R : ℝ}
    (Q : ℕ × Space n) (hQ : P.InForest a R Q) :
    (Q ∈ d1bforest_bad P c H a R ∧
        ∀ S : d1bforest_roots P c B H a R, Q ∉ d1bforest_members P c B H a R S.1) ∨
      (Q ∉ d1bforest_bad P c H a R ∧
        ∃! S : d1bforest_roots P c B H a R, Q ∈ d1bforest_members P c B H a R S.1) := by
  have hQc := d1bforest_isCell_of_inForest hQ
  by_cases hc : H < c Q
  · refine Or.inl ⟨d1bforest_mem_bad.mpr ⟨hQ, hc⟩, fun S hm => ?_⟩
    obtain ⟨-, s, hs⟩ := d1bforest_mem_members.mp hm
    exact d1bforest_state_not_bad hs hc
  · refine Or.inr ⟨fun hb => hc (d1bforest_mem_bad.mp hb).2, ?_⟩
    rcases hσ : d1bforest_state P c B H Q.1 Q.2 with _ | ⟨S, s⟩
    · exact absurd ((d1bforest_state_eq_none Q.1 Q.2).mp hσ) hc
    · obtain ⟨hScell, hQS, hroot, -⟩ := d1bforest_state_spec hHB Q.1 Q.2 hQc S s hσ
      refine ⟨⟨S, d1bforest_mem_roots.mpr ⟨d1bforest_inForest_up hT hQ hQS hScell, hroot⟩⟩,
        d1bforest_mem_members.mpr ⟨hQ, s, hσ⟩, ?_⟩
      rintro ⟨S', hS'⟩ hm
      obtain ⟨-, s', hs'⟩ := d1bforest_mem_members.mp hm
      rw [hσ] at hs'
      exact Subtype.ext (Prod.mk.inj (Option.some.inj hs')).1.symm

/-! ## (b) The chain-sum identity, the budget and the entries -/

theorem d1bforest_chainSum_eq (μ : Measure (Space n)) (k : ℕ) (Λ : ℝ) (𝒮 : Set (ℕ × Space n))
    (Q : ℕ × Space n) : chainSum P μ k Λ 𝒮 Q = d1bforest_csum P (P.coeff μ k Λ) 𝒮 Q := rfl

/-- The chain sum at a root is its own coefficient. -/
theorem d1bforest_chain_self (hT : PartitionTree P) (hHB : H ≤ B) {a : Space n} {R : ℝ}
    {j : ℕ} {w : Space n} (hw : w ∈ P.center j) (hf : P.InForest a R (j, w)) {s : ℝ≥0∞}
    (h : d1bforest_state P c B H j w = some ((j, w), s)) :
    d1bforest_csum P c (d1bforest_members P c B H a R (j, w)) (j, w) = c (j, w) := by
  have hset : {Q' : ℕ × Space n |
      Q' ∈ d1bforest_members P c B H a R (j, w) ∧ P.IsBelow (j, w) Q'} = {(j, w)} := by
    ext Q'
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hm, hb⟩
      obtain ⟨hQ'f, s', hs'⟩ := d1bforest_mem_members.mp hm
      have hb' :=
        (d1bforest_state_spec hHB Q'.1 Q'.2 (d1bforest_isCell_of_inForest hQ'f) _ s' hs').2.1
      exact hT.eq_of_isBelow Q' (j, w) hw hb' (le_antisymm hb.2.1 hb'.2.1)
    · rintro rfl
      exact ⟨d1bforest_mem_members.mpr ⟨hf, s, h⟩, hT.isBelow_refl _ hw⟩
  rw [d1bforest_csum, hset, tsum_singleton]

/-- **Chain-sum identity** by induction on the level. -/
theorem d1bforest_chain_level (hT : PartitionTree P) (hHB : H ≤ B) {a : Space n} {R : ℝ}
    (j : ℕ) : ∀ w ∈ P.center j, P.InForest a R (j, w) → ∀ (S : ℕ × Space n) (s : ℝ≥0∞),
      d1bforest_state P c B H j w = some (S, s) →
        d1bforest_csum P c (d1bforest_members P c B H a R S) (j, w) = s := by
  induction j with
  | zero =>
    intro w hw hf S s h
    have h0 := h
    rw [d1bforest_state_zero] at h0
    obtain ⟨-, ⟨rfl, rfl, -⟩ | ⟨s', hs', -⟩⟩ := d1bforest_step_cases h0
    · exact d1bforest_chain_self hT hHB hw hf h
    · exact absurd hs'.symm (Option.some_ne_none _)
  | succ j ih =>
    intro w hw hf S s h
    by_cases hS : S = (j + 1, w)
    · subst hS
      obtain ⟨rfl, -, -⟩ := d1bforest_state_new hHB hw h
      exact d1bforest_chain_self hT hHB hw hf h
    · obtain ⟨s', hs', rfl, -⟩ := d1bforest_state_inherit h hS
      have hp : P.parent j w ∈ P.center j := P.parent_mem j w hw
      have hpar : P.IsBelow (j + 1, w) (j, P.parent j w) :=
        ⟨hw, Nat.le_succ j, P.cell_subset_parent j w hw⟩
      have hpf : P.InForest a R (j, P.parent j w) := d1bforest_inForest_up hT hf hpar hp
      have hset : {Q' : ℕ × Space n |
          Q' ∈ d1bforest_members P c B H a R S ∧ P.IsBelow (j + 1, w) Q'} =
          {(j + 1, w)} ∪ {Q' : ℕ × Space n |
            Q' ∈ d1bforest_members P c B H a R S ∧ P.IsBelow (j, P.parent j w) Q'} := by
        ext Q'
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hm, hb⟩
          have hQ'c := d1bforest_isCell_of_inForest (d1bforest_mem_members.mp hm).1
          by_cases hlev : Q'.1 = j + 1
          · exact Or.inl (hT.eq_of_isBelow (j + 1, w) Q' hQ'c hb hlev.symm).symm
          · refine Or.inr ⟨hm, hT.isBelow_of_common (j + 1, w) Q' (j, P.parent j w) hQ'c hp hb
              hpar ?_⟩
            have h1 : Q'.1 ≤ j + 1 := hb.2.1
            show Q'.1 ≤ j
            omega
        · rintro (rfl | ⟨hm, hb⟩)
          · exact ⟨d1bforest_mem_members.mpr ⟨hf, _, h⟩, hT.isBelow_refl _ hw⟩
          · exact ⟨hm, hT.isBelow_trans _ _ _ hpar hb⟩
      have hnot : ((j + 1, w) : ℕ × Space n) ∉ {Q' : ℕ × Space n |
          Q' ∈ d1bforest_members P c B H a R S ∧ P.IsBelow (j, P.parent j w) Q'} := by
        rintro ⟨-, hb⟩
        exact Nat.not_succ_le_self j hb.2.1
      have ih' := ih (P.parent j w) hp hpf S s' hs'
      rw [d1bforest_csum] at ih' ⊢
      rw [hset, Summable.tsum_union_disjoint (Set.disjoint_singleton_left.mpr hnot)
        ENNReal.summable ENNReal.summable, tsum_singleton, ih', add_comm]

/-- The chain-sum identity for a member: `chainSum (members S) Q` is the recorded sum. -/
theorem d1bforest_chain (hT : PartitionTree P) (hHB : H ≤ B) {a : Space n} {R : ℝ}
    {S Q : ℕ × Space n} (hQ : Q ∈ d1bforest_members P c B H a R S) {s : ℝ≥0∞}
    (h : d1bforest_state P c B H Q.1 Q.2 = some (S, s)) :
    d1bforest_csum P c (d1bforest_members P c B H a R S) Q = s :=
  d1bforest_chain_level hT hHB Q.1 Q.2
    (d1bforest_isCell_of_inForest (d1bforest_mem_members.mp hQ).1)
    (d1bforest_mem_members.mp hQ).1 S s h

/-- **Budget**: the inclusive chain sum of a member is at most `B`. -/
theorem d1bforest_chain_budget (hT : PartitionTree P) (hHB : H ≤ B) {a : Space n} {R : ℝ}
    {S Q : ℕ × Space n} (hQ : Q ∈ d1bforest_members P c B H a R S) :
    d1bforest_csum P c (d1bforest_members P c B H a R S) Q ≤ B := by
  obtain ⟨hf, s, hs⟩ := d1bforest_mem_members.mp hQ
  rw [d1bforest_chain hT hHB hQ hs]
  exact (d1bforest_state_spec hHB Q.1 Q.2 (d1bforest_isCell_of_inForest hf) S s hs).2.2.2

/-- **Entries of a root**: a top cell, a child of a bad block, or a budget exit whose parent's
chain sum exceeds `H`. -/
theorem d1bforest_root_entry (hT : PartitionTree P) (hHB : H ≤ B) (hHH : H + H ≤ B)
    {a : Space n} {R : ℝ} {S : ℕ × Space n} (hS : S ∈ d1bforest_roots P c B H a R) :
    S.1 = 0 ∨ (∃ Q ∈ d1bforest_bad P c H a R, Q.1 + 1 = S.1 ∧ P.IsBelow S Q) ∨
      (∃ S' ∈ d1bforest_roots P c B H a R, ∃ Q ∈ d1bforest_members P c B H a R S',
        Q.1 + 1 = S.1 ∧ P.IsBelow S Q ∧
          H < d1bforest_csum P c (d1bforest_members P c B H a R S') Q) := by
  obtain ⟨hf, s₀, hs₀⟩ := d1bforest_mem_roots.mp hS
  obtain ⟨j, w⟩ := S
  cases j with
  | zero => exact Or.inl rfl
  | succ j =>
    right
    have hw : w ∈ P.center (j + 1) := d1bforest_isCell_of_inForest hf
    have hp : P.parent j w ∈ P.center j := P.parent_mem j w hw
    have hpar : P.IsBelow (j + 1, w) (j, P.parent j w) :=
      ⟨hw, Nat.le_succ j, P.cell_subset_parent j w hw⟩
    have hpf : P.InForest a R (j, P.parent j w) := d1bforest_inForest_up hT hf hpar hp
    obtain ⟨rfl, hc, hnone | ⟨S', s', hs', hB⟩⟩ := d1bforest_state_new hHB hw hs₀
    · left
      exact ⟨(j, P.parent j w),
        d1bforest_mem_bad.mpr ⟨hpf, (d1bforest_state_eq_none j (P.parent j w)).mp hnone⟩, rfl, hpar⟩
    · right
      obtain ⟨hS'c, hpS', hroot, -⟩ := d1bforest_state_spec hHB j (P.parent j w) hp S' s' hs'
      have hmem : (j, P.parent j w) ∈ d1bforest_members P c B H a R S' :=
        d1bforest_mem_members.mpr ⟨hpf, s', hs'⟩
      refine ⟨S', d1bforest_mem_roots.mpr ⟨d1bforest_inForest_up hT hpf hpS' hS'c, hroot⟩,
        (j, P.parent j w), hmem, rfl, hpar, ?_⟩
      rw [d1bforest_chain hT hHB hmem hs']
      by_contra hle
      have hle' : s' ≤ H := not_lt.mp hle
      exact absurd hB (not_lt.mpr ((add_le_add hle' (not_lt.mp hc)).trans hHH))

/-- **Assembly**: a stopping forest exists for every direct partition satisfying the tree facts. -/
theorem d1bforest_nonempty (hT : PartitionTree P) (μ : Measure (Space n)) (k : ℕ) (Λ b : ℝ)
    (a : Space n) (R : ℝ) (hb : 0 < b) : Nonempty (StoppingForest P μ k Λ b a R) := by
  have hHH : ENNReal.ofReal (b / 2) + ENNReal.ofReal (b / 2) ≤ ENNReal.ofReal b :=
    le_of_eq (by rw [← ENNReal.ofReal_add (half_pos hb).le (half_pos hb).le, add_halves])
  have hHB : ENNReal.ofReal (b / 2) ≤ ENNReal.ofReal b :=
    ENNReal.ofReal_le_ofReal (half_le_self hb.le)
  exact ⟨{
    bad := d1bforest_bad P (P.coeff μ k Λ) (ENNReal.ofReal (b / 2)) a R
    roots := d1bforest_roots P (P.coeff μ k Λ) (ENNReal.ofReal b) (ENNReal.ofReal (b / 2)) a R
    members :=
      d1bforest_members P (P.coeff μ k Λ) (ENNReal.ofReal b) (ENNReal.ofReal (b / 2)) a R
    bad_forest := fun _ hQ => (d1bforest_mem_bad.mp hQ).1
    roots_forest := fun _ hS => (d1bforest_mem_roots.mp hS).1
    bad_coeff := fun _ hQ => (d1bforest_mem_bad.mp hQ).2
    root_mem := fun _ hS => d1bforest_mem_members.mpr (d1bforest_mem_roots.mp hS)
    below_root := fun _ _ _ hQ => d1bforest_below_root hHB hQ
    hereditary := fun _ hS _ hQ _ h₁ h₂ => d1bforest_hereditary hT hS hQ h₁ h₂
    member_coeff := fun _ _ _ hQ => d1bforest_member_coeff hQ
    chain_budget := fun _ _ _ hQ => d1bforest_chain_budget hT hHB hQ
    classify := fun Q hQ => d1bforest_classify hT hHB Q hQ
    root_entry := fun _ hS => d1bforest_root_entry hT hHB hHH hS }⟩

end State

/-- **The combinatorial stopping forest exists** (`StoppingForestStatement`, in implication
form). -/
theorem d1b_stoppingForest_proof : PartitionTreeStatement → StoppingForestStatement := by
  intro hT n E ℓ₀ P μ k Λ b a R hb
  exact d1bforest_nonempty (hT n E ℓ₀ P) μ k Λ b a R hb

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
