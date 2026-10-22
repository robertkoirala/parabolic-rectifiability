import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Stopping

/-! # The first-entrance inequality

Proof of `d1b_firstEntrance_proof`, in implication form
`PartitionTreeStatement → ExitMassStatement → FirstEntranceStatement` (the two statements are
hypotheses). Strict ancestry is by generation; the stopping forest records sufficient
properties, not an exact maximal stopping.

At a cell `T`, with `ℛ_T` the roots and bad blocks below `T` (`d1bentry_entrySet`):

* **Part (a): first entrances and charging.** The first entrances (`d1bentry_firstEntrances`) are
  the elements of `ℛ_T` with no strict ancestor in `ℛ_T`, where strict ancestry is
  `DirectPartition.IsBelow` together with a strictly smaller generation (not strict containment of
  cell sets). They form an antichain, so their cells are pairwise disjoint and their total mass is
  `≤ μ(T)` (`d1bentry_firstEntrances_disjoint`, `d1bentry_firstEntrances_mass`). A non-maximal
  element `S` has a strict ancestor `S'' ∈ ℛ_T`, hence `1 ≤ S.1` and its parent cell lies below `T`
  (`d1bentry_nonmax_parent`); it is a bad block below `T`, or a root whose parent is a bad block
  below `T`, or a budget exit of the region of a root `S'` below `T`
  (`d1bentry_charging`; the last because otherwise `S''` would be a member of the region of `S'`,
  contradicting `classify`).
* **Part (b): the grouped energy estimate.** A bad block costs `(2/b) a_Q μ(Q)`; the child roots
  of a bad block `Q` have total mass `≤ μ(Q) ≤ (2/b) a_Q μ(Q)` (the second bad-energy charge, which
  pays the bad-parent term); the exits of the region of a root `S' ⊂ T` cost
`(2/b) ∑_{Q ∈ members S'} a_Q μ(Q)` by the exit mass estimate, and the regions are disjoint by `classify`. The total
  is `μ(T) + (2/b)(2 ∑_{bad ⊂ T} + ∑_{good ⊂ T}) a_Q μ(Q) ≤ μ(T) + (4/b) ∑_{Q ⊂ T} a_Q μ(Q)`.

All sums are `ℝ≥0∞`-valued `tsum`s over subtypes, so no finite-depth limit is needed. Helpers carry
the prefix `d1bentry_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal Function

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

section FirstEntrance

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
  {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} {a : Space n} {R : ℝ}

/-! ## The index sets -/

/-- `ℛ_T`: the roots and the bad blocks below `T` (the index set of (4.3)). -/
def d1bentry_entrySet (F : StoppingForest P μ k Λ b a R) (T : ℕ × Space n) :
    Set (ℕ × Space n) :=
  {S | (S ∈ F.roots ∨ S ∈ F.bad) ∧ P.IsBelow S T}

/-- **The first entrances into `T`**: the elements of `ℛ_T` without a strict ancestor in `ℛ_T`,
strict ancestry meaning `IsBelow` with a strictly smaller generation. -/
def d1bentry_firstEntrances (F : StoppingForest P μ k Λ b a R) (T : ℕ × Space n) :
    Set (ℕ × Space n) :=
  {S | S ∈ d1bentry_entrySet F T ∧
    ∀ S'' ∈ d1bentry_entrySet F T, P.IsBelow S S'' → S.1 ≤ S''.1}

/-- The bad blocks below `T`. -/
def d1bentry_badBelow (F : StoppingForest P μ k Λ b a R) (T : ℕ × Space n) :
    Set (ℕ × Space n) :=
  {Q | Q ∈ F.bad ∧ P.IsBelow Q T}

/-- The nonbad cells below `T`. -/
def d1bentry_goodBelow (F : StoppingForest P μ k Λ b a R) (T : ℕ × Space n) :
    Set (ℕ × Space n) :=
  {Q | Q ∉ F.bad ∧ P.IsBelow Q T}

/-- The roots below `T`. -/
def d1bentry_rootsBelow (F : StoppingForest P μ k Λ b a R) (T : ℕ × Space n) :
    Set (ℕ × Space n) :=
  {S | S ∈ F.roots ∧ P.IsBelow S T}

/-- The child roots of a cell `Q`: roots one generation below `Q` and below `Q`. -/
def d1bentry_childRoots (F : StoppingForest P μ k Λ b a R) (Q : ℕ × Space n) :
    Set (ℕ × Space n) :=
  {S | S ∈ F.roots ∧ Q.1 + 1 = S.1 ∧ P.IsBelow S Q}

/-! ## Facts about the stopping forest -/

/-- A forest cell is a cell. -/
theorem d1bentry_isCell_of_inForest {Q : ℕ × Space n} (h : P.InForest a R Q) : P.IsCell Q := by
  obtain ⟨_, _, _, hQ⟩ := h
  exact hQ.1

/-- A member of a region is a forest cell. -/
theorem d1bentry_member_inForest (hP : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {S Q : ℕ × Space n} (hS : S ∈ F.roots) (hQ : Q ∈ F.members S) : P.InForest a R Q :=
  hP.inForest_of_isBelow a R Q S (F.roots_forest S hS) (F.below_root S hS Q hQ)

/-- A member of a region is not bad (`classify`). -/
theorem d1bentry_member_not_bad (hP : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {S Q : ℕ × Space n} (hS : S ∈ F.roots) (hQ : Q ∈ F.members S) : Q ∉ F.bad := by
  rcases F.classify Q (d1bentry_member_inForest hP F hS hQ) with ⟨-, hnot⟩ | ⟨hnb, -⟩
  · exact absurd hQ (hnot ⟨S, hS⟩)
  · exact hnb

/-- A cell is a member of at most one region (`classify`). -/
theorem d1bentry_member_unique (hP : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {S₁ S₂ Q : ℕ × Space n} (h₁ : S₁ ∈ F.roots) (h₂ : S₂ ∈ F.roots)
    (hQ₁ : Q ∈ F.members S₁) (hQ₂ : Q ∈ F.members S₂) : S₁ = S₂ := by
  rcases F.classify Q (d1bentry_member_inForest hP F h₁ hQ₁) with ⟨-, hnot⟩ | ⟨-, hex⟩
  · exact absurd hQ₁ (hnot ⟨S₁, h₁⟩)
  · exact congrArg Subtype.val (hex.unique (y₁ := ⟨S₁, h₁⟩) (y₂ := ⟨S₂, h₂⟩) hQ₁ hQ₂)

/-! ## Antichains of cells -/

/-- Cells of a family without strict ancestry by generation inside the family are pairwise
disjoint (nested-or-disjoint, and nested cells of one generation coincide). -/
theorem d1bentry_disjoint_of_antichain (hP : PartitionTree P) {𝒜 : Set (ℕ × Space n)}
    (hcell : ∀ S ∈ 𝒜, P.IsCell S)
    (hanti : ∀ S₁ ∈ 𝒜, ∀ S₂ ∈ 𝒜, P.IsBelow S₁ S₂ → S₁.1 ≤ S₂.1) :
    Pairwise (Disjoint on fun S : 𝒜 => P.cellOf S.1) := by
  have key : ∀ S₁ S₂ : 𝒜, S₁ ≠ S₂ → S₂.1.1 ≤ S₁.1.1 →
      Disjoint (P.cellOf S₁.1) (P.cellOf S₂.1) := by
    intro S₁ S₂ hne hle
    rcases hP.isBelow_or_disjoint S₁.1 S₂.1 (hcell _ S₁.2) (hcell _ S₂.2) hle with h | h
    · exact absurd (Subtype.ext (hP.eq_of_isBelow S₁.1 S₂.1 (hcell _ S₂.2) h
        (le_antisymm (hanti _ S₁.2 _ S₂.2 h) hle))) hne
    · exact h
  intro S₁ S₂ hne
  rcases le_total S₂.1.1 S₁.1.1 with hle | hle
  · exact key S₁ S₂ hne hle
  · exact (key S₂ S₁ hne.symm hle).symm

/-- The cells of an antichain below `U` have total mass at most `ν(U)`. -/
theorem d1bentry_tsum_le_of_antichain (hP : PartitionTree P) (ν : Measure (Space n))
    (U : ℕ × Space n) {𝒜 : Set (ℕ × Space n)} (hbelow : ∀ S ∈ 𝒜, P.IsBelow S U)
    (hanti : ∀ S₁ ∈ 𝒜, ∀ S₂ ∈ 𝒜, P.IsBelow S₁ S₂ → S₁.1 ≤ S₂.1) :
    ∑' S : 𝒜, ν (P.cellOf S.1) ≤ ν (P.cellOf U) := by
  calc ∑' S : 𝒜, ν (P.cellOf S.1) ≤ ν (⋃ S : 𝒜, P.cellOf S.1) :=
        MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint ν
          (fun S : 𝒜 => P.measurable_cell S.1.1 S.1.2)
          (d1bentry_disjoint_of_antichain hP (fun S hS => (hbelow S hS).1) hanti)
    _ ≤ ν (P.cellOf U) :=
        MeasureTheory.measure_mono (Set.iUnion_subset fun S : 𝒜 => (hbelow S.1 S.2).2.2)

/-! ## Part (a): the first-entrance antichain -/

/-- First entrances have no strict ancestor (by generation) among the first entrances. -/
theorem d1bentry_firstEntrances_antichain (F : StoppingForest P μ k Λ b a R)
    (T : ℕ × Space n) :
    ∀ S₁ ∈ d1bentry_firstEntrances F T, ∀ S₂ ∈ d1bentry_firstEntrances F T,
      P.IsBelow S₁ S₂ → S₁.1 ≤ S₂.1 :=
  fun _ h₁ S₂ h₂ h => h₁.2 S₂ h₂.1 h

/-- **The first entrances have pairwise disjoint cells.** -/
theorem d1bentry_firstEntrances_disjoint (hP : PartitionTree P)
    (F : StoppingForest P μ k Λ b a R) (T : ℕ × Space n) :
    Pairwise (Disjoint on fun S : d1bentry_firstEntrances F T => P.cellOf S.1) :=
  d1bentry_disjoint_of_antichain hP (fun _ hS => hS.1.2.1)
    (d1bentry_firstEntrances_antichain F T)

/-- **The first entrances into `T` have total mass at most `μ(T)`.** -/
theorem d1bentry_firstEntrances_mass (hP : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    (T : ℕ × Space n) :
    ∑' S : d1bentry_firstEntrances F T, μ (P.cellOf S.1) ≤ μ (P.cellOf T) :=
  d1bentry_tsum_le_of_antichain hP μ T (fun _ hS => hS.1.2)
    (d1bentry_firstEntrances_antichain F T)

/-! ## Part (a): the charging classification -/

/-- A non-maximal element of `ℛ_T` has a strict ancestor (by generation) in `ℛ_T`. -/
theorem d1bentry_exists_strict_ancestor (F : StoppingForest P μ k Λ b a R) (T : ℕ × Space n)
    {S : ℕ × Space n} (hS : S ∈ d1bentry_entrySet F T)
    (hSmax : S ∉ d1bentry_firstEntrances F T) :
    ∃ S'' ∈ d1bentry_entrySet F T, P.IsBelow S S'' ∧ S''.1 < S.1 := by
  by_contra h
  apply hSmax
  refine ⟨hS, fun S'' hS'' hb => ?_⟩
  by_contra hlt
  exact h ⟨S'', hS'', hb, by omega⟩

/-- A cell `Q` one generation above `S` with `S ⊂ Q`, where `S` lies strictly below
`S'' ⊂ T`, lies below `S''` and below `T`. -/
theorem d1bentry_parent_below (hP : PartitionTree P) {S S'' Q T : ℕ × Space n}
    (hS''T : P.IsBelow S'' T) (hSS'' : P.IsBelow S S'') (hlt : S''.1 < S.1)
    (hQ : P.IsCell Q) (hQS : Q.1 + 1 = S.1) (hSQ : P.IsBelow S Q) :
    P.IsBelow Q S'' ∧ P.IsBelow Q T := by
  have h1 : P.IsBelow Q S'' :=
    hP.isBelow_of_common S S'' Q hS''T.1 hQ hSS'' hSQ (by omega)
  exact ⟨h1, hP.isBelow_trans Q S'' T h1 hS''T⟩

/-- **A non-maximal element of `ℛ_T` has generation `≥ 1` and its parent cell lies below `T`.** -/
theorem d1bentry_nonmax_parent (hP : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {T S : ℕ × Space n} (hS : S ∈ d1bentry_entrySet F T)
    (hSmax : S ∉ d1bentry_firstEntrances F T) :
    1 ≤ S.1 ∧ ∃ Q : ℕ × Space n, P.IsCell Q ∧ Q.1 + 1 = S.1 ∧ P.IsBelow S Q ∧
      P.IsBelow Q T := by
  obtain ⟨S'', hS''R, hSS'', hlt⟩ := d1bentry_exists_strict_ancestor F T hS hSmax
  obtain ⟨Q, hQ, hQ1, hSQ⟩ := hP.exists_ancestor S hS.2.1 (S.1 - 1) (Nat.sub_le _ _)
  have hQS : Q.1 + 1 = S.1 := by omega
  exact ⟨by omega, Q, hQ, hQS, hSQ, (d1bentry_parent_below hP hS''R.2 hSS'' hlt hQ hQS hSQ).2⟩

/-- **The charging classification.** A non-maximal element `S` of `ℛ_T` is a bad block below `T`,
or a root whose parent is a bad block below `T`, or a budget exit of the region of a root `S'`
below `T`. In the last case `S' ⊂ T`: otherwise `T ⊂ S'`, and the strict ancestor `S'' ∈ ℛ_T` of
`S` would be a member of the region of `S'` strictly between (heredity), contradicting
`classify`. -/
theorem d1bentry_charging (hP : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {T : ℕ × Space n} (hT : P.IsCell T) {S : ℕ × Space n}
    (hS : S ∈ d1bentry_entrySet F T) (hSmax : S ∉ d1bentry_firstEntrances F T) :
    (S ∈ F.bad ∧ P.IsBelow S T) ∨
      (S ∈ F.roots ∧ ∃ Q ∈ F.bad, P.IsBelow Q T ∧ Q.1 + 1 = S.1 ∧ P.IsBelow S Q) ∨
      (∃ S' ∈ F.roots, P.IsBelow S' T ∧ S ∈ F.exits S') := by
  obtain ⟨S'', hS''R, hSS'', hlt⟩ := d1bentry_exists_strict_ancestor F T hS hSmax
  obtain ⟨hrb, hST⟩ := hS
  rcases hrb with hroot | hbad
  · right
    rcases F.root_entry S hroot with h0 | ⟨Q, hQbad, hQS, hSQ⟩ | ⟨S', hS', Q, hQ, hQS, hSQ, -⟩
    · exfalso
      omega
    · left
      have hQcell : P.IsCell Q := d1bentry_isCell_of_inForest (F.bad_forest Q hQbad)
      exact ⟨hroot, Q, hQbad,
        (d1bentry_parent_below hP hS''R.2 hSS'' hlt hQcell hQS hSQ).2, hQS, hSQ⟩
    · right
      have hQS' : P.IsBelow Q S' := F.below_root S' hS' Q hQ
      obtain ⟨hQS'', hQT⟩ := d1bentry_parent_below hP hS''R.2 hSS'' hlt hQS'.1 hQS hSQ
      have hS'cell : P.IsCell S' := d1bentry_isCell_of_inForest (F.roots_forest S' hS')
      refine ⟨S', hS', ?_, ⟨hroot, Q, hQ, hQS, hSQ⟩⟩
      rcases le_or_gt T.1 S'.1 with hle | hlt'
      · exact hP.isBelow_of_common Q T S' hT hS'cell hQT hQS' hle
      · exfalso
        have hTS' : P.IsBelow T S' := hP.isBelow_of_common Q S' T hS'cell hT hQS' hQT hlt'.le
        have hS''S' : P.IsBelow S'' S' := hP.isBelow_trans S'' T S' hS''R.2 hTS'
        have hmem : S'' ∈ F.members S' := F.hereditary S' hS' Q hQ S'' hQS'' hS''S'
        rcases hS''R.1 with hS''root | hS''bad
        · have heq : S'' = S' :=
            d1bentry_member_unique hP F hS''root hS' (F.root_mem S'' hS''root) hmem
          have h1 : T.1 ≤ S''.1 := hS''R.2.2.1
          rw [heq] at h1
          omega
        · exact d1bentry_member_not_bad hP F hS' hmem hS''bad
  · left
    exact ⟨hbad, hST⟩

/-- `ℛ_T` is covered by the first entrances, the bad blocks below `T`, the child roots of the bad
blocks below `T`, and the exits of the regions of the roots below `T`. -/
theorem d1bentry_entrySet_subset (hP : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {T : ℕ × Space n} (hT : P.IsCell T) :
    d1bentry_entrySet F T ⊆ d1bentry_firstEntrances F T ∪
      (d1bentry_badBelow F T ∪ ((⋃ Q ∈ d1bentry_badBelow F T, d1bentry_childRoots F Q) ∪
        ⋃ S' ∈ d1bentry_rootsBelow F T, F.exits S')) := by
  intro S hS
  by_cases hmax : S ∈ d1bentry_firstEntrances F T
  · exact Or.inl hmax
  · right
    rcases d1bentry_charging hP F hT hS hmax with
      h | ⟨hroot, Q, hQbad, hQT, hQS, hSQ⟩ | ⟨S', hS', hS'T, hex⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl (Set.mem_biUnion (x := Q) ⟨hQbad, hQT⟩ ⟨hroot, hQS, hSQ⟩))
    · exact Or.inr (Or.inr (Set.mem_biUnion (x := S') ⟨hS', hS'T⟩ hex))

/-! ## Part (b): the grouped energy estimate -/

/-- `(b/2) x ≤ y` gives `x ≤ (2/b) y`. -/
theorem d1bentry_le_of_half_mul_le (hb : 0 < b) {x y : ℝ≥0∞}
    (h : ENNReal.ofReal (b / 2) * x ≤ y) : x ≤ ENNReal.ofReal (2 / b) * y := by
  have h1 : ENNReal.ofReal (2 / b) * ENNReal.ofReal (b / 2) = 1 := by
    rw [← ENNReal.ofReal_mul (div_pos two_pos hb).le, ← ENNReal.ofReal_one]
    congr 1
    rw [div_mul_div_comm, mul_comm 2 b]
    exact div_self (mul_pos hb two_pos).ne'
  calc x = ENNReal.ofReal (2 / b) * ENNReal.ofReal (b / 2) * x := by rw [h1, one_mul]
    _ = ENNReal.ofReal (2 / b) * (ENNReal.ofReal (b / 2) * x) := mul_assoc _ _ _
    _ ≤ ENNReal.ofReal (2 / b) * y := mul_le_mul' le_rfl h

/-- A bad block pays for itself: `a_Q > b/2` gives `μ(Q) ≤ (2/b) a_Q μ(Q)`. -/
theorem d1bentry_bad_mass_le (hb : 0 < b) {c m : ℝ≥0∞} (hc : ENNReal.ofReal (b / 2) < c) :
    m ≤ ENNReal.ofReal (2 / b) * (c * m) :=
  d1bentry_le_of_half_mul_le hb (mul_le_mul' hc.le le_rfl)

/-- **First bad-energy charge**: the bad blocks below `T` have total mass at most
`(2/b) ∑_{Q bad ⊂ T} a_Q μ(Q)`. -/
theorem d1bentry_badBelow_mass (hb : 0 < b) (F : StoppingForest P μ k Λ b a R)
    (T : ℕ × Space n) :
    ∑' S : d1bentry_badBelow F T, μ (P.cellOf S.1) ≤
      ENNReal.ofReal (2 / b) *
        ∑' Q : d1bentry_badBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) :=
  calc ∑' S : d1bentry_badBelow F T, μ (P.cellOf S.1)
      ≤ ∑' S : d1bentry_badBelow F T,
          ENNReal.ofReal (2 / b) * (P.coeff μ k Λ S.1 * μ (P.cellOf S.1)) :=
        ENNReal.tsum_le_tsum fun S => d1bentry_bad_mass_le hb (F.bad_coeff S.1 S.2.1)
    _ = ENNReal.ofReal (2 / b) *
          ∑' Q : d1bentry_badBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) :=
        ENNReal.tsum_mul_left

/-- The child roots of a cell `Q` have total mass at most `μ(Q)` (one generation: an antichain). -/
theorem d1bentry_childRoots_mass (hP : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    (Q : ℕ × Space n) :
    ∑' S : d1bentry_childRoots F Q, μ (P.cellOf S.1) ≤ μ (P.cellOf Q) :=
  d1bentry_tsum_le_of_antichain hP μ Q (fun _ hS => hS.2.2) fun S₁ h₁ S₂ h₂ _ => by
    have e₁ : Q.1 + 1 = S₁.1 := h₁.2.1
    have e₂ : Q.1 + 1 = S₂.1 := h₂.2.1
    omega

/-- **Second bad-energy charge (the bad-parent term)**: the child roots of the bad blocks below
`T` have total mass at most `(2/b) ∑_{Q bad ⊂ T} a_Q μ(Q)`. -/
theorem d1bentry_badParent_mass (hP : PartitionTree P) (hb : 0 < b)
    (F : StoppingForest P μ k Λ b a R) (T : ℕ × Space n) :
    ∑' S : ↥(⋃ Q ∈ d1bentry_badBelow F T, d1bentry_childRoots F Q), μ (P.cellOf S.1) ≤
      ENNReal.ofReal (2 / b) *
        ∑' Q : d1bentry_badBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) :=
  calc ∑' S : ↥(⋃ Q ∈ d1bentry_badBelow F T, d1bentry_childRoots F Q), μ (P.cellOf S.1)
      ≤ ∑' Q : d1bentry_badBelow F T, ∑' S : d1bentry_childRoots F Q.1, μ (P.cellOf S.1) :=
        ENNReal.tsum_biUnion_le_tsum (fun S => μ (P.cellOf S)) (d1bentry_badBelow F T)
          (d1bentry_childRoots F)
    _ ≤ ∑' Q : d1bentry_badBelow F T, μ (P.cellOf Q.1) :=
        ENNReal.tsum_le_tsum fun Q => d1bentry_childRoots_mass hP F Q.1
    _ ≤ ENNReal.ofReal (2 / b) *
          ∑' Q : d1bentry_badBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) :=
        d1bentry_badBelow_mass hb F T

/-- The regions of the roots below `T` are pairwise disjoint (`classify`). -/
theorem d1bentry_members_pairwiseDisjoint (hP : PartitionTree P)
    (F : StoppingForest P μ k Λ b a R) (T : ℕ × Space n) :
    (d1bentry_rootsBelow F T).PairwiseDisjoint F.members := by
  intro S₁ h₁ S₂ h₂ hne
  exact Set.disjoint_left.mpr fun Q hQ₁ hQ₂ =>
    hne (d1bentry_member_unique hP F h₁.1 h₂.1 hQ₁ hQ₂)

/-- The members of the regions of the roots below `T` are nonbad cells below `T`. -/
theorem d1bentry_members_subset_goodBelow (hP : PartitionTree P)
    (F : StoppingForest P μ k Λ b a R) (T : ℕ × Space n) :
    (⋃ S' ∈ d1bentry_rootsBelow F T, F.members S') ⊆ d1bentry_goodBelow F T :=
  Set.iUnion₂_subset fun S' hS' Q hQ =>
    ⟨d1bentry_member_not_bad hP F hS'.1 hQ,
      hP.isBelow_trans Q S' T (F.below_root S' hS'.1 Q hQ) hS'.2⟩

/-- **Budget exits**: by (4.2) and the disjointness of the regions, the exits of the regions of
the roots below `T` have total mass at most `(2/b) ∑_{Q good ⊂ T} a_Q μ(Q)`. -/
theorem d1bentry_exits_mass (hP : PartitionTree P) (hb : 0 < b)
    (F : StoppingForest P μ k Λ b a R)
    (hexit : ∀ S' ∈ F.roots,
      ENNReal.ofReal (b / 2) * (∑' S : F.exits S', μ (P.cellOf S.1)) ≤
        ∑' Q : F.members S', P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1))
    (T : ℕ × Space n) :
    ∑' S : ↥(⋃ S' ∈ d1bentry_rootsBelow F T, F.exits S'), μ (P.cellOf S.1) ≤
      ENNReal.ofReal (2 / b) *
        ∑' Q : d1bentry_goodBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) := by
  have hsub := ENNReal.tsum_mono_subtype (fun Q => P.coeff μ k Λ Q * μ (P.cellOf Q))
    (d1bentry_members_subset_goodBelow hP F T)
  calc ∑' S : ↥(⋃ S' ∈ d1bentry_rootsBelow F T, F.exits S'), μ (P.cellOf S.1)
      ≤ ∑' S' : d1bentry_rootsBelow F T, ∑' S : F.exits S'.1, μ (P.cellOf S.1) :=
        ENNReal.tsum_biUnion_le_tsum (fun S => μ (P.cellOf S)) (d1bentry_rootsBelow F T) F.exits
    _ ≤ ∑' S' : d1bentry_rootsBelow F T, ENNReal.ofReal (2 / b) *
          ∑' Q : F.members S'.1, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) :=
        ENNReal.tsum_le_tsum fun S' => d1bentry_le_of_half_mul_le hb (hexit S'.1 S'.2.1)
    _ = ENNReal.ofReal (2 / b) * ∑' S' : d1bentry_rootsBelow F T,
          ∑' Q : F.members S'.1, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (2 / b) * ∑' Q : ↥(⋃ S' ∈ d1bentry_rootsBelow F T, F.members S'),
          P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) :=
        congrArg (fun x => ENNReal.ofReal (2 / b) * x)
          (ENNReal.tsum_biUnion' (f := fun Q => P.coeff μ k Λ Q * μ (P.cellOf Q))
            (d1bentry_members_pairwiseDisjoint hP F T)).symm
    _ ≤ ENNReal.ofReal (2 / b) *
          ∑' Q : d1bentry_goodBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) :=
        mul_le_mul' le_rfl hsub

/-- The bad and the nonbad cells below `T` split the discrete energy below `T`. -/
theorem d1bentry_bad_add_good_le (F : StoppingForest P μ k Λ b a R) (T : ℕ × Space n) :
    (∑' Q : d1bentry_badBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1)) +
        ∑' Q : d1bentry_goodBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) ≤
      P.descendantEnergy μ k Λ T := by
  have hd : Disjoint (d1bentry_badBelow F T) (d1bentry_goodBelow F T) :=
    Set.disjoint_left.mpr fun _ h₁ h₂ => h₂.1 h₁.1
  have hs : d1bentry_badBelow F T ∪ d1bentry_goodBelow F T ⊆
      {Q : ℕ × Space n | P.IsBelow Q T} := by
    intro Q hQ
    rcases hQ with h | h
    · exact h.2
    · exact h.2
  calc (∑' Q : d1bentry_badBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1)) +
        ∑' Q : d1bentry_goodBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1)
      = ∑' Q : ↥(d1bentry_badBelow F T ∪ d1bentry_goodBelow F T),
          P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) :=
        (Summable.tsum_union_disjoint (f := fun Q => P.coeff μ k Λ Q * μ (P.cellOf Q)) hd
          ENNReal.summable ENNReal.summable).symm
    _ ≤ ∑' Q : ↥{Q : ℕ × Space n | P.IsBelow Q T}, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) :=
        ENNReal.tsum_mono_subtype (fun Q => P.coeff μ k Λ Q * μ (P.cellOf Q)) hs
    _ = P.descendantEnergy μ k Λ T := rfl

/-- The constants: `(2/b)(2 W_bad + W_good) ≤ (4/b)(W_bad + W_good) ≤ (4/b) ∑_{Q ⊂ T} a_Q μ(Q)`. -/
theorem d1bentry_charge_combine (hb : 0 < b) (F : StoppingForest P μ k Λ b a R)
    (T : ℕ × Space n) :
    ENNReal.ofReal (2 / b) *
        (∑' Q : d1bentry_badBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1)) +
      (ENNReal.ofReal (2 / b) *
          (∑' Q : d1bentry_badBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1)) +
        ENNReal.ofReal (2 / b) *
          ∑' Q : d1bentry_goodBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1)) ≤
      ENNReal.ofReal (4 / b) * P.descendantEnergy μ k Λ T := by
  have h2b : (0 : ℝ) ≤ 2 / b := (div_pos two_pos hb).le
  have h22 : ENNReal.ofReal (2 / b) + ENNReal.ofReal (2 / b) = ENNReal.ofReal (4 / b) := by
    rw [← ENNReal.ofReal_add h2b h2b]
    congr 1
    ring
  rw [← h22]
  generalize ENNReal.ofReal (2 / b) = c
  generalize hWB : (∑' Q : d1bentry_badBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1)) = WB
  generalize hWG : (∑' Q : d1bentry_goodBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1)) = WG
  have hD : WB + WG ≤ P.descendantEnergy μ k Λ T := by
    rw [← hWB, ← hWG]
    exact d1bentry_bad_add_good_le F T
  calc c * WB + (c * WB + c * WG) = (c + c) * WB + c * WG := by ring
    _ ≤ (c + c) * WB + (c + c) * WG :=
        add_le_add le_rfl (mul_le_mul' le_self_add le_rfl)
    _ = (c + c) * (WB + WG) := (mul_add _ _ _).symm
    _ ≤ (c + c) * P.descendantEnergy μ k Λ T := mul_le_mul' le_rfl hD

/-- **The first-entrance inequality (4.3) at one cell `T`**, given (4.2) for the forest `F`. -/
theorem d1bentry_firstEntrance_cell (hP : PartitionTree P) (hb : 0 < b)
    (F : StoppingForest P μ k Λ b a R)
    (hexit : ∀ S' ∈ F.roots,
      ENNReal.ofReal (b / 2) * (∑' S : F.exits S', μ (P.cellOf S.1)) ≤
        ∑' Q : F.members S', P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1))
    {T : ℕ × Space n} (hT : P.IsCell T) :
    (∑' S : {S : ℕ × Space n // (S ∈ F.roots ∨ S ∈ F.bad) ∧ P.IsBelow S T},
        μ (P.cellOf S.1)) ≤
      μ (P.cellOf T) + ENNReal.ofReal (4 / b) * P.descendantEnergy μ k Λ T := by
  calc (∑' S : {S : ℕ × Space n // (S ∈ F.roots ∨ S ∈ F.bad) ∧ P.IsBelow S T},
        μ (P.cellOf S.1))
      = ∑' S : d1bentry_entrySet F T, μ (P.cellOf S.1) := rfl
    _ ≤ ∑' S : ↥(d1bentry_firstEntrances F T ∪
          (d1bentry_badBelow F T ∪ ((⋃ Q ∈ d1bentry_badBelow F T, d1bentry_childRoots F Q) ∪
            ⋃ S' ∈ d1bentry_rootsBelow F T, F.exits S'))), μ (P.cellOf S.1) :=
        ENNReal.tsum_mono_subtype (fun S => μ (P.cellOf S)) (d1bentry_entrySet_subset hP F hT)
    _ ≤ ∑' S : d1bentry_firstEntrances F T, μ (P.cellOf S.1) +
          (∑' S : d1bentry_badBelow F T, μ (P.cellOf S.1) +
            (∑' S : ↥(⋃ Q ∈ d1bentry_badBelow F T, d1bentry_childRoots F Q),
                μ (P.cellOf S.1) +
              ∑' S : ↥(⋃ S' ∈ d1bentry_rootsBelow F T, F.exits S'), μ (P.cellOf S.1))) :=
        (ENNReal.tsum_union_le (fun S => μ (P.cellOf S)) _ _).trans
          (add_le_add le_rfl ((ENNReal.tsum_union_le (fun S => μ (P.cellOf S)) _ _).trans
            (add_le_add le_rfl (ENNReal.tsum_union_le (fun S => μ (P.cellOf S)) _ _))))
    _ ≤ μ (P.cellOf T) +
          (ENNReal.ofReal (2 / b) *
              (∑' Q : d1bentry_badBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1)) +
            (ENNReal.ofReal (2 / b) *
                (∑' Q : d1bentry_badBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1)) +
              ENNReal.ofReal (2 / b) *
                ∑' Q : d1bentry_goodBelow F T, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1))) :=
        add_le_add (d1bentry_firstEntrances_mass hP F T)
          (add_le_add (d1bentry_badBelow_mass hb F T)
            (add_le_add (d1bentry_badParent_mass hP hb F T) (d1bentry_exits_mass hP hb F hexit T)))
    _ ≤ μ (P.cellOf T) + ENNReal.ofReal (4 / b) * P.descendantEnergy μ k Λ T :=
        add_le_add le_rfl (d1bentry_charge_combine hb F T)

end FirstEntrance

/-- **The first-entrance inequality** at every cell, including the bad-parent term, from the
tree facts and the exit mass. -/
theorem d1b_firstEntrance_proof :
    PartitionTreeStatement → ExitMassStatement → FirstEntranceStatement := by
  intro hTree hExit n E ℓ₀ P μ k Λ b a R hb F T hT
  exact d1bentry_firstEntrance_cell (hTree n E ℓ₀ P) hb F
    (fun S' hS' => hExit n E ℓ₀ P μ k Λ b a R hb F S' hS') hT

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
