import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Stopping

/-! # The exit mass

Proof of `d1b_exitMass_proof`, in implication form `PartitionTreeStatement → ExitMassStatement`.

Route. Fix a root `S'`. For an exit `S` of `S'` with parent `Q ∈ members S'`, the entry
`root_entry S` must be its third case with the region `S'`: the first case (`S.1 = 0`) is excluded
by `S.1 = Q.1 + 1`; in the second the bad block is an ancestor of `S` at the level of `Q`, hence
equals `Q` (`eq_of_isBelow`, `isBelow_of_common`), but `Q` is a nonbad member (`classify`); in the
third the parent is again `Q`, and its region is `S'` by uniqueness in `classify`. So
`b/2 < chainSum (members S') Q` (the recorded charge: not the stronger
maximal-stopping inequality). The chain sum above `Q` is at most the sum of `a_{Q'}` over the
members `Q'` above `S`. Two distinct exits are never nested (a nested pair would put the upper
exit into `members S'` by `hereditary`, and then its own region would be `S'` by `classify`,
against its level), so their cells are disjoint. Swapping the double sum, the exits below a
member `Q'` have total mass at most `μ(Q')`. Helpers carry the prefix `d1bexit_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal Classical

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

section ExitMass

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
  {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} {a : Space n} {R : ℝ}

/-- Two ancestor cells of one cell at the same level coincide. -/
theorem d1bexit_ancestor_unique (hT : PartitionTree P) {S Q Q₀ : ℕ × Space n}
    (hQ : P.IsCell Q) (hQ₀ : P.IsCell Q₀) (hSQ : P.IsBelow S Q) (hSQ₀ : P.IsBelow S Q₀)
    (hlev : Q.1 = Q₀.1) : Q₀ = Q :=
  hT.eq_of_isBelow Q₀ Q hQ (hT.isBelow_of_common S Q Q₀ hQ hQ₀ hSQ hSQ₀ hlev.le) hlev.symm

/-- A member of a region is a forest cell. -/
theorem d1bexit_member_forest (hT : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {S' Q : ℕ × Space n} (hS' : S' ∈ F.roots) (hQ : Q ∈ F.members S') : P.InForest a R Q :=
  hT.inForest_of_isBelow a R Q S' (F.roots_forest S' hS') (F.below_root S' hS' Q hQ)

/-- A member of a region is not a bad block. -/
theorem d1bexit_member_not_bad (hT : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {S' Q : ℕ × Space n} (hS' : S' ∈ F.roots) (hQ : Q ∈ F.members S') : Q ∉ F.bad := by
  rcases F.classify Q (d1bexit_member_forest hT F hS' hQ) with ⟨_, h⟩ | ⟨h, _⟩
  · exact absurd hQ (h ⟨S', hS'⟩)
  · exact h

/-- A cell lies in the region of at most one root. -/
theorem d1bexit_member_unique (hT : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {S₁ S₂ Q : ℕ × Space n} (h₁ : S₁ ∈ F.roots) (h₂ : S₂ ∈ F.roots)
    (hQ₁ : Q ∈ F.members S₁) (hQ₂ : Q ∈ F.members S₂) : S₁ = S₂ := by
  rcases F.classify Q (d1bexit_member_forest hT F h₁ hQ₁) with ⟨_, h⟩ | ⟨_, h⟩
  · exact absurd hQ₁ (h ⟨S₁, h₁⟩)
  · exact congrArg Subtype.val
      (h.unique (y₁ := (⟨S₁, h₁⟩ : F.roots)) (y₂ := (⟨S₂, h₂⟩ : F.roots)) hQ₁ hQ₂)

/-- **The recorded charge (4.1)**: an exit `S` of the region of `S'` with parent `Q` in that
region has `b/2 < chainSum (members S') Q`. -/
theorem d1bexit_charge (hT : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {S' S Q : ℕ × Space n} (hS' : S' ∈ F.roots) (hS : S ∈ F.roots) (hQ : Q ∈ F.members S')
    (hlev : Q.1 + 1 = S.1) (hSQ : P.IsBelow S Q) :
    ENNReal.ofReal (b / 2) < chainSum P μ k Λ (F.members S') Q := by
  have hQc : P.IsCell Q := (F.below_root S' hS' Q hQ).1
  rcases F.root_entry S hS with h0 | ⟨Q₀, hQ₀, hlev₀, hSQ₀⟩ |
      ⟨S'', hS'', Q'', hQ'', hlev'', hSQ'', hch⟩
  · exfalso
    omega
  · exfalso
    obtain ⟨z₀, -, -, hQ₀b⟩ := F.bad_forest Q₀ hQ₀
    have heq : Q₀ = Q := d1bexit_ancestor_unique hT hQc hQ₀b.1 hSQ hSQ₀ (by omega)
    rw [heq] at hQ₀
    exact d1bexit_member_not_bad hT F hS' hQ hQ₀
  · have hQ''c : P.IsCell Q'' := (F.below_root S'' hS'' Q'' hQ'').1
    have heq : Q'' = Q := d1bexit_ancestor_unique hT hQc hQ''c hSQ hSQ'' (by omega)
    rw [heq] at hQ'' hch
    have hS''eq : S'' = S' := d1bexit_member_unique hT F hS'' hS' hQ'' hQ
    rw [hS''eq] at hch
    exact hch

/-- Two distinct exits of one region, the second at a level not below the first, have disjoint
cells (exits are never nested). -/
theorem d1bexit_disjoint_of_le (hT : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {S' S₁ S₂ : ℕ × Space n} (hS' : S' ∈ F.roots) (h₁ : S₁ ∈ F.exits S')
    (h₂ : S₂ ∈ F.exits S') (hne : S₁ ≠ S₂) (hle : S₂.1 ≤ S₁.1) :
    Disjoint (P.cellOf S₁) (P.cellOf S₂) := by
  obtain ⟨-, Q₁, hQ₁, hl₁, hS₁Q₁⟩ := h₁
  obtain ⟨hS₂r, Q₂, hQ₂, hl₂, hS₂Q₂⟩ := h₂
  have c₁ : P.IsCell S₁ := hS₁Q₁.1
  have c₂ : P.IsCell S₂ := hS₂Q₂.1
  rcases hT.isBelow_or_disjoint S₁ S₂ c₁ c₂ hle with hb | hd
  · exfalso
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact hne (hT.eq_of_isBelow S₁ S₂ c₂ hb heq.symm)
    · have cQ₁ : P.IsCell Q₁ := (F.below_root S' hS' Q₁ hQ₁).1
      have hQ₁S₂ : P.IsBelow Q₁ S₂ :=
        hT.isBelow_of_common S₁ S₂ Q₁ c₂ cQ₁ hb hS₁Q₁ (by omega)
      have hQ₂S' : P.IsBelow Q₂ S' := F.below_root S' hS' Q₂ hQ₂
      have hS₂S' : P.IsBelow S₂ S' := hT.isBelow_trans S₂ Q₂ S' hS₂Q₂ hQ₂S'
      have hmem : S₂ ∈ F.members S' := F.hereditary S' hS' Q₁ hQ₁ S₂ hQ₁S₂ hS₂S'
      have heq : S₂ = S' :=
        d1bexit_member_unique hT F hS₂r hS' (F.root_mem S₂ hS₂r) hmem
      have hlvl : S'.1 ≤ Q₂.1 := hQ₂S'.2.1
      rw [heq] at hl₂
      omega
  · exact hd

/-- The exits of one region have pairwise disjoint cells. -/
theorem d1bexit_pairwise_disjoint (hT : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {S' : ℕ × Space n} (hS' : S' ∈ F.roots) :
    Pairwise (Function.onFun Disjoint fun S : F.exits S' => P.cellOf S.1) := by
  intro S₁ S₂ hne
  have hne' : S₁.1 ≠ S₂.1 := fun h => hne (Subtype.ext h)
  rcases le_total S₂.1.1 S₁.1.1 with h | h
  · exact d1bexit_disjoint_of_le hT F hS' S₁.2 S₂.2 hne' h
  · exact (d1bexit_disjoint_of_le hT F hS' S₂.2 S₁.2 hne'.symm h).symm

/-- One exit pays `b/2` times its mass from the members above it. -/
theorem d1bexit_one (hT : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {S' : ℕ × Space n} (hS' : S' ∈ F.roots) (S : F.exits S') :
    ENNReal.ofReal (b / 2) * μ (P.cellOf S.1) ≤
      ∑' Q' : F.members S', P.coeff μ k Λ Q'.1 *
        (if P.IsBelow S.1 Q'.1 then μ (P.cellOf S.1) else 0) := by
  obtain ⟨hSr, Q, hQ, hlev, hSQ⟩ := S.2
  have hch : ENNReal.ofReal (b / 2) <
      ∑' Q' : {Q' : ℕ × Space n // Q' ∈ F.members S' ∧ P.IsBelow Q Q'}, P.coeff μ k Λ Q'.1 :=
    d1bexit_charge hT F hS' hSr hQ hlev hSQ
  let f : {Q' : ℕ × Space n // Q' ∈ F.members S' ∧ P.IsBelow Q Q'} → F.members S' :=
    fun Q' => ⟨Q'.1, Q'.2.1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext h
  let g : F.members S' → ℝ≥0∞ := fun Q' =>
    P.coeff μ k Λ Q'.1 * (if P.IsBelow S.1 Q'.1 then μ (P.cellOf S.1) else 0)
  calc ENNReal.ofReal (b / 2) * μ (P.cellOf S.1)
      ≤ (∑' Q' : {Q' : ℕ × Space n // Q' ∈ F.members S' ∧ P.IsBelow Q Q'},
          P.coeff μ k Λ Q'.1) * μ (P.cellOf S.1) := by
          have hle := hch.le
          gcongr
    _ = ∑' Q' : {Q' : ℕ × Space n // Q' ∈ F.members S' ∧ P.IsBelow Q Q'},
          P.coeff μ k Λ Q'.1 * μ (P.cellOf S.1) := ENNReal.tsum_mul_right.symm
    _ = ∑' Q', g (f Q') := by
        refine tsum_congr fun Q' => ?_
        have hb : P.IsBelow S.1 Q'.1 := hT.isBelow_trans S.1 Q Q'.1 hSQ Q'.2.2
        show _ = P.coeff μ k Λ Q'.1 * (if P.IsBelow S.1 Q'.1 then μ (P.cellOf S.1) else 0)
        rw [ite_eq_left hb]
    _ ≤ ∑' Q', g Q' := ENNReal.tsum_comp_le_tsum_of_injective hf g

/-- The exits below one member `Q'` have total mass at most `μ(Q')`. -/
theorem d1bexit_below_member (hT : PartitionTree P) (F : StoppingForest P μ k Λ b a R)
    {S' : ℕ × Space n} (hS' : S' ∈ F.roots) (Q' : ℕ × Space n) :
    (∑' S : F.exits S', (if P.IsBelow S.1 Q' then μ (P.cellOf S.1) else 0)) ≤
      μ (P.cellOf Q') := by
  calc (∑' S : F.exits S', (if P.IsBelow S.1 Q' then μ (P.cellOf S.1) else 0))
      ≤ ∑' S : F.exits S', μ (P.cellOf S.1 ∩ P.cellOf Q') := by
        refine ENNReal.tsum_le_tsum fun S => ?_
        split_ifs with h
        · rw [Set.inter_eq_left.mpr h.2.2]
        · exact zero_le
    _ ≤ μ (⋃ S : F.exits S', P.cellOf S.1 ∩ P.cellOf Q') := by
        refine tsum_meas_le_meas_iUnion_of_disjoint μ
          (fun S => (P.measurable_cell _ _).inter (P.measurable_cell _ _)) ?_
        intro S₁ S₂ hne
        exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left
          (d1bexit_pairwise_disjoint hT F hS' hne)
    _ ≤ μ (P.cellOf Q') := measure_mono (Set.iUnion_subset fun _ => Set.inter_subset_right)

/-- **Exit mass** (`ExitMassStatement`, in implication form). -/
theorem d1b_exitMass_proof : PartitionTreeStatement → ExitMassStatement := by
  intro hTree n E ℓ₀ P μ k Λ b a R _hb F S' hS'
  have hT := hTree n E ℓ₀ P
  calc ENNReal.ofReal (b / 2) * (∑' S : F.exits S', μ (P.cellOf S.1))
      = ∑' S : F.exits S', ENNReal.ofReal (b / 2) * μ (P.cellOf S.1) :=
        ENNReal.tsum_mul_left.symm
    _ ≤ ∑' S : F.exits S', ∑' Q' : F.members S', P.coeff μ k Λ Q'.1 *
          (if P.IsBelow S.1 Q'.1 then μ (P.cellOf S.1) else 0) :=
        ENNReal.tsum_le_tsum fun S => d1bexit_one hT F hS' S
    _ = ∑' Q' : F.members S', ∑' S : F.exits S', P.coeff μ k Λ Q'.1 *
          (if P.IsBelow S.1 Q'.1 then μ (P.cellOf S.1) else 0) := ENNReal.tsum_comm
    _ = ∑' Q' : F.members S', P.coeff μ k Λ Q'.1 *
          ∑' S : F.exits S', (if P.IsBelow S.1 Q'.1 then μ (P.cellOf S.1) else 0) :=
        tsum_congr fun _ => ENNReal.tsum_mul_left
    _ ≤ ∑' Q' : F.members S', P.coeff μ k Λ Q'.1 * μ (P.cellOf Q'.1) :=
        ENNReal.tsum_le_tsum fun Q' => by
          gcongr
          exact d1bexit_below_member hT F hS' Q'.1

end ExitMass

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
