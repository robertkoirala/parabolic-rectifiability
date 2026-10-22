import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.LastWitness
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # The ancestor-chain charging lemma

Proof of `d1d_charging_proof : Terminal.AncestorStatement → ChargingStatement`; the
member-ancestor statement is a hypothesis.

Route: put `d = O.1 - root.1` and choose, for every `t`, a member `A_t` at absolute
level `root.1 + min t d` whose cell contains the cell of `O` (`AncestorStatement`, second
clause). The comparison index `j + 1` (`j < J`, so `j + 1 - 11 ≤ d`) is charged to
`A_{j+1-11}`; the indices `j ≤ 10` all charge `A_0`, every later index a different `A_t`, so
`∑_{j<J} a_{A_{j+1-11}} ≤ 11 ∑_{t≤d} a_{A_t}` (`d1dcharge_shift_sum_le`). The `A_t`, `t ≤ d`, are
distinct addresses (their levels differ, whatever their cell sets) and each is a member above `O`,
so the chain sum is at most `O`'s budget (`d1dcharge_chain_sum_le_budget`, reindexing into the
budget's subtype and `ENNReal.sum_le_tsum`). The base `incidentWitness_sum_le` is not used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Witness

/-- **The shifted charging count.** If `J ≤ d + 11`, then
`∑_{j<J} f (j + 1 - 11) ≤ 11 ∑_{t≤d} f t`: the indices `j ≤ 10` all read `f 0`, and the indices
`j = 11 + x` read the distinct values `f (x + 1)`, `x + 1 ≤ d`. -/
theorem d1dcharge_shift_sum_le (f : ℕ → ℝ≥0∞) (J d : ℕ) (hJ : J ≤ d + 11) :
    ∑ j ∈ Finset.range J, f (j + 1 - 11) ≤ 11 * ∑ t ∈ Finset.range (d + 1), f t := by
  have hle : ∀ t, t ≤ d → f t ≤ ∑ t ∈ Finset.range (d + 1), f t := fun t ht =>
    Finset.single_le_sum_of_canonicallyOrdered (f := f) (Finset.mem_range.2 (by omega))
  rcases le_or_gt J 11 with h | h
  · calc ∑ j ∈ Finset.range J, f (j + 1 - 11)
          ≤ ∑ _j ∈ Finset.range J, ∑ t ∈ Finset.range (d + 1), f t :=
            Finset.sum_le_sum fun j hj => hle _ (by have := Finset.mem_range.1 hj; omega)
      _ = (J : ℝ≥0∞) * ∑ t ∈ Finset.range (d + 1), f t := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 11 * ∑ t ∈ Finset.range (d + 1), f t := by
            gcongr
            exact_mod_cast h
  · obtain ⟨m, rfl⟩ : ∃ m, J = 11 + m := ⟨J - 11, by omega⟩
    have h1c : ∀ j ∈ Finset.range 11, f (j + 1 - 11) = f 0 := fun j hj => by
      have := Finset.mem_range.1 hj
      congr 1
      omega
    have h1 : ∑ j ∈ Finset.range 11, f (j + 1 - 11) = 11 * f 0 := by
      rw [Finset.sum_congr rfl h1c]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]
    have h2 : ∑ x ∈ Finset.range m, f (11 + x + 1 - 11) = ∑ x ∈ Finset.range m, f (x + 1) :=
      Finset.sum_congr rfl fun x _ => by
        congr 1
        omega
    have h3 : ∑ x ∈ Finset.range m, f (x + 1) + f 0 ≤ ∑ t ∈ Finset.range (d + 1), f t := by
      rw [← Finset.sum_range_succ']
      exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
    have hf0 := hle 0 (Nat.zero_le d)
    have hsplit : ∑ j ∈ Finset.range (11 + m), f (j + 1 - 11)
        = ∑ j ∈ Finset.range 11, f (j + 1 - 11) + ∑ x ∈ Finset.range m, f (11 + x + 1 - 11) :=
      Finset.sum_range_add (fun j => f (j + 1 - 11)) 11 m
    rw [hsplit, h1, h2]
    calc 11 * f 0 + ∑ x ∈ Finset.range m, f (x + 1)
        = 10 * f 0 + (∑ x ∈ Finset.range m, f (x + 1) + f 0) := by ring
      _ ≤ 10 * ∑ t ∈ Finset.range (d + 1), f t + ∑ t ∈ Finset.range (d + 1), f t :=
          add_le_add (by gcongr) h3
      _ = 11 * ∑ t ∈ Finset.range (d + 1), f t := by ring

section Chain

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- **The member ancestor chain of `O`** (`AncestorStatement`, second clause): for every `t` a
member `A t` at absolute level `root.1 + min t (O.1 - root.1)` whose cell contains the cell of
`O`. -/
theorem d1dcharge_ancestor_chain (hanc : Terminal.AncestorStatement)
    (𝒢 : GoodRegion P μ k Λ b) {O : ℕ × Space n} (hO : O ∈ 𝒢.members) :
    ∃ A : ℕ → ℕ × Space n, ∀ t : ℕ, A t ∈ 𝒢.members ∧
      (A t).1 = 𝒢.root.1 + min t (O.1 - 𝒢.root.1) ∧ P.cellOf O ⊆ P.cellOf (A t) := by
  have hOb : P.IsCell O ∧ 𝒢.root.1 ≤ O.1 ∧ P.cellOf O ⊆ P.cellOf 𝒢.root := 𝒢.below_root O hO
  have hle := hOb.2.1
  have key : ∀ t : ℕ, ∃ Q' ∈ 𝒢.members, Q'.1 = 𝒢.root.1 + min t (O.1 - 𝒢.root.1) ∧
      P.cellOf O ⊆ P.cellOf Q' :=
    fun t => (hanc n E ℓ₀ P μ k Λ b 𝒢).2 O hO _ (by omega) (by omega)
  choose A hA using key
  exact ⟨A, hA⟩

/-- **The chain budget pays a finite chain of distinct ancestors.** If `A t`, `t ≤ d`, are members
above `O`, pairwise distinct, then `∑_{t≤d} a_{A t} ≤ ofReal b` (the budget of `O`), by
reindexing into the budget's subtype. -/
theorem d1dcharge_chain_sum_le_budget (𝒢 : GoodRegion P μ k Λ b) {O : ℕ × Space n}
    (hO : O ∈ 𝒢.members) (d : ℕ) (A : ℕ → ℕ × Space n)
    (hA : ∀ t : ℕ, A t ∈ 𝒢.members ∧ P.IsBelow O (A t))
    (hinj : ∀ s t : ℕ, s ≤ d → t ≤ d → A s = A t → s = t) :
    ∑ t ∈ Finset.range (d + 1), P.modelCoeff μ Λ (𝒢.model (A t)) (A t) ≤ ENNReal.ofReal b := by
  classical
  let g : ℕ → {Q' : ℕ × Space n // Q' ∈ 𝒢.members ∧ P.IsBelow O Q'} := fun t => ⟨A t, hA t⟩
  let F : {Q' : ℕ × Space n // Q' ∈ 𝒢.members ∧ P.IsBelow O Q'} → ℝ≥0∞ :=
    fun Q => P.modelCoeff μ Λ (𝒢.model Q.1) Q.1
  have hginj : Set.InjOn g ↑(Finset.range (d + 1)) := by
    intro s hs t ht hst
    have hs' := Finset.mem_range.1 (Finset.mem_coe.1 hs)
    have ht' := Finset.mem_range.1 (Finset.mem_coe.1 ht)
    exact hinj s t (by omega) (by omega) (congrArg Subtype.val hst)
  calc ∑ t ∈ Finset.range (d + 1), P.modelCoeff μ Λ (𝒢.model (A t)) (A t)
      = ∑ t ∈ Finset.range (d + 1), F (g t) := rfl
    _ = ∑ Q ∈ (Finset.range (d + 1)).image g, F Q := (Finset.sum_image hginj).symm
    _ ≤ ∑' Q, F Q := ENNReal.sum_le_tsum _
    _ ≤ ENNReal.ofReal b := 𝒢.budget O hO

end Chain

/-- **The ancestor-chain charging lemma** (`ChargingStatement`):
the member ancestors give `∑_{j ≤ J} e_j ≤ 11 c b`. -/
theorem d1d_charging_proof : Terminal.AncestorStatement → ChargingStatement := by
  intro hanc n E ℓ₀ P μ k Λ b 𝒢 O J e c hO hJ he0 hbound
  have hOb : P.IsCell O ∧ 𝒢.root.1 ≤ O.1 ∧ P.cellOf O ⊆ P.cellOf 𝒢.root := 𝒢.below_root O hO
  have hle := hOb.2.1
  obtain ⟨A, hA⟩ := d1dcharge_ancestor_chain hanc 𝒢 hO
  have hbel : ∀ t : ℕ, A t ∈ 𝒢.members ∧ P.IsBelow O (A t) := fun t => by
    refine ⟨(hA t).1, ?_⟩
    show P.IsCell O ∧ (A t).1 ≤ O.1 ∧ P.cellOf O ⊆ P.cellOf (A t)
    refine ⟨hOb.1, ?_, (hA t).2.2⟩
    rw [(hA t).2.1]
    omega
  have hinj : ∀ s t : ℕ, s ≤ O.1 - 𝒢.root.1 → t ≤ O.1 - 𝒢.root.1 → A s = A t → s = t := by
    intro s t hs ht hst
    have hlev := congrArg Prod.fst hst
    rw [(hA s).2.1, (hA t).2.1] at hlev
    omega
  have hchain := d1dcharge_chain_sum_le_budget 𝒢 hO (O.1 - 𝒢.root.1) A hbel hinj
  have hterm : ∀ j ∈ Finset.range J,
      e (j + 1) ≤ c * P.modelCoeff μ Λ (𝒢.model (A (j + 1 - 11))) (A (j + 1 - 11)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    refine hbound j (by omega) (A (j + 1 - 11)) (hA _).1 ?_ (hA _).2.2
    rw [(hA _).2.1]
    omega
  have hshift := d1dcharge_shift_sum_le
    (fun t => P.modelCoeff μ Λ (𝒢.model (A t)) (A t)) J (O.1 - 𝒢.root.1) (by omega)
  calc ∑ j ∈ Finset.range (J + 1), e j = ∑ j ∈ Finset.range J, e (j + 1) := by
        rw [Finset.sum_range_succ', he0, add_zero]
    _ ≤ ∑ j ∈ Finset.range J,
          c * P.modelCoeff μ Λ (𝒢.model (A (j + 1 - 11))) (A (j + 1 - 11)) :=
        Finset.sum_le_sum hterm
    _ = c * ∑ j ∈ Finset.range J,
          P.modelCoeff μ Λ (𝒢.model (A (j + 1 - 11))) (A (j + 1 - 11)) := by
        rw [Finset.mul_sum]
    _ ≤ c * (11 * ∑ t ∈ Finset.range (O.1 - 𝒢.root.1 + 1),
          P.modelCoeff μ Λ (𝒢.model (A t)) (A t)) := by
        gcongr
    _ ≤ c * (11 * ENNReal.ofReal b) := by
        gcongr
    _ = 11 * c * ENNReal.ofReal b := by ring

end Witness

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
