import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Coverage

/-! # The slab families partition the tested pairs exactly

Proof of `SlabCoverStatement → SlabDisjointStatement → SlabPartitionStatement`, in implication
form: `SlabCoverStatement` and `SlabDisjointStatement` are hypotheses.

* Members of a region are forest cells: `below_root`, `region_root`, `roots_forest`, and
  transitivity of `IsBelow`.
* A common point of two slabs of cells forces equal addresses (`SlabDisjointStatement`); then
  `SD.classify` excludes a bad member and a member of two distinct regions (`∃!`).
* Cover: `SlabCoverStatement` gives a forest cell, and `SD.classify` sends it to `𝓑` or to a
  region.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Coverage

open ParabolicRectifiability.Foundations

section

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
  {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} {a : Space n} {R K : ℝ}

/-- Every member of the region of a good root is a forest cell. -/
theorem d1fspart_member_inForest (SD : StoppingDecomposition P μ k Λ b a R K) (S : SD.roots)
    {Q : ℕ × Space n} (hQ : Q ∈ (SD.region S).members) : P.InForest a R Q := by
  have hbelow := (SD.region S).below_root Q hQ
  rw [SD.region_root S] at hbelow
  obtain ⟨z₀, hz₀, hmeet, -, -, hsub⟩ := SD.roots_forest S.1 S.2
  obtain ⟨hcell, -, hQsub⟩ := hbelow
  unfold DirectPartition.InForest DirectPartition.IsBelow
  exact ⟨z₀, hz₀, hmeet, hcell, Nat.zero_le _, hQsub.trans hsub⟩

/-- Every forest cell is a cell. -/
theorem d1fspart_inForest_isCell {Q : ℕ × Space n} (hQ : P.InForest a R Q) : P.IsCell Q := by
  obtain ⟨-, -, -, hcell, -, -⟩ := hQ
  exact hcell

/-- Two cells whose slabs share a point have equal addresses. -/
theorem d1fspart_eq_of_mem (hD : SlabDisjointStatement) {Q Q' : ℕ × Space n}
    (hQ : P.IsCell Q) (hQ' : P.IsCell Q') {p : Space n × ℝ} (hp : p ∈ slab P a R Q)
    (hp' : p ∈ slab P a R Q') : Q = Q' := by
  by_contra hne
  exact Set.disjoint_left.1 (hD n E ℓ₀ P a R Q Q' hQ hQ' hne) hp hp'

end

/-- **The slab families partition the tested pairs exactly**: every tested pair lies in exactly
one of the bad family and the region families (implication form). -/
theorem d1f_slabPartition_proof :
    SlabCoverStatement → SlabDisjointStatement → SlabPartitionStatement := by
  intro hC hD n μ a R P k Λ b K SD
  refine ⟨?_, ?_, ?_⟩
  · intro S
    refine Set.disjoint_left.2 ?_
    intro p hp hp'
    unfold badSlabs at hp
    unfold goodSlabs at hp'
    obtain ⟨Q, hQ, hpQ⟩ := Set.mem_iUnion₂.1 hp
    obtain ⟨Q', hQ', hpQ'⟩ := Set.mem_iUnion₂.1 hp'
    have hF := SD.bad_forest Q hQ
    have hF' := d1fspart_member_inForest SD S hQ'
    have heq : Q = Q' := d1fspart_eq_of_mem hD (d1fspart_inForest_isCell hF)
      (d1fspart_inForest_isCell hF') hpQ hpQ'
    subst heq
    rcases SD.classify Q hF with ⟨-, hnot⟩ | ⟨hnb, -⟩
    · exact hnot S hQ'
    · exact hnb hQ
  · intro S S' hSS'
    refine Set.disjoint_left.2 ?_
    intro p hp hp'
    unfold goodSlabs at hp hp'
    obtain ⟨Q, hQ, hpQ⟩ := Set.mem_iUnion₂.1 hp
    obtain ⟨Q', hQ', hpQ'⟩ := Set.mem_iUnion₂.1 hp'
    have hF := d1fspart_member_inForest SD S hQ
    have hF' := d1fspart_member_inForest SD S' hQ'
    have heq : Q = Q' := d1fspart_eq_of_mem hD (d1fspart_inForest_isCell hF)
      (d1fspart_inForest_isCell hF') hpQ hpQ'
    subst heq
    rcases SD.classify Q hF with ⟨-, hnot⟩ | ⟨-, huniq⟩
    · exact hnot S hQ
    · exact hSS' (huniq.unique hQ hQ')
  · intro p hp
    obtain ⟨Q, hF, hpQ⟩ := hC n μ a R P p hp
    rcases SD.classify Q hF with ⟨hbad, -⟩ | ⟨-, S, hS, -⟩
    · exact Or.inl (Set.mem_iUnion₂.2 ⟨Q, hbad, hpQ⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨S, Set.mem_iUnion₂.2 ⟨Q, hS, hpQ⟩⟩)

end Coverage

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
