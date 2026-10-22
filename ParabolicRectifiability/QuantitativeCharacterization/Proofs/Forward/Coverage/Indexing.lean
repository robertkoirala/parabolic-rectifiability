import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Coverage

/-! # Indexing of the good roots in `ℕ`

Proves `SlabBasicsStatement → IndexingStatement`, with `SlabBasicsStatement` as an implication
hypothesis. The roots are cells (`roots_forest`), hence countable; an injection `e : roots → ℕ`
gives `(Equiv.ofInjective e he).symm : range e ≃ roots`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Coverage

open ParabolicRectifiability.Foundations

/-- The roots of a stopping decomposition are cells, hence countable. -/
theorem d1findex_roots_countable (hB : SlabBasicsStatement) {n : ℕ}
    (μ : MeasureTheory.Measure (Space n)) (a : Space n) (R : ℝ) (P : DirectPartition μ.support R)
    {k : ℕ} {Λ b K : ℝ} (SD : StoppingDecomposition P μ k Λ b a R K) :
    SD.roots.Countable := by
  refine (hB n μ a R P).1.mono ?_
  intro S hS
  obtain ⟨z₀, _, _, hb⟩ := SD.roots_forest S hS
  exact hb.1

/-- **Indexing**: the good roots are in bijection with a subset of `ℕ` (implication form over
`SlabBasicsStatement`). -/
theorem d1f_indexing_proof : SlabBasicsStatement → IndexingStatement := by
  intro hB n μ a R P k Λ b K SD
  obtain ⟨e, he⟩ := Set.countable_iff_exists_injective.mp (d1findex_roots_countable hB μ a R P SD)
  exact ⟨Set.range e, ⟨(Equiv.ofInjective e he).symm⟩⟩

end Coverage

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
