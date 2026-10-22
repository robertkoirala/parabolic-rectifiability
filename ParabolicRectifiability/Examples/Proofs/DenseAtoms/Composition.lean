import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Components

/-! # Conditional composition for the dense-atoms example

The implication-form proof assembles the dense-atoms statement from its component statements.
The ambient-nullity and atom-density statements remain explicit hypotheses.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

theorem e2_dense_atoms_of (hAN : E2AmbientNullStatement) (hAD : E2AtomDensityStatement) :
    DenseAtomsStatement := by
  intro n hn k hk hk2 z _ hzD hD
  obtain ⟨hfin, hreg, hne, hsum, hpair⟩ := e2_dense_measure e2_dense_weights n k z
  obtain ⟨hdens, hae⟩ := e2_dense_density hAD e2_dense_weights n k hk z
  refine ⟨hfin, hreg, hne, hsum, hpair,
    e2_dense_energy e2_atomic_squareBound e2_dense_weights n hn k hk hk2 z, hdens, hae,
    e2_dense_support e2_dense_weights n k z hzD hD, ?_,
    e2_dense_notRectifiable hAN e2_dense_volume n hn k hk hk2⟩
  by_contra hH
  exact (e2_dense_volume n).ne' ((hAN n k hk2).1 _ (lt_top_iff_ne_top.2 hH))

end ParabolicRectifiability.Examples
