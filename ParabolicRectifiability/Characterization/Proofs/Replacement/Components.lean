import ParabolicRectifiability.Characterization.Proofs.Replacement.Statements
import ParabolicRectifiability.Characterization.Proofs.Replacement.GoodSet
import ParabolicRectifiability.Characterization.Proofs.Replacement.WhitneySelection
import ParabolicRectifiability.Characterization.Proofs.Replacement.Allocation
import ParabolicRectifiability.Characterization.Proofs.Replacement.Assembly
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.GoodDomination
import ParabolicRectifiability.Characterization.Proofs.Fivefold

/-! # Component estimates for the replacement of the bad region

The declarations below are the component estimates of `bad_region_replacement :
ReplacementStatement`; they delegate to the corresponding proof modules. They are assembled in
`bad_region_replacement_of_leaves`.

* Component estimates (each is a named statement `Rp…Statement`):
  `b3_rp_goodSet` (i), `b3_rp_whitneySelection` (ii.a), `b3_rp_allocation` (ii.b),
  `b3_rp_assembly` (iii).
* Input estimates: `b3_rp_input_fivefold` (`fivefold_ball_selection`) and
  `b3_rp_input_goodDomination` (`good_set_domination`).

The statements (i) and (ii.a) take fivefold selection as an explicit hypothesis (implication
form); the assembly applies them to the input estimate.
-/

noncomputable section

namespace ParabolicRectifiability.Characterization.ReplacementTree

/-! ## Input estimates -/

/-- Fivefold ball selection, `fivefold_ball_selection : FivefoldSelectionStatement`. -/
theorem b3_rp_input_fivefold : FivefoldSelectionStatement := by
  exact ParabolicRectifiability.Characterization.fivefold_ball_selection_proof

/-- Domination of the good part of the source, `good_set_domination : GoodDominationStatement`. -/
theorem b3_rp_input_goodDomination : GoodDominationStatement := by
  exact ParabolicRectifiability.Characterization.good_set_domination_proof

/-! ## Component estimates -/

/-- `RpGoodSetStatement`: closedness and
nonemptiness of `G_A` and the bad-mass bound with `C₀ = max (C 5^k) 1` (route in its
docstring).

Fivefold selection enters through the statement's own first hypothesis. Mathlib ingredients:
`isClosed_iff_clusterPt` or `closure_subset_iff`/`Metric.mem_closure_iff`,
`tendsto_measure_iUnion_atTop` (`Metric.ball z r = ⋃_m ball z (r - r/(m+2))`),
`Classical.choose` for the witnessing radii, `measure_iUnion_le`, `measure_biUnion`
(disjoint balls, countable `J`), `ENNReal.tsum_mul_left`, `IsADRCarrier.upper`/`.lower`,
`Measure.measure_compl_support`, `pow_le_pow_left`, `ENNReal.ofReal_le_ofReal`. -/
theorem b3_rp_goodSet : RpGoodSetStatement := by
  exact ParabolicRectifiability.Characterization.ReplacementTree.b3_rp_goodSet_proof

/-- `RpWhitneySelectionStatement`: Whitney
selection of disjoint relative balls with fivefold covering and proximity `200 r_i` (route
in its docstring).

Fivefold selection enters through the statement's own first hypothesis. Mathlib ingredients:
`Metric.infDist`, `IsClosed.notMem_iff_infDist_pos` (with `G` nonempty),
`Metric.exists_dist_lt_of_infDist_lt`, `Metric.infDist_le_dist_of_mem` (for
`Γ ∩ P(z, s(z)) ∩ G = ∅`), `Set.Countable.toEncodable`, `Encodable.encode_injective`,
`Set.InjOn`/`Equiv.ofInjective` for the reindexing into `I ⊆ ℕ`, `IsADRCarrier.lower`,
`Measure.measure_compl_support`. -/
theorem b3_rp_whitneySelection : RpWhitneySelectionStatement := by
  exact ParabolicRectifiability.Characterization.b3_rp_whitneySelection_proof

/-- `RpAllocationStatement`: exact Borel allocation
by `disjointed` and the piece bound `ν(E_i) ≤ 205^k A r_i^k` (route in its docstring).

Mathlib ingredients: `disjointed`, `MeasurableSet.disjointed`,
`disjoint_disjointed`, `iUnion_disjointed`, `disjointed_subset`, `dist_triangle`,
`measure_mono`, `mul_pow`. -/
theorem b3_rp_allocation : RpAllocationStatement := by
  exact ParabolicRectifiability.Characterization.b3_rp_allocation_proof

/-- `RpAssemblyStatement`: domination
`ν_A ≤ max ((5^k + 205^k)/c) 1 · A · σ` and mass preservation `ν_A(Γ) = ν(Γ)` (route in its
docstring).

The per-instance domination of the good part enters through the statement's own hypothesis.
Mathlib ingredients: `Measure.le_iff`, `Measure.add_apply`,
`Measure.sum_apply`, `Measure.smul_apply`, `Measure.restrict_apply`, `measure_iUnion`
(disjoint `B_i` and `E_i`), `ENNReal.tsum_le_tsum`, `ENNReal.div_le_iff`,
`ENNReal.div_mul_cancel`, `IsADRCarrier.lower`/`.upper`, `Measure.measure_compl_support`.
-/
theorem b3_rp_assembly : RpAssemblyStatement := by
  exact ParabolicRectifiability.Characterization.ReplacementTree.b3_rp_assembly_proof

end ParabolicRectifiability.Characterization.ReplacementTree
