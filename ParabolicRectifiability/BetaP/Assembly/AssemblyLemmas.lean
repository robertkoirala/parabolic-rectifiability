import ParabolicRectifiability.BetaP.Assembly.AssemblyStatements
import ParabolicRectifiability.BetaP.Assembly.Approximation
import ParabolicRectifiability.BetaP.Assembly.Remainder
import ParabolicRectifiability.BetaP.Assembly.SupportBounds

/-! # Finite assembly of a beta-`p` decomposition: the three steps

The three intermediate results used by `casm_exists_assembled_p_decomposition`:
`casm_compactApproximation`, `casm_remainder` and `casm_supportBounds`, each a restatement of the
corresponding `…_proof` theorem. The localization, the carriers and the typings are hypotheses of
`exists_assembled_p_decomposition` itself, and no law of the beta-`p` coefficients is used. The
measure identity, the carried and unavailable/disallowed clauses and the constant
`C = N C_c + 1` are handled in `casm_exists_assembled_p_decomposition`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- **Compact inner approximation** (`CasmCompactApproximationStatement`).

Proof: `D.horizontal`, `D.vertical` are Borel (`measurable_horizontal`,
`measurable_vertical`); `exists_isCompact_subset_measure_sdiff_le`
(with `[IsFiniteMeasure ν] [ν.InnerRegular]`, loss `ε/2` each) gives compact
`A_H ⊆ D.horizontal`, `A_V ⊆ D.vertical`; since `K = D.horizontal ∪ D.vertical` (`union_eq`),
`K \ (A_H ∪ A_V) ⊆ (D.horizontal \ A_H) ∪ (D.vertical \ A_V)`; finish with
`measure_union_le` and `ENNReal.ofReal_add` (as in `compactTypedPieces_exists`). -/
theorem casm_compactApproximation : CasmCompactApproximationStatement := casm_compactApproximation_proof

/-- **Remainder bookkeeping** (`CasmRemainderStatement`).

Proof: as in `GoodSourceLocalization.remainder_le`, with `pGoodSet`/`energyS … p 2` in place of
`thresholdGoodSet`/`squareEnergy`: a point of `P(0,1)` outside `E_H ∪ E_V` is either in the bad
set `{S_{p,μ}^2 > M}` or, being good, in some `region_i` (`S.cover`) but outside
`A_H i ∪ A_V i`; then `measure_union_le`, `measure_iUnion_fintype_le`, and
`Measure.restrict_apply' (S.measurable i)` to read the per-piece loss. -/
theorem casm_remainder : CasmRemainderStatement := casm_remainder_proof

/-- **Support bundle by finite summation** (`CasmSupportBoundsStatement`).

Proof (as in `familyDecomposition_of_compactSources`, with the bundle `HasRegularSupportBounds`
as target, as in `rectifiableReifenbergDecomposition_of_rectifiabilityDecomposition`):
* compactness: `K_T` is closed in the compact `(⋃ A_T i) ∩ P̄(0,1)` (`isCompact_iUnion`,
  `IsCompact.inter_right`, `IsCompact.of_isClosed_subset`); `K_T ⊆ P̄(0,1)`;
* unavailable types: `A_T i ⊆ (D i).<type> = ∅` (`horizontal_unavailable`,
  `vertical_unavailable` of `TypedSplit`), so `K_T = ∅`;
* covers: `K_H ⊆ ⋃ (D i).horizontal`, each with covers at every `ε` (`(D i).horizontal_graphs`):
  `HasHorizontalGraphCover.of_subset_iUnion`; vertical: the same argument
  (`exists_setNat_null_cover` with `GeneralRegularVerticalGraph.image`) for
  `HasGeneralRegularVerticalGraphCover`;
* `K_H ∪ K_V ⊆ ⋃ (K i).set` (`A_T i ⊆ (D i).<type> ⊆ (K i).set` by `(D i).union_eq`);
* local Hausdorff, separated sets, tube, finite and countable packing:
  `HasRectifiabilityContentBounds.of_metric_packing` applied to
  `HasMetricContentBounds.of_subset_iUnion` and `HasFiniteBallPacking.of_subset_iUnion` with
  `c ≤ c` and `(c : ℝ) * C_c ≤ C` from `(K i).content`, `(K i).packing`; the tube bound carries
  the factor `1 ^ k` (`one_pow`, `mul_one`);
* `H_P^k(K) ≤ C`: `(K i).set ⊆ supp (ν i) ⊆ P̄(center i, 1/64) ⊆ P(center i, 1)`, so
  `(K i).content.hausdorff (center i) 1` bounds `H_P^k((K i).set) ≤ C_c` (as
  `PCarrier.hausdorff_lt_top`); sum over `i`
  (`measure_iUnion_fintype_le`, `sum_fin_ofReal_le`). -/
theorem casm_supportBounds : CasmSupportBoundsStatement := casm_supportBounds_proof

end ParabolicRectifiability.BetaP
