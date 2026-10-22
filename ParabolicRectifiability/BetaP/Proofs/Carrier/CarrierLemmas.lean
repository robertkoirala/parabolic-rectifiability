import ParabolicRectifiability.BetaP.Proofs.Carrier.CarrierStatements
import ParabolicRectifiability.BetaP.Statements.Laws
import ParabolicRectifiability.Foundations.Statements.Measurability
import ParabolicRectifiability.BetaP.Proofs.Laws.Holder
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.BetaPowTwo
import ParabolicRectifiability.BetaP.Proofs.Carrier.Transfer
import ParabolicRectifiability.BetaP.Proofs.Carrier.CellsPacking
import ParabolicRectifiability.BetaP.Proofs.Carrier.Loss
import ParabolicRectifiability.BetaP.Proofs.Carrier.Separated
import ParabolicRectifiability.BetaP.Proofs.Carrier.VariablePacking
import ParabolicRectifiability.BetaP.Proofs.Carrier.Content
import ParabolicRectifiability.BetaP.Proofs.Carrier.Domination
import ParabolicRectifiability.BetaP.Proofs.Carrier.Energy

/-! # Auxiliary results for the `p`-carrier

This module proves the auxiliary statements `CellsFitTransferStatement`, `CellsPackingStatement`,
…, `CarrierEnergyStatement`, from which `ccar_exists_p_carrier` assembles `exists_p_carrier`.

An auxiliary result that needs another one takes the other's named statement as an explicit
hypothesis (implication form). No result assumes a growth, density, packing or energy bound for
the source `ν` beyond the all-scale bound of `exists_p_carrier`, and none assumes a conclusion
about the carrier.

| Result | Content | Hypotheses |
|---|---|---|
| `ccar_input_holder` | Hölder with the density factor | — |
| `ccar_input_betaPowTwo` | `B_2 = betaSq` | — |
| `ccar_cells_fit_transfer` | fixed-model Jensen transfer | — |
| `ccar_cells_packing` | barycenter cells into truncated packing | fit transfer |
| `ccar_loss` | loss `ν(X ∖ K_a)` | cells packing |
| `ccar_separated` | separated sets in `K_a` | cells packing |
| `ccar_content_of_separated` | content bounds (generic) | — |
| `ccar_variable_packing` | variable-radius packing | cells packing |
| `ccar_betaPow_domination` | domination for `B_p` | — |
| `ccar_energy` | finite energy of the carrier measure | Hölder, `B_2 = betaSq`, domination |

General lemmas used directly: `ae_largeDimension`, `exists_doubling_scale`,
`exists_deficient_radius`, `Vitali.exists_disjoint_subfamily_covering_enlargement` (selection);
`exists_maximal_separated_finset`, `hausdorffP_le_of_nets`,
`parabolicVolume_thickening_le_of_net` (content bounds); `isCompact_densityCarrier`,
`restrict_hausdorffP_densityCarrier_le`, `HasMetricContentBounds.mono`,
`HasFiniteBallPacking.mono` (assembly); `FiniteBarycenterCells` and its containment lemmas
`barycenter_mem_closedBall`, `contributing_cell_subset_ball`, the barycenter integrability and
Jensen API, and `lintegral_comp_two_Ioi_scaleMeasure` (transfer).

No law beyond Hölder and `B_2 = betaSq` is used: in particular neither `BetaPowSmulStatement`
nor `BetaPowMeasurabilityStatement` nor `Characterization.FivefoldSelectionStatement` enters.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP.CarrierTree

open ParabolicRectifiability.Foundations

/-! ## Input statements -/

/-- **Hölder with the density factor**: `BetaPowHolderStatement`, proved by `claws_holder_proof`.
Used by `ccar_energy` in its second part `B_2 ≤ Θ^{1-2/p} B_p^{2/p}` (`2 ≤ p`) for the finite
carrier measure `η = H_P^k⌊K_a`. -/
theorem ccar_input_holder : BetaPowHolderStatement := by
  exact ParabolicRectifiability.BetaP.claws_holder_proof

/-- **`B_2 = betaSq`**: `Foundations.BetaPowTwoStatement`, proved by
`f3_betaPow_two_eq_betaSq_proof`. Used by `ccar_energy` to read the Hölder bound for `B_2` as a
bound for the natural `betaSq` of `squareEnergy`. -/
theorem ccar_input_betaPowTwo : Foundations.BetaPowTwoStatement := by
  exact ParabolicRectifiability.Foundations.f3_betaPow_two_eq_betaSq_proof

/-! ## The `p`-power barycenter transfer -/

/-- **Fixed-model `p`-power Jensen transfer** (`CellsFitTransferStatement`). Jensen's inequality is
applied for one common plane before minimization.

Statement: for `p ≥ 2`, barycenter cells `D`, `s ≥ D.cutoff i` and one fixed model `L`,
`fitPow (D.atomicMeasure s) p L c_i s ≤ ofReal A * fitPow ν p L y_i (2s)`.

Proof (the `p`-version of the quadratic barycenter transfer):
1. `p`-Jensen on one cell: `ν(C) · d_P(bar_C, L)^p ≤ ∫_C d_P(w,L)^p dν` for measurable bounded
   `C` with `0 < ν(C) < ∞`. Real form: `y ↦ modelRealCost L y ^ (p/2)` is convex on coordinates
   (`ConvexOn.comp` of `convexOn_rpow` (`1 ≤ p/2`) on `Ici 0`, monotone there, with
   `convexOn_modelRealCost`), then `ConvexOn.map_integral_le` against
   `normalizedRestriction ν C` exactly as in `modelRealCost_spaceTimeBarycenter_le_normalizedIntegral`
   and `mass_mul_modelRealCost_spaceTimeBarycenter_le`; integrability from
   `integrableOn_continuous_of_bounded` (`continuous_modelRealCost` composed with
   `Real.continuous_rpow_const`). Convert with
   `infEDist w (modelSet L) ^ p = ENNReal.ofReal (modelRealCost L w ^ (p/2))`
   (from `modelCost = infEDist ^ 2 = ofReal (modelRealCost)`, `ENNReal.rpow_natCast`,
   `ENNReal.rpow_mul`, `ENNReal.ofReal_rpow_of_nonneg`).
2. Weighted form (`weighted_modelCost_le`): `ofReal w_j · d(c_j,L)^p ≤ ofReal A ∫_{C_j} d^p dν`,
   from `w_j ≤ A ν(C_j)`.
3. Sum over the contributing atoms (`fit_finiteCutoffAtomicMeasure`-style evaluation of the
   finite Dirac sum, `lintegral_dirac` with measurable singletons), disjoint cells
   `C_j ⊆ P(y_i,2s)` (`contributing_cell_subset_ball`), and `lintegral_biUnion_finset`
   (no measurability of the integrand needed). The model `L` is fixed throughout; no infimum.
The counterexample `|t|^{p/2}` shows that `p ≥ 2` is essential.

Proved by `ccar_cells_fit_transfer_proof`. -/
theorem ccar_cells_fit_transfer : CellsFitTransferStatement := by
  exact ccar_cells_fit_transfer_proof

/-- **Barycenter cells into the truncated active-radius packing** (`CellsPackingStatement`).

Statement: `Σ_i w_i ≤ Ct (b + A 2^{k+p} L^{p/2}) R^k` for cells with disjoint cutoff balls
in `P(q,R)`, weights `w_i ≤ b ρ_i^k` and sample energies `≤ L`.

Proof (the `p`-version of `sum_weight_le_of_barycenterCells`):
1. Infimum (`fittingInfimum_atomicMeasure_le`): `⨅_L fitPow(λ_s) ≤ ofReal A · ⨅_L fitPow ν(y_i,2s)`
   from the fixed-model hypothesis (`le_iInf`, `ENNReal.mul_iInf_of_ne`; `Nonempty` handles
   `A = 0`).
2. Normalization (`betaSq_atomicMeasure_le`): `betaPow λ_s k T p c_i s ≤
   ofReal A * 2^{k+p} * betaPow ν k T p y_i (2s)` for `s ≥ ρ_i`, since
   `(ofReal s)⁻¹^{k+p} = 2^{k+p} (ofReal (2s))⁻¹^{k+p}` (`ENNReal.rpow`, real exponent `k+p`).
3. Energy (`atomicEnergy_le`): raise to `2/p` (`ENNReal.mul_rpow_of_nonneg`), integrate over
   `Ioi ρ_i` (`setLIntegral_mono'`, `lintegral_const_mul'` with a finite constant), change
   variables `u = 2s` (`lintegral_comp_two_Ioi_scaleMeasure`; the radius measurability of
   `u ↦ betaPow ν k T p y u ^ (2/p)` follows as in `measurable_betaSq_monotone_source`: the
   infimum is monotone in `u` and the prefactor continuous), enlarge to `Ioi 0`: the bound is
   `ofReal ((A 2^{k+p})^{2/p} L)`.
4. Packing: with `z = D.barycenter`, `r = D.cutoff`, `w_j = D.weight j / ρ_j^k`,
   `BetaP.truncatedAtomicSource k z r w s = D.atomicMeasure s` (the bridge of
   `truncatedAtomicSource_eq_finiteCutoffAtomicMeasure`, here for the `BetaP` copy; masses
   `w_j ρ_j^k = D.weight j`); the bound `hbound` applied to `IsWeightedPacking q R z r w b`
   gives `atomicSource … univ ≤ ofReal (Ct (b + B^{p/2}) R^k)` with
   `B^{p/2} = A 2^{k+p} L^{p/2}` (`Real.mul_rpow`, `Real.rpow_rpow_inv`-type identities,
   `A, L ≥ 0`); `atomicSource … univ = Σ_i ofReal (D.weight i)` (`Measure.dirac_apply`).

Uses `CellsFitTransferStatement`. Proved by `ccar_cells_packing_proof`. -/
theorem ccar_cells_packing : CellsFitTransferStatement → CellsPackingStatement := by
  exact ccar_cells_packing_proof

/-! ## The general `K_a` estimates -/

/-- **The loss `ν(X ∖ K_a) ≤ C(a + L^{p/2})`** (`CarrierLossStatement`).

Statement: the general loss estimate of `K_a = densityCarrier ν k a` for every `a > 0`.

Proof (as in the quadratic `measure_compl_densityCarrier_le`, with `allScaleEnergyP` in place of
`allScaleEnergy` and `CellsPackingStatement` in place of `sum_weight_le_of_barycenterCells`):
1. Selection: `ae_largeDimension`, `exists_deficient_radius` (first doubling scale,
   `D = 50^{n+3}`), Vitali
   (`Vitali.exists_disjoint_subfamily_covering_enlargement`, enlargement 5).
2. For each finite subfamily: cells `P(g_i, ρ_i/10)` (`ε = 1/10`), samples from
   `exists_mem_of_ae_of_measure_ne_zero`, weights `m_i = ν(P(g_i,ρ_i/10))`, `A = 1`,
   cutoff balls `P(c_i, ρ_i/2) ⊆ P(g_i,ρ_i) ⊆ P(c,1)` and pairwise disjoint,
   `m_i < a(5ρ_i)^k = 10^k a (ρ_i/2)^k`, so `b = 10^k a`; `CellsPackingStatement` with
   `R = 1` gives `Σ m_i ≤ Ct (10^k a + 2^{k+p} L^{p/2})`.
3. Countable sum by `ENNReal.tsum_eq_iSup_sum`, doubling `ν(5B_i) ≤ D m_i`, and the
   cover of `(K_a)ᶜ` by `supp ν ᶜ`, the non-large-dimension null set and the `5B_i`.
   The constant is `C = 50^{n+3} Ct (10^{n+1} + 2^{n+1} 2^p)` (or any larger), chosen after
   `n, p, Ct`.

Uses `CellsPackingStatement`. Proved by `ccar_loss_proof`. -/
theorem ccar_loss : CellsPackingStatement → CarrierLossStatement := by
  exact ccar_loss_proof

/-- **Local nets with synthetic weights** (`CarrierSeparatedStatement`).

Statement: finite `r`-separated subsets of `K ∩ P(q,R)` have at most
`C (1 + L^{p/2}/a) (R/r)^k` points, for every `K` with the all-radius lower mass of `ν`.

Proof (as in the quadratic `card_le_of_separated_densityCarrier`): `ρ = r/20`, closed cells
`P̄(z_i,ρ)` with mass `≥ a ρ^k` (lower mass, `ρ ≤ 1`), `radius = 10ρ`, `ε = 1/10`,
cutoff `5ρ`, synthetic weights `(5ρ)^k`, `A = 5^k/a`, `b = 1`, parent `P(q,3R)`;
`CellsPackingStatement` gives `N (5ρ)^k ≤ Ct (1 + 5^k 2^{k+p} L^{p/2}/a) (3R)^k`; finish with
the arithmetic of `localNet_arith` (now with the factor `2^{k+p}` in place of `2^{k+2}`).
All radii are equal, so the truncated testing source equals the full one above the common
cutoff: the full-source packing statement is not needed.

Uses `CellsPackingStatement`. Proved by `ccar_separated_proof`. -/
theorem ccar_separated : CellsPackingStatement → CarrierSeparatedStatement := by
  exact ccar_separated_proof

/-- **Equal-radius content bounds from separated sets** (`ContentOfSeparatedStatement`). Generic:
no measure, no energy, no exponent.

Statement: `K ⊆ P(c,1)` with the separated-set bound `A ≥ 0` has
`HasMetricContentBounds k (C₀ A) K` for every `k ≤ n+2`, with `C₀ = C₀(n)`.

Proof (as the content-bound step of `density_selection_of_discrete`, with `A` in place of
`Cnet (1 + L/a)`): nets by `exists_maximal_separated_finset` with the bound `⌊A (R/ρ)^k⌋₊`; local Hausdorff by
`hausdorffP_le_of_nets` (`A 2^k R^k ≤ A 2^{n+2} R^k`); separated sets directly; the tube by one
net of `K = K ∩ P(c,1)` at scale `r` and `parabolicVolume_thickening_le_of_net`
(`A (1/r)^k 2ω (2r)^{n+2} = A 2ω 2^{n+2} r^{n+2-k}`, natural subtraction, `k ≤ n+2`).
`C₀ = 2^{n+2} + 2 (omega n).toReal 2^{n+2} + 1` works.

Proved by `ccar_content_of_separated_proof`. -/
theorem ccar_content_of_separated : ContentOfSeparatedStatement := by
  exact ccar_content_of_separated_proof

/-- **Variable-radius packing with its own transfer** (`CarrierVariablePackingStatement`).

Statement: `HasFiniteBallPacking k (C (1 + L^{p/2}/a)) K` for every `K` with the
all-radius lower mass of `ν`.

Proof (as the quadratic `variable_radius_packing_of_discrete`, with `CellsPackingStatement` in
place of the quadratic transfer): closed cells `P̄(z_i, r_i/100)` (`ε = 1/100`,
`radius = r_i`, cutoff `r_i/2`), masses `≥ a (r_i/100)^k`, synthetic weights `(r_i/2)^k`,
`A = 50^k/a`, `b = 1`, cutoff balls inside `P(z_i,r_i)` hence disjoint and inside `P(q,2R)`;
`CellsPackingStatement` gives `Σ (r_i/2)^k ≤ Ct (1 + 50^k 2^{k+p} L^{p/2}/a)(2R)^k`; multiply
by `2^k`. This is not derived from the equal-radius nets.

Uses `CellsPackingStatement`. Proved by `ccar_variable_packing_proof`. -/
theorem ccar_variable_packing : CellsPackingStatement → CarrierVariablePackingStatement := by
  exact ccar_variable_packing_proof

/-! ## Energy of the carrier measure -/

/-- **Domination transfer for `B_p`** (`BetaPowDominationStatement`).

Statement: `μ ≤ c ν` (real `c > 0`) implies `B_{p,μ}(z,r) ≤ c B_{p,ν}(z,r)`.

Proof: for `r ≤ 0` both sides are `0`. For `r > 0` and each model,
`fitPow μ p L z r ≤ fitPow (ofReal c • ν) p L z r = ofReal c * fitPow ν p L z r`
(`lintegral_mono'` with `Measure.restrict_mono`, `Measure.restrict_smul`,
`lintegral_smul_measure`); then `iInf_mono` and `ENNReal.mul_iInf_of_ne` (`ofReal c ≠ 0, ⊤`;
an empty family gives `⊤ ≤ c·⊤ = ⊤`), and multiply by the prefactor (`mul_left_comm`). The
guards are not used. This avoids `BetaPowSmulStatement`.

Proved by `ccar_betaPow_domination_proof`. -/
theorem ccar_betaPow_domination : BetaPowDominationStatement := by
  exact ccar_betaPow_domination_proof

/-- **Finite own-Hausdorff square of `η = H_P^k⌊K`** (`CarrierEnergyStatement`).

Statement: `η`-a.e. `squareEnergy η k T 1 z < ⊤`, from the proved growth of `η`, the
domination `η ≤ d ν` and the `ν`-a.e. all-scale bound `≤ L`.

Proof:
1. `η` is finite (`η univ = H_P^k(K ∩ P(c,1)) ≤ ofReal U`), hence `IsFiniteMeasureOnCompacts`
   and inner regular (`inferInstance`).
2. Good set `G = {y | allScaleEnergyP ν k T p y ≤ ofReal L}`: `ν Gᶜ = 0`, hence `η Gᶜ = 0`
   (`Measure.absolutelyContinuous_of_le_smul`); no measurability of `G` is needed.
3. For `y ∈ G` and `0 < r < 1`: `betaSq η k T y r = betaPow η k T 2 y r` (`hTwo`)
   `≤ densityRatio η k y r ^ (1 - 2/p) * betaPow η k T p y r ^ (2/p)` (`hHolder`, second
   part), `densityRatio η k y r ≤ ofReal U` (`Measure.restrict_apply measurableSet_ball`,
   growth at `R = r`), and `betaPow η … ≤ ofReal d * betaPow ν …` (`hdom` with `μ = η`); so
   `betaSq η k T y r ≤ (ofReal U)^{1-2/p} (ofReal d)^{2/p} betaPow ν k T p y r ^ (2/p)`
   (`ENNReal.rpow_le_rpow`, `ENNReal.mul_rpow_of_nonneg`).
4. Integrate over `Ioo 0 1` (`setLIntegral_mono'`, `lintegral_const_mul'` with a finite
   constant, `lintegral_mono_set` into `Ioi 0`): `squareEnergy η k T 1 y ≤ K₀ · ofReal L < ⊤`.

Uses `BetaPowHolderStatement`, `Foundations.BetaPowTwoStatement` and
`BetaPowDominationStatement`. Proved by `ccar_energy_proof`. -/
theorem ccar_energy : BetaPowHolderStatement → Foundations.BetaPowTwoStatement →
    BetaPowDominationStatement → CarrierEnergyStatement := by
  exact ccar_energy_proof

end ParabolicRectifiability.BetaP.CarrierTree
