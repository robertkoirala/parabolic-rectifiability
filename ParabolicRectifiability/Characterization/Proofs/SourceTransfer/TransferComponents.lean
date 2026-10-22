import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.TransferStatements
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.CouplingEnergy
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.ExceptionalMass
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.OnCarrierCoupling
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.CouplingErrorTonelli
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.OnCarrierErrorEstimate
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.OffCarrierErrorEstimate
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.OffCarrierKernel
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.KernelCoupling
import ParabolicRectifiability.Characterization.Proofs.Replacement.BadRegionReplacement
import ParabolicRectifiability.Foundations.Proofs.SquareEnergyBounds
import ParabolicRectifiability.Foundations.Statements.Measurability

/-! # Component estimates for the transfer of square finiteness

The declarations below are the component estimates of
`adr_source_transfer : SourceTransferStatement`; they delegate to the corresponding proof
modules and are assembled in `adr_source_transfer_of_leaves`.

* Component estimates (each is a named statement):
  `b3_couplingEnergy`, `b3_exceptionalMass`, `b3_onCarrierCoupling`,
  `b3_couplingErrorTonelli`, `b3_onCarrierErrorEstimate`, `b3_offCarrierErrorEstimate`,
  `b3_offCarrierKernel`, `b3_kernelCoupling`.
* The statements `OnCarrierErrorStatement`, `OffCarrierErrorStatement` and
  `OffCarrierCouplingStatement` are proved
  (`b3_onCarrierError_of_parts`, `b3_offCarrierError_of_parts`,
  `b3_offCarrierCoupling_of_parts`) from the bridge, the two estimates, the kernel and the
  kernel coupling.
* Input estimates: `b3_input_replacement` (`bad_region_replacement`) and
  `b3_input_squareFinitenessEndpoint` (`squareEnergy_lt_top_iff_of_endpoints`).

No component assumes a square-function conclusion of the main statement: the only
square-finiteness inputs of the assembly are the hypothesis of `SourceTransferStatement`
(reference square finite `σ`-a.e.) and the endpoint independence of the square.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.SourceTransferTree

open ParabolicRectifiability.Foundations

/-! ## Input estimates -/

/-- Replacement of the bad region, `bad_region_replacement : ReplacementStatement`. -/
theorem b3_input_replacement : ReplacementStatement := by
  exact ParabolicRectifiability.Characterization.ReplacementTree.bad_region_replacement_of_leaves

/-- Endpoint independence of square finiteness,
`squareEnergy_lt_top_iff_of_endpoints : SquareFinitenessEndpointStatement`. It is used to fill
the finite annulus `[1/2, 1)` (on carrier) and `[1/4, 1)` (off carrier) for a finite source.
A finite measure on `Space n` is finite on compacts and inner regular (Mathlib
instances), so the statement applies. -/
theorem b3_input_squareFinitenessEndpoint : SquareFinitenessEndpointStatement := by
  exact ParabolicRectifiability.Foundations.squareEnergy_lt_top_iff_of_endpoints_proof

/-! ## Component estimates -/

/-- The fixed-plane coupling inequality at the
energy level, `CouplingEnergyStatement` (route in its docstring).

Mathlib ingredients: `Measure.fst`, `Measure.snd`, `lintegral_map`,
`ENNReal.iInf_add`, `ENNReal.mul_iInf`, `Metric.infEDist_le_infEDist_add_edist`,
`ENNReal.add_pow_le` (or `(a+b)^2 ≤ 2a^2 + 2b^2` directly), `MeasurableEmbedding.lintegral_map`
for the dilation `r ↦ a r` of `dr/r`; also `betaSq_of_pos`, `radius_ratio_normalization`,
`measurable_betaSq`, `scaleMeasure_apply`; the dilation invariance of `dr/r` already exists
as `map_const_mul_scaleMeasure` and `setLIntegral_scaleMeasure_comp_const_mul`
(imported and reused). Measurability in `r` of the error term: see the corrected docstring of
`CouplingEnergyStatement` (unweighted cumulative integral monotone; the weighted one need
not be). -/
theorem b3_couplingEnergy : CouplingEnergyStatement := by
  exact ParabolicRectifiability.Characterization.SourceTransferTree.b3_couplingEnergy_proof

/-- `ExceptionalMassStatement`.

The replacement data enter through `b3_IsReplacementData`.
Mathlib ingredients: `Measure.measure_compl_support`, `measure_iUnion_le`, `measure_iUnion` (disjoint
Borel `B_i`), `ENNReal.tsum_mul_left`. -/
theorem b3_exceptionalMass : ExceptionalMassStatement := by
  exact ParabolicRectifiability.Characterization.SourceTransferTree.b3_exceptionalMass_proof

/-- The on-carrier replacement as a coupling,
`OnCarrierCouplingStatement`.

Mathlib ingredients: `Measure.map` of the diagonal, `Measure.prod`,
`Measure.sum`, `Measure.fst_sum`, `Measure.snd_sum`, `Measure.fst_prod` (probability
normalization of `σ⌊B_i / σ(B_i)`), `Measure.measure_compl_support`, `measure_iUnion`. -/
theorem b3_onCarrierCoupling : OnCarrierCouplingStatement := by
  exact ParabolicRectifiability.Characterization.SourceTransferTree.b3_onCarrierCoupling_proof

/-- The measurability/Tonelli bridge
`CouplingErrorTonelliStatement`, shared by the on-carrier and off-carrier errors.

Mathlib ingredients: `IsFiniteMeasureOnCompacts` with `SigmaCompactSpace`
(sigma-finiteness of `σ`), `Measure.withDensity` (s-finiteness of `scaleMeasure`),
`IsOpen.measurableSet` for `{(x,r,p) : dist p.1 x < r}` (second-countable product, so the
product σ-algebra is Borel), `Measurable.lintegral_prod_right'`, `lintegral_lintegral_swap`,
`lintegral_indicator`, `setLIntegral_const`-style rewriting of
`∫_x 1_D 1_{P(p.1,r)} dσ = σ(D ∩ P(p.1,r))`, `Metric.mem_ball`, `dist_comm`. -/
theorem b3_couplingErrorTonelli : CouplingErrorTonelliStatement := by
  exact ParabolicRectifiability.Characterization.SourceTransferTree.b3_couplingErrorTonelli_proof

/-- The on-carrier
geometric estimate in Tonelli form, `OnCarrierErrorEstimateStatement` (route in its
docstring). The theorem `b3_onCarrierError_of_parts` combines it with the bridge.

Mathlib ingredients: `lintegral_mono_ae`, `lintegral_indicator`,
`Measure.fst_apply` (`π.fst = ν`), `measure_iUnion` and `tsum` over the disjoint Borel `E_i`,
`setLIntegral_mono`, `lintegral_inv_pow_Ioi_scaleMeasure` with `p = 2` and
`a = 15 r_i` (`∫_{(15r_i,∞)} r^{-2} dr/r = 1/(450 r_i^2)`), `IsADRCarrier.upper` at `z_i`.
Raw constant `36 C 2^k / 450` (kept separate from the factor `2` of `b3_couplingEnergy`). -/
theorem b3_onCarrierErrorEstimate : OnCarrierErrorEstimateStatement := by
  exact ParabolicRectifiability.Characterization.SourceTransferTree.b3_onCarrierErrorEstimate_proof

/-- The off-carrier geometric estimate in Tonelli
form, `OffCarrierErrorEstimateStatement` (route in its docstring). The theorem
`b3_offCarrierError_of_parts` combines it with the bridge.

Mathlib ingredients: `Metric.infEDist`, `IsClosed.notMem_iff_infEDist_pos`
(or `Metric.mem_closure_iff_infEDist_zero`), `Metric.infEDist_ne_top` (`Γ` nonempty),
recentering `P(y,s) ⊆ P(γ,2s)` at `γ ∈ Γ ∩ P(y,s)`, `IsADRCarrier.upper`,
`lintegral_inv_pow_Ioi_scaleMeasure` with `p = 2` and `a = d(y)`. Raw constant
`9 C 2^k / 2`. -/
theorem b3_offCarrierErrorEstimate : OffCarrierErrorEstimateStatement := by
  exact ParabolicRectifiability.Characterization.SourceTransferTree.b3_offCarrierErrorEstimate_proof

/-- The normalized moving-ball Borel
probability kernel, `OffCarrierKernelStatement` (checkpoints in its docstring).

Mathlib ingredients: `ProbabilityTheory.Kernel`, `Kernel.piecewise` (on the
closed, hence measurable, `Γ`), `Kernel.deterministic` (`δ_y`, with `measurable_id`), a
kernel built from `y ↦ (σ(P(y,2d(y))))⁻¹ • σ.restrict (P(y,2d(y)))` (measurability through
`Measure.measurable_of_measurable_coe` and `measurable_measure_prodMk_left` on the Borel set
`{(y,w) : dist w y < 2 infDist y Γ}`), `IsMarkovKernel` (normalization with
`ENNReal.inv_mul_cancel` on the positive finite denominator), `Metric.infEDist`,
`Metric.exists_dist_lt_of_infDist_lt` (the non-measurable nearby point for the bounds only),
`IsADRCarrier.lower`/`.upper`/`.nonempty`, `Measure.measure_compl_support`. -/
theorem b3_offCarrierKernel : OffCarrierKernelStatement := by
  exact ParabolicRectifiability.Characterization.SourceTransferTree.b3_offCarrierKernel_proof

/-- The coupling of a Markov kernel,
`KernelCouplingStatement`. The localization conjunct of `OffCarrierCouplingStatement` is not
part of this statement; it is derived in `b3_mem_ball_of_displacement`.

Mathlib ingredients: `Measure.compProd` (`μ ⊗ₘ K`),
`Measure.fst_compProd` (Markov), `Measure.compProd_apply` or `Measure.snd_compProd` for
`π.snd Γᶜ = ∫ K_y(Γᶜ) dμ = 0`, `Measure.ae_compProd_iff` on the Borel displacement set
(`continuous_edist`, `continuous_infEDist`, `isClosed_le`), finiteness of `μ ⊗ₘ K`. -/
theorem b3_kernelCoupling : KernelCouplingStatement := by
  exact ParabolicRectifiability.Characterization.SourceTransferTree.b3_kernelCoupling_proof

end ParabolicRectifiability.Characterization.SourceTransferTree
