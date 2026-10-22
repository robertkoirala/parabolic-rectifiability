import ParabolicRectifiability.BetaP.Proofs.Localization.LocalizationStatements
import ParabolicRectifiability.BetaP.Proofs.Laws.Measurability
import ParabolicRectifiability.BetaP.Proofs.Laws.Basic
import ParabolicRectifiability.BetaP.Proofs.Localization.Tail
import ParabolicRectifiability.BetaP.Proofs.Localization.AllScale

/-! # Auxiliary results for the localization of a source

These are the results used by `cloc_exists_p_localization` to prove `exists_p_localization`.
They prove the named statements `ClocPTailStatement` and `ClocAllScaleStatement`.

* `cloc_pTail` (the exact `p`-tail) and `cloc_allScale` (the all-scale bound `2M` of a small
  restriction).
* `cloc_input_measurability` and `cloc_input_restriction`: the measurability and restriction laws
  for `B_p`.

The fixed grid, the disjointified cells, the exact cover of the good set, and the finiteness,
inner regularity and support of the restrictions come from `goodSourceLocalization`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## Input statements -/

/-- **Measurability law for `B_p`**: `BetaPowMeasurabilityStatement`, proved by
`cfit_betaPowMeasurability_proof`. It makes the good set `P(0,1) ∩ {S_p^2 ≤ M}` Borel, so the
localization regions are Borel. -/
theorem cloc_input_measurability : BetaPowMeasurabilityStatement := cfit_betaPowMeasurability_proof

/-- **Restriction law for `B_p`**: `BetaPowRestrictionStatement`, proved by
`claws_restriction_proof`. It is used by `cloc_allScale`. -/
theorem cloc_input_restriction : BetaPowRestrictionStatement := claws_restriction_proof

/-! ## The tail and the all-scale bound -/

/-- **Exact `p`-tail** (`ClocPTailStatement`): for `ν` with compact support of diameter `< 1`,
`z ∈ supp ν` and `p > 0`, `∫_{(2,∞)} B_p^{2/p} ds/s = (ofReal (2^{q_p} - 1))⁻¹ ∫_{(1,2)} B_p^{2/p}
ds/s`, `q_p = 2 + 2k/p`.

Proof (the `p`-version of the quadratic tail computation):
1. For `s ≥ 1`, `supp ν ⊆ P(z,s)` (`support_subset_ball_of_diam_lt_one`) and `ν` is carried
   by its support (`Measure.support_mem_ae`), so `fitPow ν p L z s = ∫ d_P(w,L)^p dν`
   (`Measure.restrict_eq_self_of_ae_mem`), and `betaPow ν k T p z s = (ofReal s)⁻¹^{k+p} · I_p`
   with `I_p = ⨅ L, ∫ d_P(w,L)^p dν` (adapt `betaSq_eq_global_of_support_diam`).
2. `(x · I)^{2/p} = x^{2/p} I^{2/p}` (`ENNReal.mul_rpow_of_nonneg`, `2/p ≥ 0`) and
   `((ofReal s)⁻¹^{k+p})^{2/p} = (ofReal s)⁻¹^{q_p}` (`ENNReal.rpow_mul`, `(k+p)(2/p) = q_p`).
3. Pull the constant `I_p^{2/p}` out of both integrals (`lintegral_mul_const`, adapt
   `lintegral_betaSq_of_support_diam`), and prove the real-exponent analogue of
   `lintegral_inv_pow_tail_eq_annulus`: for real `q > 0`,
   `∫_{(2,∞)} (ofReal s)⁻¹^q ds/s = (ofReal (2^q - 1))⁻¹ ∫_{(1,2)} (ofReal s)⁻¹^q ds/s`
   (via `setLIntegral_scaleMeasure`, `integral_Ioi_rpow_of_lt` with exponent `-q-1 < -1`;
   values `2^{-q}/q` and `(1-2^{-q})/q`). -/
theorem cloc_pTail : ClocPTailStatement := cloc_pTail_proof

/-- **All-scale bound `2M`** (`ClocAllScaleStatement`): for `μ⌊G` with support in `P̄(c,1/64)`, a support point
`z` with `S_{p,μ,T}^2(z) ≤ M` has `allScaleEnergyP (μ⌊G) k T p z ≤ 2M`.

Proof: as for the quadratic `allScaleEnergy_restrict_le_two_mul`, with `betaPow … ^ (2/p)` in
place of `betaSq`:
the `(0,2)` part is `energyS (μ⌊G) k T p 2 z ≤ energyS μ k T p 2 z ≤ M`
(`BetaPowRestrictionStatement` at `a = 2`); the support is compact of diameter `≤ 1/32 < 1`; the
`(2,∞)` part is `(2^{q_p}-1)^{-1}` times the `(1,2)` part (`ClocPTailStatement`), and the factor
is `≤ 1` because `q_p ≥ 2` gives `2^{q_p} - 1 ≥ 3`; the endpoint `2` is `scaleMeasure`-null
(`scaleMeasure_singleton`).

The statement is in implication form over `BetaPowRestrictionStatement` and
`ClocPTailStatement`. -/
theorem cloc_allScale : ClocAllScaleStatement := cloc_allScale_proof

end ParabolicRectifiability.BetaP
