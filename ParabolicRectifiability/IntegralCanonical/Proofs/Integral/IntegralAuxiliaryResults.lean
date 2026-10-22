import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.IntegralAuxiliaryStatements
import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.TailVanishing
import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.CappedTailLimit
import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.CappedValueLimit
import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.CompactExhaustion
import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.PositiveWeight
import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.GaugeSeriesAdmissible
import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.GaugeSeriesIntegral

/-! # Intermediate results for the integral tests

Each declaration below proves one of the seven statements of
`i2_TailVanishingStatement`, … (tail vanishing, the capped tail and capped value
limits, compact exhaustion, positive weight, and the admissibility and integrability of the
gauge series) by the corresponding `…_proof` theorem. The docstrings record the proof ideas.
-/

noncomputable section

namespace ParabolicRectifiability.IntegralCanonical

/-- **Tail vanishing** (`i2_TailVanishingStatement`).
Proof idea: for `0 < ρ ≤ R`, `S^ρ(z) = ∫_{(0,ρ)} β²(z,r) dr/r` is the mass of `(0,ρ)` for the finite
measure `scaleMeasure.restrict (Ioo 0 R)` with density `r ↦ β²(z,r)` (measurable:
`measurable_betaSq`); `⋂_j (0, 1/(j+1)) = ∅` and continuity from above give `S^{1/(j+1)}(z) → 0`;
monotonicity in the endpoint (`lintegral_mono_set`) bracketing gives the limit along `𝓝[>] 0`. -/
theorem i2_tail_vanishing : i2_TailVanishingStatement := by
  exact ParabolicRectifiability.IntegralCanonical.i2_tail_vanishing_proof

/-- **Capped tail limit** (`i2_CappedTailLimitStatement`).
Proof idea: `tendsto_lintegral_filter_of_dominated_convergence` along the countably generated filter
`𝓝[>] 0`, with measurable integrands (`measurable_squareEnergy`), bound `1`, finite
`∫_A 1 dμ = μ A` (`A` bounded, closure compact in the proper space, `IsFiniteMeasureOnCompacts`),
the pointwise hypothesis, and `∫_A 1_{S=∞} dμ = μ(A ∩ {S = ∞})` (`lintegral_indicator_const`,
`measurableSet_squareEnergy_eq_top`, which follows from `measurable_squareEnergy`). -/
theorem i2_cappedTail_limit : i2_CappedTailLimitStatement := by
  exact ParabolicRectifiability.IntegralCanonical.i2_cappedTail_limit_proof

/-- **Capped value limit** (`i2_CappedValueLimitStatement`).
Proof idea: for `L > 0`, `(ofReal L)⁻¹ ∫_A min{S, L} dμ = ∫_A (ofReal L)⁻¹ min{S, L} dμ`
(`lintegral_const_mul`, measurable integrand); the integrand lies in `[0,1]`, tends to `0` where
`S < ∞` and equals `1` where `S = ∞`; dominated convergence along `atTop` on `ℝ` with bound `1`
and finite `μ A`. -/
theorem i2_cappedValue_limit : i2_CappedValueLimitStatement := by
  exact ParabolicRectifiability.IntegralCanonical.i2_cappedValue_limit_proof

/-- **Compact exhaustion** (`i2_CompactExhaustionStatement`).
Proof idea: `B_j = P(0,j)`; continuity from below on `B_j ∩ {S ≤ N}` gives `a_j` with
`μ(B_j \ {S ≤ a_j}) < 2^{-j}/2`; inner regularity of the finite restriction (Radon) gives compact
`C_j ⊆ B_j ∩ {S ≤ a_j}` with `μ(B_j \ C_j) < 2^{-j}`; `K_j = ⋃_{i ≤ j} C_i` is compact,
increasing, `∫_{K_j} S ≤ Σ_{i ≤ j} a_i μ(C_i) < ∞`; for fixed `N` and `j ≥ N`,
`μ(B_N \ ⋃ K) ≤ μ(B_j \ C_j) < 2^{-j}`, so `μ(B_N \ ⋃ K) = 0`, and the countable union over `N`.
The energy source stays `μ`. -/
theorem i2_compactExhaustion : i2_CompactExhaustionStatement := by
  exact ParabolicRectifiability.IntegralCanonical.i2_compactExhaustion_proof

/-- **Positive weight** (`i2_PositiveWeightStatement`).
Proof idea: `w z = (1 + (S z).toReal)⁻¹` on the Borel set `{S < ∞}` and `1` elsewhere (`Measurable.ite`,
`measurable_squareEnergy`); `0 < w ≤ 1`; `ofReal (w z) * S z ≤ 1` on `{S < ∞}`, which has full
measure, so `∫_A ofReal w · S dμ ≤ μ A < ∞` for bounded `A` (`lintegral_mono_ae`). -/
theorem i2_positiveWeight : i2_PositiveWeightStatement := by
  exact ParabolicRectifiability.IntegralCanonical.i2_positiveWeight_proof

/-- **The gauge series is admissible** (`i2_GaugeSeriesAdmissibleStatement`).
Proof idea: on `[0, M]` the terms satisfy `0 ≤ min{1, u/t_j} ≤ M t_j⁻¹`, so the series converges
uniformly there (`continuousOn_tsum` on `Icc 0 M`, then on `Ici 0` locally); monotone termwise
(`tsum_le_tsum` with summable comparison); concavity inequality termwise (each term is the
minimum of two affine maps) and `tsum_add`, `tsum_mul_left`; `Φ(0) = 0`; nonnegative; unbounded:
for `u ≥ max_{j < N} t_j` the first `N` terms equal `1`, so `Φ(u) ≥ N` (`sum_le_tsum`). The
convergence is not uniform on all of `[0, ∞)`. -/
theorem i2_gaugeSeries_admissible : i2_GaugeSeriesAdmissibleStatement := by
  exact ParabolicRectifiability.IntegralCanonical.i2_gaugeSeries_admissible_proof

/-- **Finite gauge integral** (`i2_GaugeSeriesIntegralStatement`).
Proof idea: `μ(A ∩ {S > s}) ↓ 0` as `s → ∞` (`μ A < ∞`, `S < ∞` a.e.); choose recursively `t_0 ≥ 1`,
`t_j ≥ 2 t_{j-1}` with `μ(A ∩ {S > t_j}) ≤ 2^{-j}` and `t_{j-1}/t_j ≤ 2^{-j}` (so `t_j > 0` and
`Σ t_j⁻¹ ≤ 2`); off the null set `{S = ∞}`, `extendedGauge Φ_t (S) = Σ_j ofReal (min{1, S/t_j})`
(`ENNReal.ofReal_tsum_of_nonneg`); `lintegral_tsum` (measurable terms); for `j ≥ 1` split at
`S = t_{j-1}`: `∫_A min{1, S/t_j} ≤ μ(A) t_{j-1}/t_j + μ(A ∩ {S > t_{j-1}}) ≤ μ(A) 2^{-j} + 2^{1-j}`;
the first term is at most `μ A`; two geometric series. -/
theorem i2_gaugeSeries_integral : i2_GaugeSeriesIntegralStatement := by
  exact ParabolicRectifiability.IntegralCanonical.i2_gaugeSeries_integral_proof

end ParabolicRectifiability.IntegralCanonical
