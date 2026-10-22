import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyStatements
import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies.ExponentAmplitude
import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies.DataAssembly
import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies.Step
import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies.Weierstrass
import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies.Weight
import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies.NonregularAmplitude

/-! # Statements of the lacunary frequency construction

Each statement is proved by the corresponding module.
-/

namespace ParabolicRectifiability.Examples

/-- **One-step inequalities.**
Route: `M = max{…} ≤ ⌈M⌉₊ < N' = ⌈M⌉₊ + 1` (`Nat.le_ceil`), so `N' > 0` and `16 N_j ≤ N'` by
casting back to `ℕ`. With `s ≥ 0`: if `s = 0` the low-frequency bound is `0 ≤ a_{j+1}/100`;
otherwise `√N' ≥ 100π s/a_{j+1} > 0` (`Real.le_sqrt`, `Real.sqrt_sq`) gives
`π s/√N' ≤ a_{j+1}/100`. Likewise `√N' ≥ 1000 a_{j+1} √N_j/a_j > 0` gives the decay bound.
All denominators are positive (`a_j > 0`, `N_j > 0`). -/
theorem e2_lacunaryStep_spec : E2LacunaryStepStatement := by
  exact e2_lacunaryStep_spec_proof

/-- **State invariant and assembly of `IsLacunaryData`.** Implication form over the one-step inequalities.
Route: induction gives `(e2_lacunaryState a j).2 = Σ_{i<j} a_i √N_i` (`Finset.sum_range_succ`;
the step's second component is `q.2 + a_j √N_j` by `rfl`), hence `0 ≤ (state j).2`, and
`0 < N_j` (`N_0 = 1`; successors by the one-step inequalities). Fields: positivity; growth and decay from
the one-step inequalities at `q = state j`; low frequency at `0` is the empty sum (`0 ≤ a_0/100`), at `j + 1` it is
the one-step bound after rewriting `(state (j+1)).2 = Σ_{i<j+1}`; `a_j ≤ 1` is the hypothesis. -/
theorem e2_lacunaryState_assembly : E2LacunaryAssemblyStatement := by
  exact e2_lacunaryState_assembly_proof

/-- **Weighted geometric majorant and tails.**
Route: `w_j = a_j/√N_j > 0` from `amplitude_pos`, `frequency_pos`; `amplitude_decay` is
`w_{j+1} ≤ w_j/1000` after `div_div`; induction gives `w_j ≤ w_0 1000^{-j}`;
`Summable.of_nonneg_of_le` with `summable_geometric_of_lt_one`; the tail
`Σ_i w_{j+1+i} ≤ Σ_i w_j 1000^{-(i+1)} = w_j/999` by `tsum_le_tsum` and `tsum_geometric_of_lt_one`. -/
theorem e2_lacunaryWeight : E2LacunaryWeightStatement := by
  exact e2_lacunaryWeight_proof

/-- **Weierstrass M-test for the cosine series.** No lacunary hypothesis and no sign of `ε`.
Route: `|w_j cos(N_j t)| ≤ w_j` gives absolute summability (`Summable.of_nonneg_of_le`);
`tendstoUniformly_tsum_nat` (bound `‖f j t‖ ≤ w_j`) gives uniform convergence of the partial
sums to the `tsum`; multiply by the constant `ε` (uniform continuity of `x ↦ ε x`, or the
`dist` bound `|ε| · dist`), and unfold `lacunaryFunction`. -/
theorem e2_lacunary_weierstrass : E2LacunaryWeierstrassStatement := by
  exact e2_lacunary_weierstrass_proof

/-- **Nonregular amplitude admissibility.** Route: `Real.one_le_sqrt`, `inv_pos`,
`inv_le_one_of_one_le₀`, after `intro j`. -/
theorem e2_nonregularAmplitude_admissible : E2NonregularAmplitudeStatement := by
  exact e2_nonregularAmplitude_admissible_proof

/-- **Exponent amplitude admissibility, exact range.**
Route: `√(j+1) ≥ 1` and `log(j+2) ≥ log 2 > 0` (`Real.log_le_log`), so the denominator is at
least `log 2 > 0`: positivity, and `a_j ≤ a_0 = c₀/log 2`. Hence `(∀ j, a_j ≤ 1) ↔ c₀ ≤ log 2`
(`→` at `j = 0` with `√1 = 1`; `←` by `div_le_one`). -/
theorem e2_exponentAmplitude_admissible : E2ExponentAmplitudeStatement := by
  exact e2_exponentAmplitude_admissible_proof

end ParabolicRectifiability.Examples
