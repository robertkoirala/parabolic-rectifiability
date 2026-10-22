import ParabolicRectifiability.Examples.Lacunary

/-! # Named statements of the lacunary frequency construction

Definitions and proposition definitions only; the proofs are given separately.

Targets:
* `BetaP.lacunaryFrequencyExistence_obligation : LacunaryFrequencyExistence`. The `BetaP`
  declaration stays the single existence boundary; the construction here proves its unfolded
  body (no `BetaP` import on this side), and the `BetaP` side closes its type by `exact`
  (definitional unfolding).
* `Examples.lacunary_series_convergence : LacunaryConvergenceStatement`.

Indexing: Lean indices are the informal indices minus one.

**The recursion.** The state is `(N_j, Σ_{i<j} a_i √N_i)`. From state `q` at
index `j` put `s = q.2 + a_j √q.1 = Σ_{i<j+1} a_i √N_i` and
`N_{j+1} = ⌈max{16 N_j, (100π s / a_{j+1})², (1000 a_{j+1} √N_j / a_j)²}⌉₊ + 1`,
the three bounds in zero-based indexing; `N_0 = 1`.

The six statements:
1. `E2LacunaryStepStatement`: the one-step ceiling/square-root inequalities.
2. `E2LacunaryAssemblyStatement`: the state invariant `(state j).2 = Σ_{i<j} a_i √N_i` and the
   assembly of `IsLacunaryData` (implication form over 1).
3. `E2LacunaryWeightStatement`: the weighted geometric majorant `w_j = a_j/√N_j` and its tails.
4. `E2LacunaryWeierstrassStatement`: absolute summability and uniform convergence to the `tsum`
   from a summable nonnegative majorant (Weierstrass M-test; no lacunary hypothesis).
5. `E2NonregularAmplitudeStatement`: `0 < nonregularAmplitude j ≤ 1`.
6. `E2ExponentAmplitudeStatement`: `0 < exponentAmplitude c₀ j`, and `exponentAmplitude c₀ ≤ 1`
   holds for every `j` **exactly when** `c₀ ≤ log 2`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace ParabolicRectifiability.Examples

/-! ## The recursive frequency choice -/

/-- One step of the frequency recursion. From the state
`q = (N_j, Σ_{i<j} a_i √N_i)` at index `j` it returns `(N_{j+1}, Σ_{i<j+1} a_i √N_i)` with
`N_{j+1} = ⌈max{16 N_j, (100π s/a_{j+1})², (1000 a_{j+1} √N_j/a_j)²}⌉₊ + 1`,
`s = q.2 + a_j √N_j`. -/
def e2_lacunaryStep (a : ℕ → ℝ) (j : ℕ) (q : ℕ × ℝ) : ℕ × ℝ :=
  (Nat.ceil (max (16 * (q.1 : ℝ))
      (max ((100 * Real.pi * (q.2 + a j * Real.sqrt (q.1 : ℝ)) / a (j + 1)) ^ 2)
        ((1000 * a (j + 1) * Real.sqrt (q.1 : ℝ) / a j) ^ 2))) + 1,
    q.2 + a j * Real.sqrt (q.1 : ℝ))

/-- The recursion state `(N_j, Σ_{i<j} a_i √N_i)`, starting from `(1, 0)`. -/
def e2_lacunaryState (a : ℕ → ℝ) : ℕ → ℕ × ℝ
  | 0 => (1, 0)
  | j + 1 => e2_lacunaryStep a j (e2_lacunaryState a j)

/-- The constructed frequencies `N_j = (e2_lacunaryState a j).1`. -/
def e2_lacunaryFrequency (a : ℕ → ℝ) (j : ℕ) : ℕ :=
  (e2_lacunaryState a j).1

/-! ## Statements for the frequency recursion -/

/-- **One-step inequalities.** For positive amplitudes, a state with
`0 < N_j` and nonnegative partial sum `q.2` yields `N_{j+1} > 0`, `16 N_j ≤ N_{j+1}`, the
low-frequency bound `π/√N_{j+1} · s ≤ a_{j+1}/100` with `s = (e2_lacunaryStep a j q).2`, and the
amplitude-decay bound `a_{j+1}/√N_{j+1} ≤ a_j/(1000 √N_j)`. -/
def E2LacunaryStepStatement : Prop :=
  ∀ a : ℕ → ℝ, (∀ j, 0 < a j) → ∀ (j : ℕ) (q : ℕ × ℝ), 0 < q.1 → 0 ≤ q.2 →
    0 < (e2_lacunaryStep a j q).1 ∧
    16 * q.1 ≤ (e2_lacunaryStep a j q).1 ∧
    Real.pi / Real.sqrt ((e2_lacunaryStep a j q).1 : ℝ) * (e2_lacunaryStep a j q).2 ≤
      a (j + 1) / 100 ∧
    a (j + 1) / Real.sqrt ((e2_lacunaryStep a j q).1 : ℝ) ≤
      a j / (1000 * Real.sqrt (q.1 : ℝ))

/-- **State invariant and assembly.** Given the one-step inequalities,
the constructed frequencies satisfy every field of `IsLacunaryData` for amplitudes
`0 < a_j ≤ 1`. -/
def E2LacunaryAssemblyStatement : Prop :=
  E2LacunaryStepStatement →
    ∀ a : ℕ → ℝ, (∀ j, 0 < a j) → (∀ j, a j ≤ 1) → IsLacunaryData a (e2_lacunaryFrequency a)

/-! ## Statements for the series -/

/-- **Weighted geometric majorant and tails.** Under
`IsLacunaryData a N`, the weights `w_j = a_j/√N_j` are positive, `w_{j+1} ≤ w_j/1000`,
`w_j ≤ w_0 · 1000^{-j}`, `Σ w_j` converges, and `Σ_{i>j} w_i ≤ w_j/999`. The tail
bound is also the weighted-tail input of `lacunaryGraphMap_mem_ball_of_quarter`. -/
def E2LacunaryWeightStatement : Prop :=
  ∀ (a : ℕ → ℝ) (N : ℕ → ℕ), IsLacunaryData a N →
    (∀ j, 0 < a j / Real.sqrt (N j)) ∧
    (∀ j, a (j + 1) / Real.sqrt (N (j + 1)) ≤ a j / Real.sqrt (N j) / 1000) ∧
    (∀ j, a j / Real.sqrt (N j) ≤ a 0 / Real.sqrt (N 0) * (1 / 1000) ^ j) ∧
    Summable (fun j => a j / Real.sqrt (N j)) ∧
    (∀ j, ∑' i, a (j + 1 + i) / Real.sqrt (N (j + 1 + i)) ≤ a j / Real.sqrt (N j) / 999)

/-- **Weierstrass M-test.** For every `ε` and every summable
nonnegative weight sequence `a_j/√N_j`, the cosine series is absolutely summable at every `t`
and `ε` times its partial sums converge uniformly on `ℝ` to `lacunaryFunction ε a N`. The two
conclusions are those of `LacunaryConvergenceStatement`. -/
def E2LacunaryWeierstrassStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), (∀ j, 0 ≤ a j / Real.sqrt (N j)) →
    Summable (fun j => a j / Real.sqrt (N j)) →
    (∀ t : ℝ, Summable fun j => |a j / Real.sqrt (N j) * Real.cos (N j * t)|) ∧
    TendstoUniformly
      (fun (M : ℕ) (t : ℝ) =>
        ε * ∑ j ∈ Finset.range M, a j / Real.sqrt (N j) * Real.cos (N j * t))
      (lacunaryFunction ε a N) atTop

/-! ## Amplitude sequences -/

/-- **Nonregular amplitude admissibility.** `0 < a_j ≤ 1` for
`a_j = (j+1)^{-1/2}`. -/
def E2NonregularAmplitudeStatement : Prop :=
  ∀ j : ℕ, 0 < nonregularAmplitude j ∧ nonregularAmplitude j ≤ 1

/-- **Exponent amplitude admissibility.** For `c₀ > 0` the amplitudes
`a_j = c₀/(√(j+1) log(j+2))` are positive, and they are all at most `1`
exactly when `c₀ ≤ log 2` (`a_0 = c₀/log 2` is the largest). In particular `c₀ = 1` is not
admissible and `c₀ = log 2 / 2` is. -/
def E2ExponentAmplitudeStatement : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ →
    (∀ j, 0 < exponentAmplitude c₀ j) ∧ ((∀ j, exponentAmplitude c₀ j ≤ 1) ↔ c₀ ≤ Real.log 2)

end ParabolicRectifiability.Examples
