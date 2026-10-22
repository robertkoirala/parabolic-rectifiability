import ParabolicRectifiability.Geometry.SubspaceCoordinates

/-! # The lacunary primitive

The construction lives in `n = 1`, `k = 2` (`Space 1`, whose spatial factor is
`EuclideanSpace ℝ (Fin 1)`). For a fixed amplitude `0 < ε ≤ 3/16` (a hypothesis of every
statement, not of the definitions), amplitudes `0 < a_j ≤ 1` and integer frequencies `N_j`
with the three growth conditions recorded in `IsLacunaryData`,
```
f(t) = ε Σ_j a_j N_j^{-1/2} cos(N_j t),   F(t) = (f(t), t),   J = [-1,1],
ν_E = F_#(L¹⌊E).
```

**Indexing.** Mathematically, amplitudes and frequencies are indexed by `j ≥ 1`. Here they
are sequences on `ℕ`, and the Lean index `j` is the mathematical index `j + 1`. Thus the
sum over `i < j` is `Finset.range j`, and the two specific amplitude sequences
(`nonregularAmplitude`, `exponentAmplitude`) are written with `j + 1` (and `log (j + 2)`) in
place of `j` (and `log (j + 1)`).

**Frequencies.** Each `N_j` is a natural number with `0 < N_j` (positive integers;
`N_j^{-1/2}` occurs in every formula). Positivity is part of `IsLacunaryData`.

**The series.** `f` is a `tsum`. Under `IsLacunaryData` the series converges absolutely and
uniformly; no convergence fact is used by the definitions themselves. The convergence is
the separate specification `LacunaryConvergenceStatement` below (a conclusion, not a
hypothesis), proved by `lacunary_convergence`.

**The source.** `ν_E` is the pushforward of Lebesgue measure restricted to `E`. One takes
Lebesgue measurable `E ⊆ J` with Borel representatives modulo null sets;
`volume.restrict E` depends only on the null class of `E`, so the
definition needs no representative. Statements assume `NullMeasurableSet E volume` and
`E ⊆ J`.

The file also fixes three small auxiliary objects used by the statements: the Lebesgue
density point predicate, the two amplitude sequences of the examples, and the identification
of a real function of time with a normal-valued function on the zero vertical base
`{0} × ℝ` of `ℝ¹ × ℝ`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

/-- The standing amplitude and frequency hypotheses of the lacunary construction, with the
Lean index `j` standing for the mathematical index `j + 1`:
`0 < a_j ≤ 1`, positive integer frequencies, and
`N_{j+1} ≥ 16 N_j`,
`(π / √N_j) Σ_{i<j} a_i √N_i ≤ a_j / 100`,
`a_{j+1} / √N_{j+1} ≤ a_j / (1000 √N_j)`. -/
structure IsLacunaryData (a : ℕ → ℝ) (N : ℕ → ℕ) : Prop where
  amplitude_pos : ∀ j, 0 < a j
  amplitude_le_one : ∀ j, a j ≤ 1
  frequency_pos : ∀ j, 0 < N j
  frequency_growth : ∀ j, 16 * N j ≤ N (j + 1)
  low_frequency : ∀ j,
    Real.pi / Real.sqrt (N j) * ∑ i ∈ Finset.range j, a i * Real.sqrt (N i) ≤ a j / 100
  amplitude_decay : ∀ j,
    a (j + 1) / Real.sqrt (N (j + 1)) ≤ a j / (1000 * Real.sqrt (N j))

/-- The lacunary function `f(t) = ε Σ_j a_j N_j^{-1/2} cos(N_j t)`,
as a `tsum`. -/
def lacunaryFunction (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (t : ℝ) : ℝ :=
  ε * ∑' j, a j / Real.sqrt (N j) * Real.cos (N j * t)

/-- Convergence of the lacunary primitive series. Under the standing hypotheses
`0 < ε ≤ 3/16` and `IsLacunaryData a N`, at every `t ∈ ℝ` the series
`Σ_j a_j N_j^{-1/2} cos(N_j t)` is absolutely summable, and the finite partial sums
`ε Σ_{j<M} a_j N_j^{-1/2} cos(N_j t)` converge to `lacunaryFunction ε a N` uniformly on `ℝ` as
`M → ∞`. This is a proposition; `lacunary_convergence` proves it. -/
def LacunaryConvergenceStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    (∀ t : ℝ, Summable fun j => |a j / Real.sqrt (N j) * Real.cos (N j * t)|) ∧
    TendstoUniformly
      (fun (M : ℕ) (t : ℝ) =>
        ε * ∑ j ∈ Finset.range M, a j / Real.sqrt (N j) * Real.cos (N j * t))
      (lacunaryFunction ε a N) atTop

/-- The graph map `F(t) = (f(t), t) ∈ Space 1`. The spatial coordinate is
`f(t)` in the single coordinate of `ℝ¹`. -/
def lacunaryGraphMap (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (t : ℝ) : Space 1 :=
  point (EuclideanSpace.single 0 (lacunaryFunction ε a N t)) t

/-- The parameter interval `J = [-1,1]`. -/
def lacunaryInterval : Set ℝ := Icc (-1) 1

/-- The restricted graph source `ν_E = F_#(L¹⌊E)`. -/
def lacunarySource (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (E : Set ℝ) : Measure (Space 1) :=
  Measure.map (lacunaryGraphMap ε a N) (volume.restrict E)

/-- `t` is a Lebesgue density point of `E ⊆ ℝ`: `|E ∩ [t-r,t+r]| / |[t-r,t+r]| → 1` as
`r ↓ 0`. This is the form of `Besicovitch.ae_tendsto_measure_inter_div`. -/
def IsLebesgueDensityPoint (E : Set ℝ) (t : ℝ) : Prop :=
  Tendsto (fun r => volume (E ∩ Metric.closedBall t r) / volume (Metric.closedBall t r))
    (𝓝[>] (0 : ℝ)) (𝓝 1)

/-- The amplitudes `a_j = j^{-1/2}` of the nonregular lacunary example, in the
Lean index: `a j = (j + 1)^{-1/2}`. -/
def nonregularAmplitude (j : ℕ) : ℝ := (Real.sqrt ((j : ℝ) + 1))⁻¹

/-- The amplitudes `a_j = c₀ / (√j log(j+1))` of the exponent witness
below `p = 2`, in the Lean index: `a j = c₀ / (√(j+1) log(j+2))`. -/
def exponentAmplitude (c₀ : ℝ) (j : ℕ) : ℝ :=
  c₀ / (Real.sqrt ((j : ℝ) + 1) * Real.log ((j : ℝ) + 2))

/-- The zero spatial subspace of `ℝ¹`: the direction of every vertical model and full vertical
graph at `n = 1`, `k = 2` (spatial rank zero). -/
abbrev zeroDirection : Submodule ℝ (Spatial 1) := ⊥

/-- A real function `h` of time, read as the normal-valued function
`(0, t) ↦ h(t) e₁` on the vertical base `zeroDirection × ℝ`, with values in
`zeroDirectionᗮ = ℝ¹`. With `h = f` this is the full vertical function whose graph
`{(0 + 0 + f(t), t)}` is `F(ℝ)`. -/
def zeroBaseLift (h : ℝ → ℝ) : SubspaceSpace zeroDirection → zeroDirectionᗮ := fun p =>
  ⟨EuclideanSpace.single 0 (h p.2.val), by
    rw [Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top⟩

end ParabolicRectifiability.Examples
