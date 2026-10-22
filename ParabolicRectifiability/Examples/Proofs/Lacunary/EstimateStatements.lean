import ParabolicRectifiability.Examples.Statements.Lacunary

/-! # Named statements of the lacunary estimates

Definitions and proposition definitions only; the proofs are given separately.

Targets (namespace `ParabolicRectifiability.Examples`):
* `lacunary_estimates_bundle : LacunaryEstimatesStatement`;
* `lacunarySource_finite_innerRegular_ac`;
* `exists_restriction_carried_by_graph`;
* `lacunaryGraphMap_mem_ball_of_quarter`;
* `lintegral_energyT_quarter_pos`.

Indexing: Lean indices are the informal indices minus one.
Notation: `f = lacunaryFunction ε a N`, `F = lacunaryGraphMap ε a N`, `ν_E = lacunarySource ε a N E`,
`J = lacunaryInterval`, `w_j = a_j/√N_j`, `b_j = N_j^{-1/2}`, `K_b(r) = min(r/b, b/r)`,
`r_j = √(π/N_j)`, `W_j(t) = (t - π/N_j, t + π/N_j)`.

The statements `E2LacunaryWeightStatement` and `E2StationaryLengthStatement` are consumed as
hypotheses (never restated); they occur only in the types of the proofs.

Each conjunct of `LacunaryEstimatesStatement` is proved from the following groups of statements:
* modulus and isometry: `E2InvSqrtDecayStatement`, `E2KernelSumStatement`,
  `E2KernelBoundStatement`, then `LacunaryIsometryStatement`;
* ball pullback: `E2BallPullbackStatement` (the ball identity follows);
* Hausdorff identity: `E2TimeHausdorffStatement`, `E2HausdorffExactStatement`
  (`c_H = 1` for the unnormalized `hausdorffP`);
* density limit (one statement);
* full interval (one statement over `E2StationaryLengthStatement`);
* upper energy: `E2TestBoundStatement`, `E2KernelJensenStatement`,
  `E2KernelLogIntegralStatement`;
* plateau and lower energy: `E2PlateauErrorStatement`, `E2CosPlateauStatement`,
  `E2PlateauLowerStatement`, `E2PlateauBetaStatement`, `E2BandStatement`,
  `E2OccupancyStatement`, `E2LowerEnergyFirstStatement`, `E2InteriorDensityPointStatement`;
* small slopes: `E2LittleHolderStatement`, `E2SnowflakeExtensionStatement`.

`E2QuarterEnergyLowerStatement` is used for the positive-energy statement.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-! ## Definitions -/

/-- `b_j = N_j^{-1/2}`. -/
abbrev e2_invSqrtFreq (N : ℕ → ℕ) (j : ℕ) : ℝ := (Real.sqrt (N j : ℝ))⁻¹

/-- The scale kernel `K_b(r) = min(r/b, b/r)` (equal to `e^{-|log r - log b|}` for
`r, b > 0`). -/
def e2_kernelAt (b r : ℝ) : ℝ := min (r / b) (b / r)

/-- The amplitude-weighted kernel sum `Σ_j a_j K_{b_j}(r)` of the modulus bound. -/
def e2_lacunaryKernelSum (a : ℕ → ℝ) (N : ℕ → ℕ) (r : ℝ) : ℝ :=
  ∑' j, a j * e2_kernelAt (e2_invSqrtFreq N j) r

/-- The plateau centre `c_{j,t} = ε Σ_{i<j} a_i N_i^{-1/2} cos(N_i t)`. -/
def e2_plateauCenter (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (t : ℝ) : ℝ :=
  ε * ∑ i ∈ Finset.range j, a i / Real.sqrt (N i) * Real.cos (N i * t)

/-- The open period window `W_j(t) = (t - π/N_j, t + π/N_j)`: the interior of `I_j(t)`, and exactly the time pullback of the ball `P(F(t), r_j)`. -/
def e2_periodWindow (N : ℕ → ℕ) (j : ℕ) (t : ℝ) : Set ℝ :=
  Ioo (t - Real.pi / N j) (t + Real.pi / N j)

/-- The plateau radius `r_j = √(π/N_j)`. -/
def e2_plateauRadius (N : ℕ → ℕ) (j : ℕ) : ℝ := Real.sqrt (Real.pi / N j)

/-! ## Modulus and isometry -/

/-- **Reciprocal-frequency decay.** Under
`IsLacunaryData a N`, `b_{j+1} ≤ b_j/4` (from `N_{j+1} ≥ 16 N_j`). -/
def E2InvSqrtDecayStatement : Prop :=
  ∀ (a : ℕ → ℝ) (N : ℕ → ℕ), IsLacunaryData a N →
    ∀ j : ℕ, (Real.sqrt (N (j + 1) : ℝ))⁻¹ ≤ (Real.sqrt (N j : ℝ))⁻¹ / 4

/-- **Lacunary kernel sum.** For positive `b_j` with `b_{j+1} ≤ b_j/4` and every
`r > 0`, the kernels `K_{b_j}(r)` are summable with sum at most `8/3`. A pure
real-sequence fact. -/
def E2KernelSumStatement : Prop :=
  ∀ b : ℕ → ℝ, (∀ j, 0 < b j) → (∀ j, b (j + 1) ≤ b j / 4) → ∀ r : ℝ, 0 < r →
    Summable (fun j => e2_kernelAt (b j) r) ∧ ∑' j, e2_kernelAt (b j) r ≤ 8 / 3

/-- **Modulus kernel bound.** For `ε ≥ 0`, lacunary data,
`r > 0` and `|t - s| ≤ r²`: the weighted kernels are summable and
`|f(t) - f(s)| ≤ 2 ε r Σ_j a_j K_{b_j}(r)`. -/
def E2KernelBoundStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 ≤ ε → IsLacunaryData a N →
    ∀ t s r : ℝ, 0 < r → |t - s| ≤ r ^ 2 →
      Summable (fun j => a j * e2_kernelAt (e2_invSqrtFreq N j) r) ∧
        |lacunaryFunction ε a N t - lacunaryFunction ε a N s| ≤
          2 * ε * r * e2_lacunaryKernelSum a N r

/-! ## Ball pullback -/

/-- **Ball pullback.** Under the standing hypotheses, for every set `E ⊆ ℝ`, every
`t`, every `r > 0` and every measurable `g ≥ 0` on `Space 1`,
`∫_{P(F(t),r)} g dν_E = ∫_{E ∩ (t-r², t+r²)} g(F(s)) ds`. With `g = 1` this is the exact ball
identity. -/
def E2BallPullbackStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ (E : Set ℝ) (t r : ℝ), 0 < r → ∀ g : Space 1 → ℝ≥0∞, Measurable g →
      ∫⁻ w in Metric.ball (lacunaryGraphMap ε a N t) r, g w ∂(lacunarySource ε a N E) =
        ∫⁻ s in E ∩ Ioo (t - r ^ 2) (t + r ^ 2), g (lacunaryGraphMap ε a N s)

/-! ## Hausdorff identity -/

/-- **Snowflake Hausdorff measure.** On `Time` (the snowflake `(ℝ, √|t-s|)`), the
unnormalized two-dimensional Hausdorff measure of the copy of any `E ⊆ ℝ` is its Lebesgue outer
measure: `μH[2](E) = |E|` (the square of the diameter of a set is its ordinary
Euclidean diameter). -/
def E2TimeHausdorffStatement : Prop :=
  ∀ E : Set ℝ, (Measure.hausdorffMeasure (2 : ℝ) : Measure Time)
      ((Metric.Snowflaking.toSnowflaking : ℝ ≃ Time) '' E) = volume E

/-- **Exact Hausdorff identity.** Under the standing hypotheses,
`H_P²(F(E)) = |E|` for every `E ⊆ ℝ` (with `c_H = 1` for the unnormalized `hausdorffP`). -/
def E2HausdorffExactStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E : Set ℝ, hausdorffP 1 2 (lacunaryGraphMap ε a N '' E) = volume E

/-! ## All-scale upper energy -/

/-- **Single-scale test bound.** Testing the vertical line through `F(t)`:
`B_q(F(t), r) ≤ 2^{q+1} ε^q (Σ_j a_j K_{b_j}(r))^q` for every `E ⊆ ℝ`, `t`, `r > 0`, `q > 0`. -/
def E2TestBoundStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ (E : Set ℝ) (t r q : ℝ), 0 < r → 0 < q →
      betaPow (lacunarySource ε a N E) 2 .mixed q (lacunaryGraphMap ε a N t) r ≤
        ENNReal.ofReal (2 ^ (q + 1) * ε ^ q * e2_lacunaryKernelSum a N r ^ q)

/-- **Weighted Jensen for kernel sums.** For `q ≥ 1`, `0 ≤ x_j ≤ 1`, `K_j ≥ 0`
summable with `Σ K_j ≤ M`: `x K` and `x^q K` are summable and
`(Σ x_j K_j)^q ≤ M^{q-1} Σ x_j^q K_j`. A pure real-sequence fact. -/
def E2KernelJensenStatement : Prop :=
  ∀ q : ℝ, 1 ≤ q → ∀ (x K : ℕ → ℝ) (M : ℝ), (∀ j, 0 ≤ x j) → (∀ j, x j ≤ 1) →
    (∀ j, 0 ≤ K j) → Summable K → ∑' j, K j ≤ M →
      Summable (fun j => x j * K j) ∧ Summable (fun j => x j ^ q * K j) ∧
        (∑' j, x j * K j) ^ q ≤ M ^ (q - 1) * ∑' j, x j ^ q * K j

/-- **Logarithmic kernel integral.** `∫_0^∞ K_b(r) dr/r = 2` for every `b > 0`. -/
def E2KernelLogIntegralStatement : Prop :=
  ∀ b : ℝ, 0 < b → ∫⁻ r in Ioi 0, ENNReal.ofReal (e2_kernelAt b r) ∂scaleMeasure = 2

/-! ## Plateaus and restriction-stable lower energy -/

/-- **Plateau decomposition.** For `ε ≥ 0`, lacunary data, every `j`, `t`, and
`|s - t| ≤ π/N_j`: `|f(s) - c_{j,t} - ε w_j cos(N_j s)| ≤ ε w_j/50`. -/
def E2PlateauErrorStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 ≤ ε → IsLacunaryData a N →
    ∀ (j : ℕ) (t s : ℝ), |s - t| ≤ Real.pi / N j →
      |lacunaryFunction ε a N s - e2_plateauCenter ε a N j t -
          ε * (a j / Real.sqrt (N j)) * Real.cos (N j * s)| ≤
        ε * (a j / Real.sqrt (N j)) / 50

/-- **Cosine plateaus over one period.** For `ω > 0` and every `t`, each of the
sets `{cos(ω s) ≥ 1/2}` and `{cos(ω s) ≤ -1/2}` meets the open period window
`(t - π/ω, t + π/ω)` in measure at least a third of its length `2π/ω` (independently
of phase). -/
def E2CosPlateauStatement : Prop :=
  ∀ ω : ℝ, 0 < ω → ∀ t : ℝ,
    ENNReal.ofReal (2 * Real.pi / (3 * ω)) ≤
        volume ({s : ℝ | 1 / 2 ≤ Real.cos (ω * s)} ∩ Ioo (t - Real.pi / ω) (t + Real.pi / ω)) ∧
      ENNReal.ofReal (2 * Real.pi / (3 * ω)) ≤
        volume ({s : ℝ | Real.cos (ω * s) ≤ -(1 / 2)} ∩ Ioo (t - Real.pi / ω) (t + Real.pi / ω))

/-- **Plateaus survive measurable deletion.** For `ε ≥ 0`, lacunary
data and a Lebesgue measurable `E` with `|E ∩ W_j(t)| ≥ (11/12)|W_j(t)|`: for every `q > 0` and
every fitting constant `c`,
`∫_{E ∩ W_j(t)} |f(s) - c|^q ds ≥ (|W_j(t)|/4) (12 ε w_j/25)^q`, with `|W_j(t)|/4 = π/(2N_j)`. -/
def E2PlateauLowerStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 ≤ ε → IsLacunaryData a N →
    ∀ E : Set ℝ, NullMeasurableSet E volume → ∀ (j : ℕ) (t : ℝ),
      ENNReal.ofReal (11 / 12 * (2 * Real.pi / N j)) ≤ volume (E ∩ e2_periodWindow N j t) →
      ∀ q : ℝ, 0 < q → ∀ c : ℝ,
        ENNReal.ofReal (Real.pi / (2 * N j) * (12 / 25 * (ε * (a j / Real.sqrt (N j)))) ^ q) ≤
          ∫⁻ s in E ∩ e2_periodWindow N j t, ENNReal.ofReal (|lacunaryFunction ε a N s - c| ^ q)

/-- **Beta lower bound at the plateau radius.** Under the standing hypotheses,
for a Lebesgue measurable `E` with `|E ∩ W_j(t)| ≥ (11/12)|W_j(t)|` and every `q > 0`:
`B_{q,ν_E}(F(t), r_j) ≥ (1/2) π^{-q/2} (12/25)^q ε^q a_j^q`. -/
def E2PlateauBetaStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E : Set ℝ, NullMeasurableSet E volume → ∀ (j : ℕ) (t : ℝ),
      ENNReal.ofReal (11 / 12 * (2 * Real.pi / N j)) ≤ volume (E ∩ e2_periodWindow N j t) →
      ∀ q : ℝ, 0 < q →
        ENNReal.ofReal (1 / 2 * Real.pi ^ (-(q / 2)) * (12 / 25) ^ q * ε ^ q * a j ^ q) ≤
          betaPow (lacunarySource ε a N E) 2 .mixed q (lacunaryGraphMap ε a N t)
            (e2_plateauRadius N j)

/-- **One logarithmic band.** For every source, family, `q ≥ 0`, centre and
`ρ > 0`: `∫_{[ρ,2ρ]} B_q(z,r) dr/r ≥ log 2 · 2^{-(k+q)} B_q(z,ρ)` (the unnormalized
fitting infimum is nondecreasing in the radius). -/
def E2BandStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (q : ℝ), 0 ≤ q →
    ∀ (z : Space n) (ρ : ℝ), 0 < ρ →
      ENNReal.ofReal (Real.log 2) * ((2 : ℝ≥0∞) ^ ((k : ℝ) + q))⁻¹ * betaPow μ k T q z ρ ≤
        ∫⁻ r in Icc ρ (2 * ρ), betaPow μ k T q z r ∂scaleMeasure

/-- **Eventual occupancy.** For lacunary data, at a Lebesgue density point `t` of
`E` and for every `R > 0`, there is `j₀` such that every `j ≥ j₀` has
`|E ∩ W_j(t)| ≥ (11/12)|W_j(t)|` and `2 r_j < R`. `j₀` does not depend on any
exponent. -/
def E2OccupancyStatement : Prop :=
  ∀ (a : ℕ → ℝ) (N : ℕ → ℕ), IsLacunaryData a N →
    ∀ (E : Set ℝ) (t : ℝ), IsLebesgueDensityPoint E t → ∀ R : ℝ, 0 < R →
      ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
        ENNReal.ofReal (11 / 12 * (2 * Real.pi / N j)) ≤ volume (E ∩ e2_periodWindow N j t) ∧
          2 * e2_plateauRadius N j < R

/-- **Lower energy, first clause.** The first clause of
`LacunaryLowerEnergyStatement`, with its coefficient function chosen first. -/
def E2LowerEnergyFirstStatement : Prop :=
  ∃ c : ℝ → ℝ, (∀ q : ℝ, 0 < q → 0 < c q) ∧
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
      ∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ lacunaryInterval →
        ∀ t ∈ E ∩ Ioo (-1 : ℝ) 1, IsLebesgueDensityPoint E t →
        ∀ R : ℝ, 0 < R → ∃ j₀ : ℕ, ∀ q : ℝ, 0 < q →
          ENNReal.ofReal (c q * ε ^ q) * ∑' j, ENNReal.ofReal (a (j + j₀) ^ q) ≤
            energyT (lacunarySource ε a N E) 2 .mixed q R (lacunaryGraphMap ε a N t)

/-- **Interior density points of `J`.** Every `t ∈ (-1,1)` is a Lebesgue density
point of `J = [-1,1]` (for `E = J` this holds at every interior point). -/
def E2InteriorDensityPointStatement : Prop :=
  ∀ t ∈ Ioo (-1 : ℝ) 1, IsLebesgueDensityPoint lacunaryInterval t

/-! ## Small slopes -/

/-- **Little half-Hölder modulus.** For `ε ≥ 0`, lacunary data and `a_j → 0`:
for every `η > 0` there is `h > 0` with `|f(t) - f(s)| ≤ η √|t-s|` whenever `|t - s| ≤ h`. -/
def E2LittleHolderStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 ≤ ε → IsLacunaryData a N → Tendsto a atTop (𝓝 0) →
    ∀ η : ℝ, 0 < η → ∃ h : ℝ, 0 < h ∧ ∀ t s : ℝ, |t - s| ≤ h →
      |lacunaryFunction ε a N t - lacunaryFunction ε a N s| ≤ η * Real.sqrt |t - s|

/-- **Snowflake extension to a full ordinary vertical graph.** For `η > 0`, a set
`A ⊆ ℝ` and `g` with `|g(t) - g(s)| ≤ η √|t-s|` on `A`, some full ordinary vertical graph of
slope at most `η` (rank zero, `n = 1`, `k = 2`) contains `{(g(t), t) : t ∈ A}` (scalar McShane extension in the snowflake
metric). -/
def E2SnowflakeExtensionStatement : Prop :=
  ∀ η : ℝ, 0 < η → ∀ (A : Set ℝ) (g : ℝ → ℝ),
    (∀ t ∈ A, ∀ s ∈ A, |g t - g s| ≤ η * Real.sqrt |t - s|) →
    ∃ G : OrdinaryVerticalGraph 1 2 η,
      (fun t : ℝ => (point (EuclideanSpace.single (0 : Fin 1) (g t)) t : Space 1)) '' A ⊆
        G.image

/-! ## The quarter-interval energy -/

/-- **Uniform energy lower bound on `F([-1/8,1/8])`.** For `p > 0` and the
standing hypotheses, with `ν = ν_{[-1/4,1/4]}`, some `b > 0` satisfies `T²_{p,ν}(F(t)) ≥ b` for
every `t ∈ [-1/8,1/8]`. -/
def E2QuarterEnergyLowerStatement : Prop :=
  ∀ p : ℝ, 0 < p → ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 →
    IsLacunaryData a N → ∃ b : ℝ, 0 < b ∧ ∀ t ∈ Icc (-1 / 8 : ℝ) (1 / 8),
      ENNReal.ofReal b ≤
        energyT (lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) 2 .mixed p 2
          (lacunaryGraphMap ε a N t)

end ParabolicRectifiability.Examples
