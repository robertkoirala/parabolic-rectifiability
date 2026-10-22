import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.TailTruncation
import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.RestrictionLowerDensity
import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.FivefoldDensitySelection
import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.SupportCover
import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.MissedMass
import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.AmbientZeroGraph
import ParabolicRectifiability.Characterization.Proofs.Fivefold
import ParabolicRectifiability.Foundations.Proofs.AmbientCover
import ParabolicRectifiability.Enhancements.Theorems.ScaledCore
import ParabolicRectifiability.Measure.ScaleEnergy
import ParabolicRectifiability.Metric.Hausdorff
import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import ParabolicRectifiability.Enhancements.Statements.ScaledCore
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # The finite-Hausdorff criterion: intermediate statements

Intermediate statements for `FiniteHausdorffCriterionStatement`, which is proved in
`b4_finite_hausdorff_criterion`. Each delegates to its proof module.

Proof outline. The non-ambient branch uses the core form
`ScaledRectifiableReifenbergCoreStatement`, not `ScaledRectifiableReifenbergStatement`: fix the
graph tolerance `ε > 0` and an error `e > 0`; the finite tail gives `s > 0` and a Borel
`F ⊆ E` with `S^s_η ≤ e` on `F` and `η(E \ F) < e`; for `ν = H_P^k⌊F`, `S^s_ν ≤ e` on `F` by
source domination; at `ν`-a.e. point there are arbitrarily small `r` with
`ν(P(z,r)) ≥ c_k r^k`; select disjoint balls with `r_i < s/10` whose fivefold dilates cover
`ν`-almost all of `F`; apply the core property to the same full source `ν` at `a = z_i`,
`R = 5 r_i`, endpoint `10 r_i ≤ s`, threshold `M = e`, allowance `Γ = 0`; the actual supports
carry the retained measures and their `ε`-graph exceptions are `ν`-null because
`ν ≪ H_P^k`; the missed mass is at most `e + C_n e 5^k Σ r_i^k ≤ e + C_n 5^k c_k⁻¹ e η(E)`;
repeat for `e = 1/(j+1)` at fixed `ε`; the countable union misses zero Hausdorff measure.
The ambient branch (`k = n + 2`) uses `AmbientZeroGraphCoverStatement` directly; the second
conjunct (the zero-norm graph) is a separate statement, because the ambient cover statement
gives graphs of norm at most `ε` only for `ε > 0`.

Three statements are imported results (`b4_input_scaledRectifiableReifenbergCore`,
`b4_input_ambientZeroGraphCover`, `b4_input_fivefoldSelection`); six are specific to this
proof (`b4_tail_truncation`, `b4_hausdorff_restrict_ball_lower_bound`,
`b4_fivefold_density_selection`, `b4_cover_of_localCoreDecomposition`, `b4_missed_mass_bound`,
`b4_ambient_zero_norm_graph`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-! ## Imported results -/

/-- The scaled rectifiable Reifenberg core property `ScaledRectifiableReifenbergCoreStatement`, supplied by
`Enhancements.scaled_rectifiable_reifenberg_core`.

Use in `b4_cover_at_error`: only the second conjunct, at the given `n`, giving
`C > 0` with `ScaledThresholdCoreProperty n C`; that property is applied, for each selected
ball `j`, at `k`, the full restricted source `μ = ν = H_P^k⌊F`, centre `a = z_j`, radius
`R = 5 r_j`, the given family `T`, threshold `M = e` and allowance `Γ = 0`, with exceptional
mass `ν(P(z_j,5r_j) ∩ {S^{2·5r_j}_{ν,T} > e}) = 0` (endpoint `10 r_j < s`). The scaling
identities (first conjunct) are not used. -/
theorem b4_input_scaledRectifiableReifenbergCore : Enhancements.ScaledRectifiableReifenbergCoreStatement := by
  exact Enhancements.scaled_rectifiable_reifenberg_core

/-- The ambient graph cover `AmbientZeroGraphCoverStatement`, supplied by
`Foundations.ambient_zero_graph_cover_all_proof`.

Use in `b4_ambient_branch`: only the second conjunct, at the given `n` and the given
set `E`: `IsRegularlyRectifiableSet .vertical (n+2) E` for `T = .vertical` and
`IsRegularlyRectifiableSet .mixed (n+2) E` for `T = .mixed`. The first conjunct (graphs of norm
at most `ε > 0` with image `X`) is not used; it does not give the norm-zero graph of the
second conjunct of `FiniteHausdorffCriterionStatement` (see `b4_ambient_zero_norm_graph`). -/
theorem b4_input_ambientZeroGraphCover : AmbientZeroGraphCoverStatement := by
  exact Foundations.ambient_zero_graph_cover_all_proof

/-- The fivefold ball selection `FivefoldSelectionStatement`, supplied by
`Characterization.fivefold_ball_selection_proof`.

Use in `b4_cover_at_error`: passed unchanged as the first argument of
`b4_fivefold_density_selection`, which applies it once, with `X = Space n` and the ball
family of all good pairs. -/
theorem b4_input_fivefoldSelection : FivefoldSelectionStatement := by
  exact Characterization.fivefold_ball_selection_proof

/-! ## Intermediate statements -/

/-- **Finite-energy tail truncation.**

Let `E` be Borel with `H_P^k(E) < ∞`, `η = H_P^k⌊E`, `R > 0`, and suppose
`S^R_{η,T}(z) < ∞` for `η`-a.e. `z`. For every `e > 0` there are `s > 0` and a Borel `F ⊆ E`
with `S^s_{η,T}(z) ≤ e` at every `z ∈ F` and `H_P^k(E \ F) < e`. One may take
`F = E ∩ {S^s_η ≤ e}`. Any family `T` (for an unavailable family the hypothesis forces
`H_P^k(E) = 0`).

Proof sketch. For `z` with `S^R_η(z) < ∞`, `S^{s}_η(z) = ∫_{(0,s)} β²_η(z,r) dr/r` decreases to
`0` as `s ↓ 0` (continuity from above of the finite measure `β²_η(z,·) dr/r` on `(0,R)`).
Hence the Borel sets `B_j = E ∩ {S^{R/(j+1)}_η > e}` (`measurable_squareEnergy`, `η` is
finite hence finite on compacts) decrease to an `η`-null set; `η(E) < ∞` gives
`η(B_j) → 0`. Choose `j` with `η(B_j) < e`, `s = R/(j+1)`, `F = E ∩ {S^s_η ≤ e}`; then
`H_P^k(E \ F) = η(B_j)`. -/
theorem b4_tail_truncation :
    ∀ (n k : ℕ) (T : FamilyKind) (E : Set (Space n)), MeasurableSet E →
      hausdorffP n k E < ⊤ → ∀ R : ℝ, 0 < R →
      (∀ᵐ z ∂(hausdorffP n k).restrict E,
        squareEnergy ((hausdorffP n k).restrict E) k T R z < ⊤) →
      ∀ e : ℝ, 0 < e →
        ∃ s : ℝ, 0 < s ∧ ∃ F : Set (Space n), MeasurableSet F ∧ F ⊆ E ∧
          (∀ z ∈ F, squareEnergy ((hausdorffP n k).restrict E) k T s z ≤ ENNReal.ofReal e) ∧
          hausdorffP n k (E \ F) < ENNReal.ofReal e := by
  exact b4_tail_truncation_proof

/-- **Positive upper density of finite-Hausdorff restrictions.**

For `n ≥ 1` and `1 ≤ k ≤ n + 2` there is a constant `c > 0` (depending only on
`k`; chosen before `F`) such that for every Borel `F` with `H_P^k(F) < ∞` and
`ν = H_P^k⌊F`, at `ν`-a.e. `z` there are arbitrarily small radii `r > 0` with
`ν(P(z,r)) ≥ c r^k`. No lower-density-at-all-scales hypothesis.

Proof sketch. Fix `c' < 2^{-k-1}` and `c < c'`. Let
`A_j = {z ∈ F : ν(P(z,r)) ≤ c' r^k for all 0 < r < 1/j}`. Cover `A_j` by sets of diameter
`d_i < 1/(2j)` meeting `A_j`; each lies in the open ball of radius `2 d_i` about a point of
`A_j` (points: `ν({x}) = 0` by the bound), so `ν(A_j) ≤ c' 2^k Σ d_i^k`; taking the Hausdorff
infimum (Mathlib's unnormalized `diam^k` cost, which is `hausdorffP`) gives
`ν(A_j) ≤ c' 2^k H_P^k(A_j) = c' 2^k ν(A_j)` (`A_j ⊆ F`, `F` Borel), and
`ν(A_j) < ∞` forces `ν(A_j) = 0`. A point where the conclusion fails lies in `Fᶜ` or in some
`A_j`. Outer measures throughout; `A_j` need not be shown Borel. -/
theorem b4_hausdorff_restrict_ball_lower_bound :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∃ c : ℝ, 0 < c ∧ ∀ F : Set (Space n), MeasurableSet F → hausdorffP n k F < ⊤ →
        ∀ᵐ z ∂(hausdorffP n k).restrict F, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < δ ∧
          ENNReal.ofReal (c * r ^ k) ≤ (hausdorffP n k).restrict F (Metric.ball z r) := by
  exact b4_hausdorff_restrict_ball_lower_bound_proof

/-- **Fivefold selection of dense balls.**

Given `FivefoldSelectionStatement`, a measure `ν` on `X`, reals `c`, `s > 0`,
and the density property "at `ν`-a.e. `z`, arbitrarily small `r > 0` with
`ν(P(z,r)) ≥ c r^k`", there is a countable family, indexed by `J ⊆ ℕ`, of balls of `X`
`P(z_j, r_j)` with `0 < r_j`, `10 r_j < s`, pairwise disjoint, each with
`ν(P(z_j,r_j)) ≥ c r_j^k`, whose fivefold dilates `P(z_j, 5 r_j)` cover `ν`-almost all of
`X` (hence of `F` when `ν = H_P^k⌊F`).

Proof sketch (how the family and the null set come from `FivefoldSelectionStatement`). Let
`G` be the set of points satisfying the density property, so `ν(Gᶜ) = 0` (outer measure; no
measurability needed). Apply the statement once with the separable metric space
`X = Space n`, the index type `ι = {(z,r) : z ∈ G, 0 < r, 10 r < s, ν(P(z,r)) ≥ c r^k}`
(balls of `X`, not of `F`), centres `z`, radii `r`, bound `s`. It returns a countable
pairwise disjoint `J₀ ⊆ ι` with every centre `z i` in some `P(z_j, 5 r_j)`, `j ∈ J₀`. Every
`z ∈ G` is a centre of some `i ∈ ι` (take the density radius below `s/10`), so
`G ⊆ ⋃_{j ∈ J₀} P(z_j, 5 r_j)` and the complement of the union is `ν`-null. Reindex the
countable `J₀` by a subset `J ⊆ ℕ` (an injection into `ℕ`, as in
`exists_natSubset_reindex`).

`FivefoldSelectionStatement` is the first argument (implication form). -/
theorem b4_fivefold_density_selection :
    FivefoldSelectionStatement →
    ∀ (n k : ℕ) (ν : Measure (Space n)) (c s : ℝ), 0 < s →
      (∀ᵐ z ∂ν, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < δ ∧
        ENNReal.ofReal (c * r ^ k) ≤ ν (Metric.ball z r)) →
      ∃ (J : Set ℕ) (z : J → Space n) (r : J → ℝ), (∀ j, 0 < r j) ∧ (∀ j, 10 * r j < s) ∧
        (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) ∧
        (∀ j, ENNReal.ofReal (c * r j ^ k) ≤ ν (Metric.ball (z j) (r j))) ∧
        ν (⋃ j, Metric.ball (z j) (5 * r j))ᶜ = 0 := by
  exact b4_fivefold_density_selection_proof

/-- **The actual supports carry the retained measures.**

Let `μ ≪ H_P^k` and let `E_H, E_V` form a scaled core decomposition
`IsLocalCoreDecomposition k T C a R μ E_H E_V`. For every `ε > 0` there is a set
`U` with a typed graph cover of type `T` at tolerance `ε` (modulo `H_P^k`) such that the part
of `P(a,R)` it misses has `μ`-measure at most the remainder mass:
`μ(P(a,R) \ U) ≤ μ⌊(E_H ∪ E_V)ᶜ (P(a,R))`.

Proof sketch. With `K_H = supp(μ⌊E_H)`, `K_V = supp(μ⌊E_V)`, the field `supports` gives
`H_P^k`-covers `U_H` of `K_H` (horizontal, slope `≤ ε`) and `U_V` of `K_V` (general regular
vertical, norm `≤ ε`). Take `U = U_H ∪ U_V` for `T = mixed`, `U = U_H` for `T = horizontal`
(`μ⌊E_V = 0` by `horizontal_only`), `U = U_V` for `T = vertical` (`μ⌊E_H = 0` by
`vertical_only`). Then `P(a,R) \ U ⊆ (P(a,R) ∩ (E_H ∪ E_V)ᶜ) ∪ (E_H \ U) ∪ (E_V \ U)`;
`μ(E_H \ K_H) = (μ⌊E_H)(K_Hᶜ) = 0` (Mathlib `Measure.measure_compl_support`, `Space n` is
second countable) and `μ(K_H \ U_H) = 0` from `H_P^k(K_H \ U_H) = 0` and `μ ≪ H_P^k`;
likewise for `E_V`; `μ(P(a,R) ∩ (E_H ∪ E_V)ᶜ) = μ⌊(E_H ∪ E_V)ᶜ (P(a,R))` (`P(a,R)` open).
No measurability of graph images is used. -/
theorem b4_cover_of_localCoreDecomposition :
    ∀ (n k : ℕ) (T : FamilyKind) (C : ℝ) (a : Space n) (R : ℝ) (μ : Measure (Space n))
      (EH EV : Set (Space n)), μ ≪ hausdorffP n k →
      Enhancements.IsLocalCoreDecomposition k T C a R μ EH EV →
      ∀ ε : ℝ, 0 < ε → ∃ U : Set (Space n), HasTypedGraphCover T k U ε ∧
        μ (Metric.ball a R \ U) ≤ μ.restrict (EH ∪ EV)ᶜ (Metric.ball a R) := by
  exact b4_cover_of_localCoreDecomposition_proof

/-- **The missed-mass bound at one error level.**

Let `F ⊆ E` be Borel, `ν = H_P^k⌊F`, `0 ≤ C`, `0 < c`, `0 ≤ e`, and
`H_P^k(E \ F) ≤ e`. Let `(P(z_j, r_j))_{j ∈ J}`, `J ⊆ ℕ`, be pairwise disjoint balls with
`r_j > 0` and `ν(P(z_j,r_j)) ≥ c r_j^k`, whose fivefold dilates cover `ν`-almost everything,
and let `U_j` be sets with `ν(P(z_j,5r_j) \ U_j) ≤ C e (5 r_j)^k`. Then
`H_P^k(E \ ⋃_j U_j) ≤ e (1 + (C 5^k / c) H_P^k(E))`.

Exact chain (constants visible):
`H_P^k(E \ ⋃U) ≤ H_P^k(E \ F) + ν(F \ ⋃U)`,
`ν(F \ ⋃U) ≤ ν((⋃_j P(z_j,5r_j))ᶜ) + Σ_j ν(P(z_j,5r_j) \ U_j) ≤ 0 + C e 5^k Σ_j r_j^k`,
`c Σ_j r_j^k ≤ Σ_j ν(P(z_j,r_j)) = ν(⋃_j P(z_j,r_j)) ≤ ν(X) = H_P^k(F) ≤ H_P^k(E)`,
so the total is at most `e + C e 5^k c⁻¹ H_P^k(E)`; here `C = C_n` (core constant) and
`c = c_k` (density constant), `C_{n,k} = C_n 5^k / c_k`. -/
theorem b4_missed_mass_bound :
    ∀ (n k : ℕ) (E F : Set (Space n)), MeasurableSet F → F ⊆ E →
    ∀ (C c e : ℝ), 0 ≤ C → 0 < c → 0 ≤ e →
      hausdorffP n k (E \ F) ≤ ENNReal.ofReal e →
    ∀ (J : Set ℕ) (z : J → Space n) (r : J → ℝ), (∀ j, 0 < r j) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∀ j, ENNReal.ofReal (c * r j ^ k) ≤ (hausdorffP n k).restrict F (Metric.ball (z j) (r j))) →
      (hausdorffP n k).restrict F (⋃ j, Metric.ball (z j) (5 * r j))ᶜ = 0 →
    ∀ U : J → Set (Space n),
      (∀ j, (hausdorffP n k).restrict F (Metric.ball (z j) (5 * r j) \ U j) ≤
        ENNReal.ofReal (C * e * (5 * r j) ^ k)) →
      hausdorffP n k (E \ ⋃ j, U j) ≤
        ENNReal.ofReal e * (1 + ENNReal.ofReal (C * 5 ^ k / c) * hausdorffP n k E) := by
  exact b4_missed_mass_bound_proof

/-- **The ambient zero-norm vertical graph** (second conjunct of
`FiniteHausdorffCriterionStatement`).

For `n ≥ 1` there is one full general regular vertical graph of dimension
`n + 2` and norm at most `0` whose image contains every subset of `X`, i.e. is all of `X`.

Proof sketch. Direction `W = ⊤` (`finrank W = n`, so `rank_eq : n + 2 = n + 2`), offset `0`,
function `0`. Its normal space `W^⊥ = ⊥` is zero, so `LipschitzWith 0`, the representative
`g = 0` has `HasParabolicBMOBound W 0 0` (zero oscillation; `0` is locally integrable), and
`RepresentsGeneralHalfTimeDerivative` is vacuous (`Fin (finrank W^⊥) = Fin 0`); `L = B = 0`.
The graph map is `(u,t) ↦ (u,t)`, so the image is `X`. (`AmbientZeroGraphCoverStatement`
gives such graphs only at norm `ε > 0`; it is not needed.) -/
theorem b4_ambient_zero_norm_graph :
    ∀ n : ℕ, 1 ≤ n →
      ∃ G : GeneralRegularVerticalGraph n (n + 2) 0, ∀ E : Set (Space n), E ⊆ G.image := by
  exact b4_ambient_zero_norm_graph_proof

end ParabolicRectifiability.Characterization
