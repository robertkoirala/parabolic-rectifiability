import ParabolicRectifiability.Foundations.Statements.DensityBridges
import ParabolicRectifiability.Characterization.Proofs.Fivefold
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.ElementaryLemmas
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.UpperCover
import ParabolicRectifiability.Characterization.Statements.SourceTransfer

/-! # Positive upper density gives Hausdorff domination: intermediate statements

Target: `hausdorffP_le_of_upperDensity_ge : UpperDensityDominationStatement`, assembled in
`fupdom_upper_density_domination` with the constant `C_k = 2·10^k` (independent of `n`).
The proof keeps the open approximation, the mesh limit and the approximation-error limit
distinct:
* `fupdom_input_fivefold` — the fivefold selection statement `FivefoldSelectionStatement`;
* `fupdom_exists_ratio_gt` — a lower bound on the upper density gives arbitrarily small
  radii with `ρ(P(z,r)) > (a/2) r^k`;
* `fupdom_hausdorffP_le_of_fivefold` — the covering step: fivefold selection plus the
  mesh limit give `H_P^k(E) ≤ (2·10^k/a) ρ(V)` for every open `V ⊇ E`, in implication form from
  `FivefoldSelectionStatement`; the density hypothesis is required at **every** point of `E`;
* `fupdom_exists_open_measure_le` — open approximation inside `O` (outer regularity);
* the approximation-error limit, the restriction comparison and finiteness are handled in
  `fupdom_upper_density_domination`.

The declarations delegate to the proofs named `<name>_proof`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- **Fivefold selection** `FivefoldSelectionStatement`, proved as
`Characterization.fivefold_ball_selection`. It is not re-proved here; there is no second
Vitali covering. -/
theorem fupdom_input_fivefold : Characterization.FivefoldSelectionStatement := by
  exact Characterization.fivefold_ball_selection_proof

/-- **Large ratios from an upper-density bound.** There are arbitrarily small radii such that
`ρ(P(z,r)) > (a/2) r^k`; the factor `a/2` handles the non-strict hypothesis.

For any measure `μ`, any `k`, a point `z` with `a ≤ Θ^{k,*}(μ,z)` (`a > 0`
real; the upper density may be `⊤`) and `δ > 0`, there is `0 < r < δ` with
`(a/2) r^k < μ(P(z,r))` (through `ENNReal.ofReal`).

Route: `ofReal (a/2) < ofReal a ≤ limsup (densityRatio μ k z) (𝓝[>] 0)`;
`Filter.frequently_lt_of_lt_limsup` gives `∃ᶠ r in 𝓝[>] 0, ofReal (a/2) < densityRatio μ k z r`;
intersect with `Ioo 0 δ` (`Ioo_mem_nhdsGT`, `Filter.Frequently.and_eventually`, `.exists`). At
`r > 0`, `ofReal r ^ k ≠ 0, ⊤` and `ofReal (a/2) < μ(P(z,r)) / ofReal r ^ k` gives
`ofReal (a/2 * r^k) < μ(P(z,r))` (`ENNReal.lt_div_iff_mul_lt`, `ENNReal.ofReal_mul`,
`ENNReal.ofReal_pow`). No regularity of `μ`; valid for every `k`. -/
theorem fupdom_exists_ratio_gt {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n)
    (a : ℝ) (ha : 0 < a) (hz : ENNReal.ofReal a ≤ upperDensity μ k z)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (a / 2 * r ^ k) < μ (Metric.ball z r) := by
  exact fupdom_exists_ratio_gt_proof μ k z a ha hz δ hδ

/-- **The fivefold covering bound for Hausdorff measure.**
Implication form: `FivefoldSelectionStatement` is the first hypothesis;
`fupdom_upper_density_domination` supplies it from `fupdom_input_fivefold`.

For any measure `ρ` on `Space n`, any `k`, `a > 0`, an open `V` and an
**arbitrary** set `E ⊆ V` with `a ≤ Θ^{k,*}(ρ,z)` at **every** `z ∈ E`:
`H_P^k(E) ≤ (2·10^k/a) ρ(V)`. (A `ρ`-a.e. hypothesis would not suffice: the density hypothesis
is pointwise.)

Route. Fix a mesh `δ > 0`. Family indexed by `ι_δ := {p : Space n × ℝ // p.1 ∈ E ∧ 0 < p.2 ∧
10 p.2 < δ ∧ P(p.1, 5 p.2) ⊆ V ∧ ofReal (a/2 · p.2^k) < ρ(P(p.1,p.2))}` (a `Type`); radii
bounded by `δ/10`. Every `z ∈ E` is a centre: `V` open gives `s > 0` with `P(z,s) ⊆ V`;
`fupdom_exists_ratio_gt` with radius bound `min (δ/10) (s/5)`. `h5` (with `X = Space n`, separable since proper) gives a
countable `J` with pairwise disjoint balls `P(z_j,r_j)` and `E ⊆ ⋃_{j ∈ J} P(z_j, 5 r_j)`, each of
`ediam ≤ ofReal (10 r_j) ≤ δ` (`Metric.ediam_ball`/`EMetric.ediam_ball_le`-type bound
`ediam (ball x r) ≤ 2r`). Then
`∑_j ediam (P(z_j,5r_j))^k ≤ 10^k ∑_j r_j^k ≤ (2·10^k/a) ∑_j ρ(P(z_j,r_j)) ≤ (2·10^k/a) ρ(V)`
(disjoint measurable balls inside `V`: `measure_biUnion` / `tsum_meas_le_meas_iUnion_of_disjoint`
for countable `J`). Mesh limit: `Measure.hausdorffMeasure_le_liminf_tsum` with `d = (k : ℝ)`,
`l = 𝓝[>] 0` or `atTop` along `δ_j = 1/(j+1)`, the dependent countable index `J_δ` (instance
`Set.Countable.to_subtype`), and `ENNReal.rpow_natCast`; `hausdorffP n k` is
`Measure.hausdorffMeasure (k : ℝ)`. `E = ∅` is trivial. Also valid at
`k = 0` (then `H^0` counts points and each ball has mass `> a/2`). -/
theorem fupdom_hausdorffP_le_of_fivefold (h5 : Characterization.FivefoldSelectionStatement)
    {n : ℕ} (k : ℕ) (ρ : Measure (Space n)) (a : ℝ) (ha : 0 < a)
    (E V : Set (Space n)) (hV : IsOpen V) (hEV : E ⊆ V)
    (hE : ∀ z ∈ E, ENNReal.ofReal a ≤ upperDensity ρ k z) :
    hausdorffP n k E ≤ ENNReal.ofReal (2 * 10 ^ k / a) * ρ V := by
  exact fupdom_hausdorffP_le_of_fivefold_proof h5 k ρ a ha E V hV hEV hE

/-- **Open approximation inside `O`.** Choose open `V` with `E ⊆ V ⊆ O` and
`ρ(V) ≤ ρ(E) + ε`, using outer regularity and intersecting an outer approximation with `O`.

For `ρ` finite on compact sets on `Space n`, an open `O`, an arbitrary
`E ⊆ O` and `ε ≠ 0` in `ℝ≥0∞`, there is an open `V` with `E ⊆ V ⊆ O` and `ρ(V) ≤ ρ(E) + ε`.

Route: `Space n` is a proper (hence σ-compact, second-countable) metric space with its Borel
σ-algebra, so `ρ` is locally finite (`isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`) and
regular (`Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`), hence outer
regular; `Set.exists_isOpen_le_add E ρ hε` gives an open `U ⊇ E` with `ρ U ≤ ρ E + ε`
(including `ρ E = ⊤`); take `V = U ∩ O` and `measure_mono`. -/
theorem fupdom_exists_open_measure_le {n : ℕ} (ρ : Measure (Space n))
    (hρ : IsFiniteMeasureOnCompacts ρ) (E O : Set (Space n)) (hO : IsOpen O) (hEO : E ⊆ O)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ V : Set (Space n), IsOpen V ∧ E ⊆ V ∧ V ⊆ O ∧ ρ V ≤ ρ E + ε := by
  exact fupdom_exists_open_measure_le_proof ρ hρ E O hO hEO ε hε

end ParabolicRectifiability.Foundations
