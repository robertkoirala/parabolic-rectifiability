import ParabolicRectifiability.Characterization.Statements.Branches
import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import ParabolicRectifiability.Characterization.Proofs.Fivefold
import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.Envelope
import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.Criterion
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.Transfer
import ParabolicRectifiability.Characterization.Proofs.Replacement.BadRegionReplacement
import ParabolicRectifiability.Characterization.Proofs.GraphSource.SquareFiniteness
import ParabolicRectifiability.Characterization.Proofs.GraphSource.DensityBounds
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.GoodDomination
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.DominatedPieces
import ParabolicRectifiability.Characterization.Proofs.NestedPartitions.Differentiation
import ParabolicRectifiability.Characterization.Proofs.RadonApproximation

/-! # Intermediate results for the characterization theorem

This file collects the intermediate results used to prove the characterization of
parabolic rectifiability by square energies. Each declaration is a true statement with one
mathematical role; none assumes a packing, content, density or regularity hypothesis beyond
those in its statement. Each is proved by the result named in its body.

Two kinds of statements appear.

* **Named results.** The finite-Hausdorff criterion (`finite_hausdorff_criterion`),
  finiteness of graph-source squares (`graph_source_square_finite`), and the six auxiliary
  lemmas of the source-transfer argument (fivefold selection, Radon approximation, coordinate
  differentiation, good-set domination, bad-region replacement, ADR source transfer).
* **Steps of the main proof.** The Radon–Nikodym exhaustion of an intrinsic source
  (`exists_dominated_hausdorff_pieces`), Borel envelopes of individual graphs
  (`graph_borel_envelope`), and relative ADR differentiation on an individual graph
  (`graph_density_bounds`).

They are combined in `intrinsic_sufficiency_skeleton`, `necessity_skeleton` and the typed
refinements. The names here differ from the public theorems of the characterization, so the
proof can use them without importing the final theorem files.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-! ## Named results -/

/-- **Finite-Hausdorff criterion.** A Borel set `E` of finite `H_P^k` measure whose own
Hausdorff restriction `η = H_P^k⌊E` has finite `S^R_{η,T}` at `η`-a.e. point is covered
modulo `H_P^k` by typed graphs at every positive tolerance; at `k = n + 2` one zero-norm full
vertical graph contains every set.

Proof idea for `k < n + 2`: apply the scaled rectifiable Reifenberg theorem
(`ScaledRectifiableReifenbergCoreStatement`, through `ScaledThresholdCoreProperty`, which exposes the
ball `P(a,R)`, the full-source endpoint `2R` and the loss `C M R^k + Γ`) on fivefold-selected
balls, with the full restricted source and zero exceptional mass, repeated at errors `2^{-j}`.
With `e > 0`, `s > 0` from the finite tail, `F = E ∩ {S^s_η ≤ e}` and `ν = H_P^k⌊F`, it is
applied with `a = z_i`, `R = 5 r_i` (`r_i < s/10`, so `2R = 10 r_i ≤ s`), `M = e`, `Γ = 0` and
the same full source `ν`; then `∑ r_i^k ≤ c_k⁻¹ ν(F)` and the missed mass is at most
`e + C_n e 5^k ∑ r_i^k ≤ e + C_{n,k} e η(E)`. The case `k = n + 2` uses the ambient zero-norm
vertical graph instead.

Used in `intrinsic_sufficiency_skeleton` (applied to the Radon–Nikodym pieces) and
`typed_refinement_set_skeleton` (mixed at tolerance one, then each fixed family); elsewhere
through `FiniteHausdorffCriterionStatement` (density corollary, beta-p typing). -/
theorem finite_hausdorff_criterion : FiniteHausdorffCriterionStatement := by
  exact b4_finite_hausdorff_criterion

/-- **Graph-source squares are finite.** On every individual horizontal subset graph and every
individual full general regular vertical graph, the full-source square of the graph's own type
is finite off an `H_P^k`-null set, for every locally Radon source and every positive endpoint.
The proof combines the vertical and horizontal chart estimates (BMO growth, kernel bounds,
localization, Fourier estimates) with ADR source transfer.

Used in `necessity_skeleton` (squares at source-typical points of each carrying graph),
`typed_refinement_set_skeleton` and `typed_refinement_measure_skeleton` (fixed-type squares on
the assigned pieces). -/
theorem graph_source_square_finite : GraphSourceStatement := by
  exact ParabolicRectifiability.Characterization.b2_graph_source_square_finite

/-- **Fivefold selection.** Vitali fivefold selection for bounded-radius ball families in a
separable metric space. Used in `graph_density_bounds` (relative differentiation and ADR
comparison), `finite_hausdorff_criterion`, `good_set_domination` and
`bad_region_replacement`. -/
theorem fivefold_ball_selection : FivefoldSelectionStatement := by
  exact fivefold_ball_selection_proof

/-- **Radon approximation.** Restrictions of continuous compactly supported ambient functions
are dense in `L¹` of a locally Radon source on a closed subspace, and of its Borel
restrictions. Used in `coordinate_differentiation` and in the relative differentiation step of
`graph_density_bounds`. -/
theorem radon_approximation : RadonApproximationStatement := by
  exact ParabolicRectifiability.Characterization.bp2_radonApproximation_proof

/-- **Coordinate differentiation.** Lebesgue differentiation along given exact nested Borel
partitions with shrinking cells, for a finite inner regular source on a bounded Borel set.
Used in the BMO growth estimate inside `graph_source_square_finite`. -/
theorem coordinate_differentiation : CoordinateDifferentiationStatement := by
  exact ParabolicRectifiability.Characterization.CoordinateDifferentiationTree.coordinate_differentiation_of_leaves

/-- **Good-set domination.** On the good set `G_A` of a global ADR reference,
`ν⌊G_A ≤ (5^k/c) A σ`. Used in `bad_region_replacement`. -/
theorem good_set_domination : GoodDominationStatement := by
  exact ParabolicRectifiability.Characterization.good_set_domination_proof

/-- **Bad-region replacement.** Disjoint Whitney balls in the bad region with exact Borel
allocation of its source mass, the bad-mass bound, the piece bound and the replaced-source
domination with total-mass preservation. Used in `adr_source_transfer`. -/
theorem bad_region_replacement : ReplacementStatement := by
  exact ParabolicRectifiability.Characterization.ReplacementTree.bad_region_replacement_of_leaves

/-- **ADR source transfer.** A finite reference square `σ`-a.e. on a global ADR carrier
transfers to a finite square of every finite ambient source at `σ`-a.e. carrier point. Used in
`graph_source_square_finite`. -/
theorem adr_source_transfer : SourceTransferStatement := by
  exact ParabolicRectifiability.Characterization.SourceTransferTree.adr_source_transfer_of_leaves

/-! ## Steps of the main proof -/

/-- **Radon–Nikodym exhaustion of an intrinsic source.** Let `μ` be locally Radon, `μ ≪ H_P^k`, with a Borel sigma-finite `H_P^k`
carrier `E`. Write `μ = h η` with `η = H_P^k⌊E` (Radon–Nikodym; `0 < h < ∞` `μ`-a.e.), and
intersect the finite-Hausdorff Borel pieces of `E` with `{1/j ≤ h ≤ j}`. The resulting
countably many Borel sets `F_m` have `H_P^k(F_m) < ∞`, satisfy the domination
`H_P^k⌊F_m ≤ c_m μ` on the whole ambient space with a real `c_m > 0` (namely `c_m = j`), and
carry `μ`.

The domination is the only link to the original source: the energy
(`squareEnergy_mono_measure`, `squareEnergy_smul`) and the `μ`-null exceptional set are
transferred through it, so no inverse inequality under restriction is used. No dimension
restriction is needed for this measure-theoretic step. Used in
`intrinsic_sufficiency_skeleton`. -/
theorem exists_dominated_hausdorff_pieces :
    ∀ (n k : ℕ) (μ : Measure (Space n)), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      μ ≪ hausdorffP n k → HasBorelSigmaFiniteHausdorffCarrier k μ →
      ∃ F : ℕ → Set (Space n), (∀ m, MeasurableSet (F m)) ∧
        (∀ m, hausdorffP n k (F m) < ⊤) ∧
        (∀ m, ∃ c : ℝ, 0 < c ∧ (hausdorffP n k).restrict (F m) ≤ ENNReal.ofReal c • μ) ∧
        μ (⋃ m, F m)ᶜ = 0 := by
  exact ParabolicRectifiability.Characterization.exists_dominated_hausdorff_pieces_proof

/-- **Borel envelopes of individual graphs.** For one graph at a time:
* every horizontal subset graph of slope at most `ε` (arbitrary domain) lies in a horizontal
  subset graph of the same slope bound (its extension to the closure of the domain) whose
  image is Borel and has locally finite `H_P^k` measure: `H_P^k(Γ' ∩ P(q,R)) < ∞` for every
  centre `q` and radius `R`;
* every full general regular vertical graph of norm at most `ε` has Borel image with locally
  finite `H_P^k` measure.

Bounded base pieces have finite base measure and the graph maps are parabolic-Lipschitz; the
extended horizontal map and the vertical map are continuous on sigma-compact bases, so their
images are Borel. The original horizontal image itself need not be Borel. No smallness of
`ε` and no measure appears. The argument uses closed envelopes with the same bound, closed
full vertical graphs, bi-Lipschitz parametrizations and compact exhaustions of finite `H_P^k`
measure.

Used in `necessity_skeleton` (the Borel sigma-finite carrier of a graph-carried measure) and
both typed refinements (Borel first-type assignment). -/
theorem graph_borel_envelope :
    ∀ n k : ℕ,
      (∀ (ε : ℝ) (G : HorizontalGraph n k ε), ∃ G' : HorizontalGraph n k ε,
        G.image ⊆ G'.image ∧ MeasurableSet G'.image ∧
        ∀ (q : Space n) (R : ℝ), hausdorffP n k (G'.image ∩ Metric.ball q R) < ⊤) ∧
      (∀ (ε : ℝ) (G : GeneralRegularVerticalGraph n k ε), MeasurableSet G.image ∧
        ∀ (q : Space n) (R : ℝ), hausdorffP n k (G.image ∩ Metric.ball q R) < ⊤) := by
  exact Foundations.fgenv_graph_borel_envelope

/-- **Relative ADR differentiation on an individual graph.** For `n ≥ 1`, `1 ≤ k ≤ n + 2`, a locally Radon `μ ≪ H_P^k` and one graph
`Γ` (a horizontal subset graph of any finite slope, or a full general regular vertical graph
of any finite norm), at `μ`-a.e. point of `Γ` the lower `k`-density is positive and the upper
`k`-density is finite. The densities are those of the full original source, including its
mass off `Γ`.

Proof sketch. Cover the original image
`Γ`, modulo `H_P^k`, by countably many closed Borel globally ADR carriers `C_j` with
reference measures `σ_j`, `c_j r^k ≤ σ_j(P(z,r)) ≤ C_j r^k` for `z ∈ C_j` (the closed ADR
completions of the vertical and horizontal charts); the remainder is `H_P^k`-null,
hence `μ`-null. On each carrier decompose the full source
`μ = μ⌊C_j + μ⌊C_jᶜ = f_j σ_j + τ_j` with `τ_j ⊥ σ_j` (ADR–Hausdorff comparison and
`μ ≪ H_P^k`). Apply relative differentiation to the full original `μ`:
at `μ`-a.e. `z ∈ C_j`, `0 < f_j(z) < ∞` and for all sufficiently small `r`
`c_j f_j(z)/2 ≤ μ(P(z,r))/r^k ≤ 2 C_j f_j(z)`. Only then restrict the conclusion to points
of the original image `Γ`. The original graph is distinguished from its closed completion,
and no decomposition over the possibly non-Borel image `Γ` is used.

Absolute continuity is necessary (a point mass on a graph has infinite density) and is the
hypothesis of the necessity branch. No density, doubling or finite-mass hypothesis is added.
Used in `necessity_skeleton`. -/
theorem graph_density_bounds :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      μ ≪ hausdorffP n k →
      (∀ (ε : ℝ) (G : HorizontalGraph n k ε), ∀ᵐ z ∂μ, z ∈ G.image →
        0 < lowerDensity μ k z ∧ upperDensity μ k z < ⊤) ∧
      (∀ (ε : ℝ) (G : GeneralRegularVerticalGraph n k ε), ∀ᵐ z ∂μ, z ∈ G.image →
        0 < lowerDensity μ k z ∧ upperDensity μ k z < ⊤) := by
  exact ParabolicRectifiability.Characterization.b2_graph_density_bounds

end ParabolicRectifiability.Characterization
