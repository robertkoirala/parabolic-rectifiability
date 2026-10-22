import ParabolicRectifiability.BetaP.Statements.Failures
import ParabolicRectifiability.BetaP.Statements.Corollaries
import ParabolicRectifiability.BetaP.Statements.Laws
import ParabolicRectifiability.Examples.Statements.Lacunary

/-! # Statements for the `S_p` and `T_p` examples

Named statements (propositions only) used to show that the conditions `S_p` and `T_p` are not
sufficient or not necessary in the stated ranges of `p`. They are proved by the theorems
`c2_zeroBase_carried`, `c2_timeSlice_measure`, …, and assembled in the theorems
`c2_spBelowTwo_notSufficient_of_witness`, ….

Targets (namespace `ParabolicRectifiability.BetaP`):
* `spBelowTwo_notSufficient_of_witness`: `S_p` is not sufficient for `p < 2`;
* `spAboveTwo_notNecessary_of_witness`: `S_p` is not necessary for `p > 2`;
* `tpBelowTwo_notNecessary_of_witness`: `T_p` is not necessary for `p < 2`;
* `tpAboveTwo_notSufficient_of_witness`, `tpAboveTwo_noVanishingRemainder_of_witness` and
  `tpAboveTwo_noIntegratedRemainder_of_witness`: the `T_p` failures for `p > 2`;
* `spBelowTwo_noVanishingRemainder_of_witness`: the `S_p` remainder failure for `p < 2`.

Statements (one mathematical responsibility each):
1. `C2TimeSliceMeasureStatement`: `timeSlice` is a measurable embedding and pulls parabolic balls
   back to Euclidean balls.
2. `C2ZeroBaseCarriedStatement`: the rank-zero vertical graph of a general regular time function
   carries every measure concentrated on its image.
3. `C2TpAboveEndpointStatement`: from endpoint `2` to every positive endpoint for `T_p` at
   `n = 1`, `k = 2`, in implication form over the finite-annulus law `BetaPowAnnulusStatement`.
4. `C2SqueezeLimitStatement`: a remainder function tending to zero cannot stay above a positive
   constant along positive parameters squeezed below `C ε^p`.
5. `C2UniformTailsStatement`: Egorov and compact inner approximation give uniformly small `S_p`
   tails on a compact set of positive mass.
6. `C2RescaledMassStatement`: normalized rescaling at a lower-mass radius keeps unit-ball mass at
   least `c`.
7. `C2RescaledCarrierNullStatement`: horizontally rectifiable compact supports are null for the
   rescaled source of a graph-null Hausdorff restriction.

The lower mass for a restricted Hausdorff source is
`Characterization.b4_hausdorff_restrict_ball_lower_bound_proof`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## The time slice -/

/-- **Time slice as a measure map** (`c2_timeSlice_measure`). The constant-time embedding
`ι = timeSlice : ℝ² → ℝ² × ℝ` is a measurable embedding, and for every measure `ν` on `ℝ²`,
every `x` and every real `r`, `(ι_#ν)(P(ιx, r)) = ν(B(x, r))`, because
`P((x,0),r) ∩ ι(ℝ²) = ι(B(x,r))`. -/
def C2TimeSliceMeasureStatement : Prop :=
  MeasurableEmbedding timeSlice ∧
    ∀ (ν : Measure Plane) (x : Plane) (r : ℝ),
      (ν.map timeSlice) (Metric.ball (timeSlice x) r) = ν (Metric.ball x r)

/-! ## The rank-zero regular graph -/

/-- **Rank-zero graph carrying** (`c2_zeroBase_carried`). For a real time function `g` whose lift to the
zero vertical base of `ℝ¹ × ℝ` is general regular with norm bound `η`, every measure on `Space 1`
concentrated on `{(g(t), t) : t ∈ ℝ}` is carried by finitely-normed graphs of the mixed family at
`k = 2`: the single full vertical graph with direction `{0}`, offset `0` and function
`zeroBaseLift g` has exactly that image. -/
def C2ZeroBaseCarriedStatement : Prop :=
  ∀ (g : ℝ → ℝ) (η : ℝ),
    IsGeneralRegularVerticalFunction Examples.zeroDirection (Examples.zeroBaseLift g) η →
    ∀ μ : Measure (Space 1),
      μ (Set.range fun t : ℝ => point (EuclideanSpace.single (0 : Fin 1) (g t)) t)ᶜ = 0 →
      IsCarriedByFiniteNormGraphs .mixed 2 μ

/-! ## The `p > 2` lacunary family -/

/-- **Endpoint extension for `T_p`** (`c2_tpAbove_endpoint`). In implication form over the
finite-annulus law `BetaPowAnnulusStatement`: for a locally Radon source on `Space 1`,
`T_p^2(z) < ∞` implies `T_p^a(z) < ∞` for every endpoint `a > 0`, at `n = 1`, `k = 2`, mixed
family (the finite-annulus comparison makes the conclusion valid for any positive finite
endpoint). -/
def C2TpAboveEndpointStatement : Prop :=
  BetaPowAnnulusStatement →
    ∀ μ : Measure (Space 1), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ p : ℝ, 0 < p → ∀ (z : Space 1) (a : ℝ), 0 < a →
      energyT μ 2 .mixed p 2 z < ⊤ → energyT μ 2 .mixed p a z < ⊤

/-- **Squeezed limit** (`c2_squeeze_limit`). If `Φ(M) → 0` as `M ↓ 0` and
`0 < g(ε) ≤ C ε^p` for `0 < ε ≤ ε₀` (`C, p > 0`), then for every `c > 0` some `0 < ε ≤ ε₀` has
`Φ(g(ε)) < c`. (A bound `1/2 ≤ Φ(C ε^p)` for all small `ε > 0` would contradict the limit at
zero.) No monotonicity or value at zero of `Φ` is used. -/
def C2SqueezeLimitStatement : Prop :=
  ∀ Φ : ℝ → ℝ, Tendsto Φ (𝓝[>] 0) (𝓝 0) →
    ∀ (g : ℝ → ℝ) (C p ε₀ c : ℝ), 0 < C → 0 < p → 0 < ε₀ → 0 < c →
      (∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → 0 < g ε ∧ g ε ≤ C * ε ^ p) →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ Φ (g ε) < c

/-! ## The `S_p` failure below two -/

/-- **Uniform tails** (`c2_uniform_tails`). Egorov with compact inner approximation: for an
available family, a finite source `ω`, `p > 0` and a set `A` carrying `ω` with
`ω(A) > 0` on which `S_p^1 < ∞`, there is a compact `K ⊆ A` with `ω(K) > 0` on which the tails
`S_{p,ω}^h` are uniformly small: for every `M > 0` some `h > 0` has `S_{p,ω}^h ≤ M` on `K`. -/
def C2UniformTailsStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ ω : Measure (Space n), IsFiniteMeasure ω → ∀ p : ℝ, 0 < p → ∀ A : Set (Space n),
    ω Aᶜ = 0 → 0 < ω A → (∀ y ∈ A, energyS ω k T p 1 y < ⊤) →
      ∃ K : Set (Space n), IsCompact K ∧ K ⊆ A ∧ 0 < ω K ∧
        ∀ M : ℝ, 0 < M → ∃ h : ℝ, 0 < h ∧ ∀ y ∈ K, energyS ω k T p h y ≤ ENNReal.ofReal M

/-- **Rescaled mass** (`c2_rescaled_mass`). Normalized rescaling:
`ν̃ = R^{-k}(f_{q,R})_# ν` (`rescaledSource`) has
`ν̃(P(0,1)) ≥ c` as soon as `ν(P(q,R)) ≥ c R^k`, since `f_{q,R}` maps `P(q,R)` onto `P(0,1)`. -/
def C2RescaledMassStatement : Prop :=
  ∀ (n k : ℕ) (ν : Measure (Space n)) (q : Space n) (R : ℝ) (hR : 0 < R) (c : ℝ), 0 ≤ c →
    ENNReal.ofReal (c * R ^ k) ≤ ν (Metric.ball q R) →
      ENNReal.ofReal c ≤ rescaledSource ν k q R hR (Metric.ball (point 0 0) 1)

/-- **Rescaled carrier nullity** (`c2_rescaled_carrier_null`). Every allowable horizontal support
has zero `ν̃` mass, including its Hausdorff-null residual: if a Borel `A ⊆ ℝ² × ℝ` meets every horizontal graph of every slope (`n = 2`, `k = 1`) in an
`H_P^1`-null set, then for every centre `q`, scale `R > 0` and compact `K` covered modulo `H_P^1` by
countably many horizontal graphs, the rescaled source `R^{-1}(f_{q,R})_#(H_P^1⌊A)` gives `K` zero
mass. -/
def C2RescaledCarrierNullStatement : Prop :=
  ∀ A : Set (Space 2), MeasurableSet A →
    (∀ (ε : ℝ) (G : HorizontalGraph 2 1 ε), hausdorffP 2 1 (A ∩ G.image) = 0) →
    ∀ (q : Space 2) (R : ℝ) (hR : 0 < R) (K : Set (Space 2)), IsCompact K →
      (∃ (I : Set ℕ) (ε : I → ℝ) (G : ∀ i, HorizontalGraph 2 1 (ε i)),
        hausdorffP 2 1 (K \ ⋃ i, (G i).image) = 0) →
      rescaledSource ((hausdorffP 2 1).restrict A) 1 q R hR K = 0

end ParabolicRectifiability.BetaP
