import ParabolicRectifiability.QuantitativeCharacterization.Statements.Approximants
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.UpperGrowth
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.ReferenceEstimates
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Pieces
import ParabolicRectifiability.IntegralCanonical.Statements.Canonical
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Ambient.RootCovering
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reverse.ReverseBound
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.ForwardCovering
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.ReferenceIntrinsic
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Trace.ReferenceCoversRectifiable
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Pieces.CountablePieces
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.RootApproximants
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.BoundedSupport.BoundedForwardApproximants

/-! # The outer statements of the quantitative characterization

The statements below are the outer interfaces of the quantitative characterization (reference
estimates, intrinsic properties of references, traces, pieces, absolute continuity, the forward
covering, the reverse bound, the ambient case, the approximants and the bounded-support case).
Each is proved by its own module, imported above. The modules `Mono`, `Energy`, `Covers`,
`Characterization`, `Approximants` and `Pieces` of this part use these statements, together
with the explicit hypotheses supplied from intrinsic sufficiency and the canonical decomposition.

Two statements take as a hypothesis the *typed reference covers* property
`∀ ρ : Reference n k L, ∀ ε > 0, HasTypedMeasureCover ρ.kind k ρ.measure ε`. It is not an
assumption on the measure under study: it is a property of the reference class, discharged from
`reference_estimates`, `reference_intrinsic_of_estimates` and `IntrinsicSufficiencyStatement`.
One statement takes `IntegralCanonical.IsCanonicalDecomposition k μ 1` as a hypothesis,
discharged from `CanonicalDecompositionStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-! ## Reference models -/

/-- **Reference estimates.**

Uniform global ADR bounds and the own-type Carleson energy bound for **every**
available `L`-reference (horizontal plateau references, vertical references, the ambient
reference), with constants depending only on `(n,k,L)`; zero energy at `k = n + 2`. -/
theorem reference_estimates : ReferenceEstimatesStatement := by
  exact ba1_reference_estimates

/-- **Intrinsic properties of references.**

An `L`-reference measure with global `A`-ADR bounds and own-type Carleson
energy at most `C` satisfies every hypothesis of fixed-family intrinsic sufficiency for its own
type: it is locally Radon, absolutely continuous
with respect to `H_P^k`, has a Borel sigma-finite `H_P^k` carrier, and its own-type square
function is finite `σ`-almost everywhere at some positive endpoint. The constants `A, C`
are arbitrary reals. If `A ≤ 0`, the upper-growth hypothesis forces the measure to vanish; if
`C ≤ 0`, the energy hypothesis forces zero reference energy (a nonzero flat reference has zero
energy). -/
theorem reference_intrinsic_of_estimates :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ L : ℝ, 1 ≤ L → ∀ A C : ℝ,
    ∀ ρ : Reference n k L, IsADR A k ρ.measure → referenceEnergy ρ ≤ ENNReal.ofReal C →
      IsFiniteMeasureOnCompacts ρ.measure ∧ ρ.measure.InnerRegular ∧
        ρ.measure ≪ hausdorffP n k ∧ HasBorelSigmaFiniteHausdorffCarrier k ρ.measure ∧
        ∃ R : ℝ, 0 < R ∧ ∀ᵐ z ∂ρ.measure, squareEnergy ρ.measure k ρ.kind R z < ⊤ := by
  exact ParabolicRectifiability.QuantitativeCharacterization.dp2_referenceIntrinsic_proof

/-! ## The qualitative meaning of a covering -/

/-- **A measure with a quantitative covering is rectifiable.**

A locally Radon `μ` with the `(K,L)` property is regularly mixed parabolically
`k`-rectifiable, provided every `L`-reference measure has typed graph covers at every
tolerance. The proof: root packing gives `H_P^k(limsup P_i) = 0`; absolute continuity
gives finite multiplicity a.e.; finite bad logarithmic fibres and the distance floors put
almost every point of each root on one of its finitely many closed references; lower
reference ADR turns reference-null exceptional sets into `H_P^k`-null, hence `μ`-null, sets;
a countable exhaustion by support-centred roots finishes. No ADR or upper growth of `μ`.

The hypothesis on references is discharged by `reference_typed_covers`. -/
theorem qmr_rectifiable_of_reference_covers :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ L : ℝ, 1 ≤ L →
    (∀ ρ : Reference n k L, ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover ρ.kind k ρ.measure ε) →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ K : ℝ, 1 ≤ K → IsQuantitativelyMixedRectifiable k K L μ →
      IsRegularlyRectifiableMeasure .mixed k μ := by
  exact ParabolicRectifiability.QuantitativeCharacterization.dp2_qmr_rectifiable_of_reference_covers

/-- **Countable pieces from typed covers.**

From a disjoint Borel typed split `E_H, E_V` carrying `μ ≪ H_P^k`, with
`μ⌊E_H` carried by horizontal graphs of slope at most `1` and `μ⌊E_V` by full general regular
vertical graphs of norm at most `1` (the output of typed refinement at `ε = 1`):
close the horizontal envelopes, take compact patches, extend the normal coordinates
(`Lip F ≤ √(1+n)`), complete by Whitney plateaus to `L_*`-references; vertical graphs of norm
at most one are already `L_*`-references (the ambient reference at `k = n + 2`); assign the
source disjointly to obtain pieces `E_j`, each nonzero piece carried by one closed reference
and `(2^k, max 2 √(1+n))`-quantitative by the one-ball covering `P(a,2R)`. -/
theorem countable_pieces_of_typed_covers :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    μ ≪ hausdorffP n k →
    ∀ EH EV : Set (Space n), MeasurableSet EH → MeasurableSet EV → Disjoint EH EV →
    μ (EH ∪ EV)ᶜ = 0 →
    HasTypedMeasureCover .horizontal k (μ.restrict EH) 1 →
    HasTypedMeasureCover .vertical k (μ.restrict EV) 1 →
      ∃ E : ℕ → Set (Space n), (∀ j, MeasurableSet (E j)) ∧
        Pairwise (fun i j => Disjoint (E i) (E j)) ∧
        μ = Measure.sum (fun j => μ.restrict (E j)) ∧
        ∀ j, μ.restrict (E j) ≠ 0 →
          IsQuantitativelyMixedRectifiable k ((2 : ℝ) ^ k) (max 2 (Real.sqrt (1 + n)))
            (μ.restrict (E j)) := by
  exact ParabolicRectifiability.QuantitativeCharacterization.dp2_countable_pieces_of_typed_covers

/-- **Regular rectifiability from a countable restricted sum.**

Countable union of graph carriers and countable addition of absolutely
continuous restrictions. If `μ = Σ_j μ⌊E_j` with Borel `E_j` and every nonzero piece is
regularly mixed parabolically `k`-rectifiable, then so is `μ`. Zero pieces need nothing. -/
theorem isRegularlyRectifiableMeasure_of_sum_restrict :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), ∀ E : ℕ → Set (Space n), (∀ j, MeasurableSet (E j)) →
    μ = Measure.sum (fun j => μ.restrict (E j)) →
    (∀ j, μ.restrict (E j) ≠ 0 → IsRegularlyRectifiableMeasure .mixed k (μ.restrict (E j))) →
      IsRegularlyRectifiableMeasure .mixed k μ := by
  exact ParabolicRectifiability.QuantitativeCharacterization.dp2_isRegularlyRectifiableMeasure_of_sum_restrict

/-! ## The quantitative equivalence -/

/-- **Upper growth implies absolute continuity** (by Hausdorff covers; also at `k = n + 2`).

A locally Radon `μ` with the support-centred upper growth
`μ(P(z,r)) ≤ A r^k` (`z ∈ supp μ`, `r > 0`) is absolutely continuous with respect to
`H_P^k`. The constant `A` is an arbitrary real. -/
theorem absolutelyContinuous_of_upper_growth :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular → ∀ A : ℝ,
    (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) →
      μ ≪ hausdorffP n k := by
  exact Foundations.fgac_absolutelyContinuous_of_upper_growth

/-- **The local forward covering** (forward geometric covering, `k < n + 2`).

For `1 ≤ k < n + 2` and `A ≥ 1` there are `B_loc, L₀, C ≥ 1` such that, at any
support-centred root `P(a,R)` of a locally Radon `μ`, the local ADR bounds and the local
Carleson bound `∫_{P(b,s)} ∫_0^s β_μ² dr/r dμ ≤ M s^k` (whole original `μ`) for
`b ∈ supp μ ∩ P(a, B_loc R)`, `0 < s ≤ B_loc R` give a `(C(1+M), L₀)`-regular mixed covering
of `P(a,R)`: direct partitions, energy stopping with root and same-family local packing,
good-region necks, the last-witness comparison bound, the whole vertical and horizontal
completions, coverage of every good point-scale slab, and bad slabs paid by the energy.
This is the forward geometric certificate in its local form; the global forward
bound of the quantitative characterization is its specialization `M = M_β`. No approximant or
rectifiability conclusion is part of this statement. -/
theorem exists_local_forward_covering :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Bloc : ℝ, 1 ≤ Bloc ∧ ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ M : ℝ, 0 ≤ M →
      (∀ b ∈ μ.support ∩ Metric.ball a (Bloc * R), ∀ s : ℝ, 0 < s → s ≤ Bloc * R →
        ENNReal.ofReal (A⁻¹ * s ^ k) ≤ μ (Metric.ball b s) ∧
          μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k) ∧
          (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) ≤
            ENNReal.ofReal (M * s ^ k)) →
      Nonempty (RegularMixedCovering k (C * (1 + M)) L₀ μ a R) := by
  exact Forward.d1comp_exists_local_forward_covering

/-- **The local reverse estimate.**

For every `L ≥ 1` there is `B_rev(n,k,L) ≥ 1` (before `A`) and, for every
`A ≥ 1`, a constant `C(n,k,A,L) > 0`, such that a `(K,L)` covering at a support-centred root
`P(a,R)` and the upper growth `μ(P(b,s)) ≤ A s^k` for `b ∈ supp μ ∩ P(a, B_rev R)`,
`0 < s ≤ B_rev R`, give `∫_{P(a,R)} ∫_0^R β_μ² dr/r dμ ≤ C K R^k`: Hall allocation, full-source
and centre transfer to each reference, the transport error integral, the reference energy
bound, bad pairs paid by the upper beta bound. This is literally the second conjunct of
`UniformLocalStatement`; all `1 ≤ k ≤ n + 2`. -/
theorem exists_local_reverse_bound :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ L : ℝ, 1 ≤ L → ∃ Brev : ℝ, 1 ≤ Brev ∧ ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 < C ∧
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ K : ℝ, 1 ≤ K →
        Nonempty (RegularMixedCovering k K L μ a R) →
        (∀ b ∈ μ.support ∩ Metric.ball a (Brev * R), ∀ s : ℝ, 0 < s → s ≤ Brev * R →
          μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k)) →
        (∫⁻ z in Metric.ball a R, squareEnergy μ k .mixed R z ∂μ) ≤
          ENNReal.ofReal (C * K * R ^ k) := by
  exact ReverseTree.d2comp_exists_local_reverse_bound_of_inputs reference_estimates
    ba1_horizontal_basic_proof ba1_vertical_basic_proof ba1_ambient_basic_proof

/-- **The ambient root covering.**

At `k = n + 2`, at every support-centred root `P(a,R)` of a locally Radon `μ`,
the single model ball `P(a,2R)` with the ambient reference `(X, L^{n+1})`, empty bad set and
the whole tested cylinder as its scale set is a `(2^{n+2}, 2)`-regular mixed covering; with
`F_H = ∅`, `F_V = P(a,R)` it is a typed trace split, the measure identity holds at every
level, the relative tail holds for every tail constant (multiplicity one on `P(a,R)`), and
for `N ≥ 1` the approximants are `μ⌊P(a,R)` and `0` and the residual is `0`.
No growth, energy or absolute continuity hypothesis is used. -/
theorem ambient_root_covering :
    ∀ n : ℕ, 1 ≤ n →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R →
      ∃ 𝒞 : RegularMixedCovering (n + 2) ((2 : ℝ) ^ (n + 2)) 2 μ a R,
        𝒞.index = {0} ∧ (∀ i, 𝒞.center i = a ∧ 𝒞.radius i = 2 * R) ∧
        𝒞.IsTypedTraceSplit ∅ (Metric.ball a R) ∧
        𝒞.MeasureIdentity ∅ (Metric.ball a R) ∧
        (∀ c : ℝ, 𝒞.RelativeTail c) ∧
        ∀ N : ℕ, 1 ≤ N →
          𝒞.approximant (Metric.ball a R) N = μ.restrict (Metric.ball a R) ∧
            𝒞.approximant ∅ N = 0 ∧ 𝒞.residual N = 0 := by
  exact damb_ambient_root_covering_proof

/-! ## Measure approximants -/

/-- **Root approximants.**

At one support-centred root `P₀ = P(a,R)` for an arbitrary prescribed
`(K,L)` covering `𝒞`, under the upper growth `μ(P(b,s)) ≤ A s^k` for
`b ∈ supp μ ∩ P(a, 2LR)`, `0 < s ≤ 2LR` (all model balls are support-centred inside
`P(a,LR)`, with radii below `2LR`), and the typed reference covers:
* disjoint Borel `F_H, F_V ⊂ P₀` inside the typed traces carrying `μ⌊P₀`;
* the exact identity `μ⌊P₀ = μ^N_H + μ^N_V + e^N` at every level `N`;
* each `μ^N_H` horizontally and each `μ^N_V` regularly vertically rectifiable (local absolute
  continuity, reference ADR, typed reference covers);
* with `s = (2^k + A²)K`: the relative tail `e^N(P₀) ≤ 2 e^{-N/((2^k+A²)K)} μ(P₀)`
  whenever the root lower bound `A⁻¹ R^k ≤ μ(P₀)` holds;
* with `s = (2^k+1)K`: the absolute tail
  `e^N(P₀) ≤ C_abs R^k e^{-N/(C_abs K)}`, `C_abs = max(2A, 2^k + 1)`. -/
theorem exists_root_approximants :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ A : ℝ, 1 ≤ A → ∀ L : ℝ, 1 ≤ L →
    (∀ ρ : Reference n k L, ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover ρ.kind k ρ.measure ε) →
    ∀ K : ℝ, 1 ≤ K → ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ 𝒞 : RegularMixedCovering k K L μ a R,
      (∀ b ∈ μ.support ∩ Metric.ball a (2 * L * R), ∀ s : ℝ, 0 < s → s ≤ 2 * L * R →
        μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k)) →
      ∃ FH FV : Set (Space n), 𝒞.IsTypedTraceSplit FH FV ∧ 𝒞.MeasureIdentity FH FV ∧
        (∀ N : ℕ, IsRegularlyRectifiableMeasure .horizontal k (𝒞.approximant FH N) ∧
          IsRegularlyRectifiableMeasure .vertical k (𝒞.approximant FV N)) ∧
        (ENNReal.ofReal (A⁻¹ * R ^ k) ≤ μ (Metric.ball a R) →
          𝒞.RelativeTail ((2 : ℝ) ^ k + A ^ 2)) ∧
        ∀ N : ℕ, 𝒞.residual N (Metric.ball a R) ≤
          ENNReal.ofReal (max (2 * A) ((2 : ℝ) ^ k + 1) * R ^ k *
            Real.exp (-(N : ℝ) / (max (2 * A) ((2 : ℝ) ^ k + 1) * K))) := by
  exact dp2_exists_root_approximants

/-- **Canonical identification of the approximant limits.**

Let `μ` be locally Radon with support-centred upper growth, given its
canonical decomposition at endpoint `1` (the output of the canonical decomposition theorem). For a `(K,L)` covering of a root and a typed trace split whose approximants are
typed rectifiable, the retained measures increase to `μ_H⌊P₀`, `μ_V⌊P₀` on every Borel set and
the residual decreases to zero in total mass: finite multiplicity a.e. from the radius sum,
the limits `μ⌊F_H`, `μ⌊F_V` are typed rectifiable, and canonical uniqueness identifies them. -/
theorem approximant_canonical_limits :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ A L K : ℝ, 1 ≤ L → 1 ≤ K →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    IntegralCanonical.IsCanonicalDecomposition k μ 1 →
    (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ 𝒞 : RegularMixedCovering k K L μ a R,
    ∀ FH FV : Set (Space n), 𝒞.IsTypedTraceSplit FH FV →
    (∀ N : ℕ, IsRegularlyRectifiableMeasure .horizontal k (𝒞.approximant FH N) ∧
      IsRegularlyRectifiableMeasure .vertical k (𝒞.approximant FV N)) →
      𝒞.HasCanonicalLimits FH FV := by
  exact dp2_approximant_canonical_limits

/-- **Bounded-support forward approximants.**

For `1 ≤ k < n + 2` there are `L₀, C ≥ 1` such that for every nonzero locally
Radon `μ` with `0 < D_E = diam_P E < ∞`, upper growth at all radii, lower growth for
`0 < r ≤ D_E` and `M_β < ∞`, every support-centred root `P(a,R)` (small or large) has a chosen
`(C(1+M_β), L₀)` covering with a typed trace split, the measure identity and the relative
tail with `C_tail = 2^k + A²`. Use the local forward construction for `R < r_* = D_E/B`, with
`B` larger than all buffer constants. For every `R ≥ r_*`, including `r_* ≤ R ≤ D_E`, use the
bounded union of fixed `r_*`-root certificates, combined by a finite Borel assignment of their
testing regions (preserving the point-scale partition), with the scales `r_* ≤ r < R` declared
bad and the radius sum normalized by `μ(P₀)`. -/
theorem exists_bounded_forward_approximants :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular → μ ≠ 0 →
      Bornology.IsBounded μ.support → 0 < Metric.diam μ.support →
      (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) →
      (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → r ≤ Metric.diam μ.support →
        ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball z r)) →
      carlesonEnergy μ k < ⊤ → ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R →
        ∃ 𝒞 : RegularMixedCovering k (C * (1 + (carlesonEnergy μ k).toReal)) L₀ μ a R,
          ∃ FH FV : Set (Space n), 𝒞.IsTypedTraceSplit FH FV ∧ 𝒞.MeasureIdentity FH FV ∧
            𝒞.RelativeTail ((2 : ℝ) ^ k + A ^ 2) := by
  exact dp2_exists_bounded_forward_approximants

end ParabolicRectifiability.QuantitativeCharacterization
