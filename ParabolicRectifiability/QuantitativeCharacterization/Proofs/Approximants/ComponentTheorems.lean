import ParabolicRectifiability.QuantitativeCharacterization.Statements.ApproximantComponents
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.FactorialMoments
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.ExponentialTail
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.TypedSplit
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.LocalAbsoluteContinuity
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.ApproximantLimits
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.CanonicalIdentification

/-! # Intermediate lemmas for the root approximants

Each declaration below records, under a stable name, the proof of one of the named statements
of `dp2_FactorialMomentStatement` and its companions:

* `dp2_factorial_moments`: factorial moments of the multiplicity;
* `dp2_exponential_tail`: the exponential tail of the multiplicity (Markov's inequality);
* `dp2_typed_split`: the typed split and the measure identity;
* `dp2_local_absolute_continuity`: local absolute continuity with respect to `H_P^k`;
* `dp2_approximant_limits`: the limits of the approximants and of the residual;
* `dp2_canonical_identification`: canonical identification of the limits; its statement takes
  the rectifiability of absolutely continuous restrictions and of countable sums as hypotheses.

The lemmas are stated independently of each other: the exponential tail takes the factorial
moments as a hypothesis, the typed split takes trace carriage as a hypothesis, and canonical
identification takes the two rectifiability statements and the rectifiability of the limits as
hypotheses. `dp2_exists_root_approximants` and `dp2_approximant_canonical_limits` combine them.
-/

set_option autoImplicit false

noncomputable section

namespace ParabolicRectifiability.QuantitativeCharacterization

/-- **Factorial moments of the multiplicity**: `dp2_FactorialMomentStatement`.

Expand `m^p` and order each tuple's radii in nonincreasing order, at a cost of at most `p!`; the
same-family local packing bounds one step, and iterating it gives
`∫_{P₀} m^p dμ ≤ p! A S (2^k K)^{p-1}` (repeated tuple indices included).

Proof sketch.
1. One step: if `R_j ≤ R_i` and `P_j ∩ P_i ≠ ∅` then `dist(a_j, a_i) < 2R_i` and `R_j ≤ 2R_i`, so
   `𝒞.local_packing (a_i) (2R_i)` gives
   `Σ_{R_j ≤ R_i, P_j ∩ P_i ≠ ∅} ofReal(R_j)^k ≤ ofReal(K (2R_i)^k) = 2^k ofReal K ofReal(R_i)^k`
   (for `K < 0` the index set is empty: local packing at `(a_i, R_i)` fails).
2. Fix the total order `j ⪯ i :⟺ (R_j, j) ≤ (R_i, i)` lexicographically (`index ⊆ ℕ`). Define
   chain weights `f_1(i) = R_i^k`, `f_{q+1}(i) = Σ_{j ⪯ i, P_j ∩ P_i ≠ ∅} f_q(j)`; by step 1 and
   induction `f_q(i) ≤ (2^k K)^{q-1} R_i^k`.
3. Pointwise, for `z` with `I_z = {i | z ∈ P_i}` finite of size `m`:
   `m^p ≤ m.ascFactorial p = p! · #{weakly ⪯-decreasing p-sequences in I_z}`
   (`Nat.pow_succ_le_ascFactorial`, `Nat.ascFactorial_eq_factorial_mul_choose`, multisets);
   for `m = ⊤` the right side is `⊤` too (or restrict to `{m < ⊤}` after the case `p = 1`,
   which is `∫_{P₀} m = Σ_i μ(P₀ ∩ P_i) ≤ A S` directly from `dp2_multiplicity_eq_tsum` and
   `lintegral_tsum`).
4. Integrate (`lintegral_tsum`, Tonelli for counting measure): a weakly decreasing sequence with a
   common point has consecutive balls meeting, and `μ(P₀ ∩ ⋂_l P_{j_l}) ≤ μ(P_{j_p}) ≤ A R_{j_p}^k`;
   summing over chains gives `≤ A Σ_i f_p(i) ≤ A (2^k K)^{p-1} S`.
The proof in `dp2_factorial_moments_proof` organizes steps 2-4 as an induction on `p` with
weights depending on `z`.

Used with `dp2_ball_growth_of_local` for `exists_root_approximants`, at `p = 1` with
`dp2_ball_growth_of_global` for `approximant_canonical_limits`, and for the bounded-support
approximants. -/
theorem dp2_factorial_moments : dp2_FactorialMomentStatement := by
  exact dp2_factorial_moments_proof

/-- **The exponential tail of the multiplicity**: `dp2_ExponentialTailStatement`.

For any `s > 2^k K` the nonnegative exponential series of `m/s` can be integrated termwise;
Markov's inequality then bounds the residual.

Proof sketch.
1. `E(z) = Σ_{p ≥ 0} m(z)^p / (p! s^p) ∈ ℝ≥0∞` (`= exp(m/s)` if `m < ⊤`, `= ⊤` if `m = ⊤`).
2. `∫_{P₀} E dμ = μ(P₀) + Σ_{p ≥ 1} (p! s^p)⁻¹ ∫_{P₀} m^p dμ` (`lintegral_tsum`,
   `lintegral_const_mul`; the `p = 0` term is `μ(P₀)` since `m^0 = 1`), and by the hypothesis
   `≤ μ(P₀) + A S Σ_{p ≥ 1} (2^k K)^{p-1} / s^p = μ(P₀) + A S / (s - 2^k K)`
   (`ENNReal.tsum_geometric` with ratio `2^k K / s < 1`; `0 ≤ K` and `s > 2^k K` give `s > 0`).
3. On `P₀ ∩ {m > N}`, `E ≥ exp(N/s)` (`m ≥ N + 1`; the series of a finite `m` is `exp(m/s)`,
   `NormedSpace.exp_eq_tsum_div`, `Real.exp_eq_exp_ℝ`); Markov (`mul_meas_ge_le_lintegral₀`) gives
   `exp(N/s) μ(P₀ ∩ {m > N}) ≤ ∫_{P₀} E`, and `𝒞.residual N P₀ = μ(P₀ ∩ {m > N})`
   (`Measure.restrict_apply measurableSet_ball`).

Used through `dp2_relativeTail_of_exponentialTail` and `dp2_absoluteTail_of_exponentialTail`,
and for the relative tail of the bounded-support coverings (with `S ≤ A K μ(P₀)`). -/
theorem dp2_exponential_tail : dp2_ExponentialTailStatement := by
  exact dp2_exponential_tail_proof

/-- **The typed split and the measure identity**: `dp2_TypedSplitStatement`.

Enumerate the Borel traces and subtract the preceding ones to obtain disjoint typed carriers;
the exact measure identity follows level by level.

Proof sketch.
1. Every reference kind is `.horizontal` or `.vertical` (`Reference.kind`; the ambient reference
   is vertical), so `⋃_i (P_i ∩ Γ_i) = typedTrace .horizontal ∪ typedTrace .vertical`.
2. The typed traces are Borel: countable unions (`index ⊆ ℕ`) of open balls intersected with
   closed carriers (horizontal: a support, `Measure.isClosed_support`; vertical:
   `ba1_vertical_basic_proof`, which needs `1 ≤ L`; ambient: `univ`).
3. `F_H = P₀ ∩ typedTrace .horizontal`, `F_V = (P₀ ∩ typedTrace .vertical) \ typedTrace .horizontal`:
   disjoint Borel subsets of `P₀` inside their traces, and `P₀ \ (F_H ∪ F_V) ⊆
   P₀ \ ⋃_i (P_i ∩ Γ_i)` is `μ`-null by hypothesis.
4. Identity at level `N`: `F_H ∩ {m ≤ N}`, `F_V ∩ {m ≤ N}`, `P₀ ∩ {m > N}` are disjoint Borel
   (`dp2_measurableSet_multiplicity_le`, `dp2_measurableSet_lt_multiplicity`) and their
   union is a.e. equal to `P₀`; `Measure.restrict_union`, `Measure.restrict_congr_set`.

The hypothesis is supplied by `dp2_trace_carriage`. -/
theorem dp2_typed_split : dp2_TypedSplitStatement := by
  exact dp2_typed_split_proof

/-- **Local absolute continuity**: `dp2_LocalAbsoluteContinuityStatement`. Upper growth implies
`μ ≪ H_P^k`.

Proof sketch. Apply `Foundations.fgac_absolutelyContinuous_hausdorffP_of_growth_proof` to
`λ = μ⌊P₀`, `B = 2^k A`, `r₀ = R`:
* `λ` is locally Radon: `Foundations.restrict_isFiniteMeasureOnCompacts_innerRegular_proof`;
* all-centre growth for `0 < r ≤ R`: if `λ(P(p,r)) > 0`, `Measure.nonempty_inter_support_of_pos`
  gives `z ∈ P(p,r) ∩ P₀ ∩ supp μ`; then `z ∈ P(a, 2LR)` (`R ≤ 2LR`), `P(p,r) ⊆ P(z,2r)` and
  `2r ≤ 2R ≤ 2LR`, so `λ(P(p,r)) ≤ μ(P(z,2r)) ≤ A (2r)^k = 2^k A r^k` (the argument of
  `Foundations.fgac_ball_le_of_support_growth_proof`, localized).

Used for `exists_root_approximants` (`μ⌊P₀ ≪ H_P^k` makes reference-null transfer apply to the
approximants). -/
theorem dp2_local_absolute_continuity : dp2_LocalAbsoluteContinuityStatement := by
  exact dp2_local_absolute_continuity_proof

/-- **The limits of the approximants and the residual**: `dp2_ApproximantLimitsStatement`. The
retained measures increase and the residual decreases to zero in total variation.

Proof sketch.
1. Monotone / antitone: `{m ≤ N}` increases and `{m > N}` decreases in `N`;
   `Measure.restrict_mono`.
2. For `F ⊆ P₀` (no measurability of `F` is needed): put `ν = μ⌊F` and
   `H_N = {m ≤ N}`, Borel (`dp2_measurableSet_multiplicity_le`). Then
   `𝒞.approximant F N = μ⌊(F ∩ H_N) = ν⌊H_N` (`Measure.restrict_restrict`, `H_N` measurable,
   `Set.inter_comm`). Apply continuity from below to `ν` and the increasing measurable cutoffs:
   for Borel `S`, `ν⌊H_N S = ν(S ∩ H_N) → ν(S ∩ ⋃_N H_N)` (`tendsto_measure_iUnion_atTop`), and
   `⋃_N H_N = {m < ⊤}` is `ν`-conull: `{m = ⊤}` is Borel, so
   `ν{m = ⊤} = μ({m = ⊤} ∩ F) ≤ μ(P₀ ∩ {m = ⊤}) = 0` (`Measure.restrict_apply`, `F ⊆ P₀`, the
   finite-multiplicity hypothesis); hence the limit is `ν(S) = μ⌊F S`.
3. `𝒞.residual N univ = μ(P₀ ∩ {m > N})`, decreasing Borel sets
   (`dp2_measurableSet_lt_multiplicity`) of finite measure (`measure_ball_lt_top`, `Space n` is
   proper) with intersection `P₀ ∩ {m = ⊤}`, which is null (`tendsto_measure_iInter_atTop`).

Used for `approximant_canonical_limits`. -/
theorem dp2_approximant_limits : dp2_ApproximantLimitsStatement := by
  exact dp2_approximant_limits_proof

/-- **Canonical identification**: `dp2_CanonicalIdentificationStatement`. The two limiting
restrictions give a full typed decomposition; the canonical-decomposition theorem identifies them
with the unique horizontal and regular-vertical parts, and its pure remainder is zero. The
competitor is `ρ_H = μ⌊F_H + μ_H⌊Pᶜ`, `ρ_V = μ⌊F_V + μ_V⌊Pᶜ`, `ρ_P = μ_+⌊Pᶜ`.

Proof sketch.
1. `μ = μ⌊P + μ⌊Pᶜ` (`Measure.restrict_add_restrict_compl`); `μ⌊P = μ⌊F_H + μ⌊F_V`
   (`Measure.restrict_congr_set`, the remainder is null; `Measure.restrict_union`);
   `μ⌊Pᶜ = μ_H⌊Pᶜ + μ_V⌊Pᶜ + μ_+⌊Pᶜ` (`measure_eq`, `Measure.restrict_add`). Hence
   `μ = ρ_H + ρ_V + ρ_P`.
   Steps 2-3 use only the two hypotheses `hS1` (rectifiability of absolutely continuous
   restrictions) and `hS2` (rectifiability of countable sums, at universe `0`).
2. `ρ_H` is horizontally rectifiable: `μ_H⌊Pᶜ ≪ μ_H` and `horizontal_rectifiable` with `hS1`;
   the binary sum by `hS2` at `ι = Bool` (`Measure.sum_cond`). Likewise `ρ_V`.
3. `ρ_P` is graph-pure: `ρ_P ≤ μ_+` on every set (`Measure.restrict_le_self`, `Measure.le_iff'`)
   and `pure_graphPure`.
4. The field `unique` of `IsCanonicalDecomposition` gives `ρ_H = μ_H`, `ρ_V = μ_V`. Restrict to
   `P`: `(μ⌊F_H)⌊P = μ⌊F_H` (`Measure.restrict_restrict_of_subset`) and `(μ_H⌊Pᶜ)⌊P = 0`.
   `horizontalPart μ k 1` is by definition `μ.restrict {z | squareEnergy μ k .horizontal 1 z < ⊤}`.

The hypotheses `hS1`, `hS2` are supplied in `dp2_approximant_canonical_limits` by
`Foundations.f2i_isRegularlyRectifiableMeasure_of_absolutelyContinuous` and
`Foundations.f2i_isRegularlyRectifiableMeasure_sum`. -/
theorem dp2_canonical_identification : dp2_CanonicalIdentificationStatement := by
  exact dp2_canonical_identification_proof

end ParabolicRectifiability.QuantitativeCharacterization
