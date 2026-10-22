import ParabolicRectifiability.QuantitativeCharacterization.Coverings

/-! # Bounded-support auxiliary statements

Proposition definitions for the three auxiliary facts used to prove
`QuantitativeCharacterization.exists_bounded_forward_approximants`. Notation: `E = supp μ`,
`D_E = diam E`, `r_* = D_E / B`, `P₀ = P(a,R)`.

* `dp2_SeparatedRootCoverStatement`: finitely many support points `b_j` with
  `E ⊆ ⋃_j P(b_j, r)` and `N ≤ A² (8 D_E / r)^k` (proved through a maximal `r/2`-separated
  family; separation and maximality are not part of the formal output).
* `dp2_BandCostStatement`: the band `S × [r, R)` of point-scale pairs costs
  `μ(S) log(R/r) ≤ Q R^k` when `μ(S) ≤ Q r^k`.
* `dp2_BoundedUnionStatement`: finitely many root certificates at radius `r` covering `E`,
  combined by a finite Borel assignment of their testing regions, give a covering of `P(a,R)` for
  `R ≥ r`, with the radius sum `Σ_i R_i^k ≤ N K' r^k` (the formal output is existence and this
  bound only).

The multiplicity, tail, typed-split and trace-carriage statements used alongside these are
`dp2_FactorialMomentStatement`, `dp2_ExponentialTailStatement`, `dp2_TypedSplitStatement` and
`dp2_TraceCarriageStatement`; they are not restated here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **A bounded cover by a maximal separated family.** Let `μ` have bounded
support `E`, upper growth `μ(P(z,r)) ≤ A r^k` at all support points and radii, and lower growth
`A⁻¹ r^k ≤ μ(P(z,r))` for `0 < r ≤ D_E`. For every `0 < r ≤ D_E` there are finitely many support
points `b_0, …, b_{N-1}` with `E ⊆ ⋃_j P(b_j, r)` and `N ≤ A² (8 D_E / r)^k`. Proof idea: a
maximal `r/2`-separated subset of `E` has pairwise disjoint balls `P(b_j, r/4)`, each of mass at
least `A⁻¹ (r/4)^k`, inside `P(b_0, 2 D_E)` of mass at most `A (2 D_E)^k`. The formal conclusion
asserts only the finite cover by balls centred on `E` and the cardinality bound; it does not assert
separation or maximality, which are not needed later. -/
def dp2_SeparatedRootCoverStatement : Prop :=
  ∀ (n k : ℕ) (A : ℝ) (μ : Measure (Space n)), 0 < A →
    Bornology.IsBounded μ.support →
    (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) →
    (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → r ≤ Metric.diam μ.support →
      ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball z r)) →
    ∀ r : ℝ, 0 < r → r ≤ Metric.diam μ.support →
      ∃ (N : ℕ) (b : Fin N → Space n), (∀ j, b j ∈ μ.support) ∧
        μ.support ⊆ ⋃ j, Metric.ball (b j) r ∧
        (N : ℝ) ≤ A ^ 2 * (8 * Metric.diam μ.support / r) ^ k

/-- **The cost of the declared-bad band.** Declaring `r_* ≤ r < R` bad has extra cost at most
`μ(E) log_+(R/r_*) ≤ C R^k`. For `k ≥ 1`,
`0 < r ≤ R`, `Q ≥ 0` and a set `S` with `μ(S) ≤ Q r^k`, the point-scale measure of the band
`S × [r, R)` is at most `Q R^k`: it equals `μ(S) log(R/r)` (`dr/r` on `[r, R)`), and
`r^k log(R/r) ≤ R^k` since `log x ≤ x ≤ x^k` for `x = R/r ≥ 1`. -/
def dp2_BandCostStatement : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → ∀ (μ : Measure (Space n)) (S : Set (Space n)) (Q r R : ℝ),
    0 ≤ Q → 0 < r → r ≤ R → μ S ≤ ENNReal.ofReal (Q * r ^ k) →
      pointScaleMeasure μ (S ×ˢ Ico r R) ≤ ENNReal.ofReal (Q * R ^ k)

/-- **The bounded union of root certificates.** Let each
root `P(b_j, r)` (`j < N`) have a `(K', L')`-regular mixed covering `𝒞_j`, let the balls
`P(b_j, r)` cover `E = supp μ`, with `0 < r ≤ R`, `K' ≥ 0`, `0 < L' ≤ L`, every `P(b_j, L' r)`
inside `P(a, L R)` (`dist(b_j, a) + L' r ≤ L R`), and let the band `(P(a,R) ∩ E) × [r, R)` cost
at most `K_b R^k` (`K_b ≥ 0`). If `N K' + K_b ≤ K`, then `P(a,R)` has a `(K, L)`-regular mixed
covering whose radius sum is at most `N K' r^k`. The formal conclusion asserts only this existence
and this bound. The intended construction retains every model ball and reference of chosen
`𝒞_j` (references enlarged to `L` by `Reference.mono`), but equality with an input family is not
encoded (the inputs are only `Nonempty`), and it is not needed later. The testing regions
are combined by the finite Borel assignment `G_j = P(b_j, r) \ ⋃_{l < j} P(b_l, r)`: scale sets
`𝒰^j_i ∩ ((G_j ∩ P(a,R)) × ℝ)`, bad set `⋃_j 𝓑_j ∩ ((G_j ∩ P(a,R)) × ℝ)` together with the band
`(P(a,R) ∩ E) × [r, R)`. -/
def dp2_BoundedUnionStatement : Prop :=
  ∀ (n k : ℕ) (K' L' K L Kb : ℝ) (μ : Measure (Space n)) (a : Space n) (R r : ℝ) (N : ℕ)
    (b : Fin N → Space n),
    (∀ j, Nonempty (RegularMixedCovering k K' L' μ (b j) r)) →
    0 < r → r ≤ R → 0 ≤ K' → 0 < L' → L' ≤ L → 0 ≤ Kb →
    μ.support ⊆ ⋃ j, Metric.ball (b j) r →
    (∀ j, dist (b j) a + L' * r ≤ L * R) →
    pointScaleMeasure μ ((Metric.ball a R ∩ μ.support) ×ˢ Ico r R) ≤
      ENNReal.ofReal (Kb * R ^ k) →
    (N : ℝ) * K' + Kb ≤ K →
      ∃ 𝒞' : RegularMixedCovering k K L μ a R,
        ∑' i, ENNReal.ofReal (𝒞'.radius i) ^ k ≤ ENNReal.ofReal ((N : ℝ) * K' * r ^ k)

end ParabolicRectifiability.QuantitativeCharacterization
