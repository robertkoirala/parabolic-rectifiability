import ParabolicRectifiability.BetaP.Proofs.Support.Interfaces
import ParabolicRectifiability.BetaP.Statements.Laws
import ParabolicRectifiability.Measure.Neck.DensitySelection
import ParabolicRectifiability.BetaP.Proofs.Carrier.Existence
import ParabolicRectifiability.BetaP.Proofs.Packing.ActiveRadiusPacking
import ParabolicRectifiability.BetaP.Proofs.Laws.ZeroEnergy
import ParabolicRectifiability.BetaP.Proofs.Localization.Existence
import ParabolicRectifiability.BetaP.Proofs.Laws.ScaleThreshold
import ParabolicRectifiability.BetaP.Proofs.Laws.ScaleTransport
import ParabolicRectifiability.BetaP.Proofs.Laws.Clamping
import ParabolicRectifiability.BetaP.Assembly.Existence
import ParabolicRectifiability.BetaP.Proofs.Laws.Annulus
import ParabolicRectifiability.BetaP.Proofs.Laws.Unavailable
import ParabolicRectifiability.BetaP.Proofs.Packing.Variants

/-! # Outer statements for the beta-`p` laws, packing and support theorem

The theorems below state the intermediate results used to prove the beta-`p` support theorem:
laws of `B_p`, active-radius packing, localization, the `p`-carrier, finite assembly, the
zero-error bridge, and scaling. Each docstring gives the mathematical content. No statement
assumes its own conclusion, its parent's conclusion, or an unstated packing, content, density
or regularity hypothesis. Constants are exposed as existentials in the order in which they are
combined.

The quadratic discrete packing theorem is `discrete_packing_proof`, whose conclusion is the
predicate `DiscretePackingBound n C₀`; the packing bootstrap below takes that predicate as
its input and `activeRadiusPacking_bounds` supplies it.

Four of the statements restate laws of `B_p` (`betaPow_clamping`, `betaPow_measurability`,
`betaPow_annulus`, and `unavailableFamily`), so that the proofs can use the laws without
depending on the final theorems.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## Laws of `B_p` used in the proofs -/

/-- **Clamping law.** Density-free clamping comparisons: `B_2 ≤ 2^{2-p} B_p` (`p ≤ 2`) and
`B_p ≤ 2^{p-2} B_2` (`p ≥ 2`); this is `BetaPowClampingStatement`. Used for the `T_p`
reduction of the support theorem and the `T_p` rows of the classification. -/
theorem betaPowClamping_law : BetaPowClampingStatement := cclamp_betaPowClamping_proof

/-- **Measurability law.** Borel measurability of `B_p`, `S_p^a`, `T_p^a`; this is
`BetaPowMeasurabilityStatement`. Fit attainment on bounded testing balls is used separately in
`squareEnergy_eq_zero_of_energyS_eq_zero`. Used in the Chebyshev step of the integrated
rates. -/
theorem betaPowMeasurability_law : BetaPowMeasurabilityStatement := cfit_betaPowMeasurability_proof

/-- **Finite annuli.** This is `BetaPowAnnulusStatement`. Used for endpoint invariance in the
classification. -/
theorem betaPowAnnulus_law : BetaPowAnnulusStatement := by exact ParabolicRectifiability.BetaP.c2_betaPowAnnulus_proof

/-- **Unavailable family.** This is `UnavailableFamilyStatement`. Used for endpoint invariance
in the classification for an unavailable family. -/
theorem unavailableFamily_law : UnavailableFamilyStatement := by exact ParabolicRectifiability.BetaP.c2_unavailableFamily_proof

/-! ## Active-radius packing -/

/-- **Active-radius packing (bootstrap).** Main and truncated assertions.
The quadratic discrete packing bound `DiscretePackingBound n C₀`
(truncated form) bounds a packing in a parent ball `P(q,R)` by `C₀ (b + B) R^k`.
Let `Λ = sup_{x,s} s^{-k} Σ_{r_i ≤ s, z_i ∈ P(x,s)} b_i r_i^k ≤ Nb` be the active-radius
density. For `x, r`, the retained source `σ_I` (`r_i ≤ r`, `z_i ∈ P(x,r)`) has its packing balls
in the doubled parent `P(x,2r)`; restriction and Hölder bound its quadratic tails by
`Λ^{1-2/p} B`, so the quadratic bound at radius `2r` gives
`r^{-k} σ_I(X) ≤ 2^k C₀ (b + Λ^{1-2/p} B)`. Since `k < n+2`, `2^k ≤ 2^{n+1}`, and the factor
`2^k` is absorbed into the dimensional multiple `D = 2^{n+1} C₀` of the quadratic constant:
`Λ ≤ D (b + Λ^{1-2/p} B)` (at `p = 2` the density power is omitted: `Λ ≤ D (b + B)`). If
`Λ > 2Db` then `Λ/2 < D Λ^{1-2/p} B`, i.e. `Λ < (2DB)^{p/2}`; hence
`Λ ≤ max{2D, (2D)^{p/2}} (b + B^{p/2})` and `σ(X) ≤ Λ R^k`, both for the full source and for
the testing sources `σ_s` retaining `r_j ≤ s`. The output constant
`C = max{2D, (2D)^{p/2}}` depends only on `n, p, C₀`. The counterexamples (a single atom has
infinite unfiltered density, and `|t|^{p/2}` fails Jensen for `p < 2`) explain the
active-radius filter and the guard `p ≥ 2`. Used for the five packing statements and, through
them, for `exists_p_carrier`. -/
theorem activeRadiusPacking_of_discretePacking (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 2 ≤ p)
    (C₀ : ℝ) (hC₀ : 0 < C₀) (hdisc : DiscretePackingBound n C₀) :
    ∃ C : ℝ, 0 < C ∧ ActiveRadiusPackingBound n p C ∧ ActiveRadiusPackingTruncatedBound n p C := by
  exact cpk_activeRadiusPacking_of_discretePacking n hn p hp C₀ hC₀ hdisc

/-- **Active-radius packing, variants.** Unit parent with endpoint two and exceptional indices.
From the all-scale active-radius bound with constant `C`, remove the radii `≥ 1/100` (ambient
disjoint volume), partition the rest into cells of diameter `≤ 1/100`, convert the endpoint-two
tail of each restricted cell source to an all-scale tail by the exact tail formula, sum the
cells; deleting exceptional indices costs exactly their weight `Γ`. Used for the packing
statements. -/
theorem activeRadiusPacking_variants (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 2 ≤ p) (C : ℝ)
    (hC : 0 < C) (hmain : ActiveRadiusPackingBound n p C) :
    ∃ C' : ℝ, 0 < C' ∧ ActiveRadiusPackingUnitParentBound n p C' ∧
      ActiveRadiusPackingExceptionalBound n p C' ∧
      ActiveRadiusPackingUnitParentExceptionalBound n p C' := by
  exact ParabolicRectifiability.BetaP.c2_activeRadiusPacking_variants n hn p hp C hC hmain

/-! ## The support theorem: the positive `S_p` branch (`p ≥ 2`, `k < n+2`, `M > 0`) -/

/-- **Small-diameter localization and the exact tail.** There is a dimensional number `N` of disjoint Borel
pieces of the good set `P(0,1) ∩ {S_p^2 ≤ M}` (fixed grid of radius-`1/64` cylinders), each actual restriction finite,
inner regular, supported in its closed cylinder, and with `∫_0^∞ β_{p,ν_i}^2 ds/s ≤ 2M` at
`ν_i`-almost every point (restriction monotonicity plus the exact tail
`∫_2^∞ = (2^{q_p}-1)^{-1} ∫_1^2`, `q_p = 2 + 2k/p`). `N` depends only on `n`. The radius
`1/64` and the all-scale bound `2M` are what `exists_p_carrier` consumes. Used in
`positive_p_branch`. -/
theorem exists_p_localization (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 0 < N ∧ ∀ p : ℝ, 0 < p → ∀ k : ℕ, 1 ≤ k → k < n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M : ℝ, 0 ≤ M → Nonempty (PLocalization μ k T p M N) := by
  exact cloc_exists_p_localization n hn

/-- **The `p`-carrier of one localized source.** For a finite inner-regular `ν` supported in
`P̄(c,1/64)` with all-scale `S_p` bound `2M` a.e., the compact lower-mass carrier `K_a`,
`a = (2M)^{p/2}`, loses at most `C M^{p/2}` (first-doubling selection and the `p`-power barycenter
transfer into the truncated active-radius packing), has net/Hausdorff/tube bounds (synthetic
weights into the full-source packing) and finite variable-radius packing (its own transfer), and
`η = H_P^k⌊K_a` has finite `S_{2,η,T}^1` a.e. (domination `η ≤ C a^{-1} ν`, amplitude law, Hölder
with the proved upper growth of `η`). The two packing statements are its inputs. It
states the optimized choice `a = (2M)^{p/2}`, not the general `K_a` estimates. The
graph-coverage conclusion of the carrier is not part of this statement; it is supplied by
`typedSplit_exists` from the finite-Hausdorff criterion. The proof uses first-doubling
selection, the common-plane `p`-power barycenter transfer, equal-radius nets, variable-radius
packing (with its own argument), and domination and energy transfer. Used in
`positive_p_branch`. -/
theorem exists_p_carrier (hpack : ActiveRadiusPackingStatement)
    (htrunc : ActiveRadiusPackingTruncatedStatement) (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν.InnerRegular →
      ∀ c : Space n, ν.support ⊆ Metric.closedBall c (1 / 64) →
      ∀ M : ℝ, 0 < M →
      (∀ᵐ z ∂ν, allScaleEnergyP ν k T p z ≤ ENNReal.ofReal (2 * M)) →
        Nonempty (PCarrier ν k T p M C) := by
  exact CarrierTree.ccar_exists_p_carrier hpack htrunc n hn p hp

/-- **Compactification and finite assembly.** Given the localization, the carriers
`K_i` (constant `C_c`) and their Borel typings `H_i ⊔ V_i = K_i`, choose compact
`A_{T,i} ⊆ T_i ∩ P(0,1)` by inner regularity of `ν_i` with total omitted mass `≤ M^{p/2}`, put
`μ_T = Σ_i ν_i⌊A_{T,i}` and `μ⁺ = μ - μ_H - μ_V`; then the loss is at most
`Γ + N C_c M^{p/2} + M^{p/2}`, the actual supports are compact subsets of finite unions of the
`A_{T,i}` inside `P̄(0,1)` with own-type covers at every tolerance, and all Hausdorff, net, tube
and variable-radius bounds follow by finite summation (each packing centre assigned to its first
`K_i`; countable packing from finite partial sums). `C` depends only on `n, p, N, C_c`.
Used in `positive_p_branch`. -/
theorem exists_assembled_p_decomposition (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 2 ≤ p) (N : ℕ)
    (Cc : ℝ) (hCc : 0 < Cc) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 < M → 0 ≤ Γ →
      μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyS μ k T p 2 z}) ≤
        ENNReal.ofReal Γ →
      ∀ (S : PLocalization μ k T p M N)
        (K : ∀ i : Fin S.count, PCarrier (μ.restrict (S.region i)) k T p M Cc)
        (_D : ∀ i : Fin S.count, TypedSplit k T (K i).set),
        ∃ μplus μH μV : Measure (Space n),
          IsBetaPDecomposition k T C (point 0 0) 1 (C * M ^ (p / 2) + Γ) μ μplus μH μV := by
  exact casm_exists_assembled_p_decomposition n hn p hp N Cc hCc

/-! ## The support theorem: zero budget and the localized clause -/

/-- **The zero-error bridge.** For a locally Radon source and an available family, `S_{p,μ,T}^a(z) = 0` forces `B_p(z,r) = 0` for almost every `r < a`; on each
such bounded testing ball the `p`-fit is attained by an admissible plane carrying `μ⌊P(z,r)`, so
`B_2(z,r) = 0` and `S_{2,μ,T}^a(z) = 0`. Used in the zero-budget case of the unit clause,
which then invokes the rectifiable Reifenberg theorem at `M = 0` (no limit of positive-threshold
supports). -/
theorem squareEnergy_eq_zero_of_energyS_eq_zero {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {T : FamilyKind} (hT : Nonempty (Models n k T)) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) {p : ℝ} (hp : 0 < p) {a : ℝ}
    (ha : 0 < a) {z : Space n} (h : energyS μ k T p a z = 0) :
    squareEnergy μ k T a z = 0 := by
  exact cfit_squareEnergy_eq_zero_of_energyS_eq_zero_proof hn hk hkn hT hμ hreg hp ha h

/-- **Thresholds of a rescaled source.** Normalized rescaling of the source and of both
thresholds: `μ^{q,R} = R^{-k} (δ_{1/R}(·-q))_# μ` (`rescaledSource`) is locally Radon,
and, by the energy dilation identity with endpoint `2R`, its unit thresholds are exactly `R^{-k}`
times the localized thresholds of `μ` on `P(q,R)`, for `S_p` and for `T_p`, as outer measures.
Used for the localized clause. -/
theorem rescaledSource_betaP_threshold {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) (T : FamilyKind) (μ : Measure (Space n)) (hμ : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular) (q : Space n) (R : ℝ) (hR : 0 < R) (p : ℝ) (hp : 0 < p) (M : ℝ) :
    IsFiniteMeasureOnCompacts (rescaledSource μ k q R hR) ∧
      (rescaledSource μ k q R hR).InnerRegular ∧
      (rescaledSource μ k q R hR) (Metric.ball (point 0 0) 1 ∩
          {z | ENNReal.ofReal M < energyS (rescaledSource μ k q R hR) k T p 2 z}) =
        (ENNReal.ofReal R)⁻¹ ^ k *
          μ (Metric.ball q R ∩ {z | ENNReal.ofReal M < energyS μ k T p (2 * R) z}) ∧
      (rescaledSource μ k q R hR) (Metric.ball (point 0 0) 1 ∩
          {z | ENNReal.ofReal M < energyT (rescaledSource μ k q R hR) k T p 2 z}) =
        (ENNReal.ofReal R)⁻¹ ^ k *
          μ (Metric.ball q R ∩ {z | ENNReal.ofReal M < energyT μ k T p (2 * R) z}) := by
  exact cscale_rescaledSource_betaP_threshold_proof hn hk hkn T μ hμ hreg q R hR p hp M

/-- **Transport of a unit decomposition** under the similarity `F(y) = q + δ_R y`.
From a decomposition of `μ^{q,R}` at `(0,1)` with constant `C` and loss `L`,
the measures `R^k F_# ν_T` decompose `μ` at `(q,R)` with the same `C` and loss `R^k L`: supports
are images under `F` (compact, in `P̄(q,R)`), horizontal slopes and general regular norms are
dilation invariant, `H_P^k` scales by `R^k`, volume by `R^{n+2}`, separated sets and packings are
preserved, so every bound becomes its scale-`R` form. Used for the localized clause. -/
theorem IsBetaPDecomposition.of_rescaledSource {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {T : FamilyKind} {μ : Measure (Space n)} {q : Space n} {R : ℝ}
    (hR : 0 < R) {C loss : ℝ} (hC : 0 < C) {νplus νH νV : Measure (Space n)}
    (h : IsBetaPDecomposition k T C (point 0 0) 1 loss (rescaledSource μ k q R hR) νplus νH νV) :
    ∃ μplus μH μV : Measure (Space n),
      IsBetaPDecomposition k T C q R (R ^ k * loss) μ μplus μH μV := by
  exact cscb_isBetaPDecomposition_of_rescaledSource_proof hn hk hkn hR hC h

end ParabolicRectifiability.BetaP
