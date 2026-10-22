import ParabolicRectifiability.Foundations.BetaPow
import ParabolicRectifiability.Foundations.SupportBounds
import Mathlib.MeasureTheory.Measure.Support

/-! # Statements: the beta-`p` support theorem and active-radius packing

The proposition definitions specify the public interfaces; their proofs are the theorems
`betaP_support_theorem` and `activeRadiusPacking`, ….

**The decomposition is a nonnegative measure decomposition** `μ = μ⁺ + μ_H + μ_V`, not a
decomposition into restrictions of `μ`: no restriction-decomposition claim is made. The good
measures are carried by the open ball, their actual supports `K_T = supp μ_T` are the typed sets of
the support bundle `Foundations.HasRegularSupportBounds`, whose graph covers are of
the support's own type: horizontal subset graphs for `K_H`, full general regular vertical graphs for
`K_V`, at every positive tolerance.

Conventions. `P(q,R)` is `Metric.ball q R`; `S_p^a`, `T_p^a`, `B_p` are `Foundations.energyS`,
`Foundations.energyT`, `Foundations.betaPow`. The family is any `T` with `Nonempty (Models n k T)`
(the mixed family, or an available fixed family). "Locally Radon" is `IsFiniteMeasureOnCompacts μ`
together with `μ.InnerRegular`. Numerical data are real, compared through `ENNReal.ofReal`;
`M^{p/2}` is the real power, and `0^{p/2} = 0` because `p/2 ≠ 0`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## The support theorem -/

/-- The conclusion of the support theorem at centre `a` and radius `R`, for the family `T`, with
constant `C` and loss bound `loss`:
* a nonnegative decomposition `μ = μ⁺ + μ_H + μ_V`;
* the loss bound `μ⁺(P(a,R)) ≤ loss`;
* the good measures are carried by `P(a,R)`;
* unavailable types and, for a fixed family, the disallowed type have zero measure;
* the actual supports `K_H = supp μ_H`, `K_V = supp μ_V` satisfy the support bundle
  `HasRegularSupportBounds k C a R K_H K_V`: compact subsets of `P̄(a,R)`, own-type graph covers at
  every positive tolerance, `H_P^k(K) ≤ C R^k`, and the local Hausdorff, separated-set, tube and
  finite/countable variable-radius packing bounds.
The measures, hence the supports, are fixed before every graph tolerance. -/
structure IsBetaPDecomposition {n : ℕ} (k : ℕ) (T : FamilyKind) (C : ℝ) (a : Space n) (R : ℝ)
    (loss : ℝ) (μ μplus μH μV : Measure (Space n)) : Prop where
  measure_eq : μ = μplus + μH + μV
  remainder_bound : μplus (Metric.ball a R) ≤ ENNReal.ofReal loss
  horizontal_carried : μH (Metric.ball a R)ᶜ = 0
  vertical_carried : μV (Metric.ball a R)ᶜ = 0
  horizontal_unavailable : ¬ (1 ≤ k ∧ k ≤ n) → μH = 0
  vertical_unavailable : ¬ (2 ≤ k ∧ k ≤ n + 2) → μV = 0
  horizontal_disallowed : T = .vertical → μH = 0
  vertical_disallowed : T = .horizontal → μV = 0
  supports : HasRegularSupportBounds k C a R μH.support μV.support

/-- **The beta-`p` support theorem.**

For every `n ≥ 1` and every real `0 < p < ∞` there is one constant `C = C(n,p) > 0` such that, for
every `1 ≤ k ≤ n+2`, every mixed or available fixed family `T` and every locally Radon `μ`:
1. *Unit clause.* For real `0 ≤ M, Γ`:
   * if `2 ≤ p` and `μ(P(0,1) ∩ {S_{p,μ,T}^2 > M}) ≤ Γ`, there is a decomposition with
     `μ⁺(P(0,1)) ≤ C M^{p/2} + Γ`;
   * if `p ≤ 2` and `μ(P(0,1) ∩ {T_{p,μ,T}^2 > M}) ≤ Γ`, there is a decomposition with
     `μ⁺(P(0,1)) ≤ C M + Γ`;
   in both cases with all support conclusions at centre `0`, radius `1`. At `M = 0` the loss is
   `C·0^{p/2} + Γ = Γ` (resp. `C·0 + Γ = Γ`) exactly.
2. *Localized clause.* For every centre `q`, radius `R₀ > 0` and real
   `0 ≤ M, Γ`: the threshold on `P(q,R₀)` with scale endpoint `2R₀` gives a decomposition with
   losses `C M^{p/2} R₀^k + Γ`, resp. `C M R₀^k + Γ`, good measures carried by `P(q,R₀)`, and the
   support bundle at centre `q`, radius `R₀` (supports in `P̄(q,R₀)`, global Hausdorff bound
   `C R₀^k`, local Hausdorff and packing bounds `C s^k` for `0 < s ≤ R₀`, separated-set bounds
   `C (s/r)^k` for `0 < r ≤ s`, tube bound `C R₀^k r^{n+2-k}` for `0 < r ≤ R₀`, arbitrary graph
   tolerances).
3. *Ambient clause.* At `k = n+2` there is a decomposition with
   `μ⁺(P(0,1)) = 0` (loss `0`) and all support conclusions at centre `0`, radius `1`, without any
   energy assumption. -/
def BetaPSupportStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      (∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
        (2 ≤ p →
          μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyS μ k T p 2 z}) ≤
            ENNReal.ofReal Γ →
          ∃ μplus μH μV : Measure (Space n),
            IsBetaPDecomposition k T C (point 0 0) 1 (C * M ^ (p / 2) + Γ) μ μplus μH μV) ∧
        (p ≤ 2 →
          μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyT μ k T p 2 z}) ≤
            ENNReal.ofReal Γ →
          ∃ μplus μH μV : Measure (Space n),
            IsBetaPDecomposition k T C (point 0 0) 1 (C * M + Γ) μ μplus μH μV)) ∧
      (∀ (q : Space n) (R₀ : ℝ), 0 < R₀ → ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
        (2 ≤ p →
          μ (Metric.ball q R₀ ∩ {z | ENNReal.ofReal M < energyS μ k T p (2 * R₀) z}) ≤
            ENNReal.ofReal Γ →
          ∃ μplus μH μV : Measure (Space n),
            IsBetaPDecomposition k T C q R₀ (C * M ^ (p / 2) * R₀ ^ k + Γ) μ μplus μH μV) ∧
        (p ≤ 2 →
          μ (Metric.ball q R₀ ∩ {z | ENNReal.ofReal M < energyT μ k T p (2 * R₀) z}) ≤
            ENNReal.ofReal Γ →
          ∃ μplus μH μV : Measure (Space n),
            IsBetaPDecomposition k T C q R₀ (C * M * R₀ ^ k + Γ) μ μplus μH μV)) ∧
      (k = n + 2 →
        ∃ μplus μH μV : Measure (Space n),
          IsBetaPDecomposition k T C (point 0 0) 1 0 μ μplus μH μV)

/-! ## Active-radius packing -/

/-- The atomic source `σ = Σ_i b_i r_i^k δ_{z_i}` of a finite weighted family. -/
def atomicSource {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) :
    Measure (Space n) :=
  ∑ i, ENNReal.ofReal (w i * r i ^ k) • Measure.dirac (z i)

/-- The testing source at scale `s` retaining only the indices with `r_j ≤ s`:
`σ_s = Σ_{r_j ≤ s} b_j r_j^k δ_{z_j}`. -/
def truncatedAtomicSource {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (s : ℝ) :
    Measure (Space n) :=
  ∑ i ∈ Finset.univ.filter (fun i => r i ≤ s), ENNReal.ofReal (w i * r i ^ k) • Measure.dirac (z i)

/-- The hypotheses on the finite family in the packing statements: finitely
many pairwise disjoint open balls `P(z_i,r_i) ⊆ P(q,R)` of positive radii, with weights
`0 < b_i ≤ b`. This is a bundle of hypotheses only. -/
structure IsWeightedPacking {n N : ℕ} (q : Space n) (R : ℝ) (z : Fin N → Space n)
    (r w : Fin N → ℝ) (b : ℝ) : Prop where
  radius_pos : ∀ i, 0 < r i
  ball_subset : ∀ i, Metric.ball (z i) (r i) ⊆ Metric.ball q R
  pairwise_disjoint : ∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))
  weight_pos : ∀ i, 0 < w i
  weight_le : ∀ i, w i ≤ b

/-- Active-radius packing, main assertion. For `n ≥ 1` and `2 ≤ p < ∞` there is `C = C(n,p) > 0` such that for `1 ≤ k < n+2`, every
available family `T`, every finite weighted packing of `P(q,R)` with weights `0 < b_i ≤ b`, and
real `B ≥ 0`: if `∫_{r_i}^∞ β_{p,σ,T}(z_i,s)^2 ds/s ≤ B` for every `i`, then
`σ(X) ≤ C (b + B^{p/2}) R^k`. Here `β_p^2 = B_p^{2/p}` and the tail is over `(r_i,∞)` against
`scaleMeasure`. -/
def ActiveRadiusPackingStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ (q : Space n) (R : ℝ), 0 < R →
    ∀ (N : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (b B : ℝ),
      IsWeightedPacking q R z r w b → 0 ≤ B →
      (∀ i, (∫⁻ s in Ioi (r i),
          betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure) ≤
        ENNReal.ofReal B) →
      atomicSource k z r w univ ≤ ENNReal.ofReal (C * (b + B ^ (p / 2)) * R ^ k)

/-- Active-radius packing, truncated testing sources: the
same conclusion when, at each scale `s`, the testing source is `σ_s`, which retains only the
indices `r_j ≤ s`. -/
def ActiveRadiusPackingTruncatedStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ (q : Space n) (R : ℝ), 0 < R →
    ∀ (N : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (b B : ℝ),
      IsWeightedPacking q R z r w b → 0 ≤ B →
      (∀ i, (∫⁻ s in Ioi (r i),
          betaPow (truncatedAtomicSource k z r w s) k T p (z i) s ^ (2 / p) ∂scaleMeasure) ≤
        ENNReal.ofReal B) →
      atomicSource k z r w univ ≤ ENNReal.ofReal (C * (b + B ^ (p / 2)) * R ^ k)

/-- Active-radius packing, unit parent with endpoint two: for packings of a unit ball `P(q,1)`, the tail hypothesis integrated only over
`(r_i, 2)` gives `σ(X) ≤ C (b + B^{p/2})`. -/
def ActiveRadiusPackingUnitParentStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ q : Space n,
    ∀ (N : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (b B : ℝ),
      IsWeightedPacking q 1 z r w b → 0 ≤ B →
      (∀ i, (∫⁻ s in Ioo (r i) 2,
          betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure) ≤
        ENNReal.ofReal B) →
      atomicSource k z r w univ ≤ ENNReal.ofReal (C * (b + B ^ (p / 2)))

/-- Active-radius packing, exceptional indices: if the
all-scale tail hypothesis for the full source `σ` holds at every index outside a set `E` of indices
of total weight `Σ_{i ∈ E} b_i r_i^k ≤ Γ`, then `σ(X) ≤ C (b + B^{p/2}) R^k + Γ` (coefficient one
on `Γ`). -/
def ActiveRadiusPackingExceptionalStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ (q : Space n) (R : ℝ), 0 < R →
    ∀ (N : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (b B : ℝ),
      IsWeightedPacking q R z r w b → 0 ≤ B →
    ∀ (E : Finset (Fin N)) (Γ : ℝ), (∑ i ∈ E, w i * r i ^ k) ≤ Γ →
      (∀ i, i ∉ E → (∫⁻ s in Ioi (r i),
          betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure) ≤
        ENNReal.ofReal B) →
      atomicSource k z r w univ ≤ ENNReal.ofReal (C * (b + B ^ (p / 2)) * R ^ k + Γ)

/-- Active-radius packing, exceptional indices for the unit-parent form (this adds exactly `Γ`
to either conclusion): for packings of `P(q,1)` and tails over
`(r_i, 2)` holding outside indices of total weight at most `Γ`, `σ(X) ≤ C (b + B^{p/2}) + Γ`. -/
def ActiveRadiusPackingUnitParentExceptionalStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ q : Space n,
    ∀ (N : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (b B : ℝ),
      IsWeightedPacking q 1 z r w b → 0 ≤ B →
    ∀ (E : Finset (Fin N)) (Γ : ℝ), (∑ i ∈ E, w i * r i ^ k) ≤ Γ →
      (∀ i, i ∉ E → (∫⁻ s in Ioo (r i) 2,
          betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure) ≤
        ENNReal.ofReal B) →
      atomicSource k z r w univ ≤ ENNReal.ofReal (C * (b + B ^ (p / 2)) + Γ)

end ParabolicRectifiability.BetaP
