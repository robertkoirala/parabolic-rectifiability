import ParabolicRectifiability.BetaP.Proofs.Support.Interfaces
import ParabolicRectifiability.Measure.Neck.DensitySelection

/-! # Statements for the `p`-carrier

Named statements (propositions only) from which `ccar_exists_p_carrier` assembles
`exists_p_carrier`; they are proved by the theorems `ccar_cells_packing`, `ccar_loss`, …. An
auxiliary statement that needs another one is stated in implication form.

**The carrier.** For a finite source `ν` and `a > 0` the carrier is
`densityCarrier ν k a = K_a = {z ∈ supp ν : ν(P̄(z,r)) ≥ a r^k for 0 < r ≤ 1}`; no new carrier is
defined. The assembly takes `L = 2M` (the all-scale bound of the existence statement) and
`a = L^{p/2} = (2M)^{p/2}`, so `1 + L^{p/2}/a = 2` and `a + L^{p/2} = 2·2^{p/2} M^{p/2}`.

**Shape of the argument.** The quadratic version of this whole carrier is proved by
`density_selection_of_discrete` and `variable_radius_packing_of_discrete`, driven by the barycenter
cells `FiniteBarycenterCells`. The `p`-version keeps the same cells and replaces two quadratic
steps:

* the fixed-model Jensen transfer becomes the `p`-power transfer for one common model before
  minimization (`CellsFitTransferStatement`, convexity of `d_P(·,L)^p` for `p ≥ 2`);
* the quadratic discrete packing (`DiscretePackingBound`) becomes the truncated active-radius
  packing bound `ActiveRadiusPackingTruncatedBound n p Ct`, a hypothesis of `exists_p_carrier`
  (`CellsPackingStatement`, with the energy transfer `2^{2(k+p)/p}`).

The three general `K_a` estimates of BP (`CarrierLossStatement`, `CarrierSeparatedStatement`,
`CarrierVariablePackingStatement`) consume `CellsPackingStatement`; the content bounds come from
the separated-set bound by the generic `ContentOfSeparatedStatement`; the own-Hausdorff energy of
`η = H_P^k⌊K` comes from `CarrierEnergyStatement` (domination `η ≤ C a^{-1} ν` is the general
`restrict_hausdorffP_densityCarrier_le`, used directly in the assembly). Selection (first
doubling scale, deficient radii), compactness, Hausdorff/tube-from-nets and domination are
general lemmas and are used directly, not restated.

Conventions: `P(z,r)` is `Metric.ball z r`, `P̄(z,r)` is `Metric.closedBall z r`; `B_p` is
`Foundations.betaPow`; `∫_0^∞ β_p^2 ds/s` is `allScaleEnergyP`; real constants are compared
through `ENNReal.ofReal`; `L^{p/2}` and `2^{k+p}` are real powers (`Real.rpow`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP.CarrierTree

open ParabolicRectifiability.Foundations

/-! ## The `p`-power barycenter transfer -/

/-- **Fixed-model `p`-power barycenter transfer.**
For `p ≥ 2`, finitely many barycenter cells `D` of a source `ν`, a cell `i` and a scale
`s ≥ D.cutoff i`, and **one fixed model** `L` of any family:
`fit_p(λ_s; L, c_i, s) ≤ A · fit_p(ν; L, y_i, 2s)`, where `λ_s = D.atomicMeasure s` is the
cutoff atomic source `Σ_{ρ_j ≤ s} w_j δ_{c_j}` at the barycenters `c_j`, `y_i = D.sample i` and
`A = D.A`. The model is common to all cells: Jensen is applied before any minimization.
`p`-version of `FiniteBarycenterCells.fit_atomicMeasure_le`. -/
def CellsFitTransferStatement : Prop :=
  ∀ (n k : ℕ) (T : FamilyKind) (p : ℝ), 2 ≤ p →
  ∀ (ν : Measure (Space n)) (l : ℕ) (D : FiniteBarycenterCells ν (Fin l)) (i : Fin l) (s : ℝ),
    D.cutoff i ≤ s → ∀ L : Models n k T,
      fitPow (D.atomicMeasure s) p L (D.barycenter i) s ≤
        ENNReal.ofReal D.A * fitPow ν p L (D.sample i) (2 * s)

/-- **Barycenter cells into the truncated active-radius packing.** Let `Ct` be a constant of the
truncated packing bound (`ActiveRadiusPackingTruncatedBound n p Ct`, `p ≥ 2`). Let `D` be
barycenter cells of `ν` whose samples have all-scale energy `≤ L`, whose cutoff balls
`P(c_i, ρ_i)` (`ρ_i = D.cutoff i`) are pairwise disjoint and lie in `P(q,R)`, and whose weights
satisfy `w_i ≤ b ρ_i^k`. Then `Σ_i w_i ≤ Ct (b + A 2^{k+p} L^{p/2}) R^k`.
(The energy bound of the atoms is `B = (A 2^{k+p})^{2/p} L`, and `B^{p/2} = A 2^{k+p} L^{p/2}`.)
`p`-version of `sum_weight_le_of_barycenterCells`. -/
def CellsPackingStatement : Prop :=
  ∀ (n : ℕ) (p Ct : ℝ), 2 ≤ p → ActiveRadiusPackingTruncatedBound n p Ct →
  ∀ (k : ℕ) (T : FamilyKind), 1 ≤ k → k < n + 2 → Nonempty (Models n k T) →
  ∀ (ν : Measure (Space n)) (l : ℕ) (D : FiniteBarycenterCells ν (Fin l)) (L : ℝ), 0 ≤ L →
    (∀ i, allScaleEnergyP ν k T p (D.sample i) ≤ ENNReal.ofReal L) →
    ∀ (q : Space n) (R b : ℝ), 0 < R → 0 < b →
    (∀ i, Metric.ball (D.barycenter i) (D.cutoff i) ⊆ Metric.ball q R) →
    (∀ i j, i ≠ j → Disjoint (Metric.ball (D.barycenter i) (D.cutoff i))
      (Metric.ball (D.barycenter j) (D.cutoff j))) →
    (∀ i, D.weight i ≤ b * D.cutoff i ^ k) →
    ∑ i, ENNReal.ofReal (D.weight i) ≤
      ENNReal.ofReal (Ct * (b + D.A * (2 : ℝ) ^ ((k : ℝ) + p) * L ^ (p / 2)) * R ^ k)

/-! ## The general `K_a` estimates -/

/-- **Loss of the lower-mass carrier.** For the truncated packing constant `Ct`
there is `C = C(n,p,Ct)` such that every finite `ν` supported in `P̄(c,1/16)` with
`∫_0^∞ β_{p,ν}^2 ds/s ≤ L` `ν`-a.e. and every `a > 0` satisfy
`ν(X ∖ K_a) ≤ C (a + L^{p/2})`. `p`-version of `measure_compl_densityCarrier_le`. -/
def CarrierLossStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ), 2 ≤ p → ∀ (Ct : ℝ), 0 < Ct →
    ActiveRadiusPackingTruncatedBound n p Ct →
  ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k → k < n + 2 → ∀ (T : FamilyKind), Nonempty (Models n k T) →
    ∀ (ν : Measure (Space n)), IsFiniteMeasure ν →
    ∀ (c : Space n), ν.support ⊆ Metric.closedBall c (1 / 16) →
    ∀ (L a : ℝ), 0 ≤ L → 0 < a → (∀ᵐ z ∂ν, allScaleEnergyP ν k T p z ≤ ENNReal.ofReal L) →
      ν (densityCarrier ν k a)ᶜ ≤ ENNReal.ofReal (C * (a + L ^ (p / 2)))

/-- The separated-set bound with constant `A` on `K` at every centre and every
`0 < r ≤ R ≤ 1`: the `separated` field of `HasMetricContentBounds k A K`. -/
def ccar_separatedBound {n : ℕ} (k : ℕ) (A : ℝ) (K : Set (Space n)) : Prop :=
  ∀ (q : Space n) (R r : ℝ), 0 < R → R ≤ 1 → 0 < r → r ≤ R →
    ∀ F : Finset (Space n), (↑F : Set (Space n)) ⊆ K ∩ Metric.ball q R →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r ≤ dist x y) → (F.card : ℝ) ≤ A * (R / r) ^ k

/-- **Local nets with synthetic weights.** For the truncated packing constant `Ct` there is
`C = C(n,p,Ct)` such that for every finite `ν` with `ν`-a.e. all-scale energy `≤ L`, every
`a > 0` and every set `K` with the all-radius lower mass `ν(P̄(z,r)) ≥ a r^k` (`z ∈ K`,
`0 < r ≤ 1`), finite `r`-separated subsets of `K ∩ P(q,R)` have at most
`C (1 + L^{p/2}/a) (R/r)^k` points (`0 < r ≤ R ≤ 1`). `p`-version of
`card_le_of_separated_densityCarrier`. -/
def CarrierSeparatedStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ), 2 ≤ p → ∀ (Ct : ℝ), 0 < Ct →
    ActiveRadiusPackingTruncatedBound n p Ct →
  ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k → k < n + 2 → ∀ (T : FamilyKind), Nonempty (Models n k T) →
    ∀ (ν : Measure (Space n)), IsFiniteMeasure ν →
    ∀ (L a : ℝ), 0 ≤ L → 0 < a → (∀ᵐ z ∂ν, allScaleEnergyP ν k T p z ≤ ENNReal.ofReal L) →
    ∀ (K : Set (Space n)), HasUniformLowerMass ν k a K →
      ccar_separatedBound k (C * (1 + L ^ (p / 2) / a)) K

/-- **Equal-radius content bounds from the separated-set bound.** Generic, no energy and no
measure: there is `C₀ = C₀(n)` such that every `K ⊆ P(c,1)` whose finite separated subsets obey
the bound with constant `A ≥ 0` has `HasMetricContentBounds k (C₀ A) K` (local Hausdorff bound
from maximal separated nets, the separated-set bound itself, and the tube bound from one net of
`K` at each scale), for every `k ≤ n + 2`. Extracted from the content bounds step of
`density_selection_of_discrete`. -/
def ContentOfSeparatedStatement : Prop :=
  ∀ (n : ℕ), ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : ℕ), k ≤ n + 2 →
    ∀ (K : Set (Space n)) (c : Space n) (A : ℝ), 0 ≤ A → K ⊆ Metric.ball c 1 →
      ccar_separatedBound k A K → HasMetricContentBounds k (C₀ * A) K

/-- **Variable-radius packing with its own transfer.** For the
truncated packing constant `Ct` there is `C = C(n,p,Ct)` such that for every finite `ν` with
`ν`-a.e. all-scale energy `≤ L`, every `a > 0` and every `K` with the all-radius lower mass of
`ν`, `HasFiniteBallPacking k (C (1 + L^{p/2}/a)) K`. Not inferred from the equal-radius nets.
`p`-version of `variable_radius_packing_of_discrete`. -/
def CarrierVariablePackingStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ), 2 ≤ p → ∀ (Ct : ℝ), 0 < Ct →
    ActiveRadiusPackingTruncatedBound n p Ct →
  ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k → k < n + 2 → ∀ (T : FamilyKind), Nonempty (Models n k T) →
    ∀ (ν : Measure (Space n)), IsFiniteMeasure ν →
    ∀ (L a : ℝ), 0 ≤ L → 0 < a → (∀ᵐ z ∂ν, allScaleEnergyP ν k T p z ≤ ENNReal.ofReal L) →
    ∀ (K : Set (Space n)), HasUniformLowerMass ν k a K →
      HasFiniteBallPacking k (C * (1 + L ^ (p / 2) / a)) K

/-! ## Energy of the carrier measure -/

/-- **Domination transfer for `B_p`** (monotonicity and amplitude). If `μ ≤ c ν` as measures for a real `c > 0`, then
`B_{p,μ}(z,r) ≤ c B_{p,ν}(z,r)` at every centre and radius, for every family. This is the
one-sided combination of monotonicity in the source and `1`-homogeneity, and replaces
`BetaPowSmulStatement` on this route, which needs only monotonicity in the measure. -/
def BetaPowDominationStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (k : ℕ), 1 ≤ k → k ≤ n + 2 → ∀ (T : FamilyKind),
  ∀ (μ ν : Measure (Space n)) (p c : ℝ), 0 < p → 0 < c → μ ≤ ENNReal.ofReal c • ν →
    ∀ (z : Space n) (r : ℝ), betaPow μ k T p z r ≤ ENNReal.ofReal c * betaPow ν k T p z r

/-- **Finite own-Hausdorff square of the carrier measure.**
Let `η = H_P^k⌊K` with `K ⊆ P(c,1)`, proved upper growth `H_P^k(K ∩ P(q,R)) ≤ U R^k`
(`0 < R ≤ 1`), and domination `η ≤ d ν` (`d > 0`), where `ν` has all-scale `S_p` energy `≤ L`
`ν`-almost everywhere. Then `S^1_{2,η,T} < ∞` `η`-almost everywhere: for `0 < r < 1`,
`B_{2,η} ≤ Θ_η^{1-2/p} B_{p,η}^{2/p} ≤ U^{1-2/p} d^{2/p} B_{p,ν}^{2/p}`, integrated over
`(0,1)`; the `ν`-null exceptional set is `η`-null by domination. The growth is a hypothesis on
the constructed `η` (supplied by the proved content bound), never on `ν`. -/
def CarrierEnergyStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (k : ℕ), 1 ≤ k → k ≤ n + 2 → ∀ (T : FamilyKind), Nonempty (Models n k T) →
  ∀ (p : ℝ), 2 ≤ p →
  ∀ (ν : Measure (Space n)) (K : Set (Space n)) (c : Space n) (U d L : ℝ), 0 < d → 0 ≤ L →
    K ⊆ Metric.ball c 1 →
    (∀ (q : Space n) (R : ℝ), 0 < R → R ≤ 1 →
      hausdorffP n k (K ∩ Metric.ball q R) ≤ ENNReal.ofReal (U * R ^ k)) →
    (hausdorffP n k).restrict K ≤ ENNReal.ofReal d • ν →
    (∀ᵐ z ∂ν, allScaleEnergyP ν k T p z ≤ ENNReal.ofReal L) →
    ∀ᵐ z ∂(hausdorffP n k).restrict K, squareEnergy ((hausdorffP n k).restrict K) k T 1 z < ⊤

end ParabolicRectifiability.BetaP.CarrierTree
