import ParabolicRectifiability.BetaP.Statements.Main
import ParabolicRectifiability.BetaP.Statements.Laws
import ParabolicRectifiability.Foundations.Statements.Measurability
import ParabolicRectifiability.Measure.Neck.DensitySelection

/-! # Statements for the active-radius packing bound (bootstrap)

Named statements (definitions and propositions only) used to prove
`activeRadiusPacking_of_discretePacking`, with the constant `D = 2^{n+1} C₀`,
`C = max{2D, (2D)^{p/2}}`. They are proved by the theorems `cpk_activeSource`, … and assembled in
`cpk_activeRadiusPacking_of_discretePacking`.

For a finite family `(z_i, r_i, w_i)` (`Fin N`-indexed, as in `IsWeightedPacking`):
* `cpkActiveMass k z r w x s = Σ_{r_i ≤ s, z_i ∈ P(x,s)} w_i r_i^k` is the *active* mass seen at
  centre `x` and scale `s` (real valued);
* `CpkActiveDensityBound k z r w Λ` says that `Λ` bounds the active-radius density
  `Λ_σ = sup_{x, s > 0} s^{-k} Σ_{r_i ≤ s, z_i ∈ P(x,s)} w_i r_i^k`;
* `CpkSubfamilyTailBound k T z r w B'` is the quadratic truncated tail hypothesis of
  `DiscretePackingBound`, with bound `B'`, for **every** subfamily `(z ∘ e, r ∘ e, w ∘ e)` given
  by an injection `e : Fin l → Fin N`.

The six statements (active-source identity, Hölder reduction, bootstrap absorption, …):
1. `CpkActiveSourceStatement` (active-source identity): above its own radius, a centre sees the
   full source and the truncated testing source alike.
2. `CpkLeastActiveBoundStatement`: the active-radius density is finite (`≤ N b`) and is the
   least active bound.
3. `CpkHolderReductionStatement` (Hölder reduction): with an active bound `Λ`, the `p`-tails
   bound the quadratic truncated tails of every subfamily by `Λ^{1-2/p} B`.
4. `CpkDoubledParentStatement`: `DiscretePackingBound n C₀` on the doubled parent `P(x,2s)` turns
   quadratic subfamily tails `B'` into the active bound `2^k C₀ (b + B')`.
5. `CpkAbsorptionStatement` (bootstrap absorption), a real inequality.
6. `CpkMassBoundStatement`: `σ(X) ≤ Λ R^k` for every active bound `Λ`.

`BetaPowHolderStatement` and `Foundations.BetaPowTwoStatement` enter statement 3 as explicit
hypotheses (implication form); `DiscretePackingBound n C₀` enters statement 4 as an explicit
hypothesis, as it is a hypothesis of `activeRadiusPacking_of_discretePacking`.

**Name resolution.** `ParabolicRectifiability.truncatedAtomicSource` (the testing source of the
quadratic discrete packing bound) and `ParabolicRectifiability.BetaP.truncatedAtomicSource` (the
testing source of the `p`-version) have the same body. Both are visible here, so each occurrence
is qualified:
`BetaP.truncatedAtomicSource` and `_root_.ParabolicRectifiability.truncatedAtomicSource`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## Active mass, active density bounds and subfamily tails -/

/-- The active mass `Σ_{r_i ≤ s, z_i ∈ P(x,s)} w_i r_i^k` of the family at centre `x` and scale
`s` (membership `z_i ∈ P(x,s)` is written `dist (z i) x < s`). -/
def cpkActiveMass {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (x : Space n)
    (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => r i ≤ s ∧ dist (z i) x < s), w i * r i ^ k

/-- `Λ` bounds the active-radius density of the family: for every centre `x` and every scale
`s > 0`, `Σ_{r_i ≤ s, z_i ∈ P(x,s)} w_i r_i^k ≤ Λ s^k`. -/
def CpkActiveDensityBound {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ)
    (Λ : ℝ) : Prop :=
  ∀ (x : Space n) (s : ℝ), 0 < s → cpkActiveMass k z r w x s ≤ Λ * s ^ k

/-- Every subfamily `(z ∘ e, r ∘ e, w ∘ e)`, `e : Fin l → Fin N` injective, satisfies the
quadratic truncated tail hypothesis of `DiscretePackingBound` with bound
`B'`: at each of its centres, `∫_{r_{e j}}^∞ β_{2,σ'_s}(z_{e j}, s)^2 ds/s ≤ B'`, where `σ'_s` is
the quadratic truncated atomic source of the subfamily at scale `s`. -/
def CpkSubfamilyTailBound {n N : ℕ} (k : ℕ) (T : FamilyKind) (z : Fin N → Space n)
    (r w : Fin N → ℝ) (B' : ℝ) : Prop :=
  ∀ (l : ℕ) (e : Fin l → Fin N), Function.Injective e → ∀ j : Fin l,
    (∫⁻ s in Ioi (r (e j)),
        betaSq (_root_.ParabolicRectifiability.truncatedAtomicSource k (fun m => z (e m))
          (fun m => r (e m)) (fun m => w (e m)) s) k T (z (e j)) s ∂scaleMeasure) ≤
      ENNReal.ofReal B'

/-! ## The six statements -/

/-- **Active-source identity** (the `p`-version of the quadratic atomic truncation). For pairwise disjoint open balls of
positive radii, at a centre `z_i` and every scale `s ≥ r_i`, the full atomic source and the
truncated testing source `σ_s` (indices `r_j ≤ s`) have the same `B_p`, for every exponent `p`,
family `T` and weights. -/
def CpkActiveSourceStatement : Prop :=
  ∀ {n N : ℕ} (k : ℕ) (T : FamilyKind) (p : ℝ) (z : Fin N → Space n) (r w : Fin N → ℝ),
    (∀ i, 0 < r i) →
    (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
    ∀ (i : Fin N) (s : ℝ), r i ≤ s →
      betaPow (BetaP.truncatedAtomicSource k z r w s) k T p (z i) s =
        betaPow (atomicSource k z r w) k T p (z i) s

/-- **The least active bound.** For positive radii and weights
`0 < w_i ≤ b`, the active-radius density `Λ_σ` is finite (`≤ N b`, since each active term has
`r_i ≤ s`), nonnegative, an active bound, and the least one. -/
def CpkLeastActiveBoundStatement : Prop :=
  ∀ {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (b : ℝ),
    (∀ i, 0 < r i) → (∀ i, 0 < w i) → (∀ i, w i ≤ b) →
    ∃ Λ : ℝ, 0 ≤ Λ ∧ CpkActiveDensityBound k z r w Λ ∧
      ∀ Λ' : ℝ, CpkActiveDensityBound k z r w Λ' → Λ ≤ Λ'

/-- **Hölder reduction.** Let `p ≥ 2`, `k < n+2`, `T` available, radii and weights positive, `Λ ≥ 0` an active bound, and
`∫_{r_i}^∞ β_{p,σ_s,T}(z_i,s)^2 ds/s ≤ B` at every index for the truncated testing sources
`σ_s`. Then every subfamily satisfies the quadratic truncated tail bound `Λ^{1-2/p} B`
(the factor is `Λ^0 = 1` at `p = 2`). Inputs (implication form):
`BetaPowHolderStatement` and `BetaPowTwoStatement`. -/
def CpkHolderReductionStatement : Prop :=
  BetaPowHolderStatement → BetaPowTwoStatement →
  ∀ (n : ℕ), 1 ≤ n → ∀ (k : ℕ), 1 ≤ k → k < n + 2 → ∀ (T : FamilyKind), Nonempty (Models n k T) →
  ∀ (p : ℝ), 2 ≤ p →
  ∀ {N : ℕ} (z : Fin N → Space n) (r w : Fin N → ℝ) (B Λ : ℝ),
    (∀ i, 0 < r i) → (∀ i, 0 < w i) → 0 ≤ B → 0 ≤ Λ →
    CpkActiveDensityBound k z r w Λ →
    (∀ i, (∫⁻ s in Ioi (r i),
        betaPow (BetaP.truncatedAtomicSource k z r w s) k T p (z i) s ^ (2 / p) ∂scaleMeasure) ≤
      ENNReal.ofReal B) →
    CpkSubfamilyTailBound k T z r w (Λ ^ (1 - 2 / p) * B)

/-- **Doubled parent.** For a family of pairwise disjoint open balls of positive radii
with weights `0 < w_i ≤ b`, the quadratic bound `DiscretePackingBound n C₀`, applied for
every centre `x` and scale `s > 0` to the retained subfamily `{i : r_i ≤ s, z_i ∈ P(x,s)}`, whose
packing balls lie in the doubled parent `P(x,2s)`, turns the quadratic subfamily tail bound `B'`
into the active bound `2^k C₀ (b + B')`. -/
def CpkDoubledParentStatement : Prop :=
  ∀ (n : ℕ) (C₀ : ℝ), 0 < C₀ → DiscretePackingBound n C₀ →
  ∀ (k : ℕ), 1 ≤ k → k < n + 2 → ∀ (T : FamilyKind), Nonempty (Models n k T) →
  ∀ {N : ℕ} (z : Fin N → Space n) (r w : Fin N → ℝ) (b B' : ℝ),
    (∀ i, 0 < r i) →
    (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
    (∀ i, 0 < w i) → (∀ i, w i ≤ b) → 0 < b → 0 ≤ B' →
    CpkSubfamilyTailBound k T z r w B' →
    CpkActiveDensityBound k z r w (2 ^ k * C₀ * (b + B'))

/-- **Bootstrap absorption.** A real inequality: if `0 ≤ Λ ≤ D (b + Λ^{1-2/p} B)` with `D > 0`, `b, B ≥ 0` and
`p ≥ 2`, then `Λ ≤ max{2D, (2D)^{p/2}} (b + B^{p/2})`. (Either `Λ ≤ 2Db`, or `Λ > 0` and
`Λ/2 < D Λ^{1-2/p} B`, i.e. `Λ < (2DB)^{p/2}`.) -/
def CpkAbsorptionStatement : Prop :=
  ∀ (p D b B Λ : ℝ), 2 ≤ p → 0 < D → 0 ≤ b → 0 ≤ B → 0 ≤ Λ →
    Λ ≤ D * (b + Λ ^ (1 - 2 / p) * B) →
    Λ ≤ max (2 * D) ((2 * D) ^ (p / 2)) * (b + B ^ (p / 2))

/-- **Mass bound**: for a weighted packing of `P(q,R)` every radius is at most
`R` and every centre lies in `P(q,R)`, so `σ(X) = Σ_i w_i r_i^k` is the active mass at `(q,R)`
and `σ(X) ≤ Λ R^k` for every active bound `Λ`. -/
def CpkMassBoundStatement : Prop :=
  ∀ {n N : ℕ} (k : ℕ) (q : Space n) (R : ℝ) (z : Fin N → Space n) (r w : Fin N → ℝ) (b Λ : ℝ),
    IsWeightedPacking q R z r w b → CpkActiveDensityBound k z r w Λ →
    atomicSource k z r w univ ≤ ENNReal.ofReal (Λ * R ^ k)

end ParabolicRectifiability.BetaP
