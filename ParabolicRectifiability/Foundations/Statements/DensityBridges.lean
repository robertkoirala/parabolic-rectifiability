import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Measure.ScaleEnergy
import ParabolicRectifiability.Metric.Hausdorff

/-! # Statements: the three density lemmas of the shared foundations

The packing-mass lemma (`PackingMassStatement`), the upper-density domination lemma
(`UpperDensityDominationStatement`) and the absolute-continuity bridge (`ACBridgeStatement`).

These are proposition definitions only; the corresponding theorems are
`packing_mass_bound`, `hausdorffP_le_of_upperDensity` and
`absolutelyContinuous_of_lowerDensity_squareEnergy`.

Conventions. The standing assumptions `1 ≤ n` and `1 ≤ k ≤ n + 2` are hypotheses. "Locally Radon" is
`IsFiniteMeasureOnCompacts μ` together with `μ.InnerRegular`. Densities are
`lowerDensity`/`upperDensity`, `H_P^k` is `hausdorffP n k`, and `P(z,r)` is the open ball
`Metric.ball z r`. "μ-almost every `z ∈ E`" is `∀ᵐ z ∂μ, z ∈ E → …`; absolute continuity
`≪` and Hausdorff measure are evaluated on arbitrary sets (outer measure). Real constants
are compared through `ENNReal.ofReal`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.Foundations

/-- Packing turns lower density into retained mass.

Hypotheses: a Borel set `K`; real `R₀ > 0` and `C_K ≥ 0` with the disjoint-ball packing
bound: for every centre `q` and `0 < ρ ≤ R₀`, every finite family of pairwise disjoint
balls `P(z_i,r_i)` with `z_i ∈ K ∩ P(q,ρ)` and `0 < r_i ≤ ρ` has `∑ r_i^k ≤ C_K ρ^k`;
a locally Radon `ρ₀`; a real `A ≥ 0` with `Θ_*^k(ρ₀,z) ≤ A` for `ρ₀`-almost every
`z ∈ K`.
Conclusion: `(ρ₀⌊K)(P(q,ρ)) ≤ 5^k C_K A ρ^k` for every centre `q` and `0 < ρ ≤ R₀`.

The packing hypothesis uses finite families indexed by `Fin l`, in exactly the shape
of the main theorem's output field `HasRectifiabilityContentBounds.finite_packing`
(there `R₀ = 1`, `C_K = C`). Because the sums are nonnegative, this is equivalent to
the same bound for countable disjoint families (`countable_packing`): a countable sum
is the supremum of its finite partial sums. -/
def PackingMassStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ K : Set (Space n), MeasurableSet K →
  ∀ R₀ C_K : ℝ, 0 < R₀ → 0 ≤ C_K →
  (∀ (q : Space n) (ρ : ℝ), 0 < ρ → ρ ≤ R₀ →
    ∀ (l : ℕ) (z : Fin l → Space n) (r : Fin l → ℝ),
      (∀ i, z i ∈ K ∩ Metric.ball q ρ) →
      (∀ i, 0 < r i ∧ r i ≤ ρ) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∑ i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C_K * ρ ^ k)) →
  ∀ ρ₀ : Measure (Space n), IsFiniteMeasureOnCompacts ρ₀ → ρ₀.InnerRegular →
  ∀ A : ℝ, 0 ≤ A →
  (∀ᵐ z ∂ρ₀, z ∈ K → lowerDensity ρ₀ k z ≤ ENNReal.ofReal A) →
  ∀ (q : Space n) (ρ : ℝ), 0 < ρ → ρ ≤ R₀ →
    ρ₀.restrict K (Metric.ball q ρ) ≤ ENNReal.ofReal (5 ^ k * C_K * A * ρ ^ k)

/-- Pointwise positive upper density gives Hausdorff domination.

There is a constant `C_k > 0` depending only on `k` (the proof gives
`2·10^k` for the unnormalized diameter-power `H_P^k`; it does not depend on `n`) such
that: for a bounded open `O`, a Borel `F ⊆ O`, a real `a > 0` and a locally Radon `ρ`
with `Θ^{k,*}(ρ,z) ≥ a` at **every** `z ∈ F`,
`H_P^k(F ∩ B) ≤ C_k a^{-1} ρ(F ∩ B) ≤ C_k a^{-1} (ρ⌊O)(B)` for every Borel `B`, and in
particular `H_P^k(F) < ∞`.
The constant is chosen before `n`, `O`, `F`, `a` and `ρ`. -/
def UpperDensityDominationStatement : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → k ≤ n + 2 →
    ∀ O : Set (Space n), IsOpen O → Bornology.IsBounded O →
    ∀ F : Set (Space n), MeasurableSet F → F ⊆ O →
    ∀ a : ℝ, 0 < a →
    ∀ ρ : Measure (Space n), IsFiniteMeasureOnCompacts ρ → ρ.InnerRegular →
      (∀ z ∈ F, ENNReal.ofReal a ≤ upperDensity ρ k z) →
        (∀ B : Set (Space n), MeasurableSet B →
          hausdorffP n k (F ∩ B) ≤ ENNReal.ofReal (C / a) * ρ (F ∩ B) ∧
            ENNReal.ofReal (C / a) * ρ (F ∩ B) ≤ ENNReal.ofReal (C / a) * ρ.restrict O B) ∧
        hausdorffP n k F < ⊤

/-- The absolute-continuity bridge: finite lower density and finite energy imply absolute
continuity.

For an open `O`, a locally Radon `μ`, a finite endpoint `0 < R < ∞` and the mixed family or any available fixed family `T` (encoded as
`Nonempty (Models n k T)`; the mixed family is always available for `1 ≤ k ≤ n + 2`,
`1 ≤ n`): if `Θ_*^k(μ,z) < ∞` and `S_{μ,T}^R(z) < ∞` for `μ`-almost every `z ∈ O`, then
`μ⌊O ≪ H_P^k`. No positive density is assumed. -/
def ACBridgeStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ O : Set (Space n), IsOpen O →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ R : ℝ, 0 < R →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
    (∀ᵐ z ∂μ, z ∈ O → lowerDensity μ k z < ⊤ ∧ squareEnergy μ k T R z < ⊤) →
    μ.restrict O ≪ hausdorffP n k

end ParabolicRectifiability.Foundations
