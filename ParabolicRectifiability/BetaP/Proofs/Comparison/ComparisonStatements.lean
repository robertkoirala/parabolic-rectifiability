import ParabolicRectifiability.BetaP.Statements.Laws

/-! # Pointwise comparison of `S_p` and `S_2`: intermediate statements

Proposition definitions used to prove the two pointwise comparisons
* `energyS_lt_top_of_squareEnergy_lt_top`: at a point of finite upper `k`-density,
  `S_2^a(z) < ∞ ⇒ S_p^a(z) < ∞` for `0 < p < 2`;
* `squareEnergy_lt_top_of_energyS_lt_top`: at a point of finite upper `k`-density,
  `S_p^a(z) < ∞ ⇒ S_2^a(z) < ∞` for `p > 2`.

Route (Hölder with the density factor `Θ(z,r) = r^{-k} μ(P(z,r))`):
1. `c2_UpperDensityBoundStatement` (both directions): finite upper density gives `A < ∞` and
   `ρ > 0` with `Θ(z,r) ≤ A` for `0 < r < ρ`.
2. `c2_CmpLtSmallScaleStatement` (`p < 2`): Hölder (`β_p ≤ Θ^{1/p-1/2} β_2`, squared)
   and `B_2 = betaSq` give `∫_0^ρ B_p^{2/p} ds/s ≤ A^{2/p-1} ∫_0^ρ betaSq ds/s`.
3. `c2_CmpGtSmallScaleStatement` (`p > 2`): Hölder clause 2 (`B_2 ≤ Θ^{1-2/p}
   B_p^{2/p}`) gives `∫_0^ρ betaSq ds/s ≤ A^{1-2/p} ∫_0^ρ B_p^{2/p} ds/s`.
4. `c2_EnergySEndpointStatement` (`p < 2`): finite annuli (`BetaPowAnnulusStatement`, taken as a
   hypothesis in implication form) complete a finite small-scale `S_p` integral to every endpoint.

For `p > 2` the endpoint step is `squareEnergy_lt_top_iff_of_endpoints_proof`, so no separate
statement is needed there.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- **Upper-density bound** ("choose `r_z, A_z` with `Θ(z,r) ≤ A_z` for `r < r_z`"). If `Θ^{k,*}(μ,z) = limsup_{r↓0} Θ(z,r) < ∞`, there are a
finite `A` and a radius `ρ > 0` with `Θ(z,r) ≤ A` for every `0 < r < ρ`. Every measure; no
regularity. (`Filter.eventually_lt_of_limsup_lt` with any finite `A > Θ^{k,*}`, then
`mem_nhdsGT_iff_exists_Ioo_subset`.) -/
def c2_UpperDensityBoundStatement : Prop :=
  ∀ {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n), upperDensity μ k z < ⊤ →
    ∃ (A : ℝ≥0∞) (ρ : ℝ), A ≠ ⊤ ∧ 0 < ρ ∧
      ∀ r : ℝ, 0 < r → r < ρ → densityRatio μ k z r ≤ A

/-- **Small scales below two.** For `0 < p < 2`, an available family,
a locally Radon source and a finite `A` bounding `Θ(z,·)` on `(0,ρ)`:
`∫_{(0,ρ)} B_p^{2/p} ds/s ≤ A^{2/p-1} ∫_{(0,ρ)} betaSq ds/s`. Pointwise, Hölder clause 1 with
`(p, q) = (p, 2)` (`claws_holder_proof`), squared, gives `B_p^{2/p} ≤ Θ^{2/p-1} B_2`, and
`B_2 = betaSq` (`f3_betaPow_two_eq_betaSq_proof`); `Θ^{2/p-1} ≤ A^{2/p-1}` since `2/p - 1 > 0`. -/
def c2_CmpLtSmallScaleStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {k : ℕ}, 1 ≤ k → k ≤ n + 2 →
  ∀ {T : FamilyKind}, Nonempty (Models n k T) →
  ∀ {μ : Measure (Space n)}, IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ {p : ℝ}, 0 < p → p < 2 → ∀ (z : Space n) (A : ℝ≥0∞) (ρ : ℝ), A ≠ ⊤ →
    (∀ r : ℝ, 0 < r → r < ρ → densityRatio μ k z r ≤ A) →
    (∫⁻ r in Ioo 0 ρ, betaPow μ k T p z r ^ (2 / p) ∂scaleMeasure) ≤
      A ^ (2 / p - 1) * ∫⁻ r in Ioo 0 ρ, betaSq μ k T z r ∂scaleMeasure

/-- **Small scales above two.** For `p > 2`, an available family, a
locally Radon source and a finite `A` bounding `Θ(z,·)` on `(0,ρ)`:
`∫_{(0,ρ)} betaSq ds/s ≤ A^{1-2/p} ∫_{(0,ρ)} B_p^{2/p} ds/s`. Pointwise, `betaSq = B_2`
(`f3_betaPow_two_eq_betaSq_proof`) and Hölder clause 2 (`claws_holder_proof`):
`B_2 ≤ Θ^{1-2/p} B_p^{2/p} ≤ A^{1-2/p} B_p^{2/p}` since `1 - 2/p > 0`. -/
def c2_CmpGtSmallScaleStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {k : ℕ}, 1 ≤ k → k ≤ n + 2 →
  ∀ {T : FamilyKind}, Nonempty (Models n k T) →
  ∀ {μ : Measure (Space n)}, IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ {p : ℝ}, 2 < p → ∀ (z : Space n) (A : ℝ≥0∞) (ρ : ℝ), A ≠ ⊤ →
    (∀ r : ℝ, 0 < r → r < ρ → densityRatio μ k z r ≤ A) →
    (∫⁻ r in Ioo 0 ρ, betaSq μ k T z r ∂scaleMeasure) ≤
      A ^ (1 - 2 / p) * ∫⁻ r in Ioo 0 ρ, betaPow μ k T p z r ^ (2 / p) ∂scaleMeasure

/-- **`S_p` endpoint completion** ("finite annuli complete the endpoint"). Given the
finite-annulus law (`BetaPowAnnulusStatement`, a hypothesis in implication form; it is proved as
`c2_betaPowAnnulus_proof`), a finite integral `∫_{(0,ρ)} B_p^{2/p} ds/s`,
`ρ > 0`, gives `S_p^a(z) < ∞` for every endpoint `a`: for `a ≤ ρ` by monotonicity of the set, and
for `a > ρ` from `(0,a) ⊆ (0,ρ) ∪ (ρ/2, a)` and the annulus law on the annulus `(ρ/2, a)`. -/
def c2_EnergySEndpointStatement : Prop :=
  BetaPowAnnulusStatement →
  ∀ {n : ℕ}, 1 ≤ n → ∀ {k : ℕ}, 1 ≤ k → k ≤ n + 2 →
  ∀ {T : FamilyKind}, Nonempty (Models n k T) →
  ∀ {μ : Measure (Space n)}, IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ {p : ℝ}, 0 < p → ∀ (z : Space n) (ρ a : ℝ), 0 < ρ →
    (∫⁻ r in Ioo 0 ρ, betaPow μ k T p z r ^ (2 / p) ∂scaleMeasure) < ⊤ →
    energyS μ k T p a z < ⊤

end ParabolicRectifiability.BetaP
