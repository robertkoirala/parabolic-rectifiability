import ParabolicRectifiability.Foundations.BetaPow
import ParabolicRectifiability.Metric.Measure

/-! # The shared diffuse estimates: named statements

Definitions and proposition definitions only. This module uses only Foundations-level types
(`fitPow`, `betaPow`, `energyS`, `energyT`, explicit outer integrals) and imports nothing from
`BetaP`. Both the diffuse test for the sharpness statements and the diffuse conjunct of the
density tests consume the output `E2DiffuseEnergyBounds`.

Notation: `ω = L^{n+1}⌊P(0,1/4)` is `e2_diffuseBase n`, the positivity box
`D = P(0,1/16)` is `e2_diffuseBox n`, the positivity band `I = [1/32, 1/16]` is
`e2_diffuseBand`, `α = n + 2 - k > 0`.

The statements are stated at amplitude `c = 1` (`μ_c = c ω`): the amplitude clauses of the
density tests go through `squareEnergy_smul`, and their zero-density and nullity statements
rescale the base bound themselves. Inner regularity of the base is not needed.

The seven statements:
1. `E2DiffuseSourceStatement`: finite mass, `0 < ω(D)`, `ω(P(z,r)) ≤ 2ω_n r^{n+2}`.
2. `E2DiffuseBetaUpperStatement`: `B_p(z,r) ≤ 2ω_n r^{α}` at every centre (model through it).
3. `E2DiffuseHorizontalLowerStatement`: fitting lower bound for every horizontal model.
4. `E2DiffuseVerticalLowerStatement`: fitting lower bound for every vertical model.
5. `E2DiffuseBetaLowerStatement`: infimum and normalization, `B_p ≥ b` on `D × I`
   (implication form over the uniform interface `E2DiffuseFitLower`, which is built from
   3 and 4).
6. `E2ScaleIntegralStatement`: `∫_{(0,2)} r^γ dr/r = 2^γ/γ` and `0 < scaleMeasure I < ⊤`.
7. `E2DiffuseEnergyStatement`: pointwise and integrated energy assembly (implication form over
   1, 2, 6 and the conclusion of 5), with output `E2DiffuseEnergyBounds`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-! ## The diffuse objects -/

/-- The diffuse base `ω = L^{n+1}⌊P(0,1/4)` , literally the measure of `DiffuseTestStatement` at `c = 1`. -/
abbrev e2_diffuseBase (n : ℕ) : Measure (Space n) :=
  (parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))

/-- The positivity box `D = P(0,1/16)` of centres. -/
abbrev e2_diffuseBox (n : ℕ) : Set (Space n) :=
  Metric.ball (point 0 0) (1 / 16)

/-- The positivity band `I = [1/32, 1/16]` of radii. -/
abbrev e2_diffuseBand : Set ℝ :=
  Icc (1 / 32) (1 / 16)

/-! ## Shared statements -/

/-- **Source bounds.** `ω` is finite, the box has positive mass, and every
parabolic ball satisfies `ω(P(z,r)) ≤ 2ω_n r^{n+2}` (ambient ball volume). -/
def E2DiffuseSourceStatement : Prop :=
  ∀ n : ℕ, IsFiniteMeasure (e2_diffuseBase n) ∧ 0 < e2_diffuseBase n (e2_diffuseBox n) ∧
    ∀ (z : Space n) (r : ℝ), 0 < r →
      e2_diffuseBase n (Metric.ball z r) ≤ 2 * omega n * ENNReal.ofReal r ^ (n + 2)

/-- **Uniform beta upper bound.** For an available family, every centre
(including centres outside the support), every `r > 0` and `p > 0`:
`B_p(z,r) ≤ 2ω_n r^{n+2-k}`. -/
def E2DiffuseBetaUpperStatement : Prop :=
  ∀ (n k : ℕ) (T : FamilyKind), Nonempty (Models n k T) → ∀ p : ℝ, 0 < p →
    ∀ (z : Space n) (r : ℝ), 0 < r →
      betaPow (e2_diffuseBase n) k T p z r ≤
        2 * omega n * ENNReal.ofReal r ^ ((n : ℝ) + 2 - k)

/-- **Horizontal lower fit.** There is `a > 0` such that every horizontal
model `U × {τ}` has `∫_{P(z,r)} d_P(w,L)^p dω ≥ a r^{n+2+p}` for `z ∈ D`, `r ∈ I` (proved with **open** half intervals). -/
def E2DiffuseHorizontalLowerStatement : Prop :=
  ∀ (n k : ℕ) (p : ℝ), 0 < p → ∃ a : ℝ, 0 < a ∧
    ∀ (L : HorizontalModel n k) (z : Space n), z ∈ e2_diffuseBox n → ∀ r ∈ e2_diffuseBand,
      ENNReal.ofReal a * ENNReal.ofReal r ^ ((n : ℝ) + 2 + p) ≤
        ∫⁻ w in Metric.ball z r, Metric.infEDist w L.toSet ^ p ∂(e2_diffuseBase n)

/-- **Vertical lower fit.** For `k < n + 2` there is `a > 0` such that every
vertical model `(a₀ + W) × ℝ` has `∫_{P(z,r)} d_P(w,L)^p dω ≥ a r^{n+2+p}` for `z ∈ D`, `r ∈ I` (proved with the spatial subball `B(x ± 3r/4 e, r/4)`, no cap volumes). -/
def E2DiffuseVerticalLowerStatement : Prop :=
  ∀ (n k : ℕ) (p : ℝ), k < n + 2 → 0 < p → ∃ a : ℝ, 0 < a ∧
    ∀ (L : VerticalModel n k) (z : Space n), z ∈ e2_diffuseBox n → ∀ r ∈ e2_diffuseBand,
      ENNReal.ofReal a * ENNReal.ofReal r ^ ((n : ℝ) + 2 + p) ≤
        ∫⁻ w in Metric.ball z r, Metric.infEDist w L.toSet ^ p ∂(e2_diffuseBase n)

/-- The uniform lower-fit interface (the horizontal and vertical lower fits combined): one `a > 0` bounds
`fitPow ω p L z r` below by `a r^{n+2+p}` for **every** model `L` of the family `T`, every
`z ∈ D` and `r ∈ I`. Proved by `e2_diffuse_fitLower` from the horizontal and vertical lower fits. -/
def E2DiffuseFitLower (n k : ℕ) (T : FamilyKind) (p : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧
    ∀ (L : Models n k T) (z : Space n), z ∈ e2_diffuseBox n → ∀ r ∈ e2_diffuseBand,
      ENNReal.ofReal a * ENNReal.ofReal r ^ ((n : ℝ) + 2 + p) ≤ fitPow (e2_diffuseBase n) p L z r

/-- **Infimum and normalization.** From the uniform lower fit, `B_p ≥ b > 0`
on `D × I` (`b = a 32^{-(n+2-k)}`). No attainment theorem is used. -/
def E2DiffuseBetaLowerStatement : Prop :=
  ∀ (n k : ℕ) (T : FamilyKind) (p : ℝ), k < n + 2 → 0 < p → E2DiffuseFitLower n k T p →
    ∃ b : ℝ, 0 < b ∧ ∀ z ∈ e2_diffuseBox n, ∀ r ∈ e2_diffuseBand,
      ENNReal.ofReal b ≤ betaPow (e2_diffuseBase n) k T p z r

/-- **Positive-power scale integral and positive band.**
`∫_{(0,2)} r^γ dr/r = 2^γ/γ` for `γ > 0`, and the band has positive finite scale measure. -/
def E2ScaleIntegralStatement : Prop :=
  (∀ γ : ℝ, 0 < γ →
    ∫⁻ r in Ioo (0 : ℝ) 2, ENNReal.ofReal r ^ γ ∂scaleMeasure =
      ENNReal.ofReal ((2 : ℝ) ^ γ / γ)) ∧
  0 < scaleMeasure e2_diffuseBand ∧ scaleMeasure e2_diffuseBand < ⊤

/-- The output of the shared construction: real bounds
`A_S, A_T > 0` on both energies at endpoint `2` at **every** point, and positive finite outer
integrals over `P(0,1)`. -/
def E2DiffuseEnergyBounds (n k : ℕ) (T : FamilyKind) (p : ℝ) : Prop :=
  ∃ AS AT : ℝ, 0 < AS ∧ 0 < AT ∧
    (∀ z : Space n, energyS (e2_diffuseBase n) k T p 2 z ≤ ENNReal.ofReal AS ∧
      energyT (e2_diffuseBase n) k T p 2 z ≤ ENNReal.ofReal AT) ∧
    (0 < ∫⁻ z in Metric.ball (point 0 0) 1, energyS (e2_diffuseBase n) k T p 2 z
        ∂(e2_diffuseBase n) ∧
      ∫⁻ z in Metric.ball (point 0 0) 1, energyS (e2_diffuseBase n) k T p 2 z
        ∂(e2_diffuseBase n) < ⊤) ∧
    (0 < ∫⁻ z in Metric.ball (point 0 0) 1, energyT (e2_diffuseBase n) k T p 2 z
        ∂(e2_diffuseBase n) ∧
      ∫⁻ z in Metric.ball (point 0 0) 1, energyT (e2_diffuseBase n) k T p 2 z
        ∂(e2_diffuseBase n) < ⊤)

/-- **Pointwise and integrated energy assembly.** From the source bounds, the beta upper bound,
the scale integrals and a positive lower bound for `B_p` on `D × I`, both energies at endpoint
`2` are bounded everywhere and have positive finite outer integrals over `P(0,1)`, for every
available family and every `p > 0` (upper bounds
`T ≤ 2ω_n 2^α/α`, `S ≤ (2ω_n)^{2/p} 2^{2α/p}/(2α/p)`; positivity `≥ ω(D) b^{(2/p)} scaleMeasure(I)`). -/
def E2DiffuseEnergyStatement : Prop :=
  E2DiffuseSourceStatement → E2DiffuseBetaUpperStatement → E2ScaleIntegralStatement →
  ∀ (n k : ℕ) (T : FamilyKind) (p : ℝ), k < n + 2 → Nonempty (Models n k T) → 0 < p →
    (∃ b : ℝ, 0 < b ∧ ∀ z ∈ e2_diffuseBox n, ∀ r ∈ e2_diffuseBand,
      ENNReal.ofReal b ≤ betaPow (e2_diffuseBase n) k T p z r) →
    E2DiffuseEnergyBounds n k T p

end ParabolicRectifiability.Examples
