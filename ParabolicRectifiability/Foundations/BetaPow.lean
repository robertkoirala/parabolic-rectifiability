import ParabolicRectifiability.Measure.ScaleEnergy

/-! # Beta-`p` fitting quantities and the two beta-`p` energies

For a real exponent `p > 0`, a family `T` and a radius `r > 0`,
```
B_p(z,r) = r^{-k-p} · inf_{L ∈ T} ∫_{P(z,r)} d_P(w,L)^p dμ(w),     β_p = B_p^{1/p},
S_p^a(z) = ∫_{(0,a)} B_p(z,r)^{2/p} dr/r,        T_p^a(z) = ∫_{(0,a)} B_p(z,r) dr/r.
```
* `d_P(w,L)^p` is `Metric.infEDist w (modelSet L) ^ p`, the `ℝ≥0∞` real power of the
  actual parabolic distance to the represented model set (the same distance whose
  square is `modelCost`).
* There is no division by ball mass, and all values are extended nonnegative.
* The superscript `a` of `S_p^a`, `T_p^a` is the endpoint of the scale integral, never a
  power. The scale measure is the existing `scaleMeasure` (`dr/r` on positive radii),
  exactly as in `squareEnergy`.
* The nonpositive-radius convention is the one of `betaSq`: `B_p(z,r) = 0` for `r ≤ 0`.
* For an unavailable family (`IsEmpty (Models n k T)`) the infimum is empty, hence `⊤`,
  so `B_p = ⊤` at positive radii and both energies are `⊤` at positive endpoints.
  For a nonempty family and an empty testing ball the fit is
  `0`, so `B_p = 0`.
* The definitions are total in `p`; only `0 < p` is meaningful, and every statement
  using them carries that hypothesis.

The identities `B_2 = betaSq` and `S_2^a = T_2^a = squareEnergy` are statements
(`BetaPowTwoStatement`, `EnergyTwoStatement`), not definitions.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- The unnormalized `p`-fitting integral `∫_{P(z,r)} d_P(w,L)^p dμ(w)` of one model,
with the parabolic distance raised to the real power `p` in `ℝ≥0∞`. -/
def fitPow {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n)) (p : ℝ) (L : Models n k T)
    (z : Space n) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in Metric.ball z r, Metric.infEDist w (modelSet L) ^ p ∂μ

/-- The beta-`p` fitting quantity
`B_p(z,r) = r^{-k-p} inf_{L ∈ T} ∫_{P(z,r)} d_P(w,L)^p dμ(w)` for `r > 0`, and `0` for
`r ≤ 0` (the `betaSq` convention). The factor `r^{-k-p}` is `(ofReal r)⁻¹ ^ (k + p)`. -/
def betaPow {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p : ℝ)
    (z : Space n) (r : ℝ) : ℝ≥0∞ :=
  if 0 < r then
    (ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + p) * ⨅ L : Models n k T, fitPow μ p L z r
  else 0

/-- The root `β_p = B_p^{1/p}`. Statements are phrased
through `betaPow`; this abbreviation is provided for convenience only. -/
def betaPowRoot {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p : ℝ)
    (z : Space n) (r : ℝ) : ℝ≥0∞ :=
  betaPow μ k T p z r ^ (1 / p)

/-- The quadratic beta-`p` energy `S_p^a(z) = ∫_{(0,a)} B_p(z,r)^{2/p} dr/r`, valued
in `ℝ≥0∞`. The superscript `a` is a scale endpoint; `p > 0` is the meaningful exponent
range. It is zero when `a ≤ 0`, and may be infinite for positive `a`. The energy uses
the full measure argument; restricting the testing centres does not restrict that source. -/
def energyS {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p a : ℝ)
    (z : Space n) : ℝ≥0∞ :=
  ∫⁻ r in Ioo 0 a, betaPow μ k T p z r ^ (2 / p) ∂scaleMeasure

/-- The `p`-power beta-`p` energy `T_p^a(z) = ∫_{(0,a)} B_p(z,r) dr/r`, valued in
`ℝ≥0∞` and using the full measure argument. The scale interval is empty for `a ≤ 0`,
so the energy is zero there. For positive endpoints, `T_p` and `S_p` are different
energies except at the quadratic exponent, where their identification with
`squareEnergy` is a theorem. -/
def energyT {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p a : ℝ)
    (z : Space n) : ℝ≥0∞ :=
  ∫⁻ r in Ioo 0 a, betaPow μ k T p z r ∂scaleMeasure

end ParabolicRectifiability.Foundations
