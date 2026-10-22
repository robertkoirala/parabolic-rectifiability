import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Foundations.Proofs.DensityMeasurability

/-! # Moving-ball mass and the rational-radius reduction of densities

Two lemmas used to prove `fmeas1_density_measurability` (measurability of the upper and lower
densities): `fmeas1_measurable_ball_measure` (the mass of a moving ball is a measurable
function of the centre) and `fmeas1_densities_eq_rat` (both densities are countable extrema of
density ratios over rational radii). Each is proved by the corresponding `…_proof` lemma.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- **Moving-ball mass is Borel.** For a source finite on compacts and every real `r`,
`z ↦ μ(P(z,r))` is measurable.

Proof (the moving-ball argument of `measurable_fit`): `μ` is sigma-finite
(`source_sigmaFinite`), so `SFinite`; the indicator
`(z,w) ↦ 1_{dist w z < r}` is jointly measurable (`measurableSet_lt`), and
`Measurable.lintegral_prod_right` gives the measurability of `z ↦ ∫ 1_{P(z,r)} dμ = μ(P(z,r))`
(`lintegral_indicator measurableSet_ball`). Alternative route without sigma-finiteness: the map
is lower semicontinuous for every Borel measure (`LowerSemicontinuous.measurable`). -/
theorem fmeas1_measurable_ball_measure {n : ℕ} (μ : Measure (Space n))
    (hμ : IsFiniteMeasureOnCompacts μ) (r : ℝ) :
    Measurable (fun z : Space n => μ (Metric.ball z r)) := by
  exact fmeas1_measurable_ball_measure_proof μ hμ r

/-- **Rational radii compute both densities** (continuity from below of `r ↦ μ(P(z,r))`,
extrema over rational radii, then `a = 1/j ↓ 0`).

For **every** measure `μ` on `X`, every `k` and centre `z`,
`Θ_*^k(μ,z) = sup_j inf_{q ∈ ℚ, 0 < q < 1/(j+1)} μ(P(z,q))/q^k` and
`Θ^{k,*}(μ,z) = inf_j sup_{q ∈ ℚ, 0 < q < 1/(j+1)} μ(P(z,q))/q^k`, with the ratios of
`densityRatio`.

Proof. (i) `nhdsGT_basis 0` and `Filter.HasBasis.liminf_eq_iSup_iInf` /
`Filter.HasBasis.limsup_eq_iInf_iSup` write the densities as `sup_{δ>0} inf_{0<r<δ}` and
`inf_{δ>0} sup_{0<r<δ}`; the extrema are monotone in `δ`, so `δ = 1/(j+1)` suffices.
(ii) Sup: for `r > 0`, `P(z,r) = ⋃_{q ∈ ℚ, 0<q<r} P(z,q)`, so `μ(P(z,r)) = sup_q μ(P(z,q))`
(use `Directed.measure_iUnion` on the countable rational-radius subtype, or
`Monotone.measure_iUnion` along an increasing rational sequence `q ↑ r`), and
`μ(P(z,q))/r^k ≤ μ(P(z,q))/q^k`; hence the real supremum over `(0,δ)` equals the rational one.
(iii) Inf: for `r ∈ (0,δ)` and rationals `q ↑ r`, `μ(P(z,q))/q^k ≤ μ(P(z,r))/q^k`, which tends
to `μ(P(z,r))/r^k` (trivial when `μ(P(z,r)) = ⊤`; otherwise continuity of
`x ↦ c / x^k` at `r^k ∈ (0,∞)`); hence the real infimum equals the rational one.
No regularity or finiteness of `μ` is used. Both the supremum and the infimum arguments are
carried out in `ENNReal`: no continuity from above and no finite-mass assumption enters. Density
of the rationals alone would not suffice; the ball-monotonicity comparisons above are what
justify the reduction. The statement holds for every `k`, including `k = 0`, and for infinite
ball masses.

This rational-radius representation is a named theorem so that it can be reused elsewhere
(with separate lower/upper projections by `.1`/`.2`), not only in
`fmeas1_density_measurability`. -/
theorem fmeas1_densities_eq_rat (n : ℕ) (μ : Measure (Space n)) (k : ℕ) (z : Space n) :
    lowerDensity μ k z =
        ⨆ j : ℕ, ⨅ q : {q : ℚ // 0 < q ∧ (q : ℝ) < 1 / ((j : ℝ) + 1)},
          densityRatio μ k z (q.1 : ℝ) ∧
      upperDensity μ k z =
        ⨅ j : ℕ, ⨆ q : {q : ℚ // 0 < q ∧ (q : ℝ) < 1 / ((j : ℝ) + 1)},
          densityRatio μ k z (q.1 : ℝ) := by
  exact fmeas1_densities_eq_rat_proof n μ k z

end ParabolicRectifiability.Foundations
