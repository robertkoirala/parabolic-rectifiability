import ParabolicRectifiability.Metric.Hausdorff
import ParabolicRectifiability.Foundations.Proofs.UpperGrowth
import Mathlib.MeasureTheory.Measure.Support

/-! # Upper growth implies absolute continuity

Targets:
* `absolutelyContinuous_hausdorffP_of_growth`, proved by
  `fgac_absolutelyContinuous_hausdorffP_of_growth`, whose type is that of the target;
* `QuantitativeCharacterization.absolutelyContinuous_of_upper_growth`, assembled in
  `fgac_absolutelyContinuous_of_upper_growth` from that statement and the adapter
  `fgac_ball_le_of_support_growth`.

Both declarations delegate to the corresponding `_proof` theorems. The first proves absolute continuity from all-centre
small-scale growth; the second transfers support-centred growth to arbitrary centres.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- **Upper growth implies absolute continuity.** The type is that of
`absolutelyContinuous_hausdorffP_of_growth`; its proof closes that statement directly.

For `1 ≤ n`, `1 ≤ k ≤ n + 2`, a locally Radon `λ`, a real `B` and `r₀ > 0`
with `λ(P(p,r)) ≤ B r^k` for every centre `p` and `0 < r ≤ r₀`: `λ ≪ H_P^k` (arbitrary sets).

Route (Mathlib `Measure.le_mkMetric`, `Measure.mkMetric_mono_smul`,
`Measure.absolutelyContinuous_of_le_smul`). First derive finite extended diameter and prove the
diameter estimate for arbitrary sets; then apply `Measure.le_mkMetric`, followed by
`Measure.mkMetric_mono_smul` with the finite nonzero coefficient `ofReal (max B 1)`.
(`Measure.le_hausdorffMeasure` has coefficient one and is not a direct coefficient-bearing
substitute.) Put `c = ENNReal.ofReal (max B 1)`, so
`c ≠ 0, ∞`. For every set `s` with `ediam s ≤ ofReal (r₀/2)`: if `s = ∅` then `λ s = 0`;
otherwise `ediam s < ⊤`, pick `x ∈ s`, `d = diam s` (e.g. `r_j = d + (r₀ - d)/(j+2)`); for
every `r ∈ (d, r₀]`, `s ⊆ P(x,r)` and
`λ s ≤ ofReal (B r^k)`; letting `r ↓ d` gives `λ s ≤ c · d^k` (`k ≥ 1` makes `d = 0`
harmless: singletons are null). Then `le_mkMetric` with `m = c · (·)^k` gives
`λ ≤ mkMetric (c • (·)^k) ≤ c • H^k` (`mkMetric_mono_smul`), hence `λ ≪ H^k`.
`hausdorffP n k` is `Measure.hausdorffMeasure (k : ℝ)`. Neither the
locally Radon hypotheses nor `k ≤ n + 2` are needed by this route. -/
theorem fgac_absolutelyContinuous_hausdorffP_of_growth :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ lam : Measure (Space n), IsFiniteMeasureOnCompacts lam → lam.InnerRegular →
    ∀ B r₀ : ℝ, 0 < r₀ →
      (∀ (p : Space n) (r : ℝ), 0 < r → r ≤ r₀ →
        lam (Metric.ball p r) ≤ ENNReal.ofReal (B * r ^ k)) →
      lam ≪ hausdorffP n k := by
  exact fgac_absolutelyContinuous_hausdorffP_of_growth_proof

/-- **Support-centred growth gives all-centre growth.**

For any measure `μ` on `X`, any `k` and any real `A`: if
`μ(P(z,r)) ≤ A r^k` for every `z ∈ supp μ` and every `r > 0`, then
`μ(P(p,r)) ≤ 2^k A r^k` for every centre `p` and every `r > 0`.

Route. If `μ(P(p,r)) = 0` there is nothing to prove. Otherwise `P(p,r)` meets `supp μ`
(Mathlib `Measure.nonempty_inter_support_of_pos`; `X` is second countable, hence hereditarily
Lindelöf): take `z ∈ P(p,r) ∩ supp μ`; then `P(p,r) ⊆ P(z,2r)` and
`μ(P(p,r)) ≤ ofReal (A (2r)^k) = ofReal (2^k A r^k)`. No sign condition on `A` is needed: both
`ofReal` bounds are zero when `A ≤ 0`; the hypotheses then force the measure to vanish
(the route does not need this separately). The support hypothesis covers
all positive radii, so evaluating it at `2r` is legitimate for every `r > 0`. -/
theorem fgac_ball_le_of_support_growth {n : ℕ} (k : ℕ) (μ : Measure (Space n)) (A : ℝ)
    (hA : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k))
    (p : Space n) (r : ℝ) (hr : 0 < r) :
    μ (Metric.ball p r) ≤ ENNReal.ofReal (2 ^ k * A * r ^ k) := by
  exact fgac_ball_le_of_support_growth_proof k μ A hA p r hr

end ParabolicRectifiability.Foundations
