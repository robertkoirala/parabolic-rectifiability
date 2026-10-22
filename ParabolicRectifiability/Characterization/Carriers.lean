import ParabolicRectifiability.Metric.Hausdorff

/-! # The good set of the source-transfer appendix

Definitions only.

* `adrGoodSet Γ ν k A`: the good set `G_A = {z ∈ Γ : ν(P(z,r)) ≤ A r^k for every r > 0}`.

The shared carrier predicates are defined in `Foundations` and used from there:
* `Foundations.HasBorelSigmaFiniteHausdorffCarrier k μ`:
  "`μ` has a Borel sigma-finite `H_P^k` carrier", that is, countably many Borel pieces of finite `H_P^k` measure whose union carries `μ`. Conversely,
  a Borel carrier that is sigma-finite for `H_P^k` through arbitrary (not necessarily
  Borel) finite-Hausdorff pieces is such a union: take Borel hulls of the finite-Hausdorff
  pieces and intersect those hulls with the Borel carrier.
* `Foundations.IsADRCarrier k c C Γ σ` the closed Ahlfors–David
  regular reference carrier.

Conventions. `P(z,r)` is the open parabolic ball `Metric.ball z r`, real constants are
compared through `ENNReal.ofReal`, and measures are evaluated on arbitrary sets (outer
measure).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

/-- The good set `G_A = {z ∈ Γ : ν(P(z,r)) ≤ A r^k for every r > 0}`
The balls are the ambient open balls; for a source carried by
`Γ` their mass equals that of the relative balls `B_Γ(z,r) = Γ ∩ P(z,r)`. -/
def adrGoodSet {n : ℕ} (Γ : Set (Space n)) (ν : Measure (Space n)) (k : ℕ) (A : ℝ) :
    Set (Space n) :=
  {z | z ∈ Γ ∧ ∀ r : ℝ, 0 < r → ν (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)}

end ParabolicRectifiability.Characterization
