import Spec.Basic
import Spec.Metric.Hausdorff
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Characterization.Carriers` used by the headline statements. -/

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
