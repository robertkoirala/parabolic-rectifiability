import Spec.Basic
import Spec.Metric.Hausdorff
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Foundations.Carriers` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Foundations
/-- `μ` has a Borel sigma-finite `H_P^k` carrier: countably many Borel sets of finite
`H_P^k` measure whose union `E` carries `μ`, i.e. `μ (X \ E) = 0`. The union is Borel and
sigma-finite for `H_P^k`. Conversely, given a Borel carrier that is a countable union of
arbitrary sets of finite `H_P^k` measure, take Borel hulls of those finite-Hausdorff pieces
and intersect the hulls with the Borel carrier. -/
def HasBorelSigmaFiniteHausdorffCarrier {n : ℕ} (k : ℕ) (μ : Measure (Space n)) : Prop :=
  ∃ F : ℕ → Set (Space n), (∀ j, MeasurableSet (F j)) ∧ (∀ j, hausdorffP n k (F j) < ⊤) ∧
    μ (⋃ j, F j)ᶜ = 0

/-- The intrinsic source class: `μ ≪ H_P^k` and a Borel
carrier `E = ⋃_j E_j` with `μ(X \ E) = 0` and `H_P^k(E_j) < ∞` for every `j`. This is also
structural condition (c) of the integral criterion.

The pieces are Borel and indexed by `ℕ` instead of `j ≥ 1`. -/
def IsIntrinsicSource {n : ℕ} (k : ℕ) (μ : Measure (Space n)) : Prop :=
  μ ≪ hausdorffP n k ∧ HasBorelSigmaFiniteHausdorffCarrier k μ

end ParabolicRectifiability.Foundations
