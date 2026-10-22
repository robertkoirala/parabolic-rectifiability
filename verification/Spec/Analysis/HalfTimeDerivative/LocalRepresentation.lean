import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Basic
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Analysis.HalfTimeDerivative.LocalRepresentation` used by the headline statements. -/

noncomputable section
open MeasureTheory SchwartzMap FourierTransform
open scoped SchwartzMap ContDiff
namespace ParabolicRectifiability.HalfTimeDerivative
variable {m : ℕ}
/-- A complex smooth compact test, with its genuine Schwartz membership. -/
def compactTest (φ : FourierSpace m → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : 𝓢(FourierSpace m, ℂ) :=
  hc.toSchwartzMap hφ

/-- Complexification of a real smooth compact test. -/
def realCompactTest (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : 𝓢(FourierSpace m, ℂ) :=
  compactTest (fun x => (φ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hφ)
    (hc.comp_left (g := Complex.ofReal) rfl)

/-- Real compact-test representation of the half derivative on an open set. -/
def RepHalf {H : FourierSpace m → ℝ} (_hH : MemLp H 2 volume)
    (g : FourierSpace m → ℝ) (Ω : Set (FourierSpace m)) : Prop :=
  IsOpen Ω ∧ LocallyIntegrableOn g Ω volume ∧
    ∀ (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      tsupport φ ⊆ Ω →
        (∫ x, (H x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x) =
          ∫ x, (g x : ℂ) * (φ x : ℂ)

end ParabolicRectifiability.HalfTimeDerivative
