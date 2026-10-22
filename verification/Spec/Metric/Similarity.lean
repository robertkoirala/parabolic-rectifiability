import Spec.Analysis.Coordinates
import Spec.Basic
import Spec.Metric.Measure
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Metric.Similarity` used by the headline statements. -/

noncomputable section
open Set
open scoped ENNReal
namespace ParabolicRectifiability
/-- Subtract a space-time center through ordinary coordinates. -/
def translationHomeomorph {n : ℕ} (q : Space n) : Space n ≃ₜ Space n :=
  ((coordinatesHomeomorph n).trans
    ((Homeomorph.subRight q.1).prodCongr (Homeomorph.subRight q.2.val))).trans
      (coordinatesHomeomorph n).symm

/-- `T(q,a)(x,t) = ((x-qₓ)/a,(t-qₜ)/a²)` for a positive real scale. -/
def similarity {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a) : Space n ≃ₜ Space n :=
  (translationHomeomorph q).trans (dilationHomeomorph n a⁻¹ (inv_pos.mpr ha))

end ParabolicRectifiability
