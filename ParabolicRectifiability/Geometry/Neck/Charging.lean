import ParabolicRectifiability.Geometry.Neck.CoherentData

/-!
# Charging: reference-volume summation

The quantitative charging has two ingredients:

* the last-witness bound (`ChargeCollapse.lastWitness_sum`),
  which charges the betas of finitely many centers at the scales `r_j = 10^{-j} r_0`
  to the tail energy at one deepest witness;
* the reference-volume summation, which integrates a pointwise last-witness bound
  against a finite reference measure. It is proved here, in an abstract finite form.
-/

noncomputable section

namespace ParabolicRectifiability

namespace Charging

open MeasureTheory Set
open scoped ENNReal

/-- The scales `r_j = 10^{-j} r_0` are positive. -/
theorem coherentScale_pos {r₀ : ℝ} (hr₀ : 0 < r₀) (j : ℕ) : 0 < coherentScale r₀ j :=
  div_pos hr₀ (pow_pos (by norm_num) j)

/-- **Reference-volume summation, abstract finite form.** Let `ω` be a measure, `E j g`
measurable incidence sets for the finitely many nodes `g ∈ I j`, `j ∈ s`, with lower
incidence masses `w j g ≤ ω(E j g)`. If at every point the incident node values satisfy
`∑_{j,g} 1_{E j g}(x) b j g ≤ M`, then `∑_{j,g} b j g · w j g ≤ M ω(X)`.

This is ordinary finite additivity of the lower integral: the node values are constants
on Borel incidence sets. No upper density of the source and no comparison between the
source and `ω` is used. -/
theorem referenceCharge_sum {α β : Type*} [MeasurableSpace α] (ω : Measure α) (s : Finset ℕ)
    (I : ℕ → Finset β) (E : ℕ → β → Set α) (hE : ∀ j ∈ s, ∀ g ∈ I j, MeasurableSet (E j g))
    (b w : ℕ → β → ℝ≥0∞) (hw : ∀ j ∈ s, ∀ g ∈ I j, w j g ≤ ω (E j g)) (M : ℝ≥0∞)
    (hpt : ∀ x, ∑ j ∈ s, ∑ g ∈ I j, (E j g).indicator (fun _ => b j g) x ≤ M) :
    ∑ j ∈ s, ∑ g ∈ I j, b j g * w j g ≤ M * ω univ := by
  have hmeas : ∀ j ∈ s, ∀ g ∈ I j, Measurable ((E j g).indicator (fun _ : α => b j g)) :=
    fun j hj g hg => measurable_const.indicator (hE j hj g hg)
  have h1 : ∫⁻ x, ∑ j ∈ s, ∑ g ∈ I j, (E j g).indicator (fun _ => b j g) x ∂ω =
      ∑ j ∈ s, ∫⁻ x, ∑ g ∈ I j, (E j g).indicator (fun _ => b j g) x ∂ω :=
    lintegral_finsetSum s fun j hj => Finset.measurable_sum (I j) fun g hg => hmeas j hj g hg
  have h2 : ∀ j ∈ s, ∫⁻ x, ∑ g ∈ I j, (E j g).indicator (fun _ => b j g) x ∂ω =
      ∑ g ∈ I j, b j g * ω (E j g) := by
    intro j hj
    calc ∫⁻ x, ∑ g ∈ I j, (E j g).indicator (fun _ => b j g) x ∂ω
        = ∑ g ∈ I j, ∫⁻ x, (E j g).indicator (fun _ => b j g) x ∂ω :=
          lintegral_finsetSum (I j) fun g hg => hmeas j hj g hg
      _ = ∑ g ∈ I j, b j g * ω (E j g) :=
          Finset.sum_congr rfl fun g hg => lintegral_indicator_const (hE j hj g hg) (b j g)
  calc ∑ j ∈ s, ∑ g ∈ I j, b j g * w j g
      ≤ ∑ j ∈ s, ∑ g ∈ I j, b j g * ω (E j g) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun g hg =>
          mul_le_mul_right (hw j hj g hg) _
    _ = ∫⁻ x, ∑ j ∈ s, ∑ g ∈ I j, (E j g).indicator (fun _ => b j g) x ∂ω :=
        (h1.trans (Finset.sum_congr rfl h2)).symm
    _ ≤ ∫⁻ _, M ∂ω := lintegral_mono hpt
    _ = M * ω univ := lintegral_const M

end Charging

end ParabolicRectifiability
