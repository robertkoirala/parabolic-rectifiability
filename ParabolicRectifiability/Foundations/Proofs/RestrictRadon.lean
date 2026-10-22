import ParabolicRectifiability.Foundations.Statements.Measurability

/-! # Proof of `RestrictLocallyRadonStatement`

Finiteness on compacts of a restriction is the
Mathlib instance. Inner regularity: `μ.InnerRegular` gives `InnerRegularCompactLTTop μ`, which
restricts; the restriction is finite on compacts, hence sigma-finite (`source_sigmaFinite`),
and inner regularity follows from `InnerRegularCompactLTTop` plus sigma-finiteness. -/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Foundations

theorem restrict_isFiniteMeasureOnCompacts_innerRegular_proof :
    RestrictLocallyRadonStatement := by
  intro n _ μ hμ hin E _
  have h1 : IsFiniteMeasureOnCompacts (μ.restrict E) := inferInstance
  have h2 : Measure.InnerRegularCompactLTTop (μ.restrict E) := by
    have : Measure.InnerRegularCompactLTTop μ := inferInstance
    infer_instance
  have h3 : SigmaFinite (μ.restrict E) := source_sigmaFinite _
  exact ⟨h1, inferInstance⟩

end ParabolicRectifiability.Foundations
