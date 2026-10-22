import ParabolicRectifiability.BetaP.Statements.Laws
import ParabolicRectifiability.BetaP.Proofs.Laws.Fitting

/-! # Borel measurability of `B_p`, `S_p^a`, `T_p^a`

`BetaPowMeasurabilityStatement`. `(z,r) ↦ B_p(z,r)` is jointly Borel by the countable fitting
family (`cfit_measurable_betaPow`); `S_p^a` and `T_p^a` are Borel in the
centre as parameter `lintegral`s against the s-finite `scaleMeasure` restricted to `(0,a)`
(`Measurable.lintegral_prod_right`), as for `measurable_squareEnergy`. Availability and inner
regularity are not used; local finiteness is.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- `S_p^a` is Borel in the centre (finite-on-compacts source, `p ≥ 0`, any endpoint). -/
theorem cfit_measurable_energyS {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ) (T : FamilyKind) {p : ℝ} (hp : 0 ≤ p) (a : ℝ) :
    Measurable (energyS μ k T p a) :=
  Measurable.lintegral_prod_right (ν := scaleMeasure.restrict (Ioo 0 a))
    (f := fun z r => betaPow μ k T p z r ^ (2 / p))
    ((cfit_measurable_betaPow μ k T hp).pow_const (2 / p))

/-- `T_p^a` is Borel in the centre (finite-on-compacts source, `p ≥ 0`, any endpoint). -/
theorem cfit_measurable_energyT {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ) (T : FamilyKind) {p : ℝ} (hp : 0 ≤ p) (a : ℝ) :
    Measurable (energyT μ k T p a) :=
  Measurable.lintegral_prod_right (ν := scaleMeasure.restrict (Ioo 0 a))
    (f := fun z r => betaPow μ k T p z r) (cfit_measurable_betaPow μ k T hp)

/-- Borel measurability of `B_p`, `S_p^a`, `T_p^a` (`BetaPowMeasurabilityStatement`). -/
theorem cfit_betaPowMeasurability_proof : BetaPowMeasurabilityStatement := by
  intro n _ k _ _ T _ μ hμ _ p hp
  exact ⟨cfit_measurable_betaPow μ k T hp.le, fun a _ =>
    ⟨cfit_measurable_energyS μ k T hp.le a, cfit_measurable_energyT μ k T hp.le a⟩⟩

end ParabolicRectifiability.BetaP
