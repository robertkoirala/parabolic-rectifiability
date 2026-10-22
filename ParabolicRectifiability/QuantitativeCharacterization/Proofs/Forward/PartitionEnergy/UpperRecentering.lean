import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # Upper recentring

Local ADR in `P(a, ρ)` bounds the mass of every ball `P(y, s) ⊆ P(a, ρ)` with `2s ≤ ρ`, centred
anywhere, by `2^k A s^k`. Route: if `P(y, s)` meets `supp μ` at `b`, then
`P(y, s) ⊆ P(b, 2s)` and the upper ADR bound at `b` applies; otherwise `P(y, s)` lies in the
null set `(supp μ)ᶜ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

open ParabolicRectifiability.Foundations

/-- A ball with a support point `b` lies in the double ball around `b`. -/
theorem d1aupper_ball_subset_ball_double {n : ℕ} {y b : Space n} {s : ℝ}
    (hb : b ∈ Metric.ball y s) : Metric.ball y s ⊆ Metric.ball b (2 * s) := by
  intro x hx
  rw [Metric.mem_ball] at hb hx ⊢
  have := dist_triangle x y b
  rw [dist_comm y b] at this
  linarith

/-- **Upper recentring** (`UpperRecenteringStatement`; `A_* = 2^k A`). -/
theorem d1a_upperRecentering_proof : UpperRecenteringStatement := by
  intro n k μ A a ρ hADR y s hs hsub h2s
  by_cases hmeet : (Metric.ball y s ∩ μ.support).Nonempty
  · obtain ⟨b, hby, hbsupp⟩ := hmeet
    have hbρ : b ∈ Metric.ball a ρ := hsub hby
    have h2spos : (0 : ℝ) < 2 * s := by linarith
    have hup := (hADR b ⟨hbsupp, hbρ⟩ (2 * s) h2spos h2s).2
    calc μ (Metric.ball y s) ≤ μ (Metric.ball b (2 * s)) :=
          measure_mono (d1aupper_ball_subset_ball_double hby)
      _ ≤ ENNReal.ofReal (A * (2 * s) ^ k) := hup
      _ = ENNReal.ofReal (2 ^ k * A * s ^ k) := by
          rw [mul_pow]; congr 1; ring
  · have hdisj : Metric.ball y s ⊆ μ.supportᶜ := by
      intro x hx hxs
      exact hmeet ⟨x, hx, hxs⟩
    have : μ (Metric.ball y s) = 0 :=
      measure_mono_null hdisj Measure.measure_compl_support
    rw [this]
    exact bot_le

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
