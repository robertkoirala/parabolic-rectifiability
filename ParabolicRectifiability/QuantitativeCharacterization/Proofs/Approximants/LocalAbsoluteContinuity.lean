import ParabolicRectifiability.QuantitativeCharacterization.Statements.ApproximantComponents
import ParabolicRectifiability.Foundations.Proofs.UpperGrowth
import ParabolicRectifiability.Foundations.Proofs.RestrictRadon

/-! # Local absolute continuity

Proof of `dp2_LocalAbsoluteContinuityStatement`, i.e. of `QuantitativeCharacterization.dp2_local_absolute_continuity`.

Proof idea. With `λ = μ⌊P(a,R)`:
1. `λ` is locally Radon (`Foundations.restrict_isFiniteMeasureOnCompacts_innerRegular_proof`);
2. all-centre growth `λ(P(p,r)) ≤ 2^k A r^k` for `0 < r ≤ R`: if `λ(P(p,r)) > 0`, a support point
   `z ∈ P(p,r) ∩ P(a,R)` of `μ` has `z ∈ P(a,2LR)`, `P(p,r) ⊆ P(z,2r)` and `2r ≤ 2R ≤ 2LR`, so the
   hypothesis at `(z, 2r)` applies. No case on the sign of `A` is needed (`ofReal` of a negative
   number is `0`, and the hypothesis then says the same);
3. the growth criterion `Foundations.fgac_absolutelyContinuous_hausdorffP_of_growth_proof`
   with `B = 2^k A`, `r₀ = R`.

Helpers carry the prefix `dp2_lac_`. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- All-centre growth of the restriction to the root ball, for radii `r ≤ R`. -/
theorem dp2_lac_restrict_ball_le {n : ℕ} (k : ℕ) (A L : ℝ) (hL : 1 ≤ L)
    (μ : Measure (Space n)) (a : Space n) (R : ℝ) (hR : 0 < R)
    (hgrowth : ∀ b ∈ μ.support ∩ Metric.ball a (2 * L * R), ∀ s : ℝ, 0 < s → s ≤ 2 * L * R →
      μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k))
    (p : Space n) (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    μ.restrict (Metric.ball a R) (Metric.ball p r) ≤ ENNReal.ofReal (2 ^ k * A * r ^ k) := by
  have hLR : R ≤ L * R := by nlinarith
  rw [Measure.restrict_apply measurableSet_ball]
  by_cases h0 : μ (Metric.ball p r ∩ Metric.ball a R) = 0
  · rw [h0]; exact zero_le
  have hpos : 0 < μ (Metric.ball p r ∩ Metric.ball a R) := pos_iff_ne_zero.2 h0
  obtain ⟨z, ⟨hzp, hza⟩, hzs⟩ := Measure.nonempty_inter_support_of_pos hpos
  have hza' : z ∈ Metric.ball a (2 * L * R) := by
    rw [Metric.mem_ball] at hza ⊢
    linarith
  have hsub : Metric.ball p r ∩ Metric.ball a R ⊆ Metric.ball z (2 * r) := by
    intro y hy
    have hy1 := hy.1
    rw [Metric.mem_ball] at hy1 hzp ⊢
    have := dist_triangle y p z
    rw [dist_comm p z] at this
    linarith
  refine (measure_mono hsub).trans ((hgrowth z ⟨hzs, hza'⟩ (2 * r) (by linarith)
    (by linarith)).trans ?_)
  refine le_of_eq ?_
  congr 1
  rw [mul_pow]
  ring

/-- **LAC**, local absolute continuity: `μ⌊P(a,R) ≪ H_P^k` from growth at the permitted centres
and radii `≤ 2LR`. -/
theorem dp2_local_absolute_continuity_proof : dp2_LocalAbsoluteContinuityStatement := by
  intro n hn k hk hkn A L hL μ hfin hinner a R hR hgrowth
  obtain ⟨hlamfin, hlaminner⟩ :=
    restrict_isFiniteMeasureOnCompacts_innerRegular_proof n hn μ hfin hinner (Metric.ball a R)
      measurableSet_ball
  exact fgac_absolutelyContinuous_hausdorffP_of_growth_proof n hn k hk hkn
    (μ.restrict (Metric.ball a R)) hlamfin hlaminner (2 ^ k * A) R hR
    (fun p r hr hrR => dp2_lac_restrict_ball_le k A L hL μ a R hR hgrowth p r hr hrR)

end ParabolicRectifiability.QuantitativeCharacterization
