import ParabolicRectifiability.Foundations.Proofs.DensityBridges.PackingMassLemmas

/-! # Packing turns lower density into retained mass: assembly

`fpack_packing_mass` has exactly the type `PackingMassStatement` of
`restrict_ball_le_of_packing_lowerDensity`.

Assembly (the limiting step `ε ↓ 0`): `fpack_restrict_ball_le_add_of_fivefold`, fed with the
fivefold input, gives `(ρ₀⌊K)(P(q,ρ)) ≤ ofReal (5^k C_K (A+ε) ρ^k)` for every `ε > 0`; the right
side is continuous in `ε` and tends to `ofReal (5^k C_K A ρ^k)` as `ε ↓ 0`, so `ge_of_tendsto`
gives the bound. Nothing is assumed beyond the statement's own hypotheses.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ParabolicRectifiability.Foundations

/-- **Packing turns lower density into retained mass**: `PackingMassStatement`. -/
theorem fpack_packing_mass : PackingMassStatement := by
  intro n hn k hk hkn K hK R₀ C_K hR₀ hC hpack ρ₀ hfin hreg A hA hdens q ρ hρ hρR
  have hε : ∀ ε : ℝ, 0 < ε →
      ρ₀.restrict K (Metric.ball q ρ) ≤ ENNReal.ofReal (5 ^ k * C_K * (A + ε) * ρ ^ k) :=
    fpack_restrict_ball_le_add_of_fivefold fpack_input_fivefold n hn k hk hkn K hK R₀ C_K hR₀
      hC hpack ρ₀ hfin hreg A hA hdens q ρ hρ hρR
  have hcont : Continuous fun ε : ℝ => ENNReal.ofReal (5 ^ k * C_K * (A + ε) * ρ ^ k) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (5 ^ k * C_K * (A + ε) * ρ ^ k))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (5 ^ k * C_K * A * ρ ^ k))) :=
    (hcont.tendsto' 0 _ (by simp only [add_zero])).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε' => hε ε hε')

end ParabolicRectifiability.Foundations
