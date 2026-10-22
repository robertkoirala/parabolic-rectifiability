import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion
import ParabolicRectifiability.Geometry.Chart.InductionEstimates
import ParabolicRectifiability.Geometry.Chart.RecurrenceEstimates
import ParabolicRectifiability.Geometry.Chart.LevelPartitionsAndCoverage
import ParabolicRectifiability.Geometry.Chart.LimitChart

/-! # `q-chart` for the actual projection limit (`d1e_chart`)

Proves `d1e_chart_proof : d1e_ChartStatement`.

Route. The assembly of `NeckHubTree.vertical_coherent_chart_of_leaves`
for the *given* initial chart `P` and the given `κ`, with
the two chart children A6 and A7 supplied by `recurrences_proof` and
`finite_metric_proof`, A4 by `induction_estimates_proof`,
A9 by `parent_patch_proof`, A5 by `pathBound_of_verticalSquareBound_proof`, A10 by
`coverage_proof`, and A12 by `limit_chart_of_finite`. The
existential limit `G` of `limit_chart_of_finite` satisfies
`|stage F P N u t - G u t| ≤ ε r_N / (1 - h) → 0`, so the stage sequence converges to `G u t`
and `d1e_projectionLimit F P u t = limUnder atTop (stage F P · u t) = G u t` by uniqueness of
limits (`Filter.Tendsto.limUnder_eq`). The conclusions of `G` are then conclusions of
`d1e_projectionLimit F P`. Thresholds `δ₀ = deltaThreshold n σ`, `E₀ = energyThreshold n σ`,
`κ₀ = 1/200`; constant `C = 10 (1 + 12 A + 10 A C_t)`.

Helpers carry the prefix `d1echart_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

open ParabolicRectifiability.Foundations
open CoherentChart

/-- Arithmetic of the stopping constant (copy of the private `glue_arith` of
`NeckHubTree.vertical_coherent_chart_of_leaves`). -/
theorem d1echart_glue_arith {A Ct θ δ X r d : ℝ} (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hθ : 0 ≤ θ)
    (hδ : 0 ≤ δ) (hX : X ≤ θ + 12 * A * δ) (hr : 0 ≤ r) (hrd : r ≤ 10 * d) :
    X * r ≤ (1 + 12 * A + 10 * A * Ct) * 10 * (θ + δ) * d := by
  have h0 : 0 ≤ θ + 12 * A * δ :=
    add_nonneg hθ (mul_nonneg (mul_nonneg (by norm_num) hA) hδ)
  have h1 : X * r ≤ (θ + 12 * A * δ) * r := mul_le_mul_of_nonneg_right hX hr
  have h2 : (θ + 12 * A * δ) * r ≤ (θ + 12 * A * δ) * (10 * d) :=
    mul_le_mul_of_nonneg_left hrd h0
  have hAC : 0 ≤ A * Ct := mul_nonneg hA hCt
  have h3 : θ + 12 * A * δ ≤ (1 + 12 * A + 10 * A * Ct) * (θ + δ) := by
    nlinarith [mul_nonneg hA hθ, mul_nonneg hAC hθ, mul_nonneg hAC hδ]
  have h4 := mul_le_mul_of_nonneg_right h3 (by linarith : (0 : ℝ) ≤ 10 * d)
  linarith

/-- Uniqueness of limits: a sequence within `b N → 0` of `g` has `limUnder` equal to `g`. -/
theorem d1echart_limUnder_eq {E : Type*} [NormedAddCommGroup E] (f : ℕ → E) (g : E)
    (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝 0)) (h : ∀ N, ‖f N - g‖ ≤ b N) :
    limUnder atTop f = g := by
  have hf : Tendsto f atTop (𝓝 g) :=
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun N => norm_nonneg _) h hb)
  exact hf.limUnder_eq

/-- **Same-map identification.** A map `G` within `ε r_N / (1 - h)` of every stage is the
projection limit `d1e_projectionLimit F P`. -/
theorem d1echart_projectionLimit_eq {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι)
    (P : InitialChart F) (ε : ℝ) (G : Spatial m → ℝ → Spatial n)
    (hconv : ∀ (N : ℕ) (u : Spatial m) (t : ℝ),
      ‖stage F P N u t - G u t‖ ≤ ε * F.scale N / (1 - ratio)) :
    d1e_projectionLimit F P = G := by
  have hb : Tendsto (fun N => ε * F.scale N / (1 - ratio)) atTop (𝓝 0) := by
    have h := ((tendsto_scale_zero F).const_mul ε).div_const (1 - ratio)
    rw [mul_zero, zero_div] at h
    exact h
  funext u t
  exact d1echart_limUnder_eq (fun N => stage F P N u t) (G u t) _ hb (fun N => hconv N u t)

/-- **`q-chart` for the actual projection limit**: the type `d1e_ChartStatement`. -/
theorem d1e_chart_proof : d1e_ChartStatement := by
  intro n _hn σ hσ _hσ₁
  obtain ⟨-, -, -, -, -, -, ht, hA⟩ := chartConsts_bounds (n := n) hσ
  have hA0 : 0 ≤ chartA n σ := by linarith
  have hCpos : 0 < 1 + 12 * chartA n σ + 10 * chartA n σ * chartCt n σ := by
    have := mul_nonneg hA0 ht
    linarith
  refine ⟨deltaThreshold n σ, energyThreshold n σ, heightThreshold,
    (1 + 12 * chartA n σ + 10 * chartA n σ * chartCt n σ) * 10, deltaThreshold_pos hσ,
    energyThreshold_pos hσ, by norm_num [heightThreshold], by positivity, ?_⟩
  intro m ι F δ E κ hδ hδ₀ _ hE₀ hκ hκ₀ hF hsq hheight P
  obtain ⟨hsmall, hEsmall, hcovκ, -⟩ := smallness_of_le hσ hδ hδ₀ hE₀ hκ₀
  have hpath : ∀ N : ℕ, PathBoundUpTo F P E N := fun N =>
    pathBound_of_verticalSquareBound_proof (n := n) (m := m) (ι := ι)
      (fun {F σ δ N} hσ hδ hsmall hF P => induction_estimates_proof (F := F) (σ := σ) (δ := δ)
        (N := N) hσ hδ hsmall hF P) hσ hδ hsmall (hF N)
      (fun w => (ENNReal.sum_le_tsum _).trans (hsq w)) P
  obtain ⟨G, hconv, -, hbilip, -, hinit, hcov⟩ :=
    limit_chart_of_finite
      (fun {n m ι F σ δ N} hσ hδ hsmall hF P => induction_estimates_proof (n := n) (m := m)
        (ι := ι) (F := F) (σ := σ) (δ := δ) (N := N) hσ hδ hsmall hF P)
      (fun {n m ι F σ δ E N} hσ hδ hsmall hEsmall hF P hpath =>
        finite_metric_proof (n := n) (m := m) (ι := ι)
          (fun {F σ δ N} hσ hδ hsmall hF P => induction_estimates_proof (F := F) (σ := σ)
            (δ := δ) (N := N) hσ hδ hsmall hF P)
          (F := F) (σ := σ) (δ := δ) (E := E) (N := N) hσ hδ hsmall hEsmall hF P hpath)
      (fun {n m ι F σ δ E κ N} hσ hδ hsmall hEsmall hκ hcov hF hheight P hpath =>
        coverage_proof (n := n) (m := m) (ι := ι)
          (fun {F σ δ N} hσ hδ hsmall hF P => induction_estimates_proof (F := F) (σ := σ)
            (δ := δ) (N := N) hσ hδ hsmall hF P)
          (parent_patch_proof (n := n) (m := m) (ι := ι)
            (fun {F σ δ E N} hσ hδ hsmall hEsmall hF P hpath =>
              recurrences_proof (n := n) (m := m) (ι := ι)
                (fun {F σ δ N} hσ hδ hsmall hF P => induction_estimates_proof (F := F)
                  (σ := σ) (δ := δ) (N := N) hσ hδ hsmall hF P)
                (F := F) (σ := σ) (δ := δ) (E := E) (N := N)
                hσ hδ hsmall hEsmall hF P hpath))
          (F := F) (σ := σ) (δ := δ) (E := E) (κ := κ) (N := N)
          hσ hδ hsmall hEsmall hκ hcov hF hheight P hpath)
      hσ hδ hsmall hEsmall hF P hpath
  -- same-map contract: the existential limit is the actual projection limit
  have hGeq : d1e_projectionLimit F P = G := d1echart_projectionLimit_eq F P _ G hconv
  subst hGeq
  refine ⟨fun p p' => hbilip p.1 p'.1 p.2.val p'.2.val, ?_, ?_⟩
  · exact (hcov κ hκ hcovκ hheight).1
  · obtain ⟨-, hstop⟩ := hcov κ hκ hcovκ hheight
    intro θ hθ c d o ho
    rcases o with _ | ⟨j, a⟩
    · obtain ⟨hp₁, hp₂⟩ := ho
      obtain ⟨u, hu⟩ := hinit c θ hp₁
      refine ⟨u, hu.trans (d1echart_glue_arith hA0 ht hθ hδ ?_ F.initialRadius_pos.le
        (by linarith))⟩
      have he : chartEps n σ δ / (1 - ratio) = 100 / 9 * chartA n σ * δ := by
        rw [chartEps_eq]; unfold ratio; ring
      rw [he]
      nlinarith [mul_nonneg hA0 hδ]
    · obtain ⟨ha, hdist, hinf, hrd⟩ := ho
      obtain ⟨u, hu⟩ := hstop j a ha c θ hdist hinf
      have hb : (θ + 3 * δ) * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio) =
          (θ + 3 * δ + 10 / 9 * chartA n σ * δ) * F.scale j := by
        rw [scale_succ F j, chartEps_eq]; unfold ratio; ring
      refine ⟨u, hu.trans (hb.le.trans
        (d1echart_glue_arith hA0 ht hθ hδ ?_ (scale_pos F j).le (by linarith)))⟩
      nlinarith [mul_nonneg hA0 hδ, mul_nonneg (sub_nonneg.mpr hA) hδ]

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
