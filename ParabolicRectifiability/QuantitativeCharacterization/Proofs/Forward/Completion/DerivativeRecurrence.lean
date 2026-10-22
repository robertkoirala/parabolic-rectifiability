import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion
import ParabolicRectifiability.Geometry.Chart.InductionEstimates
import ParabolicRectifiability.Geometry.Chart.RecurrenceEstimates
import ParabolicRectifiability.Geometry.Chart.LevelPartitionsAndCoverage

/-! # The derivative recurrence of the actual stages

Proof of `d1e_derivative_recurrence_proof : d1e_DerivativeRecurrenceStatement`.

Route, at one parameter `(u,t)` and one level `j`, along the actual path (no supremum over
parameters). Truncate at `N = j`: infinite coherence gives `IsCoherentUpTo σ δ j`, and the
vertical square bound gives the path bound `PathBoundUpTo F P E j` (base A5
`pathBound_of_verticalSquareBound_proof`, fed with A4 `induction_estimates_proof`).

* Base A4 (active tangent/height clause) gives, through `HardLeaves2.exists_alpha_height`, the
  separate maxima `α, H ≥ 0` over the active indices at the path point with
  `α + H ≤ (A/h) d_j` and `α + H ≤ ε`.
* `HardLeaves2.level_bounds` (the base `CoherentProjection.one_step` and
  `CoherentProjection.hessian_norm_le` through `PartitionAdapter` and
  `PartitionHessianAdapter`) gives `‖D_xσ_j‖ ≤ 1 + C₀H`, `|∂_tσ_j| ≤ C₀H/r_j` and
  `‖D_x²σ_j[v,w]‖ ≤ C₁(α+H)/r_j |v||w|` on the actual tangent space; base A6
  (`HardLeaves2.speed_bounds`) gives the spatial speed `≤ 1.01`.
* The chain rules (6.2) (`HardLeaves2.fderiv_fderiv_stage_succ_apply`,
  `HardLeaves2.deriv_stage_succ`) then give `‖D_u²F_{j+1}‖ ≤ (1+C₀H)‖D_u²F_j‖ + 1.0201 C₁(α+H)/r_j`
  and `|∂_tF_{j+1}| ≤ (1+C₀H)|∂_tF_j| + C₀H/r_j`. Multiplying by `r_{j+1} = h r_j`, `h = 1/10`,
  and using `h(1 + C₀H) ≤ h(1 + C₂ε) ≤ 1/2` (`DeltaSmall.contraction`) gives
  `b_{j+1} ≤ b_j/2 + A(2C₁ + C₀) d_j`.
* The displacement is the weighted projection identity (first conclusion of
  `one_step_parabolicWeight`): `|F_{j+1} - F_j| = |σ_j(F_j) - F_j| ≤ H r_j ≤ 10 A r_j d_j`.

Inactive points need no separate case: every one-step bound above holds at every point, and its
geometric hypotheses are required only at active indices; at a point with no active index they
are vacuous (the stage increment's relevant jet vanishes, so the bounds hold with any `α, H ≥ 0`).
No identity neighbourhood is used.

The constant is `C = A (2 C₁ + C₀ + 10)`, the thresholds `δ₀ = deltaThreshold n σ`,
`E₀ = energyThreshold n σ`; all depend only on `n, σ`. Also proved: `b_0 = 0`
(`d1erecur_curvature_zero`), since `F_0` is time-independent affine.
-/

set_option autoImplicit false

noncomputable section

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

open CoherentChart

/-- The constant `C = A (2 C₁ + C₀ + 10)` of the recurrence and the displacement bound. -/
def d1erecur_const (n : ℕ) (σ : ℝ) : ℝ :=
  chartA n σ * (2 * chartC₁ n σ + chartC₀ n σ + 10)

theorem d1erecur_const_nonneg {n : ℕ} {σ : ℝ} (hσ : 0 < σ) : 0 ≤ d1erecur_const n σ := by
  obtain ⟨h0, hC1, -, -, -, -, -, hA⟩ := chartConsts_bounds (n := n) hσ
  unfold d1erecur_const
  exact mul_nonneg (by linarith) (by linarith)

/-- The scalar step: from `D₂' ≤ k D₂ + c₁/r`, `T' ≤ k T + c₀/r`, `h k ≤ 1/2` and
`h (c₁ + c₀) ≤ K d` follows `h r (D₂' + T') ≤ (r (D₂ + T))/2 + K d`. -/
theorem d1erecur_step_arith {h r D2 T D2' T' k c₁ c₀ d K : ℝ}
    (hh : 0 ≤ h) (hr : 0 < r) (hD2 : 0 ≤ D2) (hT : 0 ≤ T)
    (hk : h * k ≤ 1 / 2) (hc : h * (c₁ + c₀) ≤ K * d)
    (h2 : D2' ≤ k * D2 + c₁ / r) (h3 : T' ≤ k * T + c₀ / r) :
    h * r * (D2' + T') ≤ 1 / 2 * (r * (D2 + T)) + K * d := by
  have e1 : r * (c₁ / r) = c₁ := mul_div_cancel₀ c₁ hr.ne'
  have e0 : r * (c₀ / r) = c₀ := mul_div_cancel₀ c₀ hr.ne'
  have e : h * r * (k * D2 + c₁ / r + (k * T + c₀ / r)) =
      h * k * (r * (D2 + T)) + h * (c₁ + c₀) := by
    linear_combination h * e1 + h * e0
  have hb : 0 ≤ r * (D2 + T) := mul_nonneg hr.le (add_nonneg hD2 hT)
  calc h * r * (D2' + T') ≤ h * r * (k * D2 + c₁ / r + (k * T + c₀ / r)) :=
        mul_le_mul_of_nonneg_left (add_le_add h2 h3) (mul_nonneg hh hr.le)
    _ = h * k * (r * (D2 + T)) + h * (c₁ + c₀) := e
    _ ≤ 1 / 2 * (r * (D2 + T)) + K * d :=
        add_le_add (mul_le_mul_of_nonneg_right hk hb) hc

/-- `b_0 = 0`: the initial stage `F_0 = x_* + U_* u` is time-independent affine, so its second
spatial derivative and its time derivative vanish (used downstream for
`b_j ≤ C ∑_{i<j} 2^{-(j-1-i)} d_i`). -/
theorem d1erecur_curvature_zero {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι)
    (P : InitialChart F) (u : Spatial m) (t : ℝ) : d1e_curvature F P 0 u t = 0 := by
  unfold d1e_curvature
  rw [HardLeaves2.fderiv_fderiv_stage_zero, HardLeaves2.deriv_stage_zero,
    ContinuousLinearMap.opNorm_zero, norm_zero, add_zero, mul_zero]

/-- **The recurrence at one level, for a truncation `N = j`.** Under the finite coherence and
the path bound through level `j`, at every parameter: `b_{j+1} ≤ b_j/2 + C d_j` and
`|F_{j+1} - F_j| ≤ C r_j d_j`, with `C = d1erecur_const n σ`. -/
theorem d1erecur_level {n m : ℕ} {ι : Type*} {F : CoherentFamily n m ι} {σ δ E : ℝ} {j : ℕ}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) (hEsmall : EnergySmall n σ E)
    (hF : F.IsCoherentUpTo σ δ j) (P : InitialChart F) (hpath : PathBoundUpTo F P E j)
    (u : Spatial m) (t : ℝ) :
    d1e_curvature F P (j + 1) u t ≤
        1 / 2 * d1e_curvature F P j u t + d1erecur_const n σ * d1e_pathError F P j u t ∧
      ‖stage F P (j + 1) u t - stage F P j u t‖ ≤
        d1erecur_const n σ * F.scale j * d1e_pathError F P j u t := by
  obtain ⟨h0, hC1, hC2, -, -, -, -, hA⟩ := chartConsts_bounds (n := n) hσ
  have hC0 : 0 ≤ chartC₀ n σ := by linarith
  have hA0 : 0 ≤ chartA n σ := by linarith
  have hε := chartEps_nonneg (n := n) hσ hδ
  have hC02 := HardLeaves2.chartC₀_le_chartC₂ (n := n) hσ
  have hr := scale_pos F j
  have hact : HardLeaves2.ActiveBound F P σ j := (induction_estimates_proof hσ hδ hsmall hF P).2.1
  obtain ⟨α, H, hα, hH, hsumA, hsumε, he, hc⟩ :=
    HardLeaves2.exists_alpha_height hσ hδ hF hact le_rfl u t
  obtain ⟨hDs, hdt, -, hhess⟩ := HardLeaves2.level_bounds hσ hF le_rfl (stage F P j u t) t
    (tangent F P j u t) α H hα hH he hc
  have hspeed : ∀ v : Spatial m,
      ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ≤ 101 / 100 * ‖v‖ := fun v =>
    (HardLeaves2.speed_bounds hσ hδ hsmall hEsmall hF hact hpath j (Nat.le_succ j) u t v).2
  -- the path coefficient of the statement is the base `pathCoeff`
  have hdef : d1e_pathError F P j u t = HardLeaves2.pathCoeff F P j u t := rfl
  have hd0 : 0 ≤ HardLeaves2.pathCoeff F P j u t := HardLeaves2.pathCoeff_nonneg j u t
  set d := HardLeaves2.pathCoeff F P j u t
  have hk0 : 0 ≤ 1 + chartC₀ n σ * H := add_nonneg zero_le_one (mul_nonneg hC0 hH)
  have hαH0 : 0 ≤ α + H := add_nonneg hα hH
  -- `h (α + H) ≤ A d_j`
  have hαH : ratio * (α + H) ≤ chartA n σ * d := by
    calc ratio * (α + H) ≤ ratio * (chartA n σ / ratio * d) :=
          mul_le_mul_of_nonneg_left hsumA ratio_pos.le
      _ = chartA n σ * d := by rw [← mul_assoc, mul_div_cancel₀ _ ratio_pos.ne']
  have hratio : ratio = 1 / 10 := rfl
  have hCsplit : d1erecur_const n σ * d =
      10 * (chartA n σ * d) + chartA n σ * (2 * chartC₁ n σ + chartC₀ n σ) * d := by
    unfold d1erecur_const; ring
  have hCrest : 0 ≤ chartA n σ * (2 * chartC₁ n σ + chartC₀ n σ) * d :=
    mul_nonneg (mul_nonneg hA0 (by linarith)) hd0
  refine ⟨?_, ?_⟩
  · -- the second spatial derivative, by the second chain rule
    have hD2 : ‖fderiv ℝ (fun v => fderiv ℝ (fun w => stage F P (j + 1) w t) v) u‖ ≤
        (1 + chartC₀ n σ * H) * ‖fderiv ℝ (fun v => fderiv ℝ (fun w => stage F P j w t) v) u‖ +
          10201 / 10000 * (chartC₁ n σ * (α + H)) / F.scale j := by
      refine ContinuousLinearMap.opNorm_le_bound₂ _
        (add_nonneg (mul_nonneg hk0 (ContinuousLinearMap.opNorm_nonneg _))
          (div_nonneg (mul_nonneg (by norm_num) (mul_nonneg hC1 hαH0)) hr.le)) fun v w => ?_
      rw [HardLeaves2.fderiv_fderiv_stage_succ_apply]
      have hv := norm_nonneg v
      have hw := norm_nonneg w
      have hA1 : ‖fderiv ℝ (fun x => stageMap F j x t) (stage F P j u t)
          (fderiv ℝ (fun y => fderiv ℝ (fun w => stage F P j w t) y) u v w)‖ ≤
          (1 + chartC₀ n σ * H) *
            (‖fderiv ℝ (fun y => fderiv ℝ (fun w => stage F P j w t) y) u‖ * ‖v‖ * ‖w‖) :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul hDs (ContinuousLinearMap.le_opNorm₂ _ v w) (norm_nonneg _) hk0)
      have hA2 : ‖fderiv ℝ (fderiv ℝ (fun x => stageMap F j x t)) (stage F P j u t)
          (fderiv ℝ (fun w => stage F P j w t) u v) (fderiv ℝ (fun w => stage F P j w t) u w)‖ ≤
          chartC₁ n σ * (α + H) / F.scale j * (101 / 100 * ‖v‖ * (101 / 100 * ‖w‖)) := by
        have h : ‖fderiv ℝ (fderiv ℝ (fun x => stageMap F j x t)) (stage F P j u t)
            (fderiv ℝ (fun w => stage F P j w t) u v) (fderiv ℝ (fun w => stage F P j w t) u w)‖ ≤
            chartC₁ n σ * (α + H) / F.scale j * ‖fderiv ℝ (fun w => stage F P j w t) u v‖ *
              ‖fderiv ℝ (fun w => stage F P j w t) u w‖ :=
          hhess _ (LinearMap.mem_range_self _ v) _ (LinearMap.mem_range_self _ w)
        have hpq : ‖fderiv ℝ (fun w => stage F P j w t) u v‖ *
            ‖fderiv ℝ (fun w => stage F P j w t) u w‖ ≤
            101 / 100 * ‖v‖ * (101 / 100 * ‖w‖) :=
          mul_le_mul (hspeed v) (hspeed w) (norm_nonneg _) (by positivity)
        have hX : 0 ≤ chartC₁ n σ * (α + H) / F.scale j :=
          div_nonneg (mul_nonneg hC1 hαH0) hr.le
        exact h.trans ((mul_assoc _ _ _).trans_le (mul_le_mul_of_nonneg_left hpq hX))
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ (1 + chartC₀ n σ * H) *
              (‖fderiv ℝ (fun y => fderiv ℝ (fun w => stage F P j w t) y) u‖ * ‖v‖ * ‖w‖) +
            chartC₁ n σ * (α + H) / F.scale j * (101 / 100 * ‖v‖ * (101 / 100 * ‖w‖)) :=
            add_le_add hA1 hA2
        _ = ((1 + chartC₀ n σ * H) *
              ‖fderiv ℝ (fun v => fderiv ℝ (fun w => stage F P j w t) v) u‖ +
            10201 / 10000 * (chartC₁ n σ * (α + H)) / F.scale j) * ‖v‖ * ‖w‖ := by ring
    -- the time derivative, by the time chain rule
    have hT : ‖deriv (fun s => stage F P (j + 1) u s) t‖ ≤
        (1 + chartC₀ n σ * H) * ‖deriv (fun s => stage F P j u s) t‖ +
          chartC₀ n σ * H / F.scale j := by
      rw [HardLeaves2.deriv_stage_succ]
      exact (norm_add_le _ _).trans (add_le_add ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hDs (norm_nonneg _))) hdt)
    -- the contraction `h (1 + C₀ H) ≤ 1/2`
    have hk : ratio * (1 + chartC₀ n σ * H) ≤ 1 / 2 := by
      have hHε : H ≤ chartEps n σ δ := by linarith
      have hCH : chartC₀ n σ * H ≤ chartC₂ n σ * chartEps n σ δ := mul_le_mul hC02 hHε hH hC2
      calc ratio * (1 + chartC₀ n σ * H) ≤ ratio * (1 + chartC₂ n σ * chartEps n σ δ) :=
            mul_le_mul_of_nonneg_left (by linarith) ratio_pos.le
        _ ≤ 1 / 2 := hsmall.contraction
    -- the forcing `h (1.0201 C₁ (α + H) + C₀ H) ≤ C d_j`
    have hforce : ratio * (10201 / 10000 * (chartC₁ n σ * (α + H)) + chartC₀ n σ * H) ≤
        d1erecur_const n σ * d := by
      have h1 : 10201 / 10000 * (chartC₁ n σ * (α + H)) + chartC₀ n σ * H ≤
          (2 * chartC₁ n σ + chartC₀ n σ) * (α + H) := by
        have hX := mul_nonneg hC1 hαH0
        have hCH : chartC₀ n σ * H ≤ chartC₀ n σ * (α + H) :=
          mul_le_mul_of_nonneg_left (by linarith) hC0
        have e : (2 * chartC₁ n σ + chartC₀ n σ) * (α + H) =
            2 * (chartC₁ n σ * (α + H)) + chartC₀ n σ * (α + H) := by ring
        linarith
      have h2 : ratio * ((2 * chartC₁ n σ + chartC₀ n σ) * (α + H)) ≤
          (2 * chartC₁ n σ + chartC₀ n σ) * (chartA n σ * d) := by
        have hm := mul_le_mul_of_nonneg_left hαH
          (show 0 ≤ 2 * chartC₁ n σ + chartC₀ n σ by linarith)
        calc ratio * ((2 * chartC₁ n σ + chartC₀ n σ) * (α + H)) =
              (2 * chartC₁ n σ + chartC₀ n σ) * (ratio * (α + H)) := by ring
          _ ≤ _ := hm
      have e2 : (2 * chartC₁ n σ + chartC₀ n σ) * (chartA n σ * d) =
          chartA n σ * (2 * chartC₁ n σ + chartC₀ n σ) * d := by ring
      have hAd : 0 ≤ chartA n σ * d := mul_nonneg hA0 hd0
      calc _ ≤ ratio * ((2 * chartC₁ n σ + chartC₀ n σ) * (α + H)) :=
            mul_le_mul_of_nonneg_left h1 ratio_pos.le
        _ ≤ _ := h2
        _ = _ := e2
        _ ≤ d1erecur_const n σ * d := by linarith
    unfold d1e_curvature
    rw [scale_succ F j, hdef]
    exact d1erecur_step_arith ratio_pos.le hr (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _)
      hk hforce hD2 hT
  · -- the displacement, by the weighted projection identity
    have hdisj : (F.index j : Set ι).PairwiseDisjoint
        (fun a => Metric.ball (F.center j a) (σ * F.scale j / 3)) := by
      intro a ha b hb hab
      have hsep := hF.separated j le_rfl a ha b hb hab
      have hpos : 0 < σ * F.scale j := mul_pos hσ hr
      exact Metric.ball_disjoint_ball (by linarith)
    have hdisp : ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ H * F.scale j :=
      (one_step_parabolicWeight hσ hr (F.index j) (F.center j) hdisj (F.plane j)
        (stage F P j u t) t H α hH hα he (tangent F P j u t) hc).1
    have hHd : H ≤ d1erecur_const n σ * d := by
      have h1 : ratio * H ≤ chartA n σ * d := by
        have := mul_nonneg ratio_pos.le hα
        linarith
      rw [hratio] at h1
      linarith
    rw [hdef]
    calc ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ H * F.scale j := hdisp
      _ ≤ d1erecur_const n σ * d * F.scale j := mul_le_mul_of_nonneg_right hHd hr.le
      _ = d1erecur_const n σ * F.scale j * d := by ring

/-- **The derivative recurrence of the actual stages**
(`d1e_DerivativeRecurrenceStatement`).
Constants: `C = A (2 C₁ + C₀ + 10)`, `δ₀ = deltaThreshold n σ`, `E₀ = energyThreshold n σ`.
At a level `j`, the infinite data are truncated at `N = j` (finite coherence, and the path
bound from the vertical square bound by base A5). -/
theorem d1e_derivative_recurrence_proof : d1e_DerivativeRecurrenceStatement := by
  intro n σ hσ _hσ₁
  refine ⟨d1erecur_const n σ, deltaThreshold n σ, energyThreshold n σ,
    d1erecur_const_nonneg hσ, deltaThreshold_pos hσ, energyThreshold_pos hσ, ?_⟩
  intro m ι F δ E hδ hδ₀ _hE hE₀ hF hsq P u t j
  obtain ⟨hsmall, hEsmall, -, -⟩ :=
    smallness_of_le (κ := 0) hσ hδ hδ₀ hE₀ (by norm_num [heightThreshold])
  have hpath : PathBoundUpTo F P E j :=
    pathBound_of_verticalSquareBound_proof (n := n) (m := m) (ι := ι)
      (fun {F σ δ N} hσ hδ hsmall hF P => induction_estimates_proof (F := F) (σ := σ) (δ := δ)
        (N := N) hσ hδ hsmall hF P) hσ hδ hsmall (hF j)
      (fun w => (ENNReal.sum_le_tsum _).trans (hsq w)) P
  exact d1erecur_level hσ hδ hsmall hEsmall (hF j) P hpath u t

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
