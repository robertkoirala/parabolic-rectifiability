import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ProjectionEnergy

/-! # Continuity of the finite-stage derivative size `b_j`

Proof of `d1e2_CurvatureContinuousStatement`.

Proof sketch: the stage map `G(u,t) = CoherentChart.stage F P j u t` is jointly `C^∞`
(`CoherentChart.contDiff_stage`). Parametric derivatives of a jointly smooth map are jointly
smooth (`ContDiff.fderiv`): twice in the spatial variable for `D_u² G`, once in time for
`∂_t G` (`deriv = fderiv · 1`). Composition with `p ↦ (p.1, p.2.val)` on the base `Space m`
(`Metric.Snowflaking.continuous_ofSnowflaking`) gives continuity of
`b_j(u,t) = r_j (‖D_u² F_j(u,t)‖ + |∂_t F_j(u,t)|)`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-- For a jointly smooth `G : ℝ^m × ℝ → ℝ^n`, the second spatial derivative
`(u,t) ↦ D_u² G(u,t)` is jointly continuous. -/
theorem d1e2ccont_continuous_spatialSecondDeriv {m n : ℕ} {G : Spatial m × ℝ → Spatial n}
    (hG : ContDiff ℝ ∞ G) :
    Continuous fun x : Spatial m × ℝ =>
      fderiv ℝ (fun v => fderiv ℝ (fun w => G (w, x.2)) v) x.1 := by
  have hG2 : ContDiff ℝ 2 G := hG.of_le (by simp)
  have h1 : ContDiff ℝ 1 fun x : Spatial m × ℝ => fderiv ℝ (fun w => G (w, x.2)) x.1 := by
    refine ContDiff.fderiv (f := fun (x : Spatial m × ℝ) (w : Spatial m) => G (w, x.2))
      (g := fun x => x.1) ?_ contDiff_fst one_add_one_eq_two.le
    exact hG2.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
  have h2 : ContDiff ℝ 0 fun x : Spatial m × ℝ =>
      fderiv ℝ (fun v => fderiv ℝ (fun w => G (w, x.2)) v) x.1 := by
    refine ContDiff.fderiv (f := fun (x : Spatial m × ℝ) (v : Spatial m) =>
        fderiv ℝ (fun w => G (w, x.2)) v) (g := fun x => x.1) ?_ contDiff_fst (zero_add 1).le
    exact h1.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
  exact h2.continuous

/-- For a jointly smooth `G : ℝ^m × ℝ → ℝ^n`, the time derivative `(u,t) ↦ ∂_t G(u,t)` is
jointly continuous. -/
theorem d1e2ccont_continuous_timeDeriv {m n : ℕ} {G : Spatial m × ℝ → Spatial n}
    (hG : ContDiff ℝ ∞ G) :
    Continuous fun x : Spatial m × ℝ => deriv (fun s => G (x.1, s)) x.2 := by
  have hG1 : ContDiff ℝ 1 G := (hG.of_le (by simp) : ContDiff ℝ 2 G).of_le one_le_two
  have h0 : ContDiff ℝ 0 fun x : Spatial m × ℝ => fderiv ℝ (fun s => G (x.1, s)) x.2 := by
    refine ContDiff.fderiv (f := fun (x : Spatial m × ℝ) (s : ℝ) => G (x.1, s))
      (g := fun x => x.2) ?_ contDiff_snd (zero_add 1).le
    exact hG1.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact h0.continuous.clm_apply continuous_const

/-- The base coordinates `p ↦ (p.1, p.2.val)` of `Space m` are continuous. -/
theorem d1e2ccont_continuous_coords {m : ℕ} :
    Continuous fun p : Space m => (p.1, p.2.val) :=
  continuous_fst.prodMk (Metric.Snowflaking.continuous_ofSnowflaking.comp continuous_snd)

/-- **Continuity of `b_j`**: the normalized derivative size
`b_j(u,t) = r_j (‖D_u² F_j(u,t)‖ + |∂_t F_j(u,t)|)` of every finite stage is continuous. -/
theorem d1e2_curvature_continuous_proof : d1e2_CurvatureContinuousStatement := by
  intro n m ι F P j
  have hG := CoherentChart.contDiff_stage F P j
  have h2 : Continuous fun p : Space m =>
      fderiv ℝ (fun v => fderiv ℝ (fun w => CoherentChart.stage F P j w p.2.val) v) p.1 :=
    (d1e2ccont_continuous_spatialSecondDeriv hG).comp d1e2ccont_continuous_coords
  have ht : Continuous fun p : Space m =>
      deriv (fun s => CoherentChart.stage F P j p.1 s) p.2.val :=
    (d1e2ccont_continuous_timeDeriv hG).comp d1e2ccont_continuous_coords
  have h2n : Continuous fun p : Space m =>
      ‖fderiv ℝ (fun v => fderiv ℝ (fun w => CoherentChart.stage F P j w p.2.val) v) p.1‖ :=
    -- the norm and topology of the iterated operator space are fixed explicitly
    (continuous_norm (E := Spatial m →L[ℝ] Spatial m →L[ℝ] Spatial n)).comp h2
  have htn : Continuous fun p : Space m =>
      ‖deriv (fun s => CoherentChart.stage F P j p.1 s) p.2.val‖ :=
    (continuous_norm (E := Spatial n)).comp ht
  unfold d1e_curvature
  exact continuous_const.fun_mul (h2n.fun_add htn)

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
