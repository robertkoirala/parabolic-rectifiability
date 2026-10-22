import ParabolicRectifiability.Geometry.Chart.Construction

/-!
# The limiting chart from the finite estimates

Infinite form of the coherent chart theorem: the recursion `F_{j+1} = σ_j(F_j, t)`
(`stage`) converges to a limiting chart with the metric, closed-image and coverage
conclusions of `CoherentChart.limit_chart`. The theorem `limit_chart_of_finite` shows
that the statements of `induction_estimates`, `finite_metric` and `coverage`, taken as
hypotheses, imply the statement of `limit_chart`; the four statements are restated
here. Hypothesis names of the restated binders that are never referenced are written `_`.

Proof.
* **Uniform convergence.** The induction estimates at truncation `N = i` give the displacement
  `|F_{i+1} - F_i| ≤ ε r_i` for every `i`; the geometric sum
  `norm_sub_le_geometric` gives `|F_l - F_k| ≤ ε r_k/(1-h)` for `k ≤ l`. Since
  `r_k → 0` the sequence is uniformly Cauchy; one limit `G(u,t)` is chosen once, before
  any `κ`, and `|F_N - G| ≤ ε r_N/(1-h)` follows by passing to the limit.
* **Metric bounds.** `finite_metric` at `N = j` gives the time modulus and the
  bi-Lipschitz bounds for `F_j`;
  both are closed conditions and pass to the pointwise limit.
* **Closed image.** `Φ(p) = (G(p), t)` is bi-Lipschitz on the complete space
  `Space m`, hence has closed range.
* **Initial-plane stopping.** `F_0(u,t) = x_* + U_* u` parametrizes `L_*` for every
  `t`; the nearest point of `L_*` to `x_c` is some `F_0(u, t_c)`, so
  `|G(u,t_c) - x_c| ≤ θ r_0 + ε r_0/(1-h)`. No time anchor is used.
* **Coverage.** Under the coverage condition and center heights, `coverage` at `N = j` gives
  `|F_{j+1}(u,t_c) - x_c| ≤ (θ + 3δ) r_j`, and uniform convergence adds
  `ε r_{j+1}/(1-h)`. For a level limit `z = lim z_i`, `coverage` at each center's own time gives
  parameters with `|G(u_i, t_i) - x_i| ≤ (η + ε/(1-h)) r_{l_i} → 0`, so
  `Φ(u_i, t_i) → z` and `z` lies in the closed image.
-/

noncomputable section

namespace ParabolicRectifiability

namespace CoherentChart

open scoped ENNReal
open Filter Topology

universe u

section Helpers

variable {n m : ℕ} {ι : Type*}

/-- At a fixed time, `x ↦ (x, t)` is an isometry. -/
theorem isometry_point_time (t : ℝ) : Isometry (fun x : Spatial n => point x t) :=
  Isometry.of_dist_eq fun x y => by
    rw [dist_point, sub_self, abs_zero, Real.sqrt_zero, max_eq_left (norm_nonneg _),
      dist_eq_norm]

/-- The scales `r_j = 10^{-j} r_0` tend to zero. -/
theorem tendsto_scale_zero (F : CoherentFamily n m ι) : Tendsto F.scale atTop (𝓝 0) := by
  have hs : F.scale = fun j => F.initialRadius * (1 / 10 : ℝ) ^ j := by
    funext j
    rw [CoherentFamily.scale, coherentScale, one_div_pow, mul_one_div]
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 10 : ℝ)) (by norm_num)
    (by norm_num)).const_mul F.initialRadius
  rw [mul_zero] at h
  rw [hs]
  exact h

theorem scale_zero_eq (F : CoherentFamily n m ι) : F.scale 0 = F.initialRadius := by
  simp [CoherentFamily.scale, coherentScale]

end Helpers

/-- **The limiting chart from the finite estimates.** The statements of
`induction_estimates` (`hA4`), `finite_metric` (`hA7`) and `coverage` (`hA10`) imply the
statement of `limit_chart`. -/
theorem limit_chart_of_finite
    (hA4 :
      ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ} (_ : 0 < σ)
          (_ : 0 ≤ δ) (_ : DeltaSmall n σ δ) (_ : F.IsCoherentUpTo σ δ N)
          (P : InitialChart F),
          (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
            Function.Injective (fderiv ℝ (fun v => stage F P j v t) u)) ∧
          (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ), ∀ a ∈ F.index j, ∀ b ∈ F.index j,
            IsActive F j a (stage F P j u t) t → IsActive F j b (stage F P j u t) t →
              ENNReal.ofReal (‖(tangent F P j u t).starProjection - (F.plane j a).linearProjection‖ +
                  (F.scale j)⁻¹ * Metric.infDist (stage F P j u t) (F.plane j b).toSet) ≤
                ENNReal.ofReal (chartA n σ / ratio) * localError F j (pathPoint F P j u t)) ∧
          (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
            ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ chartEps n σ δ * F.scale j))
    (hA7 :
      ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ} (_ : 0 < σ)
          (_ : 0 ≤ δ) (_ : DeltaSmall n σ δ) (_ : EnergySmall n σ E)
          (_ : F.IsCoherentUpTo σ δ N) (P : InitialChart F) (_ : PathBoundUpTo F P E N),
          ∀ j ≤ N + 1,
            (∀ (u : Spatial m) (t s : ℝ),
              ‖stage F P j u t - stage F P j u s‖ ≤
                chartCt n σ * chartEps n σ δ * Real.sqrt |t - s|) ∧
            (∀ (u v : Spatial m) (t : ℝ),
              9 / 10 * ‖u - v‖ ≤ ‖stage F P j u t - stage F P j v t‖ ∧
                ‖stage F P j u t - stage F P j v t‖ ≤ 101 / 100 * ‖u - v‖) ∧
            (∀ (u v : Spatial m) (t s : ℝ),
              4 / 5 * dist (point u t) (point v s) ≤
                  dist (point (stage F P j u t) t) (point (stage F P j v s) s) ∧
                dist (point (stage F P j u t) t) (point (stage F P j v s) s) ≤
                  11 / 10 * dist (point u t) (point v s)))
    (hA10 :
      ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E κ : ℝ} {N : ℕ} (_ : 0 < σ)
          (_ : 0 ≤ δ) (_ : DeltaSmall n σ δ) (_ : EnergySmall n σ E) (_ : 0 ≤ κ)
          (_ : CoverageSmall n σ κ δ) (_ : F.IsCoherentUpTo σ δ N)
          (_ : F.HasCenterHeightUpTo κ N) (P : InitialChart F)
          (_ : PathBoundUpTo F P E N),
          (∀ j ≤ N, ∀ a ∈ F.index j, ∀ t : ℝ, |t - (F.center j a).2.val| ≤ (3 / 2 * F.scale j) ^ 2 →
            ∃ u : Spatial m,
              ‖stage F P (j + 1) u t - (F.center j a).1‖ ≤ coverageCoeff n σ κ δ * F.scale j ∧
              ∀ l, j + 1 ≤ l → l ≤ N + 1 →
                ‖stage F P l u t - (F.center j a).1‖ ≤
                  coverageCoeff n σ κ δ * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio)) ∧
          (∀ j ≤ N, ∀ a ∈ F.index j, ∀ (c : Space n) (θ : ℝ), dist c (F.center j a) ≤ F.scale j →
            Metric.infDist c.1 (F.plane j a).toSet ≤ θ * F.scale j →
            ∃ u : Spatial m,
              ‖stage F P (j + 1) u c.2.val - c.1‖ ≤ (θ + 3 * δ) * F.scale j ∧
              ∀ l, j + 1 ≤ l → l ≤ N + 1 →
                ‖stage F P l u c.2.val - c.1‖ ≤
                  (θ + 3 * δ) * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio))) :
  ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E : ℝ} (_ : 0 < σ) (_ : 0 ≤ δ)
      (_ : DeltaSmall n σ δ) (_ : EnergySmall n σ E) (_ : F.IsCoherent σ δ)
      (P : InitialChart F) (_ : ∀ N : ℕ, PathBoundUpTo F P E N),
      ∃ G : Spatial m → ℝ → Spatial n,
        (∀ (N : ℕ) (u : Spatial m) (t : ℝ),
          ‖stage F P N u t - G u t‖ ≤ chartEps n σ δ * F.scale N / (1 - ratio)) ∧
        (∀ (u : Spatial m) (t s : ℝ),
          ‖G u t - G u s‖ ≤ chartCt n σ * chartEps n σ δ * Real.sqrt |t - s|) ∧
        (∀ (u v : Spatial m) (t s : ℝ),
          4 / 5 * dist (point u t) (point v s) ≤ dist (point (G u t) t) (point (G v s) s) ∧
            dist (point (G u t) t) (point (G v s) s) ≤ 11 / 10 * dist (point u t) (point v s)) ∧
        IsClosed (Set.range fun p : Space m => point (G p.1 p.2.val) p.2.val) ∧
        (∀ (c : Space n) (θ : ℝ), Metric.infDist c.1 F.initialPlane.toSet ≤ θ * F.initialRadius →
          ∃ u : Spatial m,
            ‖G u c.2.val - c.1‖ ≤ (θ + chartEps n σ δ / (1 - ratio)) * F.initialRadius) ∧
        ∀ κ : ℝ, 0 ≤ κ → CoverageSmall n σ κ δ → F.HasCenterHeight κ →
          (∀ z : Space n, F.IsLevelLimit z →
            z ∈ Set.range fun p : Space m => point (G p.1 p.2.val) p.2.val) ∧
          ∀ j : ℕ, ∀ a ∈ F.index j, ∀ (c : Space n) (θ : ℝ), dist c (F.center j a) ≤ F.scale j →
            Metric.infDist c.1 (F.plane j a).toSet ≤ θ * F.scale j →
            ∃ u : Spatial m, ‖G u c.2.val - c.1‖ ≤
              (θ + 3 * δ) * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio) := by
  intro n m ι F σ δ E hσ hδ hsmall hEsmall hF P hpath
  have hε : 0 ≤ chartEps n σ δ := chartEps_nonneg hσ hδ
  have hh : (0 : ℝ) < 1 - ratio := by norm_num [ratio]
  -- the displacement steps (`hA4` at truncation `N = i`) and their geometric sums
  have hstep : ∀ (i : ℕ) (u : Spatial m) (t : ℝ),
      ‖stage F P (i + 1) u t - stage F P i u t‖ ≤ chartEps n σ δ * F.scale i :=
    fun i u t => (hA4 hσ hδ hsmall (hF i) P).2.2 i le_rfl u t
  have hdisp : ∀ k l : ℕ, k ≤ l → ∀ (u : Spatial m) (t : ℝ),
      ‖stage F P l u t - stage F P k u t‖ ≤ chartEps n σ δ * F.scale k / (1 - ratio) :=
    fun k l hkl u t => norm_sub_le_geometric F (fun j => stage F P j u t) (chartEps n σ δ) hε
      hkl (fun i _ _ => hstep i u t)
  have hb : Tendsto (fun N => 2 * (chartEps n σ δ * F.scale N / (1 - ratio))) atTop (𝓝 0) := by
    have h := (((tendsto_scale_zero F).const_mul (chartEps n σ δ)).div_const
      (1 - ratio)).const_mul 2
    rw [mul_zero, zero_div, mul_zero] at h
    exact h
  -- one limiting map, chosen before any `κ`
  obtain ⟨G, hG⟩ : ∃ G : Spatial m → ℝ → Spatial n, ∀ (u : Spatial m) (t : ℝ),
      Tendsto (fun N => stage F P N u t) atTop (𝓝 (G u t)) := by
    refine ⟨fun u t => limUnder atTop (fun N => stage F P N u t), fun u t => ?_⟩
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    refine cauchySeq_of_le_tendsto_0 _ (fun a b N ha hb' => ?_) hb
    calc dist (stage F P a u t) (stage F P b u t)
        ≤ dist (stage F P a u t) (stage F P N u t) + dist (stage F P b u t) (stage F P N u t) :=
          dist_triangle_right _ _ _
      _ ≤ chartEps n σ δ * F.scale N / (1 - ratio) + chartEps n σ δ * F.scale N / (1 - ratio) := by
          rw [dist_eq_norm, dist_eq_norm]
          exact add_le_add (hdisp N a ha u t) (hdisp N b hb' u t)
      _ = 2 * (chartEps n σ δ * F.scale N / (1 - ratio)) := by ring
  -- uniform convergence
  have hconv : ∀ (N : ℕ) (u : Spatial m) (t : ℝ),
      ‖stage F P N u t - G u t‖ ≤ chartEps n σ δ * F.scale N / (1 - ratio) := by
    intro N u t
    have hlim : Tendsto (fun l => ‖stage F P N u t - stage F P l u t‖) atTop
        (𝓝 ‖stage F P N u t - G u t‖) := (tendsto_const_nhds.sub (hG u t)).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop N] with l hl
    rw [norm_sub_rev]
    exact hdisp N l hl u t
  -- the finite metric bounds (`hA7` at truncation `N = j`, stage `j`)
  have hmet := fun j : ℕ =>
    hA7 hσ hδ hsmall hEsmall (hF j) P (hpath j) j (Nat.le_succ j)
  have hΦ : ∀ (u : Spatial m) (t : ℝ),
      Tendsto (fun j => point (stage F P j u t) t) atTop (𝓝 (point (G u t) t)) :=
    fun u t => ((isometry_point_time t).continuous.tendsto _).comp (hG u t)
  have htime : ∀ (u : Spatial m) (t s : ℝ),
      ‖G u t - G u s‖ ≤ chartCt n σ * chartEps n σ δ * Real.sqrt |t - s| := fun u t s =>
    le_of_tendsto' ((hG u t).sub (hG u s)).norm fun j => (hmet j).1 u t s
  have hbilip : ∀ (u v : Spatial m) (t s : ℝ),
      4 / 5 * dist (point u t) (point v s) ≤ dist (point (G u t) t) (point (G v s) s) ∧
        dist (point (G u t) t) (point (G v s) s) ≤ 11 / 10 * dist (point u t) (point v s) := by
    intro u v t s
    have hd := (hΦ u t).dist (hΦ v s)
    exact ⟨ge_of_tendsto' hd fun j => ((hmet j).2.2 u v t s).1,
      le_of_tendsto' hd fun j => ((hmet j).2.2 u v t s).2⟩
  -- closed image: `Φ` is bi-Lipschitz on the complete space `Space m`
  have hclosed : IsClosed (Set.range fun p : Space m => point (G p.1 p.2.val) p.2.val) := by
    have hpt : ∀ p p' : Space m,
        dist p p' = dist (point p.1 p.2.val) (point p'.1 p'.2.val) := fun _ _ => rfl
    have hanti : AntilipschitzWith (5 / 4 : NNReal)
        (fun p : Space m => point (G p.1 p.2.val) p.2.val) := by
      refine AntilipschitzWith.of_le_mul_dist fun p p' => ?_
      have h := (hbilip p.1 p'.1 p.2.val p'.2.val).1
      rw [hpt]
      push_cast
      linarith
    have hlip : LipschitzWith (11 / 10 : NNReal)
        (fun p : Space m => point (G p.1 p.2.val) p.2.val) := by
      refine LipschitzWith.of_dist_le_mul fun p p' => ?_
      have h := (hbilip p.1 p'.1 p.2.val p'.2.val).2
      rw [hpt]
      push_cast
      exact h
    exact hanti.isClosed_range hlip.uniformContinuous
  refine ⟨G, hconv, htime, hbilip, hclosed, ?_, ?_⟩
  · -- initial-plane stopping, with no time anchor
    intro c θ hc
    have hy := F.initialPlane.projection_mem c.1
    have hnear : ‖c.1 - F.initialPlane.projection c.1‖ ≤ θ * F.initialRadius := by
      refine le_trans ?_ hc
      refine (Metric.le_infDist F.initialPlane.nonempty).2 ?_
      intro w hw
      rw [dist_eq_norm]
      exact F.initialPlane.nearest c.1 hw
    have hdir : F.initialPlane.projection c.1 - P.origin ∈ F.initialPlane.direction := by
      have h1 := hy
      have h2 := P.origin_mem
      rw [AffineSpatialPlane.mem_toSet] at h1 h2
      have h3 := F.initialPlane.direction.sub_mem h1 h2
      rwa [sub_sub_sub_cancel_right] at h3
    rw [← P.range_eq] at hdir
    obtain ⟨u, hu⟩ := hdir
    refine ⟨u, ?_⟩
    have h0 : stage F P 0 u c.2.val = F.initialPlane.projection c.1 := by
      have hu' : P.isometry u = F.initialPlane.projection c.1 - P.origin := hu
      show P.origin + P.isometry u = _
      rw [hu']
      abel
    calc ‖G u c.2.val - c.1‖
        ≤ ‖G u c.2.val - stage F P 0 u c.2.val‖ + ‖stage F P 0 u c.2.val - c.1‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ chartEps n σ δ * F.scale 0 / (1 - ratio) + θ * F.initialRadius := by
          refine add_le_add ?_ ?_
          · rw [norm_sub_rev]
            exact hconv 0 u c.2.val
          · rw [h0, norm_sub_rev]
            exact hnear
      _ = (θ + chartEps n σ δ / (1 - ratio)) * F.initialRadius := by
          rw [scale_zero_eq]
          ring
  · intro κ hκ hcov hheight
    have hheightN : ∀ N : ℕ, F.HasCenterHeightUpTo κ N := fun N j _ a ha => hheight j a ha
    have hcovN := fun N : ℕ =>
      hA10 hσ hδ hsmall hEsmall hκ hcov (hF N) (hheightN N) P (hpath N)
    have hη : 0 ≤ coverageCoeff n σ κ δ := by
      obtain ⟨-, -, -, -, -, -, -, hA⟩ := chartConsts_bounds (n := n) hσ
      unfold coverageCoeff ratio
      have : 0 ≤ (5 + chartA n σ) * δ := mul_nonneg (by linarith) hδ
      positivity
    refine ⟨?_, ?_⟩
    · -- level limits lie in the closed image
      intro z hz
      obtain ⟨level, idx, hmem, hlevel, hlim⟩ := hz
      have hchoice : ∀ i : ℕ, ∃ u : Spatial m,
          ‖stage F P (level i + 1) u (F.center (level i) (idx i)).2.val -
              (F.center (level i) (idx i)).1‖ ≤
            coverageCoeff n σ κ δ * F.scale (level i) := by
        intro i
        obtain ⟨u, hu, -⟩ := (hcovN (level i)).1 (level i) le_rfl (idx i) (hmem i)
          (F.center (level i) (idx i)).2.val (by rw [sub_self, abs_zero]; positivity)
        exact ⟨u, hu⟩
      choose u hu using hchoice
      have hsl : ∀ l : ℕ, F.scale (l + 1) ≤ F.scale l := by
        intro l
        rw [scale_succ]
        have := (scale_pos F l).le
        unfold ratio
        linarith
      have key : ∀ (l : ℕ) (b : ι) (v : Spatial m),
          ‖stage F P (l + 1) v (F.center l b).2.val - (F.center l b).1‖ ≤
            coverageCoeff n σ κ δ * F.scale l →
          dist (point (G v (F.center l b).2.val) (F.center l b).2.val) z ≤
            (chartEps n σ δ / (1 - ratio) + coverageCoeff n σ κ δ) * F.scale l +
              dist (F.center l b) z := by
        intro l b v hv
        have hG' : ‖G v (F.center l b).2.val - (F.center l b).1‖ ≤
            (chartEps n σ δ / (1 - ratio) + coverageCoeff n σ κ δ) * F.scale l := by
          calc ‖G v (F.center l b).2.val - (F.center l b).1‖
              ≤ ‖G v (F.center l b).2.val - stage F P (l + 1) v (F.center l b).2.val‖ +
                ‖stage F P (l + 1) v (F.center l b).2.val - (F.center l b).1‖ :=
                norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ chartEps n σ δ * F.scale (l + 1) / (1 - ratio) +
                coverageCoeff n σ κ δ * F.scale l := by
                refine add_le_add ?_ hv
                rw [norm_sub_rev]
                exact hconv (l + 1) v _
            _ ≤ chartEps n σ δ * F.scale l / (1 - ratio) +
                coverageCoeff n σ κ δ * F.scale l :=
                add_le_add (div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hsl l) hε) hh.le) le_rfl
            _ = (chartEps n σ δ / (1 - ratio) + coverageCoeff n σ κ δ) * F.scale l := by ring
        have e : dist (point (G v (F.center l b).2.val) (F.center l b).2.val) (F.center l b) =
            ‖G v (F.center l b).2.val - (F.center l b).1‖ := by
          have h := dist_point (G v (F.center l b).2.val) (F.center l b).1
            (F.center l b).2.val (F.center l b).2.val
          rw [sub_self, abs_zero, Real.sqrt_zero, max_eq_left (norm_nonneg _)] at h
          exact h
        calc dist (point (G v (F.center l b).2.val) (F.center l b).2.val) z
            ≤ dist (point (G v (F.center l b).2.val) (F.center l b).2.val) (F.center l b) +
                dist (F.center l b) z := dist_triangle _ _ _
          _ ≤ (chartEps n σ δ / (1 - ratio) + coverageCoeff n σ κ δ) * F.scale l +
                dist (F.center l b) z := by
              rw [e]
              exact add_le_add hG' le_rfl
      have hbound := fun i : ℕ => key (level i) (idx i) (u i) (hu i)
      have hb0 : Tendsto (fun i => (chartEps n σ δ / (1 - ratio) + coverageCoeff n σ κ δ) *
          F.scale (level i) + dist (F.center (level i) (idx i)) z) atTop (𝓝 0) := by
        have h := (((tendsto_scale_zero F).comp hlevel).const_mul
          (chartEps n σ δ / (1 - ratio) + coverageCoeff n σ κ δ)).add
          (tendsto_iff_dist_tendsto_zero.1 hlim)
        rw [mul_zero, add_zero] at h
        exact h
      refine hclosed.mem_of_tendsto (b := (atTop : Filter ℕ)) (f := fun i => point (G (u i)
          (F.center (level i) (idx i)).2.val) (F.center (level i) (idx i)).2.val) ?_
        (Eventually.of_forall fun i => ⟨point (u i) (F.center (level i) (idx i)).2.val, rfl⟩)
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun i => dist_nonneg) hbound hb0
    · -- stopping centers with an occurrence as parent
      intro j a ha c θ hc₁ hc₂
      obtain ⟨u, hu, -⟩ := (hcovN j).2 j le_rfl a ha c θ hc₁ hc₂
      refine ⟨u, ?_⟩
      calc ‖G u c.2.val - c.1‖
          ≤ ‖G u c.2.val - stage F P (j + 1) u c.2.val‖ + ‖stage F P (j + 1) u c.2.val - c.1‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ chartEps n σ δ * F.scale (j + 1) / (1 - ratio) + (θ + 3 * δ) * F.scale j := by
            refine add_le_add ?_ hu
            rw [norm_sub_rev]
            exact hconv (j + 1) u c.2.val
        _ = (θ + 3 * δ) * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio) := by ring

end CoherentChart

end ParabolicRectifiability
