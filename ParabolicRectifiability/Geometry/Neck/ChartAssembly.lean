import ParabolicRectifiability.Geometry.Chart.InductionEstimates
import ParabolicRectifiability.Geometry.Chart.LevelPartitionsAndCoverage
import ParabolicRectifiability.Geometry.Chart.LimitChart
import ParabolicRectifiability.Geometry.Neck.HorizontalReduction

/-!
# Neck, part 1: the coherent charts and the finite chart

The neck theorems `vertical_coherent_chart` (infinite form, with the ambient square
bound) and `horizontal_coherent_chart`, and the finite chart (finite form) used by the
buffered reference theorems, are assembled here from the estimates for the chart
construction.

The inputs are the recurrence estimates (`hA6`) and the finite metric estimates (`hA7`)
of `CoherentChart`; they enter as explicit hypotheses whose types are those of the
corresponding statements, generalized over `n, m` and the index type. The other
ingredients are proved:

* `induction_estimates_proof`;
* `parent_patch_proof`, from the recurrence estimates;
* `pathBound_of_verticalSquareBound_proof` and `coverage_proof`,
  from the induction estimates and the parent patch;
* `limit_chart_of_finite`, from the induction estimates, the
  finite metric estimates and the coverage;
* the horizontal reduction `horizontal_coherent_chart_of_vertical`.

Declarations:

* `finite_chart_of_leaves`: the finite chart through stage `N + 1` from the *ambient*
  truncated square bound, from the recurrence and finite metric estimates;
* `vertical_coherent_chart_of_leaves`: the statement of `vertical_coherent_chart`,
  with the thresholds of `smallness_of_le` and the constant `C = 1 + 12A + 10AC_t`;
* `horizontal_coherent_chart_of_leaves`: the statement of `horizontal_coherent_chart`.
-/

noncomputable section

namespace ParabolicRectifiability

namespace NeckHubTree

open MeasureTheory Set
open scoped ENNReal
open CoherentChart

universe u

private theorem glue_arith {A Ct θ δ X r d : ℝ} (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hθ : 0 ≤ θ)
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

/-- **The finite chart** from the recurrence and finite metric estimates. The conclusion is
the statement of `CoherentChart.finite_chart`: for finite coherent data through level `N` with the ambient
vertical square bound on levels `0, …, N` and the `δ`- and `E`-conditions, the completed
chart `F_{N+1}` has the time modulus, the bi-Lipschitz bounds, total displacement at most
`ε r_0/(1-h)` from the affine chart `F_0`, and, under the coverage condition and center
heights, the center coverage and the stopping estimate. The hypotheses `hA6`, `hA7` are the statements of the recurrence and finite metric
estimates. -/
theorem finite_chart_of_leaves
    (hA6 : ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ},
      0 < σ → 0 ≤ δ → DeltaSmall n σ δ → EnergySmall n σ E → F.IsCoherentUpTo σ δ N →
      ∀ (P : InitialChart F), PathBoundUpTo F P E N →
      (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ) (v : Spatial m),
        99 / 100 * ‖v‖ ≤ ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ∧
          ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ≤ 101 / 100 * ‖v‖) ∧
      (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
        ‖fderiv ℝ (fun v => fderiv ℝ (fun w => stage F P j w t) v) u‖ ≤
            chartCa n σ * chartEps n σ δ / F.scale j ∧
          ‖deriv (fun s => stage F P j u s) t‖ ≤ chartCa n σ * chartEps n σ δ / F.scale j) ∧
      (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
        ‖deriv (fun s => stage F P (j + 1) u s - stage F P j u s) t‖ ≤
          chartCΔ n σ * chartEps n σ δ / F.scale j))
    (hA7 : ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ},
      0 < σ → 0 ≤ δ → DeltaSmall n σ δ → EnergySmall n σ E → F.IsCoherentUpTo σ δ N →
      ∀ (P : InitialChart F), PathBoundUpTo F P E N →
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
              11 / 10 * dist (point u t) (point v s))) :
    ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ},
      0 < σ → 0 ≤ δ → DeltaSmall n σ δ → EnergySmall n σ E →
      F.IsCoherentUpTo σ δ N → F.VerticalSquareBoundUpTo E N →
      ∀ (P : InitialChart F),
    (∀ (u : Spatial m) (t s : ℝ),
      ‖stage F P (N + 1) u t - stage F P (N + 1) u s‖ ≤
        chartCt n σ * chartEps n σ δ * Real.sqrt |t - s|) ∧
    (∀ (u v : Spatial m) (t s : ℝ),
      4 / 5 * dist (point u t) (point v s) ≤
          dist (point (stage F P (N + 1) u t) t) (point (stage F P (N + 1) v s) s) ∧
        dist (point (stage F P (N + 1) u t) t) (point (stage F P (N + 1) v s) s) ≤
          11 / 10 * dist (point u t) (point v s)) ∧
    (∀ (u : Spatial m) (t : ℝ),
      ‖stage F P (N + 1) u t - stage F P 0 u t‖ ≤ chartEps n σ δ * F.scale 0 / (1 - ratio)) ∧
    (∀ κ : ℝ, 0 ≤ κ → CoverageSmall n σ κ δ → F.HasCenterHeightUpTo κ N →
      (∀ j ≤ N, ∀ a ∈ F.index j, ∀ t : ℝ,
        |t - (F.center j a).2.val| ≤ (3 / 2 * F.scale j) ^ 2 →
        ∃ u : Spatial m, ‖stage F P (N + 1) u t - (F.center j a).1‖ ≤
          coverageCoeff n σ κ δ * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio)) ∧
      (∀ j ≤ N, ∀ a ∈ F.index j, ∀ (c : Space n) (θ : ℝ), dist c (F.center j a) ≤ F.scale j →
        Metric.infDist c.1 (F.plane j a).toSet ≤ θ * F.scale j →
        ∃ u : Spatial m, ‖stage F P (N + 1) u c.2.val - c.1‖ ≤
          (θ + 3 * δ) * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio))) := by
  intro n m ι F σ δ E N hσ hδ hsmall hEsmall hF hE P
  have hA4 := induction_estimates_proof hσ hδ hsmall hF P
  have hpath : PathBoundUpTo F P E N :=
    pathBound_of_verticalSquareBound_proof (n := n) (m := m) (ι := ι)
      (fun {F σ δ N} hσ hδ hsmall hF P => induction_estimates_proof (F := F) (σ := σ) (δ := δ)
        (N := N) hσ hδ hsmall hF P) hσ hδ hsmall hF hE P
  have hmet := hA7 hσ hδ hsmall hEsmall hF P hpath (N + 1) le_rfl
  refine ⟨hmet.1, hmet.2.2, ?_, ?_⟩
  · intro u t
    exact norm_sub_le_geometric F (fun j => stage F P j u t) (chartEps n σ δ)
      (chartEps_nonneg hσ hδ) (Nat.zero_le _)
      (fun i _ hi => hA4.2.2 i (Nat.lt_succ_iff.mp hi) u t)
  · intro κ hκ hcov hheight
    have hc := coverage_proof (n := n) (m := m) (ι := ι)
      (fun {F σ δ N} hσ hδ hsmall hF P => induction_estimates_proof (F := F) (σ := σ) (δ := δ)
        (N := N) hσ hδ hsmall hF P)
      (parent_patch_proof (n := n) (m := m) (ι := ι)
        (fun {F σ δ E N} hσ hδ hsmall hEsmall hF P hpath =>
          hA6 (F := F) (σ := σ) (δ := δ) (E := E) (N := N) hσ hδ hsmall hEsmall hF P hpath))
      hσ hδ hsmall hEsmall hκ hcov hF hheight P hpath
    refine ⟨fun j hj a ha t ht => ?_, fun j hj a ha c θ hc₁ hc₂ => ?_⟩
    · obtain ⟨u, -, hl⟩ := hc.1 j hj a ha t ht
      exact ⟨u, hl (N + 1) (by omega) le_rfl⟩
    · obtain ⟨u, -, hl⟩ := hc.2 j hj a ha c θ hc₁ hc₂
      exact ⟨u, hl (N + 1) (by omega) le_rfl⟩

/-- **The vertical coherent chart** from the recurrence and finite metric estimates. The
conclusion is the statement of `vertical_coherent_chart` (written, as in
`horizontal_coherent_chart_of_vertical`, with the unused hypotheses as plain arrows).
Thresholds `δ₀ = deltaThreshold n σ`, `E₀ = energyThreshold n σ`,
`κ₀ = 1/200` and the constant `C = 1 + 12A + 10AC_t` depend only on `n, σ`. The ambient
square bound gives the path bound for every truncation, and `limit_chart_of_finite` gives
the limiting chart. -/
theorem vertical_coherent_chart_of_leaves
    (hA6 : ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ},
      0 < σ → 0 ≤ δ → DeltaSmall n σ δ → EnergySmall n σ E → F.IsCoherentUpTo σ δ N →
      ∀ (P : InitialChart F), PathBoundUpTo F P E N →
      (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ) (v : Spatial m),
        99 / 100 * ‖v‖ ≤ ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ∧
          ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ≤ 101 / 100 * ‖v‖) ∧
      (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
        ‖fderiv ℝ (fun v => fderiv ℝ (fun w => stage F P j w t) v) u‖ ≤
            chartCa n σ * chartEps n σ δ / F.scale j ∧
          ‖deriv (fun s => stage F P j u s) t‖ ≤ chartCa n σ * chartEps n σ δ / F.scale j) ∧
      (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
        ‖deriv (fun s => stage F P (j + 1) u s - stage F P j u s) t‖ ≤
          chartCΔ n σ * chartEps n σ δ / F.scale j))
    (hA7 : ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ},
      0 < σ → 0 ≤ δ → DeltaSmall n σ δ → EnergySmall n σ E → F.IsCoherentUpTo σ δ N →
      ∀ (P : InitialChart F), PathBoundUpTo F P E N →
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
              11 / 10 * dist (point u t) (point v s))) :
    ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ 1 →
      ∃ δ₀ E₀ κ₀ C : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < C ∧
        ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (δ E : ℝ),
          0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ →
          F.IsCoherent σ δ → F.VerticalSquareBound E →
          ∃ G : Spatial m → ℝ → Spatial n,
            (∀ p p' : Space m,
              4 / 5 * dist p p' ≤ dist (timePreservingMap G p) (timePreservingMap G p') ∧
                dist (timePreservingMap G p) (timePreservingMap G p') ≤ 11 / 10 * dist p p') ∧
            (∀ (u : Spatial m) (t s : ℝ), ‖G u t - G u s‖ ≤ C * δ * Real.sqrt |t - s|) ∧
            IsClosed (Set.range (timePreservingMap G)) ∧
            ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ₀ → F.HasCenterHeight κ →
              (∀ z : Space n, F.IsLevelLimit z → z ∈ Set.range (timePreservingMap G)) ∧
              ∀ θ : ℝ, 0 ≤ θ → ∀ (c : Space n) (d : ℝ) (p : Option (ℕ × ι)),
                F.IsStoppingParent θ c d p →
                  ∃ u : Spatial m, ‖G u c.2.val - c.1‖ ≤ C * 10 * (θ + δ) * d := by
  intro n σ hσ _hσ₁
  obtain ⟨-, -, -, -, -, -, ht, hA⟩ := chartConsts_bounds (n := n) hσ
  have hA0 : 0 ≤ chartA n σ := by linarith
  have hCpos : 0 < 1 + 12 * chartA n σ + 10 * chartA n σ * chartCt n σ := by
    have := mul_nonneg hA0 ht
    linarith
  refine ⟨deltaThreshold n σ, energyThreshold n σ, heightThreshold,
    1 + 12 * chartA n σ + 10 * chartA n σ * chartCt n σ, deltaThreshold_pos hσ,
    energyThreshold_pos hσ, by norm_num [heightThreshold], hCpos, ?_⟩
  intro m ι F δ E hδ hδ₀ _ hE₀ hF hsq
  obtain ⟨P⟩ := nonempty_initialChart F
  obtain ⟨hsmall, hEsmall, -, -⟩ :=
    smallness_of_le (κ := 0) hσ hδ hδ₀ hE₀ (by norm_num [heightThreshold])
  have hpath : ∀ N : ℕ, PathBoundUpTo F P E N := fun N =>
    pathBound_of_verticalSquareBound_proof (n := n) (m := m) (ι := ι)
      (fun {F σ δ N} hσ hδ hsmall hF P => induction_estimates_proof (F := F) (σ := σ) (δ := δ)
        (N := N) hσ hδ hsmall hF P) hσ hδ hsmall (hF N)
      (fun w => (ENNReal.sum_le_tsum _).trans (hsq w)) P
  obtain ⟨G, -, htime, hbilip, hclosed, hinit, hcov⟩ :=
    limit_chart_of_finite
      (fun {n m ι F σ δ N} hσ hδ hsmall hF P => induction_estimates_proof (n := n) (m := m)
        (ι := ι) (F := F) (σ := σ) (δ := δ) (N := N) hσ hδ hsmall hF P)
      (fun {n m ι F σ δ E N} hσ hδ hsmall hEsmall hF P hpath =>
        hA7 (n := n) (m := m) (ι := ι) (F := F) (σ := σ) (δ := δ) (E := E) (N := N)
          hσ hδ hsmall hEsmall hF P hpath)
      (fun {n m ι F σ δ E κ N} hσ hδ hsmall hEsmall hκ hcov hF hheight P hpath =>
        coverage_proof (n := n) (m := m) (ι := ι)
          (fun {F σ δ N} hσ hδ hsmall hF P => induction_estimates_proof (F := F) (σ := σ)
            (δ := δ) (N := N) hσ hδ hsmall hF P)
          (parent_patch_proof (n := n) (m := m) (ι := ι)
            (fun {F σ δ E N} hσ hδ hsmall hEsmall hF P hpath =>
              hA6 (F := F) (σ := σ) (δ := δ) (E := E) (N := N) hσ hδ hsmall hEsmall hF P hpath))
          (F := F) (σ := σ) (δ := δ) (E := E) (κ := κ) (N := N)
          hσ hδ hsmall hEsmall hκ hcov hF hheight P hpath)
      hσ hδ hsmall hEsmall hF P hpath
  refine ⟨G, fun p p' => hbilip p.1 p'.1 p.2.val p'.2.val, fun u t s => ?_, hclosed, ?_⟩
  · refine (htime u t s).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    rw [chartEps_eq]
    nlinarith [mul_nonneg (mul_nonneg hA0 ht) hδ, mul_nonneg hA0 hδ]
  · intro κ hκ hκ₀ hheight
    have hcovκ := (smallness_of_le hσ hδ hδ₀ hE₀ hκ₀).2.2.1
    obtain ⟨hlev, hstop⟩ := hcov κ hκ hcovκ hheight
    refine ⟨hlev, fun θ hθ c d p hp => ?_⟩
    rcases p with _ | ⟨j, a⟩
    · obtain ⟨hp₁, hp₂⟩ := hp
      obtain ⟨u, hu⟩ := hinit c θ hp₁
      refine ⟨u, hu.trans (glue_arith hA0 ht hθ hδ ?_ F.initialRadius_pos.le (by linarith))⟩
      have he : chartEps n σ δ / (1 - ratio) = 100 / 9 * chartA n σ * δ := by
        rw [chartEps_eq]; unfold ratio; ring
      rw [he]
      nlinarith [mul_nonneg hA0 hδ]
    · obtain ⟨ha, hdist, hinf, hrd⟩ := hp
      obtain ⟨u, hu⟩ := hstop j a ha c θ hdist hinf
      have hb : (θ + 3 * δ) * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio) =
          (θ + 3 * δ + 10 / 9 * chartA n σ * δ) * F.scale j := by
        rw [scale_succ F j, chartEps_eq]; unfold ratio; ring
      refine ⟨u, hu.trans (hb.le.trans
        (glue_arith hA0 ht hθ hδ ?_ (scale_pos F j).le (by linarith)))⟩
      nlinarith [mul_nonneg hA0 hδ, mul_nonneg (sub_nonneg.mpr hA) hδ]

/-- **The horizontal coherent chart** (spatial chart) from the recurrence and finite metric
estimates: the reduction `horizontal_coherent_chart_of_vertical` applied to
`vertical_coherent_chart_of_leaves`; same constants. -/
theorem horizontal_coherent_chart_of_leaves
    (hA6 : ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ},
      0 < σ → 0 ≤ δ → DeltaSmall n σ δ → EnergySmall n σ E → F.IsCoherentUpTo σ δ N →
      ∀ (P : InitialChart F), PathBoundUpTo F P E N →
      (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ) (v : Spatial m),
        99 / 100 * ‖v‖ ≤ ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ∧
          ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ≤ 101 / 100 * ‖v‖) ∧
      (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
        ‖fderiv ℝ (fun v => fderiv ℝ (fun w => stage F P j w t) v) u‖ ≤
            chartCa n σ * chartEps n σ δ / F.scale j ∧
          ‖deriv (fun s => stage F P j u s) t‖ ≤ chartCa n σ * chartEps n σ δ / F.scale j) ∧
      (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
        ‖deriv (fun s => stage F P (j + 1) u s - stage F P j u s) t‖ ≤
          chartCΔ n σ * chartEps n σ δ / F.scale j))
    (hA7 : ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ},
      0 < σ → 0 ≤ δ → DeltaSmall n σ δ → EnergySmall n σ E → F.IsCoherentUpTo σ δ N →
      ∀ (P : InitialChart F), PathBoundUpTo F P E N →
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
              11 / 10 * dist (point u t) (point v s))) :
    ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ 1 →
    ∃ δ₀ E₀ κ₀ C : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < C ∧
      ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (δ E γ : ℝ),
        0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → 0 ≤ γ → γ ≤ min (σ ^ 2) 1 / 4 →
        F.IsCoherent σ δ → F.HorizontalSquareBound E → F.IsTimeCompatible γ →
        ∃ G : Spatial m → Spatial n,
          (∀ u v : Spatial m,
            4 / 5 * ‖u - v‖ ≤ ‖G u - G v‖ ∧ ‖G u - G v‖ ≤ 11 / 10 * ‖u - v‖) ∧
          IsClosed (Set.range G) ∧
          ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ₀ → F.HasCenterHeight κ →
            (∀ z : Space n, F.IsLevelLimit z → z.1 ∈ Set.range G) ∧
            ∀ θ : ℝ, 0 ≤ θ → ∀ (c : Space n) (d : ℝ) (p : Option (ℕ × ι)),
              F.IsStoppingParent θ c d p →
                ∃ u : Spatial m, ‖G u - c.1‖ ≤ C * 10 * (θ + δ) * d :=
  horizontal_coherent_chart_of_vertical (vertical_coherent_chart_of_leaves hA6 hA7)

end NeckHubTree

end ParabolicRectifiability
