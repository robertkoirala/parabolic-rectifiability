import ParabolicRectifiability.Geometry.Neck.ChartAssembly

/-!
# Neck, part 2: the buffered finite reference measures

The neck theorems `vertical_buffered_reference` and `horizontal_buffered_reference`
(buffered finite reference measures) are reduced to two inputs:

* the finite chart, entering as the hypothesis `hA11` whose type is the type of
  `CoherentChart.finite_chart`; `NeckHubTree.finite_chart_of_leaves` proves it from the
  recurrence and finite metric estimates;
* one buffer construction per type, entering as `hBV` / `hBH`: the types of
  `NeckHubTree.verticalBufferedReference_of_chart` and
  `NeckHubTree.horizontalBufferedReference_of_chart`. They are
  the metric and measure part of the argument: a chart that is `(0.8, 1.1)`
  bi-Lipschitz, within `C_* R` of an affine isometric chart through a point near `x_q`, and
  that reaches every center (at its own time, vertical case) within `r_j/4`, carries the
  buffered reference measure on the base ball `D` of radius `C_r R`.

The proof chooses the initial parametrization with origin at the given point of `L_*` near
`x_q`, takes the thresholds of `smallness_of_le`, and checks the numerics:
the total displacement is `ε r_0/(1-h) ≤ r_0/90 ≤ C_* R`, and the center-coverage
coefficient with its displacement tail is `η + ε h/(1-h) ≤ 1/100 + 1/900 < 1/4`. The
horizontal case uses the synthetic family `(x_{j,a}, 0)` of `CoherentFamily.synthetic` and the finite
chart at time `0`.
-/

noncomputable section

namespace ParabolicRectifiability

namespace NeckHubTree

open MeasureTheory Set
open scoped ENNReal
open CoherentChart

universe u

/-- Total displacement numerics: `ε ≤ 1/100` and `0 ≤ r ≤ S` give `ε r/(1-h) ≤ S`. -/
theorem displacement_le_of_eps {ε r S : ℝ} (hε : ε ≤ 1 / 100) (hr : 0 ≤ r) (hrS : r ≤ S) :
    ε * r / (1 - ratio) ≤ S := by
  have key : ε * r / (1 - ratio) = 10 / 9 * (ε * r) := by unfold ratio; ring
  rw [key]
  have h1 : ε * r ≤ 1 / 100 * r := mul_le_mul_of_nonneg_right hε hr
  linarith

/-- Center-coverage numerics: `η ≤ 1/100`, `ε ≤ 1/100` and `r' = h r` give
`η r + ε r'/(1-h) ≤ r/4`. -/
theorem coverage_le_quarter {η ε r r' : ℝ} (hη : η ≤ 1 / 100) (hε : ε ≤ 1 / 100)
    (hr : 0 < r) (hr' : r' = ratio * r) :
    η * r + ε * r' / (1 - ratio) ≤ r / 4 := by
  have key : ε * r' / (1 - ratio) = ε * r / 9 := by rw [hr']; unfold ratio; ring
  rw [key]
  have h1 : η * r ≤ 1 / 100 * r := mul_le_mul_of_nonneg_right hη hr.le
  have h2 : ε * r ≤ 1 / 100 * r := mul_le_mul_of_nonneg_right hε hr.le
  linarith

/-- An initial parametrization with a prescribed origin `x ∈ L_*`. -/
theorem exists_initialChart_origin {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι)
    {x : Spatial n} (hx : x ∈ F.initialPlane.toSet) :
    ∃ P : InitialChart F, P.origin = x := by
  obtain ⟨P₀⟩ := nonempty_initialChart F
  exact ⟨⟨x, hx, P₀.isometry, P₀.range_eq⟩, rfl⟩

/-- **Vertical buffered reference** from the finite chart and the buffer construction. The
conclusion is the statement of `vertical_buffered_reference`. Thresholds: those of
`smallness_of_le`; `c_b` is that of the buffer construction (it depends on `n` only);
`C_r, C_m` are those of the buffer construction for the given `C_*`. -/
theorem vertical_buffered_reference_of_finite_chart
    (hA11 : ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ},
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
            (θ + 3 * δ) * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio))))
    (hBV : ∀ n : ℕ, ∃ cb : ℝ, 0 < cb ∧ ∀ Cs : ℝ, 0 < Cs → ∃ Cr Cm : ℝ, 0 < Cr ∧ 0 < Cm ∧
      ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (N : ℕ) (q : Space n) (R : ℝ)
        (G : Spatial m → ℝ → Spatial n) (x : Spatial n) (U : Spatial m →ₗᵢ[ℝ] Spatial n),
        0 < R →
        (∀ p p' : Space m,
          4 / 5 * dist p p' ≤ dist (timePreservingMap G p) (timePreservingMap G p') ∧
            dist (timePreservingMap G p) (timePreservingMap G p') ≤ 11 / 10 * dist p p') →
        (∀ (u : Spatial m) (t : ℝ), ‖G u t - (x + U u)‖ ≤ Cs * R) →
        ‖x - q.1‖ ≤ Cs * R →
        F.initialRadius ≤ Cs * R →
        (∀ j ≤ N, ∀ a ∈ F.index j, F.center j a ∈ Metric.ball q (Cs * R)) →
        (∀ j ≤ N, ∀ a ∈ F.index j, ∃ u : Spatial m,
          ‖G u (F.center j a).2.val - (F.center j a).1‖ ≤ F.scale j / 4) →
        F.HasVerticalBufferedReference R Cr Cm cb N) :
    ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ 1 →
    ∃ δ₀ E₀ κ₀ cb : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < cb ∧
      ∀ Cs : ℝ, 0 < Cs → ∃ Cr Cm : ℝ, 0 < Cr ∧ 0 < Cm ∧
        ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (N : ℕ) (q : Space n)
          (R δ E κ : ℝ), 0 < R → 0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → 0 ≤ κ → κ ≤ κ₀ →
          F.IsCoherentUpTo σ δ N → F.VerticalSquareBoundUpTo E N →
          F.HasCenterHeightUpTo κ N →
          F.initialRadius ≤ Cs * R →
          (∀ j ≤ N, ∀ a ∈ F.index j, F.center j a ∈ Metric.ball q (Cs * R)) →
          (∃ x ∈ F.initialPlane.toSet, ‖x - q.1‖ ≤ Cs * R) →
          F.HasVerticalBufferedReference R Cr Cm cb N := by
  intro n σ hσ _hσ₁
  obtain ⟨cb, hcb, hBVn⟩ := hBV n
  refine ⟨deltaThreshold n σ, energyThreshold n σ, heightThreshold, cb, deltaThreshold_pos hσ,
    energyThreshold_pos hσ, by norm_num [heightThreshold], hcb, fun Cs hCs => ?_⟩
  obtain ⟨Cr, Cm, hCr, hCm, hbuf⟩ := hBVn Cs hCs
  refine ⟨Cr, Cm, hCr, hCm, ?_⟩
  intro m ι F N q R δ E κ hR hδ hδ₀ _hE hE₀ hκ hκ₀ hF hsq hheight hr₀ hcent hx
  obtain ⟨x, hxL, hxq⟩ := hx
  obtain ⟨hsmall, hEsmall, hcov, -⟩ := smallness_of_le hσ hδ hδ₀ hE₀ hκ₀
  obtain ⟨P, hP⟩ := exists_initialChart_origin F hxL
  obtain ⟨-, hbilip, hdisp, hcover⟩ := hA11 hσ hδ hsmall hEsmall hF hsq P
  obtain ⟨hcenters, -⟩ := hcover κ hκ hcov hheight
  have hε := hsmall.eps_le
  refine hbuf F N q R (stage F P (N + 1)) x P.isometry hR
    (fun p p' => hbilip p.1 p'.1 p.2.val p'.2.val) (fun u t => ?_) hxq hr₀ hcent
    (fun j hj a ha => ?_)
  · have h0 : stage F P 0 u t = x + P.isometry u := by
      rw [← hP]
      rfl
    rw [← h0]
    exact (hdisp u t).trans
      (displacement_le_of_eps hε (scale_pos F 0).le ((scale_zero_eq F).le.trans hr₀))
  · obtain ⟨u, hu⟩ := hcenters j hj a ha (F.center j a).2.val (by
      rw [sub_self, abs_zero]
      positivity)
    exact ⟨u, hu.trans (coverage_le_quarter hcov hε (scale_pos F j) (scale_succ F j))⟩

/-- **Horizontal buffered reference** from the finite chart and the buffer construction. The
conclusion is the statement of `horizontal_buffered_reference`. The finite chart is applied to the synthetic family
`(x_{j,a}, 0)` (coherent by time compatibility, with the vertical square bound from the
horizontal one, `verticalSquareBound_synthetic`), and the spatial chart is its slice at time `0`. -/
theorem horizontal_buffered_reference_of_finite_chart
    (hA11 : ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ},
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
            (θ + 3 * δ) * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio))))
    (hBH : ∀ n : ℕ, ∃ cb : ℝ, 0 < cb ∧ ∀ Cs : ℝ, 0 < Cs → ∃ Cr Cm : ℝ, 0 < Cr ∧ 0 < Cm ∧
      ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (N : ℕ) (y : Spatial n) (R : ℝ)
        (G : Spatial m → Spatial n) (x : Spatial n) (U : Spatial m →ₗᵢ[ℝ] Spatial n),
        0 < R →
        (∀ u v : Spatial m,
          4 / 5 * ‖u - v‖ ≤ ‖G u - G v‖ ∧ ‖G u - G v‖ ≤ 11 / 10 * ‖u - v‖) →
        (∀ u : Spatial m, ‖G u - (x + U u)‖ ≤ Cs * R) →
        ‖x - y‖ ≤ Cs * R →
        F.initialRadius ≤ Cs * R →
        (∀ j ≤ N, ∀ a ∈ F.index j, (F.center j a).1 ∈ Metric.ball y (Cs * R)) →
        (∀ j ≤ N, ∀ a ∈ F.index j, ∃ u : Spatial m,
          ‖G u - (F.center j a).1‖ ≤ F.scale j / 4) →
        F.HasHorizontalBufferedReference R Cr Cm cb N) :
    ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ 1 →
    ∃ δ₀ E₀ κ₀ cb : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < cb ∧
      ∀ Cs : ℝ, 0 < Cs → ∃ Cr Cm : ℝ, 0 < Cr ∧ 0 < Cm ∧
        ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (N : ℕ) (q : Space n)
          (R δ E κ γ : ℝ), 0 < R → 0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → 0 ≤ κ → κ ≤ κ₀ →
          0 ≤ γ → γ ≤ min (σ ^ 2) 1 / 4 →
          F.IsCoherentUpTo σ δ N → F.HorizontalSquareBoundUpTo E N →
          F.HasCenterHeightUpTo κ N → F.IsTimeCompatibleUpTo γ N →
          F.initialRadius ≤ Cs * R →
          (∀ j ≤ N, ∀ a ∈ F.index j, F.center j a ∈ Metric.ball q (Cs * R)) →
          (∃ x ∈ F.initialPlane.toSet, ‖x - q.1‖ ≤ Cs * R) →
          F.HasHorizontalBufferedReference R Cr Cm cb N := by
  intro n σ hσ _hσ₁
  obtain ⟨cb, hcb, hBHn⟩ := hBH n
  refine ⟨deltaThreshold n σ, energyThreshold n σ, heightThreshold, cb, deltaThreshold_pos hσ,
    energyThreshold_pos hσ, by norm_num [heightThreshold], hcb, fun Cs hCs => ?_⟩
  obtain ⟨Cr, Cm, hCr, hCm, hbuf⟩ := hBHn Cs hCs
  refine ⟨Cr, Cm, hCr, hCm, ?_⟩
  intro m ι F N q R δ E κ γ hR hδ hδ₀ _hE hE₀ hκ hκ₀ hγ hγ' hF hsq hheight htime hr₀ hcent hx
  obtain ⟨x, hxL, hxq⟩ := hx
  obtain ⟨hsmall, hEsmall, hcov, -⟩ := smallness_of_le hσ hδ hδ₀ hE₀ hκ₀
  have hF' : F.synthetic.IsCoherentUpTo σ δ N := hF.synthetic F hγ hγ' htime
  have hsq' : F.synthetic.VerticalSquareBoundUpTo E N := F.verticalSquareBoundUpTo_synthetic hsq
  have hheight' : F.synthetic.HasCenterHeightUpTo κ N :=
    (F.hasCenterHeightUpTo_synthetic_iff).2 hheight
  obtain ⟨P, hP⟩ := exists_initialChart_origin F.synthetic (x := x) hxL
  obtain ⟨-, hbilip, hdisp, hcover⟩ := hA11 hσ hδ hsmall hEsmall hF' hsq' P
  obtain ⟨hcenters, -⟩ := hcover κ hκ hcov hheight'
  have hε := hsmall.eps_le
  refine hbuf F N q.1 R (fun u => stage F.synthetic P (N + 1) u 0) x P.isometry hR
    (fun u v => ?_) (fun u => ?_) hxq hr₀ (fun j hj a ha => ?_) (fun j hj a ha => ?_)
  · have h := hbilip u v 0 0
    simp only [dist_point_zero, dist_eq_norm] at h
    exact h
  · have h0 : stage F.synthetic P 0 u 0 = x + P.isometry u := by
      rw [← hP]
      rfl
    show ‖stage F.synthetic P (N + 1) u 0 - (x + P.isometry u)‖ ≤ Cs * R
    rw [← h0]
    exact (hdisp u 0).trans (displacement_le_of_eps hε (scale_pos F.synthetic 0).le
      ((scale_zero_eq F.synthetic).le.trans hr₀))
  · exact Metric.mem_ball.2 (lt_of_le_of_lt (dist_fst_le_dist_space _ _) (hcent j hj a ha))
  · have ht0 : (F.synthetic.center j a).2.val = 0 := rfl
    obtain ⟨u, hu⟩ := hcenters j hj a ha 0 (by
      rw [ht0, sub_self, abs_zero]
      positivity)
    exact ⟨u, hu.trans
      (coverage_le_quarter hcov hε (scale_pos F.synthetic j) (scale_succ F.synthetic j))⟩

end NeckHubTree

end ParabolicRectifiability
