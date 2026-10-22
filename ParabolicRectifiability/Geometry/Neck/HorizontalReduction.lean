import ParabolicRectifiability.Geometry.Neck.Conclusions
import ParabolicRectifiability.Geometry.Neck.Synthetic

/-!
# The horizontal coherent chart as a consequence of the vertical one

The spatial chart of horizontal coherent data is an elementary consequence of the
vertical chart. This module proves that the statement of `vertical_coherent_chart`
implies the statement of `horizontal_coherent_chart`.

Proof. Replace the family by its synthetic family `F.synthetic` (centers `(x_{j,a}, 0)`,
same rank, planes, parents and scales; `CoherentFamily.synthetic`). Time compatibility with
`0 ≤ γ ≤ min(σ², 1)/4` makes it coherent with the same `σ, δ`, and the horizontal square
bound gives its vertical square bound. Apply the vertical chart, with the same constants
`δ₀, E₀, κ₀, C`, to obtain `Φ(u,t) = (Ĝ(u,t), t)`, and put `G u = Ĝ(u,0)`:

* on the slice `t = 0` the parabolic distances are Euclidean, so `Φ(u,0) = (G u, 0)`
  gives `0.8|u-v| ≤ |G u - G v| ≤ 1.1|u-v|`;
* `range G` is the preimage of the closed set `range Φ` under the isometry
  `x ↦ (x, 0)`, because `Φ` preserves time;
* center heights carry over unchanged; a level limit `z` gives the synthetic level limit
  `(x_z, 0) ∈ range Φ`, hence `x_z ∈ range G`; a stopping parent of `c` is a stopping
  parent of `(x_c, 0)`, and the vertical same-time estimate at time `0` is the spatial
  estimate `|G u - x_c| ≤ C·10·(θ+δ)·d`.

The vertical time modulus is not needed. Every rank `m` is covered, including `m = 0`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal

universe u

/-- The time-preserving map at time zero. -/
theorem timePreservingMap_point_zero {n m : ℕ} (G : Spatial m → ℝ → Spatial n)
    (u : Spatial m) : timePreservingMap G (point u 0) = point (G u 0) 0 := rfl

theorem eq_of_point_eq {n : ℕ} {x y : Spatial n} {t s : ℝ} (h : point x t = point y s) :
    x = y ∧ t = s :=
  ⟨congrArg Prod.fst h, congrArg (fun z : Space n => z.2.val) h⟩

theorem isometry_point_zero {n : ℕ} : Isometry (fun x : Spatial n => point x 0) :=
  Isometry.of_dist_eq fun x y => dist_point_zero x y

/-- The time-zero slice of a time-preserving map: `x = G(u,0)` for some `u` iff `(x,0)` is
in the image of `Φ`. -/
theorem mem_range_slice_iff {n m : ℕ} (G : Spatial m → ℝ → Spatial n) (x : Spatial n) :
    x ∈ range (fun u => G u 0) ↔ point x 0 ∈ range (timePreservingMap G) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨point u 0, rfl⟩
  · rintro ⟨p, hp⟩
    obtain ⟨h1, h2⟩ := eq_of_point_eq hp
    refine ⟨p.1, ?_⟩
    show G p.1 0 = x
    rw [← h2]
    exact h1

/-- **The horizontal chart from the vertical chart.** The statement of
`vertical_coherent_chart` implies the statement of `horizontal_coherent_chart` (the
unused hypotheses `hσ, hσ₁` are written as plain arrows), with the same constants `δ₀, E₀, κ₀, C`. -/
theorem horizontal_coherent_chart_of_vertical
    (hV :
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
                    ∃ u : Spatial m, ‖G u c.2.val - c.1‖ ≤ C * 10 * (θ + δ) * d) :
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
                ∃ u : Spatial m, ‖G u - c.1‖ ≤ C * 10 * (θ + δ) * d := by
  intro n σ hσ hσ₁
  obtain ⟨δ₀, E₀, κ₀, C, hδ₀, hE₀, hκ₀, hC, hchart⟩ := hV n σ hσ hσ₁
  refine ⟨δ₀, E₀, κ₀, C, hδ₀, hE₀, hκ₀, hC, ?_⟩
  intro m ι F δ E γ hδ hδ₀' hE hE₀' hγ hγ' hcoh hsq htime
  obtain ⟨Ĝ, hbilip, -, hclosed, hcover⟩ := hchart F.synthetic δ E hδ hδ₀' hE hE₀'
    (F.isCoherent_synthetic hγ hγ' hcoh htime) (F.verticalSquareBound_synthetic hsq)
  refine ⟨fun u => Ĝ u 0, ?_, ?_, ?_⟩
  · intro u v
    have h := hbilip (point u 0) (point v 0)
    simp only [timePreservingMap_point_zero, dist_point_zero, dist_eq_norm] at h
    exact h
  · have hrange : range (fun u => Ĝ u 0) =
        (fun x : Spatial n => point x 0) ⁻¹' range (timePreservingMap Ĝ) := by
      ext x
      exact mem_range_slice_iff Ĝ x
    rw [hrange]
    exact hclosed.preimage isometry_point_zero.continuous
  · intro κ hκ hκ₀' hheight
    obtain ⟨hlim, hstop⟩ :=
      hcover κ hκ hκ₀' ((F.hasCenterHeight_synthetic_iff).2 hheight)
    refine ⟨fun z hz => (mem_range_slice_iff Ĝ z.1).2 (hlim _ (hz.synthetic F)), ?_⟩
    intro θ hθ c d p hp
    obtain ⟨u, hu⟩ := hstop θ hθ (point c.1 0) d p (hp.synthetic F)
    exact ⟨u, hu⟩

end ParabolicRectifiability
