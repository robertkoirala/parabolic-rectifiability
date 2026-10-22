import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion
import ParabolicRectifiability.Geometry.Neck.NeckTheorems

/-! # The horizontal neck trace (`d1e_horizontal_trace`)

Proof of `d1e_HorizontalTraceStatement` (premise-free) from
`NeckHubTree.horizontal_neck_structure_proof`.

The structure theorem, at `c₀` and `σ`, gives thresholds `δ₀ E₀ κ₀ θ₀` and, for a horizontal neck with
`δ ≤ δ₀`, `E ≤ E₀`, `κ ≤ κ₀`, `θ ≤ θ₀`, `γ ≤ min(σ², min(c₀², 1))/4`, a horizontal
parametrization with distortion `2`. We take
`ε₀ = min(δ₀, E₀, κ₀, θ₀, min(σ², min(c₀², 1))/4)`; it is positive and bounds all five
tolerances of the statement (the statement quantifies `ε₀` after `n k c₀ σ` and before the
tolerances and the neck). The upper bi-Lipschitz bound of the pair `(G, τ_A)` gives
`√|τ u - τ v| ≤ 2 |u - v|`, hence `|τ u - τ v| ≤ 2² |u - v|²`; `τ_A` is extended by `0` off `A`.
If `A = ∅` the centre set is empty and `D = {0}`, `τ = 0` is a singleton trace.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-- The quadratic bound for the time coordinate from the upper bi-Lipschitz bound of the
point map `u ↦ (G u, τ u)` (distortion `2`). -/
theorem d1ehtrace_time_bound {k n : ℕ} (G : Spatial k → Spatial n) (A : Set (Spatial k))
    (τ : A → ℝ)
    (hbl : ∀ u v : A, dist (point (G u) (τ u)) (point (G v) (τ v)) ≤ 2 * dist u v)
    (u v : A) : |τ u - τ v| ≤ 2 ^ 2 * dist (u : Spatial k) v ^ 2 := by
  have h := hbl u v
  rw [dist_point] at h
  have h2 : Real.sqrt |τ u - τ v| ≤ 2 * dist (u : Spatial k) v :=
    (le_max_right _ _).trans (by simpa [Subtype.dist_eq] using h)
  have h3 := (Real.sqrt_le_left (by positivity)).1 h2
  calc |τ u - τ v| ≤ (2 * dist (u : Spatial k) v) ^ 2 := h3
    _ = 2 ^ 2 * dist (u : Spatial k) v ^ 2 := by ring

/-- **`d1e_horizontal_trace`**: the horizontal neck trace. -/
theorem d1e_horizontal_trace_proof : d1e_HorizontalTraceStatement := by
  intro n k c₀ σ hc₀ hσ hσ₁
  obtain ⟨_cb, _Cr, _Cm, -, hhub⟩ := NeckHubTree.horizontal_neck_structure_proof n
  obtain ⟨_C, -, hhub₂⟩ := hhub c₀ hc₀
  obtain ⟨δ₀, E₀, κ₀, θ₀, hδ₀, hE₀, hκ₀, hθ₀, hN⟩ := hhub₂ σ hσ hσ₁
  have hγpos : 0 < min (σ ^ 2) (min (c₀ ^ 2) 1) / 4 :=
    div_pos (lt_min (by positivity) (lt_min (by positivity) one_pos)) (by norm_num)
  refine ⟨min (min (min (min δ₀ E₀) κ₀) θ₀) (min (σ ^ 2) (min (c₀ ^ 2) 1) / 4),
    lt_min (lt_min (lt_min (lt_min hδ₀ hE₀) hκ₀) hθ₀) hγpos, ?_⟩
  intro ι q R Cd Cs δ E κ θ γ hδ hE hκ hθ hγ N
  have hpar : N.HasHorizontalParametrization 2 :=
    (hN N (hδ.trans (min_le_left _ _ |>.trans (min_le_left _ _) |>.trans (min_le_left _ _)
        |>.trans (min_le_left _ _)))
      (hE.trans (min_le_left _ _ |>.trans (min_le_left _ _) |>.trans (min_le_left _ _)
        |>.trans (min_le_right _ _)))
      (hκ.trans (min_le_left _ _ |>.trans (min_le_left _ _) |>.trans (min_le_right _ _)))
      (hθ.trans (min_le_left _ _ |>.trans (min_le_right _ _)))
      (hγ.trans (min_le_right _ _))).1
  obtain ⟨G, hG, A, τ, hA, hbl, hrange⟩ := hpar
  refine ⟨G, fun u v => ?_, ?_⟩
  · have h := hG u v
    rw [dist_eq_norm, dist_eq_norm]
    constructor
    · have := h.1
      linarith
    · exact h.2
  · by_cases hAe : A.Nonempty
    · classical
      refine ⟨A, fun u => if h : u ∈ A then τ ⟨u, h⟩ else 0, hAe, hA, ?_, ?_⟩
      · intro u hu v hv
        have := d1ehtrace_time_bound G A τ (fun a b => (hbl a b).2) ⟨u, hu⟩ ⟨v, hv⟩
        simpa [hu, hv] using this
      · intro c hc
        rw [← hrange] at hc
        obtain ⟨u, rfl⟩ := hc
        exact ⟨u, u.2, by simp [u.2]⟩
    · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.1 hAe
      have hcen : N.centers = ∅ := by
        rw [← hrange]
        refine Set.range_eq_empty_iff.2 ?_
        rw [hAempty]
        infer_instance
      refine ⟨{0}, fun _ => 0, Set.singleton_nonempty _, isCompact_singleton, ?_, ?_⟩
      · intro u _ v _
        simp
      · rw [hcen]
        exact Set.empty_subset _

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
