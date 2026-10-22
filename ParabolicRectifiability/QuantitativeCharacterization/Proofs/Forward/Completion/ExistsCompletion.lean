import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion

/-! # The completion datum exists (`d1e_exists_completion`)

Proves `d1e_exists_completion_proof : d1e_CompletionDatumStatement`.

Route (metric only, no tents). For a stopping centre `c` choose a parameter `u_c` of the
hypothesis and put `p_c = (u_c, t_c)` (the centre's own time); elsewhere `p_c = (0, t_c)`.
Then `d(Φ⁰ p_c, c) = |F⁰(p_c) - x_c| ≤ 2 ζ d_c`. The triangle inequality, the upper chart bound
`1.1`, stop separation `c₀ max(d_c, d_{c'}) ≤ d(c, c')` and `30 χ ≤ min(c₀, 1)`, `24 ζ ≤ χ` give
`χ (d_c + d_{c'}) ≤ d(p_c, p_{c'})`; core separation `d_c ≤ d(c, z)` gives
`χ d_c ≤ d(p, p_c)` for every core preimage `p`.

Helpers carry the prefix `d1edatum_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

open ParabolicRectifiability.Foundations

/-- The time-preserving image of a parameter at the time of `c` is at parabolic distance
`|G(v, t_c) - x_c|` from `c`. -/
theorem d1edatum_dist_map_same_time {n m : ℕ} (G : Spatial m → ℝ → Spatial n)
    (v : Spatial m) (c : Space n) :
    dist (timePreservingMap G (v, c.2)) c = ‖G v c.2.val - c.1‖ := by
  show dist (point (G v c.2.val) c.2.val) (point c.1 c.2.val) = _
  rw [dist_point, sub_self, abs_zero, Real.sqrt_zero, max_eq_left (norm_nonneg _)]

/-- Separation arithmetic: from `c₀ max(d, d') ≤ D ≤ 2ζd + 1.1 X + 2ζd'` with
`30 χ ≤ c₀` and `24 ζ ≤ χ`, `χ d + χ d' ≤ X`. -/
theorem d1edatum_separation_arith {c₀ χ ζ d d' D X : ℝ} (hχ : 0 < χ)
    (hc₀ : 30 * χ ≤ c₀) (hζχ : 24 * ζ ≤ χ) (hd : 0 ≤ d) (hd' : 0 ≤ d')
    (hsep : c₀ * max d d' ≤ D) (htri : D ≤ 2 * ζ * d + 11 / 10 * X + 2 * ζ * d') :
    χ * d + χ * d' ≤ X := by
  have hmax : 0 ≤ max d d' := le_trans hd (le_max_left _ _)
  have h1 : 30 * χ * max d d' ≤ c₀ * max d d' := mul_le_mul_of_nonneg_right hc₀ hmax
  have h2 : d + d' ≤ 2 * max d d' := by
    have := le_max_left d d'
    have := le_max_right d d'
    linarith
  have h3 : χ * (d + d') ≤ χ * (2 * max d d') := mul_le_mul_of_nonneg_left h2 hχ.le
  have h4 : 24 * ζ * d ≤ χ * d := mul_le_mul_of_nonneg_right hζχ hd
  have h5 : 24 * ζ * d' ≤ χ * d' := mul_le_mul_of_nonneg_right hζχ hd'
  nlinarith

/-- Core-avoidance arithmetic: from `d ≤ D ≤ 2ζd + 1.1 X` with `30 χ ≤ 1` and
`24 ζ ≤ χ`, `χ d ≤ X`. -/
theorem d1edatum_core_arith {χ ζ d D X : ℝ} (hχ1 : 30 * χ ≤ 1) (hζχ : 24 * ζ ≤ χ)
    (hd : 0 ≤ d) (hsep : d ≤ D) (htri : D ≤ 2 * ζ * d + 11 / 10 * X) :
    χ * d ≤ X := by
  have h1 : 30 * χ * d ≤ 1 * d := mul_le_mul_of_nonneg_right hχ1 hd
  have h2 : 24 * ζ * d ≤ χ * d := mul_le_mul_of_nonneg_right hζχ hd
  nlinarith

/-- The parameter chosen for a stopping centre (zero elsewhere). -/
def d1edatum_param {n k : ℕ} {ι : Type} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
    (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ)
    (P : CoherentChart.InitialChart N.family) (ζ : ℝ)
    (hstop : ∀ c ∈ N.stopping, ∃ u : Spatial (NeckType.vertical.rank k),
      ‖d1e_projectionLimit N.family P u c.2.val - c.1‖ ≤ 2 * ζ * N.radius c)
    (c : Space n) : Spatial (NeckType.vertical.rank k) := by
  classical
  exact if h : c ∈ N.stopping then Classical.choose (hstop c h) else 0

theorem d1edatum_param_spec {n k : ℕ} {ι : Type} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
    (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ)
    (P : CoherentChart.InitialChart N.family) (ζ : ℝ)
    (hstop : ∀ c ∈ N.stopping, ∃ u : Spatial (NeckType.vertical.rank k),
      ‖d1e_projectionLimit N.family P u c.2.val - c.1‖ ≤ 2 * ζ * N.radius c)
    {c : Space n} (hc : c ∈ N.stopping) :
    ‖d1e_projectionLimit N.family P (d1edatum_param N P ζ hstop c) c.2.val - c.1‖ ≤
      2 * ζ * N.radius c := by
  classical
  unfold d1edatum_param
  rw [dite_eq_left hc]
  exact Classical.choose_spec (hstop c hc)

/-- **Existence of the completion datum**: the type `d1e_CompletionDatumStatement`. -/
theorem d1e_exists_completion_proof : d1e_CompletionDatumStatement := by
  intro n k ι q R c₀ Cd Cs σ δ E κ θ γ N P χ ζ hχ _hζ hχc hζχ hmet hstop
  have hc₀ : 30 * χ ≤ c₀ := hχc.trans (min_le_left _ _)
  have hχ1 : 30 * χ ≤ 1 := hχc.trans (min_le_right _ _)
  set u := d1edatum_param N P ζ hstop with hu_def
  have hu : ∀ c ∈ N.stopping,
      dist (timePreservingMap (d1e_projectionLimit N.family P) (u c, c.2)) c ≤
        2 * ζ * N.radius c := by
    intro c hc
    rw [d1edatum_dist_map_same_time]
    exact d1edatum_param_spec N P ζ hstop hc
  refine ⟨{ chart := P
            pre := fun c => (u c, c.2)
            pre_time := fun c _ => rfl
            stop_error := fun c hc => d1edatum_param_spec N P ζ hstop hc
            ball_disjoint := ?_
            core_avoid := ?_ }, rfl⟩
  · intro c hc c' hc' hne
    have hsep := N.stop_separation c hc.1 c' hc'.1 hc.2 hc'.2 hne
    have hup := (hmet (u c, c.2) (u c', c'.2)).2
    have htri : dist c c' ≤ 2 * ζ * N.radius c +
        11 / 10 * dist ((u c, c.2) : Space (NeckType.vertical.rank k)) (u c', c'.2) +
          2 * ζ * N.radius c' := by
      have h1 := dist_triangle4 c (timePreservingMap (d1e_projectionLimit N.family P) (u c, c.2))
        (timePreservingMap (d1e_projectionLimit N.family P) (u c', c'.2)) c'
      have h2 : dist c (timePreservingMap (d1e_projectionLimit N.family P) (u c, c.2)) ≤
          2 * ζ * N.radius c := by
        rw [dist_comm]; exact hu c hc
      have h3 := hu c' hc'
      linarith
    exact d1edatum_separation_arith hχ hc₀ hζχ hc.2.le hc'.2.le hsep htri
  · intro c hc p hp
    have hcore := N.core_separation c hc.1 hc.2 _ hp.1 hp.2
    have hup := (hmet (u c, c.2) p).2
    have htri : dist c (timePreservingMap (d1e_projectionLimit N.family P) p) ≤
        2 * ζ * N.radius c + 11 / 10 * dist p ((u c, c.2) : Space (NeckType.vertical.rank k)) := by
      have h1 := dist_triangle c (timePreservingMap (d1e_projectionLimit N.family P) (u c, c.2))
        (timePreservingMap (d1e_projectionLimit N.family P) p)
      have h2 : dist c (timePreservingMap (d1e_projectionLimit N.family P) (u c, c.2)) ≤
          2 * ζ * N.radius c := by
        rw [dist_comm]; exact hu c hc
      rw [dist_comm p]
      linarith
    exact d1edatum_core_arith hχ1 hζχ hc.2.le hcore htri

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
