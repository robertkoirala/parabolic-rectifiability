import ParabolicRectifiability.Characterization.Proofs.GraphSource.HorizontalChart
import ParabolicRectifiability.QuantitativeCharacterization.Statements.PiecesComponents

/-! # The sharp horizontal chart

Proves `dp2_sharp_chart_proof : dp2_SharpChartStatement`.

Proof idea: a copy of `Characterization.b2chart_explicit_constant` at `ε = 1`,
reusing the coordinates `b2chart_coords`, the normal extension `b2chart_exists_normal_extension`
(at `K = |1| = 1`, so `‖g' x - g' y‖ ≤ √n ‖x - y‖`) and `b2chart_norm_symm_sub`, with
`b2chart_bilip` replaced by its Pythagorean companion `dp2_sc_bilip`: `x - y ∈ U` and
`g' x - g' y ∈ Uᗮ` are orthogonal, so `‖F x - F y‖² = ‖x - y‖² + ‖g' x - g' y‖²`, which lies
between `‖x - y‖²` and `(1 + n) ‖x - y‖²`. The trace bound is `Foundations.bf1genv1_time_bound`
at `ε = 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.Characterization

/-- Pythagoras on `U ⊕ Uᗮ`: for `g'` valued in `Uᗮ`, the chart `x ↦ a + x + g' x` satisfies
`‖F x - F y‖² = ‖x - y‖² + ‖g' x - g' y‖²` (written with products). -/
theorem dp2_sc_pythagoras {n : ℕ} (U : Submodule ℝ (Spatial n)) (a : Spatial n)
    (g' : U → U.orthogonal) (x y : U) :
    ‖(a + (x : Spatial n) + ((g' x : U.orthogonal) : Spatial n)) -
        (a + (y : Spatial n) + ((g' y : U.orthogonal) : Spatial n))‖ *
      ‖(a + (x : Spatial n) + ((g' x : U.orthogonal) : Spatial n)) -
        (a + (y : Spatial n) + ((g' y : U.orthogonal) : Spatial n))‖ =
    ‖(x : Spatial n) - (y : Spatial n)‖ * ‖(x : Spatial n) - (y : Spatial n)‖ +
      ‖((g' x : U.orthogonal) : Spatial n) - ((g' y : U.orthogonal) : Spatial n)‖ *
        ‖((g' x : U.orthogonal) : Spatial n) - ((g' y : U.orthogonal) : Spatial n)‖ := by
  have hsplit : (a + (x : Spatial n) + ((g' x : U.orthogonal) : Spatial n)) -
      (a + (y : Spatial n) + ((g' y : U.orthogonal) : Spatial n)) =
      ((x : Spatial n) - (y : Spatial n)) +
        (((g' x : U.orthogonal) : Spatial n) - ((g' y : U.orthogonal) : Spatial n)) := by
    abel
  rw [hsplit]
  have hxy : (x : Spatial n) - (y : Spatial n) ∈ U := U.sub_mem x.2 y.2
  have hperp : ((g' x : U.orthogonal) : Spatial n) - ((g' y : U.orthogonal) : Spatial n) ∈
      U.orthogonal := U.orthogonal.sub_mem (g' x).2 (g' y).2
  exact norm_add_sq_eq_norm_sq_add_norm_sq_real (Submodule.inner_right_of_mem_orthogonal hxy hperp)

/-- The sharp companion of `b2chart_bilip`: if `g' : U → Uᗮ` is `√n`-Lipschitz, the chart
`x ↦ a + x + g' x` is bi-Lipschitz with constants `1` and `√(1+n)`. -/
theorem dp2_sc_bilip {n : ℕ} (U : Submodule ℝ (Spatial n)) (a : Spatial n)
    (g' : U → U.orthogonal)
    (hg : ∀ x y : U, ‖((g' x : U.orthogonal) : Spatial n) - ((g' y : U.orthogonal) : Spatial n)‖ ≤
      Real.sqrt n * ‖(x : Spatial n) - (y : Spatial n)‖) (x y : U) :
    ‖(x : Spatial n) - (y : Spatial n)‖ ≤
        ‖(a + (x : Spatial n) + ((g' x : U.orthogonal) : Spatial n)) -
          (a + (y : Spatial n) + ((g' y : U.orthogonal) : Spatial n))‖ ∧
      ‖(a + (x : Spatial n) + ((g' x : U.orthogonal) : Spatial n)) -
          (a + (y : Spatial n) + ((g' y : U.orthogonal) : Spatial n))‖ ≤
        Real.sqrt (1 + n) * ‖(x : Spatial n) - (y : Spatial n)‖ := by
  have hP := dp2_sc_pythagoras U a g' x y
  set N := ‖(a + (x : Spatial n) + ((g' x : U.orthogonal) : Spatial n)) -
      (a + (y : Spatial n) + ((g' y : U.orthogonal) : Spatial n))‖ with hN
  set A := ‖(x : Spatial n) - (y : Spatial n)‖ with hA
  set B := ‖((g' x : U.orthogonal) : Spatial n) - ((g' y : U.orthogonal) : Spatial n)‖ with hB
  have hN0 : 0 ≤ N := norm_nonneg _
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hBA : B * B ≤ n * (A * A) := by
    have h1 : B * B ≤ (Real.sqrt n * A) * (Real.sqrt n * A) :=
      mul_self_le_mul_self hB0 (hg x y)
    have h2 : (Real.sqrt n * A) * (Real.sqrt n * A) = n * (A * A) := by
      rw [show (Real.sqrt n * A) * (Real.sqrt n * A) = (Real.sqrt n * Real.sqrt n) * (A * A) by
        ring, Real.mul_self_sqrt hn0]
    linarith
  constructor
  · apply (mul_self_le_mul_self_iff hA0 hN0).mpr
    nlinarith [mul_self_nonneg B]
  · have hS0 : 0 ≤ Real.sqrt (1 + n) * A := mul_nonneg (Real.sqrt_nonneg _) hA0
    apply (mul_self_le_mul_self_iff hN0 hS0).mpr
    have h3 : (Real.sqrt (1 + n) * A) * (Real.sqrt (1 + n) * A) = (1 + n) * (A * A) := by
      rw [show (Real.sqrt (1 + n) * A) * (Real.sqrt (1 + n) * A) =
          (Real.sqrt (1 + n) * Real.sqrt (1 + n)) * (A * A) by ring,
        Real.mul_self_sqrt (by linarith)]
    rw [h3]
    nlinarith

/-- **The sharp horizontal chart** (`dp2_sharp_chart`): the chart
`F v = offset + e⁻¹ v + g'(e⁻¹ v)`, base `D = e '' G.domain`, trace `τ = time ∘ e⁻¹` on `D`. -/
theorem dp2_sharp_chart_proof : dp2_SharpChartStatement := by
  classical
  intro n k G
  let e : G.direction ≃ₗᵢ[ℝ] Spatial k := b2chart_coords G
  obtain ⟨g', hg'L, hg'eq⟩ := b2chart_exists_normal_extension G.direction G.domain G.normal _
    (bf1genv1_normal_lipschitz G)
  have hg'L' : ∀ x y : G.direction,
      ‖((g' x : G.direction.orthogonal) : Spatial n) -
          ((g' y : G.direction.orthogonal) : Spatial n)‖ ≤
        Real.sqrt n * ‖(x : Spatial n) - (y : Spatial n)‖ := by
    intro x y
    have := hg'L x y
    rwa [abs_one, Real.toNNReal_one, NNReal.coe_one, mul_one] at this
  obtain ⟨τ0, hτ0⟩ : ∃ τ0 : G.direction → ℝ, ∀ u : G.domain, τ0 u.val = G.time u :=
    ⟨fun x => if h : x ∈ G.domain then G.time ⟨x, h⟩ else 0, fun u => by simp [u.2]⟩
  refine ⟨fun v => G.offset + ((e.symm v : G.direction) : Spatial n) +
      ((g' (e.symm v) : G.direction.orthogonal) : Spatial n),
    e '' G.domain, fun v => τ0 (e.symm v), ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    obtain ⟨hlo, hhi⟩ := dp2_sc_bilip G.direction G.offset g' hg'L' (e.symm u) (e.symm v)
    rw [b2chart_norm_symm_sub] at hlo hhi
    simp only [dist_eq_norm] at hlo hhi ⊢
    exact ⟨hlo, hhi⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [LinearIsometryEquiv.symm_apply_apply]
    have h1 : τ0 x = G.time ⟨x, hx⟩ := hτ0 ⟨x, hx⟩
    have h2 : τ0 y = G.time ⟨y, hy⟩ := hτ0 ⟨y, hy⟩
    rw [h1, h2]
    have hd : ‖((x : G.direction) : Spatial n) - ((y : G.direction) : Spatial n)‖ =
        dist (e x) (e y) := by
      rw [LinearIsometryEquiv.dist_map, Subtype.dist_eq, dist_eq_norm]
    have ht : |G.time ⟨x, hx⟩ - G.time ⟨y, hy⟩| ≤
        (|(1 : ℝ)| * ‖((x : G.direction) : Spatial n) - ((y : G.direction) : Spatial n)‖) ^ 2 :=
      bf1genv1_time_bound G ⟨x, hx⟩ ⟨y, hy⟩
    rwa [hd, abs_one, one_mul] at ht
  · exact fun h => h.image _
  · exact fun h => h.image e.continuous
  · intro z hz
    simp only [HorizontalGraph.image, Set.mem_range] at hz
    obtain ⟨u, rfl⟩ := hz
    refine ⟨e u.val, ⟨u.val, u.2, rfl⟩, ?_⟩
    simp only [LinearIsometryEquiv.symm_apply_apply]
    rw [hg'eq u, hτ0 u]

end ParabolicRectifiability.QuantitativeCharacterization
