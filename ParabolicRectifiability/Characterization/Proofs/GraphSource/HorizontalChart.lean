import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.HorizontalClosedExtension

/-! # The spatial chart of a horizontal subset graph

Proves `b2_horizontal_chart_proof` (the statement of `b2_horizontal_chart`): a horizontal graph
of norm `ε` over a subset of its `k`-dimensional direction is parametrized by a bi-Lipschitz
spatial chart on a subset of `ℝ^k` together with a time function satisfying a quadratic
(parabolic Lipschitz) bound.

Construction, for a horizontal graph `G` over `domain ⊆ U` (`U = G.direction`):

* `e : U ≃ₗᵢ ℝ^k`: orthonormal coordinates (`stdOrthonormalBasis` reindexed by
  `finCongr G.rank_eq`); `D = e(domain)`.
* the normal map `g : domain → Uᗮ` is `|ε|`-Lipschitz (`bf1genv1_normal_lipschitz`).
  Its Euclidean coordinates are extended componentwise by McShane (`LipschitzOnWith.extend_pi`,
  sup-norm constant `|ε|`); back in `ℝ^n` the constant is at most `√n |ε|`; composing with the
  orthogonal projection onto `Uᗮ` (`1`-Lipschitz, identity on `Uᗮ`) gives a global
  `√n |ε|`-Lipschitz `g̃ : U → Uᗮ` extending `g`.
* `F(v) = a + e⁻¹ v + g̃(e⁻¹ v)`. Since `e⁻¹ v - e⁻¹ w ∈ U` and `g̃(e⁻¹ v) - g̃(e⁻¹ w) ∈ Uᗮ`,
  `|v - w| ≤ |F v - F w| ≤ (1 + √n |ε|) |v - w|`.
* `τ = h ∘ e⁻¹` on `D` (`0` off `D`); the time bound of the graph envelope gives `|τ u - τ v| ≤ ε²|u - v|²`.

The constant is `L = 1 + √n |ε|`, independent of `k`. No case split on the sign of `ε` is needed
(the graph-envelope Lipschitz and time bounds use `|ε|`). In `n = 0` the trace bound is trivial since
`ℝ^0` is a point; otherwise `|ε| ≤ √n |ε| ≤ L`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- Orthonormal coordinates on the direction of a horizontal graph. -/
def b2chart_coords {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) :
    G.direction ≃ₗᵢ[ℝ] Spatial k :=
  ((stdOrthonormalBasis ℝ G.direction).reindex (finCongr G.rank_eq)).repr

/-- The Euclidean norm on `ℝ^n` is at most `√n` times the sup norm. -/
theorem b2chart_dist_toLp_le {n : ℕ} (a b : Fin n → ℝ) :
    dist (WithLp.toLp 2 a : Spatial n) (WithLp.toLp 2 b) ≤ Real.sqrt n * dist a b := by
  have h := (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).dist_le_mul a b
  have hc : (((Fintype.card (Fin n) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal : ℝ≥0) : ℝ) =
      Real.sqrt n := by
    rw [NNReal.coe_rpow, Fintype.card_fin, NNReal.coe_natCast, Real.sqrt_eq_rpow]
    congr 1
    simp
  rw [hc] at h
  exact h

/-- Componentwise McShane extension of a Lipschitz normal map into `Uᗮ`, followed by the
orthogonal projection onto `Uᗮ`. -/
theorem b2chart_exists_normal_extension {n : ℕ} (U : Submodule ℝ (Spatial n)) (S : Set U)
    (g : S → U.orthogonal) (K : ℝ≥0) (hg : LipschitzWith K g) :
    ∃ g' : U → U.orthogonal,
      (∀ x y : U, ‖((g' x : U.orthogonal) : Spatial n) - ((g' y : U.orthogonal) : Spatial n)‖ ≤
        Real.sqrt n * K * ‖(x : Spatial n) - (y : Spatial n)‖) ∧
      ∀ u : S, g' u.val = g u := by
  classical
  let f : U → Fin n → ℝ := fun x =>
    if h : x ∈ S then WithLp.ofLp ((g ⟨x, h⟩ : U.orthogonal) : Spatial n) else 0
  have hf : LipschitzOnWith K f S := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    simp only [f, hx, hy, dite_true]
    calc dist (WithLp.ofLp ((g ⟨x, hx⟩ : U.orthogonal) : Spatial n))
          (WithLp.ofLp ((g ⟨y, hy⟩ : U.orthogonal) : Spatial n))
        ≤ 1 * dist ((g ⟨x, hx⟩ : U.orthogonal) : Spatial n) ((g ⟨y, hy⟩ : U.orthogonal) : Spatial n) :=
          by
            have := (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℝ)).dist_le_mul
              ((g ⟨x, hx⟩ : U.orthogonal) : Spatial n) ((g ⟨y, hy⟩ : U.orthogonal) : Spatial n)
            simpa using this
      _ = dist (g ⟨x, hx⟩) (g ⟨y, hy⟩) := by rw [one_mul, Subtype.dist_eq]
      _ ≤ K * dist (⟨x, hx⟩ : S) ⟨y, hy⟩ := hg.dist_le_mul _ _
      _ = K * dist x y := by rw [Subtype.dist_eq]
  obtain ⟨φ, hφ, hEq⟩ := hf.extend_pi
  refine ⟨fun x => U.orthogonal.orthogonalProjectionOnto (WithLp.toLp 2 (φ x)), ?_, ?_⟩
  · intro x y
    dsimp only
    rw [← dist_eq_norm, ← Subtype.dist_eq]
    calc dist (U.orthogonal.orthogonalProjectionOnto (WithLp.toLp 2 (φ x)))
          (U.orthogonal.orthogonalProjectionOnto (WithLp.toLp 2 (φ y)))
        ≤ 1 * dist (WithLp.toLp 2 (φ x) : Spatial n) (WithLp.toLp 2 (φ y)) := by
          have := (Submodule.lipschitzWith_orthogonalProjectionOnto U.orthogonal).dist_le_mul
            (WithLp.toLp 2 (φ x) : Spatial n) (WithLp.toLp 2 (φ y))
          simpa using this
      _ ≤ 1 * (Real.sqrt n * dist (φ x) (φ y)) := by
          rw [one_mul, one_mul]; exact b2chart_dist_toLp_le _ _
      _ ≤ 1 * (Real.sqrt n * (K * dist x y)) := by
          gcongr
          exact hφ.dist_le_mul x y
      _ = Real.sqrt n * K * ‖(x : Spatial n) - (y : Spatial n)‖ := by
          rw [Subtype.dist_eq, dist_eq_norm]; ring
  · intro u
    have hu : f u.val = φ u.val := hEq u.2
    simp only [f, u.2, dite_true] at hu
    show U.orthogonal.orthogonalProjectionOnto (WithLp.toLp 2 (φ u.val)) = g u
    rw [← hu, WithLp.toLp_ofLp]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (g u)

/-- Orthogonal decomposition: the chart `x ↦ a + x + g' x` over `U`, with `g'` valued in `Uᗮ`
and `K`-Lipschitz, is bi-Lipschitz with constants `1` and `1 + K`. -/
theorem b2chart_bilip {n : ℕ} (U : Submodule ℝ (Spatial n)) (a : Spatial n)
    (g' : U → U.orthogonal) (K : ℝ)
    (hg : ∀ x y : U, ‖((g' x : U.orthogonal) : Spatial n) - ((g' y : U.orthogonal) : Spatial n)‖ ≤
      K * ‖(x : Spatial n) - (y : Spatial n)‖) (x y : U) :
    ‖(x : Spatial n) - (y : Spatial n)‖ ≤
        ‖(a + (x : Spatial n) + ((g' x : U.orthogonal) : Spatial n)) -
          (a + (y : Spatial n) + ((g' y : U.orthogonal) : Spatial n))‖ ∧
      ‖(a + (x : Spatial n) + ((g' x : U.orthogonal) : Spatial n)) -
          (a + (y : Spatial n) + ((g' y : U.orthogonal) : Spatial n))‖ ≤
        (1 + K) * ‖(x : Spatial n) - (y : Spatial n)‖ := by
  have hsplit : (a + (x : Spatial n) + ((g' x : U.orthogonal) : Spatial n)) -
      (a + (y : Spatial n) + ((g' y : U.orthogonal) : Spatial n)) =
      ((x : Spatial n) - (y : Spatial n)) +
        (((g' x : U.orthogonal) : Spatial n) - ((g' y : U.orthogonal) : Spatial n)) := by
    abel
  rw [hsplit]
  have hxy : (x : Spatial n) - (y : Spatial n) ∈ U := U.sub_mem x.2 y.2
  have hperp : ((g' x : U.orthogonal) : Spatial n) - ((g' y : U.orthogonal) : Spatial n) ∈
      U.orthogonal := U.orthogonal.sub_mem (g' x).2 (g' y).2
  constructor
  · -- the projection onto `U` recovers the `U`-component
    have hproj : U.starProjection
        (((x : Spatial n) - (y : Spatial n)) +
          (((g' x : U.orthogonal) : Spatial n) - ((g' y : U.orthogonal) : Spatial n))) =
        (x : Spatial n) - (y : Spatial n) := by
      rw [map_add, Submodule.starProjection_eq_self_iff.mpr hxy,
        (Submodule.starProjection_apply_eq_zero_iff U).mpr hperp, add_zero]
    have h := U.norm_starProjection_apply_le
      (((x : Spatial n) - (y : Spatial n)) +
        (((g' x : U.orthogonal) : Spatial n) - ((g' y : U.orthogonal) : Spatial n)))
    rw [hproj] at h
    exact h
  · calc _ ≤ ‖(x : Spatial n) - (y : Spatial n)‖ +
          ‖((g' x : U.orthogonal) : Spatial n) - ((g' y : U.orthogonal) : Spatial n)‖ :=
          norm_add_le _ _
      _ ≤ ‖(x : Spatial n) - (y : Spatial n)‖ + K * ‖(x : Spatial n) - (y : Spatial n)‖ := by
          gcongr; exact hg x y
      _ = (1 + K) * ‖(x : Spatial n) - (y : Spatial n)‖ := by ring

/-- In coordinates, distances of the direction are Euclidean distances of `ℝ^k`. -/
theorem b2chart_norm_symm_sub {n k : ℕ} (U : Submodule ℝ (Spatial n))
    (e : U ≃ₗᵢ[ℝ] Spatial k) (u v : Spatial k) :
    ‖((e.symm u : U) : Spatial n) - ((e.symm v : U) : Spatial n)‖ = dist u v := by
  rw [← dist_eq_norm, ← Subtype.dist_eq, LinearIsometryEquiv.dist_map]

/-- The chart with the explicit constant `L = 1 + √n |ε|` (independent of `k`). -/
theorem b2chart_explicit_constant (n k : ℕ) (ε : ℝ) :
    1 ≤ 1 + Real.sqrt n * |ε| ∧ ∀ G : HorizontalGraph n k ε,
      ∃ (F : Spatial k → Spatial n) (D : Set (Spatial k)) (τ : Spatial k → ℝ),
        (∀ u v : Spatial k, dist u v ≤ (1 + Real.sqrt n * |ε|) * dist (F u) (F v) ∧
          dist (F u) (F v) ≤ (1 + Real.sqrt n * |ε|) * dist u v) ∧
        (∀ u ∈ D, ∀ v ∈ D, |τ u - τ v| ≤ (1 + Real.sqrt n * |ε|) ^ 2 * dist u v ^ 2) ∧
        (G.domain.Nonempty → D.Nonempty) ∧ (IsCompact G.domain → IsCompact D) ∧
        G.image ⊆ (fun u => point (F u) (τ u)) '' D := by
  classical
  have hK0 : 0 ≤ Real.sqrt n * |ε| := by positivity
  have hL1 : 1 ≤ 1 + Real.sqrt n * |ε| := by linarith
  refine ⟨hL1, fun G => ?_⟩
  let e : G.direction ≃ₗᵢ[ℝ] Spatial k := b2chart_coords G
  obtain ⟨g', hg'L, hg'eq⟩ := b2chart_exists_normal_extension G.direction G.domain G.normal _
    (bf1genv1_normal_lipschitz G)
  have hg'L' : ∀ x y : G.direction,
      ‖((g' x : G.direction.orthogonal) : Spatial n) -
          ((g' y : G.direction.orthogonal) : Spatial n)‖ ≤
        Real.sqrt n * |ε| * ‖(x : Spatial n) - (y : Spatial n)‖ := by
    intro x y
    have := hg'L x y
    rwa [Real.coe_toNNReal _ (abs_nonneg ε)] at this
  obtain ⟨τ0, hτ0⟩ : ∃ τ0 : G.direction → ℝ, ∀ u : G.domain, τ0 u.val = G.time u :=
    ⟨fun x => if h : x ∈ G.domain then G.time ⟨x, h⟩ else 0, fun u => by simp [u.2]⟩
  refine ⟨fun v => G.offset + ((e.symm v : G.direction) : Spatial n) +
      ((g' (e.symm v) : G.direction.orthogonal) : Spatial n),
    e '' G.domain, fun v => τ0 (e.symm v), ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    obtain ⟨hlo, hhi⟩ := b2chart_bilip G.direction G.offset g' _ hg'L' (e.symm u) (e.symm v)
    rw [b2chart_norm_symm_sub] at hlo hhi
    simp only [dist_eq_norm] at hlo hhi ⊢
    exact ⟨hlo.trans (le_mul_of_one_le_left (norm_nonneg _) hL1), hhi⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [LinearIsometryEquiv.symm_apply_apply]
    have h1 : τ0 x = G.time ⟨x, hx⟩ := hτ0 ⟨x, hx⟩
    have h2 : τ0 y = G.time ⟨y, hy⟩ := hτ0 ⟨y, hy⟩
    rw [h1, h2]
    have hd : ‖((x : G.direction) : Spatial n) - ((y : G.direction) : Spatial n)‖ =
        dist (e x) (e y) := by
      rw [LinearIsometryEquiv.dist_map, Subtype.dist_eq, dist_eq_norm]
    have ht : |G.time ⟨x, hx⟩ - G.time ⟨y, hy⟩| ≤
        (|ε| * ‖((x : G.direction) : Spatial n) - ((y : G.direction) : Spatial n)‖) ^ 2 :=
      bf1genv1_time_bound G ⟨x, hx⟩ ⟨y, hy⟩
    rw [hd] at ht
    have hcoef : |ε| * dist (e x) (e y) ≤ (1 + Real.sqrt n * |ε|) * dist (e x) (e y) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have h0 : ∀ w : Spatial 0, ‖w‖ = 0 := fun w => by simp [EuclideanSpace.norm_eq]
        rw [← hd, h0, mul_zero, mul_zero]
      · have hsq : 1 ≤ Real.sqrt n := by
          rw [Real.one_le_sqrt]
          exact_mod_cast hn
        have h3 := mul_le_mul_of_nonneg_right hsq (abs_nonneg ε)
        have : |ε| ≤ 1 + Real.sqrt n * |ε| := by linarith
        exact mul_le_mul_of_nonneg_right this dist_nonneg
    calc |G.time ⟨x, hx⟩ - G.time ⟨y, hy⟩| ≤ (|ε| * dist (e x) (e y)) ^ 2 := ht
      _ ≤ ((1 + Real.sqrt n * |ε|) * dist (e x) (e y)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (abs_nonneg ε) dist_nonneg) hcoef 2
      _ = (1 + Real.sqrt n * |ε|) ^ 2 * dist (e x) (e y) ^ 2 := by ring
  · exact fun h => h.image _
  · exact fun h => h.image e.continuous
  · intro z hz
    simp only [HorizontalGraph.image, Set.mem_range] at hz
    obtain ⟨u, rfl⟩ := hz
    refine ⟨e u.val, ⟨u.val, u.2, rfl⟩, ?_⟩
    simp only [LinearIsometryEquiv.symm_apply_apply]
    rw [hg'eq u, hτ0 u]

/-- **Spatial chart of a horizontal graph** (the statement of `b2_horizontal_chart`), with
`L = 1 + √n |ε|`. -/
theorem b2_horizontal_chart_proof :
    ∀ (n k : ℕ) (ε : ℝ), ∃ L : ℝ, 1 ≤ L ∧ ∀ G : HorizontalGraph n k ε,
      ∃ (F : Spatial k → Spatial n) (D : Set (Spatial k)) (τ : Spatial k → ℝ),
        (∀ u v : Spatial k, dist u v ≤ L * dist (F u) (F v) ∧ dist (F u) (F v) ≤ L * dist u v) ∧
        (∀ u ∈ D, ∀ v ∈ D, |τ u - τ v| ≤ L ^ 2 * dist u v ^ 2) ∧
        (G.domain.Nonempty → D.Nonempty) ∧ (IsCompact G.domain → IsCompact D) ∧
        G.image ⊆ (fun u => point (F u) (τ u)) '' D :=
  fun n k ε => ⟨_, b2chart_explicit_constant n k ε⟩

end ParabolicRectifiability.Characterization
