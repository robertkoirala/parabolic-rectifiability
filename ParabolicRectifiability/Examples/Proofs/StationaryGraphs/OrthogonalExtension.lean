import ParabolicRectifiability.Examples.Proofs.Reductions.ReductionStatements

/-! # Orthogonal Lipschitz extension

An `L`-Lipschitz map `g : E → W^⊥` on a subset
`E ⊆ W` extends to `g' : W → W^⊥` with Lipschitz bound `√(n - dim W) L`. Route: coordinates in
`stdOrthonormalBasis ℝ W^⊥` (of size `finrank W^⊥ = n - dim W`), each coordinate is `L`-Lipschitz
on `E` and extended by McShane (`LipschitzOnWith.extend_real`); reassembling gives a map whose
Euclidean distance is at most `√d · L · dist`. The case `E = ∅` needs no separate treatment. -/

noncomputable section

namespace ParabolicRectifiability.Examples

open scoped NNReal

theorem e2_orthogonalExtension_proof : E2OrthogonalExtensionStatement := by
  intro n W E g L hg
  classical
  let b := stdOrthonormalBasis ℝ Wᗮ
  have hdim : Module.finrank ℝ Wᗮ = n - Module.finrank ℝ W := by
    have h := Submodule.finrank_add_finrank_orthogonal W
    rw [finrank_euclideanSpace_fin] at h
    omega
  -- coordinate functions, defined on all of `W`
  let F : Fin (Module.finrank ℝ Wᗮ) → W → ℝ :=
    fun i u => if h : u ∈ E then b.repr (g ⟨u, h⟩) i else 0
  have hF : ∀ i, LipschitzOnWith L (F i) E := by
    intro i
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [F, hx, hy, dite_true]
    have h1 : dist (g ⟨x, hx⟩) (g ⟨y, hy⟩) ≤ L * dist x y := by
      have := hg.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
      simpa [Subtype.dist_eq] using this
    calc dist (b.repr (g ⟨x, hx⟩) i) (b.repr (g ⟨y, hy⟩) i)
        ≤ dist (b.repr (g ⟨x, hx⟩)) (b.repr (g ⟨y, hy⟩)) := PiLp.dist_apply_le _ _ i
      _ = dist (g ⟨x, hx⟩) (g ⟨y, hy⟩) := b.repr.dist_map _ _
      _ ≤ L * dist x y := h1
  choose G hGL hGeq using fun i => (hF i).extend_real
  refine ⟨fun u => b.repr.symm (WithLp.toLp 2 fun i => G i u), ?_, ?_⟩
  · intro u
    apply b.repr.injective
    ext i
    have := hGeq i u.2
    simp only [F, u.2, dite_true] at this
    simpa using this.symm
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    have hcoord : ∀ i, dist (G i u) (G i v) ≤ L * dist u v := fun i =>
      (hGL i).dist_le_mul u v
    have hsum : ∑ i, dist (G i u) (G i v) ^ 2 ≤
        (Module.finrank ℝ Wᗮ : ℝ) * (L * dist u v) ^ 2 := by
      calc ∑ i, dist (G i u) (G i v) ^ 2 ≤ ∑ _i : Fin (Module.finrank ℝ Wᗮ), (L * dist u v) ^ 2 :=
            Finset.sum_le_sum fun i _ =>
              pow_le_pow_left₀ dist_nonneg (hcoord i) 2
        _ = (Module.finrank ℝ Wᗮ : ℝ) * (L * dist u v) ^ 2 := by simp
    have hc : ((Module.finrank ℝ Wᗮ : ℕ) : ℝ) = ((n - Module.finrank ℝ W : ℕ) : ℝ) := by
      rw [hdim]
    rw [hc] at hsum
    rw [← b.repr.dist_map, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.apply_symm_apply, EuclideanSpace.dist_eq]
    rw [NNReal.coe_mul, Real.coe_sqrt, NNReal.coe_natCast]
    calc Real.sqrt (∑ i, dist (G i u) (G i v) ^ 2)
        ≤ Real.sqrt (((n - Module.finrank ℝ W : ℕ) : ℝ) * (L * dist u v) ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt ((n - Module.finrank ℝ W : ℕ) : ℝ) * (L * dist u v) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      _ = _ := by ring

end ParabolicRectifiability.Examples
