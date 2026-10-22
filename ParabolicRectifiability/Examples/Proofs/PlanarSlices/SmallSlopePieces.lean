import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiabilityStatements
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Nat.Pairing

/-! # Small-slope pieces of a differentiable curve

A countable dense family of nonzero vectors supplies the line directions. At a
parameter with nonzero derivative, choose a nearby vector and a uniform radius
for the linear approximation. Intersect each approximation class with a ball
of half that radius. Every chord in the resulting piece has small error from a
vector on its chosen line; contraction of both orthogonal projections then
controls its slope. No regularity away from the covered parameters is needed.
-/

noncomputable section

open Set Filter Topology
open ParabolicRectifiability.BetaP (Plane)

namespace ParabolicRectifiability.Examples

private theorem slope_of_linear_error (q w : Plane) (a η θ : ℝ)
    (hθ : 0 ≤ θ) (hηθ : η ≤ θ * (1 - η))
    (herr : ‖w - a • q‖ ≤ η * (|a| * ‖q‖)) :
    ‖(ℝ ∙ q)ᗮ.starProjection w‖ ≤ θ * ‖(ℝ ∙ q).starProjection w‖ := by
  let V : Submodule ℝ Plane := ℝ ∙ q
  have hq : a • q ∈ V := V.smul_mem a (Submodule.mem_span_singleton_self q)
  have hpar : V.starProjection (a • q) = a • q :=
    V.starProjection_eq_self_iff.mpr hq
  have hperp : Vᗮ.starProjection (a • q) = 0 :=
    V.starProjection_orthogonal_apply_eq_zero hq
  have hn : ‖Vᗮ.starProjection w‖ ≤ η * (|a| * ‖q‖) := by
    calc
      ‖Vᗮ.starProjection w‖ = ‖Vᗮ.starProjection (w - a • q)‖ := by
        rw [map_sub, hperp, sub_zero]
      _ ≤ ‖w - a • q‖ := Vᗮ.norm_starProjection_apply_le _
      _ ≤ _ := herr
  have hp : (1 - η) * (|a| * ‖q‖) ≤ ‖V.starProjection w‖ := by
    have hb := V.norm_starProjection_apply_le (w - a • q)
    rw [map_sub, hpar] at hb
    have ht := norm_le_norm_add_norm_sub' (a • q) (V.starProjection w)
    rw [norm_sub_rev (a • q)] at ht
    rw [norm_smul, Real.norm_eq_abs] at ht
    nlinarith
  exact hn.trans ((mul_le_mul_of_nonneg_right hηθ (mul_nonneg (abs_nonneg _) (norm_nonneg _))).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hθ))

private theorem near_direction_radius (F : ℝ → Plane) (s : ℝ) (v q : Plane) (η : ℝ)
    (hq : q ≠ 0) (hη : 0 < η) (hv : HasDerivAt F v s)
    (hclose : ‖v - q‖ < η / 2 * ‖q‖) :
    ∃ r > 0, ∀ t : ℝ, dist t s < r →
      ‖F t - F s - (t - s) • q‖ ≤ η * (|t - s| * ‖q‖) := by
  have hc : 0 < η / 2 * ‖q‖ := mul_pos (by linarith) (norm_pos_iff.mpr hq)
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp (hv.isLittleO.def hc)
  refine ⟨r, hr, fun t ht => ?_⟩
  have he := hb ht
  change ‖F t - F s - (t - s) • v‖ ≤ η / 2 * ‖q‖ * ‖t - s‖ at he
  calc
    ‖F t - F s - (t - s) • q‖ =
        ‖(F t - F s - (t - s) • v) + (t - s) • (v - q)‖ := by
      congr 1
      simp only [smul_sub]
      abel
    _ ≤ ‖F t - F s - (t - s) • v‖ + ‖(t - s) • (v - q)‖ := norm_add_le _ _
    _ ≤ η / 2 * ‖q‖ * |t - s| + |t - s| * (η / 2 * ‖q‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add (by simpa only [Real.norm_eq_abs] using he)
        (mul_le_mul_of_nonneg_left hclose.le (abs_nonneg _))
    _ = _ := by ring

/-- Every curve's nonzero-derivative parameters have a countable cover by pieces
with arbitrarily small slope over genuine Euclidean lines. -/
theorem e2_sb_smallSlopePieces_proof : E2sbSmallSlopePieces := by
  classical
  intro F θ hθ
  let η : ℝ := θ / (2 * (1 + θ))
  have hden : 0 < 2 * (1 + θ) := by positivity
  have hη : 0 < η := div_pos hθ hden
  have hηθ : η ≤ θ * (1 - η) := by
    have he : η * (2 * (1 + θ)) = θ := div_mul_cancel₀ _ hden.ne'
    nlinarith
  obtain ⟨q₀, hq₀⟩ := exists_ne (0 : Plane)
  let : Nonempty {q : Plane // q ≠ 0} := ⟨⟨q₀, hq₀⟩⟩
  let q : ℕ → {q : Plane // q ≠ 0} := TopologicalSpace.denseSeq _
  let c : ℕ → ℝ := TopologicalSpace.denseSeq ℝ
  let r : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hr : ∀ m, 0 < r m := fun m => by dsimp [r]; positivity
  let P : ℕ × ℕ × ℕ → Set ℝ := fun i =>
    {s | dist s (c i.2.2) < r i.2.1 / 2 ∧
      ∀ t : ℝ, dist t s < r i.2.1 →
        ‖F t - F s - (t - s) • (q i.1).val‖ ≤
          η * (|t - s| * ‖(q i.1).val‖)}
  let V : ℕ × ℕ × ℕ → Submodule ℝ Plane := fun i => ℝ ∙ (q i.1).val
  let e : (ℕ × ℕ × ℕ) ≃ ℕ :=
    (Equiv.prodCongr (Equiv.refl ℕ) Nat.pairEquiv).trans Nat.pairEquiv
  refine ⟨P ∘ e.symm, V ∘ e.symm, ?_, ?_, ?_⟩
  · intro i
    exact finrank_span_singleton (q (e.symm i).1).property
  · rintro s ⟨v, hv, hder⟩
    have hopen : IsOpen {u : {q : Plane // q ≠ 0} | ‖v - u.val‖ < η / 2 * ‖u.val‖} :=
      isOpen_lt (continuous_const.sub continuous_subtype_val).norm
        (continuous_const.mul continuous_subtype_val.norm)
    have hne : ({u : {q : Plane // q ≠ 0} | ‖v - u.val‖ < η / 2 * ‖u.val‖} : Set _).Nonempty := by
      refine ⟨⟨v, hv⟩, ?_⟩
      simp only [mem_ofPred_eq, sub_self, norm_zero]
      exact mul_pos (by linarith) (norm_pos_iff.mpr hv)
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq {q : Plane // q ≠ 0}).exists_mem_open hopen hne
    obtain ⟨δ, hδ, happrox⟩ := near_direction_radius F s v (q n).val η (q n).property hη hder hn
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq ℝ) s
      (r m / 2) (by positivity)
    apply mem_iUnion.mpr
    refine ⟨e (n, m, k), ?_⟩
    change s ∈ P (e.symm (e (n, m, k)))
    rw [e.symm_apply_apply]
    exact ⟨hk, fun t ht => happrox t (ht.trans hm)⟩
  · intro i s hs t ht
    change s ∈ P (e.symm i) at hs
    change t ∈ P (e.symm i) at ht
    have hdist : dist t s < r (e.symm i).2.1 := by
      calc
        dist t s ≤ dist t (c (e.symm i).2.2) + dist (c (e.symm i).2.2) s := dist_triangle _ _ _
        _ < r (e.symm i).2.1 / 2 + r (e.symm i).2.1 / 2 := by
          rw [dist_comm (c (e.symm i).2.2) s]
          exact add_lt_add ht.1 hs.1
        _ = _ := by ring
    exact slope_of_linear_error _ _ _ _ _ hθ.le hηθ (hs.2 t hdist)

end ParabolicRectifiability.Examples
