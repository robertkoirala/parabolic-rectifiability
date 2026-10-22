import ParabolicRectifiability.IntegralCanonical.Proofs.Canonical.CanonicalAuxiliaryStatements

/-! # The separation inequality for `H ∩ V`

Proof of `i2_SeparationInequalityStatement`, the auxiliary statement
`i2_separation_inequality`.

Write `p = (x,t)`, `q = (x',t')` for two points of `H ∩ V`, `d = |x - x'|`, `h = √|t - t'|`,
`W = V.direction`, `a = |P_W x - P_W x'|` and `b = |G(z) - G(z')|`, where `p = V.map z` and
`q = V.map z'`. The vertical field gives `L ≥ 0`.
* `ε < 0`: `small_slope` forces `u = u'` in the horizontal domain, so `d = h = 0`.
* `ε ≥ 0`: `h ≤ ε |u - u'| ≤ ε d` (the tangential part of `x - x'` for `H`); the offsets
  cancel under `P_W`, so `a = |z.1 - z'.1|`, and the Lipschitz bound of `G` on `W × Time` gives
  `b ≤ L max(a,h) ≤ L a + L ε d`; with `d ≤ a + b` and `L ε ≤ 1/2`, `d ≤ 2(1+L) a`; finally
  `d_P(p,q) = max(d,h) = d` since `h ≤ ε d ≤ d`.

Helpers carry the prefix `i2_si_`.
-/

noncomputable section

open Set

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

/-- The tangential part of an orthogonal sum is at most the sum (Pythagoras). -/
theorem i2_si_norm_le_norm_add {n : ℕ} (K : Submodule ℝ (Spatial n)) {v w : Spatial n}
    (hv : v ∈ K) (hw : w ∈ Kᗮ) : ‖v‖ ≤ ‖v + w‖ := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (Submodule.inner_right_of_mem_orthogonal hv hw)
  exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _) (by nlinarith [mul_self_nonneg ‖w‖])

/-- The snowflaked time distance of two time coordinates. -/
theorem i2_si_dist_time (t s : ℝ) :
    dist (Metric.Snowflaking.toSnowflaking t : Time) (Metric.Snowflaking.toSnowflaking s) =
      Real.sqrt |t - s| := by
  simp only [Metric.Snowflaking.dist_toSnowflaking_toSnowflaking, dist_eq_norm,
    Real.norm_eq_abs, Real.sqrt_eq_rpow]

/-- Under `P_W`, a vertical graph point `a₀ + u + G(u,s)` projects to `P_W a₀ + u`. -/
theorem i2_si_proj_map {n k : ℕ} {L : ℝ} (V : OrdinaryVerticalGraph n k L)
    (w : SubspaceSpace V.direction) :
    V.direction.orthogonalProjectionOnto
        (V.offset + (w.1 : Spatial n) + (V.function w : Spatial n)) =
      V.direction.orthogonalProjectionOnto V.offset + w.1 := by
  rw [map_add, map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.2 (V.function w).2, add_zero]

/-- **I2-ineq.** `d_P(p,q) ≤ 2(1+L) |P_W p_x - P_W q_x|` on `H ∩ V`. -/
theorem i2_separation_inequality_proof : i2_SeparationInequalityStatement := by
  intro n k _hk2 _hkn L V ε H hε1 hLε p hp q hq
  obtain ⟨L', hG, hL'⟩ := V.lipschitz
  have hL0 : 0 ≤ L := le_trans L'.2 hL'
  simp only [HorizontalGraph.image, OrdinaryVerticalGraph.image, mem_inter_iff, mem_range]
    at hp hq
  obtain ⟨⟨u, rfl⟩, z, hz⟩ := hp
  obtain ⟨⟨u', rfl⟩, z', hz'⟩ := hq
  have hz1 := congrArg Prod.fst hz
  have hz2 := congrArg Prod.snd hz
  have hz1' := congrArg Prod.fst hz'
  have hz2' := congrArg Prod.snd hz'
  simp only [OrdinaryVerticalGraph.map, point] at hz1 hz2 hz1' hz2'
  rw [dist_point]
  simp only [point]
  -- the projection distance is the base distance `a`
  have ha : dist (V.direction.orthogonalProjectionOnto
        (H.offset + (u.val : Spatial n) + (H.normal u : Spatial n)))
      (V.direction.orthogonalProjectionOnto
        (H.offset + (u'.val : Spatial n) + (H.normal u' : Spatial n))) =
      ‖(z.1 : Spatial n) - z'.1‖ := by
    rw [← hz1, ← hz1', i2_si_proj_map, i2_si_proj_map, dist_add_left, Subtype.dist_eq,
      dist_eq_norm]
  rw [ha]
  set d := ‖H.offset + (u.val : Spatial n) + (H.normal u : Spatial n) -
    (H.offset + (u'.val : Spatial n) + (H.normal u' : Spatial n))‖ with hd_def
  set a := ‖(z.1 : Spatial n) - z'.1‖
  set h := Real.sqrt |H.time u - H.time u'|
  have hd0 : 0 ≤ d := norm_nonneg _
  have ha0 : 0 ≤ a := norm_nonneg _
  have hh0 : 0 ≤ h := Real.sqrt_nonneg _
  -- horizontal decomposition of `x - x'`
  have hdiffH : H.offset + (u.val : Spatial n) + (H.normal u : Spatial n) -
      (H.offset + (u'.val : Spatial n) + (H.normal u' : Spatial n)) =
      ((u.val : Spatial n) - u'.val) + ((H.normal u : Spatial n) - H.normal u') := by
    abel
  have hu_le : ‖(u.val : Spatial n) - u'.val‖ ≤ d := by
    rw [hd_def, hdiffH]
    exact i2_si_norm_le_norm_add H.direction (H.direction.sub_mem u.val.2 u'.val.2)
      (Submodule.sub_mem _ (H.normal u).2 (H.normal u').2)
  have hs := H.small_slope u u'
  have hN : ‖(H.normal u : Spatial n) - H.normal u'‖ = ‖H.normal u - H.normal u'‖ := by
    rw [← Submodule.norm_coe, Submodule.coe_sub]
  have hsN : ‖(H.normal u : Spatial n) - H.normal u'‖ ≤ ε * ‖(u.val : Spatial n) - u'.val‖ :=
    by rw [hN]; exact (le_max_left _ _).trans hs
  have hsh : h ≤ ε * ‖(u.val : Spatial n) - u'.val‖ := (le_max_right _ _).trans hs
  have hRHS : 0 ≤ 2 * (1 + L) * a := mul_nonneg (by linarith) ha0
  rcases lt_or_ge ε 0 with hneg | hpos
  · -- `ε < 0`: the horizontal domain is a subsingleton, so `p = q`
    have hΔu0 := norm_nonneg ((u.val : Spatial n) - u'.val)
    have hΔu : ‖(u.val : Spatial n) - u'.val‖ = 0 := le_antisymm (by nlinarith) hΔu0
    have hd : d ≤ 0 := by
      rw [hd_def, hdiffH]
      refine (norm_add_le _ _).trans ?_
      rw [hΔu] at hsN ⊢
      linarith
    rw [hΔu] at hsh
    exact le_trans (max_le hd (by linarith)) hRHS
  · -- `ε ≥ 0`
    have hhd : h ≤ ε * d := hsh.trans (mul_le_mul_of_nonneg_left hu_le hpos)
    have hεd : ε * d ≤ d := by nlinarith
    -- vertical decomposition of `x - x'`
    have hdiffV : H.offset + (u.val : Spatial n) + (H.normal u : Spatial n) -
        (H.offset + (u'.val : Spatial n) + (H.normal u' : Spatial n)) =
        ((z.1 : Spatial n) - z'.1) + ((V.function z : Spatial n) - V.function z') := by
      rw [← hz1, ← hz1']
      abel
    have hdab : d ≤ a + ‖(V.function z : Spatial n) - V.function z'‖ := by
      rw [hd_def, hdiffV]
      exact norm_add_le _ _
    -- the Lipschitz bound of `G` on `W × Time`
    have hzz : dist z z' = max a h := by
      rw [Prod.dist_eq, Subtype.dist_eq, dist_eq_norm, hz2, hz2', i2_si_dist_time]
    have hb : ‖(V.function z : Spatial n) - V.function z'‖ ≤ L * a + L * (ε * d) := by
      have h1 := hG.dist_le_mul z z'
      rw [Subtype.dist_eq, dist_eq_norm, hzz] at h1
      have h2 : max a h ≤ a + ε * d := (max_le_add_of_nonneg ha0 hh0).trans (by linarith)
      have h3 : (L' : ℝ) * max a h ≤ L * (a + ε * d) :=
        mul_le_mul hL' h2 (le_max_of_le_left ha0) hL0
      linarith
    have hLεd : L * (ε * d) ≤ 1 / 2 * d := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hLε hd0
    have hfin : d ≤ 2 * (1 + L) * a := by linarith
    exact max_le hfin (hhd.trans (hεd.trans hfin))

end ParabolicRectifiability.IntegralCanonical
