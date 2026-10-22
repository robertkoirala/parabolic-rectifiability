import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.LastWitness
import ParabolicRectifiability.Measure.Neck.ConstructionCoherence

/-! # The pair bound (`d1d_pairBound`)

Proof of `Forward.Witness.d1d_pairBound_proof : PairBoundStatement`.

`E_{j+1}(w)` is the maximum of the same-level and the adjacent comparison suprema. Each term is
a plane comparison at the **actual pair anchor** (`x_a` for a same-level pair `(a, b)`, `x_b` for
an adjacent pair `(a, b)` of levels `j + 1`, `j`); spatial domination by `pos` puts that anchor
within `20 r_j` of both occurrences, so the hypothesis bounds both comparisons with the test
plane `L` by `√D⁺`, and the triangle inequality for `planeComparison` bounds the term by
`2 √D⁺`. Squaring, `ofReal (2 √D⁺)² ≤ ofReal (4 D)`. Every helper carries the prefix `d1dpair_`.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Witness

/-- Triangle inequality for the plane comparison through a test plane `L`, at a fixed anchor
and a nonnegative radius. -/
theorem d1dpair_planeComparison_triangle {n m : ℕ} (y : Spatial n) {r : ℝ} (hr : 0 ≤ r)
    (L₁ L₂ L : AffineSpatialPlane n m) :
    planeComparison y r L₁ L₂ ≤ planeComparison y r L₁ L + planeComparison y r L₂ L := by
  unfold planeComparison
  have h1 : ‖L₁.linearProjection - L₂.linearProjection‖ ≤
      ‖L₁.linearProjection - L.linearProjection‖ + ‖L₂.linearProjection - L.linearProjection‖ := by
    calc ‖L₁.linearProjection - L₂.linearProjection‖ ≤
          ‖L₁.linearProjection - L.linearProjection‖ +
            ‖L.linearProjection - L₂.linearProjection‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = _ := by rw [norm_sub_rev L.linearProjection]
  have h2 : ‖L₁.projection y - L₂.projection y‖ ≤
      ‖L₁.projection y - L.projection y‖ + ‖L₂.projection y - L.projection y‖ := by
    calc ‖L₁.projection y - L₂.projection y‖ ≤
          ‖L₁.projection y - L.projection y‖ + ‖L.projection y - L₂.projection y‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = _ := by rw [norm_sub_rev (L.projection y)]
  have hinv : 0 ≤ r⁻¹ := inv_nonneg.2 hr
  have h3 := mul_le_mul_of_nonneg_left h2 hinv
  rw [mul_add] at h3
  linarith

/-- A nonnegative real whose square is bounded in `ℝ≥0∞` by `ofReal D` is at most `√D`. -/
theorem d1dpair_le_sqrt_of_ofReal_sq_le {p D : ℝ} (hp : 0 ≤ p)
    (h : ENNReal.ofReal (p ^ 2) ≤ ENNReal.ofReal D) : p ≤ Real.sqrt D := by
  rcases ENNReal.ofReal_le_ofReal_iff'.1 h with h' | h'
  · calc p = Real.sqrt (p ^ 2) := (Real.sqrt_sq hp).symm
      _ ≤ Real.sqrt D := Real.sqrt_le_sqrt h'
  · have : p = 0 := by nlinarith [sq_nonneg p]
    rw [this]
    exact Real.sqrt_nonneg D

/-- A comparison term bounded through the test plane: if both planes are within `√D` of `L` at
the anchor, the term is at most `ofReal (2 √D)`. -/
theorem d1dpair_term_le {n m : ℕ} (y : Spatial n) {r : ℝ} (hr : 0 < r)
    (L₁ L₂ L : AffineSpatialPlane n m) (D : ℝ)
    (h₁ : ENNReal.ofReal (planeComparison y r L₁ L ^ 2) ≤ ENNReal.ofReal D)
    (h₂ : ENNReal.ofReal (planeComparison y r L₂ L ^ 2) ≤ ENNReal.ofReal D) :
    ENNReal.ofReal (planeComparison y r L₁ L₂) ≤ ENNReal.ofReal (2 * Real.sqrt D) := by
  apply ENNReal.ofReal_le_ofReal
  have e₁ := d1dpair_le_sqrt_of_ofReal_sq_le (planeComparison_nonneg hr L₁ L) h₁
  have e₂ := d1dpair_le_sqrt_of_ofReal_sq_le (planeComparison_nonneg hr L₂ L) h₂
  have t := d1dpair_planeComparison_triangle y hr.le L₁ L₂ L
  linarith

/-- The final squaring: `ofReal (2 √D)² ≤ ofReal (4 D)`. -/
theorem d1dpair_sq_le (D : ℝ) :
    ENNReal.ofReal (2 * Real.sqrt D) ^ 2 ≤ ENNReal.ofReal (4 * D) := by
  rw [← ENNReal.ofReal_pow (by positivity)]
  rcases le_or_gt 0 D with hD | hD
  · apply le_of_eq
    congr 1
    rw [mul_pow, Real.sq_sqrt hD]
    norm_num
  · rw [Real.sqrt_eq_zero'.2 hD.le]
    simp

/-- **The pair bound** (`PairBoundStatement`). -/
theorem d1d_pairBound_proof : PairBoundStatement := by
  intro n m ι W _ pos F L D j w hpos hD
  have hr : 0 < F.scale j := by
    unfold CoherentFamily.scale coherentScale
    exact div_pos F.initialRadius_pos (pow_pos (by norm_num) j)
  have hbound : F.comparisonEnergy pos (j + 1) w ≤ ENNReal.ofReal (2 * Real.sqrt D) := by
    simp only [CoherentFamily.comparisonEnergy]
    refine max_le ?_ ?_
    · -- same-level pairs, anchored at `x_{j,a}`
      unfold CoherentFamily.sameLevelComparisonTerm
      refine iSup₂_le fun a ha => iSup₂_le fun b hb => iSup_le fun hab => ?_
      obtain ⟨hab, haw, hbw⟩ := hab
      have hsa := hD j (Or.inl rfl) a ha haw (F.center j a).1 (by
        rw [sub_self, norm_zero]
        exact mul_nonneg (by norm_num) hr.le)
      have hsb := hD j (Or.inl rfl) b hb hbw (F.center j a).1
        (le_trans (hpos (F.center j a) (F.center j b)) hab)
      exact d1dpair_term_le _ hr _ _ L D hsa hsb
    · -- adjacent pairs, anchored at `x_{j,b}`
      unfold CoherentFamily.adjacentComparisonTerm
      refine iSup₂_le fun a ha => iSup₂_le fun b hb => iSup_le fun hab => ?_
      obtain ⟨hab, haw, hbw⟩ := hab
      have hsa := hD (j + 1) (Or.inr rfl) a ha haw (F.center j b).1
        (le_trans (hpos (F.center j b) (F.center (j + 1) a)) (by rw [dist_comm]; exact hab))
      have hsb := hD j (Or.inl rfl) b hb hbw (F.center j b).1 (by
        rw [sub_self, norm_zero]
        exact mul_nonneg (by norm_num) hr.le)
      exact d1dpair_term_le _ hr _ _ L D hsa hsb
  calc F.comparisonEnergy pos (j + 1) w ^ 2 ≤ ENNReal.ofReal (2 * Real.sqrt D) ^ 2 :=
        pow_le_pow_left₀ zero_le hbound 2
    _ ≤ ENNReal.ofReal (4 * D) := d1dpair_sq_le D

end Witness

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
