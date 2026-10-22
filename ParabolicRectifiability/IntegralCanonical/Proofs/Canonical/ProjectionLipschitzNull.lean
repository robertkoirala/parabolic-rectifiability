import ParabolicRectifiability.IntegralCanonical.Proofs.Canonical.CanonicalAuxiliaryStatements

/-! # Projection-Lipschitz sets are `H_P^k`-null

Proof of `i2_ProjectionLipschitzNullStatement`, the auxiliary statement
`i2_projection_lipschitz_null`.

Route. Let `P p = P_W p_x`, a map from `Space n`
with its parabolic metric to `↥W` with the Euclidean metric inherited from `Spatial n`, and
`f = Function.invFunOn P S`.
1. For `y = P p ∈ P '' S`, `f y ∈ S` and `P (f y) = y`. The hypothesis gives
   `d_P(f y, f y') ≤ C |y - y'| ≤ C⁺ |y - y'|`, so `f` is `C⁺`-Lipschitz on `P '' S`
   (`LipschitzOnWith.of_dist_le'`, constant `Real.toNNReal C`).
2. For `p ∈ S`, `d_P(p, f (P p)) ≤ C |P p - P p| = 0`, so `p = f (P p)` and `S ⊆ f '' (P '' S)`.
3. `dimH S ≤ dimH (f '' (P '' S)) ≤ dimH (P '' S) ≤ dimH (univ : Set W) = dim W = k - 2 < k`
   (`dimH_mono`, `LipschitzOnWith.dimH_image_le`, `Real.dimH_univ_eq_finrank`). The dimension of
   `S` is taken in the parabolic metric of `Space n`, the metric of `hausdorffP` (`hausdorffP_eq`).
4. `μH[k] S = 0` (`hausdorffMeasure_of_dimH_lt`), i.e. `hausdorffP n k S = 0`.

The case `C < 0` (subsingleton `S`, `hausdorffP_singleton`) needs no separate treatment:
the bound `C ≤ C⁺` makes steps 1-4 valid for every real `C` (for `C ≤ 0`, `f` is `0`-Lipschitz).
Outer measure only; no measurability of `S` is used. Empty `S` is split off first
(`dimH_empty`), since `Function.invFunOn` needs `Nonempty X`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.IntegralCanonical

/-- A set on which the distance is bounded by `C` times the distance of the images under a map
`P` into a finite-dimensional real normed space `E` has Hausdorff dimension at most `dim E`,
for every real `C`. -/
theorem i2_pn_dimH_le {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (P : X → E) (S : Set X) (C : ℝ)
    (h : ∀ p ∈ S, ∀ q ∈ S, dist p q ≤ C * dist (P p) (P q)) :
    dimH S ≤ (Module.finrank ℝ E : ℝ≥0∞) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, -⟩
  · rw [dimH_empty]
    exact bot_le
  have : Nonempty X := ⟨p₀⟩
  set f := Function.invFunOn P S with hf
  have hfS : ∀ y ∈ P '' S, f y ∈ S ∧ P (f y) = y := by
    rintro y ⟨p, hp, rfl⟩
    exact Function.invFunOn_pos ⟨p, hp, rfl⟩
  have hlip : LipschitzOnWith (Real.toNNReal C) f (P '' S) := by
    refine LipschitzOnWith.of_dist_le' fun y hy y' hy' => ?_
    obtain ⟨h1, h2⟩ := hfS y hy
    obtain ⟨h1', h2'⟩ := hfS y' hy'
    calc dist (f y) (f y') ≤ C * dist (P (f y)) (P (f y')) := h _ h1 _ h1'
      _ = C * dist y y' := by rw [h2, h2']
  have hsub : S ⊆ f '' (P '' S) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hfS (P p) ⟨p, hp, rfl⟩
    refine ⟨P p, ⟨p, hp, rfl⟩, ?_⟩
    have hle : dist p (f (P p)) ≤ 0 := by
      have := h p hp _ h1
      rwa [h2, dist_self, mul_zero] at this
    exact (dist_le_zero.mp hle).symm
  calc dimH S ≤ dimH (f '' (P '' S)) := dimH_mono hsub
    _ ≤ dimH (P '' S) := hlip.dimH_image_le
    _ ≤ dimH (univ : Set E) := dimH_mono (subset_univ _)
    _ = Module.finrank ℝ E := Real.dimH_univ_eq_finrank E

/-- **Null sets under Lipschitz projection.** A set `S ⊆ X` on which `d_P(p,q) ≤ C |P_W p_x - P_W q_x|` for a subspace
`W` of dimension `k - 2` is `H_P^k`-null, for every real `C`. -/
theorem i2_projection_lipschitz_null_proof : i2_ProjectionLipschitzNullStatement := by
  intro n k W hk S C h
  have hdim : dimH S ≤ (Module.finrank ℝ W : ℝ≥0∞) :=
    i2_pn_dimH_le (fun p : Space n => W.orthogonalProjectionOnto p.1) S C h
  have hlt : dimH S < ((k : ℝ≥0) : ℝ≥0∞) := by
    refine lt_of_le_of_lt hdim ?_
    rw [ENNReal.coe_natCast]
    exact_mod_cast (by omega : Module.finrank ℝ W < k)
  have h0 := hausdorffMeasure_of_dimH_lt hlt
  rw [NNReal.coe_natCast] at h0
  rw [hausdorffP_eq]
  exact h0

end ParabolicRectifiability.IntegralCanonical
