import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # The same-level plane comparison (`d1c_sameLevel`)

This module proves `d1c_sameLevel_proof`, in implication form:

`LocalErrorStatement → PartitionEnergy.PlaneComparisonStatement → SameLevelStatement`.

Route, with `p = k + 2`, `K = (2000 Λ)^p` and the constants `C, e₀` of the plane comparison at
`(n, k, A)`: `Λ₀ = 4000` (the local error), `B = 1000`, and
`b₀ = min(e₀ 5^p / K, η² 5^p / (50 C K))`.
For admissible `g, g'` of one level `j ≥ 1` with `d_P(g, g') ≤ 20 r_j`:
* the comparison ball is `P(g, s)` with `s = 5 r_j`; its buffer `P(g, 4s) = P(g, 20 r_j)` lies in
  `P(a, 1000 R)` because `d_P(g, a) < 5R` (forest root cell) and `r_j ≤ 48 ℓ_* ≤ 48 R`;
* the horizontal small-error hypothesis is the local fit itself:
  `fit μ Π_g g (2s) ≤ fit μ Π_g g (40 r_j) ≤ K b r_j^p ≤ e₀ s^p`;
* the two dominating measures are `μ⌞P(g, 40 r_j)` and `μ⌞P(g', 40 r_j)`, both `≥ μ⌞P(g, 5 r_j)`;
  for each, the spatial fitting integral of the fitted plane is at most the full-model fit
  (`dist(x, L_M) ≤ d_P(·, M)` pointwise), hence at most `K b r_j^p` (local error);
* so `d_{x_g, s}(L_g, L_{g'})² ≤ (C / s^p) 2 K b r_j^p = 2 C K b / 5^p ≤ η² / 25`, and the radius
  change `s → r_j` costs the factor `5`: `d_{x_g, r_j} ≤ 5 d_{x_g, 5 r_j} ≤ η`.

Both inputs enter only as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section SameHelpers

variable {n : ℕ}

/-- The spatial distance to a plane is at most the parabolic distance to any lower model set
on it. -/
theorem d1csame_spatial_sq_le_lower (T : NeckType) {m : ℕ} (L : AffineSpatialPlane n m)
    (τ : ℝ) (z : Space n) :
    ENNReal.ofReal (‖z.1 - L.projection z.1‖ ^ 2) ≤
      Metric.infEDist z (T.lowerModelSet L τ) ^ 2 := by
  have h : ENNReal.ofReal ‖z.1 - L.projection z.1‖ ≤
      Metric.infEDist z (T.lowerModelSet L τ) := by
    refine Metric.le_infEDist.2 fun y hy => ?_
    have hy1 : y.1 ∈ L.toSet := by
      cases T with
      | horizontal => exact (show y.1 ∈ L.toSet ∧ y.2.val = τ from hy).1
      | vertical => exact (show y.1 ∈ L.toSet from hy)
    have hzy : ‖z.1 - y.1‖ ≤ dist z y := by
      rw [← dist_eq_norm, Prod.dist_eq]
      exact le_max_left _ _
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal ((L.nearest z.1 hy1).trans hzy)
  rw [ENNReal.ofReal_pow (norm_nonneg _)]
  gcongr

/-- The squared spatial distance to the plane of a model is at most its model cost. -/
theorem d1csame_spatial_le_modelCost {k : ℕ} (T : NeckType) (M : Models n k T.toFamilyKind)
    (z : Space n) :
    ENNReal.ofReal (‖z.1 - (NeckSelection.modelPlane T M).projection z.1‖ ^ 2) ≤
      modelCost M z := by
  have h := d1csame_spatial_sq_le_lower T (NeckSelection.modelPlane T M)
    (NeckSelection.modelTime T M) z
  rw [NeckSelection.lowerModelSet_modelPlane] at h
  exact h

/-- The spatial fitting integral of a model's plane on `μ⌞P(g, r)` is at most the model's fit. -/
theorem d1csame_spatialFit_le_fit {k : ℕ} (μ : Measure (Space n)) (T : NeckType)
    (M : Models n k T.toFamilyKind) (g : Space n) (r : ℝ) :
    spatialFittingIntegral (μ.restrict (Metric.ball g r)) (NeckSelection.modelPlane T M) ≤
      fit μ M g r := by
  unfold spatialFittingIntegral fit
  exact lintegral_mono fun z => d1csame_spatial_le_modelCost T M z

/-- The fit is monotone in the radius. -/
theorem d1csame_fit_mono {k : ℕ} {F : FamilyKind} (μ : Measure (Space n)) (M : Models n k F)
    (g : Space n) {r s : ℝ} (h : r ≤ s) : fit μ M g r ≤ fit μ M g s := by
  unfold fit
  exact lintegral_mono_set (Metric.ball_subset_ball h)

/-- The plane comparison is nonnegative at a nonnegative radius. -/
theorem d1csame_planeComparison_nonneg {m : ℕ} (x : Spatial n) {r : ℝ} (hr : 0 ≤ r)
    (L L' : AffineSpatialPlane n m) : 0 ≤ planeComparison x r L L' := by
  unfold planeComparison
  exact add_nonneg (norm_nonneg _) (mul_nonneg (inv_nonneg.2 hr) (norm_nonneg _))

/-- Radius change `5r → r` in the plane comparison costs the factor `5`. -/
theorem d1csame_planeComparison_le_five {m : ℕ} (x : Spatial n) (r : ℝ)
    (L L' : AffineSpatialPlane n m) :
    planeComparison x r L L' ≤ 5 * planeComparison x (5 * r) L L' := by
  unfold planeComparison
  have ha := norm_nonneg (L.linearProjection - L'.linearProjection)
  have hinv : (5 * r)⁻¹ = r⁻¹ / 5 := by
    rw [mul_inv]
    ring
  rw [hinv]
  have hexp : 5 * (‖L.linearProjection - L'.linearProjection‖ +
      r⁻¹ / 5 * ‖L.projection x - L'.projection x‖) =
      5 * ‖L.linearProjection - L'.linearProjection‖ +
        r⁻¹ * ‖L.projection x - L'.projection x‖ := by ring
  rw [hexp]
  linarith

variable {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The root cell lies in the partitioned set. -/
theorem d1csame_rootCell_subset (𝒢 : GoodRegion P μ k Λ b) : 𝒢.rootCell ⊆ E := by
  intro x hx
  rw [← P.cell_cover 𝒢.root.1]
  exact Set.mem_biUnion (t := fun z => P.cell 𝒢.root.1 z)
    (show 𝒢.root.2 ∈ P.center 𝒢.root.1 from 𝒢.root_isCell)
    (show x ∈ P.cell 𝒢.root.1 𝒢.root.2 from hx)

/-- The construction scales are positive. -/
theorem d1csame_stageScale_pos (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) : 0 < stageScale 𝒢 j := by
  unfold stageScale coherentScale
  have := d1c_rootScale_pos 𝒢
  positivity

/-- `r_j ≤ r_0 = 48 ℓ_*`. -/
theorem d1csame_stageScale_le (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    stageScale 𝒢 j ≤ 48 * 𝒢.rootScale := by
  unfold stageScale coherentScale
  have := d1c_rootScale_pos 𝒢
  exact div_le_self (by linarith) (one_le_pow₀ (by norm_num))

end SameHelpers

section SameForest

variable {n : ℕ} {E : Set (Space n)} {R : ℝ} {P : DirectPartition E R} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The root side is at most the top scale `R`. -/
theorem d1csame_rootScale_le (𝒢 : GoodRegion P μ k Λ b) : 𝒢.rootScale ≤ R := by
  unfold GoodRegion.rootScale DirectPartition.scale coherentScale
  exact div_le_self P.scale_pos.le (one_le_pow₀ (by norm_num))

/-- A point of the root cell of a forest region lies within `5R` of `a`. -/
theorem d1csame_dist_lt (𝒢 : GoodRegion P μ k Λ b) {a : Space n}
    (hfor : P.InForest a R 𝒢.root) {g : Space n} (hg : g ∈ 𝒢.rootCell) : dist g a < 5 * R := by
  obtain ⟨z₀, hz₀, ⟨w, hw0, hwa⟩, hbelow⟩ := hfor
  have hball := P.cell_subset_ball 0 z₀ hz₀
  have hgc : g ∈ P.cell 0 z₀ := hbelow.2.2 hg
  have h1 : dist g z₀ < 2 * coherentScale R 0 := hball hgc
  have h2 : dist w z₀ < 2 * coherentScale R 0 := hball hw0
  have hc : coherentScale R 0 = R := by
    unfold coherentScale
    rw [pow_zero, div_one]
  rw [hc] at h1 h2
  have h3 : dist w a < R := hwa
  calc dist g a ≤ dist g z₀ + dist z₀ w + dist w a := dist_triangle4 g z₀ w a
    _ = dist g z₀ + dist w z₀ + dist w a := by rw [dist_comm z₀ w]
    _ < 5 * R := by linarith

end SameForest

/-- **Same-level plane comparison** (`d1c_sameLevel`): same-level comparison of two admissible
occurrences of one level within `20 r_j`, from the local error and the same-source plane
comparison (both as hypotheses). -/
theorem d1c_sameLevel_proof :
    LocalErrorStatement → PartitionEnergy.PlaneComparisonStatement → SameLevelStatement := by
  intro hLE hPC n hn k hk hkn A hA
  obtain ⟨Cc, hCc, e₀, he₀, hPC⟩ := hPC n hn k hk hkn A hA
  refine ⟨4000, by norm_num, fun Λ hΛ => ⟨1000, by norm_num, fun η hη => ?_⟩⟩
  have hK : 0 < (2000 * Λ) ^ (k + 2) := pow_pos (by linarith) _
  have h5 : (0 : ℝ) < 5 ^ (k + 2) := pow_pos (by norm_num) _
  have hCK : 0 < 50 * Cc * (2000 * Λ) ^ (k + 2) := mul_pos (mul_pos (by norm_num) hCc) hK
  refine ⟨min (e₀ * 5 ^ (k + 2) / (2000 * Λ) ^ (k + 2))
      (η ^ 2 * 5 ^ (k + 2) / (50 * Cc * (2000 * Λ) ^ (k + 2))),
    lt_min (div_pos (mul_pos he₀ h5) hK) (div_pos (mul_pos (pow_pos hη 2) h5) hCK), ?_⟩
  intro b hb hbb μ hfin hreg a ha R hR hADR P 𝒢 hfor fits j g g' hj hg hg' hgg'
  have hr : 0 < stageScale 𝒢 j := d1csame_stageScale_pos 𝒢 j
  have hrR : stageScale 𝒢 j ≤ 48 * R := by
    have h1 := d1csame_stageScale_le 𝒢 j
    have h2 := d1csame_rootScale_le 𝒢
    linarith
  have hrp : 0 < stageScale 𝒢 j ^ (k + 2) := pow_pos hr _
  -- the buffer of the comparison ball `P(g, 5 r_j)`
  have hga : dist g a < 5 * R := d1csame_dist_lt 𝒢 hfor hg.1
  have hball : Metric.ball g (4 * (5 * stageScale 𝒢 j)) ⊆ Metric.ball a (1000 * R) :=
    Metric.ball_subset_ball' (by linarith)
  have h4 : 4 * (5 * stageScale 𝒢 j) ≤ 1000 * R := by linarith
  -- the local errors at `g` and `g'`
  have hloc : ∀ x, Admissible 𝒢 j x →
      fit μ (fits.model j x) x (40 * stageScale 𝒢 j) ≤
        ENNReal.ofReal ((2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 j ^ (k + 2)) :=
    fun x hx => hLE n μ.support R P μ k Λ b 𝒢 fits hΛ j x hx
  have hb1 : b ≤ e₀ * 5 ^ (k + 2) / (2000 * Λ) ^ (k + 2) := hbb.trans (min_le_left _ _)
  have hb2 : b ≤ η ^ 2 * 5 ^ (k + 2) / (50 * Cc * (2000 * Λ) ^ (k + 2)) :=
    hbb.trans (min_le_right _ _)
  have hKb : b * (2000 * Λ) ^ (k + 2) ≤ e₀ * 5 ^ (k + 2) := (le_div_iff₀ hK).1 hb1
  -- the horizontal small-error hypothesis, from the local fit at `g`
  have hhor : 𝒢.type = .horizontal → ∃ M : Models n k 𝒢.type.toFamilyKind,
      fit μ M g (2 * (5 * stageScale 𝒢 j)) ≤
        ENNReal.ofReal (e₀ * (5 * stageScale 𝒢 j) ^ (k + 2)) := by
    intro _
    refine ⟨fits.model j g, (d1csame_fit_mono μ _ g (by linarith)).trans
      ((hloc g hg).trans (ENNReal.ofReal_le_ofReal ?_))⟩
    calc (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 j ^ (k + 2)
        = b * (2000 * Λ) ^ (k + 2) * stageScale 𝒢 j ^ (k + 2) := by ring
      _ ≤ e₀ * 5 ^ (k + 2) * stageScale 𝒢 j ^ (k + 2) :=
          mul_le_mul_of_nonneg_right hKb hrp.le
      _ = e₀ * (5 * stageScale 𝒢 j) ^ (k + 2) := by
          rw [mul_pow (5 : ℝ) (stageScale 𝒢 j) (k + 2)]; ring
  -- the common source `μ⌞P(g, 5 r_j)` lies in both fitting balls
  have hsub1 : Metric.ball g (5 * stageScale 𝒢 j) ⊆ Metric.ball g (40 * stageScale 𝒢 j) :=
    Metric.ball_subset_ball (by linarith)
  have hsub2 : Metric.ball g (5 * stageScale 𝒢 j) ⊆ Metric.ball g' (40 * stageScale 𝒢 j) :=
    Metric.ball_subset_ball' (by linarith)
  have hcmp := hPC 𝒢.type 𝒢.type_available μ a (1000 * R) hADR g
    (d1csame_rootCell_subset 𝒢 hg.1) (5 * stageScale 𝒢 j) (by linarith) hball h4 hhor
    (NeckSelection.modelPlane 𝒢.type (fits.model j g))
    (NeckSelection.modelPlane 𝒢.type (fits.model j g'))
    (μ.restrict (Metric.ball g (40 * stageScale 𝒢 j)))
    (μ.restrict (Metric.ball g' (40 * stageScale 𝒢 j)))
    (Measure.restrict_mono hsub1 le_rfl) (Measure.restrict_mono hsub2 le_rfl)
  have hS1 := (d1csame_spatialFit_le_fit μ 𝒢.type (fits.model j g) g
    (40 * stageScale 𝒢 j)).trans (hloc g hg)
  have hS2 := (d1csame_spatialFit_le_fit μ 𝒢.type (fits.model j g') g'
    (40 * stageScale 𝒢 j)).trans (hloc g' hg')
  have hX : 0 ≤ (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 j ^ (k + 2) :=
    (mul_pos (mul_pos hK hb) hrp).le
  have hCr : 0 ≤ Cc / (5 * stageScale 𝒢 j) ^ (k + 2) :=
    div_nonneg hCc.le (pow_pos (by linarith) _).le
  have hsum := add_le_add hS1 hS2
  rw [← ENNReal.ofReal_add hX hX] at hsum
  have hmain := hcmp.trans (mul_le_mul' le_rfl hsum)
  rw [← ENNReal.ofReal_mul hCr,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCr (add_nonneg hX hX))] at hmain
  -- arithmetic: `d_{x_g, 5 r_j}² ≤ 2 C K b / 5^p ≤ η² / 25`
  have hsimp : Cc / (5 * stageScale 𝒢 j) ^ (k + 2) *
      ((2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 j ^ (k + 2) +
        (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 j ^ (k + 2)) =
      2 * Cc * (2000 * Λ) ^ (k + 2) * b / 5 ^ (k + 2) := by
    rw [mul_pow (5 : ℝ) (stageScale 𝒢 j) (k + 2), div_mul_eq_mul_div, div_eq_div_iff (mul_pos h5 hrp).ne' h5.ne']
    ring
  rw [hsimp] at hmain
  have hb2' : b * (50 * Cc * (2000 * Λ) ^ (k + 2)) ≤ η ^ 2 * 5 ^ (k + 2) :=
    (le_div_iff₀ hCK).1 hb2
  have h25 : 25 * (2 * Cc * (2000 * Λ) ^ (k + 2) * b / 5 ^ (k + 2)) ≤ η ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ h5]
    calc 25 * (2 * Cc * (2000 * Λ) ^ (k + 2) * b)
        = b * (50 * Cc * (2000 * Λ) ^ (k + 2)) := by ring
      _ ≤ η ^ 2 * 5 ^ (k + 2) := hb2'
  set L₁ := NeckSelection.modelPlane 𝒢.type (fits.model j g)
  set L₂ := NeckSelection.modelPlane 𝒢.type (fits.model j g')
  have hpc5 := d1csame_planeComparison_nonneg g.1 (by linarith : 0 ≤ 5 * stageScale 𝒢 j) L₁ L₂
  have hsq : (5 * planeComparison g.1 (5 * stageScale 𝒢 j) L₁ L₂) ^ 2 ≤ η ^ 2 := by
    calc (5 * planeComparison g.1 (5 * stageScale 𝒢 j) L₁ L₂) ^ 2
        = 25 * planeComparison g.1 (5 * stageScale 𝒢 j) L₁ L₂ ^ 2 := by ring
      _ ≤ 25 * (2 * Cc * (2000 * Λ) ^ (k + 2) * b / 5 ^ (k + 2)) :=
          mul_le_mul_of_nonneg_left hmain (by norm_num)
      _ ≤ η ^ 2 := h25
  have h5pc : 5 * planeComparison g.1 (5 * stageScale 𝒢 j) L₁ L₂ ≤ η :=
    (pow_le_pow_iff_left₀ (by linarith) hη.le two_ne_zero).1 hsq
  exact (d1csame_planeComparison_le_five g.1 (stageScale 𝒢 j) L₁ L₂).trans h5pc

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
