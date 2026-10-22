import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # The adjacent-level plane comparison (`d1c_adjacentLevel`)

This module proves `d1c_adjacentLevel_proof`, in implication form:

`LocalErrorStatement → PartitionEnergy.PlaneComparisonStatement → AdjacentLevelStatement`.

Route, with `p = k + 2`, `K = (2000 Λ)^p` and the constants `C, e₀` of the plane comparison at
`(n, k, A)`: `Λ₀ = 4000` (the local error), `B = 1000`, and
`b₀ = min(e₀ 5^p / K, η² 5^p / (968 C K 10^p))`.
For an admissible child `g` of level `j + 1`, an admissible `g'` of level `j ≥ 1` and
`d_P(g, g') ≤ 20 r_j`, write `r' = r_{j+1}`, so `r_j = 10 r'`:
* the comparison ball is the child-centred `P(g, s)`, `s = 5 r'`; its buffer `P(g, 20 r')` lies in
  `P(a, 1000 R)` (`d_P(g, a) < 5R`, `r' ≤ 48 R`);
* the horizontal small-error hypothesis is the child's local fit:
  `fit μ Π_g g (2s) ≤ fit μ Π_g g (40 r') ≤ K b r'^p ≤ e₀ s^p`;
* the dominating measures are `μ⌞P(g, 40 r')` and `μ⌞P(g', 40 r_j)`; both contain
  `μ⌞P(g, 5 r')` because `5 r' + 200 r' ≤ 400 r'`;
* the spatial fitting integrals are at most `K b r'^p` and `K b r_j^p = 10^p K b r'^p` (local
  errors at the two levels), so `d_{x_g, s}(L_g, L_{g'})² ≤ C K b (1 + 10^p) / 5^p`;
* anchor change `x_g → x_{g'}` (`‖x_{g'} - x_g‖ ≤ 200 r' = 40 s`) and radius change `s → r_j`
  (`affineComparison_change_anchor_radius`, factor `1 + 41 s / r_j = 43/2 ≤ 22`), and
  `484 C K b (1 + 10^p) / 5^p ≤ η²`.

Both inputs enter only as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section AdjHelpers

variable {n : ℕ}

/-- The spatial distance to a plane is at most the parabolic distance to any lower model set
on it. -/
theorem d1cadj_spatial_sq_le_lower (T : NeckType) {m : ℕ} (L : AffineSpatialPlane n m)
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
theorem d1cadj_spatial_le_modelCost {k : ℕ} (T : NeckType) (M : Models n k T.toFamilyKind)
    (z : Space n) :
    ENNReal.ofReal (‖z.1 - (NeckSelection.modelPlane T M).projection z.1‖ ^ 2) ≤
      modelCost M z := by
  have h := d1cadj_spatial_sq_le_lower T (NeckSelection.modelPlane T M)
    (NeckSelection.modelTime T M) z
  rw [NeckSelection.lowerModelSet_modelPlane] at h
  exact h

/-- The spatial fitting integral of a model's plane on `μ⌞P(g, r)` is at most the model's fit. -/
theorem d1cadj_spatialFit_le_fit {k : ℕ} (μ : Measure (Space n)) (T : NeckType)
    (M : Models n k T.toFamilyKind) (g : Space n) (r : ℝ) :
    spatialFittingIntegral (μ.restrict (Metric.ball g r)) (NeckSelection.modelPlane T M) ≤
      fit μ M g r := by
  unfold spatialFittingIntegral fit
  exact lintegral_mono fun z => d1cadj_spatial_le_modelCost T M z

/-- The fit is monotone in the radius. -/
theorem d1cadj_fit_mono {k : ℕ} {F : FamilyKind} (μ : Measure (Space n)) (M : Models n k F)
    (g : Space n) {r s : ℝ} (h : r ≤ s) : fit μ M g r ≤ fit μ M g s := by
  unfold fit
  exact lintegral_mono_set (Metric.ball_subset_ball h)

/-- Passage from the extended comparison inequality to a real one. -/
theorem d1cadj_real_of_ennreal {x Cr X₁ X₂ : ℝ} (hCr : 0 ≤ Cr) (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    {S₁ S₂ : ℝ≥0∞} (h : ENNReal.ofReal x ≤ ENNReal.ofReal Cr * (S₁ + S₂))
    (h₁ : S₁ ≤ ENNReal.ofReal X₁) (h₂ : S₂ ≤ ENNReal.ofReal X₂) : x ≤ Cr * (X₁ + X₂) := by
  have h' := h.trans (mul_le_mul' le_rfl (add_le_add h₁ h₂))
  rw [← ENNReal.ofReal_add hX₁ hX₂, ← ENNReal.ofReal_mul hCr,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCr (add_nonneg hX₁ hX₂))] at h'
  exact h'

variable {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The root cell lies in the partitioned set. -/
theorem d1cadj_rootCell_subset (𝒢 : GoodRegion P μ k Λ b) : 𝒢.rootCell ⊆ E := by
  intro x hx
  rw [← P.cell_cover 𝒢.root.1]
  exact Set.mem_biUnion (t := fun z => P.cell 𝒢.root.1 z)
    (show 𝒢.root.2 ∈ P.center 𝒢.root.1 from 𝒢.root_isCell)
    (show x ∈ P.cell 𝒢.root.1 𝒢.root.2 from hx)

/-- The construction scales are positive. -/
theorem d1cadj_stageScale_pos (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) : 0 < stageScale 𝒢 j := by
  unfold stageScale coherentScale
  have := d1c_rootScale_pos 𝒢
  positivity

/-- `r_j ≤ r_0 = 48 ℓ_*`. -/
theorem d1cadj_stageScale_le (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    stageScale 𝒢 j ≤ 48 * 𝒢.rootScale := by
  unfold stageScale coherentScale
  have := d1c_rootScale_pos 𝒢
  exact div_le_self (by linarith) (one_le_pow₀ (by norm_num))

/-- `r_j = 10 r_{j+1}`. -/
theorem d1cadj_stageScale_succ (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    stageScale 𝒢 j = 10 * stageScale 𝒢 (j + 1) := by
  unfold stageScale coherentScale
  have h : (10 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [pow_succ]
  field_simp

end AdjHelpers

section AdjForest

variable {n : ℕ} {E : Set (Space n)} {R : ℝ} {P : DirectPartition E R} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The root side is at most the top scale `R`. -/
theorem d1cadj_rootScale_le (𝒢 : GoodRegion P μ k Λ b) : 𝒢.rootScale ≤ R := by
  unfold GoodRegion.rootScale DirectPartition.scale coherentScale
  exact div_le_self P.scale_pos.le (one_le_pow₀ (by norm_num))

/-- A point of the root cell of a forest region lies within `5R` of `a`. -/
theorem d1cadj_dist_lt (𝒢 : GoodRegion P μ k Λ b) {a : Space n}
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

end AdjForest

/-- The arithmetic of the adjacent comparison: from the squared comparison at the child's
radius `5 r'`, the anchor and radius change to `(x_{g'}, 10 r')` gives tolerance `η`. -/
theorem d1cadj_final {n m : ℕ} (L₁ L₂ : AffineSpatialPlane n m) (x y : Spatial n)
    {r' X η : ℝ} (hr' : 0 < r') (hη : 0 < η) (hxy : ‖y - x‖ ≤ 40 * (5 * r'))
    (hsq : planeComparison x (5 * r') L₁ L₂ ^ 2 ≤ X) (hX : 484 * X ≤ η ^ 2) :
    planeComparison y (10 * r') L₁ L₂ ≤ η := by
  have hs : 0 < 5 * r' := by linarith
  have hr : 0 < 10 * r' := by linarith
  have hch := affineComparison_change_anchor_radius L₁ L₂ x y (5 * r') (10 * r') 40 hs hr
    (by norm_num) hxy
  have hfac : 1 + (40 + 1) * (5 * r') / (10 * r') = 43 / 2 := by
    field_simp
    ring
  rw [hfac] at hch
  have hpc0 : 0 ≤ planeComparison x (5 * r') L₁ L₂ := affineComparison_nonneg L₁ L₂ x hs.le
  have h22 : (22 * planeComparison x (5 * r') L₁ L₂) ^ 2 ≤ η ^ 2 := by
    calc (22 * planeComparison x (5 * r') L₁ L₂) ^ 2
        = 484 * planeComparison x (5 * r') L₁ L₂ ^ 2 := by ring
      _ ≤ 484 * X := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ ≤ η ^ 2 := hX
  have h22' : 22 * planeComparison x (5 * r') L₁ L₂ ≤ η :=
    (pow_le_pow_iff_left₀ (by linarith) hη.le two_ne_zero).1 h22
  calc planeComparison y (10 * r') L₁ L₂ = affineComparison L₁ L₂ y (10 * r') := rfl
    _ ≤ 43 / 2 * affineComparison L₁ L₂ x (5 * r') := hch
    _ = 43 / 2 * planeComparison x (5 * r') L₁ L₂ := rfl
    _ ≤ 22 * planeComparison x (5 * r') L₁ L₂ := by linarith
    _ ≤ η := h22'

/-- **Adjacent-level comparison** (`d1c_adjacentLevel`): adjacent comparison of an admissible child of
level `j + 1` and an admissible occurrence of level `j ≥ 1` within `20 r_j`, anchored at the
preceding occurrence, from the local error and the same-source plane comparison (both as
hypotheses). -/
theorem d1c_adjacentLevel_proof :
    LocalErrorStatement → PartitionEnergy.PlaneComparisonStatement →
      AdjacentLevelStatement := by
  intro hLE hPC n hn k hk hkn A hA
  obtain ⟨Cc, hCc, e₀, he₀, hPC⟩ := hPC n hn k hk hkn A hA
  refine ⟨4000, by norm_num, fun Λ hΛ => ⟨1000, by norm_num, fun η hη => ?_⟩⟩
  have hK : 0 < (2000 * Λ) ^ (k + 2) := pow_pos (by linarith) _
  have h5 : (0 : ℝ) < 5 ^ (k + 2) := pow_pos (by norm_num) _
  have h10 : (0 : ℝ) < 10 ^ (k + 2) := pow_pos (by norm_num) _
  have hCK : 0 < 968 * Cc * (2000 * Λ) ^ (k + 2) * 10 ^ (k + 2) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hCc) hK) h10
  refine ⟨min (e₀ * 5 ^ (k + 2) / (2000 * Λ) ^ (k + 2))
      (η ^ 2 * 5 ^ (k + 2) / (968 * Cc * (2000 * Λ) ^ (k + 2) * 10 ^ (k + 2))),
    lt_min (div_pos (mul_pos he₀ h5) hK) (div_pos (mul_pos (pow_pos hη 2) h5) hCK), ?_⟩
  intro b hb hbb μ hfin hreg a ha R hR hADR P 𝒢 hfor fits j g g' hj hg hg' hgg'
  -- the scales `r' = r_{j+1}` and `r_j = 10 r'`
  have hr' : 0 < stageScale 𝒢 (j + 1) := d1cadj_stageScale_pos 𝒢 (j + 1)
  have hrj : stageScale 𝒢 j = 10 * stageScale 𝒢 (j + 1) := d1cadj_stageScale_succ 𝒢 j
  have hrR : stageScale 𝒢 (j + 1) ≤ 48 * R := by
    have h1 := d1cadj_stageScale_le 𝒢 (j + 1)
    have h2 := d1cadj_rootScale_le 𝒢
    linarith
  have hrp : 0 < stageScale 𝒢 (j + 1) ^ (k + 2) := pow_pos hr' _
  -- the buffer of the child-centred comparison ball `P(g, 5 r')`
  have hga : dist g a < 5 * R := d1cadj_dist_lt 𝒢 hfor hg.1
  have hball : Metric.ball g (4 * (5 * stageScale 𝒢 (j + 1))) ⊆ Metric.ball a (1000 * R) :=
    Metric.ball_subset_ball' (by linarith)
  have h4 : 4 * (5 * stageScale 𝒢 (j + 1)) ≤ 1000 * R := by linarith
  -- the local errors at the two levels
  have hloc : ∀ (i : ℕ) (x : Space n), Admissible 𝒢 i x →
      fit μ (fits.model i x) x (40 * stageScale 𝒢 i) ≤
        ENNReal.ofReal ((2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 i ^ (k + 2)) :=
    fun i x hx => hLE n μ.support R P μ k Λ b 𝒢 fits hΛ i x hx
  have hb1 : b ≤ e₀ * 5 ^ (k + 2) / (2000 * Λ) ^ (k + 2) := hbb.trans (min_le_left _ _)
  have hb2 : b ≤ η ^ 2 * 5 ^ (k + 2) / (968 * Cc * (2000 * Λ) ^ (k + 2) * 10 ^ (k + 2)) :=
    hbb.trans (min_le_right _ _)
  have hKb : b * (2000 * Λ) ^ (k + 2) ≤ e₀ * 5 ^ (k + 2) := (le_div_iff₀ hK).1 hb1
  -- the horizontal small-error hypothesis, from the child's local fit
  have hhor : 𝒢.type = .horizontal → ∃ M : Models n k 𝒢.type.toFamilyKind,
      fit μ M g (2 * (5 * stageScale 𝒢 (j + 1))) ≤
        ENNReal.ofReal (e₀ * (5 * stageScale 𝒢 (j + 1)) ^ (k + 2)) := by
    intro _
    refine ⟨fits.model (j + 1) g, (d1cadj_fit_mono μ _ g (by linarith)).trans
      ((hloc (j + 1) g hg).trans (ENNReal.ofReal_le_ofReal ?_))⟩
    calc (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 (j + 1) ^ (k + 2)
        = b * (2000 * Λ) ^ (k + 2) * stageScale 𝒢 (j + 1) ^ (k + 2) := by ring
      _ ≤ e₀ * 5 ^ (k + 2) * stageScale 𝒢 (j + 1) ^ (k + 2) :=
          mul_le_mul_of_nonneg_right hKb hrp.le
      _ = e₀ * (5 * stageScale 𝒢 (j + 1)) ^ (k + 2) := by
          rw [mul_pow (5 : ℝ) (stageScale 𝒢 (j + 1)) (k + 2)]; ring
  -- the common source `μ⌞P(g, 5 r')` lies in both fitting balls
  have hsub1 : Metric.ball g (5 * stageScale 𝒢 (j + 1)) ⊆
      Metric.ball g (40 * stageScale 𝒢 (j + 1)) :=
    Metric.ball_subset_ball (by linarith)
  have hsub2 : Metric.ball g (5 * stageScale 𝒢 (j + 1)) ⊆
      Metric.ball g' (40 * stageScale 𝒢 j) :=
    Metric.ball_subset_ball' (by rw [hrj] at hgg' ⊢; linarith)
  have hcmp := hPC 𝒢.type 𝒢.type_available μ a (1000 * R) hADR g
    (d1cadj_rootCell_subset 𝒢 hg.1) (5 * stageScale 𝒢 (j + 1)) (by linarith) hball h4 hhor
    (NeckSelection.modelPlane 𝒢.type (fits.model (j + 1) g))
    (NeckSelection.modelPlane 𝒢.type (fits.model j g'))
    (μ.restrict (Metric.ball g (40 * stageScale 𝒢 (j + 1))))
    (μ.restrict (Metric.ball g' (40 * stageScale 𝒢 j)))
    (Measure.restrict_mono hsub1 le_rfl) (Measure.restrict_mono hsub2 le_rfl)
  have hS1 := (d1cadj_spatialFit_le_fit μ 𝒢.type (fits.model (j + 1) g) g
    (40 * stageScale 𝒢 (j + 1))).trans (hloc (j + 1) g hg)
  have hS2 := (d1cadj_spatialFit_le_fit μ 𝒢.type (fits.model j g') g'
    (40 * stageScale 𝒢 j)).trans (hloc j g' hg')
  have hX1 : 0 ≤ (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 (j + 1) ^ (k + 2) :=
    (mul_pos (mul_pos hK hb) hrp).le
  have hX2 : 0 ≤ (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 j ^ (k + 2) :=
    (mul_pos (mul_pos hK hb) (pow_pos (d1cadj_stageScale_pos 𝒢 j) _)).le
  have hCr : 0 ≤ Cc / (5 * stageScale 𝒢 (j + 1)) ^ (k + 2) :=
    div_nonneg hCc.le (pow_pos (by linarith) _).le
  have hmain := d1cadj_real_of_ennreal hCr hX1 hX2 hcmp hS1 hS2
  -- arithmetic: `d_{x_g, 5 r'}² ≤ C K b (1 + 10^p) / 5^p`
  have hr'0 : stageScale 𝒢 (j + 1) ≠ 0 := hr'.ne'
  have hsimp : Cc / (5 * stageScale 𝒢 (j + 1)) ^ (k + 2) *
      ((2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 (j + 1) ^ (k + 2) +
        (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 j ^ (k + 2)) =
      Cc * (2000 * Λ) ^ (k + 2) * b * (1 + 10 ^ (k + 2)) / 5 ^ (k + 2) := by
    rw [hrj, mul_pow (5 : ℝ) (stageScale 𝒢 (j + 1)) (k + 2),
      mul_pow (10 : ℝ) (stageScale 𝒢 (j + 1)) (k + 2)]
    field_simp
  rw [hsimp] at hmain
  have hb2' : b * (968 * Cc * (2000 * Λ) ^ (k + 2) * 10 ^ (k + 2)) ≤ η ^ 2 * 5 ^ (k + 2) :=
    (le_div_iff₀ hCK).1 hb2
  have hCKb : 0 ≤ Cc * (2000 * Λ) ^ (k + 2) * b := (mul_pos (mul_pos hCc hK) hb).le
  have h110 : (1 : ℝ) + 10 ^ (k + 2) ≤ 2 * 10 ^ (k + 2) := by
    have : (1 : ℝ) ≤ 10 ^ (k + 2) := one_le_pow₀ (by norm_num)
    linarith
  have hX : 484 * (Cc * (2000 * Λ) ^ (k + 2) * b * (1 + 10 ^ (k + 2)) / 5 ^ (k + 2)) ≤
      η ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ h5]
    calc 484 * (Cc * (2000 * Λ) ^ (k + 2) * b * (1 + 10 ^ (k + 2)))
        ≤ 484 * (Cc * (2000 * Λ) ^ (k + 2) * b * (2 * 10 ^ (k + 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h110 hCKb) (by norm_num)
      _ = b * (968 * Cc * (2000 * Λ) ^ (k + 2) * 10 ^ (k + 2)) := by ring
      _ ≤ η ^ 2 * 5 ^ (k + 2) := hb2'
  -- anchor change `x_g → x_{g'}` and radius change `5 r' → r_j = 10 r'`
  have hxy : ‖g'.1 - g.1‖ ≤ 40 * (5 * stageScale 𝒢 (j + 1)) := by
    have h1 : ‖g'.1 - g.1‖ ≤ dist g' g := by
      rw [← dist_eq_norm, Prod.dist_eq]
      exact le_max_left _ _
    have h2 : dist g' g = dist g g' := dist_comm _ _
    rw [hrj] at hgg'
    linarith
  rw [hrj]
  exact d1cadj_final _ _ g.1 g'.1 hr' hη hxy hmain hX

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
