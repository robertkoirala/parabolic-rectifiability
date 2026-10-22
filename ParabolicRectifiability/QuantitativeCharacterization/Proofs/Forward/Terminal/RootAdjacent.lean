import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # The root plane comparison (`d1c_rootAdjacent`)

This module proves `d1c_rootAdjacent_proof`, in implication form:

`LocalErrorStatement → PartitionEnergy.PlaneComparisonStatement → RootAdjacentStatement`.

Route, with `p = k + 2`, `K = (2000 Λ)^p` and the constants `C, e₀` of the plane comparison at
`(n, k, A)`: `Λ₀ = 4000` (the local error), `B = 1000`, and
`b₀ = min(e₀ 5^p / K, η² 5^p / (18 C K))`.
For an admissible `g` of level `1` and an anchor `x` with `‖x - x_q‖ ≤ r₀ = 48 ℓ_*`, write
`r₁ = 48 ℓ_* / 10`, so `5 r₁ = 24 ℓ_*` and `r₀ = 10 r₁`:
* the comparison ball is the child-centred `P(g, s)`, `s = 5 r₁`; its buffer `P(g, 20 r₁)` lies in
  `P(a, 1000 R)` (`d_P(g, a) < 5R`, `r₁ ≤ 48 R`);
* the horizontal small-error hypothesis is the local fit:
  `fit μ Π_g g (2s) ≤ fit μ Π_g g (40 r₁) ≤ K b r₁^p ≤ e₀ s^p`;
* the dominating measures are `μ⌞P(g, 40 r₁)` and the root coefficient ball `μ⌞P(q, Λ ℓ_*)`; the
  second contains `μ⌞P(g, 24 ℓ_*)` because `d_P(g, q) < 2 ℓ_*` and `26 ℓ_* ≤ Λ ℓ_*`;
* the spatial fitting integrals: the local error gives `K b r₁^p`; the root plane is the plane of
  the root model `Π_*`, whose fit on its coefficient ball is at most `(Λ ℓ_*)^p b ≤ K b r₁^p`
  (`model_optimal` is not needed: the root term of the chain budget bounds `modelCoeff` directly);
  so `d_{x_g, s}(L_g, L_*)² ≤ 2 C K b / 5^p`;
* anchor change `x_g → x` (`‖x - x_g‖ ≤ 48 ℓ_* + 2 ℓ_* = 50 ℓ_* ≤ 3 s`) and radius change
  `s → r₀` (`affineComparison_change_anchor_radius`, factor `1 + 4 s / r₀ = 3`), and
  `9 · 2 C K b / 5^p ≤ η²`. The local fit need not equal the root plane.

Both inputs enter only as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section RadjHelpers

variable {n : ℕ}

/-- The spatial distance to a plane is at most the parabolic distance to any lower model set
on it. -/
theorem d1cradj_spatial_sq_le_lower (T : NeckType) {m : ℕ} (L : AffineSpatialPlane n m)
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
theorem d1cradj_spatial_le_modelCost {k : ℕ} (T : NeckType) (M : Models n k T.toFamilyKind)
    (z : Space n) :
    ENNReal.ofReal (‖z.1 - (NeckSelection.modelPlane T M).projection z.1‖ ^ 2) ≤
      modelCost M z := by
  have h := d1cradj_spatial_sq_le_lower T (NeckSelection.modelPlane T M)
    (NeckSelection.modelTime T M) z
  rw [NeckSelection.lowerModelSet_modelPlane] at h
  exact h

/-- The spatial fitting integral of a model's plane on `μ⌞P(g, r)` is at most the model's fit. -/
theorem d1cradj_spatialFit_le_fit {k : ℕ} (μ : Measure (Space n)) (T : NeckType)
    (M : Models n k T.toFamilyKind) (g : Space n) (r : ℝ) :
    spatialFittingIntegral (μ.restrict (Metric.ball g r)) (NeckSelection.modelPlane T M) ≤
      fit μ M g r := by
  unfold spatialFittingIntegral fit
  exact lintegral_mono fun z => d1cradj_spatial_le_modelCost T M z

/-- The fit is monotone in the radius. -/
theorem d1cradj_fit_mono {k : ℕ} {F : FamilyKind} (μ : Measure (Space n)) (M : Models n k F)
    (g : Space n) {r s : ℝ} (h : r ≤ s) : fit μ M g r ≤ fit μ M g s := by
  unfold fit
  exact lintegral_mono_set (Metric.ball_subset_ball h)

/-- Passage from the extended comparison inequality to a real one. -/
theorem d1cradj_real_of_ennreal {x Cr X₁ X₂ : ℝ} (hCr : 0 ≤ Cr) (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    {S₁ S₂ : ℝ≥0∞} (h : ENNReal.ofReal x ≤ ENNReal.ofReal Cr * (S₁ + S₂))
    (h₁ : S₁ ≤ ENNReal.ofReal X₁) (h₂ : S₂ ≤ ENNReal.ofReal X₂) : x ≤ Cr * (X₁ + X₂) := by
  have h' := h.trans (mul_le_mul' le_rfl (add_le_add h₁ h₂))
  rw [← ENNReal.ofReal_add hX₁ hX₂, ← ENNReal.ofReal_mul hCr,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCr (add_nonneg hX₁ hX₂))] at h'
  exact h'

variable {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The root cell lies in the partitioned set. -/
theorem d1cradj_rootCell_subset (𝒢 : GoodRegion P μ k Λ b) : 𝒢.rootCell ⊆ E := by
  intro x hx
  rw [← P.cell_cover 𝒢.root.1]
  exact Set.mem_biUnion (t := fun z => P.cell 𝒢.root.1 z)
    (show 𝒢.root.2 ∈ P.center 𝒢.root.1 from 𝒢.root_isCell)
    (show x ∈ P.cell 𝒢.root.1 𝒢.root.2 from hx)

/-- The construction scales are positive. -/
theorem d1cradj_stageScale_pos (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) : 0 < stageScale 𝒢 j := by
  unfold stageScale coherentScale
  have := d1c_rootScale_pos 𝒢
  positivity

/-- `r_j ≤ r_0 = 48 ℓ_*`. -/
theorem d1cradj_stageScale_le (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    stageScale 𝒢 j ≤ 48 * 𝒢.rootScale := by
  unfold stageScale coherentScale
  have := d1c_rootScale_pos 𝒢
  exact div_le_self (by linarith) (one_le_pow₀ (by norm_num))

/-- `r_j = 10 r_{j+1}`. -/
theorem d1cradj_stageScale_succ (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    stageScale 𝒢 j = 10 * stageScale 𝒢 (j + 1) := by
  unfold stageScale coherentScale
  have h : (10 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [pow_succ]
  field_simp

end RadjHelpers

section RadjForest

variable {n : ℕ} {E : Set (Space n)} {R : ℝ} {P : DirectPartition E R} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The root side is at most the top scale `R`. -/
theorem d1cradj_rootScale_le (𝒢 : GoodRegion P μ k Λ b) : 𝒢.rootScale ≤ R := by
  unfold GoodRegion.rootScale DirectPartition.scale coherentScale
  exact div_le_self P.scale_pos.le (one_le_pow₀ (by norm_num))

/-- A point of the root cell of a forest region lies within `5R` of `a`. -/
theorem d1cradj_dist_lt (𝒢 : GoodRegion P μ k Λ b) {a : Space n}
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

end RadjForest

section RadjRoot

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The root model's fit on the root coefficient ball is at most `(Λ ℓ_*)^{k+2} b` (the root
term of the chain budget). -/
theorem d1cradj_root_fit_le (𝒢 : GoodRegion P μ k Λ b) (hpos : 0 < Λ * P.scale 𝒢.root.1) :
    fit μ (𝒢.model 𝒢.root) 𝒢.root.2 (Λ * P.scale 𝒢.root.1) ≤
      ENNReal.ofReal (Λ * P.scale 𝒢.root.1) ^ (k + 2) * ENNReal.ofReal b := by
  have hbelow : P.IsBelow 𝒢.root 𝒢.root := ⟨𝒢.root_isCell, le_rfl, subset_rfl⟩
  have hcoeff : P.modelCoeff μ Λ (𝒢.model 𝒢.root) 𝒢.root ≤ ENNReal.ofReal b := by
    refine le_trans ?_ (𝒢.budget 𝒢.root 𝒢.root_mem)
    exact ENNReal.le_tsum
      (f := fun Q' : {Q' : ℕ × Space n // Q' ∈ 𝒢.members ∧ P.IsBelow 𝒢.root Q'} =>
        P.modelCoeff μ Λ (𝒢.model Q'.1) Q'.1) ⟨𝒢.root, 𝒢.root_mem, hbelow⟩
  have hx0 : ENNReal.ofReal (Λ * P.scale 𝒢.root.1) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  have hxt : ENNReal.ofReal (Λ * P.scale 𝒢.root.1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have heq : fit μ (𝒢.model 𝒢.root) 𝒢.root.2 (Λ * P.scale 𝒢.root.1) =
      ENNReal.ofReal (Λ * P.scale 𝒢.root.1) ^ (k + 2) *
        P.modelCoeff μ Λ (𝒢.model 𝒢.root) 𝒢.root := by
    rw [DirectPartition.modelCoeff, ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel hx0 hxt,
      one_pow, one_mul]
  rw [heq]
  gcongr

/-- A point of the root cell lies within `2 ℓ_*` of the root centre `q`. -/
theorem d1cradj_dist_root_lt (𝒢 : GoodRegion P μ k Λ b) {g : Space n} (hg : g ∈ 𝒢.rootCell) :
    dist g 𝒢.root.2 < 2 * 𝒢.rootScale := by
  have h := P.cell_subset_ball 𝒢.root.1 𝒢.root.2 𝒢.root_isCell hg
  exact h

/-- `r₀ = 48 ℓ_*`. -/
theorem d1cradj_stageScale_zero (𝒢 : GoodRegion P μ k Λ b) :
    stageScale 𝒢 0 = 48 * 𝒢.rootScale := by
  unfold stageScale coherentScale
  rw [pow_zero, div_one]

end RadjRoot

/-- The arithmetic of the root comparison: from the squared comparison at `(x_g, 5 r₁)`, the
anchor and radius change to `(x, 10 r₁)` gives tolerance `η`. -/
theorem d1cradj_final {n m : ℕ} (L₁ L₂ : AffineSpatialPlane n m) (x y : Spatial n)
    {r₁ X η : ℝ} (hr₁ : 0 < r₁) (hη : 0 < η) (hxy : ‖y - x‖ ≤ 3 * (5 * r₁))
    (hsq : planeComparison x (5 * r₁) L₁ L₂ ^ 2 ≤ X) (hX : 9 * X ≤ η ^ 2) :
    planeComparison y (10 * r₁) L₁ L₂ ≤ η := by
  have hs : 0 < 5 * r₁ := by linarith
  have hr : 0 < 10 * r₁ := by linarith
  have hch := affineComparison_change_anchor_radius L₁ L₂ x y (5 * r₁) (10 * r₁) 3 hs hr
    (by norm_num) hxy
  have hfac : 1 + (3 + 1) * (5 * r₁) / (10 * r₁) = 3 := by
    field_simp
    ring
  rw [hfac] at hch
  have hpc0 : 0 ≤ planeComparison x (5 * r₁) L₁ L₂ := affineComparison_nonneg L₁ L₂ x hs.le
  have h3 : (3 * planeComparison x (5 * r₁) L₁ L₂) ^ 2 ≤ η ^ 2 := by
    calc (3 * planeComparison x (5 * r₁) L₁ L₂) ^ 2
        = 9 * planeComparison x (5 * r₁) L₁ L₂ ^ 2 := by ring
      _ ≤ 9 * X := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ ≤ η ^ 2 := hX
  have h3' : 3 * planeComparison x (5 * r₁) L₁ L₂ ≤ η :=
    (pow_le_pow_iff_left₀ (by linarith) hη.le two_ne_zero).1 h3
  calc planeComparison y (10 * r₁) L₁ L₂ = affineComparison L₁ L₂ y (10 * r₁) := rfl
    _ ≤ 3 * affineComparison L₁ L₂ x (5 * r₁) := hch
    _ = 3 * planeComparison x (5 * r₁) L₁ L₂ := rfl
    _ ≤ η := h3'

/-- **Root plane comparison** (`d1c_rootAdjacent`): comparison of an admissible level-`1`
occurrence with the initial plane `L_*` at every anchor within `r₀` of `x_q`, from the local
error and the same-source plane comparison (both as hypotheses), on the child-centred
source inside the root coefficient ball. -/
theorem d1c_rootAdjacent_proof :
    LocalErrorStatement → PartitionEnergy.PlaneComparisonStatement →
      RootAdjacentStatement := by
  intro hLE hPC n hn k hk hkn A hA
  obtain ⟨Cc, hCc, e₀, he₀, hPC⟩ := hPC n hn k hk hkn A hA
  refine ⟨4000, by norm_num, fun Λ hΛ => ⟨1000, by norm_num, fun η hη => ?_⟩⟩
  have hK : 0 < (2000 * Λ) ^ (k + 2) := pow_pos (by linarith) _
  have h5 : (0 : ℝ) < 5 ^ (k + 2) := pow_pos (by norm_num) _
  have hCK : 0 < 18 * Cc * (2000 * Λ) ^ (k + 2) := mul_pos (mul_pos (by norm_num) hCc) hK
  refine ⟨min (e₀ * 5 ^ (k + 2) / (2000 * Λ) ^ (k + 2))
      (η ^ 2 * 5 ^ (k + 2) / (18 * Cc * (2000 * Λ) ^ (k + 2))),
    lt_min (div_pos (mul_pos he₀ h5) hK) (div_pos (mul_pos (pow_pos hη 2) h5) hCK), ?_⟩
  intro b hb hbb μ hfin hreg a ha R hR hADR P 𝒢 hfor fits g hg x hx
  -- the scales `r₁`, `r₀ = 10 r₁ = 48 ℓ_*`
  have hℓ : 0 < 𝒢.rootScale := d1c_rootScale_pos 𝒢
  have hr₁ : 0 < stageScale 𝒢 1 := d1cradj_stageScale_pos 𝒢 1
  have hr0 : stageScale 𝒢 0 = 10 * stageScale 𝒢 1 := d1cradj_stageScale_succ 𝒢 0
  have hr0ℓ : stageScale 𝒢 0 = 48 * 𝒢.rootScale := d1cradj_stageScale_zero 𝒢
  have hrR : stageScale 𝒢 1 ≤ 48 * R := by
    have h1 := d1cradj_stageScale_le 𝒢 1
    have h2 := d1cradj_rootScale_le 𝒢
    linarith
  have hrp : 0 < stageScale 𝒢 1 ^ (k + 2) := pow_pos hr₁ _
  -- the buffer of the child-centred comparison ball `P(g, 5 r₁)`
  have hga : dist g a < 5 * R := d1cradj_dist_lt 𝒢 hfor hg.1
  have hball : Metric.ball g (4 * (5 * stageScale 𝒢 1)) ⊆ Metric.ball a (1000 * R) :=
    Metric.ball_subset_ball' (by linarith)
  have h4 : 4 * (5 * stageScale 𝒢 1) ≤ 1000 * R := by linarith
  -- the local error at `g`
  have hloc : fit μ (fits.model 1 g) g (40 * stageScale 𝒢 1) ≤
      ENNReal.ofReal ((2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 1 ^ (k + 2)) :=
    hLE n μ.support R P μ k Λ b 𝒢 fits hΛ 1 g hg
  have hb1 : b ≤ e₀ * 5 ^ (k + 2) / (2000 * Λ) ^ (k + 2) := hbb.trans (min_le_left _ _)
  have hb2 : b ≤ η ^ 2 * 5 ^ (k + 2) / (18 * Cc * (2000 * Λ) ^ (k + 2)) :=
    hbb.trans (min_le_right _ _)
  have hKb : b * (2000 * Λ) ^ (k + 2) ≤ e₀ * 5 ^ (k + 2) := (le_div_iff₀ hK).1 hb1
  -- the horizontal small-error hypothesis, from the local fit at `g`
  have hhor : 𝒢.type = .horizontal → ∃ M : Models n k 𝒢.type.toFamilyKind,
      fit μ M g (2 * (5 * stageScale 𝒢 1)) ≤
        ENNReal.ofReal (e₀ * (5 * stageScale 𝒢 1) ^ (k + 2)) := by
    intro _
    refine ⟨fits.model 1 g, (d1cradj_fit_mono μ _ g (by linarith)).trans
      (hloc.trans (ENNReal.ofReal_le_ofReal ?_))⟩
    calc (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 1 ^ (k + 2)
        = b * (2000 * Λ) ^ (k + 2) * stageScale 𝒢 1 ^ (k + 2) := by ring
      _ ≤ e₀ * 5 ^ (k + 2) * stageScale 𝒢 1 ^ (k + 2) :=
          mul_le_mul_of_nonneg_right hKb hrp.le
      _ = e₀ * (5 * stageScale 𝒢 1) ^ (k + 2) := by
          rw [mul_pow (5 : ℝ) (stageScale 𝒢 1) (k + 2)]; ring
  -- the common source `μ⌞P(g, 5 r₁)` lies in the fitting ball and the root coefficient ball
  have hgq : dist g 𝒢.root.2 < 2 * 𝒢.rootScale := d1cradj_dist_root_lt 𝒢 hg.1
  have hΛℓ : 4000 * 𝒢.rootScale ≤ Λ * 𝒢.rootScale := mul_le_mul_of_nonneg_right hΛ hℓ.le
  have hsub1 : Metric.ball g (5 * stageScale 𝒢 1) ⊆ Metric.ball g (40 * stageScale 𝒢 1) :=
    Metric.ball_subset_ball (by linarith)
  have hsub2 : Metric.ball g (5 * stageScale 𝒢 1) ⊆
      Metric.ball 𝒢.root.2 (Λ * P.scale 𝒢.root.1) :=
    Metric.ball_subset_ball' (by
      show 5 * stageScale 𝒢 1 + dist g 𝒢.root.2 ≤ Λ * 𝒢.rootScale
      linarith)
  have hcmp := hPC 𝒢.type 𝒢.type_available μ a (1000 * R) hADR g
    (d1cradj_rootCell_subset 𝒢 hg.1) (5 * stageScale 𝒢 1) (by linarith) hball h4 hhor
    (NeckSelection.modelPlane 𝒢.type (fits.model 1 g)) (rootPlane 𝒢)
    (μ.restrict (Metric.ball g (40 * stageScale 𝒢 1)))
    (μ.restrict (Metric.ball 𝒢.root.2 (Λ * P.scale 𝒢.root.1)))
    (Measure.restrict_mono hsub1 le_rfl) (Measure.restrict_mono hsub2 le_rfl)
  have hS1 := (d1cradj_spatialFit_le_fit μ 𝒢.type (fits.model 1 g) g
    (40 * stageScale 𝒢 1)).trans hloc
  -- the root plane on the root coefficient ball
  have hpos : 0 < Λ * P.scale 𝒢.root.1 := by
    show 0 < Λ * 𝒢.rootScale
    linarith
  have hroot : (Λ * P.scale 𝒢.root.1) ^ (k + 2) * b ≤
      (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 1 ^ (k + 2) := by
    have hle : Λ * P.scale 𝒢.root.1 ≤ 2000 * Λ * stageScale 𝒢 1 := by
      show Λ * 𝒢.rootScale ≤ 2000 * Λ * stageScale 𝒢 1
      have hℓr : 𝒢.rootScale ≤ 2000 * stageScale 𝒢 1 := by linarith
      calc Λ * 𝒢.rootScale ≤ Λ * (2000 * stageScale 𝒢 1) :=
            mul_le_mul_of_nonneg_left hℓr (by linarith)
        _ = 2000 * Λ * stageScale 𝒢 1 := by ring
    have hpow := pow_le_pow_left₀ hpos.le hle (k + 2)
    rw [mul_pow (2000 * Λ) (stageScale 𝒢 1) (k + 2)] at hpow
    calc (Λ * P.scale 𝒢.root.1) ^ (k + 2) * b
        ≤ (2000 * Λ) ^ (k + 2) * stageScale 𝒢 1 ^ (k + 2) * b :=
          mul_le_mul_of_nonneg_right hpow hb.le
      _ = (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 1 ^ (k + 2) := by ring
  have hS2 : spatialFittingIntegral (μ.restrict (Metric.ball 𝒢.root.2 (Λ * P.scale 𝒢.root.1)))
      (rootPlane 𝒢) ≤
        ENNReal.ofReal ((2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 1 ^ (k + 2)) := by
    refine ((d1cradj_spatialFit_le_fit μ 𝒢.type (𝒢.model 𝒢.root) 𝒢.root.2
      (Λ * P.scale 𝒢.root.1)).trans (d1cradj_root_fit_le 𝒢 hpos)).trans ?_
    rw [← ENNReal.ofReal_pow hpos.le, ← ENNReal.ofReal_mul (pow_nonneg hpos.le _)]
    exact ENNReal.ofReal_le_ofReal hroot
  have hX : 0 ≤ (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 1 ^ (k + 2) :=
    (mul_pos (mul_pos hK hb) hrp).le
  have hCr : 0 ≤ Cc / (5 * stageScale 𝒢 1) ^ (k + 2) :=
    div_nonneg hCc.le (pow_pos (by linarith) _).le
  have hmain := d1cradj_real_of_ennreal hCr hX hX hcmp hS1 hS2
  -- arithmetic: `d_{x_g, 5 r₁}² ≤ 2 C K b / 5^p`
  have hsimp : Cc / (5 * stageScale 𝒢 1) ^ (k + 2) *
      ((2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 1 ^ (k + 2) +
        (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 1 ^ (k + 2)) =
      2 * Cc * (2000 * Λ) ^ (k + 2) * b / 5 ^ (k + 2) := by
    rw [mul_pow (5 : ℝ) (stageScale 𝒢 1) (k + 2), div_mul_eq_mul_div,
      div_eq_div_iff (mul_pos h5 hrp).ne' h5.ne']
    ring
  rw [hsimp] at hmain
  have hb2' : b * (18 * Cc * (2000 * Λ) ^ (k + 2)) ≤ η ^ 2 * 5 ^ (k + 2) :=
    (le_div_iff₀ hCK).1 hb2
  have h9 : 9 * (2 * Cc * (2000 * Λ) ^ (k + 2) * b / 5 ^ (k + 2)) ≤ η ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ h5]
    calc 9 * (2 * Cc * (2000 * Λ) ^ (k + 2) * b)
        = b * (18 * Cc * (2000 * Λ) ^ (k + 2)) := by ring
      _ ≤ η ^ 2 * 5 ^ (k + 2) := hb2'
  -- anchor change `x_g → x` (`≤ 50 ℓ_* ≤ 3 · 5 r₁`) and radius change `5 r₁ → r₀ = 10 r₁`
  have hxy : ‖x - g.1‖ ≤ 3 * (5 * stageScale 𝒢 1) := by
    have h1 : ‖𝒢.root.2.1 - g.1‖ ≤ dist 𝒢.root.2 g := by
      rw [← dist_eq_norm, Prod.dist_eq]
      exact le_max_left _ _
    have h2 := norm_sub_le_norm_sub_add_norm_sub x 𝒢.root.2.1 g.1
    rw [dist_comm] at h1
    linarith
  rw [hr0]
  exact d1cradj_final _ _ g.1 x hr₁ hη hxy hmain h9

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
