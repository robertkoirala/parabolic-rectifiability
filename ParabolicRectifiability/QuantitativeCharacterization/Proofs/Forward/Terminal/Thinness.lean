import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # Thinness: the full parabolic tube tests

Proof of `d1c_thinness_proof : LocalErrorStatement → PartitionEnergy.PointToFitStatement →
ThinnessStatement` (implication form over the local error statement and the point-to-fit
statement).

Constants: `Λ₀ = 4000`, `B = 50`, and for a tolerance `η > 0`
`b₀ = min(1, (η/4)^{k+2}) / (A (1000 Λ)^{k+2})`.

Route. For `j ≥ 1` and admissible `(j, g)`: `g ∈ S` is within `5R` of `a` (root forest) and
`r_j ≤ 4.8 ℓ_* ≤ 4.8 R`, so `P(g, 8 r_j) ⊆ P(a, 50 R)`. The local error (hypothesis) gives
`fit μ Π_g g (4 r_j) ≤ fit μ Π_g g (40 r_j) ≤ (2000Λ)^{k+2} b r_j^{k+2} = e (2 r_j)^{k+2}` with
`e = (1000 Λ)^{k+2} b`, and `A e ≤ min(1, (η/4)^{k+2})`. Point-to-fit (hypothesis) at centre `g`,
radius `2 r_j` gives `d_P(z, Π_g) ≤ 4 (A e)^{1/(k+2)} r_j ≤ η r_j` for every
`z ∈ supp μ ∩ P(g, 2 r_j)`. The model set is `T.lowerModelSet L_g τ_g`, so the spatial distance
to `L_g` and (horizontally) `√|t_z - τ_g|` are at most `d_P(z, Π_g)`. Every fit is of the
original `μ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- `ℓ_* ≤ ℓ₀`. -/
theorem d1cthin_rootScale_le (𝒢 : GoodRegion P μ k Λ b) : 𝒢.rootScale ≤ ℓ₀ := by
  unfold GoodRegion.rootScale DirectPartition.scale coherentScale
  exact div_le_self P.scale_pos.le (one_le_pow₀ (by norm_num))

/-- `r_j > 0`. -/
theorem d1cthin_stageScale_pos (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) : 0 < stageScale 𝒢 j := by
  unfold stageScale coherentScale
  exact div_pos (mul_pos (by norm_num) (d1c_rootScale_pos 𝒢)) (pow_pos (by norm_num) _)

/-- `r_j ≤ 4.8 ℓ_*` for `j ≥ 1`. -/
theorem d1cthin_stageScale_le (𝒢 : GoodRegion P μ k Λ b) {j : ℕ} (hj : 1 ≤ j) :
    stageScale 𝒢 j ≤ 48 * 𝒢.rootScale / 10 := by
  unfold stageScale coherentScale
  apply div_le_div_of_nonneg_left (mul_pos (by norm_num) (d1c_rootScale_pos 𝒢)).le
    (by norm_num)
  calc (10 : ℝ) = 10 ^ 1 := by norm_num
    _ ≤ 10 ^ j := pow_le_pow_right₀ (by norm_num) hj

end

/-- Every point of a root-forest region's root cell is within `5R` of `a`. -/
theorem d1cthin_dist_lt {n : ℕ} {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} {a : Space n} {R : ℝ}
    (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b) (hF : P.InForest a R 𝒢.root) :
    ∀ g ∈ 𝒢.rootCell, dist g a < 5 * R := by
  intro g hg
  obtain ⟨z₀, hz₀, ⟨w, hw0, hwa⟩, -, -, hsub⟩ := hF
  have hball := P.cell_subset_ball 0 z₀ hz₀
  have h0 : coherentScale R 0 = R := by simp [coherentScale]
  rw [h0] at hball
  have hg0 : g ∈ Metric.ball z₀ (2 * R) := hball (hsub hg)
  have hw0' : w ∈ Metric.ball z₀ (2 * R) := hball hw0
  rw [Metric.mem_ball] at hg0 hw0' hwa
  have hc := dist_comm z₀ w
  calc dist g a ≤ dist g z₀ + dist z₀ w + dist w a := dist_triangle4 _ _ _ _
    _ < 2 * R + 2 * R + R := by linarith
    _ = 5 * R := by ring

/-- `√|t_z - t_w| ≤ d_P(z, w)`. -/
theorem d1cthin_sqrt_le_dist {n : ℕ} (z w : Space n) :
    Real.sqrt |z.2.val - w.2.val| ≤ dist z w := by
  calc Real.sqrt |z.2.val - w.2.val|
      ≤ max ‖z.1 - w.1‖ (Real.sqrt |z.2.val - w.2.val|) := le_max_right _ _
    _ = dist (point z.1 z.2.val) (point w.1 w.2.val) := (dist_point _ _ _ _).symm
    _ = dist z w := rfl

/-- **The tube reading of a full-model distance**: since `modelSet M` is
`T.lowerModelSet (modelPlane T M) (modelTime T M)`, a bound `d_P(z, M) ≤ c` bounds the spatial
distance to the plane by `c` and, horizontally, `|t_z - τ|` by `c²`. -/
theorem d1cthin_tube {n k : ℕ} (T : NeckType) (M : Models n k T.toFamilyKind) (z : Space n)
    (c : ℝ) (h : Metric.infDist z (modelSet M) ≤ c) :
    Metric.infDist z.1 (NeckSelection.modelPlane T M).toSet ≤ c ∧
      (T = .horizontal → |z.2.val - NeckSelection.modelTime T M| ≤ c ^ 2) := by
  have hset := NeckSelection.lowerModelSet_modelPlane T M
  have hne : (modelSet M).Nonempty := modelSet_nonempty M
  constructor
  · refine le_trans ((Metric.le_infDist hne).mpr fun w hw => ?_) h
    have hw' : w.1 ∈ (NeckSelection.modelPlane T M).toSet := by
      rw [← hset] at hw
      cases T with
      | horizontal => exact hw.1
      | vertical => exact hw
    calc Metric.infDist z.1 (NeckSelection.modelPlane T M).toSet ≤ dist z.1 w.1 :=
          Metric.infDist_le_dist_of_mem hw'
      _ ≤ dist z w := by rw [Prod.dist_eq]; exact le_max_left _ _
  · intro hT
    subst hT
    have hsq : Real.sqrt |z.2.val - NeckSelection.modelTime .horizontal M| ≤ c := by
      refine le_trans ((Metric.le_infDist hne).mpr fun w hw => ?_) h
      rw [← hset] at hw
      have hwt : w.2.val = NeckSelection.modelTime .horizontal M := hw.2
      rw [← hwt]
      exact d1cthin_sqrt_le_dist z w
    have h0 := Real.sq_sqrt (abs_nonneg (z.2.val - NeckSelection.modelTime .horizontal M))
    rw [← h0]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2

/-- `x ≤ c^{k+2}` gives `x^{1/(k+2)} ≤ c`. -/
theorem d1cthin_rpow_le (k : ℕ) {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ≤ c ^ (k + 2)) :
    x ^ ((1 : ℝ) / (k + 2)) ≤ c := by
  have hp : ((k : ℝ) + 2) ≠ 0 := by positivity
  calc x ^ ((1 : ℝ) / (k + 2)) ≤ (c ^ (k + 2)) ^ ((1 : ℝ) / (k + 2)) :=
        Real.rpow_le_rpow hx h (by positivity)
    _ = c := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc]
        have h1 : ((k + 2 : ℕ) : ℝ) * (1 / ((k : ℝ) + 2)) = 1 := by
          rw [Nat.cast_add, Nat.cast_ofNat]
          exact mul_one_div_cancel hp
        rw [h1, Real.rpow_one]

/-- `(2x)^p w y^p = x^p w (2y)^p`. -/
theorem d1cthin_pow_identity (x y w : ℝ) (p : ℕ) :
    (2 * x) ^ p * w * y ^ p = x ^ p * w * (2 * y) ^ p := by
  rw [mul_pow, mul_pow]; ring

/-- **Thinness: the full parabolic tube tests** (`ThinnessStatement`). -/
theorem d1c_thinness_proof :
    LocalErrorStatement → PartitionEnergy.PointToFitStatement → ThinnessStatement := by
  intro hErr hP2F n hn k hk hkn A hA
  refine ⟨4000, by norm_num, fun Λ hΛ => ⟨50, by norm_num, fun η hη => ?_⟩⟩
  have hΛ0 : 0 < Λ := by linarith
  have hA0 : 0 < A := by linarith
  have hc0 : 0 < (1000 * Λ) ^ (k + 2) := pow_pos (by linarith) _
  have hη4 : 0 < η / 4 := div_pos hη (by norm_num)
  have hm0 : 0 < min 1 ((η / 4) ^ (k + 2)) := lt_min one_pos (pow_pos hη4 _)
  refine ⟨min 1 ((η / 4) ^ (k + 2)) / (A * (1000 * Λ) ^ (k + 2)),
    div_pos hm0 (mul_pos hA0 hc0), fun b hb hbb => ?_⟩
  intro μ hμc hμr a ha R hR hADR P 𝒢 hF fits j g hj hadm z hz
  have he0 : 0 ≤ (1000 * Λ) ^ (k + 2) * b := mul_nonneg hc0.le hb.le
  have hAe : A * ((1000 * Λ) ^ (k + 2) * b) ≤ min 1 ((η / 4) ^ (k + 2)) := by
    have h := (le_div_iff₀ (mul_pos hA0 hc0)).mp hbb
    calc A * ((1000 * Λ) ^ (k + 2) * b) = b * (A * (1000 * Λ) ^ (k + 2)) := by ring
      _ ≤ _ := h
  have hroot : (A * ((1000 * Λ) ^ (k + 2) * b)) ^ ((1 : ℝ) / (k + 2)) ≤ η / 4 :=
    d1cthin_rpow_le k (mul_nonneg hA0.le he0) hη4.le (hAe.trans (min_le_right _ _))
  have hℓR : 𝒢.rootScale ≤ R := d1cthin_rootScale_le 𝒢
  have hr : 0 < stageScale 𝒢 j := d1cthin_stageScale_pos 𝒢 j
  have hrj : stageScale 𝒢 j ≤ 48 * 𝒢.rootScale / 10 := d1cthin_stageScale_le 𝒢 hj
  have hga : dist g a < 5 * R := d1cthin_dist_lt P 𝒢 hF g hadm.1
  have hsub : Metric.ball g (4 * (2 * stageScale 𝒢 j)) ⊆ Metric.ball a (50 * R) :=
    Metric.ball_subset_ball' (by linarith)
  have h4 : 4 * (2 * stageScale 𝒢 j) ≤ 50 * R := by linarith
  have hfit : fit μ (fits.model j g) g (2 * (2 * stageScale 𝒢 j)) ≤
      ENNReal.ofReal ((1000 * Λ) ^ (k + 2) * b * (2 * stageScale 𝒢 j) ^ (k + 2)) := by
    calc fit μ (fits.model j g) g (2 * (2 * stageScale 𝒢 j))
        ≤ fit μ (fits.model j g) g (40 * stageScale 𝒢 j) :=
          MeasureTheory.lintegral_mono_set (Metric.ball_subset_ball (by linarith))
      _ ≤ ENNReal.ofReal ((2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 j ^ (k + 2)) :=
          hErr n μ.support R P μ k Λ b 𝒢 fits hΛ j g hadm
      _ = ENNReal.ofReal ((1000 * Λ) ^ (k + 2) * b * (2 * stageScale 𝒢 j) ^ (k + 2)) := by
          congr 1
          rw [show (2000 : ℝ) * Λ = 2 * (1000 * Λ) by ring]
          exact d1cthin_pow_identity _ _ _ _
  have hP := hP2F n k 𝒢.type.toFamilyKind μ A a (50 * R) hA hADR g (2 * stageScale 𝒢 j)
    (by linarith) hsub h4 (fits.model j g) _ he0 (hAe.trans (min_le_left _ _)) hfit z hz
  have hd : Metric.infDist z (modelSet (fits.model j g)) ≤ η * stageScale 𝒢 j := by
    have h := mul_le_mul_of_nonneg_right hroot hr.le
    refine hP.trans ?_
    nlinarith
  obtain ⟨h1, h2⟩ := d1cthin_tube 𝒢.type (fits.model j g) z _ hd
  exact ⟨hd, h1, h2⟩

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
