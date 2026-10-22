import ParabolicRectifiability.Foundations.Statements.DensityBridges
import ParabolicRectifiability.Measure.BetaLaws
import ParabolicRectifiability.Specifications.Rectifiability
import ParabolicRectifiability.Foundations.Proofs.EnergyRescaling

/-! # Rescaling in the bounded-growth argument

Proofs of `fbgrowth_rescaled_lowerDensity_ae`, `fbgrowth_rescaled_threshold` and
`fbgrowth_ball_eq_rescaled`, with the same types.

Shared algebra: the all-set evaluation `μ'(S) = ρ^{-k} ν(T⁻¹ S)` of
`μ' = rescaledSource ν k q ρ hρ` (`T = similarity q ρ hρ`; `MeasurableEquiv.map_apply`, valid for
every set), and the ball preimage `T⁻¹ P(T z, r) = P(z, ρ r)` (`preimage_similarity_ball`).
* `fbgrowth_rescaled_lowerDensity_ae`: `densityRatio μ' k (T z) r = densityRatio ν k z (ρ r)` and `map (ρ * ·) 𝓝[>]0 = 𝓝[>]0`
  give `Θ_*^k(μ', T z) = Θ_*^k(ν, z)`; the exceptional set of `μ'` pulls back to that of `ν`,
  so its `μ'`-mass is `ρ^{-k} · 0` (no measurability of the density predicate is used).
* `fbgrowth_rescaled_threshold`: `S^2_{μ'}(T z) = S^{2ρ}_ν(z) ≤ S^R_ν(z)` (by
  `squareEnergy_rescaledSource_eq_proof` and `lintegral_mono_set`); the pulled-back exceptional set is `ν`-null.
* `fbgrowth_ball_eq_rescaled`: `T q = point 0 0`, so `μ'(P(0,1)) = ρ^{-k} ν(P(q,ρ))`; cancel `ρ^k ρ^{-k} = 1`.

Helpers carry the prefix `fbfb5_`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- All-set evaluation of the rescaled source (restates `rescaledSource_apply`). -/
theorem fbfb5_rescaledSource_apply {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (q : Space n)
    (ρ : ℝ) (hρ : 0 < ρ) (S : Set (Space n)) :
    rescaledSource ν k q ρ hρ S = (ENNReal.ofReal ρ)⁻¹ ^ k * ν (similarity q ρ hρ ⁻¹' S) := by
  rw [rescaledSource, Measure.smul_apply, smul_eq_mul]
  congr 1
  exact (similarity q ρ hρ).toMeasurableEquiv.map_apply S

/-- Ball evaluation: `μ'(P(T z, r)) = ρ^{-k} ν(P(z, ρ r))`. -/
theorem fbfb5_rescaledSource_ball {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (q : Space n)
    (ρ : ℝ) (hρ : 0 < ρ) (z : Space n) (r : ℝ) :
    rescaledSource ν k q ρ hρ (Metric.ball (similarity q ρ hρ z) r) =
      (ENNReal.ofReal ρ)⁻¹ ^ k * ν (Metric.ball z (ρ * r)) := by
  rw [fbfb5_rescaledSource_apply, preimage_similarity_ball]

/-- The similarity sends its centre to the origin (restates `similarity_self`). -/
theorem fbfb5_similarity_self {n : ℕ} (q : Space n) (ρ : ℝ) (hρ : 0 < ρ) :
    similarity q ρ hρ q = point 0 0 := by
  simp [similarity_apply]

/-- Pointwise density-ratio identity: `densityRatio μ' k (T z) r = densityRatio ν k z (ρ r)`. -/
theorem fbfb5_densityRatio_similarity {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (q : Space n)
    (ρ : ℝ) (hρ : 0 < ρ) (z : Space n) (r : ℝ) :
    densityRatio (rescaledSource ν k q ρ hρ) k (similarity q ρ hρ z) r =
      densityRatio ν k z (ρ * r) := by
  have h0 : ENNReal.ofReal ρ ^ k ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hρ).ne'
  have ht : ENNReal.ofReal ρ ^ k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  simp only [densityRatio, fbfb5_rescaledSource_ball, div_eq_mul_inv, ENNReal.ofReal_mul hρ.le,
    mul_pow]
  rw [ENNReal.mul_inv (Or.inl h0) (Or.inl ht)]
  simp only [ENNReal.inv_pow]
  ring

/-- The positive dilation `r ↦ ρ r` maps `𝓝[>] 0` onto itself. -/
theorem fbfb5_map_mul_nhdsGT_zero {ρ : ℝ} (hρ : 0 < ρ) :
    Filter.map (fun r : ℝ => ρ * r) (nhdsWithin (0 : ℝ) (Ioi 0)) = nhdsWithin (0 : ℝ) (Ioi 0) := by
  conv_lhs => rw [← comap_mulLeft_nhdsGT_zero hρ]
  exact Filter.map_comap_of_surjective (fun y => ⟨y / ρ, mul_div_cancel₀ y hρ.ne'⟩) _

/-- Scale invariance of the lower density: `Θ_*^k(μ', T z) = Θ_*^k(ν, z)`. -/
theorem fbfb5_lowerDensity_similarity {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (q : Space n)
    (ρ : ℝ) (hρ : 0 < ρ) (z : Space n) :
    lowerDensity (rescaledSource ν k q ρ hρ) k (similarity q ρ hρ z) = lowerDensity ν k z := by
  have hfun : densityRatio (rescaledSource ν k q ρ hρ) k (similarity q ρ hρ z) =
      densityRatio ν k z ∘ fun r : ℝ => ρ * r :=
    funext fun r => fbfb5_densityRatio_similarity ν k q ρ hρ z r
  unfold lowerDensity
  rw [hfun, Filter.liminf, Filter.liminf, ← Filter.map_map, fbfb5_map_mul_nhdsGT_zero hρ]

/-- The lower density bound transfers to the rescaled source almost everywhere
(`fbgrowth_rescaled_lowerDensity_ae`). -/
theorem fbgrowth_rescaled_lowerDensity_ae_proof {n : ℕ} (ν : Measure (Space n)) (k : ℕ)
    (q : Space n) (ρ : ℝ) (hρ : 0 < ρ) (A : ℝ)
    (h : ∀ᵐ z ∂ν, lowerDensity ν k z ≤ ENNReal.ofReal A) :
    ∀ᵐ w ∂(rescaledSource ν k q ρ hρ),
      lowerDensity (rescaledSource ν k q ρ hρ) k w ≤ ENNReal.ofReal A := by
  rw [ae_iff, fbfb5_rescaledSource_apply]
  have hpre : similarity q ρ hρ ⁻¹'
      {w | ¬ lowerDensity (rescaledSource ν k q ρ hρ) k w ≤ ENNReal.ofReal A} =
      {z | ¬ lowerDensity ν k z ≤ ENNReal.ofReal A} := by
    ext z
    simp only [mem_preimage, mem_ofPred_eq, fbfb5_lowerDensity_similarity]
  rw [hpre, ae_iff.mp h, mul_zero]

/-- The square-energy threshold transfers to the rescaled source
(`fbgrowth_rescaled_threshold`). -/
theorem fbgrowth_rescaled_threshold_proof {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) (T : FamilyKind) (ν : Measure (Space n)) (q : Space n) (ρ : ℝ)
    (hρ : 0 < ρ) (m R : ℝ) (hρR : 2 * ρ ≤ R)
    (h : ∀ᵐ z ∂ν, squareEnergy ν k T R z ≤ ENNReal.ofReal m) :
    rescaledSource ν k q ρ hρ (Metric.ball (point 0 0) 1 ∩
      {z | ENNReal.ofReal m < squareEnergy (rescaledSource ν k q ρ hρ) k T 2 z}) ≤
        ENNReal.ofReal 0 := by
  have hnull : ν {z | ENNReal.ofReal m < squareEnergy ν k T R z} = 0 := by
    have h' := ae_iff.mp h
    simpa only [not_le] using h'
  have hsub : similarity q ρ hρ ⁻¹' (Metric.ball (point 0 0) 1 ∩
      {z | ENNReal.ofReal m < squareEnergy (rescaledSource ν k q ρ hρ) k T 2 z}) ⊆
      {z | ENNReal.ofReal m < squareEnergy ν k T R z} := by
    intro z hz
    have h2 : ENNReal.ofReal m <
        squareEnergy (rescaledSource ν k q ρ hρ) k T 2 (similarity q ρ hρ z) := hz.2
    rw [squareEnergy_rescaledSource_eq_proof n hn k hk hkn T ν q ρ hρ 2 two_pos,
      Homeomorph.symm_apply_apply] at h2
    have hmono : squareEnergy ν k T (ρ * 2) z ≤ squareEnergy ν k T R z := by
      unfold squareEnergy
      exact lintegral_mono_set (Ioo_subset_Ioo_right (by linarith))
    exact lt_of_lt_of_le h2 hmono
  rw [fbfb5_rescaledSource_apply, measure_mono_null hsub hnull, mul_zero]
  exact bot_le

/-- The mass of a ball equals the rescaled mass of the unit ball (`fbgrowth_ball_eq_rescaled`). -/
theorem fbgrowth_ball_eq_rescaled_proof {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (q : Space n)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ν (Metric.ball q ρ) =
      ENNReal.ofReal ρ ^ k * rescaledSource ν k q ρ hρ (Metric.ball (point 0 0) 1) := by
  have h0 : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.mpr hρ).ne'
  rw [← fbfb5_similarity_self q ρ hρ, fbfb5_rescaledSource_ball, mul_one, ← mul_assoc,
    ← mul_pow, ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top, one_pow, one_mul]

end ParabolicRectifiability.Foundations
