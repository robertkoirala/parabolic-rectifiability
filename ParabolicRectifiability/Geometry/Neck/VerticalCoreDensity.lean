import ParabolicRectifiability.Geometry.Neck.ParabolicDensityHalf
import ParabolicRectifiability.Geometry.Neck.Conclusions
import ParabolicRectifiability.Geometry.Neck.CenterProperties
import ParabolicRectifiability.Metric.BaseVolume

/-!
# Vertical core density (vertical parameter space)

Positive lower density of the core's own Hausdorff measure for a vertical neck, as
`vertical_coreLowerDensity_of_parametrization_proof` (the type of
`vertical_coreLowerDensity_of_parametrization`).

* `nk5_ae_lowerDensity_image`: for a compact `A ⊆ ℝ^m × ℝ` and a globally defined map
  `Φ : Space m → Space n` that is `L`-Lipschitz and `L`-antilipschitz, the own Hausdorff
  measure `η = H^{m+2}_P ⌞ Φ(A)` satisfies `η(P(Φ p, r)) ≥ ½ L^{-2(m+2)} r^{m+2}` for all
  small `r` at every parabolic density point `p ∈ A`
  (`nk5_ae_parabolicVolume_density_half`); the remaining parameters form a volume-null set,
  whose image is Hausdorff-null (`parabolic_hausdorff_comparison` and the Lipschitz bound).
  This is the vertical analogue of `horizontalChart_ae_lowerDensity_proof`.
* The statement: `A₀ = A ∩ Φ⁻¹(𝒞₀)` is compact because the core is compact (`isCompact_core`,
  derived from the separation fields) and `Φ` is continuous; `Φ(A₀) = 𝒞 ∩ 𝒞₀ = 𝒞₀`;
  the parameter dimension is `(k - 2) + 2 = k` under the vertical guard `2 ≤ k`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

namespace NeckHubTree

universe u

/-- **Lower density on a parametrized vertical core.** Let `A ⊆ ℝ^m × ℝ` be compact and let
`Φ : Space m → Space n` be `L`-Lipschitz and `L`-antilipschitz for the parabolic metrics. Then
the own `k = m + 2`-dimensional Hausdorff measure of `Φ(A)` has positive lower `k`-density,
with explicit eventual radius bounds, at almost every point of `Φ(A)`. -/
theorem nk5_ae_lowerDensity_image {n m k : ℕ} (hk : m + 2 = k) {A : Set (Space m)}
    (hA : IsCompact A) {Φ : Space m → Space n} {L : ℝ≥0} (hL : 0 < L)
    (hΦ : LipschitzWith L Φ) (hΦ' : AntilipschitzWith L Φ) :
    ∀ᵐ z ∂(hausdorffP n k).restrict (Φ '' A), ∃ a r₀ : ℝ, 0 < a ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        ENNReal.ofReal (a * r ^ k) ≤ (hausdorffP n k).restrict (Φ '' A) (Metric.ball z r) := by
  subst hk
  classical
  have hLr : (0 : ℝ) < L := NNReal.coe_pos.2 hL
  have hℓ0 : (L : ℝ≥0∞) ≠ 0 := by exact_mod_cast hL.ne'
  have hℓt : (L : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have h2ω0 : (2 : ℝ≥0∞) * omega m ≠ 0 := mul_ne_zero two_ne_zero (omega_pos m).ne'
  have h2ωt : (2 : ℝ≥0∞) * omega m ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (omega_lt_top m).ne
  -- Parabolic density points of `A`.
  set D : Set (Space m) := {p | ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
    parabolicVolume m (Metric.ball p r) ≤ 2 * parabolicVolume m (A ∩ Metric.ball p r)}
  have hAm : MeasurableSet A := hA.isClosed.measurableSet
  have hN : parabolicVolume m (A \ D) = 0 := by
    have h := nk5_ae_parabolicVolume_density_half A
    rw [ae_restrict_iff' hAm, ae_iff] at h
    refine measure_mono_null ?_ h
    intro p hp h'
    exact hp.2 (h' hp.1)
  -- The non-density parameters have Hausdorff-null image.
  have hS : hausdorffP n (m + 2) (Φ '' (A \ D)) = 0 := by
    have h1 : hausdorffP m (m + 2) (A \ D) = 0 :=
      le_antisymm ((parabolic_hausdorff_comparison m (A \ D)).2.trans
        (by rw [hN, mul_zero])) zero_le
    have h2 := hΦ.hausdorffMeasure_image_le (d := ((m + 2 : ℕ) : ℝ)) (by positivity) (A \ D)
    rw [hausdorffP_eq] at h1
    rw [h1, mul_zero] at h2
    rw [hausdorffP_eq]
    exact le_antisymm h2 zero_le
  -- The image is compact, hence measurable.
  have hKm : MeasurableSet (Φ '' A) := (hA.image hΦ.continuous).isClosed.measurableSet
  -- Lower density at the image of a parabolic density point.
  have hgood : ∀ p ∈ A, p ∈ D → ∃ a r₀ : ℝ, 0 < a ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (a * r ^ (m + 2)) ≤
        (hausdorffP n (m + 2)).restrict (Φ '' A) (Metric.ball (Φ p) r) := by
    rintro p - ⟨r₀, hr₀, hdens⟩
    refine ⟨((L : ℝ)⁻¹) ^ (m + 2) * ((L : ℝ)⁻¹) ^ (m + 2) / 2, L * r₀,
      div_pos (mul_pos (pow_pos (inv_pos.2 hLr) _) (pow_pos (inv_pos.2 hLr) _)) two_pos,
      mul_pos hLr hr₀, fun r hr hrr => ?_⟩
    have hrL : 0 < r / L := div_pos hr hLr
    have hrL' : r / L ≤ r₀ := by
      rw [div_le_iff₀ hLr]
      linarith [mul_comm (L : ℝ) r₀]
    have hT : Φ '' (A ∩ Metric.ball p (r / L)) ⊆ Metric.ball (Φ p) r ∩ Φ '' A := by
      rintro _ ⟨b, hb, rfl⟩
      refine ⟨?_, mem_image_of_mem Φ hb.1⟩
      rw [Metric.mem_ball]
      calc dist (Φ b) (Φ p) ≤ L * dist b p := hΦ.dist_le_mul b p
        _ < L * (r / L) := mul_lt_mul_of_pos_left (Metric.mem_ball.1 hb.2) hLr
        _ = r := mul_div_cancel₀ r hLr.ne'
    -- Lower Hausdorff bound through the antilipschitz map.
    have hlow : hausdorffP m (m + 2) (A ∩ Metric.ball p (r / L)) ≤
        (L : ℝ≥0∞) ^ (m + 2) * hausdorffP n (m + 2) (Φ '' (A ∩ Metric.ball p (r / L))) := by
      have h := hΦ'.le_hausdorffMeasure_image (d := ((m + 2 : ℕ) : ℝ)) (by positivity)
        (A ∩ Metric.ball p (r / L))
      rw [ENNReal.rpow_natCast] at h
      rw [hausdorffP_eq, hausdorffP_eq]
      exact h
    have hcmp := (parabolic_hausdorff_comparison m (A ∩ Metric.ball p (r / L))).1
    have hd := hdens (r / L) hrL hrL'
    rw [parabolicVolume_ball p _ hrL] at hd
    -- Arithmetic: `x / 2 ≤ (2 ω)⁻¹ |A ∩ P_b(p, r/L)|` with `x = (r/L)^k`.
    have hx : ENNReal.ofReal (r / L) ^ (m + 2) / 2 ≤
        hausdorffP m (m + 2) (A ∩ Metric.ball p (r / L)) := by
      refine le_trans (ENNReal.div_le_of_le_mul ?_) hcmp
      calc ENNReal.ofReal (r / L) ^ (m + 2)
          = (2 * omega m)⁻¹ * (2 * omega m * ENNReal.ofReal (r / L) ^ (m + 2)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel h2ω0 h2ωt, one_mul]
        _ ≤ (2 * omega m)⁻¹ * (2 * parabolicVolume m (A ∩ Metric.ball p (r / L))) := by
            gcongr
        _ = (2 * omega m)⁻¹ * parabolicVolume m (A ∩ Metric.ball p (r / L)) * 2 := by ring
    have hval : ENNReal.ofReal (((L : ℝ)⁻¹) ^ (m + 2) * ((L : ℝ)⁻¹) ^ (m + 2) / 2 * r ^ (m + 2)) =
        ((L : ℝ≥0∞)⁻¹) ^ (m + 2) * (ENNReal.ofReal (r / L) ^ (m + 2) / 2) := by
      have : ((L : ℝ)⁻¹) ^ (m + 2) * ((L : ℝ)⁻¹) ^ (m + 2) / 2 * r ^ (m + 2) =
          ((L : ℝ)⁻¹) ^ (m + 2) * ((r / L) ^ (m + 2) / 2) := by
        rw [div_eq_mul_inv r, mul_pow]
        ring
      rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos two_pos,
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow hrL.le, ENNReal.ofReal_ofNat,
        ENNReal.ofReal_inv_of_pos hLr, ENNReal.ofReal_coe_nnreal]
    rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet, hval]
    calc ((L : ℝ≥0∞)⁻¹) ^ (m + 2) * (ENNReal.ofReal (r / L) ^ (m + 2) / 2)
        ≤ ((L : ℝ≥0∞)⁻¹) ^ (m + 2) * hausdorffP m (m + 2) (A ∩ Metric.ball p (r / L)) := by
          gcongr
      _ ≤ ((L : ℝ≥0∞)⁻¹) ^ (m + 2) * ((L : ℝ≥0∞) ^ (m + 2) *
            hausdorffP n (m + 2) (Φ '' (A ∩ Metric.ball p (r / L)))) := by
          gcongr
      _ = hausdorffP n (m + 2) (Φ '' (A ∩ Metric.ball p (r / L))) := by
          rw [← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel hℓ0 hℓt, one_pow, one_mul]
      _ ≤ hausdorffP n (m + 2) (Metric.ball (Φ p) r ∩ Φ '' A) := measure_mono hT
  -- Almost every image point is the image of a density point.
  rw [ae_restrict_iff' hKm]
  refine ae_iff.2 (measure_mono_null ?_ hS)
  intro z hz
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hz
  obtain ⟨⟨p, hpA, rfl⟩, hz⟩ := hz
  exact ⟨p, ⟨hpA, fun hpD => hz (hgood p hpA hpD)⟩, rfl⟩

/-- **Vertical core lower density:** if the center set of a vertical neck region has an exact vertical
parametrization with distortion `2`, then the core's own Hausdorff measure
`η = H^k_P ⌞ 𝒞₀` has positive lower `k`-density at `η`-almost every point. The type is
that of `vertical_coreLowerDensity_of_parametrization`. -/
theorem vertical_coreLowerDensity_of_parametrization_proof {n k : ℕ} {ι : Type u} {q : Space n}
    {R c₀ Cd Cs σ δ E κ θ γ : ℝ} (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ) :
    N.HasVerticalParametrization 2 →
      ∀ᵐ z ∂(hausdorffP n k).restrict N.core, ∃ a r₀ : ℝ, 0 < a ∧ 0 < r₀ ∧
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          ENNReal.ofReal (a * r ^ k) ≤ (hausdorffP n k).restrict N.core (Metric.ball z r) := by
  rintro ⟨G, A, hbi, hA, hrange⟩
  have hav : 2 ≤ k ∧ k ≤ n + 2 := N.available
  have hk : k - 2 + 2 = k := Nat.sub_add_cancel hav.1
  have hLip : LipschitzWith 2 (timePreservingMap G) := LipschitzWith.of_dist_le_mul fun p p' => by
    have h := (hbi p p').2
    push_cast
    exact h
  have hAnti : AntilipschitzWith 2 (timePreservingMap G) :=
    AntilipschitzWith.of_le_mul_dist fun p p' => by
      have h := (hbi p p').1
      push_cast
      linarith
  -- The compact core preimage `A₀ = A ∩ Φ⁻¹(𝒞₀)`, with image exactly the core.
  have hA₀ : IsCompact (A ∩ timePreservingMap G ⁻¹' N.core) :=
    hA.inter_right (N.isCompact_core.isClosed.preimage hLip.continuous)
  have himage : timePreservingMap G '' (A ∩ timePreservingMap G ⁻¹' N.core) = N.core := by
    rw [image_inter_preimage, hrange]
    exact inter_eq_self_of_subset_right N.core_subset_centers
  have h := nk5_ae_lowerDensity_image hk hA₀ two_pos hLip hAnti
  rw [himage] at h
  exact h

end NeckHubTree

end ParabolicRectifiability
