import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Analysis.FourierAffine.Estimate
import ParabolicRectifiability.Analysis.HalfTimeDerivative.TailOscillation
import ParabolicRectifiability.Analysis.MeanOscillation
import ParabolicRectifiability.Analysis.RegularExtension.AffineCutoff.AffineEnergyCutoff
import ParabolicRectifiability.Analysis.RegularExtension.ComponentError
import ParabolicRectifiability.Analysis.RegularExtension.LocalDecomposition
import ParabolicRectifiability.Analysis.RegularExtension.LocalGluing

/-! # Half-time derivative of a function with affine Carleson bound is in BMO

`halfTimeBMO_of_affineCarleson_proof` shows that a compactly supported parabolically Lipschitz
function whose affine errors satisfy a Carleson bound has half-time derivative in parabolic BMO,
with a constant depending only on the dimensions. The proof assembles three ingredients:

* the cutoff estimate `affineEnergy_cutoff_le_proof` (localization of the affine energy);
* the local decomposition `exists_local_halfTime_decomposition_of_scalar_of_component`
  (`LocalDecomposition`), applied with the coordinate estimate
  `affineErrorSq_component_le_proof` (`ComponentError`);
* the gluing of local representatives `exists_halfTime_representative_of_local_proof`
  (`LocalGluing`).

The auxiliary statements `repHalf_add_of_subset_proof` (linearity of the half-time
representation) and `exists_scalar_local_halfTime_decomposition_proof` (the scalar local
decomposition at the origin) are proved along the way.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability

open HalfTimeDerivative in
/-- Linearity of the half-time representation. -/
theorem repHalf_add_of_subset_proof {m : ℕ} {H₁ H₂ g₁ g₂ : FourierSpace m → ℝ}
    (h₁ : MemLp H₁ 2 volume) (h₂ : MemLp H₂ 2 volume) {Ω₁ Ω₂ Ω : Set (FourierSpace m)}
    (hr₁ : RepHalf h₁ g₁ Ω₁) (hr₂ : RepHalf h₂ g₂ Ω₂) (hΩ : IsOpen Ω)
    (hΩ₁ : Ω ⊆ Ω₁) (hΩ₂ : Ω ⊆ Ω₂) :
    RepHalf (h₁.add h₂) (fun x => g₁ x + g₂ x) Ω := by
  refine ⟨hΩ, (hr₁.2.1.mono_set hΩ₁).add (hr₂.2.1.mono_set hΩ₂), fun φ hφ hc hs => ?_⟩
  obtain ⟨i₁H, i₁g⟩ := repHalf_test_integrable h₁ hr₁ φ hφ hc (hs.trans hΩ₁)
  obtain ⟨i₂H, i₂g⟩ := repHalf_test_integrable h₂ hr₂ φ hφ hc (hs.trans hΩ₂)
  have e₁ := hr₁.2.2 φ hφ hc (hs.trans hΩ₁)
  have e₂ := hr₂.2.2 φ hφ hc (hs.trans hΩ₂)
  calc (∫ x, (((H₁ + H₂) x : ℝ) : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x)
      = ∫ x, ((H₁ x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x +
          (H₂ x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Pi.add_apply, Complex.ofReal_add]
        ring
    _ = (∫ x, (H₁ x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x) +
          ∫ x, (H₂ x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x :=
        integral_add i₁H i₂H
    _ = (∫ x, (g₁ x : ℂ) * (φ x : ℂ)) + ∫ x, (g₂ x : ℂ) * (φ x : ℂ) := by rw [e₁, e₂]
    _ = ∫ x, ((g₁ x + g₂ x : ℝ) : ℂ) * (φ x : ℂ) := by
        rw [← integral_add i₁g i₂g]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Complex.ofReal_add]
        ring

/-- Scalar local decomposition at the origin, using the cutoff estimate
`affineEnergy_cutoff_le_proof`. -/
theorem exists_scalar_local_halfTime_decomposition_proof (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : FourierSpace m → ℝ) (L B R : ℝ), 0 ≤ L → 0 < R → HasCompactSupport F →
        HalfTimeDerivative.ParabolicLipschitz F L →
        HasAffineCarlesonBound (parabolicVolume m) (fun z => F ((fourierToParabolic m).symm z)) B →
        ∃ (hF : MemLp F 2 volume) (a b : FourierSpace m → ℝ),
          HalfTimeDerivative.RepHalf hF (fun x => a x + b x)
            (analyticCylinder (point (0 : Spatial m) 0) R) ∧
          MemLp a 2 volume ∧
          ∫⁻ x, ‖a x‖ₑ ^ 2 ≤ ENNReal.ofReal (C * (B + L ^ 2) * R ^ (m + 2)) ∧
          ∀ (u v : Spatial m) (t t₀ : ℝ), ‖u‖ < R → ‖v‖ < R → |t| < R ^ 2 → |t₀| < R ^ 2 →
            |b (WithLp.toLp 2 (u, t)) - b (WithLp.toLp 2 (v, t₀))| ≤ C * L := by
  obtain ⟨Cχ, C₁₁, hCχ, hC₁₁, hA11⟩ := affineEnergy_cutoff_le_proof m
  obtain ⟨C₁₀, hA10⟩ := FourierAffine.exists_halfTime_representative m
  have hT0 : 0 < HalfTimeDerivative.tailOscillationConstant Cχ :=
    HalfTimeDerivative.tailOscillationConstant_pos hCχ
  refine ⟨(C₁₀ : ℝ) * C₁₁ + HalfTimeDerivative.tailOscillationConstant Cχ,
    add_nonneg (mul_nonneg C₁₀.coe_nonneg hC₁₁) hT0.le, ?_⟩
  intro F L B R hL hR hc hF hcarl
  have hB : 0 ≤ B := hcarl.1
  obtain ⟨χ, hχ, hen⟩ := hA11 R hR
  have henergy := hen F L B hL hF hcarl
  have hFm : MemLp F 2 volume := (hF.continuous hL).memLp_of_hasCompactSupport hc
  have hTm := HalfTimeDerivative.memLp_tailRemainder hF hL hR hc hχ
  have hhm : MemLp (fun x => χ x * (F x - HalfTimeDerivative.tailMean F R)) 2 volume := by
    have h := hFm.sub hTm
    convert h using 1
    funext x
    simp only [Pi.sub_apply, HalfTimeDerivative.tailRemainder]
    ring
  obtain ⟨_hA, g, hg, -, -, hrepg, hgL2⟩ :=
    hA10 (fun x => χ x * (F x - HalfTimeDerivative.tailMean F R)) hhm
      (lt_of_le_of_lt henergy ENNReal.ofReal_lt_top)
  have hrepT := HalfTimeDerivative.repHalf_oscillationTail hF hL hR hc hχ
  have hsum := repHalf_add_of_subset_proof hhm hTm hrepg hrepT hrepT.1 (subset_univ _) subset_rfl
  have hrep : HalfTimeDerivative.RepHalf hFm
      (fun x => g x + HalfTimeDerivative.oscillationTail F χ R (WithLp.ofLp x).1
        (WithLp.ofLp x).2) (analyticCylinder (point (0 : Spatial m) 0) R) := by
    refine (HalfTimeDerivative.repHalf_congr (hhm.add hTm) hFm ?_ Filter.EventuallyEq.rfl).1 hsum
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [Pi.add_apply, HalfTimeDerivative.tailRemainder]
    ring
  refine ⟨hFm, g, fun x => HalfTimeDerivative.oscillationTail F χ R (WithLp.ofLp x).1
    (WithLp.ofLp x).2, hrep, hg, ?_, ?_⟩
  · have hX : 0 ≤ (B + L ^ 2) * R ^ (m + 2) :=
      mul_nonneg (add_nonneg hB (sq_nonneg L)) (pow_nonneg hR.le _)
    calc ∫⁻ x, ‖g x‖ₑ ^ 2
        ≤ (C₁₀ : ℝ≥0∞) * ENNReal.ofReal (C₁₁ * (B + L ^ 2) * R ^ (m + 2)) :=
          hgL2.trans (mul_le_mul_right henergy _)
      _ = ENNReal.ofReal ((C₁₀ : ℝ) * (C₁₁ * (B + L ^ 2) * R ^ (m + 2))) := by
          rw [ENNReal.ofReal_mul C₁₀.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      _ ≤ ENNReal.ofReal (((C₁₀ : ℝ) * C₁₁ + HalfTimeDerivative.tailOscillationConstant Cχ) *
            (B + L ^ 2) * R ^ (m + 2)) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : (C₁₀ : ℝ) * (C₁₁ * (B + L ^ 2) * R ^ (m + 2)) =
              ((C₁₀ : ℝ) * C₁₁) * ((B + L ^ 2) * R ^ (m + 2)) := by ring
          have h2 : ((C₁₀ : ℝ) * C₁₁ + HalfTimeDerivative.tailOscillationConstant Cχ) *
              (B + L ^ 2) * R ^ (m + 2) =
              ((C₁₀ : ℝ) * C₁₁ + HalfTimeDerivative.tailOscillationConstant Cχ) *
                ((B + L ^ 2) * R ^ (m + 2)) := by ring
          rw [h1, h2]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hT0.le) hX
  · intro u v t t₀ hu hv ht ht₀
    have h := HalfTimeDerivative.oscillationTail_le hF hL hR hc hχ hCχ hu hv ht ht₀
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hL)
    exact le_add_of_nonneg_left (mul_nonneg C₁₀.coe_nonneg hC₁₁)

/-- **`halfTimeBMO_of_affineCarleson`**: the affine-Carleson half-time BMO estimate. It follows
from the scalar local decomposition (using the coordinate estimate) and the gluing of local
half-time representatives. -/
theorem halfTimeBMO_of_affineCarleson_proof (m d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (W : Submodule ℝ (Spatial n)),
      Module.finrank ℝ W = m → Module.finrank ℝ W.orthogonal = d →
      ∀ (F : SubspaceSpace W → W.orthogonal) (L : ℝ≥0) (B : ℝ),
        HasCompactSupport F → LipschitzWith L F →
        HasAffineCarlesonBound (intrinsicParabolicVolume W) F B →
        ∃ g : SubspaceSpace W → W.orthogonal,
          RepresentsHalfTimeDerivative W F g ∧
            HasParabolicBMOBound W g (C * ((L : ℝ) + Real.sqrt B)) := by
  obtain ⟨Cs, hCs, hs⟩ := exists_scalar_local_halfTime_decomposition_proof m
  obtain ⟨C', hC', hloc⟩ := exists_local_halfTime_decomposition_of_scalar_of_component
    affineErrorSq_component_le_proof m d Cs hCs hs
  refine ⟨3 * C' + 1, by linarith, ?_⟩
  intro n W hm hd F L B hc hF hcarl
  obtain ⟨g, hrep, hli, huniq⟩ := exists_halfTime_representative_of_local_proof W F
    (fun p r hr => by
      obtain ⟨a, b, hab, -⟩ := hloc W hm hd F L B hc hF hcarl p r hr
      exact ⟨fun x => a x + b x, hab⟩)
  have hLB : 0 ≤ (L : ℝ) + Real.sqrt B := add_nonneg L.coe_nonneg (Real.sqrt_nonneg B)
  refine ⟨g, hrep, mul_nonneg (by linarith) hLB, hli, fun p r hr => ?_⟩
  obtain ⟨a, b, hab, ha, haL2, hb, hpair⟩ := hloc W hm hd F L B hc hF hcarl p r hr
  have hgab := huniq p r hr _ hab
  have hosc := parabolicBall_meanOscillation_le_L2_add W p hr ha hb hgab
    (mul_nonneg hC' L.coe_nonneg) hpair
  have hvol := intrinsicBall_volume_pos_lt_top W p hr
  have hV : 0 < (intrinsicParabolicVolume W).real (Metric.ball p r) :=
    ENNReal.toReal_pos hvol.1.ne' hvol.2.ne
  have hX : 0 ≤ C' * ((L : ℝ) + Real.sqrt B) := mul_nonneg hC' hLB
  have hVV : (intrinsicParabolicVolume W).real (Metric.ball p r) ^ (-1 / 2 : ℝ) *
      Real.sqrt ((intrinsicParabolicVolume W).real (Metric.ball p r)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hV]
    norm_num
  have hsI : Real.sqrt (∫ x in Metric.ball p r, ‖a x‖ ^ 2 ∂intrinsicParabolicVolume W) ≤
      C' * ((L : ℝ) + Real.sqrt B) *
        Real.sqrt ((intrinsicParabolicVolume W).real (Metric.ball p r)) := by
    calc Real.sqrt (∫ x in Metric.ball p r, ‖a x‖ ^ 2 ∂intrinsicParabolicVolume W)
        ≤ Real.sqrt ((C' * ((L : ℝ) + Real.sqrt B)) ^ 2 *
            (intrinsicParabolicVolume W).real (Metric.ball p r)) := Real.sqrt_le_sqrt haL2
      _ = C' * ((L : ℝ) + Real.sqrt B) *
            Real.sqrt ((intrinsicParabolicVolume W).real (Metric.ball p r)) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hX]
  have hVn : 0 ≤ (intrinsicParabolicVolume W).real (Metric.ball p r) ^ (-1 / 2 : ℝ) :=
    Real.rpow_nonneg hV.le _
  have h2 : 2 * (intrinsicParabolicVolume W).real (Metric.ball p r) ^ (-1 / 2 : ℝ) *
      Real.sqrt (∫ x in Metric.ball p r, ‖a x‖ ^ 2 ∂intrinsicParabolicVolume W) ≤
      2 * (C' * ((L : ℝ) + Real.sqrt B)) := by
    calc 2 * (intrinsicParabolicVolume W).real (Metric.ball p r) ^ (-1 / 2 : ℝ) *
          Real.sqrt (∫ x in Metric.ball p r, ‖a x‖ ^ 2 ∂intrinsicParabolicVolume W)
        ≤ 2 * (intrinsicParabolicVolume W).real (Metric.ball p r) ^ (-1 / 2 : ℝ) *
            (C' * ((L : ℝ) + Real.sqrt B) *
              Real.sqrt ((intrinsicParabolicVolume W).real (Metric.ball p r))) :=
          mul_le_mul_of_nonneg_left hsI (mul_nonneg zero_le_two hVn)
      _ = 2 * (C' * ((L : ℝ) + Real.sqrt B)) *
            ((intrinsicParabolicVolume W).real (Metric.ball p r) ^ (-1 / 2 : ℝ) *
              Real.sqrt ((intrinsicParabolicVolume W).real (Metric.ball p r))) := by ring
      _ = 2 * (C' * ((L : ℝ) + Real.sqrt B)) := by rw [hVV, mul_one]
  have hCL : C' * (L : ℝ) ≤ C' * ((L : ℝ) + Real.sqrt B) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg B)) hC'
  have hexp : (3 * C' + 1) * ((L : ℝ) + Real.sqrt B) =
      3 * (C' * ((L : ℝ) + Real.sqrt B)) + ((L : ℝ) + Real.sqrt B) := by ring
  refine hosc.trans ?_
  rw [hexp]
  linarith

end ParabolicRectifiability
