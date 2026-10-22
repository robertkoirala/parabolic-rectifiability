import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry
import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Characterization.Proofs.Fourier.EstimateStatements
import ParabolicRectifiability.Foundations.Statements.Ambient
import ParabolicRectifiability.Foundations.Proofs.Similarity.HalfTimeCovariance

/-! # Dilation covariance on the standard base

Proof of `ba1_standard_dilation` (dilation part of the half-time derivative covariance).

For `ρ > 0`, `δ_ρ = dilate ρ`, `F_ρ = ρ⁻¹ F ∘ δ_ρ` and `f_ρ = f ∘ δ_ρ`:

* `b1dil_lipschitzWith`: `d(δ_ρ p, δ_ρ q) = ρ d(p,q)` (`dist_dilate`), so `F_ρ` keeps the
  Lipschitz constant.
* `b1dil_hasStandardParabolicBMOBound`: `δ_ρ⁻¹ P(δ_ρ p, ρ r) = P(p, r)` and
  `(δ_ρ)_# L = ρ^{-(m+2)} L` (`map_dilate_parabolicVolume`), so
  `∫_{P(p,r)} g ∘ δ_ρ = ρ^{-(m+2)} ∫_{P(δ_ρ p, ρ r)} g` and
  `L(P(p,r)) = ρ^{-(m+2)} L(P(δ_ρ p, ρ r))`: ball averages and mean oscillations of `f_ρ` at
  `(p, r)` are those of `f` at `(δ_ρ p, ρ r)`; local integrability transfers through the
  homeomorphism `δ_ρ`.
* `b1dil_representsStandardHalfTimeDerivative`: the representation is read in ordinary
  coordinates through `fourierToParabolic m`, where `δ_ρ` is `(u,t) ↦ (ρu, ρ²t)`. This is the
  dilation stage `fsim_representsHomogeneousHalfTimeDerivative_dilation_proof` of the similarity
  covariance of the half-time derivative, applied with `R = ρ⁻¹`. That proof carries out the
  route of the statement docstring:
  test `φ ∘ δ_{1/ρ}`, the a.e. kernel covariance
  `|D_t|^{1/2}(φ ∘ δ_{1/ρ}) = ρ⁻¹ (|D_t|^{1/2} φ) ∘ δ_{1/ρ}`, the window identity
  `Window(F_ρ, φ, T) = ρ^{-(m+2)} Window(F, φ ∘ δ_{1/ρ}, ρ² T)` on symmetric windows, and
  `∫ f_ρ φ = ρ^{-(m+2)} ∫ f (φ ∘ δ_{1/ρ})`. No time translation occurs, so no bracket integrability is used.

Helpers carry the prefix `b1dil_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-! ## (1) Lipschitz constants -/

/-- `F_ρ = ρ⁻¹ F ∘ δ_ρ` has the Lipschitz constant of `F`. -/
theorem b1dil_lipschitzWith {m : ℕ} {F : Space m → ℝ} {L : ℝ≥0} {ρ : ℝ} (hρ : 0 < ρ)
    (hF : LipschitzWith L F) : LipschitzWith L (fun p => ρ⁻¹ * F (dilate ρ p)) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have h1 : dist (F (dilate ρ p)) (F (dilate ρ q)) ≤ L * dist (dilate ρ p) (dilate ρ q) :=
    hF.dist_le_mul _ _
  rw [dist_dilate ρ hρ.le] at h1
  show dist (ρ⁻¹ * F (dilate ρ p)) (ρ⁻¹ * F (dilate ρ q)) ≤ L * dist p q
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hρ), ← Real.dist_eq]
  calc ρ⁻¹ * dist (F (dilate ρ p)) (F (dilate ρ q))
      ≤ ρ⁻¹ * (L * (ρ * dist p q)) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hρ.le)
    _ = L * dist p q * (ρ⁻¹ * ρ) := by ring
    _ = L * dist p q := by rw [inv_mul_cancel₀ hρ.ne', mul_one]

/-! ## (2) Parabolic BMO bounds -/

/-- `δ_ρ⁻¹ P(δ_ρ p, ρ r) = P(p, r)`. -/
theorem b1dil_preimage_ball {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (p : Space m) (r : ℝ) :
    dilate ρ ⁻¹' Metric.ball (dilate ρ p) (ρ * r) = Metric.ball p r := by
  ext q
  simp only [mem_preimage, Metric.mem_ball, dist_dilate ρ hρ.le]
  exact ⟨fun h => lt_of_mul_lt_mul_left h hρ.le, fun h => mul_lt_mul_of_pos_left h hρ⟩

/-- The volume factor `c = ρ^{-(m+2)}` of `(δ_ρ)_# L = c L`, as a real number. -/
theorem b1dil_factor_toReal {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    ((ENNReal.ofReal ρ)⁻¹ ^ (m + 2)).toReal = ρ⁻¹ ^ (m + 2) := by
  rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofReal hρ.le]

theorem b1dil_factor_toReal_ne_zero {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    ((ENNReal.ofReal ρ)⁻¹ ^ (m + 2)).toReal ≠ 0 := by
  rw [b1dil_factor_toReal hρ]
  exact pow_ne_zero _ (inv_ne_zero hρ.ne')

theorem b1dil_factor_ne_top {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    (ENNReal.ofReal ρ)⁻¹ ^ (m + 2) ≠ ⊤ :=
  ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hρ))

/-- `L(P(p,r)) = ρ^{-(m+2)} L(P(δ_ρ p, ρ r))`. -/
theorem b1dil_measure_ball {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (p : Space m) (r : ℝ) :
    parabolicVolume m (Metric.ball p r) =
      (ENNReal.ofReal ρ)⁻¹ ^ (m + 2) * parabolicVolume m (Metric.ball (dilate ρ p) (ρ * r)) := by
  rw [← b1dil_preimage_ball hρ p r, ← Measure.map_apply (measurable_dilate ρ) measurableSet_ball,
    map_dilate_parabolicVolume ρ hρ, Measure.smul_apply, smul_eq_mul]

/-- `∫_{P(p,r)} g ∘ δ_ρ = ρ^{-(m+2)} ∫_{P(δ_ρ p, ρ r)} g`, for every real `g`. -/
theorem b1dil_setIntegral_ball {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (g : Space m → ℝ) (p : Space m)
    (r : ℝ) :
    ∫ q in Metric.ball p r, g (dilate ρ q) ∂parabolicVolume m =
      ((ENNReal.ofReal ρ)⁻¹ ^ (m + 2)).toReal *
        ∫ w in Metric.ball (dilate ρ p) (ρ * r), g w ∂parabolicVolume m := by
  have he : MeasurableEmbedding (dilate ρ : Space m → Space m) :=
    (dilationMeasurableEquiv m ρ hρ).measurableEmbedding
  rw [← b1dil_preimage_ball hρ p r, ← he.setIntegral_map g, map_dilate_parabolicVolume ρ hρ,
    Measure.restrict_smul, integral_smul_measure, smul_eq_mul]

/-- Local integrability with respect to a finite multiple of a measure. -/
theorem b1dil_locallyIntegrable_smul {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {g : X → ℝ} {μ : Measure X} (hg : LocallyIntegrable g μ) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    LocallyIntegrable g (c • μ) := by
  intro x
  obtain ⟨U, hU, h⟩ := hg x
  refine ⟨U, hU, ?_⟩
  change Integrable g ((c • μ).restrict U)
  rw [Measure.restrict_smul]
  exact h.smul_measure hc

/-- `f ∘ δ_ρ` is locally integrable when `f` is. -/
theorem b1dil_locallyIntegrable {m : ℕ} {f : Space m → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : LocallyIntegrable f (parabolicVolume m)) :
    LocallyIntegrable (fun p => f (dilate ρ p)) (parabolicVolume m) := by
  have hf' : LocallyIntegrable f
      (Measure.map (dilationHomeomorph m ρ hρ) (parabolicVolume m)) := by
    have hmap : Measure.map (dilationHomeomorph m ρ hρ) (parabolicVolume m) =
        (ENNReal.ofReal ρ)⁻¹ ^ (m + 2) • parabolicVolume m :=
      map_dilate_parabolicVolume ρ hρ
    rw [hmap]
    exact b1dil_locallyIntegrable_smul hf (b1dil_factor_ne_top hρ)
  exact (locallyIntegrable_map_homeomorph (dilationHomeomorph m ρ hρ)).mp hf'

/-- Ball averages: `(f ∘ δ_ρ)_{P(p,r)} = f_{P(δ_ρ p, ρ r)}`. -/
theorem b1dil_standardBallAverage {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (f : Space m → ℝ) (p : Space m)
    (r : ℝ) :
    standardBallAverage m (fun q => f (dilate ρ q)) p r =
      standardBallAverage m f (dilate ρ p) (ρ * r) := by
  have hc0 := b1dil_factor_toReal_ne_zero (m := m) hρ
  have h1 : standardBallAverage m (fun q => f (dilate ρ q)) p r =
      ((parabolicVolume m (Metric.ball p r)).toReal)⁻¹ *
        ∫ q in Metric.ball p r, f (dilate ρ q) ∂parabolicVolume m := rfl
  have h2 : standardBallAverage m f (dilate ρ p) (ρ * r) =
      ((parabolicVolume m (Metric.ball (dilate ρ p) (ρ * r))).toReal)⁻¹ *
        ∫ w in Metric.ball (dilate ρ p) (ρ * r), f w ∂parabolicVolume m := rfl
  rw [h1, h2, b1dil_measure_ball hρ p r, b1dil_setIntegral_ball hρ f p r, ENNReal.toReal_mul,
    mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hc0, one_mul]

/-- A real parabolic BMO bound `B` of `f` is one of `f ∘ δ_ρ`. -/
theorem b1dil_hasStandardParabolicBMOBound {m : ℕ} {f : Space m → ℝ} {B ρ : ℝ} (hρ : 0 < ρ)
    (h : HasStandardParabolicBMOBound m f B) :
    HasStandardParabolicBMOBound m (fun p => f (dilate ρ p)) B := by
  obtain ⟨hB, hloc, hosc⟩ := h
  refine ⟨hB, b1dil_locallyIntegrable hρ hloc, fun p r hr => ?_⟩
  have hc0 := b1dil_factor_toReal_ne_zero (m := m) hρ
  show (∫ q in Metric.ball p r,
      ‖f (dilate ρ q) - standardBallAverage m (fun q => f (dilate ρ q)) p r‖
        ∂parabolicVolume m) / (parabolicVolume m (Metric.ball p r)).toReal ≤ B
  rw [b1dil_standardBallAverage hρ f p r,
    b1dil_setIntegral_ball hρ (fun w => ‖f w - standardBallAverage m f (dilate ρ p) (ρ * r)‖) p r,
    b1dil_measure_ball hρ p r, ENNReal.toReal_mul, mul_div_mul_left _ _ hc0]
  exact hosc (dilate ρ p) (ρ * r) (mul_pos hρ hr)

/-! ## (3) The half-time derivative representation -/

/-- In ordinary coordinates `δ_ρ` is `(u,t) ↦ (ρu, ρ²t)`. -/
theorem b1dil_dilate_fourierToParabolic {m : ℕ} (ρ : ℝ) (x : FourierSpace m) :
    dilate ρ (fourierToParabolic m x) =
      fourierToParabolic m (WithLp.toLp 2 (ρ • (WithLp.ofLp x).1, ρ ^ 2 * (WithLp.ofLp x).2)) :=
  rfl

/-- If `f` represents the homogeneous half-time derivative of `F` on the standard base, then
`f ∘ δ_ρ` represents that of `ρ⁻¹ F ∘ δ_ρ`: the dilation stage of the similarity covariance with `R = ρ⁻¹`. -/
theorem b1dil_representsStandardHalfTimeDerivative {m : ℕ} {F f : Space m → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (h : RepresentsStandardHalfTimeDerivative m F f) :
    RepresentsStandardHalfTimeDerivative m (fun p => ρ⁻¹ * F (dilate ρ p))
      (fun p => f (dilate ρ p)) := by
  have key := fsim_representsHomogeneousHalfTimeDerivative_dilation_proof ρ⁻¹ (inv_pos.mpr hρ)
    (fun x => F (fourierToParabolic m x)) (fun x => f (fourierToParabolic m x)) h
  simp only [inv_inv] at key
  unfold RepresentsStandardHalfTimeDerivative
  simp only [b1dil_dilate_fourierToParabolic]
  exact key

/-! ## The statement -/

/-- **Dilation covariance on the standard base** (`ba1_standard_dilation`): exact type of
`ba1_standard_dilation`. -/
theorem ba1_standard_dilation_proof :
    ∀ (m : ℕ) (F f : Space m → ℝ) (L : ℝ≥0) (B ρ : ℝ), 0 < ρ →
      (LipschitzWith L F → LipschitzWith L (fun p => ρ⁻¹ * F (dilate ρ p))) ∧
      (HasStandardParabolicBMOBound m f B →
        HasStandardParabolicBMOBound m (fun p => f (dilate ρ p)) B) ∧
      (RepresentsStandardHalfTimeDerivative m F f →
        RepresentsStandardHalfTimeDerivative m (fun p => ρ⁻¹ * F (dilate ρ p))
          (fun p => f (dilate ρ p))) := by
  intro m F f L B ρ hρ
  exact ⟨b1dil_lipschitzWith hρ, b1dil_hasStandardParabolicBMOBound hρ,
    b1dil_representsStandardHalfTimeDerivative hρ⟩

end ParabolicRectifiability.QuantitativeCharacterization
