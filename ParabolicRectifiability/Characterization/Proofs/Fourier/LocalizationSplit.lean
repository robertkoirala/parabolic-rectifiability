import ParabolicRectifiability.Characterization.Proofs.Fourier.LocalizationLowPass
import ParabolicRectifiability.Characterization.Proofs.Fourier.LocalizationNear

/-! # Critical Sobolev localization: the decomposition and the near part

Part of the proof of `ba1_critical_sobolev_localization_proof`. With
`η = b1loc_cutoff`, `K = I - η * I`, `G = F ∘ Ψ`, `g = f ∘ Ψ`, `x₀ = Ψ⁻¹ p₀`,
`c = f_{P(p₀,10)}` (`standardBallAverage m f p₀ 10`) and `Ω = Ψ⁻¹ P(p₀,10)`:

* **decomposition** (`b1loc_decomposition`): almost everywhere,
  `G - F(p₀) = A + N + V∞` with the low-pass part `A = η *_t (G - F(p₀))`
  (`b1loc_lowPass`), the near part `N = K *_t w`, `w = 1_Ω (g - c)` (`b1loc_nearPart`), and the
  far part `V∞ = K *_t w∞`, `w∞ = 1_{Ωᶜ} (g - c)` (`b1loc_farPart`). It uses the high-pass identity in
  coordinates (`b1loc_highPass_coordinates`), `∫ η = 1` and `∫ K = 0`;
* **near input** (`b1loc_near_input`): `∫ |w|² = ∫_{P(p₀,10)} |f - c|² ≤ C_BMO B² |P(p₀,10)|`
  (clause 2 of `BMOGrowthStatement`, transported by `fourierToParabolic_measurePreserving`), so `w ∈ L²`;
  then `b1loc_near_estimate` with `C_K` of `b1loc_kernel_adapter` and the cutoff product rule
  give `χ_{x₀} N ∈ L²` and `b1loc_timeGagliardo (χ_{x₀} N) ≤ C B²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative

attribute [local instance] FourierAffine.continuousSMul_fourierSpace

variable {m : ℕ}

/-! ## The near set and the two parts of the BMO function -/

/-- `Ω = Ψ⁻¹ P(p₀,10)`. -/
def b1loc_nearSet (m : ℕ) (p₀ : Space m) : Set (FourierSpace m) :=
  fourierToParabolic m ⁻¹' Metric.ball p₀ 10

theorem b1loc_measurableSet_nearSet (p₀ : Space m) : MeasurableSet (b1loc_nearSet m p₀) :=
  (Metric.isOpen_ball.preimage (fourierToParabolic m).continuous).measurableSet

/-- `g - c` with `g = f ∘ Ψ` and `c = f_{P(p₀,10)}`. -/
def b1loc_meanFree (m : ℕ) (f : Space m → ℝ) (p₀ : Space m) (y : FourierSpace m) : ℝ :=
  f (fourierToParabolic m y) - standardBallAverage m f p₀ 10

/-- The near part `w = 1_Ω (g - c)`. -/
def b1loc_nearPart (m : ℕ) (f : Space m → ℝ) (p₀ : Space m) : FourierSpace m → ℝ :=
  (b1loc_nearSet m p₀).indicator (b1loc_meanFree m f p₀)

/-- The far part `w∞ = 1_{Ωᶜ} (g - c)`. -/
def b1loc_farPart (m : ℕ) (f : Space m → ℝ) (p₀ : Space m) : FourierSpace m → ℝ :=
  (b1loc_nearSet m p₀)ᶜ.indicator (b1loc_meanFree m f p₀)

theorem b1loc_aestronglyMeasurable_meanFree {f : Space m → ℝ} {B : ℝ}
    (hB : HasStandardParabolicBMOBound m f B) (p₀ : Space m) :
    AEStronglyMeasurable (b1loc_meanFree m f p₀) volume := by
  have h : AEStronglyMeasurable (fun y : FourierSpace m => f (fourierToParabolic m y)) volume :=
    hB.2.1.aestronglyMeasurable.comp_measurePreserving (fourierToParabolic_measurePreserving m)
  exact h.sub aestronglyMeasurable_const

theorem b1loc_aestronglyMeasurable_nearPart {f : Space m → ℝ} {B : ℝ}
    (hB : HasStandardParabolicBMOBound m f B) (p₀ : Space m) :
    AEStronglyMeasurable (b1loc_nearPart m f p₀) volume :=
  (b1loc_aestronglyMeasurable_meanFree hB p₀).indicator (b1loc_measurableSet_nearSet p₀)

theorem b1loc_aestronglyMeasurable_farPart {f : Space m → ℝ} {B : ℝ}
    (hB : HasStandardParabolicBMOBound m f B) (p₀ : Space m) :
    AEStronglyMeasurable (b1loc_farPart m f p₀) volume :=
  (b1loc_aestronglyMeasurable_meanFree hB p₀).indicator (b1loc_measurableSet_nearSet p₀).compl

/-- A time convolution of a.e. strongly measurable functions is a.e. strongly measurable. -/
theorem b1loc_aestronglyMeasurable_timeConvolution' {K : ℝ → ℝ}
    (hK : AEStronglyMeasurable K volume) {w : FourierSpace m → ℝ}
    (hw : AEStronglyMeasurable w volume) :
    AEStronglyMeasurable (fhp_timeConvolution K w) volume :=
  ((hK.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
    (b1loc_aestronglyMeasurable_shift hw)).integral_prod_right'

/-! ## The decomposition -/

/-- **Decomposition** `G - F(p₀) = A + N + V∞` almost everywhere. -/
theorem b1loc_decomposition (hK : HighPassKernelStatement) (hI : HighPassIdentityStatement)
    {F f : Space m → ℝ} {L : ℝ≥0} {B : ℝ} (hL : LipschitzWith L F)
    (hB : HasStandardParabolicBMOBound m f B) (hrep : RepresentsStandardHalfTimeDerivative m F f)
    (p₀ : Space m) :
    ∀ᵐ x ∂(volume : Measure (FourierSpace m)),
      F (fourierToParabolic m x) - F p₀ =
        b1loc_lowPass m F p₀ x +
          fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_nearPart m f p₀) x +
          fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀) x := by
  obtain ⟨h1, h2, h3⟩ := b1loc_highPass_coordinates hI b1loc_cutoff b1loc_cutoff_admissible m
    F f L B hL hB hrep
  obtain ⟨-, hKint, hK0, -⟩ := hK b1loc_cutoff b1loc_cutoff_admissible
  filter_upwards [h2, h3] with x hx2 hx3
  have hx3' : F (fourierToParabolic m x) -
      ∫ s : ℝ, b1loc_cutoff s * F (fourierToParabolic m (x - s • timeVector m)) =
      ∫ s : ℝ, fhp_highPassKernel b1loc_cutoff s *
        f (fourierToParabolic m (x - s • timeVector m)) := hx3
  -- the low-pass part
  have hA : b1loc_lowPass m F p₀ x =
      (∫ s : ℝ, b1loc_cutoff s * F (fourierToParabolic m (x - s • timeVector m))) - F p₀ := by
    rw [b1loc_lowPass_apply]
    simp only [mul_sub]
    rw [integral_sub (h1 x) ((b1loc_cutoff.integrable (μ := volume)).mul_const (F p₀)),
      integral_mul_const, b1loc_integral_cutoff_eq_one, one_mul]
  -- the high-pass part, with the mean subtracted
  have hKg : (∫ s : ℝ, fhp_highPassKernel b1loc_cutoff s *
        b1loc_meanFree m f p₀ (x - s • timeVector m)) =
      ∫ s : ℝ, fhp_highPassKernel b1loc_cutoff s *
        f (fourierToParabolic m (x - s • timeVector m)) := by
    simp only [b1loc_meanFree, mul_sub]
    rw [integral_sub hx2 (hKint.mul_const (standardBallAverage m f p₀ 10)), integral_mul_const,
      hK0, zero_mul, sub_zero]
  have hint : Integrable (fun s : ℝ => fhp_highPassKernel b1loc_cutoff s *
      b1loc_meanFree m f p₀ (x - s • timeVector m)) := by
    have h := hx2.sub (hKint.mul_const (standardBallAverage m f p₀ 10))
    refine h.congr (Eventually.of_forall fun s => ?_)
    simp only [Pi.sub_apply, b1loc_meanFree]
    ring
  have hSm : MeasurableSet ((fun s : ℝ => x - s • timeVector m) ⁻¹' b1loc_nearSet m p₀) :=
    (b1loc_measurableSet_nearSet p₀).preimage
      (measurable_const.sub (measurable_id.smul_const _))
  have hN : fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_nearPart m f p₀) x =
      ∫ s in (fun s : ℝ => x - s • timeVector m) ⁻¹' b1loc_nearSet m p₀,
        fhp_highPassKernel b1loc_cutoff s * b1loc_meanFree m f p₀ (x - s • timeVector m) := by
    rw [← integral_indicator hSm]
    show (∫ s : ℝ, fhp_highPassKernel b1loc_cutoff s *
      b1loc_nearPart m f p₀ (x - s • timeVector m)) = _
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    by_cases hs : x - s • timeVector m ∈ b1loc_nearSet m p₀
    · have hs' : s ∈ (fun s : ℝ => x - s • timeVector m) ⁻¹' b1loc_nearSet m p₀ := hs
      simp only [b1loc_nearPart, indicator_of_mem hs, indicator_of_mem hs']
    · have hs' : s ∉ (fun s : ℝ => x - s • timeVector m) ⁻¹' b1loc_nearSet m p₀ := hs
      simp only [b1loc_nearPart, indicator_of_notMem hs, indicator_of_notMem hs', mul_zero]
  have hV : fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀) x =
      ∫ s in ((fun s : ℝ => x - s • timeVector m) ⁻¹' b1loc_nearSet m p₀)ᶜ,
        fhp_highPassKernel b1loc_cutoff s * b1loc_meanFree m f p₀ (x - s • timeVector m) := by
    rw [← integral_indicator hSm.compl]
    show (∫ s : ℝ, fhp_highPassKernel b1loc_cutoff s *
      b1loc_farPart m f p₀ (x - s • timeVector m)) = _
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    by_cases hs : x - s • timeVector m ∈ b1loc_nearSet m p₀
    · have h1' : x - s • timeVector m ∉ (b1loc_nearSet m p₀)ᶜ := fun h => h hs
      have hs' : s ∉ ((fun s : ℝ => x - s • timeVector m) ⁻¹' b1loc_nearSet m p₀)ᶜ :=
        fun h => h hs
      simp only [b1loc_farPart, indicator_of_notMem h1', indicator_of_notMem hs', mul_zero]
    · have h1' : x - s • timeVector m ∈ (b1loc_nearSet m p₀)ᶜ := hs
      have hs' : s ∈ ((fun s : ℝ => x - s • timeVector m) ⁻¹' b1loc_nearSet m p₀)ᶜ := hs
      simp only [b1loc_farPart, indicator_of_mem h1', indicator_of_mem hs']
  rw [hA, hN, hV, add_assoc, integral_add_compl hSm hint, hKg, ← hx3']
  ring

/-! ## The near part -/

theorem b1loc_lintegral_nearPart_sq (f : Space m → ℝ) (p₀ : Space m) :
    ∫⁻ x, ‖b1loc_nearPart m f p₀ x‖ₑ ^ 2 =
      ∫⁻ q in Metric.ball p₀ 10, ‖f q - standardBallAverage m f p₀ 10‖ₑ ^ 2
        ∂parabolicVolume m := by
  have h1 : (fun x => ‖b1loc_nearPart m f p₀ x‖ₑ ^ 2) =
      (b1loc_nearSet m p₀).indicator (fun x => ‖b1loc_meanFree m f p₀ x‖ₑ ^ 2) := by
    funext x
    by_cases hx : x ∈ b1loc_nearSet m p₀
    · rw [b1loc_nearPart, indicator_of_mem hx, indicator_of_mem hx]
    · rw [b1loc_nearPart, indicator_of_notMem hx, indicator_of_notMem hx, enorm_zero]
      norm_num
  rw [h1, lintegral_indicator (b1loc_measurableSet_nearSet p₀)]
  exact (fourierToParabolic_measurePreserving m).setLIntegral_comp_preimage_emb
    (fourierToParabolicMeasurableEquiv m).measurableEmbedding
    (fun q => ‖f q - standardBallAverage m f p₀ 10‖ₑ ^ 2) (Metric.ball p₀ 10)

/-- `|P(p₀,10)|` (independent of `p₀`). -/
def b1loc_V10 (m : ℕ) : ℝ :=
  (2 * ParabolicRectifiability.omega m * ENNReal.ofReal 10 ^ (m + 2)).toReal

theorem b1loc_V10_nonneg : 0 ≤ b1loc_V10 m := ENNReal.toReal_nonneg

theorem b1loc_parabolicVolume_ball_ten (p₀ : Space m) :
    parabolicVolume m (Metric.ball p₀ 10) = ENNReal.ofReal (b1loc_V10 m) := by
  rw [parabolicVolume_ball p₀ 10 (by norm_num), b1loc_V10, ENNReal.ofReal_toReal]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (omega_lt_top m).ne)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem b1loc_memLp_of_lintegral_sq {g : FourierSpace m → ℝ}
    (hg : AEStronglyMeasurable g volume) (hfin : ∫⁻ x, ‖g x‖ₑ ^ 2 ≠ ⊤) :
    MemLp g 2 volume := by
  rw [memLp_iff, lt_top_iff_ne_top]
  intro htop
  rw [FourierAffine.lintegral_enorm_sq_eq hg, htop, pow_two, ENNReal.top_mul_top] at hfin
  exact hfin rfl

/-- **Near input.** There is `C` (depending only on `m` and the fixed cutoff) such that for every
`f` with real parabolic BMO bound `B` and every centre `p₀`, `χ_{x₀} N ∈ L²` and
`b1loc_timeGagliardo (χ_{x₀} N) ≤ C B²`, `N = K *_t w`. -/
theorem b1loc_near_input (hBMO : BMOGrowthStatement) (hK : HighPassKernelStatement) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Space m → ℝ) (B : ℝ), HasStandardParabolicBMOBound m f B →
      ∀ p₀ : Space m,
        MemLp (fun x => b1loc_cut ((fourierToParabolic m).symm p₀) x *
          fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_nearPart m f p₀) x)
          2 volume ∧
        b1loc_timeGagliardo (fun x => b1loc_cut ((fourierToParabolic m).symm p₀) x *
          fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_nearPart m f p₀) x) ≤
          ENNReal.ofReal (C * B ^ 2) := by
  obtain ⟨Cb, hCb, hb⟩ := hBMO m
  obtain ⟨hKint, -, -, -, ⟨CK, hCK⟩⟩ :=
    b1loc_kernel_adapter hK b1loc_cutoff b1loc_cutoff_admissible
  have ha : 0 ≤ (4 * Real.pi ^ 2 + 4) * CK ^ 2 := by positivity
  have hb' : 0 ≤ (∫ t, ‖fhp_highPassKernel b1loc_cutoff t‖) ^ 2 := sq_nonneg _
  have hV : 0 ≤ b1loc_V10 m := b1loc_V10_nonneg
  have hab : 0 ≤ 2 * ((4 * Real.pi ^ 2 + 4) * CK ^ 2) +
      6 * (∫ t, ‖fhp_highPassKernel b1loc_cutoff t‖) ^ 2 := by positivity
  refine ⟨(2 * ((4 * Real.pi ^ 2 + 4) * CK ^ 2) +
      6 * (∫ t, ‖fhp_highPassKernel b1loc_cutoff t‖) ^ 2) * (Cb * b1loc_V10 m),
    mul_nonneg hab (mul_nonneg hCb.le hV), fun f B hB p₀ => ?_⟩
  have hCB : 0 ≤ Cb * B ^ 2 := mul_nonneg hCb.le (sq_nonneg B)
  have hw2 : ∫⁻ x, ‖b1loc_nearPart m f p₀ x‖ₑ ^ 2 ≤
      ENNReal.ofReal (Cb * B ^ 2 * b1loc_V10 m) := by
    rw [b1loc_lintegral_nearPart_sq]
    have h := (hb f B hB).2.1 p₀ 10 (by norm_num)
    rwa [b1loc_parabolicVolume_ball_ten, ← ENNReal.ofReal_mul hCB] at h
  have hw : MemLp (b1loc_nearPart m f p₀) 2 volume :=
    b1loc_memLp_of_lintegral_sq (b1loc_aestronglyMeasurable_nearPart hB p₀)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hw2)
  obtain ⟨hN, hN2, hNG⟩ := b1loc_near_estimate hKint hCK hw
  refine ⟨hN.of_le ((b1loc_continuous_cut _).aestronglyMeasurable.mul hN.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_), ?_⟩
  · rw [norm_mul]
    have hc : ‖b1loc_cut ((fourierToParabolic m).symm p₀) x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (b1loc_cut_nonneg _ _)]
      exact b1loc_cut_le_one _ _
    calc ‖b1loc_cut ((fourierToParabolic m).symm p₀) x‖ *
          ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_nearPart m f p₀) x‖
        ≤ 1 * ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff)
            (b1loc_nearPart m f p₀) x‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ = _ := one_mul _
  · have hLG := (b1loc_localGagliardo_le ((fourierToParabolic m).symm p₀) _).trans hNG
    have hL2 := (setLIntegral_le_lintegral (Metric.ball ((fourierToParabolic m).symm p₀) 7)
      (fun x => ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff)
        (b1loc_nearPart m f p₀) x‖ₑ ^ 2)).trans hN2
    calc b1loc_timeGagliardo (fun x => b1loc_cut ((fourierToParabolic m).symm p₀) x *
          fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_nearPart m f p₀) x)
        ≤ ENNReal.ofReal 2 * b1loc_localGagliardo ((fourierToParabolic m).symm p₀)
              (fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_nearPart m f p₀)) +
            ENNReal.ofReal 6 * ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
              ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff)
                (b1loc_nearPart m f p₀) x‖ₑ ^ 2 :=
          b1loc_timeGagliardo_cut_mul_le _ hN.aestronglyMeasurable
      _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal ((4 * Real.pi ^ 2 + 4) * CK ^ 2) *
              ∫⁻ x, ‖b1loc_nearPart m f p₀ x‖ₑ ^ 2) +
            ENNReal.ofReal 6 * (ENNReal.ofReal
              ((∫ t, ‖fhp_highPassKernel b1loc_cutoff t‖) ^ 2) *
              ∫⁻ x, ‖b1loc_nearPart m f p₀ x‖ₑ ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hLG zero_le)
            (mul_le_mul_of_nonneg_left hL2 zero_le)
      _ = ENNReal.ofReal (2 * ((4 * Real.pi ^ 2 + 4) * CK ^ 2) +
              6 * (∫ t, ‖fhp_highPassKernel b1loc_cutoff t‖) ^ 2) *
            ∫⁻ x, ‖b1loc_nearPart m f p₀ x‖ₑ ^ 2 := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by norm_num), ← add_mul,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (2 * ((4 * Real.pi ^ 2 + 4) * CK ^ 2) +
              6 * (∫ t, ‖fhp_highPassKernel b1loc_cutoff t‖) ^ 2) *
            ENNReal.ofReal (Cb * B ^ 2 * b1loc_V10 m) :=
          mul_le_mul_of_nonneg_left hw2 zero_le
      _ = ENNReal.ofReal ((2 * ((4 * Real.pi ^ 2 + 4) * CK ^ 2) +
              6 * (∫ t, ‖fhp_highPassKernel b1loc_cutoff t‖) ^ 2) *
            (Cb * b1loc_V10 m) * B ^ 2) := by
          rw [← ENNReal.ofReal_mul hab]
          congr 1
          ring

end ParabolicRectifiability.Characterization
