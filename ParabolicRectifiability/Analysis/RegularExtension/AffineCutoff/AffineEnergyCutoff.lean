import ParabolicRectifiability.Analysis.RegularExtension.AffineCutoff.LargeScale
import ParabolicRectifiability.Analysis.RegularExtension.AffineCutoff.ExplicitCutoff

/-! # Localization of the affine energy: `affineEnergy_cutoff_le`

`affineEnergy_cutoff_le_proof` shows that the affine energy of a compactly supported parabolically
Lipschitz function, localized by a smooth cutoff at scale `R`, is bounded by the affine Carleson
constant and the Lipschitz constant, with a constant depending on `m` only.

Proof.
* The cutoff is the explicit smooth parabolic bump `χ_R` (`ExplicitCutoff`); `Cχ` is
  the bump bound `B_m`.
* The energy integrand on Fourier coordinates is the unrestricted affine error
  `κ_h(Φp, r)^2` on `Space m` of `h ∘ Φ⁻¹` (`rx4_fourier_integrand_eq`), and the coordinate map
  `Φ` is measure preserving, so the energy is `∫_V ∫_0^∞ κ_H(y,r)^2 dr/r dy`, `H = χ (G - c)`,
  `G = F ∘ Φ⁻¹`, `c` the mean of `F` over `P(0,R)`.
* Split the scales at `R`. On `(0,R]` the small-scale comparison `rx4_affineErrorSq_cutoff_le_small`
  gives
  `κ_H^2 ≤ 1_{P(0,5R)} (2 κ_G^2 + 450 v K^2 L^2 r/R)`; the Carleson hypothesis at radius `5R`
  and `∫_0^R (r/R) dr/r = 1` bound its integral by `2 B (5R)^k + 450 v K^2 L^2 v (5R)^k`.
* On `(R,∞)` the large-scale estimate `rx4_lintegral_large_scale_le` (zero comparison, Tonelli on
  a measurable majorant) gives
  `(49/2) v^2 20^k L^2 R^k`.
* The sum of the two ranges is integrated using measurability of the large-scale majorant's
  section integral only; no measurability of the affine errors is needed.

The constant is `C = 2·5^k + 450 v^2 K^2 5^k + 49 v^2 20^k`, `v = 2ω_m`, `K = B_m`,
`k = m + 2`; it depends on `m` only.
-/

noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-- `∫_{(0,R₀]} (s/R₀) ds/s = 1` (compare `lintegral_Ioc_div_scaleMeasure`). -/
theorem rx4_lintegral_Ioc_div_scaleMeasure {R₀ : ℝ} (hR : 0 < R₀) :
    ∫⁻ s in Ioc 0 R₀, ENNReal.ofReal (s / R₀) ∂scaleMeasure = 1 := by
  rw [setLIntegral_scaleMeasure measurableSet_Ioc (fun s hs => hs.1) _
    (measurable_id'.div_const R₀).ennreal_ofReal]
  rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => ENNReal.ofReal (1 / R₀))
    fun s hs => by
      have hs0 : 0 < s := hs.1
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp]
  rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity),
    one_div, inv_mul_cancel₀ hR.ne', ENNReal.ofReal_one]

theorem rx4_baseDimension_add_two (m : ℕ) : baseDimension (Spatial m) + 2 = m + 4 := by
  have := rx4_baseDimension_spatial_eq m
  omega

/-! ## Small scales, integrated in the scale variable -/

section Small

variable {m : ℕ} {χ : Space m → ℝ} {K R₀ : ℝ} {z₀ : Space m}

/-- For each `y`, `∫_{(-∞,R₀]} κ_H(y,s)^2 ds/s ≤ 1_{P(z₀,5R₀)}(y)
(2 ∫_{(0,5R₀)} κ_G(y,s)^2 ds/s + 450 v K^2 L^2)`. -/
theorem rx4_lintegral_small_scale_le (hR : 0 < R₀) (hχ : HasParabolicDerivBounds χ K R₀)
    (h01 : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1) (hsupp : ∀ p, χ p ≠ 0 → p ∈ Metric.ball z₀ (4 * R₀))
    (G : Space m → ℝ) (c : ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hG : ∀ p q, ‖G p - G q‖ ≤ L * dist p q)
    (hc : ∀ q, dist q z₀ ≤ 6 * R₀ → ‖G q - c‖ ≤ 7 * L * R₀) (y : Space m) :
    ∫⁻ s in Iic R₀, affineErrorSq (parabolicVolume m) (fun p => χ p • (G p - c)) y s
        ∂scaleMeasure ≤
      (Metric.ball z₀ (5 * R₀)).indicator (fun y' =>
        2 * ∫⁻ s in Ioo 0 (5 * R₀), affineErrorSq (parabolicVolume m) G y' s ∂scaleMeasure +
          ENNReal.ofReal (450 * (2 * omega m).toReal * K ^ 2 * L ^ 2)) y := by
  have hK := rx4_nonneg_of_hasParabolicDerivBounds hR hχ
  set X := 450 * (2 * omega m).toReal * K ^ 2 * L ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have hmeas2 : Measurable ((Ioc 0 R₀).indicator fun s : ℝ => ENNReal.ofReal (s / R₀)) :=
    (measurable_id'.div_const R₀).ennreal_ofReal.indicator measurableSet_Ioc
  have hpt : ∀ s ∈ Iic R₀,
      affineErrorSq (parabolicVolume m) (fun p => χ p • (G p - c)) y s ≤
        (Metric.ball z₀ (5 * R₀)).indicator (fun y' =>
          2 * (Ioo 0 (5 * R₀)).indicator
              (fun s => affineErrorSq (parabolicVolume m) G y' s) s +
            ENNReal.ofReal X * (Ioc 0 R₀).indicator (fun s => ENNReal.ofReal (s / R₀)) s) y := by
    intro s hs
    rcases le_or_gt s 0 with hs0 | hs0
    · rw [affineErrorSq_of_nonpos _ _ _ hs0]
      exact zero_le
    · have hsR : s ≤ R₀ := hs
      refine (rx4_affineErrorSq_cutoff_le_small hR hχ h01 hsupp G c hL hG hc y hs0 hsR).trans ?_
      refine Set.indicator_le_indicator ?_
      have h5 : s ∈ Ioo 0 (5 * R₀) := ⟨hs0, by linarith⟩
      have h6 : s ∈ Ioc 0 R₀ := ⟨hs0, hsR⟩
      rw [Set.indicator_of_mem h5, Set.indicator_of_mem h6]
      refine add_le_add le_rfl ?_
      rw [← ENNReal.ofReal_mul hX0]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : s / R₀ ≤ 1 := (div_le_one hR).2 hsR
      calc X * (s / R₀) ^ 2 = X * (s / R₀) * (s / R₀) := by ring
        _ ≤ X * (s / R₀) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = X * (s / R₀) := mul_one _
  refine (setLIntegral_mono' measurableSet_Iic hpt).trans ?_
  by_cases hy : y ∈ Metric.ball z₀ (5 * R₀)
  · simp only [Set.indicator_of_mem hy]
    refine (setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)
    rw [lintegral_add_right _ (hmeas2.const_mul _),
      lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top, lintegral_const_mul _ hmeas2,
      lintegral_indicator measurableSet_Ioo, lintegral_indicator measurableSet_Ioc,
      rx4_lintegral_Ioc_div_scaleMeasure hR, mul_one]
  · simp only [Set.indicator_of_notMem hy, lintegral_zero, le_refl]

end Small

/-! ## The localized affine energy on parabolic space -/

/-- The constant of the localized affine energy; it depends on `m` and `K` only. -/
def rx4_energyConstant (m : ℕ) (K : ℝ) : ℝ :=
  2 * 5 ^ (m + 2) + 450 * (2 * omega m).toReal ^ 2 * K ^ 2 * 5 ^ (m + 2) +
    49 * (2 * omega m).toReal ^ 2 * 20 ^ (m + 2)

theorem rx4_energyConstant_nonneg (m : ℕ) (K : ℝ) : 0 ≤ rx4_energyConstant m K := by
  unfold rx4_energyConstant
  positivity

section Energy

variable {m : ℕ} {χ : Space m → ℝ} {K R₀ : ℝ} {z₀ : Space m}

/-- The localized affine energy on `Space m`:
`∫_V ∫_0^∞ κ_H(y,s)^2 ds/s dy ≤ C (B + L^2) R₀^k` for `H = χ (G - c)`. -/
theorem rx4_lintegral_energy_le (hR : 0 < R₀) (hχ : HasParabolicDerivBounds χ K R₀)
    (h01 : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1) (hsupp : ∀ p, χ p ≠ 0 → p ∈ Metric.ball z₀ (4 * R₀))
    (G : Space m → ℝ) (c : ℝ) {L B : ℝ} (hL : 0 ≤ L)
    (hG : ∀ p q, ‖G p - G q‖ ≤ L * dist p q)
    (hc : ∀ q, dist q z₀ ≤ 6 * R₀ → ‖G q - c‖ ≤ 7 * L * R₀)
    (hB : HasAffineCarlesonBound (parabolicVolume m) G B) :
    ∫⁻ y, ∫⁻ s, affineErrorSq (parabolicVolume m) (fun p => χ p • (G p - c)) y s
        ∂scaleMeasure ∂parabolicVolume m ≤
      ENNReal.ofReal (rx4_energyConstant m K * (B + L ^ 2) * R₀ ^ (m + 2)) := by
  have hK := rx4_nonneg_of_hasParabolicDerivBounds hR hχ
  have hv : 0 ≤ (2 * omega m).toReal := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ B := hB.1
  have hR0 : R₀ ≠ 0 := hR.ne'
  set M := 49 * L ^ 2 * R₀ ^ 2 * ((2 * omega m).toReal * (4 * R₀) ^ (m + 2)) with hM
  have hM0 : 0 ≤ M := by positivity
  set X := 450 * (2 * omega m).toReal * K ^ 2 * L ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  set Φ : Space m → ℝ≥0∞ := fun y =>
    ∫⁻ s in Ioo 0 (5 * R₀), affineErrorSq (parabolicVolume m) G y s ∂scaleMeasure with hΦ
  have hsplit : ∀ y, ∫⁻ s, affineErrorSq (parabolicVolume m) (fun p => χ p • (G p - c)) y s
        ∂scaleMeasure ≤
      (Metric.ball z₀ (5 * R₀)).indicator (fun y' => 2 * Φ y' + ENNReal.ofReal X) y +
        ∫⁻ s in Ioi R₀, rx4_largeMajorant m z₀ R₀ (ENNReal.ofReal M) y s ∂scaleMeasure := by
    intro y
    rw [← lintegral_add_compl _ (measurableSet_Iic : MeasurableSet (Iic R₀)), compl_Iic]
    exact add_le_add (rx4_lintegral_small_scale_le hR hχ h01 hsupp G c hL hG hc y)
      (setLIntegral_mono' measurableSet_Ioi fun s hs =>
        rx4_affineErrorSq_cutoff_le_largeMajorant hR h01 hsupp G c hL hc y
          (hR.trans (mem_Ioi.1 hs)))
  have hgm : Measurable fun y =>
      ∫⁻ s in Ioi R₀, rx4_largeMajorant m z₀ R₀ (ENNReal.ofReal M) y s ∂scaleMeasure :=
    rx4_measurable_lintegral_largeMajorant z₀ R₀ _ _
  have hC : ∫⁻ y in Metric.ball z₀ (5 * R₀), Φ y ∂parabolicVolume m ≤
      ENNReal.ofReal (B * (5 * R₀) ^ (m + 2)) := by
    have h := hB.2 z₀ (5 * R₀) (by positivity)
    rw [rx4_baseDimension_spatial_eq] at h
    exact h
  have hsmall : ∫⁻ y, (Metric.ball z₀ (5 * R₀)).indicator
        (fun y' => 2 * Φ y' + ENNReal.ofReal X) y ∂parabolicVolume m ≤
      ENNReal.ofReal (2 * (B * (5 * R₀) ^ (m + 2)) +
        X * ((2 * omega m).toReal * (5 * R₀) ^ (m + 2))) := by
    rw [lintegral_indicator measurableSet_ball, lintegral_add_right _ measurable_const,
      lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top, setLIntegral_const,
      TraceExtension.parabolicVolume_ball_eq_ofReal z₀ (by positivity : (0 : ℝ) < 5 * R₀),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hX0,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    exact add_le_add (mul_le_mul' le_rfl hC) le_rfl
  have hlarge := rx4_lintegral_largeMajorant_le (m := m) z₀ hR M hM0
  calc ∫⁻ y, ∫⁻ s, affineErrorSq (parabolicVolume m) (fun p => χ p • (G p - c)) y s
        ∂scaleMeasure ∂parabolicVolume m
      ≤ ∫⁻ y, ((Metric.ball z₀ (5 * R₀)).indicator (fun y' => 2 * Φ y' + ENNReal.ofReal X) y +
          ∫⁻ s in Ioi R₀, rx4_largeMajorant m z₀ R₀ (ENNReal.ofReal M) y s ∂scaleMeasure)
          ∂parabolicVolume m := lintegral_mono hsplit
    _ = ∫⁻ y, (Metric.ball z₀ (5 * R₀)).indicator (fun y' => 2 * Φ y' + ENNReal.ofReal X) y
          ∂parabolicVolume m +
        ∫⁻ y, ∫⁻ s in Ioi R₀, rx4_largeMajorant m z₀ R₀ (ENNReal.ofReal M) y s ∂scaleMeasure
          ∂parabolicVolume m :=
        lintegral_add_right' _ hgm.aemeasurable
    _ ≤ ENNReal.ofReal (2 * (B * (5 * R₀) ^ (m + 2)) +
          X * ((2 * omega m).toReal * (5 * R₀) ^ (m + 2))) +
        ENNReal.ofReal (M * ((2 * omega m).toReal * 5 ^ (m + 2)) * ((R₀ ^ 2)⁻¹ / 2)) :=
        add_le_add hsmall hlarge
    _ ≤ ENNReal.ofReal (rx4_energyConstant m K * (B + L ^ 2) * R₀ ^ (m + 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have key : rx4_energyConstant m K * (B + L ^ 2) * R₀ ^ (m + 2) -
            (2 * (B * (5 * R₀) ^ (m + 2)) + X * ((2 * omega m).toReal * (5 * R₀) ^ (m + 2)) +
              M * ((2 * omega m).toReal * 5 ^ (m + 2)) * ((R₀ ^ 2)⁻¹ / 2)) =
            2 * 5 ^ (m + 2) * L ^ 2 * R₀ ^ (m + 2) +
              450 * (2 * omega m).toReal ^ 2 * K ^ 2 * 5 ^ (m + 2) * B * R₀ ^ (m + 2) +
              49 * (2 * omega m).toReal ^ 2 * (4 ^ (m + 2) * 5 ^ (m + 2)) * B * R₀ ^ (m + 2) +
              49 / 2 * (2 * omega m).toReal ^ 2 * (4 ^ (m + 2) * 5 ^ (m + 2)) * L ^ 2 *
                R₀ ^ (m + 2) := by
          rw [hX, hM, rx4_energyConstant,
            show (20 : ℝ) ^ (m + 2) = 4 ^ (m + 2) * 5 ^ (m + 2) by rw [← mul_pow]; norm_num]
          field_simp
          ring
        have hpos : 0 ≤ 2 * 5 ^ (m + 2) * L ^ 2 * R₀ ^ (m + 2) +
              450 * (2 * omega m).toReal ^ 2 * K ^ 2 * 5 ^ (m + 2) * B * R₀ ^ (m + 2) +
              49 * (2 * omega m).toReal ^ 2 * (4 ^ (m + 2) * 5 ^ (m + 2)) * B * R₀ ^ (m + 2) +
              49 / 2 * (2 * omega m).toReal ^ 2 * (4 ^ (m + 2) * 5 ^ (m + 2)) * L ^ 2 *
                R₀ ^ (m + 2) := by positivity
        linarith

end Energy

/-! ## Fourier coordinates -/

/-- The energy integrand is the unrestricted affine error on
`Space m` of the transported function, at the transported centre (for every real `r`;
both sides vanish for `r ≤ 0`). -/
theorem rx4_fourier_integrand_eq (m : ℕ) (f : FourierSpace m → ℝ) (p : FourierSpace m)
    (r : ℝ) :
    (ENNReal.ofReal r)⁻¹ ^ (m + 4) *
        ⨅ (a : ℝ) (B' : Spatial m →L[ℝ] ℝ),
          ∫⁻ q in {q : FourierSpace m | ‖(WithLp.ofLp q).1 - (WithLp.ofLp p).1‖ < r ∧
              |(WithLp.ofLp q).2 - (WithLp.ofLp p).2| < r ^ 2},
            ‖f q - (a + B' (WithLp.ofLp q).1)‖ₑ ^ 2 =
      affineErrorSq (parabolicVolume m) (fun z => f ((fourierToParabolic m).symm z))
        (fourierToParabolicMeasurableEquiv m p) r := by
  rcases le_or_gt r 0 with hr | hr
  · rw [affineErrorSq_of_nonpos _ _ _ hr]
    have hempty : {q : FourierSpace m | ‖(WithLp.ofLp q).1 - (WithLp.ofLp p).1‖ < r ∧
        |(WithLp.ofLp q).2 - (WithLp.ofLp p).2| < r ^ 2} = ∅ := by
      ext q
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h
      exact absurd ((norm_nonneg _).trans_lt h) (not_lt.2 hr)
    simp only [hempty, Measure.restrict_empty, lintegral_zero_measure, iInf_const, mul_zero]
  · rw [affineErrorSq_of_pos _ _ _ hr, rx4_baseDimension_add_two]
    congr 1
    refine iInf_congr fun a => iInf_congr fun B' => ?_
    have hset : {q : FourierSpace m | ‖(WithLp.ofLp q).1 - (WithLp.ofLp p).1‖ < r ∧
        |(WithLp.ofLp q).2 - (WithLp.ofLp p).2| < r ^ 2} =
        fourierToParabolicMeasurableEquiv m ⁻¹'
          Metric.ball (fourierToParabolicMeasurableEquiv m p) r := by
      ext q
      simp only [mem_ofPred_eq, mem_preimage, fourierToParabolicMeasurableEquiv_apply]
      rw [mem_ball_point _ _ _ _ _ hr]
    rw [hset, affineFitIntegral]
    refine Eq.trans ?_ ((fourierToParabolic_measurePreserving m).setLIntegral_comp_preimage_emb
      (fourierToParabolicMeasurableEquiv m).measurableEmbedding
      (fun z => ‖f ((fourierToParabolic m).symm z) - (a + B' z.1)‖ₑ ^ 2)
      (Metric.ball (fourierToParabolicMeasurableEquiv m p) r))
    exact setLIntegral_congr_fun
      (measurableSet_ball.preimage (fourierToParabolicMeasurableEquiv m).measurable)
      fun q _ => rfl

/-- **Localization of the affine energy** (`affineEnergy_cutoff_le`). -/
theorem affineEnergy_cutoff_le_proof (m : ℕ) :
    ∃ Cχ C : ℝ, 0 ≤ Cχ ∧ 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ χ : FourierSpace m → ℝ, HalfTimeDerivative.TailCutoff χ R Cχ ∧
        ∀ (F : FourierSpace m → ℝ) (L B : ℝ), 0 ≤ L →
          HalfTimeDerivative.ParabolicLipschitz F L →
          HasAffineCarlesonBound (parabolicVolume m)
            (fun z => F ((fourierToParabolic m).symm z)) B →
          ∫⁻ p : FourierSpace m, ∫⁻ r : ℝ, ((ENNReal.ofReal r)⁻¹ ^ (m + 4) *
            ⨅ (a : ℝ) (B' : Spatial m →L[ℝ] ℝ),
              ∫⁻ q in {q : FourierSpace m | ‖(WithLp.ofLp q).1 - (WithLp.ofLp p).1‖ < r ∧
                  |(WithLp.ofLp q).2 - (WithLp.ofLp p).2| < r ^ 2},
                ‖χ q * (F q - HalfTimeDerivative.tailMean F R) -
                  (a + B' (WithLp.ofLp q).1)‖ₑ ^ 2) ∂scaleMeasure ≤
            ENNReal.ofReal (C * (B + L ^ 2) * R ^ (m + 2)) := by
  refine ⟨SmoothCutoff.bumpBound m, rx4_energyConstant m (SmoothCutoff.bumpBound m),
    SmoothCutoff.bumpBound_nonneg m, rx4_energyConstant_nonneg m _, fun R hR =>
      ⟨rx4_cutoff m R, rx4_tailCutoff hR, fun F L B hL hF hB => ?_⟩⟩
  have hint : ∀ (p : FourierSpace m) (r : ℝ),
      (ENNReal.ofReal r)⁻¹ ^ (m + 4) *
          ⨅ (a : ℝ) (B' : Spatial m →L[ℝ] ℝ),
            ∫⁻ q in {q : FourierSpace m | ‖(WithLp.ofLp q).1 - (WithLp.ofLp p).1‖ < r ∧
                |(WithLp.ofLp q).2 - (WithLp.ofLp p).2| < r ^ 2},
              ‖rx4_cutoff m R q * (F q - HalfTimeDerivative.tailMean F R) -
                (a + B' (WithLp.ofLp q).1)‖ₑ ^ 2 =
        affineErrorSq (parabolicVolume m)
          (fun z => rx4_cutoffSpace m R z •
            (F ((fourierToParabolic m).symm z) - HalfTimeDerivative.tailMean F R))
          (fourierToParabolicMeasurableEquiv m p) r := fun p r =>
    rx4_fourier_integrand_eq m
      (fun q => rx4_cutoff m R q * (F q - HalfTimeDerivative.tailMean F R)) p r
  calc _ = ∫⁻ p : FourierSpace m, (fun y => ∫⁻ r, affineErrorSq (parabolicVolume m)
          (fun z => rx4_cutoffSpace m R z •
            (F ((fourierToParabolic m).symm z) - HalfTimeDerivative.tailMean F R)) y r
          ∂scaleMeasure) (fourierToParabolicMeasurableEquiv m p) :=
        lintegral_congr fun p => lintegral_congr fun r => hint p r
    _ = ∫⁻ y, ∫⁻ r, affineErrorSq (parabolicVolume m)
          (fun z => rx4_cutoffSpace m R z •
            (F ((fourierToParabolic m).symm z) - HalfTimeDerivative.tailMean F R)) y r
          ∂scaleMeasure ∂parabolicVolume m :=
        (fourierToParabolic_measurePreserving m).lintegral_comp_emb
          (fourierToParabolicMeasurableEquiv m).measurableEmbedding
          (fun y => ∫⁻ r, affineErrorSq (parabolicVolume m)
            (fun z => rx4_cutoffSpace m R z •
              (F ((fourierToParabolic m).symm z) - HalfTimeDerivative.tailMean F R)) y r
            ∂scaleMeasure)
    _ ≤ _ := rx4_lintegral_energy_le hR (rx4_cutoffSpace_hasParabolicDerivBounds hR)
          rx4_cutoffSpace_mem_Icc (rx4_cutoffSpace_support hR)
          (fun z => F ((fourierToParabolic m).symm z)) (HalfTimeDerivative.tailMean F R) hL
          (rx4_norm_sub_le_of_parabolicLipschitz hF) (rx4_norm_sub_tailMean_le hF hL hR) hB

end ParabolicRectifiability
