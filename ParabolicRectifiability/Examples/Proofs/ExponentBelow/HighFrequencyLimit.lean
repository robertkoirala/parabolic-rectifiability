import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements

/-! # Pass the finite high-frequency bound to the periodic limit

Write `S_m` for the partial sums and `κ = ε / √(2π)`.  For `M ≥ K`,
`S_M - S_K` is the finite sum of the high-frequency estimate with coefficients `c_j = κ a_j`.  Its
integral on `(α, α + ℓ]` is controlled by that estimate: the interval-integral bound
is converted to the half-open set integral using the positive interval order
and `ofReal_integral_eq_lintegral_ofReal`.  The coefficient estimate
`κ² ≤ ε²` and finite-sum domination by the summable square series give a bound
uniform in `M`.  Minkowski then bounds the `L²` norm of `h - S_K` by the norm
of `h - S_M` plus this uniform tail bound.  The periodic-convergence hypothesis sends the first
norm to zero, yielding the estimate with the same constant `5`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace ParabolicRectifiability.Examples

private lemma e2_bmo4_enorm_sq (x : ℝ) :
    ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

private lemma e2_bmo4_enorm_sq_rpow (x : ℝ) :
    ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := by
  calc
    ‖x‖ₑ ^ (2 : ℝ) = ‖x‖ₑ ^ (2 : ℕ) := ENNReal.rpow_natCast _ _
    _ = ENNReal.ofReal (x ^ 2) := e2_bmo4_enorm_sq x

private lemma e2_bmo4_lintegral_sq_eq_eLpNorm_sq {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    (∫⁻ t, ENNReal.ofReal (f t ^ 2) ∂μ) =
      eLpNorm f 2 μ ^ (2 : ℕ) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := 2) two_ne_zero hf
  simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] at h
  calc
    (∫⁻ t, ENNReal.ofReal (f t ^ 2) ∂μ) =
        ∫⁻ t, ‖f t‖ₑ ^ (2 : ℕ) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards with t
          exact (e2_bmo4_enorm_sq (f t)).symm
    _ = eLpNorm f 2 μ ^ (2 : ℕ) := h.symm

private lemma e2_bmo4_eLpNorm_eq_lintegral_rpow {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ =
      (∫⁻ t, ENNReal.ofReal (f t ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  have hf' : AEStronglyMeasurable f μ := hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf']
  have hbase :
      (∫⁻ t, ‖f t‖ₑ ^ (2 : ℝ) ∂μ) = ∫⁻ t, ENNReal.ofReal (f t ^ 2) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards with t
    exact e2_bmo4_enorm_sq_rpow (f t)
  rw [ENNReal.toReal_ofNat, hbase]

/-- The uniform finite-tail high-frequency estimate passes to the periodic `L²` limit on the
same half-open interval. -/
theorem e2_highFrequency_limit_proof :
    E2HighFrequencyL2Statement → E2PeriodicLocalStatement → E2HighFrequencyLimitStatement := by
  intro hHigh hLocal ε a N hdata hsum h hperiodic α ℓ hℓ K hK
  let κ : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * ε
  let μ : Measure ℝ := volume.restrict (Ioc α (α + ℓ))
  let S : ℕ → ℝ → ℝ := fun m t => e2_halfDerivPartialSum ε a N m t
  let c : ℕ → ℝ := fun j => κ * a j
  let T : ℕ → ℝ → ℝ := fun M t =>
    ∑ j ∈ Finset.Ico K M, c j * Real.cos (N j * t)

  have hκsq : κ ^ 2 ≤ ε ^ 2 := by
    have hden : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hsqrt : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi :=
      Real.sq_sqrt (by positivity)
    have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 ≤ 1 := by
      rw [inv_pow, hsqrt]
      exact inv_le_one_of_one_le₀ hden
    dsimp [κ]
    calc
      ((Real.sqrt (2 * Real.pi))⁻¹ * ε) ^ 2 =
          (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 * ε ^ 2 := by rw [mul_pow]
      _ ≤ 1 * ε ^ 2 := mul_le_mul_of_nonneg_right hinv (sq_nonneg ε)
      _ = ε ^ 2 := one_mul _

  have htsum_nonneg : 0 ≤ ∑' j, a j ^ 2 :=
    tsum_nonneg fun j => sq_nonneg (a j)

  have hcoeff (M : ℕ) :
      ∑ j ∈ Finset.Ico K M, c j ^ 2 ≤ ε ^ 2 * ∑' j, a j ^ 2 := by
    have hfinite :
        ∑ j ∈ Finset.Ico K M, a j ^ 2 ≤ ∑' j, a j ^ 2 :=
      hsum.sum_le_tsum (Finset.Ico K M) (by intro j hj; exact sq_nonneg (a j))
    calc
      ∑ j ∈ Finset.Ico K M, c j ^ 2 =
          κ ^ 2 * ∑ j ∈ Finset.Ico K M, a j ^ 2 := by
            simp [c, mul_pow, Finset.mul_sum]
      _ ≤ ε ^ 2 * ∑ j ∈ Finset.Ico K M, a j ^ 2 :=
          mul_le_mul_of_nonneg_right hκsq (Finset.sum_nonneg fun j hj => sq_nonneg (a j))
      _ ≤ ε ^ 2 * ∑' j, a j ^ 2 :=
          mul_le_mul_of_nonneg_left hfinite (sq_nonneg ε)

  have hC_nonneg : 0 ≤ 5 * ℓ * (ε ^ 2 * ∑' j, a j ^ 2) := by
    positivity
  let C : ℝ := 5 * ℓ * (ε ^ 2 * ∑' j, a j ^ 2)

  have hlocal := hLocal ε a N h hperiodic
  have hconv := (hlocal.2 α (α + ℓ)).2

  have hScont (m : ℕ) : Continuous (S m) := by
    dsimp [S, e2_halfDerivPartialSum]
    fun_prop

  have hTcont (M : ℕ) : Continuous (T M) := by
    dsimp [T]
    fun_prop

  have hresMeas (m : ℕ) : AEStronglyMeasurable (fun t => h t - S m t) μ := by
    exact (hperiodic.1.sub (hScont m).measurable).aestronglyMeasurable.restrict

  have hTMeas (M : ℕ) : AEStronglyMeasurable (T M) μ := by
    exact (hTcont M).measurable.aestronglyMeasurable.restrict

  have hresNormLim :
      Tendsto (fun m => eLpNorm (fun t => h t - S m t) 2 μ) atTop (nhds 0) := by
    have hroot :=
      ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞)).comp hconv
    convert hroot using 1
    · funext m
      exact e2_bmo4_eLpNorm_eq_lintegral_rpow (μ := μ) (f := fun t => h t - S m t)
        (hresMeas m)
    · simp

  have htailfun (M : ℕ) (hKM : K ≤ M) : (fun t => S M t - S K t) = T M := by
    funext t
    dsimp [S, T, c, κ, e2_halfDerivPartialSum]
    calc
      ((Real.sqrt (2 * Real.pi))⁻¹ * ε) *
          (∑ j ∈ Finset.range M, a j * Real.cos (N j * t)) -
        ((Real.sqrt (2 * Real.pi))⁻¹ * ε) *
          (∑ j ∈ Finset.range K, a j * Real.cos (N j * t)) =
          ((Real.sqrt (2 * Real.pi))⁻¹ * ε) *
            ((∑ j ∈ Finset.range M, a j * Real.cos (N j * t)) -
              (∑ j ∈ Finset.range K, a j * Real.cos (N j * t))) := by ring
      _ = ((Real.sqrt (2 * Real.pi))⁻¹ * ε) *
            (∑ j ∈ Finset.Ico K M, a j * Real.cos (N j * t)) := by
              rw [Finset.sum_Ico_eq_sub _ hKM]
      _ = ∑ j ∈ Finset.Ico K M,
            (((Real.sqrt (2 * Real.pi))⁻¹ * ε) * a j) * Real.cos (N j * t) := by
              rw [Finset.mul_sum]
              simp [mul_assoc]

  have htailLin (M : ℕ) :
      (∫⁻ t in Ioc α (α + ℓ), ENNReal.ofReal (T M t ^ 2)) ≤ ENNReal.ofReal C := by
    have htailReal := hHigh c N hdata.frequency_pos hdata.frequency_growth α ℓ hℓ K hK M
    rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right hℓ.le)] at htailReal
    have hint : Integrable (fun t => T M t ^ 2) μ := by
      exact (hTcont M).pow 2 |>.integrableOn_Ioc
    have hnonneg : 0 ≤ᵐ[μ] fun t => T M t ^ 2 :=
      Eventually.of_forall fun t => sq_nonneg (T M t)
    have hbridge := ofReal_integral_eq_lintegral_ofReal hint hnonneg
    have hsumBound :
        5 * ℓ * ∑ j ∈ Finset.Ico K M, c j ^ 2 ≤ C := by
      dsimp [C]
      exact mul_le_mul_of_nonneg_left (hcoeff M) (by positivity)
    calc
      (∫⁻ t in Ioc α (α + ℓ), ENNReal.ofReal (T M t ^ 2)) =
          ENNReal.ofReal (∫ t in Ioc α (α + ℓ), T M t ^ 2) := hbridge.symm
      _ ≤ ENNReal.ofReal (5 * ℓ * ∑ j ∈ Finset.Ico K M, c j ^ 2) :=
          ENNReal.ofReal_le_ofReal htailReal
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hsumBound

  have htailNormBound (M : ℕ) (hKM : K ≤ M) :
      eLpNorm (T M) 2 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
    have hsq : eLpNorm (T M) 2 μ ^ 2 ≤ ENNReal.ofReal C := by
      calc
        eLpNorm (T M) 2 μ ^ 2 =
            ∫⁻ t in Ioc α (α + ℓ), ENNReal.ofReal (T M t ^ 2) := by
              simpa [μ] using
                (e2_bmo4_lintegral_sq_eq_eLpNorm_sq (μ := μ) (f := T M) (hTMeas M)).symm
        _ ≤ ENNReal.ofReal C := htailLin M
    have htop : eLpNorm (T M) 2 μ ≠ ⊤ := by
      intro htop
      simp [htop] at hsq
    have hreal : (eLpNorm (T M) 2 μ).toReal ^ 2 ≤ C := by
      have hC0 : 0 ≤ C := by dsimp [C]; positivity
      have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsq
      simpa [pow_two, ENNReal.toReal_mul, htop, ENNReal.toReal_ofReal hC0] using hmono
    calc
      eLpNorm (T M) 2 μ =
          ENNReal.ofReal (eLpNorm (T M) 2 μ).toReal :=
            (ENNReal.ofReal_toReal htop).symm
      _ ≤ ENNReal.ofReal (Real.sqrt C) :=
          ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le hreal)

  have htargetNorm :
      eLpNorm (fun t => h t - S K t) 2 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
    have hlim : Tendsto
        (fun M => eLpNorm (fun t => h t - S M t) 2 μ +
          ENNReal.ofReal (Real.sqrt C)) atTop
        (nhds (ENNReal.ofReal (Real.sqrt C))) := by
      simpa using hresNormLim.add_const (ENNReal.ofReal (Real.sqrt C))
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop K] with M hKM
    have hdecomp :
        (fun t => h t - S K t) = (fun t => h t - S M t) + T M := by
      funext t
      change h t - S K t = (h t - S M t) + T M t
      rw [← htailfun M hKM]
      ring
    calc
      eLpNorm (fun t => h t - S K t) 2 μ =
          eLpNorm ((fun t => h t - S M t) + T M) 2 μ := by rw [hdecomp]
      _ ≤ eLpNorm (fun t => h t - S M t) 2 μ +
            eLpNorm (T M) 2 μ :=
          eLpNorm_add_le (by norm_num)
      _ ≤ eLpNorm (fun t => h t - S M t) 2 μ +
            ENNReal.ofReal (Real.sqrt C) := by
          gcongr
          exact htailNormBound M hKM

  have htargetMeas :
      AEStronglyMeasurable (fun t => h t - S K t) μ := hresMeas K
  have htargetSq :
      eLpNorm (fun t => h t - S K t) 2 μ ^ 2 ≤ ENNReal.ofReal C := by
    calc
      eLpNorm (fun t => h t - S K t) 2 μ ^ 2 ≤
          ENNReal.ofReal (Real.sqrt C) ^ 2 := by gcongr
      _ = ENNReal.ofReal C := by
        rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg C), Real.sq_sqrt hC_nonneg]

  calc
    (∫⁻ t in Ioc α (α + ℓ),
        ENNReal.ofReal ((h t - e2_halfDerivPartialSum ε a N K t) ^ 2)) =
        eLpNorm (fun t => h t - S K t) 2 μ ^ 2 := by
          simpa [S, μ] using
            (e2_bmo4_lintegral_sq_eq_eLpNorm_sq (μ := μ)
              (f := fun t => h t - S K t) htargetMeas)
    _ ≤ ENNReal.ofReal C := htargetSq
    _ = ENNReal.ofReal (5 * ℓ * (ε ^ 2 * ∑' j, a j ^ 2)) := by rfl

end ParabolicRectifiability.Examples
