import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements
import ParabolicRectifiability.Analysis.MeanOscillation

/-! # Interval BMO bound for the lacunary half-time derivative

The low-frequency oscillation estimate, the high-frequency limit estimate and the local
periodic estimate combine, through the mean-oscillation adapter, to a mean-oscillation bound on
every open interval for the periodic half derivative of a lacunary series.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.MeanOscillation

/-- The low-frequency block is controlled by its modulus, and the high-frequency remainder by
its local square integral.  The existing mean-oscillation adapter combines these two estimates. -/
theorem e2_below_intervalBMO_proof :
    E2LowFrequencyOscillationStatement → E2HighFrequencyLimitStatement →
      E2PeriodicLocalStatement → E2BelowIntervalBMOStatement := by
  intro hLow hHigh hLocal ε a N hε hN hsum h hper
  rcases hper with ⟨hMeas, hPeriodic, hConverges⟩
  have hlocData := hLocal ε a N h ⟨hMeas, hPeriodic, hConverges⟩
  rcases hlocData with ⟨hLocallyIntegrable, hLocalSquare⟩
  refine ⟨hLocallyIntegrable, ?_⟩
  intro τ ρ hρ
  let ℓ : ℝ := 2 * ρ
  let I : Set ℝ := Ioo (τ - ρ) (τ + ρ)
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity

  have hN_lower : ∀ k : ℕ, k + 1 ≤ N k := by
    intro k
    induction k with
    | zero => have := hN.frequency_pos 0; omega
    | succ k ih =>
      have ihR : (k : ℝ) + 1 ≤ (N k : ℝ) := by exact_mod_cast ih
      have hposR : 0 < (N k : ℝ) := by exact_mod_cast hN.frequency_pos k
      have hgrowthR : 16 * (N k : ℝ) ≤ (N (k + 1) : ℝ) := by
        exact_mod_cast hN.frequency_growth k
      have hnextR : (k : ℝ) + 2 ≤ (N (k + 1) : ℝ) := by nlinarith
      exact_mod_cast hnextR
  have hCutoffExists : ∃ k : ℕ, 1 ≤ ℓ * (N k : ℝ) := by
    obtain ⟨k, hk⟩ := exists_nat_gt ℓ⁻¹
    have hkNk := hN_lower k
    have hkNnat : k ≤ N k := by omega
    have hkN : (k : ℝ) ≤ (N k : ℝ) := by exact_mod_cast hkNnat
    have hkprod : 1 < ℓ * (k : ℝ) := by
      calc
        1 = ℓ * ℓ⁻¹ := (mul_inv_cancel₀ (ne_of_gt hℓ)).symm
        _ < ℓ * (k : ℝ) := mul_lt_mul_of_pos_left hk hℓ
    exact ⟨k, le_trans hkprod.le (mul_le_mul_of_nonneg_left hkN hℓ.le)⟩
  let K : ℕ := Nat.find hCutoffExists
  have hK : 1 ≤ ℓ * (N K : ℝ) := Nat.find_spec hCutoffExists
  have hLowIndex : ∀ j < K, (N j : ℝ) * ℓ ≤ 1 := by
    intro j hj
    have hnot : ¬ 1 ≤ ℓ * (N j : ℝ) := Nat.find_min hCutoffExists hj
    have hlt : ℓ * (N j : ℝ) < 1 := lt_of_not_ge hnot
    nlinarith [hlt]

  let q : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  let c : ℕ → ℝ := fun j => q * ε * a j
  let S : ℝ → ℝ := e2_halfDerivPartialSum ε a N K
  let err : ℝ → ℝ := fun t => h t - S t
  let A : ℝ := ∑' j, a j ^ 2
  let B : ℝ := 2 * ε * Real.sqrt A

  have hScont : Continuous S := by
    dsimp [S, e2_halfDerivPartialSum]
    fun_prop
  have hS_as_sum (t : ℝ) :
      S t = ∑ j ∈ Finset.range K, c j * Real.cos (N j * t) := by
    dsimp [S, e2_halfDerivPartialSum, c, q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

  have hqroot : 1 ≤ Real.sqrt (2 * Real.pi) := by
    apply Real.one_le_sqrt.mpr
    nlinarith [Real.pi_gt_three]
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqle : q ≤ 1 := by
    dsimp [q]
    exact inv_le_one_of_one_le₀ hqroot
  have hq_sq : q ^ 2 ≤ 1 := by
    calc
      q ^ 2 = q * q := by ring
      _ ≤ 1 * q := mul_le_mul_of_nonneg_right hqle hqpos.le
      _ ≤ 1 := by nlinarith [hqle]
  have hcoeff : ∀ j : ℕ, c j ^ 2 ≤ ε ^ 2 * a j ^ 2 := by
    intro j
    dsimp [c]
    calc
      (q * ε * a j) ^ 2 = q ^ 2 * (ε * a j) ^ 2 := by ring
      _ ≤ 1 * (ε * a j) ^ 2 := mul_le_mul_of_nonneg_right hq_sq (sq_nonneg _)
      _ = ε ^ 2 * a j ^ 2 := by ring
  have hWeighted : Summable (fun j : ℕ => ε ^ 2 * a j ^ 2) := hsum.mul_left _
  have hcoeff_sum :
      (∑ j ∈ Finset.range K, c j ^ 2) ≤ ε ^ 2 * A := by
    calc
      (∑ j ∈ Finset.range K, c j ^ 2) ≤
          ∑ j ∈ Finset.range K, ε ^ 2 * a j ^ 2 :=
        Finset.sum_le_sum fun j hj => hcoeff j
      _ ≤ ∑' j, ε ^ 2 * a j ^ 2 := hWeighted.sum_le_tsum (Finset.range K)
        (fun j hj => mul_nonneg (sq_nonneg ε) (sq_nonneg (a j)))
        
      _ = ε ^ 2 * A := by
        dsimp [A]
        exact hsum.tsum_mul_left _
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact tsum_nonneg fun j => sq_nonneg (a j)
  have hrootSum :
      Real.sqrt (∑ j ∈ Finset.range K, c j ^ 2) ≤ ε * Real.sqrt A := by
    calc
      Real.sqrt (∑ j ∈ Finset.range K, c j ^ 2) ≤ Real.sqrt (ε ^ 2 * A) :=
        Real.sqrt_le_sqrt hcoeff_sum
      _ = ε * Real.sqrt A := by
        rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le]

  have hpair : ∀ x ∈ I, ∀ y ∈ I, ‖S x - S y‖ ≤ B := by
    intro x hx y hy
    rcases hx with ⟨hxl, hxu⟩
    rcases hy with ⟨hyl, hyu⟩
    have hgap : |x - y| ≤ ℓ := by
      rw [abs_le]
      constructor <;> dsimp [ℓ] <;> linarith
    have hosc := hLow c N hN.frequency_pos hN.frequency_growth ℓ hℓ K hLowIndex x y hgap
    rw [Real.norm_eq_abs, hS_as_sum x, hS_as_sum y]
    calc
      |(∑ j ∈ Finset.range K, c j * Real.cos (N j * x)) -
          ∑ j ∈ Finset.range K, c j * Real.cos (N j * y)| ≤
          2 * Real.sqrt (∑ j ∈ Finset.range K, c j ^ 2) := hosc
      _ ≤ 2 * (ε * Real.sqrt A) := mul_le_mul_of_nonneg_left hrootSum (by norm_num)
      _ = B := by dsimp [B]; ring

  have hIvol : volume I = ENNReal.ofReal ℓ := by
    dsimp [I, ℓ]
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hIpos : 0 < volume I := by
    rw [hIvol]
    exact ENNReal.ofReal_pos.mpr hℓ
  have hItop : volume I < ∞ := by
    rw [hIvol]
    exact ENNReal.ofReal_lt_top
  have hvolReal : volume.real I = ℓ := by
    rw [Measure.real_def, hIvol, ENNReal.toReal_ofReal hℓ.le]

  have hErrorMeas : Measurable (fun t : ℝ => err t ^ 2) := by
    dsimp [err]
    exact (hMeas.sub hScont.measurable).pow_const 2
  have hHighBound := hHigh ε a N hN hsum h ⟨hMeas, hPeriodic, hConverges⟩
    (τ - ρ) ℓ hℓ K hK
  have hI_subset : I ⊆ Ioc (τ - ρ) ((τ - ρ) + ℓ) := by
    intro t ht
    rcases ht with ⟨htl, htu⟩
    refine ⟨htl, ?_⟩
    have hend : (τ - ρ) + ℓ = τ + ρ := by dsimp [ℓ]; ring
    rw [hend]
    exact htu.le
  have hErrorLIntegral :
      ∫⁻ t in I, ENNReal.ofReal (err t ^ 2) ∂volume ≤
        ENNReal.ofReal (5 * ℓ * (ε ^ 2 * A)) := by
    calc
      ∫⁻ t in I, ENNReal.ofReal (err t ^ 2) ∂volume ≤
          ∫⁻ t in Ioc (τ - ρ) ((τ - ρ) + ℓ), ENNReal.ofReal (err t ^ 2) ∂volume :=
        lintegral_mono_set hI_subset
      _ ≤ ENNReal.ofReal (5 * ℓ * (ε ^ 2 * A)) := by
        simpa [err, A, S, e2_halfDerivPartialSum] using hHighBound
  have hErrorLIntegralFinite :
      (∫⁻ t in I, ENNReal.ofReal (err t ^ 2) ∂volume) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hErrorLIntegral
  have hErrorSqInt : Integrable (fun t : ℝ => err t ^ 2) (volume.restrict I) :=
    (lintegral_ofReal_ne_top_iff_integrable
      hErrorMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => sq_nonneg (err t))).1 hErrorLIntegralFinite
  have hErrMeas : AEStronglyMeasurable err (volume.restrict I) := by
    dsimp [err]
    exact (hMeas.sub hScont.measurable).aestronglyMeasurable
  have hErrMemLp : MemLp err 2 (volume.restrict I) :=
    (memLp_two_iff_integrable_sq hErrMeas).2 hErrorSqInt

  have hSIntIcc : IntegrableOn S (Icc (τ - ρ) (τ + ρ)) volume :=
    hScont.integrableOn_Icc
  have hSInt : IntegrableOn S I volume :=
    hSIntIcc.mono_set (by
      intro t ht
      rcases ht with ⟨htl, htu⟩
      exact ⟨htl.le, htu.le⟩)
  have hrep : h =ᵐ[volume.restrict I] fun t => err t + S t := by
    filter_upwards with t
    dsimp [err]
    ring
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (by norm_num) hε.le) (Real.sqrt_nonneg A)

  have hAdapter := oscillation_restrict_le_L2_add_of_pairwise
    (μ := volume) (Q := I) (a := err) (b := S) (g := h)
    measurableSet_Ioo hIpos hItop hErrMemLp hSInt hrep hBnonneg hpair
  have hAdapter' :
      oscillation (volume.restrict I) h ≤
        2 * ℓ ^ (-1 / 2 : ℝ) * Real.sqrt (∫ t in I, err t ^ 2 ∂volume) + B := by
    simpa [hvolReal, Real.norm_eq_abs, sq_abs] using hAdapter

  have hErrorRealBound :
      (∫ t in I, err t ^ 2 ∂volume) ≤ 5 * ℓ * (ε ^ 2 * A) := by
    have hIntegralEq := ofReal_integral_eq_lintegral_ofReal hErrorSqInt
      (Filter.Eventually.of_forall fun t => sq_nonneg (err t))
    have hOfRealBound :
        ENNReal.ofReal (∫ t in I, err t ^ 2 ∂volume) ≤
          ENNReal.ofReal (5 * ℓ * (ε ^ 2 * A)) := by
      rw [hIntegralEq]
      exact hErrorLIntegral
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hOfRealBound
  have hSqrtFactor :
      Real.sqrt (5 * ℓ * (ε ^ 2 * A)) =
        Real.sqrt 5 * Real.sqrt ℓ * ε * Real.sqrt A := by
    calc
      Real.sqrt (5 * ℓ * (ε ^ 2 * A)) =
          Real.sqrt (5 * ℓ) * Real.sqrt (ε ^ 2 * A) := by
            rw [Real.sqrt_mul (by positivity)]
      _ = (Real.sqrt 5 * Real.sqrt ℓ) * (ε * Real.sqrt A) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5),
          Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le]
      _ = Real.sqrt 5 * Real.sqrt ℓ * ε * Real.sqrt A := by ring
  have hSqrtError :
      Real.sqrt (∫ t in I, err t ^ 2 ∂volume) ≤
        Real.sqrt 5 * Real.sqrt ℓ * ε * Real.sqrt A := by
    exact (Real.sqrt_le_sqrt hErrorRealBound).trans_eq hSqrtFactor
  have hCancel : ℓ ^ (-1 / 2 : ℝ) * Real.sqrt ℓ = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hℓ]
    norm_num
  have hFirstTerm :
      2 * ℓ ^ (-1 / 2 : ℝ) * Real.sqrt (∫ t in I, err t ^ 2 ∂volume) ≤
        2 * Real.sqrt 5 * ε * Real.sqrt A := by
    calc
      _ ≤ 2 * ℓ ^ (-1 / 2 : ℝ) *
          (Real.sqrt 5 * Real.sqrt ℓ * ε * Real.sqrt A) :=
        mul_le_mul_of_nonneg_left hSqrtError (by positivity)
      _ = 2 * Real.sqrt 5 * ε * Real.sqrt A := by
        calc
          _ = 2 * Real.sqrt 5 * ε * Real.sqrt A *
              (ℓ ^ (-1 / 2 : ℝ) * Real.sqrt ℓ) := by ring
          _ = 2 * Real.sqrt 5 * ε * Real.sqrt A := by rw [hCancel, mul_one]

  have hConst : 2 * Real.sqrt 5 + 2 < 16 := by
    have hs5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 5, hs5]
  have hOscBound : oscillation (volume.restrict I) h ≤ 16 * ε * Real.sqrt A := by
    have hoscSmall : oscillation (volume.restrict I) h ≤
        (2 * Real.sqrt 5 + 2) * ε * Real.sqrt A := by
      calc
        oscillation (volume.restrict I) h ≤
            2 * ℓ ^ (-1 / 2 : ℝ) * Real.sqrt (∫ t in I, err t ^ 2 ∂volume) + B :=
          hAdapter'
        _ ≤ 2 * Real.sqrt 5 * ε * Real.sqrt A + B := add_le_add hFirstTerm le_rfl
        _ = (2 * Real.sqrt 5 + 2) * ε * Real.sqrt A := by dsimp [B, A]; ring
    have hFactorNonneg : 0 ≤ ε * Real.sqrt A := mul_nonneg hε.le (Real.sqrt_nonneg A)
    have hConstMul :
        (2 * Real.sqrt 5 + 2) * ε * Real.sqrt A ≤ 16 * ε * Real.sqrt A := by
      calc
        (2 * Real.sqrt 5 + 2) * ε * Real.sqrt A =
            (2 * Real.sqrt 5 + 2) * (ε * Real.sqrt A) := by ring
        _ ≤ 16 * (ε * Real.sqrt A) := mul_le_mul_of_nonneg_right hConst.le hFactorNonneg
        _ = 16 * ε * Real.sqrt A := by ring
    exact hoscSmall.trans hConstMul

  have hOscId :
      oscillation (volume.restrict I) h =
        (∫ s in I, |h s - (2 * ρ)⁻¹ * (∫ u in I, h u ∂volume)| ∂volume) / (2 * ρ) := by
    rw [oscillation_restrict_eq, hvolReal, smul_eq_mul]
    simp only [Real.norm_eq_abs]
    dsimp [ℓ]
  calc
    (∫ s in I, |h s - (2 * ρ)⁻¹ * (∫ u in I, h u ∂volume)| ∂volume) =
        ((∫ s in I, |h s - (2 * ρ)⁻¹ * (∫ u in I, h u ∂volume)| ∂volume) / (2 * ρ)) * (2 * ρ) := by
      have hden : (2 * ρ) ≠ 0 := ne_of_gt (by positivity)
      field_simp
      apply integral_congr_ae
      filter_upwards with s
      congr 1
      ring
    _ = oscillation (volume.restrict I) h * (2 * ρ) := by rw [← hOscId]
    _ ≤ (16 * ε * Real.sqrt A) * (2 * ρ) :=
      mul_le_mul_of_nonneg_right hOscBound (by positivity)

end ParabolicRectifiability.Examples
