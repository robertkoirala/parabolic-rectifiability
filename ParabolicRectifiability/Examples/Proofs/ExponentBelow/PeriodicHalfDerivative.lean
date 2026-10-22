import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements
import Mathlib.Analysis.Fourier.AddCircle

/-!
Construct the periodic half derivative as an L² Fourier limit on `AddCircle (2 * π)`.
The lacunary frequencies are distinct, and the two exponential modes at each frequency encode
one real cosine.  The square-summability of the amplitudes makes the corresponding orthogonal
Fourier series convergent in `Lp ℂ 2`; a measurable representative gives the claimed periodic
real-valued function.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

private abbrev e2L2Period : ℝ := 2 * Real.pi

local instance e2L2PeriodPos : Fact (0 < e2L2Period) := ⟨by positivity⟩

private def e2L2Amplitude (ε : ℝ) (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * ε * a j

private def e2L2FourierFreq (N : ℕ → ℕ) (i : Σ _j : ℕ, Bool) : ℤ :=
  if i.2 then -(N i.1 : ℤ) else (N i.1 : ℤ)

private def e2L2FourierCoeff (ε : ℝ) (a : ℕ → ℝ) (i : Σ _j : ℕ, Bool) : ℂ :=
  ((e2L2Amplitude ε a i.1 / 2 : ℝ) : ℂ)

private def e2L2FourierTerm (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ)
    (i : Σ _j : ℕ, Bool) :
    Lp ℂ (2 : ℝ≥0∞) (@AddCircle.haarAddCircle e2L2Period e2L2PeriodPos) :=
  e2L2FourierCoeff ε a i •
    @fourierLp e2L2Period e2L2PeriodPos (2 : ℝ≥0∞) _ (e2L2FourierFreq N i)

private def e2L2FourierBlock (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) :
    Lp ℂ (2 : ℝ≥0∞) (@AddCircle.haarAddCircle e2L2Period e2L2PeriodPos) :=
  ∑ b : Bool, e2L2FourierTerm ε a N ⟨j, b⟩

private def e2L2FourierPartial (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (m : ℕ) :
    Lp ℂ (2 : ℝ≥0∞) (@AddCircle.haarAddCircle e2L2Period e2L2PeriodPos) :=
  ∑ j ∈ Finset.range m, e2L2FourierBlock ε a N j

private def e2L2CirclePartial (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (m : ℕ)
    (x : AddCircle e2L2Period) : ℂ :=
  ∑ j ∈ Finset.range m,
    (e2L2FourierCoeff ε a ⟨j, false⟩ * fourier (e2L2FourierFreq N ⟨j, false⟩) x +
      e2L2FourierCoeff ε a ⟨j, true⟩ * fourier (e2L2FourierFreq N ⟨j, true⟩) x)

private theorem e2L2_lintegral_sq_eq_norm_sq {α : Type} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℂ (2 : ℝ≥0∞) μ) :
    (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) = ENNReal.ofReal (‖f‖ ^ 2) := by
  have hp := eLpNorm_eq_lintegral_rpow_enorm_toReal (f := (f : α → ℂ))
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (Lp.aestronglyMeasurable f)
  have hp' : eLpNorm (f : α → ℂ) (2 : ℝ≥0∞) μ =
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    simpa using hp
  have hpow := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) hp'
  have hroot : ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) =
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
    convert ENNReal.rpow_rpow_inv (x := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ)
      (y := (1 / (2 : ℝ))) (by norm_num) using 1; norm_num
  rw [hroot] at hpow
  have hnorm : ENNReal.ofReal (‖f‖ ^ 2) = (eLpNorm (f : α → ℂ) (2 : ℝ≥0∞) μ) ^ (2 : ℝ) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def]
    simp [ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  exact hpow.symm.trans hnorm.symm

private theorem e2L2_re_sq_le_norm_sq (z : ℂ) :
    ENNReal.ofReal (z.re ^ 2) ≤ ‖z‖ₑ ^ (2 : ℝ) := by
  have hreal : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    calc
      z.re ^ 2 = |z.re| ^ 2 := by rw [sq_abs]
      _ ≤ ‖z‖ ^ 2 := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2
        (Complex.abs_re_le_norm z)
  calc
    ENNReal.ofReal (z.re ^ 2) ≤ ENNReal.ofReal (‖z‖ ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = ‖z‖ₑ ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _)]
      simp [enorm]

private theorem e2L2_fourier_coe_re (n : ℤ) (t : ℝ) :
    (fourier n (t : AddCircle e2L2Period)).re = Real.cos ((n : ℝ) * t) := by
  rw [fourier_coe_apply]
  have hexp : (2 * Real.pi * Complex.I * n * (t : ℂ) / e2L2Period) =
      (((n : ℝ) * t : ℝ) : ℂ) * Complex.I := by
    simp only [e2L2Period]
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hexp, Complex.exp_ofReal_mul_I_re]

private theorem e2L2_fourier_pair_re (c : ℝ) (n : ℤ) (x : AddCircle e2L2Period) :
    (((c / 2 : ℝ) : ℂ) * fourier n x +
      ((c / 2 : ℝ) : ℂ) * fourier (-n) x).re = c * (fourier n x).re := by
  rw [fourier_neg]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.mul_re, Complex.conj_re, Complex.conj_im, zero_mul, sub_zero]
  ring

private theorem e2L2_frequency_injective (a : ℕ → ℝ) (N : ℕ → ℕ)
    (hdata : IsLacunaryData a N) : Function.Injective (e2L2FourierFreq N) := by
  have hpos : ∀ j, 0 < N j := hdata.frequency_pos
  have hnext : ∀ j, N j < N (j + 1) := by
    intro j
    have hg := hdata.frequency_growth j
    have hj := hpos j
    omega
  have hmono : StrictMono N := strictMono_nat_of_lt_succ hnext
  intro i k hik
  rcases i with ⟨i, bi⟩
  rcases k with ⟨k, bk⟩
  cases bi <;> cases bk
  · have hfreq : (N i : ℤ) = (N k : ℤ) := by simpa [e2L2FourierFreq] using hik
    have hik' : i = k := hmono.injective (by exact_mod_cast hfreq)
    subst k
    rfl
  · have hfreq : (N i : ℤ) = -(N k : ℤ) := by simpa [e2L2FourierFreq] using hik
    have hi : (0 : ℤ) < (N i : ℤ) := by exact_mod_cast hpos i
    have hk : (0 : ℤ) < (N k : ℤ) := by exact_mod_cast hpos k
    omega
  · have hfreq : -(N i : ℤ) = (N k : ℤ) := by simpa [e2L2FourierFreq] using hik
    have hi : (0 : ℤ) < (N i : ℤ) := by exact_mod_cast hpos i
    have hk : (0 : ℤ) < (N k : ℤ) := by exact_mod_cast hpos k
    omega
  · have hfreq : (N i : ℤ) = (N k : ℤ) := by simpa [e2L2FourierFreq] using hik
    have hik' : i = k := hmono.injective (by exact_mod_cast hfreq)
    subst k
    rfl

theorem e2_periodic_halfDerivative_proof : E2PeriodicLimitStatement := by
  intro ε a N hdata ha2
  classical
  let coeff : ℕ → ℝ := e2L2Amplitude ε a
  let indexCoeff : (Σ j : ℕ, Bool) → ℂ := e2L2FourierCoeff ε a
  let indexFreq : (Σ j : ℕ, Bool) → ℤ := e2L2FourierFreq N
  let term : (Σ j : ℕ, Bool) →
      Lp ℂ (2 : ℝ≥0∞) (@AddCircle.haarAddCircle e2L2Period e2L2PeriodPos) :=
    e2L2FourierTerm ε a N
  let block : ℕ → Lp ℂ (2 : ℝ≥0∞) (@AddCircle.haarAddCircle e2L2Period e2L2PeriodPos) :=
    e2L2FourierBlock ε a N
  let partialLp : ℕ → Lp ℂ (2 : ℝ≥0∞) (@AddCircle.haarAddCircle e2L2Period e2L2PeriodPos) :=
    e2L2FourierPartial ε a N
  let q : ℕ → AddCircle e2L2Period → ℂ := e2L2CirclePartial ε a N

  have hcoeffSq : Summable (fun j => coeff j ^ 2) := by
    apply (ha2.mul_left (((Real.sqrt (2 * Real.pi))⁻¹ * ε) ^ 2)).congr
    intro j
    simp only [coeff, e2L2Amplitude]
    ring

  have hindexCoeffSq : Summable (fun i : Σ j : ℕ, Bool => ‖indexCoeff i‖ ^ 2) := by
    rw [summable_sigma_of_nonneg (fun i => sq_nonneg (‖indexCoeff i‖))]
    refine ⟨?_, ?_⟩
    · intro j
      exact Summable.of_finite
    · convert hcoeffSq.mul_left (1 / 2 : ℝ) using 1
      ext j
      simp [coeff, indexCoeff, e2L2FourierCoeff, e2L2Amplitude, tsum_fintype,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg Real.pi), abs_of_nonneg (Real.sqrt_nonneg 2)]
      ring_nf
      rw [sq_abs ε, sq_abs (a j)]

  have horth : Orthonormal ℂ (fun i : Σ j : ℕ, Bool =>
      @fourierLp e2L2Period e2L2PeriodPos (2 : ℝ≥0∞) _ (indexFreq i)) := by
    exact (@orthonormal_fourier e2L2Period e2L2PeriodPos).comp indexFreq
      (e2L2_frequency_injective a N hdata)
  have htermSummable : Summable term := by
    change Summable (fun i : Σ j : ℕ, Bool =>
      indexCoeff i • @fourierLp e2L2Period e2L2PeriodPos (2 : ℝ≥0∞) _ (indexFreq i))
    exact (horth.orthogonalFamily.summable_iff_norm_sq_summable indexCoeff).2 hindexCoeffSq

  have hblockSummable : Summable block := by
    have hfalse : Summable (fun j => term ⟨j, false⟩) :=
      htermSummable.comp_injective (by intro i j hij; simpa using hij)
    have htrue : Summable (fun j => term ⟨j, true⟩) :=
      htermSummable.comp_injective (by intro i j hij; simpa using hij)
    have hsum : Summable (fun j => term ⟨j, false⟩ + term ⟨j, true⟩) := hfalse.add htrue
    exact hsum.congr (fun j => by
      simp [block, term, e2L2FourierBlock, e2L2FourierTerm,
        e2L2FourierCoeff, e2L2FourierFreq, add_comm])

  let limit : Lp ℂ (2 : ℝ≥0∞) (@AddCircle.haarAddCircle e2L2Period e2L2PeriodPos) :=
    ∑' j, block j
  have hpartialLimit : Tendsto partialLp atTop (𝓝 limit) := by
    change Tendsto (fun n => ∑ j ∈ Finset.range n, block j) atTop
      (𝓝 (∑' j, block j))
    exact hblockSummable.hasSum.tendsto_sum_nat

  let h : ℝ → ℝ := fun t => (limit (t : AddCircle e2L2Period)).re
  have hmeas : Measurable h := by
    exact Complex.continuous_re.measurable.comp
      ((Lp.stronglyMeasurable limit).measurable.comp AddCircle.measurable_mk')
  have hperiodic : Function.Periodic h e2L2Period := by
    intro t
    simp [h]

  have hpartialAE (m : ℕ) : (partialLp m : AddCircle e2L2Period → ℂ) =ᵐ[
      AddCircle.haarAddCircle] q m := by
    classical
    let μ : Measure (AddCircle e2L2Period) :=
      @AddCircle.haarAddCircle e2L2Period e2L2PeriodPos
    have htermAE (i : Σ j : ℕ, Bool) :
        (term i : AddCircle e2L2Period → ℂ) =ᵐ[μ]
          fun x => indexCoeff i * fourier (indexFreq i) x := by
      dsimp only [term, e2L2FourierTerm]
      have hsmul := Lp.coeFn_smul (indexCoeff i)
        (@fourierLp e2L2Period e2L2PeriodPos (2 : ℝ≥0∞) _ (indexFreq i))
      filter_upwards [hsmul, coeFn_fourierLp (2 : ℝ≥0∞) (indexFreq i)] with x hsmul hx
      calc
        ((e2L2FourierCoeff ε a i •
            @fourierLp e2L2Period e2L2PeriodPos (2 : ℝ≥0∞) _
              (e2L2FourierFreq N i) : Lp ℂ (2 : ℝ≥0∞)
                (@AddCircle.haarAddCircle e2L2Period e2L2PeriodPos)) x) =
            indexCoeff i • (@fourierLp e2L2Period e2L2PeriodPos
              (2 : ℝ≥0∞) _ (indexFreq i) : Lp ℂ (2 : ℝ≥0∞)
                (@AddCircle.haarAddCircle e2L2Period e2L2PeriodPos)) x := hsmul
        _ = indexCoeff i * fourier (indexFreq i) x := by
          rw [hx]
          simp [smul_eq_mul]
    have hblockAE (j : ℕ) :
        (block j : AddCircle e2L2Period → ℂ) =ᵐ[μ]
          fun x => ∑ b : Bool, indexCoeff ⟨j, b⟩ * fourier (indexFreq ⟨j, b⟩) x := by
      dsimp only [block, e2L2FourierBlock]
      have hsum := Lp.coeFn_finsetSum Finset.univ
        (fun b : Bool => term ⟨j, b⟩)
      have hall : ∀ᵐ x ∂μ, ∀ b : Bool,
          (term ⟨j, b⟩ : AddCircle e2L2Period → ℂ) x =
            indexCoeff ⟨j, b⟩ * fourier (indexFreq ⟨j, b⟩) x :=
        Filter.eventually_all.2 (fun b => htermAE ⟨j, b⟩)
      filter_upwards [hsum, hall] with x hsum hx
      simp only [Finset.sum_apply] at hsum
      rw [hsum]
      refine Finset.sum_congr rfl ?_
      intro b _
      exact hx b
    dsimp only [partialLp, e2L2FourierPartial]
    have houter := Lp.coeFn_finsetSum (Finset.range m) (fun j : ℕ => block j)
    have hall : ∀ᵐ x ∂μ, ∀ j ∈ Finset.range m,
        (block j : AddCircle e2L2Period → ℂ) x =
          ∑ b : Bool, indexCoeff ⟨j, b⟩ * fourier (indexFreq ⟨j, b⟩) x := by
      rw [Finset.eventually_all]
      intro j hj
      exact hblockAE j
    filter_upwards [houter, hall] with x houter hx
    rw [houter]
    simp only [Finset.sum_apply]
    simp only [q, e2L2CirclePartial]
    change (∑ j ∈ Finset.range m,
        (block j : AddCircle e2L2Period → ℂ) x) =
      ∑ j ∈ Finset.range m,
        (e2L2FourierCoeff ε a ⟨j, false⟩ *
            fourier (e2L2FourierFreq N ⟨j, false⟩) x +
          e2L2FourierCoeff ε a ⟨j, true⟩ *
            fourier (e2L2FourierFreq N ⟨j, true⟩) x)
    refine Finset.sum_congr rfl ?_
    intro j hj
    simpa [indexCoeff, indexFreq, add_comm] using hx j hj

  have hrealPart (m : ℕ) (t : ℝ) :
      (q m (t : AddCircle e2L2Period)).re =
        e2_halfDerivPartialSum ε a N m t := by
    simp only [q, e2L2CirclePartial]
    rw [Complex.re_sum, e2_halfDerivPartialSum]
    rw [Finset.mul_sum (Finset.range m)
      (fun j => a j * Real.cos (N j * t)) ((Real.sqrt (2 * Real.pi))⁻¹ * ε)]
    apply Finset.sum_congr rfl
    intro j hj
    have hcalc :
        (e2L2FourierCoeff ε a ⟨j, false⟩ *
            fourier (e2L2FourierFreq N ⟨j, false⟩) (t : AddCircle e2L2Period) +
          e2L2FourierCoeff ε a ⟨j, true⟩ *
            fourier (e2L2FourierFreq N ⟨j, true⟩) (t : AddCircle e2L2Period)).re =
          e2L2Amplitude ε a j * Real.cos (N j * t) := by
      have hfpos : e2L2FourierFreq N ⟨j, false⟩ = (N j : ℤ) := by simp [e2L2FourierFreq]
      have hfneg : e2L2FourierFreq N ⟨j, true⟩ = -(N j : ℤ) := by simp [e2L2FourierFreq]
      rw [hfpos, hfneg]
      calc
        (e2L2FourierCoeff ε a ⟨j, false⟩ * fourier (N j : ℤ)
            (t : AddCircle e2L2Period) +
          e2L2FourierCoeff ε a ⟨j, true⟩ * fourier (-(N j : ℤ))
            (t : AddCircle e2L2Period)).re =
            e2L2Amplitude ε a j * (fourier (N j : ℤ)
              (t : AddCircle e2L2Period)).re := by
          simpa [e2L2FourierCoeff] using e2L2_fourier_pair_re
            (e2L2Amplitude ε a j) (N j : ℤ) (t : AddCircle e2L2Period)
        _ = e2L2Amplitude ε a j * Real.cos (N j * t) := by
          rw [e2L2_fourier_coe_re]
          congr 1
    rw [hcalc]
    simp [e2L2Amplitude]
    ring

  have herrorAE (m : ℕ) :
      (fun x : AddCircle e2L2Period => (limit x - q m x)) =ᵐ[
        AddCircle.haarAddCircle] (fun x => (limit - partialLp m) x) := by
    filter_upwards [Lp.coeFn_sub limit (partialLp m), hpartialAE m] with x hsub hq
    simpa [hq] using hsub.symm

  have hbound (m : ℕ) :
      (∫⁻ t in Ioc 0 e2L2Period,
          ENNReal.ofReal ((h t - e2_halfDerivPartialSum ε a N m t) ^ 2)) ≤
        ENNReal.ofReal (e2L2Period * ‖limit - partialLp m‖ ^ 2) := by
    let err : AddCircle e2L2Period → ℝ≥0∞ := fun x =>
      ENNReal.ofReal ((limit x - q m x).re ^ 2)
    have hinterval :
        (∫⁻ t in Ioc 0 e2L2Period,
            ENNReal.ofReal ((h t - e2_halfDerivPartialSum ε a N m t) ^ 2)) =
          ∫⁻ x : AddCircle e2L2Period, err x ∂volume := by
      calc
        (∫⁻ t in Ioc 0 e2L2Period,
            ENNReal.ofReal ((h t - e2_halfDerivPartialSum ε a N m t) ^ 2)) =
            ∫⁻ t in Ioc 0 e2L2Period, err (t : AddCircle e2L2Period) := by
          apply lintegral_congr_ae
          filter_upwards with t
          simp [err, h, hrealPart]
        _ = ∫⁻ x : AddCircle e2L2Period, err x ∂volume := by
          simpa [e2L2Period] using AddCircle.lintegral_preimage e2L2Period 0 err
    have hAEvol :
        (fun x : AddCircle e2L2Period => limit x - q m x) =ᵐ[volume]
        (fun x => (limit - partialLp m) x) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      exact Measure.ae_smul_measure (herrorAE m) (ENNReal.ofReal e2L2Period)
    have hpoint : ∀ᵐ x : AddCircle e2L2Period ∂volume,
        err x ≤ ‖(limit - partialLp m) x‖ₑ ^ (2 : ℝ) := by
      filter_upwards [hAEvol] with x hx
      have hx' : (limit x - q m x).re = ((limit - partialLp m) x).re := by
        simpa using congrArg Complex.re hx
      change ENNReal.ofReal ((limit x - q m x).re ^ 2) ≤ _
      rw [hx']
      exact e2L2_re_sq_le_norm_sq ((limit - partialLp m) x)
    rw [hinterval]
    calc
      (∫⁻ x : AddCircle e2L2Period, err x ∂volume) ≤
          ∫⁻ x : AddCircle e2L2Period, ‖(limit - partialLp m) x‖ₑ ^ (2 : ℝ) ∂volume :=
        lintegral_mono_ae hpoint
      _ = ENNReal.ofReal (e2L2Period * ‖limit - partialLp m‖ ^ 2) := by
        rw [AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure,
          e2L2_lintegral_sq_eq_norm_sq]
        change ENNReal.ofReal e2L2Period * ENNReal.ofReal (‖limit - partialLp m‖ ^ 2) = _
        rw [← ENNReal.ofReal_mul (by positivity)]

  have hnorm : Tendsto (fun m : ℕ => ‖limit - partialLp m‖) atTop (𝓝 0) := by
    have hcont : Continuous (fun x : Lp ℂ (2 : ℝ≥0∞) AddCircle.haarAddCircle => ‖limit - x‖) :=
      continuous_norm.comp (continuous_const.sub continuous_id)
    change Tendsto ((fun x : Lp ℂ (2 : ℝ≥0∞) AddCircle.haarAddCircle => ‖limit - x‖) ∘
      partialLp) atTop (𝓝 0)
    simpa using (hcont.tendsto limit).comp hpartialLimit
  have hupper : Tendsto (fun m : ℕ =>
      ENNReal.ofReal (e2L2Period * ‖limit - partialLp m‖ ^ 2)) atTop (𝓝 0) := by
    have hreal : Tendsto (fun m : ℕ => e2L2Period * ‖limit - partialLp m‖ ^ 2) atTop (𝓝 0) := by
      have hpow : Tendsto (fun m : ℕ => ‖limit - partialLp m‖ ^ 2) atTop (𝓝 ((0 : ℝ) ^ 2)) :=
        hnorm.pow 2
      have hmul : Tendsto (fun m : ℕ =>
          e2L2Period * ‖limit - partialLp m‖ ^ 2) atTop
          (𝓝 (e2L2Period * (0 : ℝ) ^ 2)) :=
        tendsto_const_nhds.mul hpow
      simpa using hmul
    simpa using ENNReal.tendsto_ofReal hreal
  have hconv : Tendsto (fun m : ℕ =>
      ∫⁻ t in Ioc 0 e2L2Period,
        ENNReal.ofReal ((h t - e2_halfDerivPartialSum ε a N m t) ^ 2)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro m
      exact bot_le
    · exact hbound

  exact ⟨h, hmeas, hperiodic, by simpa [e2L2Period] using hconv⟩

end ParabolicRectifiability.Examples
