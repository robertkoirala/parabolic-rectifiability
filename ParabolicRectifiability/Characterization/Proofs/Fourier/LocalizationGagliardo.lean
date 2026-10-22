import ParabolicRectifiability.Characterization.Proofs.Fourier.LocalizationCutoff

/-! # Critical Sobolev localization: calculus of the temporal Gagliardo energy

Two rules used to assemble the temporal estimate of `H = χ_{x₀} (F ∘ Ψ - F(p₀))` from the
low-pass, near and far parts (multiplication by a cutoff is bounded on the energy):

* **splitting** (`b1loc_timeGagliardo_le_add3`): if `H = f₁ + f₂ + f₃` almost everywhere with
  `f₁, f₂ ∈ L²`, then `b1loc_timeGagliardo H ≤ 3 Σ b1loc_timeGagliardo f_i`; the measurability in
  the scale `s` comes from the translation Plancherel identity;
* **cutoff product rule** (`b1loc_timeGagliardo_cut_mul_le`): for the `1`-Lipschitz cutoff
  `χ_{x₀}` (`0 ≤ χ ≤ 1`, support in `B(x₀,6)`) and any a.e. strongly measurable `f`,
  `b1loc_timeGagliardo (χ_{x₀} f) ≤ 2 b1loc_localGagliardo x₀ f + 6 ∫_{B(x₀,7)} |f|²`, where the
  local energy only uses `0 < s ≤ 1` and `x ∈ B(x₀,7)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.HalfTimeDerivative

attribute [local instance] FourierAffine.continuousSMul_fourierSpace

variable {m : ℕ}

theorem b1loc_norm_timeVector : ‖timeVector m‖ = 1 := by
  have h : ‖timeVector m‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_timeVector, timeCoordinate_timeVector]
  have hn := norm_nonneg (timeVector m)
  nlinarith

theorem b1loc_enorm_add3_sq_le (a b c : ℝ) :
    ‖a + b + c‖ₑ ^ 2 ≤ ENNReal.ofReal 3 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2 + ‖c‖ₑ ^ 2) := by
  simp only [← ofReal_norm, Real.norm_eq_abs]
  rw [← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_pow (abs_nonneg _),
    ← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_pow (abs_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  simp only [sq_abs]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

theorem b1loc_enorm_add_sq_le (a b : ℝ) :
    ‖a + b‖ₑ ^ 2 ≤ ENNReal.ofReal 2 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2) := by
  simp only [← ofReal_norm, Real.norm_eq_abs]
  rw [← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_pow (abs_nonneg _),
    ← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  simp only [sq_abs]
  nlinarith [sq_nonneg (a - b)]

/-- For `F ∈ L²`, the difference energy is measurable in the scale (through translation
Plancherel). -/
theorem b1loc_measurable_diffEnergy {F : FourierSpace m → ℝ} (hF : MemLp F 2 volume) :
    Measurable fun s : ℝ => ∫⁻ x, ‖F (x + s • timeVector m) - F x‖ₑ ^ 2 := by
  have h : (fun s : ℝ => ∫⁻ x, ‖F (x + s • timeVector m) - F x‖ₑ ^ 2) = fun s =>
      ∫⁻ ζ, ‖((𝐞 (s * (WithLp.ofLp ζ).2) : Circle) : ℂ) - 1‖ₑ ^ 2 *
        ‖(𝓕 (realLp hF) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
    funext s
    rw [b1loc_lintegral_translate_sub_sq hF]
    simp_rw [b1loc_inner_smul_timeVector]
  rw [h]
  exact Measurable.lintegral_prod_right'
    (f := fun p : ℝ × FourierSpace m =>
      ‖((𝐞 (p.1 * (WithLp.ofLp p.2).2) : Circle) : ℂ) - 1‖ₑ ^ 2 *
        ‖(𝓕 (realLp hF) : Lp ℂ 2 (volume : Measure (FourierSpace m))) p.2‖ₑ ^ 2)
    ((b1loc_continuous_phase_time.measurable.enorm.pow_const 2).mul
      (((Lp.stronglyMeasurable _).measurable.enorm.pow_const 2).comp measurable_snd))

theorem b1loc_aemeasurable_diff {F : FourierSpace m → ℝ} (hF : AEStronglyMeasurable F volume)
    (s : ℝ) : AEMeasurable (fun x => ‖F (x + s • timeVector m) - F x‖ₑ ^ 2) volume :=
  (((hF.comp_measurePreserving (measurePreserving_add_right volume (s • timeVector m))).sub
    hF).enorm.pow_const 2)

/-- The difference energy `∫ |f(x + s e_t) - f(x)|² dx` at scale `s`. -/
def b1loc_diffEnergy (f : FourierSpace m → ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ‖f (x + s • timeVector m) - f x‖ₑ ^ 2

theorem b1loc_timeGagliardo_eq_diff (f : FourierSpace m → ℝ) :
    b1loc_timeGagliardo f =
      ∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal s)⁻¹ ^ 2 * b1loc_diffEnergy f s := rfl

theorem b1loc_measurable_weight : Measurable fun s : ℝ => (ENNReal.ofReal s)⁻¹ ^ 2 :=
  (ENNReal.measurable_ofReal.inv).pow_const 2

/-- **Splitting rule.** -/
theorem b1loc_timeGagliardo_le_add3 {H f₁ f₂ f₃ : FourierSpace m → ℝ}
    (h₁ : MemLp f₁ 2 volume) (h₂ : MemLp f₂ 2 volume)
    (hH : H =ᵐ[volume] fun x => f₁ x + f₂ x + f₃ x) :
    b1loc_timeGagliardo H ≤ ENNReal.ofReal 3 *
      (b1loc_timeGagliardo f₁ + b1loc_timeGagliardo f₂ + b1loc_timeGagliardo f₃) := by
  have hpt : ∀ s : ℝ, b1loc_diffEnergy H s ≤
      ENNReal.ofReal 3 * (b1loc_diffEnergy f₁ s + b1loc_diffEnergy f₂ s +
        b1loc_diffEnergy f₃ s) := by
    intro s
    have hsh : (fun x => H (x + s • timeVector m)) =ᵐ[volume]
        fun x => f₁ (x + s • timeVector m) + f₂ (x + s • timeVector m) +
          f₃ (x + s • timeVector m) :=
      (measurePreserving_add_right volume (s • timeVector m)).quasiMeasurePreserving.ae_eq_comp
        hH
    have hm1 := b1loc_aemeasurable_diff h₁.aestronglyMeasurable s
    have hm2 := b1loc_aemeasurable_diff h₂.aestronglyMeasurable s
    calc b1loc_diffEnergy H s
        = ∫⁻ x, ‖(f₁ (x + s • timeVector m) - f₁ x) + (f₂ (x + s • timeVector m) - f₂ x) +
            (f₃ (x + s • timeVector m) - f₃ x)‖ₑ ^ 2 := by
          unfold b1loc_diffEnergy
          apply lintegral_congr_ae
          filter_upwards [hsh, hH] with x hx1 hx2
          rw [hx1, hx2]
          congr 2
          ring
      _ ≤ ∫⁻ x, ENNReal.ofReal 3 * (‖f₁ (x + s • timeVector m) - f₁ x‖ₑ ^ 2 +
            ‖f₂ (x + s • timeVector m) - f₂ x‖ₑ ^ 2 +
            ‖f₃ (x + s • timeVector m) - f₃ x‖ₑ ^ 2) :=
          lintegral_mono fun x => b1loc_enorm_add3_sq_le _ _ _
      _ = ENNReal.ofReal 3 * (b1loc_diffEnergy f₁ s + b1loc_diffEnergy f₂ s +
            b1loc_diffEnergy f₃ s) := by
          unfold b1loc_diffEnergy
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left' (show AEMeasurable (fun x =>
              ‖f₁ (x + s • timeVector m) - f₁ x‖ₑ ^ 2 +
                ‖f₂ (x + s • timeVector m) - f₂ x‖ₑ ^ 2) volume from hm1.add hm2),
            lintegral_add_left' hm1]
  have hD1 : Measurable fun s => (ENNReal.ofReal s)⁻¹ ^ 2 * b1loc_diffEnergy f₁ s :=
    b1loc_measurable_weight.mul (b1loc_measurable_diffEnergy h₁)
  have hD2 : Measurable fun s => (ENNReal.ofReal s)⁻¹ ^ 2 * b1loc_diffEnergy f₂ s :=
    b1loc_measurable_weight.mul (b1loc_measurable_diffEnergy h₂)
  rw [b1loc_timeGagliardo_eq_diff, b1loc_timeGagliardo_eq_diff, b1loc_timeGagliardo_eq_diff,
    b1loc_timeGagliardo_eq_diff]
  calc ∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal s)⁻¹ ^ 2 * b1loc_diffEnergy H s
      ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal 3 *
          ((ENNReal.ofReal s)⁻¹ ^ 2 * b1loc_diffEnergy f₁ s +
            (ENNReal.ofReal s)⁻¹ ^ 2 * b1loc_diffEnergy f₂ s +
            (ENNReal.ofReal s)⁻¹ ^ 2 * b1loc_diffEnergy f₃ s) := by
        refine lintegral_mono fun s => ?_
        calc (ENNReal.ofReal s)⁻¹ ^ 2 * b1loc_diffEnergy H s
            ≤ (ENNReal.ofReal s)⁻¹ ^ 2 * (ENNReal.ofReal 3 * (b1loc_diffEnergy f₁ s +
                b1loc_diffEnergy f₂ s + b1loc_diffEnergy f₃ s)) :=
              mul_le_mul_of_nonneg_left (hpt s) zero_le
          _ = _ := by ring
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left' (show AEMeasurable (fun s =>
            (ENNReal.ofReal s)⁻¹ ^ 2 * b1loc_diffEnergy f₁ s +
              (ENNReal.ofReal s)⁻¹ ^ 2 * b1loc_diffEnergy f₂ s) (volume.restrict (Ioi 0)) from
            (hD1.add hD2).aemeasurable),
          lintegral_add_left' hD1.aemeasurable]

/-! ## The cutoff product rule -/

/-- The local temporal Gagliardo energy on `B(x₀,7)` and scales `0 < s ≤ 1`. -/
def b1loc_localGagliardo (x₀ : FourierSpace m) (f : FourierSpace m → ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (0 : ℝ) 1, (ENNReal.ofReal s)⁻¹ ^ 2 *
    ∫⁻ x in Metric.ball x₀ 7, ‖f (x + s • timeVector m) - f x‖ₑ ^ 2

theorem b1loc_localGagliardo_le (x₀ : FourierSpace m) (f : FourierSpace m → ℝ) :
    b1loc_localGagliardo x₀ f ≤ b1loc_timeGagliardo f := by
  unfold b1loc_localGagliardo b1loc_timeGagliardo
  calc ∫⁻ s in Ioc (0 : ℝ) 1, (ENNReal.ofReal s)⁻¹ ^ 2 *
        ∫⁻ x in Metric.ball x₀ 7, ‖f (x + s • timeVector m) - f x‖ₑ ^ 2
      ≤ ∫⁻ s in Ioc (0 : ℝ) 1, (ENNReal.ofReal s)⁻¹ ^ 2 *
          ∫⁻ x, ‖f (x + s • timeVector m) - f x‖ₑ ^ 2 :=
        lintegral_mono fun s => mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) zero_le
    _ ≤ _ := lintegral_mono_set Ioc_subset_Ioi_self

/-- Pointwise product rule for `0 < s ≤ 1`. -/
theorem b1loc_cut_mul_diff_sq_le (x₀ : FourierSpace m) (f : FourierSpace m → ℝ) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (x : FourierSpace m) :
    ‖b1loc_cut x₀ (x + s • timeVector m) * f (x + s • timeVector m) -
        b1loc_cut x₀ x * f x‖ₑ ^ 2 ≤
      (Metric.ball x₀ 7).indicator (fun x => ENNReal.ofReal 2 *
        (‖f (x + s • timeVector m) - f x‖ₑ ^ 2 + ENNReal.ofReal (s ^ 2) * ‖f x‖ₑ ^ 2)) x := by
  have hv : ‖s • timeVector m‖ = s := by
    rw [norm_smul, b1loc_norm_timeVector, mul_one, Real.norm_eq_abs, abs_of_pos hs0]
  by_cases hx : x ∈ Metric.ball x₀ 7
  · rw [indicator_of_mem hx]
    have hdecomp : b1loc_cut x₀ (x + s • timeVector m) * f (x + s • timeVector m) -
        b1loc_cut x₀ x * f x =
        b1loc_cut x₀ (x + s • timeVector m) * (f (x + s • timeVector m) - f x) +
          (b1loc_cut x₀ (x + s • timeVector m) - b1loc_cut x₀ x) * f x := by ring
    rw [hdecomp]
    refine (b1loc_enorm_add_sq_le _ _).trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) zero_le)
    · rw [enorm_mul, mul_pow]
      calc ‖b1loc_cut x₀ (x + s • timeVector m)‖ₑ ^ 2 * ‖f (x + s • timeVector m) - f x‖ₑ ^ 2
          ≤ 1 * ‖f (x + s • timeVector m) - f x‖ₑ ^ 2 := by
            gcongr
            rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_one]
            apply ENNReal.ofReal_le_ofReal
            rw [Real.norm_eq_abs, abs_of_nonneg (b1loc_cut_nonneg _ _)]
            nlinarith [b1loc_cut_nonneg x₀ (x + s • timeVector m),
              b1loc_cut_le_one x₀ (x + s • timeVector m)]
        _ = _ := one_mul _
    · rw [enorm_mul, mul_pow]
      gcongr
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have h := b1loc_abs_cut_sub_le x₀ (x + s • timeVector m) x
      rw [add_sub_cancel_left, hv] at h
      rw [Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
  · rw [indicator_of_notMem hx]
    have h7 : 7 ≤ ‖x - x₀‖ := by
      rw [Metric.mem_ball, dist_eq_norm, not_lt] at hx
      exact hx
    have h1 : b1loc_cut x₀ x = 0 := b1loc_cut_eq_zero (by linarith)
    have h2 : b1loc_cut x₀ (x + s • timeVector m) = 0 := by
      apply b1loc_cut_eq_zero
      have := norm_sub_norm_le (x - x₀) (-(s • timeVector m))
      rw [norm_neg, sub_neg_eq_add, hv] at this
      calc (6 : ℝ) ≤ ‖x - x₀‖ - s := by linarith
        _ ≤ ‖x - x₀ + s • timeVector m‖ := this
        _ = ‖x + s • timeVector m - x₀‖ := by congr 1; abel
    rw [h1, h2, zero_mul, zero_mul, sub_zero, enorm_zero]
    simp

/-- **Cutoff product rule.** -/
theorem b1loc_timeGagliardo_cut_mul_le (x₀ : FourierSpace m) {f : FourierSpace m → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    b1loc_timeGagliardo (fun x => b1loc_cut x₀ x * f x) ≤
      ENNReal.ofReal 2 * b1loc_localGagliardo x₀ f +
        ENNReal.ofReal 6 * ∫⁻ x in Metric.ball x₀ 7, ‖f x‖ₑ ^ 2 := by
  set X := ∫⁻ x in Metric.ball x₀ 7, ‖f x‖ₑ ^ 2 with hX
  have hcf : AEStronglyMeasurable (fun x => b1loc_cut x₀ x * f x) volume :=
    (b1loc_continuous_cut x₀).aestronglyMeasurable.mul hf
  -- small scales
  have hsmall : ∀ s : ℝ, 0 < s → s ≤ 1 →
      b1loc_diffEnergy (fun x => b1loc_cut x₀ x * f x) s ≤
        ENNReal.ofReal 2 * (∫⁻ x in Metric.ball x₀ 7, ‖f (x + s • timeVector m) - f x‖ₑ ^ 2) +
          ENNReal.ofReal 2 * (ENNReal.ofReal (s ^ 2) * X) := by
    intro s hs0 hs1
    unfold b1loc_diffEnergy
    calc ∫⁻ x, ‖b1loc_cut x₀ (x + s • timeVector m) * f (x + s • timeVector m) -
          b1loc_cut x₀ x * f x‖ₑ ^ 2
        ≤ ∫⁻ x, (Metric.ball x₀ 7).indicator (fun x => ENNReal.ofReal 2 *
          (‖f (x + s • timeVector m) - f x‖ₑ ^ 2 + ENNReal.ofReal (s ^ 2) * ‖f x‖ₑ ^ 2)) x :=
          lintegral_mono fun x => b1loc_cut_mul_diff_sq_le x₀ f hs0 hs1 x
      _ = ∫⁻ x in Metric.ball x₀ 7, ENNReal.ofReal 2 *
          (‖f (x + s • timeVector m) - f x‖ₑ ^ 2 + ENNReal.ofReal (s ^ 2) * ‖f x‖ₑ ^ 2) :=
          lintegral_indicator measurableSet_ball _
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left' (b1loc_aemeasurable_diff hf s).restrict,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_add]
  -- large scales
  have hloc : ∫⁻ x, ‖b1loc_cut x₀ x * f x‖ₑ ^ 2 ≤ X := by
    rw [hX, ← lintegral_indicator measurableSet_ball]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ Metric.ball x₀ 7
    · rw [indicator_of_mem hx, enorm_mul, mul_pow]
      calc ‖b1loc_cut x₀ x‖ₑ ^ 2 * ‖f x‖ₑ ^ 2 ≤ 1 * ‖f x‖ₑ ^ 2 := by
            gcongr
            rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_one]
            apply ENNReal.ofReal_le_ofReal
            rw [Real.norm_eq_abs, abs_of_nonneg (b1loc_cut_nonneg _ _)]
            nlinarith [b1loc_cut_nonneg x₀ x, b1loc_cut_le_one x₀ x]
        _ = _ := one_mul _
    · rw [indicator_of_notMem hx]
      have h7 : 7 ≤ ‖x - x₀‖ := by
        rw [Metric.mem_ball, dist_eq_norm, not_lt] at hx
        exact hx
      rw [b1loc_cut_eq_zero (by linarith), zero_mul, enorm_zero]
      simp
  have hlarge : ∀ s : ℝ, b1loc_diffEnergy (fun x => b1loc_cut x₀ x * f x) s ≤
      ENNReal.ofReal 4 * X := by
    intro s
    have hshift : ∫⁻ x, ‖b1loc_cut x₀ (x + s • timeVector m) * f (x + s • timeVector m)‖ₑ ^ 2 =
        ∫⁻ x, ‖b1loc_cut x₀ x * f x‖ₑ ^ 2 :=
      lintegral_add_right_eq_self (fun x => ‖b1loc_cut x₀ x * f x‖ₑ ^ 2) (s • timeVector m)
    have hmeas : AEMeasurable (fun x =>
        ‖b1loc_cut x₀ (x + s • timeVector m) * f (x + s • timeVector m)‖ₑ ^ 2) volume :=
      (hcf.comp_measurePreserving
        (measurePreserving_add_right volume (s • timeVector m))).enorm.pow_const 2
    unfold b1loc_diffEnergy
    calc ∫⁻ x, ‖b1loc_cut x₀ (x + s • timeVector m) * f (x + s • timeVector m) -
          b1loc_cut x₀ x * f x‖ₑ ^ 2
        ≤ ∫⁻ x, ENNReal.ofReal 2 *
          (‖b1loc_cut x₀ (x + s • timeVector m) * f (x + s • timeVector m)‖ₑ ^ 2 +
            ‖b1loc_cut x₀ x * f x‖ₑ ^ 2) := by
          refine lintegral_mono fun x => ?_
          have h := b1loc_enorm_add_sq_le
            (b1loc_cut x₀ (x + s • timeVector m) * f (x + s • timeVector m))
            (-(b1loc_cut x₀ x * f x))
          rw [← sub_eq_add_neg, enorm_neg] at h
          exact h
      _ = ENNReal.ofReal 2 * ((∫⁻ x, ‖b1loc_cut x₀ x * f x‖ₑ ^ 2) +
            ∫⁻ x, ‖b1loc_cut x₀ x * f x‖ₑ ^ 2) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hmeas, hshift]
      _ ≤ ENNReal.ofReal 2 * (X + X) :=
          mul_le_mul_of_nonneg_left (add_le_add hloc hloc) zero_le
      _ = ENNReal.ofReal 4 * X := by
          rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
  have hsub : Ioi (0 : ℝ) ⊆ Ioc 0 1 ∪ Ioi 1 := by
    intro s hs
    by_cases h1 : s ≤ 1
    · exact Or.inl ⟨hs, h1⟩
    · exact Or.inr (lt_of_not_ge h1)
  have hLG : b1loc_localGagliardo x₀ f = ∫⁻ s in Ioc (0 : ℝ) 1, (ENNReal.ofReal s)⁻¹ ^ 2 *
      ∫⁻ x in Metric.ball x₀ 7, ‖f (x + s • timeVector m) - f x‖ₑ ^ 2 := rfl
  rw [b1loc_timeGagliardo_eq_diff, hLG]
  calc ∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal s)⁻¹ ^ 2 *
        b1loc_diffEnergy (fun x => b1loc_cut x₀ x * f x) s
      ≤ ∫⁻ s in Ioc (0 : ℝ) 1 ∪ Ioi 1, (ENNReal.ofReal s)⁻¹ ^ 2 *
          b1loc_diffEnergy (fun x => b1loc_cut x₀ x * f x) s := lintegral_mono_set hsub
    _ ≤ (∫⁻ s in Ioc (0 : ℝ) 1, (ENNReal.ofReal s)⁻¹ ^ 2 *
          b1loc_diffEnergy (fun x => b1loc_cut x₀ x * f x) s) +
        ∫⁻ s in Ioi (1 : ℝ), (ENNReal.ofReal s)⁻¹ ^ 2 *
          b1loc_diffEnergy (fun x => b1loc_cut x₀ x * f x) s := lintegral_union_le _ _ _
    _ ≤ (∫⁻ s in Ioc (0 : ℝ) 1, (ENNReal.ofReal 2 * ((ENNReal.ofReal s)⁻¹ ^ 2 *
            ∫⁻ x in Metric.ball x₀ 7, ‖f (x + s • timeVector m) - f x‖ₑ ^ 2) +
          ENNReal.ofReal 2 * X)) +
        ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal 4 * X * (ENNReal.ofReal s)⁻¹ ^ 2 := by
        refine add_le_add (setLIntegral_mono' measurableSet_Ioc fun s hs => ?_)
          (setLIntegral_mono' measurableSet_Ioi fun s _ => ?_)
        · have hs2 : (ENNReal.ofReal s)⁻¹ ^ 2 * ENNReal.ofReal (s ^ 2) = 1 := by
            rw [ENNReal.ofReal_pow hs.1.le, ← mul_pow, ENNReal.inv_mul_cancel
              (ENNReal.ofReal_pos.2 hs.1).ne' ENNReal.ofReal_ne_top, one_pow]
          calc (ENNReal.ofReal s)⁻¹ ^ 2 * b1loc_diffEnergy (fun x => b1loc_cut x₀ x * f x) s
              ≤ (ENNReal.ofReal s)⁻¹ ^ 2 * (ENNReal.ofReal 2 *
                  (∫⁻ x in Metric.ball x₀ 7, ‖f (x + s • timeVector m) - f x‖ₑ ^ 2) +
                ENNReal.ofReal 2 * (ENNReal.ofReal (s ^ 2) * X)) :=
                mul_le_mul_of_nonneg_left (hsmall s hs.1 hs.2) zero_le
            _ = ENNReal.ofReal 2 * ((ENNReal.ofReal s)⁻¹ ^ 2 *
                  ∫⁻ x in Metric.ball x₀ 7, ‖f (x + s • timeVector m) - f x‖ₑ ^ 2) +
                ENNReal.ofReal 2 * ((ENNReal.ofReal s)⁻¹ ^ 2 * ENNReal.ofReal (s ^ 2)) * X := by
                ring
            _ = _ := by rw [hs2, mul_one]
        · calc (ENNReal.ofReal s)⁻¹ ^ 2 * b1loc_diffEnergy (fun x => b1loc_cut x₀ x * f x) s
              ≤ (ENNReal.ofReal s)⁻¹ ^ 2 * (ENNReal.ofReal 4 * X) :=
                mul_le_mul_of_nonneg_left (hlarge s) zero_le
            _ = _ := mul_comm _ _
    _ = ENNReal.ofReal 2 * (∫⁻ s in Ioc (0 : ℝ) 1, (ENNReal.ofReal s)⁻¹ ^ 2 *
            ∫⁻ x in Metric.ball x₀ 7, ‖f (x + s • timeVector m) - f x‖ₑ ^ 2) +
          ENNReal.ofReal 2 * X + ENNReal.ofReal 4 * X := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Ioc, sub_zero,
          ENNReal.ofReal_one, mul_one, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul _ b1loc_measurable_weight, b1loc_lintegral_Ioi_inv_sq zero_lt_one,
          inv_one, ENNReal.ofReal_one, mul_one]
    _ = _ := by
        rw [add_assoc, ← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num

end ParabolicRectifiability.Characterization
