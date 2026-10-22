import ParabolicRectifiability.Analysis.FractionalKernel.OneDimWeighted

/-! # The unweighted one-dimensional half-derivative estimate

One-dimensional analysis, using the kernel splitting of the weighted estimate
(`fhpbb1w_oneDimWeighted`), with an arbitrary real normalization `κ`.

For `f : ℝ → ℂ` write `D f(t) = κ ∫ |h|^{-3/2} (f(t) - f(t-h)) dh` (a Bochner integral, `0` at a
time where the `h`-integrand is not integrable). Main result (`fhpbb1u_oneDimUnweighted`): there
is `C ≥ 0` such that for every `C¹` function `f`,
`∫⁻ ‖D f(t)‖ₑ dt ≤ C ∫⁻ (‖f(t)‖ₑ + ‖f'(t)‖ₑ) dt`.
No integrability of `f` is assumed: both sides are extended integrals.

Proof. Split `|h|^{-3/2} = n(h) + a(h)` at `|h| = 1` (`fhpbb1w_near`, `fhpbb1w_far`).
* Pointwise (`fhpbb1u_pointwise`), for every `t` (no integrability needed, since
  `‖∫ g‖ₑ ≤ ∫⁻ ‖g‖ₑ` holds in general):
  `‖∫ |h|^{-3/2} (f t - f(t-h)) dh‖ₑ ≤ ∫⁻ n(h) ‖f t - f(t-h)‖ₑ + ‖a‖₁ ‖f t‖ₑ + ∫⁻ a(h) ‖f(t-h)‖ₑ`.
* Local part (`fhpbb1u_local_fixed`, `fhpbb1u_local`): `f(t) - f(t-h) = -∫_0^1 (-h) f'(t - αh) dα`
  (`fhpbb1w_enorm_sub_le`), Tonelli and translation invariance give
  `∫⁻ ‖f t - f(t-h)‖ₑ dt ≤ |h| ‖f'‖₁`, hence the local part is `≤ (∫⁻ n(h)|h|) ‖f'‖₁`.
* Far part (`fhpbb1u_far`): Tonelli and translation invariance give `∫⁻∫⁻ a(h) ‖f(t-h)‖ₑ = ‖a‖₁ ‖f‖₁`.
The constant is `‖κ‖ (∫⁻ n(h)|h| + 2 ‖a‖₁)` (`= 8|κ|` by the explicit masses `4` and `4`; only
finiteness is used).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ParabolicRectifiability.FractionalKernel

/-- **Pointwise bound** (unweighted): for continuous `f` and every `t`,
`‖∫ |h|^{-3/2} (f t - f (t-h)) dh‖ₑ ≤ ∫⁻ n(h) ‖f t - f(t-h)‖ₑ dh + (‖a‖₁ ‖f t‖ₑ +
∫⁻ a(h) ‖f (t-h)‖ₑ dh)`. -/
theorem fhpbb1u_pointwise (f : ℝ → ℂ) (hfc : Continuous f) (t : ℝ) :
    ‖∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))‖ₑ ≤
      (∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ) +
        (fhpbb1w_farMass * ‖f t‖ₑ + ∫⁻ h, ENNReal.ofReal (fhpbb1w_far h) * ‖f (t - h)‖ₑ) := by
  have hsh : Continuous fun h : ℝ => f (t - h) := hfc.comp (continuous_const.sub continuous_id)
  have hmN : Measurable fun h : ℝ => ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ :=
    fhpbb1w_measurable_near.ennreal_ofReal.mul (continuous_const.sub hsh).measurable.enorm
  have hmF : Measurable fun h : ℝ => ENNReal.ofReal (fhpbb1w_far h) * ‖f t‖ₑ :=
    fhpbb1w_measurable_far.ennreal_ofReal.mul_const _
  have hpt : ∀ h : ℝ, ‖((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))‖ₑ ≤
      ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ +
        (ENNReal.ofReal (fhpbb1w_far h) * ‖f t‖ₑ +
          ENNReal.ofReal (fhpbb1w_far h) * ‖f (t - h)‖ₑ) := by
    intro h
    have hk : ‖((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))‖ₑ =
        (ENNReal.ofReal (fhpbb1w_near h) + ENNReal.ofReal (fhpbb1w_far h)) *
          ‖f t - f (t - h)‖ₑ := by
      rw [enorm_mul, fhpbb1w_enorm_ofReal, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg h) _),
        ← fhpbb1w_near_add_far h,
        ENNReal.ofReal_add (fhpbb1w_near_nonneg h) (fhpbb1w_far_nonneg h)]
    rw [hk, add_mul, ← mul_add]
    gcongr
    exact enorm_sub_le
  calc ‖∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))‖ₑ
      ≤ ∫⁻ h, ‖((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ h, (ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ +
          (ENNReal.ofReal (fhpbb1w_far h) * ‖f t‖ₑ +
            ENNReal.ofReal (fhpbb1w_far h) * ‖f (t - h)‖ₑ)) :=
        lintegral_mono hpt
    _ = (∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ) +
          ((∫⁻ h, ENNReal.ofReal (fhpbb1w_far h) * ‖f t‖ₑ) +
            ∫⁻ h, ENNReal.ofReal (fhpbb1w_far h) * ‖f (t - h)‖ₑ) := by
        rw [lintegral_add_left hmN, lintegral_add_left hmF]
    _ = _ := by
        rw [fhpbb1w_farMass, lintegral_mul_const' ‖f t‖ₑ _ enorm_ne_top]

/-- **Local part for one shift** (Tonelli and translation invariance): for `C¹` `f` and
every `h`, `∫⁻ ‖f t - f (t-h)‖ₑ dt ≤ ‖h‖ₑ ∫⁻ ‖f' x‖ₑ dx`. -/
theorem fhpbb1u_local_fixed (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (h : ℝ) :
    ∫⁻ t, ‖f t - f (t - h)‖ₑ ≤ ‖h‖ₑ * ∫⁻ x, ‖deriv f x‖ₑ := by
  have hc : Continuous (deriv f) := hf.continuous_deriv_one
  have hmeas : AEMeasurable (Function.uncurry fun (t α : ℝ) => ‖deriv f (t - α * h)‖ₑ)
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    have hin : Continuous fun p : ℝ × ℝ => p.1 - p.2 * h :=
      continuous_fst.sub (continuous_snd.mul continuous_const)
    have hm : Measurable fun p : ℝ × ℝ => ‖deriv f (p.1 - p.2 * h)‖ₑ :=
      (hc.comp hin).measurable.enorm
    exact hm.aemeasurable
  calc ∫⁻ t, ‖f t - f (t - h)‖ₑ
      ≤ ∫⁻ t, ‖h‖ₑ * ∫⁻ α in Ioc (0 : ℝ) 1, ‖deriv f (t - α * h)‖ₑ :=
        lintegral_mono fun t => fhpbb1w_enorm_sub_le f hf t h
    _ = ‖h‖ₑ * ∫⁻ t, ∫⁻ α in Ioc (0 : ℝ) 1, ‖deriv f (t - α * h)‖ₑ :=
        lintegral_const_mul' _ _ enorm_ne_top
    _ = ‖h‖ₑ * ∫⁻ α in Ioc (0 : ℝ) 1, ∫⁻ t, ‖deriv f (t - α * h)‖ₑ := by
        rw [lintegral_lintegral_swap hmeas]
    _ = ‖h‖ₑ * ∫⁻ _α in Ioc (0 : ℝ) 1, ∫⁻ t, ‖deriv f t‖ₑ := by
        congr 1
        refine lintegral_congr fun α => ?_
        exact lintegral_sub_right_eq_self (fun x => ‖deriv f x‖ₑ) (α * h)
    _ = ‖h‖ₑ * ∫⁻ x, ‖deriv f x‖ₑ := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- **Local part** (unweighted):
`∫⁻ ∫⁻ n(h) ‖f t - f (t-h)‖ₑ dh dt ≤ (∫⁻ n(h)|h|) ∫⁻ ‖f' x‖ₑ dx`. -/
theorem fhpbb1u_local (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    ∫⁻ t, ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ ≤
      fhpbb1w_nearMass * ∫⁻ x, ‖deriv f x‖ₑ := by
  have hfc : Continuous f := hf.continuous
  have hmeas : AEMeasurable (Function.uncurry fun t h : ℝ =>
      ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ) (volume.prod volume) := by
    have hm : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal (fhpbb1w_near p.2) * ‖f p.1 - f (p.1 - p.2)‖ₑ :=
      (fhpbb1w_measurable_near.comp measurable_snd).ennreal_ofReal.mul
        ((hfc.comp continuous_fst).sub (hfc.comp (continuous_fst.sub continuous_snd))
          ).measurable.enorm
    exact hm.aemeasurable
  have hK : Measurable fun h : ℝ => ENNReal.ofReal (fhpbb1w_near h) * ‖h‖ₑ :=
    fhpbb1w_measurable_near.ennreal_ofReal.mul measurable_id.enorm
  calc ∫⁻ t, ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ
      = ∫⁻ h, ∫⁻ t, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ :=
        lintegral_lintegral_swap hmeas
    _ = ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ∫⁻ t, ‖f t - f (t - h)‖ₑ :=
        lintegral_congr fun h => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * (‖h‖ₑ * ∫⁻ x, ‖deriv f x‖ₑ) :=
        lintegral_mono fun h => mul_le_mul' le_rfl (fhpbb1u_local_fixed f hf h)
    _ = ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖h‖ₑ * ∫⁻ x, ‖deriv f x‖ₑ :=
        lintegral_congr fun h => (mul_assoc _ _ _).symm
    _ = fhpbb1w_nearMass * ∫⁻ x, ‖deriv f x‖ₑ :=
        lintegral_mul_const _ hK

/-- **Far part** (for arbitrary `f`, its unweighted norm is bounded by `C ‖f‖₁`):
`∫⁻ ∫⁻ a(h) ‖f (t-h)‖ₑ dh dt = ‖a‖₁ ∫⁻ ‖f x‖ₑ dx`. -/
theorem fhpbb1u_far (f : ℝ → ℂ) (hfc : Continuous f) :
    ∫⁻ t, ∫⁻ h, ENNReal.ofReal (fhpbb1w_far h) * ‖f (t - h)‖ₑ =
      fhpbb1w_farMass * ∫⁻ x, ‖f x‖ₑ := by
  have hmeas : AEMeasurable (Function.uncurry fun t h : ℝ =>
      ENNReal.ofReal (fhpbb1w_far h) * ‖f (t - h)‖ₑ) (volume.prod volume) := by
    have hm : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal (fhpbb1w_far p.2) * ‖f (p.1 - p.2)‖ₑ :=
      (fhpbb1w_measurable_far.comp measurable_snd).ennreal_ofReal.mul
        (hfc.comp (continuous_fst.sub continuous_snd)).measurable.enorm
    exact hm.aemeasurable
  have hK : Measurable fun h : ℝ => ENNReal.ofReal (fhpbb1w_far h) :=
    fhpbb1w_measurable_far.ennreal_ofReal
  calc ∫⁻ t, ∫⁻ h, ENNReal.ofReal (fhpbb1w_far h) * ‖f (t - h)‖ₑ
      = ∫⁻ h, ∫⁻ t, ENNReal.ofReal (fhpbb1w_far h) * ‖f (t - h)‖ₑ :=
        lintegral_lintegral_swap hmeas
    _ = ∫⁻ h, ENNReal.ofReal (fhpbb1w_far h) * ∫⁻ t, ‖f (t - h)‖ₑ :=
        lintegral_congr fun h => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ∫⁻ h, ENNReal.ofReal (fhpbb1w_far h) * ∫⁻ x, ‖f x‖ₑ := by
        refine lintegral_congr fun h => ?_
        rw [lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ) h]
    _ = fhpbb1w_farMass * ∫⁻ x, ‖f x‖ₑ :=
        lintegral_mul_const _ hK

/-- **The unweighted one-dimensional estimate**, for an arbitrary real
normalization `κ`: there is `C ≥ 0` such that for every `C¹` function `f : ℝ → ℂ`,
`∫⁻ ‖κ ∫ |h|^{-3/2} (f t - f (t-h)) dh‖ₑ dt ≤ C ∫⁻ (‖f t‖ₑ + ‖f' t‖ₑ) dt`.
The constant is `‖κ‖ₑ (∫⁻ n(h)|h| + 2 ‖a‖₁)`, converted with `toReal` (it is finite). No
integrability of `f` is assumed. -/
theorem fhpbb1u_oneDimUnweighted (κ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 1 f →
      ∫⁻ t, ‖(κ : ℂ) * ∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))‖ₑ ≤
        ENNReal.ofReal C * ∫⁻ t, (‖f t‖ₑ + ‖deriv f t‖ₑ) := by
  have hM : ‖(κ : ℂ)‖ₑ * (fhpbb1w_nearMass + 2 * fhpbb1w_farMass) ≠ ⊤ :=
    ENNReal.mul_ne_top enorm_ne_top (ENNReal.add_ne_top.mpr
      ⟨fhpbb1w_nearMass_lt_top.ne, ENNReal.mul_ne_top (by norm_num) fhpbb1w_farMass_lt_top.ne⟩)
  refine ⟨(‖(κ : ℂ)‖ₑ * (fhpbb1w_nearMass + 2 * fhpbb1w_farMass)).toReal,
    ENNReal.toReal_nonneg, fun f hf => ?_⟩
  rw [ENNReal.ofReal_toReal hM]
  have hfc : Continuous f := hf.continuous
  have hfm : Measurable fun t : ℝ => ‖f t‖ₑ := hfc.measurable.enorm
  have hA : Measurable fun t : ℝ =>
      ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ := by
    have hm : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal (fhpbb1w_near p.2) * ‖f p.1 - f (p.1 - p.2)‖ₑ :=
      (fhpbb1w_measurable_near.comp measurable_snd).ennreal_ofReal.mul
        ((hfc.comp continuous_fst).sub (hfc.comp (continuous_fst.sub continuous_snd))
          ).measurable.enorm
    exact hm.lintegral_prod_right'
  have hFc : Measurable fun t : ℝ => fhpbb1w_farMass * ‖f t‖ₑ := hfm.const_mul _
  calc ∫⁻ t, ‖(κ : ℂ) * ∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))‖ₑ
      ≤ ∫⁻ t, ‖(κ : ℂ)‖ₑ *
          ((∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ) +
            (fhpbb1w_farMass * ‖f t‖ₑ +
              ∫⁻ h, ENNReal.ofReal (fhpbb1w_far h) * ‖f (t - h)‖ₑ)) := by
        refine lintegral_mono fun t => ?_
        beta_reduce
        rw [enorm_mul]
        exact mul_le_mul' le_rfl (fhpbb1u_pointwise f hfc t)
    _ = ‖(κ : ℂ)‖ₑ *
          ((∫⁻ t, ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ) +
            (fhpbb1w_farMass * (∫⁻ t, ‖f t‖ₑ) +
              ∫⁻ t, ∫⁻ h, ENNReal.ofReal (fhpbb1w_far h) * ‖f (t - h)‖ₑ)) := by
        rw [lintegral_const_mul' ‖(κ : ℂ)‖ₑ _ enorm_ne_top, lintegral_add_left hA,
          lintegral_add_left hFc, lintegral_const_mul fhpbb1w_farMass hfm]
    _ ≤ ‖(κ : ℂ)‖ₑ *
          (fhpbb1w_nearMass * (∫⁻ x, ‖deriv f x‖ₑ) +
            (fhpbb1w_farMass * (∫⁻ t, ‖f t‖ₑ) + fhpbb1w_farMass * ∫⁻ x, ‖f x‖ₑ)) := by
        rw [fhpbb1u_far f hfc]
        gcongr ‖(κ : ℂ)‖ₑ * (?_ + _)
        exact fhpbb1u_local f hf
    _ ≤ ‖(κ : ℂ)‖ₑ *
          (fhpbb1w_nearMass * (∫⁻ t, (‖f t‖ₑ + ‖deriv f t‖ₑ)) +
            (fhpbb1w_farMass * (∫⁻ t, (‖f t‖ₑ + ‖deriv f t‖ₑ)) +
              fhpbb1w_farMass * ∫⁻ t, (‖f t‖ₑ + ‖deriv f t‖ₑ))) := by
        gcongr ‖(κ : ℂ)‖ₑ * (fhpbb1w_nearMass * ?_ + (fhpbb1w_farMass * ?_ +
          fhpbb1w_farMass * ?_))
        · exact lintegral_mono fun t => le_add_self
        · exact lintegral_mono fun t => le_self_add
        · exact lintegral_mono fun t => le_self_add
    _ = ‖(κ : ℂ)‖ₑ * (fhpbb1w_nearMass + 2 * fhpbb1w_farMass) *
          ∫⁻ t, (‖f t‖ₑ + ‖deriv f t‖ₑ) := by ring

end ParabolicRectifiability.FractionalKernel
