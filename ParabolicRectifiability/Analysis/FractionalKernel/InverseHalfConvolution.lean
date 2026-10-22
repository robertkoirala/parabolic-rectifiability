import ParabolicRectifiability.Analysis.FractionalKernel.InverseHalfAsymptotic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! # Differentiated convolutions `ρ * |·|^{-1/2}`

One-dimensional analysis. From the asymptotic expansion file it uses the smoothness of `|x|^r` away from `0` (`fhpbb2a_contDiffAt`), Schwartz decay
against `(1+|s|)^{-2}` (`fhpbb2a_decay_weight`) and the uniform remote-singularity bound
(`fhpbb2a_remote`).

Write `I(x) = |x|^{-1/2}` (Mathlib's `Real.rpow`, so `I(0) = 0`) and, for a real Schwartz `ρ`,
`(ρ * I)(t) = ∫ ρ(s) I(t - s) ds`. Main results:
* `fhpbb2b_integrable`: `s ↦ ρ(s) I(t - s)` is integrable for every `t`;
* `fhpbb2b_hasDerivAt`: `(ρ * I)' = ρ' * I` at every point (derivative moved onto `ρ`);
* `fhpbb2b_iteratedDeriv`: `(ρ * I)^{(j)} = ρ^{(j)} * I` for every `j`, with `ρ^{(j)}` the
  Schwartz map `(derivCLM ℝ ℝ)^[j] ρ`, whose values are `iteratedDeriv j ρ`
  (`fhpbb2b_coe_iterate`);
* `fhpbb2b_contDiff`: `ρ * I` is smooth on all of `ℝ`;
* `fhpbb2b_iteratedDeriv_sub`: for `t ≠ 0`,
  `(I - ρ * I)^{(j)}(t) = I^{(j)}(t) - ∫ ρ^{(j)}(s) I(t - s) ds`.

Proof. Substitute `s = t - u`, so `(ρ * I)(t) = ∫ ρ(t - u) I(u) du`, and
differentiate under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). For
`|x - t₀| < 1` the Peetre-type comparison `1 + |u| ≤ (1 + |x - u|)(2 + |t₀|)`
(`fhpbb2b_weight_shift`) gives the majorant
`|ρ'(x - u)| I(u) ≤ B (2 + |t₀|)^2 (1 + |u|)^{-2} I(u)`, integrable by `fhpbb2a_remote 0`.
Induct on `j`, and conclude smoothness with `contDiff_of_differentiable_iteratedDeriv`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Nat Topology SchwartzMap ContDiff

namespace ParabolicRectifiability.FractionalKernel

/-- Schwartz decay in the form `|ρ s| ≤ B (1+|s|)^{-2}`. -/
theorem fhpbb2b_abs_le (ρ : 𝓢(ℝ, ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, |ρ s| ≤ B * ((1 + |s|) ^ 2)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := fhpbb2a_decay_weight ρ 0
  refine ⟨B, hB0, fun s => ?_⟩
  have h := hB 0 le_rfl s
  rwa [pow_zero, one_mul] at h

theorem fhpbb2b_measurable_inverseHalf :
    Measurable (fun u : ℝ => |u| ^ (-(1 / 2 : ℝ))) :=
  continuous_abs.measurable.pow_const _

/-- `s ↦ ρ(s) |t - s|^{-1/2}` is integrable for every real Schwartz `ρ` and every `t`. -/
theorem fhpbb2b_integrable (ρ : 𝓢(ℝ, ℝ)) (t : ℝ) :
    Integrable (fun s : ℝ => ρ s * |t - s| ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨B, _, hB⟩ := fhpbb2b_abs_le ρ
  have hdom : Integrable
      (fun s : ℝ => B * (((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ)))) :=
    (fhpbb2a_remote t).1.const_mul B
  have hmeasI : Measurable (fun s : ℝ => |t - s| ^ (-(1 / 2 : ℝ))) :=
    fhpbb2b_measurable_inverseHalf.comp (measurable_const.sub measurable_id)
  refine hdom.mono' (ρ.continuous.measurable.mul hmeasI).aestronglyMeasurable
    (ae_of_all _ fun s => ?_)
  have hI : (0 : ℝ) ≤ |t - s| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hI, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hB s) hI

/-- The substitution `s = t - u`: `∫ g(s) |t - s|^{-1/2} ds = ∫ g(t - u) |u|^{-1/2} du`. -/
theorem fhpbb2b_integral_sub (g : ℝ → ℝ) (t : ℝ) :
    ∫ s : ℝ, g s * |t - s| ^ (-(1 / 2 : ℝ)) =
      ∫ u : ℝ, g (t - u) * |u| ^ (-(1 / 2 : ℝ)) := by
  have h := integral_sub_left_eq_self (fun s : ℝ => g s * |t - s| ^ (-(1 / 2 : ℝ))) volume t
  simp only [sub_sub_cancel] at h
  exact h.symm

/-- Peetre-type comparison: for `|x - t₀| < 1`,
`(1 + |x - u|)^{-2} ≤ (2 + |t₀|)^2 (1 + |u|)^{-2}`. -/
theorem fhpbb2b_weight_shift {t₀ x : ℝ} (hx : dist x t₀ < 1) (u : ℝ) :
    ((1 + |x - u|) ^ 2)⁻¹ ≤ (2 + |t₀|) ^ 2 * ((1 + |u|) ^ 2)⁻¹ := by
  have hxt : |x - t₀| < 1 := by rwa [Real.dist_eq] at hx
  have hx' : |x| ≤ 1 + |t₀| := by
    have h1 := abs_sub_abs_le_abs_sub x t₀
    linarith
  have hu : |u| ≤ |x - u| + |x| := by
    have h1 := le_abs_self (x - u)
    have h2 := neg_abs_le (x - u)
    have h3 := le_abs_self x
    have h4 := neg_abs_le x
    rw [abs_le]
    constructor <;> linarith
  have hprod : 1 + |u| ≤ (1 + |x - u|) * (2 + |t₀|) := by
    have hexp : (1 + |x - u|) * (2 + |t₀|) = 2 + |t₀| + 2 * |x - u| + |x - u| * |t₀| := by ring
    have hnn : 0 ≤ |x - u| * |t₀| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hxu : 0 ≤ |x - u| := abs_nonneg _
    rw [hexp]
    linarith
  have hsq : (1 + |u|) ^ 2 ≤ (1 + |x - u|) ^ 2 * (2 + |t₀|) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hprod 2
  have ha : (0 : ℝ) < (1 + |x - u|) ^ 2 := by positivity
  have hb : (0 : ℝ) < (1 + |u|) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hb, inv_mul_le_iff₀ ha]
  exact hsq

/-- **Differentiation of `ρ * I`.** For a real Schwartz `ρ`, the convolution
`t ↦ ∫ ρ(s) |t - s|^{-1/2} ds` has derivative `∫ ρ'(s) |t₀ - s|^{-1/2} ds` at every `t₀`, where
`ρ' = derivCLM ℝ ℝ ρ` (whose values are `deriv ρ`). -/
theorem fhpbb2b_hasDerivAt (ρ : 𝓢(ℝ, ℝ)) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ s : ℝ, ρ s * |t - s| ^ (-(1 / 2 : ℝ)))
      (∫ s : ℝ, SchwartzMap.derivCLM ℝ ℝ ρ s * |t₀ - s| ^ (-(1 / 2 : ℝ))) t₀ := by
  have e : (fun t : ℝ => ∫ s : ℝ, ρ s * |t - s| ^ (-(1 / 2 : ℝ))) =
      fun t : ℝ => ∫ u : ℝ, ρ (t - u) * |u| ^ (-(1 / 2 : ℝ)) :=
    funext fun t => fhpbb2b_integral_sub (⇑ρ) t
  rw [e, fhpbb2b_integral_sub (⇑(SchwartzMap.derivCLM ℝ ℝ ρ)) t₀]
  set ρ' : 𝓢(ℝ, ℝ) := SchwartzMap.derivCLM ℝ ℝ ρ with hρ'
  obtain ⟨B, hB0, hB⟩ := fhpbb2b_abs_le ρ'
  have hI : ∀ u : ℝ, (0 : ℝ) ≤ |u| ^ (-(1 / 2 : ℝ)) := fun u => Real.rpow_nonneg (abs_nonneg _) _
  -- integrability at `t₀`
  have hint0 : Integrable (fun u : ℝ => ρ (t₀ - u) * |u| ^ (-(1 / 2 : ℝ))) := by
    refine ((fhpbb2b_integrable ρ t₀).comp_sub_left t₀).congr (ae_of_all _ fun u => ?_)
    simp only [sub_sub_cancel]
  -- the integrable majorant
  have hw0 : Integrable (fun u : ℝ => ((1 + |u|) ^ 2)⁻¹ * |u| ^ (-(1 / 2 : ℝ))) := by
    have h := (fhpbb2a_remote 0).1
    simp only [zero_sub, abs_neg] at h
    exact h
  have hbound_int : Integrable (fun u : ℝ =>
      B * (2 + |t₀|) ^ 2 * (((1 + |u|) ^ 2)⁻¹ * |u| ^ (-(1 / 2 : ℝ)))) :=
    hw0.const_mul _
  have hbound : ∀ᵐ u ∂(volume : Measure ℝ), ∀ x ∈ Metric.ball t₀ 1,
      ‖ρ' (x - u) * |u| ^ (-(1 / 2 : ℝ))‖ ≤
        B * (2 + |t₀|) ^ 2 * (((1 + |u|) ^ 2)⁻¹ * |u| ^ (-(1 / 2 : ℝ))) := by
    refine ae_of_all _ fun u x hx => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hI u)]
    have h1 := hB (x - u)
    have h2 := fhpbb2b_weight_shift (Metric.mem_ball.mp hx) u
    calc |ρ' (x - u)| * |u| ^ (-(1 / 2 : ℝ))
        ≤ (B * ((1 + |x - u|) ^ 2)⁻¹) * |u| ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (hI u)
      _ ≤ (B * ((2 + |t₀|) ^ 2 * ((1 + |u|) ^ 2)⁻¹)) * |u| ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hB0) (hI u)
      _ = B * (2 + |t₀|) ^ 2 * (((1 + |u|) ^ 2)⁻¹ * |u| ^ (-(1 / 2 : ℝ))) := by ring
  have hdiff : ∀ᵐ u ∂(volume : Measure ℝ), ∀ x ∈ Metric.ball t₀ 1,
      HasDerivAt (fun x : ℝ => ρ (x - u) * |u| ^ (-(1 / 2 : ℝ)))
        (ρ' (x - u) * |u| ^ (-(1 / 2 : ℝ))) x := by
    refine ae_of_all _ fun u x _ => ?_
    have h1 : HasDerivAt (⇑ρ) (ρ' (x - u)) (x - u) := by
      rw [hρ', SchwartzMap.derivCLM_apply]
      exact ρ.hasDerivAt (x - u)
    exact (h1.comp_sub_const x u).mul_const _
  have hmeas : ∀ᶠ x in 𝓝 t₀, AEStronglyMeasurable
      (fun u : ℝ => ρ (x - u) * |u| ^ (-(1 / 2 : ℝ))) (volume : Measure ℝ) :=
    Eventually.of_forall fun x =>
      ((ρ.continuous.comp (continuous_const.sub continuous_id)).measurable.mul
        fhpbb2b_measurable_inverseHalf).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable
      (fun u : ℝ => ρ' (t₀ - u) * |u| ^ (-(1 / 2 : ℝ))) (volume : Measure ℝ) :=
    ((ρ'.continuous.comp (continuous_const.sub continuous_id)).measurable.mul
      fhpbb2b_measurable_inverseHalf).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u => ρ (x - u) * |u| ^ (-(1 / 2 : ℝ)))
    (F' := fun x u => ρ' (x - u) * |u| ^ (-(1 / 2 : ℝ)))
    (Metric.ball_mem_nhds t₀ one_pos) hmeas hint0 hmeas' hbound hbound_int hdiff).2

/-- `(ρ * I)' = ρ' * I` as functions. -/
theorem fhpbb2b_deriv (ρ : 𝓢(ℝ, ℝ)) :
    deriv (fun t : ℝ => ∫ s : ℝ, ρ s * |t - s| ^ (-(1 / 2 : ℝ))) =
      fun t : ℝ => ∫ s : ℝ, SchwartzMap.derivCLM ℝ ℝ ρ s * |t - s| ^ (-(1 / 2 : ℝ)) :=
  funext fun t => (fhpbb2b_hasDerivAt ρ t).deriv

/-- **Iterated derivatives of `ρ * I`**: `(ρ * I)^{(j)} = ρ^{(j)} * I` with
`ρ^{(j)} = (derivCLM ℝ ℝ)^[j] ρ`. -/
theorem fhpbb2b_iteratedDeriv (j : ℕ) (ρ : 𝓢(ℝ, ℝ)) :
    iteratedDeriv j (fun t : ℝ => ∫ s : ℝ, ρ s * |t - s| ^ (-(1 / 2 : ℝ))) =
      fun t : ℝ => ∫ s : ℝ,
        ((⇑(SchwartzMap.derivCLM ℝ ℝ))^[j] ρ) s * |t - s| ^ (-(1 / 2 : ℝ)) := by
  induction j generalizing ρ with
  | zero => simp only [iteratedDeriv_zero, Function.iterate_zero, id_eq]
  | succ j ih => rw [iteratedDeriv_succ', fhpbb2b_deriv, ih, Function.iterate_succ_apply]

/-- The Schwartz map `(derivCLM ℝ ℝ)^[j] ρ` has values `iteratedDeriv j ρ`. -/
theorem fhpbb2b_coe_iterate (j : ℕ) (ρ : 𝓢(ℝ, ℝ)) :
    ⇑((⇑(SchwartzMap.derivCLM ℝ ℝ))^[j] ρ) = iteratedDeriv j ⇑ρ := by
  induction j generalizing ρ with
  | zero => simp only [Function.iterate_zero, id_eq, iteratedDeriv_zero]
  | succ j ih =>
    have hD : ⇑(SchwartzMap.derivCLM ℝ ℝ ρ) = deriv ⇑ρ :=
      funext fun x => SchwartzMap.derivCLM_apply ℝ ρ x
    rw [Function.iterate_succ_apply, ih, hD, iteratedDeriv_succ']

/-- **`ρ * I` is smooth on all of `ℝ`.** -/
theorem fhpbb2b_contDiff (ρ : 𝓢(ℝ, ℝ)) :
    ContDiff ℝ ∞ (fun t : ℝ => ∫ s : ℝ, ρ s * |t - s| ^ (-(1 / 2 : ℝ))) := by
  refine contDiff_of_differentiable_iteratedDeriv fun m _ => ?_
  rw [fhpbb2b_iteratedDeriv]
  exact fun t => (fhpbb2b_hasDerivAt _ t).differentiableAt

/-- **Derivatives of `I - ρ * I` away from `0`**: for `t ≠ 0` and every `j`,
`(I - ρ * I)^{(j)}(t) = I^{(j)}(t) - ∫ ρ^{(j)}(s) I(t - s) ds`, with Mathlib's global
`iteratedDeriv` on both sides. -/
theorem fhpbb2b_iteratedDeriv_sub (ρ : 𝓢(ℝ, ℝ)) (j : ℕ) {t : ℝ} (ht : t ≠ 0) :
    iteratedDeriv j
        (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)) - ∫ s : ℝ, ρ s * |x - s| ^ (-(1 / 2 : ℝ))) t =
      iteratedDeriv j (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t -
        ∫ s : ℝ, iteratedDeriv j (⇑ρ) s * |t - s| ^ (-(1 / 2 : ℝ)) := by
  have e : (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)) - ∫ s : ℝ, ρ s * |x - s| ^ (-(1 / 2 : ℝ))) =
      (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) -
        (fun x : ℝ => ∫ s : ℝ, ρ s * |x - s| ^ (-(1 / 2 : ℝ))) := rfl
  have h1 : ContDiffAt ℝ j (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t := fhpbb2a_contDiffAt _ ht
  have h2 : ContDiffAt ℝ j (fun x : ℝ => ∫ s : ℝ, ρ s * |x - s| ^ (-(1 / 2 : ℝ))) t :=
    (contDiff_infty.mp (fhpbb2b_contDiff ρ) j).contDiffAt
  have key := iteratedDerivWithin_sub (Set.mem_univ t) uniqueDiffOn_univ
    h1.contDiffWithinAt h2.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at key
  rw [e, key, fhpbb2b_iteratedDeriv, fhpbb2b_coe_iterate]

end ParabolicRectifiability.FractionalKernel
