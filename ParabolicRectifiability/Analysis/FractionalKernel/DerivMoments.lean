import ParabolicRectifiability.Analysis.FractionalKernel.InverseHalfConvolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Moments of the derivatives of a frequency cutoff

One-dimensional analysis. From the convolution file only the Schwartz iterate
`(derivCLM ℝ ℝ)^[j] η` (as in `fhpbb2b_iteratedDeriv`) is used.

Main results, for a real Schwartz function `η` and `η^{(j)} = (derivCLM ℝ ℝ)^[j] η`:
* `fhpbb2t_cutoff_moment` (the **Fourier–moment bridge**): if `η̂ = 1` near `0` (Mathlib's phase),
  then `∫ s^k η(s) ds = 1` for `k = 0` and `0` for `k ≥ 1`. Indeed
  `iteratedDeriv k η̂ 0 = ∫ (-2πi s)^k η(s) ds` (`Real.iteratedDeriv_fourier`) and
  `iteratedDeriv k η̂ 0 = iteratedDeriv k 1 0 = δ_{k0}` (`η̂` is locally constant at `0`);
* `fhpbb2t_moment_deriv` (**integration by parts**):
  `∫ s^{k+1} ρ'(s) ds = -(k+1) ∫ s^k ρ(s) ds`, and `fhpbb2t_integral_deriv`: `∫ ρ' = 0`;
* `fhpbb2t_moment_iterate`: if `∫ s^k η = δ_{k0}` for all `k`, then
  `∫ s^k η^{(j)}(s) ds = (-1)^j j!` for `k = j` and `0` otherwise (induction on `j`).
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Nat Topology SchwartzMap FourierTransform

namespace ParabolicRectifiability.FractionalKernel

/-- Polynomial moments of a real Schwartz function are integrable. -/
theorem fhpbb2t_integrable_pow_mul (f : 𝓢(ℝ, ℝ)) (k : ℕ) :
    Integrable (fun s : ℝ => s ^ k * f s) := by
  refine (f.integrable_pow_mul volume k).mono'
    ((continuous_pow k).mul f.continuous).aestronglyMeasurable (ae_of_all _ fun s => ?_)
  exact le_of_eq (by rw [norm_mul, norm_pow])

/-- The derivative of a real Schwartz function, as `HasDerivAt` with the Schwartz map `ρ'`. -/
theorem fhpbb2t_hasDerivAt (ρ : 𝓢(ℝ, ℝ)) (x : ℝ) :
    HasDerivAt (⇑ρ) (SchwartzMap.derivCLM ℝ ℝ ρ x) x := by
  rw [SchwartzMap.derivCLM_apply]
  exact ρ.differentiableAt.hasDerivAt

/-- `∫ ρ' = 0` for a real Schwartz function `ρ`. -/
theorem fhpbb2t_integral_deriv (ρ : 𝓢(ℝ, ℝ)) :
    ∫ s : ℝ, SchwartzMap.derivCLM ℝ ℝ ρ s = 0 :=
  integral_eq_zero_of_hasDerivAt_of_integrable (f := ⇑ρ) (fhpbb2t_hasDerivAt ρ)
    (SchwartzMap.derivCLM ℝ ℝ ρ).integrable ρ.integrable

/-- **Integration by parts**: `∫ s^{k+1} ρ'(s) ds = -((k+1) ∫ s^k ρ(s) ds)`. -/
theorem fhpbb2t_moment_deriv (ρ : 𝓢(ℝ, ℝ)) (k : ℕ) :
    ∫ s : ℝ, s ^ (k + 1) * SchwartzMap.derivCLM ℝ ℝ ρ s =
      -(((k : ℝ) + 1) * ∫ s : ℝ, s ^ k * ρ s) := by
  have hu : ∀ x : ℝ, HasDerivAt (fun s : ℝ => s ^ (k + 1)) (((k : ℝ) + 1) * x ^ k) x := by
    intro x
    simpa using hasDerivAt_pow (k + 1) x
  have h1 : Integrable (fun s : ℝ => s ^ (k + 1) * SchwartzMap.derivCLM ℝ ℝ ρ s) :=
    fhpbb2t_integrable_pow_mul _ (k + 1)
  have h2 : Integrable (fun s : ℝ => ((k : ℝ) + 1) * s ^ k * ρ s) := by
    simpa only [mul_assoc] using (fhpbb2t_integrable_pow_mul ρ k).const_mul ((k : ℝ) + 1)
  have h3 : Integrable (fun s : ℝ => s ^ (k + 1) * ρ s) := fhpbb2t_integrable_pow_mul ρ (k + 1)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun s : ℝ => s ^ (k + 1)) (v := ⇑ρ)
    (u' := fun s : ℝ => ((k : ℝ) + 1) * s ^ k) (v' := ⇑(SchwartzMap.derivCLM ℝ ℝ ρ))
    (fun x _ => hu x) (fun x _ => fhpbb2t_hasDerivAt ρ x) h1 h2 h3
  rw [key]
  congr 1
  rw [← integral_const_mul]
  congr 1
  ext s
  ring

/-- **The Fourier–moment bridge.** If the Fourier transform of a real Schwartz `η` (Mathlib's
phase) equals `1` near `0`, then `∫ η = 1` and all higher moments of `η` vanish. -/
theorem fhpbb2t_cutoff_moment (η : 𝓢(ℝ, ℝ))
    (h1 : ∀ᶠ τ in 𝓝 (0 : ℝ), 𝓕 (fun t : ℝ => (η t : ℂ)) τ = 1) (k : ℕ) :
    ∫ s : ℝ, s ^ k * η s = if k = 0 then 1 else 0 := by
  set f : ℝ → ℂ := fun t => (η t : ℂ) with hf
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (⊤ : ℕ∞) → Integrable (fun x : ℝ => x ^ n • f x) := by
    intro n _
    refine ((fhpbb2t_integrable_pow_mul η n).ofReal (𝕜 := ℂ)).congr (ae_of_all _ fun x => ?_)
    show ((x ^ n * η x : ℝ) : ℂ) = _
    simp only [hf, Complex.real_smul, Complex.ofReal_mul]
  have hD := Real.iteratedDeriv_fourier (f := f) (N := ⊤) (n := k) hint le_top
  have hL : iteratedDeriv k (𝓕 f) 0 = if k = 0 then 1 else 0 := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq k (f := 𝓕 f) (g := fun _ => (1 : ℂ)) h1,
      iteratedDeriv_const]
  have hL2 : ∫ v : ℝ, (-2 * (Real.pi : ℂ) * I * (v : ℂ)) ^ k * f v =
      if k = 0 then 1 else 0 := by
    rw [← hL, hD, Real.fourier_real_eq]
    congr 1
    ext v
    simp
  have hL3 : ∫ v : ℝ, (-2 * (Real.pi : ℂ) * I * (v : ℂ)) ^ k * f v =
      (-2 * (Real.pi : ℂ) * I) ^ k * ((∫ v : ℝ, v ^ k * η v : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul]
    congr 1
    ext v
    simp only [hf, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  rw [hL3] at hL2
  have hc : (-2 * (Real.pi : ℂ) * I) ^ k ≠ 0 :=
    pow_ne_zero _ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])
  split_ifs at hL2 ⊢ with hk
  · subst hk
    rw [pow_zero, one_mul] at hL2
    exact_mod_cast hL2
  · exact_mod_cast (mul_eq_zero.mp hL2).resolve_left hc

/-- **Moments of the derivatives.** If `∫ s^k η = δ_{k0}` for every `k`, then
`∫ s^k η^{(j)}(s) ds = (-1)^j j!` for `k = j` and `0` for `k ≠ j`. -/
theorem fhpbb2t_moment_iterate (η : 𝓢(ℝ, ℝ))
    (h0 : ∀ k : ℕ, ∫ s : ℝ, s ^ k * η s = if k = 0 then 1 else 0) (j k : ℕ) :
    ∫ s : ℝ, s ^ k * ((⇑(SchwartzMap.derivCLM ℝ ℝ))^[j] η) s =
      if k = j then (-1 : ℝ) ^ j * (j ! : ℝ) else 0 := by
  induction j generalizing k with
  | zero =>
    rw [Function.iterate_zero, id_eq, h0 k, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    cases k with
    | zero =>
      simp only [pow_zero, one_mul]
      rw [fhpbb2t_integral_deriv, ite_eq_right (by omega)]
    | succ k =>
      rw [fhpbb2t_moment_deriv, ih k]
      by_cases hk : k = j
      · subst hk
        rw [ite_eq_left rfl, ite_eq_left rfl, Nat.factorial_succ, Nat.cast_mul, pow_succ]
        push_cast
        ring
      · rw [ite_eq_right hk, ite_eq_right (by omega)]
        ring

end ParabolicRectifiability.FractionalKernel
