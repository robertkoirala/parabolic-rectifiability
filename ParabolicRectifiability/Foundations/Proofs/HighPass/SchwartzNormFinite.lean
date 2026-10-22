import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements

/-! # Schwartz tests have finite weighted norm

Proof of `fhpbc_b1_schwartzNormFinite`, as `fhpbc_b1_schwartzNormFinite_proof`, of type
`FhpbcSchwartzNormFiniteStatement` (weight `1 + |t|`, `m = 0` included).

Route. With `a = ‖θ‖` and `b = ‖fderiv ℝ θ‖` (the operator norm) one has, pointwise,
`(1 + |t|) (‖θ x‖ₑ + ‖Dθ x e_t‖ₑ) ≤ ofReal ((1 + ‖x‖) (a x + b x))`, because `|t| ≤ ‖x‖` and
`‖e_t‖ = 1`. The real function `(1 + ‖x‖) (a + b)` is a sum of four terms `‖x‖^k ‖g x‖` with
`k ∈ {0,1}`, `g ∈ {θ, fderivCLM θ}`, each integrable by `SchwartzMap.integrable_pow_mul`.
Hence `∫⁻ ofReal(...) < ⊤`. -/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

variable {m : ℕ}

/-- The time vector is a unit vector (also for `m = 0`). -/
theorem fhpbb1n_norm_timeVector : ‖timeVector m‖ = 1 := by
  rw [timeVector, WithLp.prod_norm_eq_of_L2]
  simp

/-- The time coordinate is bounded by the norm. -/
theorem fhpbb1n_abs_time_le (x : FourierSpace m) : |(WithLp.ofLp x).2| ≤ ‖x‖ := by
  rw [WithLp.prod_norm_eq_of_L2]
  refine Real.abs_le_sqrt ?_
  simp only [Real.norm_eq_abs, sq_abs]
  have h : WithLp.snd x = (WithLp.ofLp x).2 := rfl
  rw [h]
  nlinarith [sq_nonneg ‖WithLp.fst x‖]

/-- The time derivative is bounded by the operator norm of the derivative. -/
theorem fhpbb1n_enorm_dt_le (θ : 𝓢(FourierSpace m, ℂ)) (x : FourierSpace m) :
    ‖fderiv ℝ (⇑θ) x (timeVector m)‖ₑ ≤ ENNReal.ofReal ‖fderiv ℝ (⇑θ) x‖ := by
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖fderiv ℝ (⇑θ) x (timeVector m)‖ ≤ ‖fderiv ℝ (⇑θ) x‖ * ‖timeVector m‖ :=
        (fderiv ℝ (⇑θ) x).le_opNorm _
    _ = ‖fderiv ℝ (⇑θ) x‖ := by rw [fhpbb1n_norm_timeVector, mul_one]

/-- The real majorant of the integrand of `N(θ)`. -/
def fhpbb1n_majorant (θ : 𝓢(FourierSpace m, ℂ)) (x : FourierSpace m) : ℝ :=
  (1 + ‖x‖) * (‖θ x‖ + ‖fderiv ℝ (⇑θ) x‖)

theorem fhpbb1n_integrable_majorant (θ : 𝓢(FourierSpace m, ℂ)) :
    Integrable (fhpbb1n_majorant θ) volume := by
  have h0 := θ.integrable_pow_mul volume 0
  have h1 := θ.integrable_pow_mul volume 1
  have h0' := (SchwartzMap.fderivCLM ℝ (FourierSpace m) ℂ θ).integrable_pow_mul volume 0
  have h1' := (SchwartzMap.fderivCLM ℝ (FourierSpace m) ℂ θ).integrable_pow_mul volume 1
  simp only [SchwartzMap.fderivCLM_apply] at h0' h1'
  have hsum := (h0.add h1).add (h0'.add h1')
  refine hsum.congr (Eventually.of_forall fun x => ?_)
  simp only [fhpbb1n_majorant, Pi.add_apply, pow_zero, pow_one, one_mul]
  ring

theorem fhpbb1n_le_majorant (θ : 𝓢(FourierSpace m, ℂ)) (x : FourierSpace m) :
    ENNReal.ofReal (1 + |(WithLp.ofLp x).2|) *
        (‖θ x‖ₑ + ‖fderiv ℝ (⇑θ) x (timeVector m)‖ₑ) ≤
      ENNReal.ofReal (fhpbb1n_majorant θ x) := by
  unfold fhpbb1n_majorant
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
    ofReal_norm]
  gcongr
  · exact fhpbb1n_abs_time_le x
  · exact (fhpbb1n_enorm_dt_le θ x)

/-- **Schwartz tests have finite weighted norm.** Every complex Schwartz test on `ℝ^m × ℝ` has finite weighted norm. -/
theorem fhpbc_b1_schwartzNormFinite_proof : FhpbcSchwartzNormFiniteStatement := by
  intro m θ
  unfold fhp_weightedTestNorm
  calc _ ≤ ∫⁻ x, ENNReal.ofReal (fhpbb1n_majorant θ x) :=
        lintegral_mono fun x => fhpbb1n_le_majorant θ x
    _ < ⊤ := (fhpbb1n_integrable_majorant θ).lintegral_lt_top

end ParabolicRectifiability.Foundations
