import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements

/-! # Corrected compact tests

Proof of `fhpbc_c2_correctedTest`, as `fhpbc_c2_correctedTest_proof`, of type
`FhpbcSchwartzNormFiniteStatement → FhpbcCorrectedTestStatement`.

Construction. `θ = Re ∘ Θ` is smooth and integrable. Fix
* the time cutoff `χ = fhpbc2t_chi` (a bump on `ℝ`: smooth, `0 ≤ χ ≤ 1`, `χ = 1` on `[-1,1]`,
  `χ = 0` off `(-2,2)`), and `χ_n(x) = χ(t/(n+1))` (`fhpbc2t_cutoff`, scale `n + 1`);
* a normalized bump `ρ = fhpbc2t_rho m` on `ℝ^m × ℝ` (smooth, compactly supported, `∫ ρ = 1`);
* `A' = A ∪ π(tsupport ρ)`, `π(u,t) = u`; `D = ∫ |θ|`;
* `a_n = ∫ χ_n θ` (`fhpbc2t_coeff`) and `θ_n = χ_n θ - a_n ρ` (`fhpbc2t_approx`).

Then `θ_n` is smooth with compact support in `π⁻¹(A) ∩ {|t| ≤ 2(n+1)}` united with `tsupport ρ`,
`∫ θ_n = a_n - a_n = 0`, `|a_n| ≤ D`, `a_n → ∫ θ = 0` and `θ_n → θ` pointwise (dominated
convergence). The **differentiated-cutoff estimate** is `fhpbc2t_abs_cutoff_dt_le`:
`|∂_t χ_n(x)| ≤ M/(n+1)` with `M = sup |χ'|`. With it,
`θ_n - θ = (χ_n - 1) θ - a_n ρ` and
`∂_t(θ_n - θ) = (χ_n - 1) ∂_tθ + θ ∂_tχ_n - a_n ∂_tρ`, so the integrand of `N(θ_n - θ)` is
dominated by `(1 + M) w_Θ + D w_ρ` (the integrands of `N(Θ) < ∞`, from `FhpbcSchwartzNormFiniteStatement`, and of `N(ρ) < ∞`) and
tends to `0` pointwise; dominated convergence for lower integrals gives `N(θ_n - θ) → 0`.

The formal statement asks for one compact `A'` supporting `θ` and every `θ_n`; this `A'` also
contains `A`. The bump `ρ` is not chosen as a product `ρ₁(u) ρ₂(t)`: the statement does not
need that structure.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- As in the construction of `testKernel`: a direct route to this instance;
proof-local. -/
local instance fhpbc2t_continuousSMul (m : ℕ) : ContinuousSMul ℝ (FourierSpace m) :=
  IsBoundedSMul.continuousSMul

variable {m : ℕ}

/-! ## The one-dimensional cutoff `χ` -/

/-- The cutoff `χ`: smooth, `0 ≤ χ ≤ 1`, `χ = 1` on `[-1,1]`, `χ = 0` off `(-2,2)`. -/
def fhpbc2t_chi : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩

theorem fhpbc2t_chi_contDiff : ContDiff ℝ ∞ fhpbc2t_chi := fhpbc2t_chi.contDiff

theorem fhpbc2t_chi_eq_one {t : ℝ} (ht : |t| ≤ 1) : fhpbc2t_chi t = 1 :=
  fhpbc2t_chi.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact ht)

theorem fhpbc2t_chi_eq_zero {t : ℝ} (ht : 2 ≤ |t|) : fhpbc2t_chi t = 0 :=
  fhpbc2t_chi.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact ht)

/-- `χ'` is bounded: `|χ'| ≤ M`. -/
theorem fhpbc2t_exists_deriv_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv fhpbc2t_chi t| ≤ M := by
  obtain ⟨C, hC⟩ := (fhpbc2t_chi_contDiff.continuous_deriv
    (by exact_mod_cast le_top)).bounded_above_of_compact_support
    fhpbc2t_chi.hasCompactSupport.deriv
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  have h := hC t
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-! ## The scaled time cutoff `χ_n(x) = χ(t/(n+1))` -/

/-- The scaled time coordinate `x ↦ t/(n+1)`. -/
def fhpbc2t_scale (m n : ℕ) : FourierSpace m →L[ℝ] ℝ := ((n : ℝ) + 1)⁻¹ • timeCoordinate m

theorem fhpbc2t_scale_apply (n : ℕ) (x : FourierSpace m) :
    fhpbc2t_scale m n x = ((n : ℝ) + 1)⁻¹ * (WithLp.ofLp x).2 := by
  rw [fhpbc2t_scale, smul_apply, smul_eq_mul, timeCoordinate_apply]

theorem fhpbc2t_scale_timeVector (n : ℕ) :
    fhpbc2t_scale m n (timeVector m) = ((n : ℝ) + 1)⁻¹ := by
  rw [fhpbc2t_scale, smul_apply, timeCoordinate_timeVector, smul_eq_mul,
    mul_one]

/-- The cutoff at scale `n + 1`: `χ_n(u,t) = χ(t/(n+1))`. -/
def fhpbc2t_cutoff (m n : ℕ) (x : FourierSpace m) : ℝ := fhpbc2t_chi (fhpbc2t_scale m n x)

theorem fhpbc2t_cutoff_nonneg (n : ℕ) (x : FourierSpace m) : 0 ≤ fhpbc2t_cutoff m n x :=
  fhpbc2t_chi.nonneg

theorem fhpbc2t_cutoff_le_one (n : ℕ) (x : FourierSpace m) : fhpbc2t_cutoff m n x ≤ 1 :=
  fhpbc2t_chi.le_one

theorem fhpbc2t_contDiff_cutoff (n : ℕ) : ContDiff ℝ ∞ (fhpbc2t_cutoff m n) :=
  fhpbc2t_chi_contDiff.comp (fhpbc2t_scale m n).contDiff

theorem fhpbc2t_hasFDerivAt_cutoff (n : ℕ) (x : FourierSpace m) :
    HasFDerivAt (fhpbc2t_cutoff m n)
      (deriv fhpbc2t_chi (fhpbc2t_scale m n x) • fhpbc2t_scale m n) x :=
  ((fhpbc2t_chi_contDiff.differentiable (by simp)) (fhpbc2t_scale m n x)).hasDerivAt.comp_hasFDerivAt
    x (fhpbc2t_scale m n).hasFDerivAt

theorem fhpbc2t_cutoff_dt (n : ℕ) (x : FourierSpace m) :
    fderiv ℝ (fhpbc2t_cutoff m n) x (timeVector m) =
      deriv fhpbc2t_chi (fhpbc2t_scale m n x) * ((n : ℝ) + 1)⁻¹ := by
  rw [(fhpbc2t_hasFDerivAt_cutoff n x).fderiv, smul_apply,
    fhpbc2t_scale_timeVector, smul_eq_mul]

/-- **The differentiated-cutoff estimate**: `|∂_t χ_n| ≤ M/(n+1)` whenever
`|χ'| ≤ M`. -/
theorem fhpbc2t_abs_cutoff_dt_le {M : ℝ} (hM : ∀ t, |deriv fhpbc2t_chi t| ≤ M) (n : ℕ)
    (x : FourierSpace m) :
    |fderiv ℝ (fhpbc2t_cutoff m n) x (timeVector m)| ≤ M * ((n : ℝ) + 1)⁻¹ := by
  rw [fhpbc2t_cutoff_dt, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹)]
  exact mul_le_mul_of_nonneg_right (hM _) (by positivity)

/-- `χ_n(x) = 1` as soon as `n + 1 ≥ |t|`. -/
theorem fhpbc2t_cutoff_eventually_one (x : FourierSpace m) :
    ∀ᶠ n : ℕ in atTop, fhpbc2t_cutoff m n x = 1 := by
  refine eventually_atTop.2 ⟨⌈|(WithLp.ofLp x).2|⌉₊, fun n hn => ?_⟩
  apply fhpbc2t_chi_eq_one
  rw [fhpbc2t_scale_apply, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹),
    inv_mul_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1), mul_one]
  have h1 : |(WithLp.ofLp x).2| ≤ (⌈|(WithLp.ofLp x).2|⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((⌈|(WithLp.ofLp x).2|⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- `χ_n(x) = 0` when `|t| ≥ 2(n+1)`. -/
theorem fhpbc2t_cutoff_eq_zero (n : ℕ) {x : FourierSpace m}
    (hx : 2 * ((n : ℝ) + 1) ≤ |(WithLp.ofLp x).2|) : fhpbc2t_cutoff m n x = 0 := by
  apply fhpbc2t_chi_eq_zero
  rw [fhpbc2t_scale_apply, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹),
    le_inv_mul_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  linarith

theorem fhpbc2t_cutoff_tendsto (x : FourierSpace m) :
    Tendsto (fun n : ℕ => fhpbc2t_cutoff m n x) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' ((fhpbc2t_cutoff_eventually_one x).mono fun _ hn => hn.symm)

theorem fhpbc2t_abs_cutoff_mul_le (n : ℕ) (θ : FourierSpace m → ℝ) (x : FourierSpace m) :
    |fhpbc2t_cutoff m n x * θ x| ≤ |θ x| := by
  rw [abs_mul, abs_of_nonneg (fhpbc2t_cutoff_nonneg n x)]
  exact mul_le_of_le_one_left (abs_nonneg _) (fhpbc2t_cutoff_le_one n x)

/-! ## The corrector bump `ρ` -/

/-- An auxiliary bump on `ℝ^m × ℝ`. -/
def fhpbc2t_bump (m : ℕ) : ContDiffBump (0 : FourierSpace m) := ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- The corrector `ρ`: smooth, compactly supported, `∫ ρ = 1`. -/
def fhpbc2t_rho (m : ℕ) : FourierSpace m → ℝ := (fhpbc2t_bump m).normed volume

theorem fhpbc2t_contDiff_rho (m : ℕ) : ContDiff ℝ ∞ (fhpbc2t_rho m) :=
  (fhpbc2t_bump m).contDiff_normed

theorem fhpbc2t_hasCompactSupport_rho (m : ℕ) : HasCompactSupport (fhpbc2t_rho m) :=
  (fhpbc2t_bump m).hasCompactSupport_normed

theorem fhpbc2t_integrable_rho (m : ℕ) : Integrable (fhpbc2t_rho m) :=
  (fhpbc2t_bump m).integrable_normed

theorem fhpbc2t_integral_rho (m : ℕ) : ∫ x, fhpbc2t_rho m x = 1 :=
  (fhpbc2t_bump m).integral_normed

/-! ## The weighted norm of compact smooth functions -/

theorem fhpbc2t_ofReal_mul_enorm {E : Type*} [NormedAddCommGroup E] {w : ℝ} (hw : 0 ≤ w)
    (a b : E) :
    ENNReal.ofReal w * (‖a‖ₑ + ‖b‖ₑ) = ENNReal.ofReal (w * (‖a‖ + ‖b‖)) := by
  rw [ENNReal.ofReal_mul hw, ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm,
    ofReal_norm]

theorem fhpbc2t_measurable_integrand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] (f : FourierSpace m → E)
    (hf : Measurable f) :
    Measurable fun x : FourierSpace m => ENNReal.ofReal (1 + |(WithLp.ofLp x).2|) *
      (‖f x‖ₑ + ‖fderiv ℝ f x (timeVector m)‖ₑ) :=
  (ENNReal.measurable_ofReal.comp (measurable_const.add (measurable_timeCoordinate m).abs)).mul
    (hf.enorm.add (measurable_fderiv_apply_const ℝ f (timeVector m)).enorm)

/-- `N(f) < ∞` for a real `C¹` function with compact support. -/
theorem fhpbc2t_weightedTestNorm_lt_top (f : FourierSpace m → ℝ) (hf : ContDiff ℝ ∞ f)
    (hcs : HasCompactSupport f) : fhp_weightedTestNorm f < ⊤ := by
  set g : FourierSpace m → ℝ := fun x =>
    (1 + |(WithLp.ofLp x).2|) * (‖f x‖ + ‖fderiv ℝ f x (timeVector m)‖) with hg
  have hgc : Continuous g :=
    (continuous_const.add (continuous_timeCoordinate m).abs).mul
      (hf.continuous.norm.add ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).norm)
  have hgs : HasCompactSupport g := by
    refine HasCompactSupport.intro hcs fun x hx => ?_
    have h1 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h2 : fderiv ℝ f x = 0 := by
      by_contra h
      exact hx (support_fderiv_subset ℝ h)
    simp [hg, h1, h2]
  calc fhp_weightedTestNorm f = ∫⁻ x, ENNReal.ofReal (g x) :=
        lintegral_congr fun x => fhpbc2t_ofReal_mul_enorm (by positivity) _ _
    _ < ⊤ := (hgc.integrable_of_hasCompactSupport hgs).lintegral_lt_top

/-! ## The real part `θ` of `Θ` -/

section Theta

variable {θ : FourierSpace m → ℝ} {Θ : 𝓢(FourierSpace m, ℂ)}

theorem fhpbc2t_theta_eq (hΘ : ∀ x, Θ x = (θ x : ℂ)) : θ = fun x => Complex.reCLM (Θ x) :=
  funext fun x => by simp [hΘ x]

theorem fhpbc2t_contDiff_theta (hΘ : ∀ x, Θ x = (θ x : ℂ)) : ContDiff ℝ ∞ θ := by
  rw [fhpbc2t_theta_eq hΘ]
  exact Complex.reCLM.contDiff.comp (Θ.smooth ⊤)

theorem fhpbc2t_integrable_theta (hΘ : ∀ x, Θ x = (θ x : ℂ)) : Integrable θ :=
  Θ.integrable.norm.mono' (fhpbc2t_contDiff_theta hΘ).continuous.aestronglyMeasurable
    (ae_of_all _ fun x => le_of_eq (by rw [hΘ x, Complex.norm_real]))

theorem fhpbc2t_abs_dt_theta_le (hΘ : ∀ x, Θ x = (θ x : ℂ)) (x : FourierSpace m) :
    |fderiv ℝ θ x (timeVector m)| ≤ ‖fderiv ℝ (⇑Θ) x (timeVector m)‖ := by
  have h : HasFDerivAt θ (Complex.reCLM.comp (fderiv ℝ (⇑Θ) x)) x := by
    rw [fhpbc2t_theta_eq hΘ]
    exact Complex.reCLM.hasFDerivAt.comp x Θ.differentiableAt.hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
  exact Complex.abs_re_le_norm _

theorem fhpbc2t_abs_theta_le (hΘ : ∀ x, Θ x = (θ x : ℂ)) (x : FourierSpace m) :
    |θ x| ≤ ‖Θ x‖ :=
  le_of_eq (by rw [hΘ x, Complex.norm_real, Real.norm_eq_abs])

end Theta

/-! ## The approximants `θ_n = χ_n θ - a_n ρ` -/

/-- `a_n = ∫ χ_n θ`. -/
def fhpbc2t_coeff (θ : FourierSpace m → ℝ) (n : ℕ) : ℝ := ∫ x, fhpbc2t_cutoff m n x * θ x

/-- `θ_n = χ_n θ - a_n ρ`. -/
def fhpbc2t_approx (θ : FourierSpace m → ℝ) (n : ℕ) (x : FourierSpace m) : ℝ :=
  fhpbc2t_cutoff m n x * θ x - fhpbc2t_coeff θ n * fhpbc2t_rho m x

section Approx

variable {θ : FourierSpace m → ℝ}

theorem fhpbc2t_contDiff_approx (hθ : ContDiff ℝ ∞ θ) (n : ℕ) :
    ContDiff ℝ ∞ (fhpbc2t_approx θ n) :=
  ((fhpbc2t_contDiff_cutoff n).mul hθ).sub (contDiff_const.mul (fhpbc2t_contDiff_rho m))

theorem fhpbc2t_integrable_cutoff_mul (hθc : Continuous θ) (hθi : Integrable θ) (n : ℕ) :
    Integrable fun x => fhpbc2t_cutoff m n x * θ x :=
  hθi.mono ((fhpbc2t_contDiff_cutoff n).continuous.mul hθc).aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact fhpbc2t_abs_cutoff_mul_le n θ x)

/-- `|a_n| ≤ ‖θ‖₁ = D`. -/
theorem fhpbc2t_abs_coeff_le (hθi : Integrable θ) (n : ℕ) :
    |fhpbc2t_coeff θ n| ≤ ∫ x, |θ x| := by
  have h := norm_integral_le_of_norm_le (μ := volume)
    (f := fun x => fhpbc2t_cutoff m n x * θ x) hθi.abs
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact fhpbc2t_abs_cutoff_mul_le n θ x)
  rw [Real.norm_eq_abs] at h
  exact h

/-- `a_n → ∫ θ = 0` (dominated convergence, domination `|θ|`). -/
theorem fhpbc2t_tendsto_coeff (hθc : Continuous θ) (hθi : Integrable θ) (hθ0 : ∫ x, θ x = 0) :
    Tendsto (fhpbc2t_coeff (m := m) θ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun n x => fhpbc2t_cutoff m n x * θ x) (f := θ) (fun x => |θ x|)
    (fun n => ((fhpbc2t_contDiff_cutoff n).continuous.mul hθc).aestronglyMeasurable) hθi.abs
    (fun n => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact fhpbc2t_abs_cutoff_mul_le n θ x)
    (ae_of_all _ fun x => by
      have h := (fhpbc2t_cutoff_tendsto (m := m) x).mul_const (θ x)
      rwa [one_mul] at h)
  rw [hθ0] at h
  exact h

theorem fhpbc2t_diff_apply (n : ℕ) (x : FourierSpace m) :
    fhpbc2t_approx θ n x - θ x =
      (fhpbc2t_cutoff m n x - 1) * θ x - fhpbc2t_coeff θ n * fhpbc2t_rho m x := by
  unfold fhpbc2t_approx
  ring

theorem fhpbc2t_hasFDerivAt_diff (hθ : ContDiff ℝ ∞ θ) (n : ℕ) (x : FourierSpace m) :
    HasFDerivAt (fun y => fhpbc2t_approx θ n y - θ y)
      ((fhpbc2t_cutoff m n x • fderiv ℝ θ x + θ x • fderiv ℝ (fhpbc2t_cutoff m n) x) -
          fhpbc2t_coeff θ n • fderiv ℝ (fhpbc2t_rho m) x - fderiv ℝ θ x) x := by
  have hθd : HasFDerivAt θ (fderiv ℝ θ x) x :=
    ((hθ.differentiable (by simp)) x).hasFDerivAt
  have hc : HasFDerivAt (fhpbc2t_cutoff m n) (fderiv ℝ (fhpbc2t_cutoff m n) x) x :=
    (fhpbc2t_hasFDerivAt_cutoff n x).differentiableAt.hasFDerivAt
  have hρ : HasFDerivAt (fhpbc2t_rho m) (fderiv ℝ (fhpbc2t_rho m) x) x :=
    (((fhpbc2t_contDiff_rho m).differentiable (by simp)) x).hasFDerivAt
  exact ((hc.mul hθd).sub (hρ.const_mul (fhpbc2t_coeff θ n))).sub hθd

/-- `∂_t(θ_n - θ) = (χ_n - 1) ∂_tθ + θ ∂_tχ_n - a_n ∂_tρ`. -/
theorem fhpbc2t_dt_diff (hθ : ContDiff ℝ ∞ θ) (n : ℕ) (x : FourierSpace m) :
    fderiv ℝ (fun y => fhpbc2t_approx θ n y - θ y) x (timeVector m) =
      (fhpbc2t_cutoff m n x - 1) * fderiv ℝ θ x (timeVector m) +
        θ x * fderiv ℝ (fhpbc2t_cutoff m n) x (timeVector m) -
        fhpbc2t_coeff θ n * fderiv ℝ (fhpbc2t_rho m) x (timeVector m) := by
  rw [(fhpbc2t_hasFDerivAt_diff hθ n x).fderiv]
  simp only [sub_apply, add_apply,
    smul_apply, smul_eq_mul]
  ring

/-- The pointwise algebra behind the domination. -/
theorem fhpbc2t_real_bound {c a e th dth Th dTh r dr M D : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (he : |e| ≤ M) (ha : |a| ≤ D) (hTh : |th| ≤ Th) (hdTh : |dth| ≤ dTh) :
    ‖(c - 1) * th - a * r‖ + ‖(c - 1) * dth + th * e - a * dr‖ ≤
      (1 + M) * (Th + dTh) + D * (‖r‖ + ‖dr‖) := by
  simp only [Real.norm_eq_abs]
  have hc : |c - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans he
  have hdTh0 : 0 ≤ dTh := (abs_nonneg _).trans hdTh
  have hTh0 : 0 ≤ Th := (abs_nonneg _).trans hTh
  have k1 : |(c - 1) * th| ≤ Th := by
    rw [abs_mul]
    calc |c - 1| * |th| ≤ 1 * Th := mul_le_mul hc hTh (abs_nonneg _) zero_le_one
      _ = Th := one_mul _
  have k2 : |(c - 1) * dth| ≤ dTh := by
    rw [abs_mul]
    calc |c - 1| * |dth| ≤ 1 * dTh := mul_le_mul hc hdTh (abs_nonneg _) zero_le_one
      _ = dTh := one_mul _
  have k3 : |a * r| ≤ D * |r| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have k4 : |a * dr| ≤ D * |dr| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have k5 : |th * e| ≤ Th * M := by
    rw [abs_mul]; exact mul_le_mul hTh he (abs_nonneg _) hTh0
  have s1 : |(c - 1) * th - a * r| ≤ |(c - 1) * th| + |a * r| := by
    have := abs_add_le ((c - 1) * th) (-(a * r))
    rwa [abs_neg, ← sub_eq_add_neg] at this
  have s2 : |(c - 1) * dth + th * e - a * dr| ≤ |(c - 1) * dth| + |th * e| + |a * dr| := by
    have h1 := abs_add_le ((c - 1) * dth + th * e) (-(a * dr))
    have h2 := abs_add_le ((c - 1) * dth) (th * e)
    rw [abs_neg, ← sub_eq_add_neg] at h1
    linarith
  have hMd : 0 ≤ M * dTh := mul_nonneg hM hdTh0
  linarith

end Approx

/-! ## The approximation in `N` -/

section Norm

variable {θ : FourierSpace m → ℝ} {Θ : 𝓢(FourierSpace m, ℂ)}

/-- The domination of the integrand of `N(θ_n - θ)`. -/
theorem fhpbc2t_integrand_le (hΘ : ∀ x, Θ x = (θ x : ℂ)) {M D : ℝ}
    (hM : ∀ t, |deriv fhpbc2t_chi t| ≤ M) (hM0 : 0 ≤ M) (hD0 : 0 ≤ D)
    (hD : ∀ n, |fhpbc2t_coeff θ n| ≤ D) (n : ℕ) (x : FourierSpace m) :
    ENNReal.ofReal (1 + |(WithLp.ofLp x).2|) *
        (‖fhpbc2t_approx θ n x - θ x‖ₑ +
          ‖fderiv ℝ (fun y => fhpbc2t_approx θ n y - θ y) x (timeVector m)‖ₑ) ≤
      ENNReal.ofReal (1 + M) * (ENNReal.ofReal (1 + |(WithLp.ofLp x).2|) *
          (‖Θ x‖ₑ + ‖fderiv ℝ (⇑Θ) x (timeVector m)‖ₑ)) +
        ENNReal.ofReal D * (ENNReal.ofReal (1 + |(WithLp.ofLp x).2|) *
          (‖fhpbc2t_rho m x‖ₑ + ‖fderiv ℝ (fhpbc2t_rho m) x (timeVector m)‖ₑ)) := by
  have hw : (0 : ℝ) ≤ 1 + |(WithLp.ofLp x).2| := by positivity
  have hM1 : (0 : ℝ) ≤ 1 + M := by linarith
  have hθc := fhpbc2t_contDiff_theta hΘ
  have he : |fderiv ℝ (fhpbc2t_cutoff m n) x (timeVector m)| ≤ M := by
    refine (fhpbc2t_abs_cutoff_dt_le hM n x).trans ?_
    have hk : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
    exact mul_le_of_le_one_right hM0 hk
  have hb := fhpbc2t_real_bound (fhpbc2t_cutoff_nonneg n x) (fhpbc2t_cutoff_le_one n x) he
    (hD n) (fhpbc2t_abs_theta_le hΘ x) (fhpbc2t_abs_dt_theta_le hΘ x)
    (r := fhpbc2t_rho m x) (dr := fderiv ℝ (fhpbc2t_rho m) x (timeVector m))
  calc ENNReal.ofReal (1 + |(WithLp.ofLp x).2|) *
        (‖fhpbc2t_approx θ n x - θ x‖ₑ +
          ‖fderiv ℝ (fun y => fhpbc2t_approx θ n y - θ y) x (timeVector m)‖ₑ)
      = ENNReal.ofReal ((1 + |(WithLp.ofLp x).2|) *
        (‖(fhpbc2t_cutoff m n x - 1) * θ x - fhpbc2t_coeff θ n * fhpbc2t_rho m x‖ +
          ‖(fhpbc2t_cutoff m n x - 1) * fderiv ℝ θ x (timeVector m) +
              θ x * fderiv ℝ (fhpbc2t_cutoff m n) x (timeVector m) -
            fhpbc2t_coeff θ n * fderiv ℝ (fhpbc2t_rho m) x (timeVector m)‖)) := by
        rw [fhpbc2t_ofReal_mul_enorm hw, fhpbc2t_dt_diff hθc, fhpbc2t_diff_apply]
    _ ≤ ENNReal.ofReal ((1 + M) * ((1 + |(WithLp.ofLp x).2|) *
            (‖Θ x‖ + ‖fderiv ℝ (⇑Θ) x (timeVector m)‖)) +
          D * ((1 + |(WithLp.ofLp x).2|) *
            (‖fhpbc2t_rho m x‖ + ‖fderiv ℝ (fhpbc2t_rho m) x (timeVector m)‖))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc _ ≤ (1 + |(WithLp.ofLp x).2|) *
              ((1 + M) * (‖Θ x‖ + ‖fderiv ℝ (⇑Θ) x (timeVector m)‖) +
                D * (‖fhpbc2t_rho m x‖ + ‖fderiv ℝ (fhpbc2t_rho m) x (timeVector m)‖)) :=
              mul_le_mul_of_nonneg_left hb hw
          _ = _ := by ring
    _ = _ := by
        rw [ENNReal.ofReal_add
            (mul_nonneg hM1 (mul_nonneg hw (add_nonneg (norm_nonneg _) (norm_nonneg _))))
            (mul_nonneg hD0 (mul_nonneg hw (add_nonneg (norm_nonneg _) (norm_nonneg _)))),
          ENNReal.ofReal_mul hM1, ENNReal.ofReal_mul hD0, fhpbc2t_ofReal_mul_enorm hw,
          fhpbc2t_ofReal_mul_enorm hw]

/-- The integrand of `N(θ_n - θ)` tends to `0` at every point. -/
theorem fhpbc2t_integrand_tendsto (hΘ : ∀ x, Θ x = (θ x : ℂ)) {M : ℝ}
    (hM : ∀ t, |deriv fhpbc2t_chi t| ≤ M) (ha : Tendsto (fhpbc2t_coeff (m := m) θ) atTop (𝓝 0))
    (x : FourierSpace m) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (1 + |(WithLp.ofLp x).2|) *
        (‖fhpbc2t_approx θ n x - θ x‖ₑ +
          ‖fderiv ℝ (fun y => fhpbc2t_approx θ n y - θ y) x (timeVector m)‖ₑ)) atTop (𝓝 0) := by
  have hw : (0 : ℝ) ≤ 1 + |(WithLp.ofLp x).2| := by positivity
  have hθc := fhpbc2t_contDiff_theta hΘ
  have hc1 : Tendsto (fun n : ℕ => fhpbc2t_cutoff m n x - 1) atTop (𝓝 0) := by
    have h := (fhpbc2t_cutoff_tendsto (m := m) x).sub_const 1
    rwa [sub_self] at h
  have hk : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have he : Tendsto (fun n : ℕ => fderiv ℝ (fhpbc2t_cutoff m n) x (timeVector m)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n : ℕ => M * ((n : ℝ) + 1)⁻¹) (fun n => ?_) ?_
    · rw [Real.norm_eq_abs]
      exact fhpbc2t_abs_cutoff_dt_le hM n x
    · have h := hk.const_mul M
      rwa [mul_zero] at h
  have hα : Tendsto (fun n : ℕ =>
      (fhpbc2t_cutoff m n x - 1) * θ x - fhpbc2t_coeff θ n * fhpbc2t_rho m x) atTop (𝓝 0) := by
    have h := (hc1.mul_const (θ x)).sub (ha.mul_const (fhpbc2t_rho m x))
    rwa [zero_mul, zero_mul, sub_zero] at h
  have hβ : Tendsto (fun n : ℕ =>
      (fhpbc2t_cutoff m n x - 1) * fderiv ℝ θ x (timeVector m) +
        θ x * fderiv ℝ (fhpbc2t_cutoff m n) x (timeVector m) -
        fhpbc2t_coeff θ n * fderiv ℝ (fhpbc2t_rho m) x (timeVector m)) atTop (𝓝 0) := by
    have h := ((hc1.mul_const (fderiv ℝ θ x (timeVector m))).add (he.const_mul (θ x))).sub
      (ha.mul_const (fderiv ℝ (fhpbc2t_rho m) x (timeVector m)))
    rwa [zero_mul, mul_zero, add_zero, zero_mul, sub_zero] at h
  have h := ENNReal.tendsto_ofReal ((hα.norm.add hβ.norm).const_mul (1 + |(WithLp.ofLp x).2|))
  rw [norm_zero, add_zero, mul_zero, ENNReal.ofReal_zero] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  try dsimp only
  rw [fhpbc2t_ofReal_mul_enorm hw, fhpbc2t_dt_diff hθc, fhpbc2t_diff_apply]

/-- `N(θ_n - θ) → 0`. -/
theorem fhpbc2t_tendsto_weightedTestNorm (hN : FhpbcSchwartzNormFiniteStatement)
    (hΘ : ∀ x, Θ x = (θ x : ℂ)) (hθ0 : ∫ x, θ x = 0) :
    Tendsto (fun n : ℕ => fhp_weightedTestNorm (fun x => fhpbc2t_approx θ n x - θ x)) atTop
      (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := fhpbc2t_exists_deriv_bound
  have hθc := fhpbc2t_contDiff_theta hΘ
  have hθi := fhpbc2t_integrable_theta hΘ
  have hD0 : (0 : ℝ) ≤ ∫ x, |θ x| := integral_nonneg fun x => abs_nonneg _
  have hmΘ := fhpbc2t_measurable_integrand (m := m) (⇑Θ) Θ.continuous.measurable
  have hmρ := fhpbc2t_measurable_integrand (m := m) (fhpbc2t_rho m)
    (fhpbc2t_contDiff_rho m).continuous.measurable
  have hfin : ∫⁻ x, (ENNReal.ofReal (1 + M) * (ENNReal.ofReal (1 + |(WithLp.ofLp x).2|) *
          (‖Θ x‖ₑ + ‖fderiv ℝ (⇑Θ) x (timeVector m)‖ₑ)) +
        ENNReal.ofReal (∫ x, |θ x|) * (ENNReal.ofReal (1 + |(WithLp.ofLp x).2|) *
          (‖fhpbc2t_rho m x‖ₑ + ‖fderiv ℝ (fhpbc2t_rho m) x (timeVector m)‖ₑ))) ≠ ⊤ := by
    rw [lintegral_add_left (hmΘ.const_mul _), lintegral_const_mul _ hmΘ,
      lintegral_const_mul _ hmρ]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hN m Θ).ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (fhpbc2t_weightedTestNorm_lt_top (fhpbc2t_rho m)
          (fhpbc2t_contDiff_rho m) (fhpbc2t_hasCompactSupport_rho m)).ne⟩
  have h := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun n x => ENNReal.ofReal (1 + |(WithLp.ofLp x).2|) *
      (‖fhpbc2t_approx θ n x - θ x‖ₑ +
        ‖fderiv ℝ (fun y => fhpbc2t_approx θ n y - θ y) x (timeVector m)‖ₑ))
    (f := fun _ => 0) _
    (fun n => fhpbc2t_measurable_integrand (fun y => fhpbc2t_approx θ n y - θ y)
      ((fhpbc2t_contDiff_approx hθc n).continuous.sub hθc.continuous).measurable)
    (fun n => ae_of_all _ fun x => fhpbc2t_integrand_le hΘ hM hM0 hD0
      (fun k => fhpbc2t_abs_coeff_le hθi k) n x)
    hfin
    (ae_of_all _ fun x => fhpbc2t_integrand_tendsto hΘ hM
      (fhpbc2t_tendsto_coeff hθc.continuous hθi hθ0) x)
  simp only [lintegral_zero] at h
  exact h

end Norm

/-! ## The statement -/

/-- **Corrected compact tests** (`fhpbc_c2_correctedTest`):
`θ_n = χ_n θ - a_n ρ` with `A' = A ∪ π(tsupport ρ)` and `D = ∫ |θ|`. -/
theorem fhpbc_c2_correctedTest_proof : FhpbcSchwartzNormFiniteStatement →
    FhpbcCorrectedTestStatement := by
  intro hN m θ Θ hΘ A hA hθA hθ0
  have hθc := fhpbc2t_contDiff_theta hΘ
  have hθi := fhpbc2t_integrable_theta hΘ
  have hρs := fhpbc2t_hasCompactSupport_rho m
  refine ⟨A ∪ (fun x : FourierSpace m => (WithLp.ofLp x).1) '' tsupport (fhpbc2t_rho m),
    fhpbc2t_rho m, ∫ x, |θ x|, fhpbc2t_approx θ, ?_, ?_, fhpbc2t_contDiff_rho m, hρs,
    fun n => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, fhpbc2t_tendsto_weightedTestNorm hN hΘ hθ0⟩
  · -- `A'` is compact
    exact hA.union (hρs.isCompact.image
      (continuous_fst.comp (WithLp.prod_continuous_ofLp 2 (Spatial m) ℝ)))
  · -- `θ` is supported spatially in `A'`
    exact fun x hx => hθA x fun h => hx (Or.inl h)
  · -- `θ_n` is smooth
    exact fhpbc2t_contDiff_approx hθc n
  · -- `θ_n` has compact support
    refine HasCompactSupport.intro (K := (WithLp.toLp 2 : Spatial m × ℝ → FourierSpace m) ''
        (A ×ˢ Metric.closedBall (0 : ℝ) (2 * ((n : ℝ) + 1))) ∪ tsupport (fhpbc2t_rho m))
      (((hA.prod (isCompact_closedBall _ _)).image
        (WithLp.prod_continuous_toLp 2 (Spatial m) ℝ)).union hρs.isCompact) fun x hx => ?_
    have hρ0 : fhpbc2t_rho m x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (Or.inr h)
    have hcθ : fhpbc2t_cutoff m n x * θ x = 0 := by
      by_cases h1 : (WithLp.ofLp x).1 ∈ A
      · by_cases h2 : |(WithLp.ofLp x).2| ≤ 2 * ((n : ℝ) + 1)
        · exfalso
          refine hx (Or.inl ⟨WithLp.ofLp x, ⟨h1, ?_⟩, rfl⟩)
          rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
          exact h2
        · rw [fhpbc2t_cutoff_eq_zero n (le_of_lt (not_le.1 h2)), zero_mul]
      · rw [hθA x h1, mul_zero]
    unfold fhpbc2t_approx
    rw [hcθ, hρ0, mul_zero, sub_zero]
  · -- `∫ θ_n = 0`
    unfold fhpbc2t_approx
    rw [integral_sub (fhpbc2t_integrable_cutoff_mul hθc.continuous hθi n)
      ((fhpbc2t_integrable_rho m).const_mul _), integral_const_mul, fhpbc2t_integral_rho,
      mul_one]
    exact sub_self _
  · -- `θ_n` is supported spatially in `A'`
    intro x hx
    have hθx : θ x = 0 := hθA x fun h => hx (Or.inl h)
    have hρ0 : fhpbc2t_rho m x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hx (Or.inr ⟨x, h, rfl⟩)
    unfold fhpbc2t_approx
    rw [hθx, hρ0, mul_zero, mul_zero, sub_zero]
  · -- domination `|θ_n| ≤ |θ| + D |ρ|`
    intro n x
    unfold fhpbc2t_approx
    have s := abs_add_le (fhpbc2t_cutoff m n x * θ x) (-(fhpbc2t_coeff θ n * fhpbc2t_rho m x))
    rw [abs_neg, ← sub_eq_add_neg, abs_mul (fhpbc2t_coeff θ n)] at s
    have k1 := fhpbc2t_abs_cutoff_mul_le n θ x
    have k2 := mul_le_mul_of_nonneg_right (fhpbc2t_abs_coeff_le hθi n)
      (abs_nonneg (fhpbc2t_rho m x))
    linarith
  · -- pointwise convergence
    intro x
    have h := ((fhpbc2t_cutoff_tendsto (m := m) x).mul_const (θ x)).sub
      ((fhpbc2t_tendsto_coeff hθc.continuous hθi hθ0).mul_const (fhpbc2t_rho m x))
    rw [one_mul, zero_mul, sub_zero] at h
    exact h

end ParabolicRectifiability.Foundations
