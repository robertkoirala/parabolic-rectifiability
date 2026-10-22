import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Foundations.Proofs.HighPassBracket.FibreKernel

/-! # The representation extends to spatially compact Schwartz tests

Proof of `fhpbc_c2_schwartzExtension`, in implication form over (b1)
(`HighPassWeightedPairingStatement`), `FhpbcBMOLogGrowthStatement` and
`FhpbcCorrectedTestStatement`.

Let `θ` be a real test with Schwartz complexification `Θ`, supported spatially in a compact `A`,
with `∫ θ = 0`, and let `T(Ψ) = ∫ halfTimeSpatialBracket G Ψ`.

* **Checkpoint 1** (`fhpbc2s_integrable_mul`): `g θ` is integrable. Schwartz decay gives
  `|θ(u,t)| ≤ 8 M (1 + |j|)^{-3}` on the cylinder `A × [j, j+1]`, `FhpbcBMOLogGrowthStatement` gives
  `∫_{A × [j,j+1]} |g| ≤ C (1 + log (2 + |j|)) ≤ 2 C (1 + |j|)`, and
  `Σ_{j ∈ ℤ} (1 + |j|)^{-2} < ∞`.
* **Checkpoint 2** (`fhpbc2s_integral_bracket_sub`): `T(Ψ₁ - Ψ₂) = T(Ψ₁) - T(Ψ₂)` whenever the
  spatial integrands of `Ψ₁, Ψ₂` are integrable for a.e. time and both brackets are integrable
  (the integrability clauses of (b1)). Linearity of the `L²` map `halfTimeDeriv` holds a.e. on
  `ℝ^m × ℝ`; it is transferred to a.e. spatial fibre through the measure-preserving time-first
  coordinates of `fhpa_ae_fibre_halfTimeDeriv` and `Measure.ae_ae_of_ae_prod`; then the spatial integrals and the time
  integrals are subtracted using those integrability clauses. No integral over the whole product
  is interchanged.
* **The limit.** With the corrected tests `θ_n` of `FhpbcCorrectedTestStatement` and their complexifications `Ψ_n`:
  the representation clause and the window limit of (b1) give `T(Ψ_n) = ∫ g θ_n`; checkpoint 2
  and the (b1) bound on `Ψ_n - Θ` (supported spatially in `A'`, mean zero) give
  `‖T(Ψ_n) - T(Θ)‖ ≤ C N(θ_n - θ) → 0`; dominated convergence with `|g θ_n| ≤ |g θ| + |D| |g ρ|`
  gives `∫ g θ_n → ∫ g θ`. Uniqueness of limits gives `T(Θ) = ∫ g θ`.

The coordinate lemma `fhpab12_timeFirst_measurePreserving` is taken from the proof of
`fhpa_ae_fibre_halfTimeDeriv`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- Proof-only shortcut, as in the construction of `testKernel`: the default
instance search for `ContinuousSMul ℝ (FourierSpace m)` on the `L²` product exceeds the heartbeat
budget. -/
local instance fhpbc2s_continuousSMul (m : ℕ) : ContinuousSMul ℝ (FourierSpace m) :=
  IsBoundedSMul.continuousSMul

/-! ## Real tests with a Schwartz complexification -/

/-- A real function whose complexification is a Schwartz map is smooth: it is `Re ∘ Θ`. -/
theorem fhpbc2s_contDiff {m : ℕ} {θ : FourierSpace m → ℝ} {Θ : 𝓢(FourierSpace m, ℂ)}
    (hΘ : ∀ x, Θ x = (θ x : ℂ)) : ContDiff ℝ ∞ θ := by
  have h : θ = Complex.reCLM ∘ Θ := funext fun x => by simp [hΘ x]
  rw [h]
  exact Complex.reCLM.contDiff.comp (Θ.smooth ⊤)

/-- Schwartz decay of a real test: `(1 + ‖x‖)^3 |θ x| ≤ M`. -/
theorem fhpbc2s_decay {m : ℕ} {θ : FourierSpace m → ℝ} {Θ : 𝓢(FourierSpace m, ℂ)}
    (hΘ : ∀ x, Θ x = (θ x : ℂ)) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, (1 + ‖x‖) ^ 3 * |θ x| ≤ M := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x, (1 + ‖x‖) ^ 3 * ‖iteratedFDeriv ℝ 0 Θ x‖ ≤ M :=
    ⟨_, SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (3, 0)) le_rfl le_rfl Θ⟩
  refine ⟨M, le_trans (by positivity) (hM 0), fun x => ?_⟩
  have h := hM x
  rwa [norm_iteratedFDeriv_zero, hΘ x, Complex.norm_real, Real.norm_eq_abs] at h

/-- The weighted norm of the complexification of a differentiable real function is the weighted
norm of the function. -/
theorem fhpbc2s_weightedTestNorm_ofReal {m : ℕ} {f : FourierSpace m → ℝ}
    (hf : Differentiable ℝ f) :
    fhp_weightedTestNorm (fun x => (f x : ℂ)) = fhp_weightedTestNorm f := by
  have h1 : ∀ x, ‖((f x : ℝ) : ℂ)‖ₑ = ‖f x‖ₑ := fun x =>
    enorm_eq_iff_norm_eq.2 (Complex.norm_real (f x))
  have h2 : ∀ x, ‖fderiv ℝ (fun y => (f y : ℂ)) x (timeVector m)‖ₑ =
      ‖fderiv ℝ f x (timeVector m)‖ₑ := by
    intro x
    have hfun : (fun y => (f y : ℂ)) = Complex.ofRealCLM ∘ f := by
      funext y
      simp only [Function.comp_apply, Complex.ofRealCLM_apply]
    have hd : fderiv ℝ (fun y => (f y : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ f x) := by
      rw [hfun]
      exact (Complex.ofRealCLM.hasFDerivAt.comp x (hf x).hasFDerivAt).fderiv
    rw [hd, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
    exact enorm_eq_iff_norm_eq.2 (Complex.norm_real _)
  simp only [fhp_weightedTestNorm, h1, h2]

/-! ## Checkpoint 1: integrability of `g θ` -/

/-- The space-time cylinders `A × J` of measurable sets are measurable. -/
theorem fhpbc2s_measurableSet_cylinder {m : ℕ} {A : Set (Spatial m)} (hA : MeasurableSet A)
    {J : Set ℝ} (hJ : MeasurableSet J) : MeasurableSet (fhp_cylinder A J) :=
  (fourierCoordinatesMeasurableEquiv m).measurable (hA.prod hJ)

/-- `Σ_{j ∈ ℤ} (1 + |j|)^{-2} < ∞`. -/
theorem fhpbc2s_summable_inv_sq : Summable (fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2) := by
  refine Summable.of_norm_bounded_eventually (Real.summable_one_div_int_pow.2 one_lt_two) ?_
  filter_upwards [eventually_cofinite_ne 0] with j hj
  have hj' : (j : ℝ) ≠ 0 := Int.cast_ne_zero.2 hj
  have hpos : (0 : ℝ) < (j : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact pow_pos (abs_pos.2 hj') 2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply one_div_le_one_div_of_le hpos
  rw [← sq_abs (j : ℝ)]
  exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2

/-- On the cylinder `A × [j, j+1]` a test with `(1 + ‖x‖)^3 |θ x| ≤ M` satisfies
`|θ x| ≤ 8 M / (1 + |j|)^3`. -/
theorem fhpbc2s_le_on_cylinder {m : ℕ} {θ : FourierSpace m → ℝ} {M : ℝ}
    (hM : ∀ x, (1 + ‖x‖) ^ 3 * |θ x| ≤ M) {A : Set (Spatial m)} (j : ℤ) {x : FourierSpace m}
    (hx : x ∈ fhp_cylinder A (Icc (0 + (j : ℝ)) (1 + j))) :
    |θ x| ≤ 8 * M / (1 + |(j : ℝ)|) ^ 3 := by
  have hx' : (WithLp.ofLp x).1 ∈ A ∧ (WithLp.ofLp x).2 ∈ Icc (0 + (j : ℝ)) (1 + j) := hx
  obtain ⟨-, ht1, ht2⟩ := hx'
  have htx : |(WithLp.ofLp x).2| ≤ ‖x‖ := by
    have h := WithLp.norm_snd_le (p := 2) (α := Spatial m) (β := ℝ) x
    rwa [Real.norm_eq_abs] at h
  have hj : |(j : ℝ)| ≤ |(WithLp.ofLp x).2| + 1 := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self (WithLp.ofLp x).2, neg_abs_le (WithLp.ofLp x).2]
  have h1 : 1 + |(j : ℝ)| ≤ 2 * (1 + ‖x‖) := by linarith [norm_nonneg x]
  have h2 : (1 + |(j : ℝ)|) ^ 3 ≤ (2 * (1 + ‖x‖)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h1 3
  rw [le_div_iff₀ (by positivity)]
  calc |θ x| * (1 + |(j : ℝ)|) ^ 3 ≤ |θ x| * (2 * (1 + ‖x‖)) ^ 3 :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = 8 * ((1 + ‖x‖) ^ 3 * |θ x|) := by ring
    _ ≤ 8 * M := by linarith [hM x]

/-- The real inequality behind the cylinder sum:
`C (1 + log (2 + a)) · 8 M / (1 + a)^3 ≤ 16 C' M / (1 + a)^2` for `C ≤ C'`, `0 ≤ C'`. -/
theorem fhpbc2s_term_le {Cg C' M a : ℝ} (hCC' : Cg ≤ C') (hC'0 : 0 ≤ C') (hM0 : 0 ≤ M)
    (ha : 0 ≤ a) :
    Cg * (1 + Real.log (2 + a)) * (8 * M / (1 + a) ^ 3) ≤ 16 * C' * M * (1 / (1 + a) ^ 2) := by
  have hq0 : 0 ≤ 8 * M / (1 + a) ^ 3 := by positivity
  have hlog0 : 0 ≤ Real.log (2 + a) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2 + a) ≤ 1 + a := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + a by linarith)
    linarith
  have hL : Cg * (1 + Real.log (2 + a)) ≤ C' * (2 * (1 + a)) :=
    calc Cg * (1 + Real.log (2 + a)) ≤ C' * (1 + Real.log (2 + a)) :=
          mul_le_mul_of_nonneg_right hCC' (by linarith)
      _ ≤ C' * (2 * (1 + a)) := mul_le_mul_of_nonneg_left (by linarith) hC'0
  calc Cg * (1 + Real.log (2 + a)) * (8 * M / (1 + a) ^ 3)
      ≤ C' * (2 * (1 + a)) * (8 * M / (1 + a) ^ 3) := mul_le_mul_of_nonneg_right hL hq0
    _ = 16 * C' * M * (1 / (1 + a) ^ 2) := by
        have hne : (1 + a) ≠ 0 := by positivity
        field_simp
        ring

/-- **Checkpoint 1.** If `g` has finite parabolic BMO seminorm and is locally integrable, and
the real test `θ` has a Schwartz complexification and is supported spatially in a compact set,
then `g θ` is integrable (`FhpbcBMOLogGrowthStatement` on the unit cylinders `A × [j, j+1]`). -/
theorem fhpbc2s_integrable_mul (hc1g : FhpbcBMOLogGrowthStatement) {m : ℕ}
    {g : FourierSpace m → ℝ}
    (hg : ∃ B : ℝ, HasStandardParabolicBMOBound m (g ∘ (fourierToParabolic m).symm) B)
    (hgl : LocallyIntegrable g volume) {θ : FourierSpace m → ℝ} {Θ : 𝓢(FourierSpace m, ℂ)}
    (hΘ : ∀ x, Θ x = (θ x : ℂ)) {A : Set (Spatial m)} (hA : IsCompact A)
    (hθA : fhp_IsSpatiallySupportedIn θ A) :
    Integrable (fun x => g x * θ x) := by
  obtain ⟨Cg, hCg⟩ := hc1g m g hg A hA.isBounded hA.measurableSet 0 1
  obtain ⟨M, hM0, hM⟩ := fhpbc2s_decay hΘ
  obtain ⟨C', hC'0, hCC'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ Cg ≤ C' :=
    ⟨max Cg 0, le_max_right _ _, le_max_left _ _⟩
  have hb0 : ∀ j : ℤ, 0 ≤ 16 * C' * M * (1 / (1 + |(j : ℝ)|) ^ 2) := fun j => by positivity
  have hbs : Summable (fun j : ℤ => 16 * C' * M * (1 / (1 + |(j : ℝ)|) ^ 2)) :=
    fhpbc2s_summable_inv_sq.mul_left _
  refine ⟨hgl.aestronglyMeasurable.mul (fhpbc2s_contDiff hΘ).continuous.aestronglyMeasurable, ?_⟩
  show ∫⁻ x, ‖g x * θ x‖ₑ < ⊤
  have hsupp : (Function.support fun x => ‖g x * θ x‖ₑ) ⊆
      ⋃ j : ℤ, fhp_cylinder A (Icc (0 + (j : ℝ)) (1 + j)) := by
    intro x hx
    rw [Function.mem_support] at hx
    have hθx : θ x ≠ 0 := fun h => hx (by rw [h, mul_zero, enorm_zero])
    have hxA : (WithLp.ofLp x).1 ∈ A := by
      by_contra h
      exact hθx (hθA x h)
    refine Set.mem_iUnion.2 ⟨⌊(WithLp.ofLp x).2⌋, ?_⟩
    show (WithLp.ofLp x).1 ∈ A ∧ (WithLp.ofLp x).2 ∈
      Icc (0 + ((⌊(WithLp.ofLp x).2⌋ : ℤ) : ℝ)) (1 + ((⌊(WithLp.ofLp x).2⌋ : ℤ) : ℝ))
    refine ⟨hxA, Set.mem_Icc.2 ⟨?_, ?_⟩⟩
    · rw [zero_add]
      exact Int.floor_le _
    · rw [add_comm]
      exact (Int.lt_floor_add_one _).le
  have hcyl : ∀ j : ℤ, ∫⁻ x in fhp_cylinder A (Icc (0 + (j : ℝ)) (1 + j)), ‖g x * θ x‖ₑ ≤
      ENNReal.ofReal (16 * C' * M * (1 / (1 + |(j : ℝ)|) ^ 2)) := by
    intro j
    have hmeas : MeasurableSet (fhp_cylinder A (Icc (0 + (j : ℝ)) (1 + j))) :=
      fhpbc2s_measurableSet_cylinder hA.measurableSet measurableSet_Icc
    have hq0 : 0 ≤ 8 * M / (1 + |(j : ℝ)|) ^ 3 := by positivity
    have hpt : ∀ x ∈ fhp_cylinder A (Icc (0 + (j : ℝ)) (1 + j)),
        ‖g x * θ x‖ₑ ≤ ‖g x‖ₑ * ENNReal.ofReal (8 * M / (1 + |(j : ℝ)|) ^ 3) := by
      intro x hx
      have hθle := fhpbc2s_le_on_cylinder hM j hx
      rw [enorm_mul, Real.enorm_eq_ofReal_abs (θ x)]
      gcongr
    calc ∫⁻ x in fhp_cylinder A (Icc (0 + (j : ℝ)) (1 + j)), ‖g x * θ x‖ₑ
        ≤ ∫⁻ x in fhp_cylinder A (Icc (0 + (j : ℝ)) (1 + j)),
            ‖g x‖ₑ * ENNReal.ofReal (8 * M / (1 + |(j : ℝ)|) ^ 3) :=
          setLIntegral_mono' hmeas hpt
      _ = (∫⁻ x in fhp_cylinder A (Icc (0 + (j : ℝ)) (1 + j)), ‖g x‖ₑ) *
            ENNReal.ofReal (8 * M / (1 + |(j : ℝ)|) ^ 3) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Cg * (1 + Real.log (2 + |(j : ℝ)|))) *
            ENNReal.ofReal (8 * M / (1 + |(j : ℝ)|) ^ 3) := by
          gcongr
          exact hCg j
      _ = ENNReal.ofReal
            (Cg * (1 + Real.log (2 + |(j : ℝ)|)) * (8 * M / (1 + |(j : ℝ)|) ^ 3)) :=
          (ENNReal.ofReal_mul' hq0).symm
      _ ≤ ENNReal.ofReal (16 * C' * M * (1 / (1 + |(j : ℝ)|) ^ 2)) :=
          ENNReal.ofReal_le_ofReal (fhpbc2s_term_le hCC' hC'0 hM0 (abs_nonneg _))
  calc ∫⁻ x, ‖g x * θ x‖ₑ
      = ∫⁻ x in ⋃ j : ℤ, fhp_cylinder A (Icc (0 + (j : ℝ)) (1 + j)), ‖g x * θ x‖ₑ :=
        (setLIntegral_eq_of_support_subset hsupp).symm
    _ ≤ ∑' j : ℤ, ∫⁻ x in fhp_cylinder A (Icc (0 + (j : ℝ)) (1 + j)), ‖g x * θ x‖ₑ :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' j : ℤ, ENNReal.ofReal (16 * C' * M * (1 / (1 + |(j : ℝ)|) ^ 2)) :=
        ENNReal.tsum_le_tsum hcyl
    _ = ENNReal.ofReal (∑' j : ℤ, 16 * C' * M * (1 / (1 + |(j : ℝ)|) ^ 2)) :=
        (ENNReal.ofReal_tsum_of_nonneg hb0 hbs).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-! ## Checkpoint 2: linearity of the bracket integral -/

/-- Linearity of `halfTimeDeriv` on almost every spatial fibre: for a.e. time `t`, for a.e.
`u`, `|D_t|^{1/2}(Ψ₁ - Ψ₂)(u,t) = |D_t|^{1/2}Ψ₁(u,t) - |D_t|^{1/2}Ψ₂(u,t)` for the chosen `L²`
representatives. The a.e. identity on `ℝ^m × ℝ` (linearity of the `L²` map) is pulled back along
the measure-preserving time-first coordinates of `fhpa_ae_fibre_halfTimeDeriv` and sliced with time outside. -/
theorem fhpbc2s_ae_fibre_halfTimeDeriv_sub {m : ℕ} (Ψ₁ Ψ₂ : 𝓢(FourierSpace m, ℂ)) :
    ∀ᵐ t : ℝ, ∀ᵐ u : Spatial m,
      halfTimeDeriv m (Ψ₁ - Ψ₂) (WithLp.toLp 2 (u, t)) =
        halfTimeDeriv m Ψ₁ (WithLp.toLp 2 (u, t)) - halfTimeDeriv m Ψ₂ (WithLp.toLp 2 (u, t)) := by
  have h0 : (⇑(halfTimeDeriv m (Ψ₁ - Ψ₂)) : FourierSpace m → ℂ) =ᵐ[volume]
      ⇑(halfTimeDeriv m Ψ₁) - ⇑(halfTimeDeriv m Ψ₂) := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  have h1 := (fhpab12_timeFirst_measurePreserving m).quasiMeasurePreserving.ae_eq_comp h0
  exact Measure.ae_ae_of_ae_prod h1

/-- Linearity of the spatial bracket at almost every time, given a.e. integrability of the two
spatial integrands. -/
theorem fhpbc2s_ae_bracket_sub {m : ℕ} (G : FourierSpace m → ℝ) (Ψ₁ Ψ₂ : 𝓢(FourierSpace m, ℂ))
    (h₁ : ∀ᵐ t : ℝ, Integrable (halfTimeSpatialIntegrand G Ψ₁ t))
    (h₂ : ∀ᵐ t : ℝ, Integrable (halfTimeSpatialIntegrand G Ψ₂ t)) :
    ∀ᵐ t : ℝ, halfTimeSpatialBracket G (Ψ₁ - Ψ₂) t =
      halfTimeSpatialBracket G Ψ₁ t - halfTimeSpatialBracket G Ψ₂ t := by
  filter_upwards [fhpbc2s_ae_fibre_halfTimeDeriv_sub Ψ₁ Ψ₂, h₁, h₂] with t ht hi₁ hi₂
  unfold halfTimeSpatialBracket
  rw [← integral_sub hi₁ hi₂]
  refine integral_congr_ae ?_
  filter_upwards [ht] with u hu
  simp only [halfTimeSpatialIntegrand, hu, mul_sub]

/-- **Checkpoint 2.** Linearity of the bracket integral `T(Ψ) = ∫ halfTimeSpatialBracket G Ψ`
under the integrability clauses of (b1): a.e. integrable spatial integrands and integrable
brackets for `Ψ₁` and `Ψ₂`. -/
theorem fhpbc2s_integral_bracket_sub {m : ℕ} (G : FourierSpace m → ℝ)
    (Ψ₁ Ψ₂ : 𝓢(FourierSpace m, ℂ))
    (h₁ : ∀ᵐ t : ℝ, Integrable (halfTimeSpatialIntegrand G Ψ₁ t))
    (h₂ : ∀ᵐ t : ℝ, Integrable (halfTimeSpatialIntegrand G Ψ₂ t))
    (hb₁ : Integrable (halfTimeSpatialBracket G Ψ₁))
    (hb₂ : Integrable (halfTimeSpatialBracket G Ψ₂)) :
    ∫ t, halfTimeSpatialBracket G (Ψ₁ - Ψ₂) t =
      (∫ t, halfTimeSpatialBracket G Ψ₁ t) - ∫ t, halfTimeSpatialBracket G Ψ₂ t := by
  rw [← integral_sub hb₁ hb₂]
  exact integral_congr_ae (fhpbc2s_ae_bracket_sub G Ψ₁ Ψ₂ h₁ h₂)

/-! ## The statement -/

/-- **The representation extends to spatially compact Schwartz tests**
(`fhpbc_c2_schwartzExtension`, implication form). -/
theorem fhpbc_c2_schwartzExtension_proof : HighPassWeightedPairingStatement →
    FhpbcBMOLogGrowthStatement → FhpbcCorrectedTestStatement →
    FhpbcSchwartzExtensionStatement := by
  intro hb1 hc1g hc2t m G g hG hg hrep θ Θ hΘ A hA hθA hθ0
  have hint : Integrable (fun x => g x * θ x) :=
    fhpbc2s_integrable_mul hc1g hg hrep.1 hΘ hA hθA
  refine ⟨hint, ?_⟩
  obtain ⟨A', ρ, D, θs, hA', hθA', hρs, hρc, hθs, hdom, hlim, hN⟩ :=
    hc2t m θ Θ hΘ A hA hθA hθ0
  obtain ⟨C, -, hC⟩ := hb1 m G hG A' hA'
  have hθd : Differentiable ℝ θ := (fhpbc2s_contDiff hΘ).differentiable (by simp)
  -- the complexified corrected tests
  let Ψ : ℕ → 𝓢(FourierSpace m, ℂ) := fun n => realCompactTest (θs n) (hθs n).1 (hθs n).2.1
  have hΨ : ∀ n x, Ψ n x = (θs n x : ℂ) := fun n x => realCompactTest_apply _ _ _ x
  have hΨA : ∀ n, fhp_IsSpatiallySupportedIn (⇑(Ψ n)) A' := fun n x hx => by
    rw [hΨ n x, (hθs n).2.2.2 x hx, Complex.ofReal_zero]
  have hΨ0 : ∀ n, ∫ x, Ψ n x = 0 := fun n => by
    simp_rw [hΨ n]
    rw [integral_complex_ofReal, (hθs n).2.2.1, Complex.ofReal_zero]
  have hΘA : fhp_IsSpatiallySupportedIn (⇑Θ) A' := fun x hx => by
    rw [hΘ x, hθA' x hx, Complex.ofReal_zero]
  have hΘ0 : ∫ x, Θ x = 0 := by
    simp_rw [hΘ]
    rw [integral_complex_ofReal, hθ0, Complex.ofReal_zero]
  obtain ⟨hΘi, hΘb, -, -⟩ := hC Θ hΘA hΘ0
  -- (1) `T(Ψ n) = ∫ g θ_n`: the window limits of (b1) and of the representation agree
  have hT : ∀ n, ∫ t, halfTimeSpatialBracket G (Ψ n) t = ((∫ x, g x * θs n x : ℝ) : ℂ) := by
    intro n
    obtain ⟨-, -, hwin, -⟩ := hC (Ψ n) (hΨA n) (hΨ0 n)
    obtain ⟨-, -, hrepn⟩ := hrep.2 (θs n) (hθs n).1 (hθs n).2.1 (hθs n).2.2.1
    rw [tendsto_nhds_unique hwin hrepn, ← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun x => (Complex.ofReal_mul _ _).symm)
  -- (2) `‖T(Ψ n) - T(Θ)‖ ≤ C N(θ_n - θ)`: checkpoint 2 and the (b1) bound on `Ψ n - Θ`
  have hkey : ∀ n, ‖(∫ t, halfTimeSpatialBracket G (Ψ n) t) -
      ∫ t, halfTimeSpatialBracket G Θ t‖ₑ ≤
        ENNReal.ofReal C * fhp_weightedTestNorm (fun x => θs n x - θ x) := by
    intro n
    obtain ⟨hΨi, hΨb, -, -⟩ := hC (Ψ n) (hΨA n) (hΨ0 n)
    have hdA : fhp_IsSpatiallySupportedIn (⇑(Ψ n - Θ)) A' := fun x hx => by
      rw [sub_apply, hΨA n x hx, hΘA x hx, sub_zero]
    have hd0 : ∫ x, (Ψ n - Θ) x = 0 := by
      simp only [sub_apply]
      rw [integral_sub (Ψ n).integrable Θ.integrable, hΨ0 n, hΘ0, sub_zero]
    obtain ⟨-, -, -, hbd⟩ := hC (Ψ n - Θ) hdA hd0
    have hfun : (⇑(Ψ n - Θ) : FourierSpace m → ℂ) = fun x => ((θs n x - θ x : ℝ) : ℂ) := by
      funext x
      rw [sub_apply, hΨ n x, hΘ x, Complex.ofReal_sub]
    have hd : Differentiable ℝ (fun x => θs n x - θ x) :=
      ((hθs n).1.differentiable (by simp)).sub hθd
    rw [← fhpbc2s_integral_bracket_sub G (Ψ n) Θ hΨi hΘi hΨb hΘb,
      ← fhpbc2s_weightedTestNorm_ofReal hd, ← hfun]
    exact hbd
  have hconv : Tendsto (fun n => ∫ t, halfTimeSpatialBracket G (Ψ n) t) atTop
      (𝓝 (∫ t, halfTimeSpatialBracket G Θ t)) := by
    rw [tendsto_iff_edist_tendsto_0]
    have hlim0 : Tendsto (fun n => ENNReal.ofReal C * fhp_weightedTestNorm
        (fun x => θs n x - θ x)) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul hN (Or.inr ENNReal.ofReal_ne_top)
        (a := ENNReal.ofReal C)
      rwa [mul_zero] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim0
      (fun _ => zero_le) (fun n => ?_)
    rw [edist_eq_enorm_sub]
    exact hkey n
  -- (3) `∫ g θ_n → ∫ g θ` by dominated convergence
  have hgρ : Integrable (fun x => g x * ρ x) := by
    simpa only [smul_eq_mul] using
      hrep.1.integrable_smul_right_of_hasCompactSupport hρs.continuous hρc
  have hdct : Tendsto (fun n => ∫ x, g x * θs n x) atTop (𝓝 (∫ x, g x * θ x)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |g x * θ x| + |D| * |g x * ρ x|) (fun n => ?_) ?_ (fun n => ?_) ?_
    · exact hrep.1.aestronglyMeasurable.mul (hθs n).1.continuous.aestronglyMeasurable
    · exact hint.abs.add (hgρ.abs.const_mul _)
    · refine Eventually.of_forall fun x => ?_
      simp only [Real.norm_eq_abs, abs_mul]
      calc |g x| * |θs n x| ≤ |g x| * (|θ x| + D * |ρ x|) :=
            mul_le_mul_of_nonneg_left (hdom n x) (abs_nonneg _)
        _ = |g x| * |θ x| + D * (|g x| * |ρ x|) := by ring
        _ ≤ |g x| * |θ x| + |D| * (|g x| * |ρ x|) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_abs_self D) (by positivity))
    · exact Eventually.of_forall fun x => (hlim x).const_mul (g x)
  have hconv' : Tendsto (fun n => ∫ t, halfTimeSpatialBracket G (Ψ n) t) atTop
      (𝓝 ((∫ x, g x * θ x : ℝ) : ℂ)) := by
    simp_rw [hT]
    exact (Complex.continuous_ofReal.tendsto _).comp hdct
  exact tendsto_nhds_unique hconv hconv'

end ParabolicRectifiability.Foundations
