import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements

/-! # Lacunary series pairing

Uniform convergence and the integrability of the test kernel give the left pairing limit.
On the right, the explicit periodic-convergence hypothesis gives local periodic-`L²` convergence; Cauchy–Schwarz
on an interval containing the compact time support upgrades it to the weighted `L¹` limit.
The finite sums agree mode by mode by the supplied scalar representation identity and the normalization
`(ε a_j / √N_j) √(N_j/(2π)) = (2π)⁻¹ᐟ² ε a_j`.
-/

noncomputable section

open MeasureTheory
open Filter Topology Set
open ParabolicRectifiability
open ParabolicRectifiability.HalfTimeDerivative
open scoped ENNReal NNReal ContDiff

namespace ParabolicRectifiability.Examples

private def e2_rep2_toCoordinates (t : ℝ) : Coordinates 0 := (0, t)

private def e2_rep2_toFourier (t : ℝ) : FourierSpace 0 :=
  (fourierCoordinatesMeasurableEquiv 0).symm (e2_rep2_toCoordinates t)

private def e2_rep2_timeEquiv : ℝ ≃ᵐ FourierSpace 0 where
  toFun := e2_rep2_toFourier
  invFun := timeCoordinate 0
  left_inv := by intro t; simp [e2_rep2_toFourier, e2_rep2_toCoordinates]
  right_inv := by
    intro x
    apply (fourierCoordinatesMeasurableEquiv 0).injective
    change (0, timeCoordinate 0 x) = (fourierCoordinatesMeasurableEquiv 0) x
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  measurable_toFun :=
    (fourierCoordinatesMeasurableEquiv 0).symm.measurable.comp measurable_prodMk_left
  measurable_invFun := measurable_timeCoordinate 0

private def e2_rep2_timeHomeomorph : ℝ ≃ₜ FourierSpace 0 where
  toEquiv := e2_rep2_timeEquiv
  continuous_toFun := by
    change Continuous (fun t : ℝ =>
      (fourierCoordinatesHomeomorph 0).symm (0, t))
    exact (fourierCoordinatesHomeomorph 0).symm.continuous.comp
      (continuous_const.prodMk continuous_id)
  continuous_invFun := continuous_timeCoordinate 0

private theorem e2_rep2_timeMap_measurePreserving :
    MeasurePreserving e2_rep2_timeEquiv (volume : Measure ℝ)
      (volume : Measure (FourierSpace 0)) := by
  have hcoord : MeasurePreserving e2_rep2_toCoordinates (volume : Measure ℝ)
      (volume : Measure (Coordinates 0)) := by
    refine ⟨?_, ?_⟩
    · change Measurable (fun t : ℝ => (0, t))
      exact measurable_prodMk_left
    change Measure.map (fun t : ℝ => (0, t)) volume = (volume : Measure (Coordinates 0))
    rw [volume_coordinates_eq_prod 0, volume_euclideanSpace_eq_dirac (Fin 0),
      Measure.dirac_prod]
  change MeasurePreserving
    (fun t : ℝ => (fourierCoordinatesMeasurableEquiv 0).symm (0, t))
    (volume : Measure ℝ) (volume : Measure (FourierSpace 0))
  exact (fourierCoordinates_symm_measurePreserving_prod 0).comp hcoord

private theorem e2_rep2_timeIntegral (g : FourierSpace 0 → ℂ) :
    (∫ x, g x ∂(volume : Measure (FourierSpace 0))) =
      ∫ t, g (e2_rep2_toFourier t) :=
  (e2_rep2_timeMap_measurePreserving.integral_comp' g).symm

private theorem e2_rep2_left_partial_tendsto (hconv : LacunaryConvergenceStatement)
    (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (hε : 0 < ε) (hε' : ε ≤ 3 / 16)
    (hdata : IsLacunaryData a N) (φ : FourierSpace 0 → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Tendsto
      (fun m => ∫ x, ((ε * ∑ j ∈ Finset.range m,
        a j / Real.sqrt (N j) * Real.cos (N j * timeCoordinate 0 x) : ℝ) : ℂ) *
          testKernel (realCompactTest φ hφ hc) x)
      atTop
      (𝓝 (∫ x, (lacunaryFunction ε a N (timeCoordinate 0 x) : ℂ) *
        testKernel (realCompactTest φ hφ hc) x)) := by
  obtain ⟨hsummable, huniform⟩ := hconv ε a N hε hε' hdata
  let ψ := realCompactTest φ hφ hc
  have hψ : Integrable (testKernel ψ) volume := by
    apply integrable_testKernel_of_hasCompactSupport
    change IsCompact (tsupport (realCompactTest φ hφ hc))
    rw [tsupport_realCompactTest]
    exact hc
  have hcoeff : Summable (fun j => |a j / Real.sqrt (N j)|) := by
    simpa using hsummable 0
  let C : ℝ := |ε| * ∑' j, |a j / Real.sqrt (N j)|
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (abs_nonneg _) (tsum_nonneg fun j => abs_nonneg _)
  have hpartial_bound (m : ℕ) (x : FourierSpace 0) :
      |ε * ∑ j ∈ Finset.range m,
          a j / Real.sqrt (N j) * Real.cos (N j * timeCoordinate 0 x)| ≤ C := by
    dsimp [C]
    calc
      |ε * ∑ j ∈ Finset.range m,
          a j / Real.sqrt (N j) * Real.cos (N j * timeCoordinate 0 x)| =
          |ε| * |∑ j ∈ Finset.range m,
            a j / Real.sqrt (N j) * Real.cos (N j * timeCoordinate 0 x)| := abs_mul _ _
      _ ≤ |ε| * ∑ j ∈ Finset.range m,
            |a j / Real.sqrt (N j) * Real.cos (N j * timeCoordinate 0 x)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
      _ ≤ |ε| * ∑ j ∈ Finset.range m, |a j / Real.sqrt (N j)| := by
          apply mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j hj => ?_) (abs_nonneg _)
          rw [abs_mul]
          calc
            |a j / Real.sqrt (N j)| * |Real.cos (N j * timeCoordinate 0 x)| ≤
                |a j / Real.sqrt (N j)| * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
            _ = |a j / Real.sqrt (N j)| := mul_one _
      _ ≤ |ε| * ∑' j, |a j / Real.sqrt (N j)| := by
          gcongr
          exact hcoeff.sum_le_tsum (Finset.range m) (fun _ _ => abs_nonneg _)
  have hmeas : ∀ m : ℕ, AEStronglyMeasurable
      (fun x : FourierSpace 0 =>
        ((ε * ∑ j ∈ Finset.range m,
          a j / Real.sqrt (N j) * Real.cos (N j * timeCoordinate 0 x) : ℝ) : ℂ) *
          testKernel ψ x) volume := by
    intro m
    have hp : Continuous (fun x : FourierSpace 0 =>
        ε * ∑ j ∈ Finset.range m,
          a j / Real.sqrt (N j) * Real.cos (N j * timeCoordinate 0 x)) := by
      fun_prop
    exact (Complex.continuous_ofReal.comp hp).aestronglyMeasurable.mul
      (stronglyMeasurable_testKernel ψ).aestronglyMeasurable
  have hbound : ∀ m : ℕ, ∀ᵐ x ∂volume,
      ‖((ε * ∑ j ∈ Finset.range m,
          a j / Real.sqrt (N j) * Real.cos (N j * timeCoordinate 0 x) : ℝ) : ℂ) *
          testKernel ψ x‖ ≤ C * ‖testKernel ψ x‖ := by
    intro m
    filter_upwards [] with x
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hpartial_bound m x) (norm_nonneg _)
  have hpoint (x : FourierSpace 0) : Tendsto
      (fun m : ℕ => ((ε * ∑ j ∈ Finset.range m,
        a j / Real.sqrt (N j) * Real.cos (N j * timeCoordinate 0 x) : ℝ) : ℂ) *
          testKernel ψ x)
      atTop (𝓝 ((lacunaryFunction ε a N (timeCoordinate 0 x) : ℂ) * testKernel ψ x)) := by
    exact ((Complex.continuous_ofReal.tendsto _).comp
      (huniform.tendsto_at (timeCoordinate 0 x))).mul_const (testKernel ψ x)
  have hboundInt : Integrable (fun x : FourierSpace 0 => C * ‖testKernel ψ x‖) volume :=
    hψ.norm.const_mul C
  simpa [ψ] using tendsto_integral_of_dominated_convergence
    (fun x : FourierSpace 0 => C * ‖testKernel ψ x‖) hmeas hboundInt hbound
    (Eventually.of_forall hpoint)

private def e2_rep2_timeTest (φ : FourierSpace 0 → ℝ) : ℝ → ℝ :=
  fun t => φ (e2_rep2_toFourier t)

private theorem e2_rep2_timeTest_hasCompactSupport (φ : FourierSpace 0 → ℝ)
    (_hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    HasCompactSupport (e2_rep2_timeTest φ) := by
  change HasCompactSupport (φ ∘ (e2_rep2_timeHomeomorph : ℝ → FourierSpace 0))
  exact hc.comp_homeomorph e2_rep2_timeHomeomorph

private theorem e2_rep2_local_l1_tendsto {h : ℝ → ℝ} {S : ℕ → ℝ → ℝ}
    {φ : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β) (hh : Measurable h)
    (hS : ∀ m, Continuous (S m)) (hφ : Continuous φ)
    (hL2 : Tendsto (fun m => ∫⁻ t in Ioc α β,
      ENNReal.ofReal ((h t - S m t) ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun m => ∫⁻ t in Ioc α β,
      ENNReal.ofReal (|(S m t - h t) * φ t|)) atTop (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Ioc α β)
  let d (m : ℕ) (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal |h t - S m t|
  let q (m : ℕ) : ℝ≥0∞ := ∫⁻ t, d m t ∂μ
  let l2 (m : ℕ) : ℝ≥0∞ := ∫⁻ t in Ioc α β,
    ENNReal.ofReal ((h t - S m t) ^ 2)
  have hμfinite : μ univ ≠ (⊤ : ℝ≥0∞) := by
    change (volume.restrict (Ioc α β)) univ ≠ (⊤ : ℝ≥0∞)
    rw [Measure.restrict_apply_univ (Ioc α β)]
    exact ne_of_lt (measure_Ioc_lt_top (μ := volume))
  have hdmeas (m : ℕ) : AEMeasurable (d m) μ := by
    apply (ENNReal.continuous_ofReal.measurable.comp ?_).aemeasurable
    exact (measurable_abs.comp (hh.sub (hS m).measurable))
  have hL2' : Tendsto l2 atTop (𝓝 0) := by
    simpa only [l2, μ] using hL2
  have hd2 (m : ℕ) : ∫⁻ t, (d m t) ^ 2 ∂μ = l2 m := by
    change (∫⁻ t, (ENNReal.ofReal |h t - S m t|) ^ 2
        ∂(volume.restrict (Ioc α β))) =
      ∫⁻ t, ENNReal.ofReal ((h t - S m t) ^ 2)
        ∂(volume.restrict (Ioc α β))
    apply lintegral_congr_ae
    filter_upwards [] with t
    rw [← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
  have hqBound (m : ℕ) : q m ≤ μ univ ^ (1 / 2 : ℝ) *
      (l2 m) ^ (1 / 2 : ℝ) := by
    have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
      (f := fun _ => (1 : ℝ≥0∞)) (g := d m) aemeasurable_const (hdmeas m)
    have hCS' : q m ≤ μ univ ^ (1 / 2 : ℝ) *
        (∫⁻ t, (d m t) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
      simpa only [q, Pi.mul_apply, one_mul, ENNReal.one_rpow, one_pow,
        lintegral_one, ENNReal.rpow_two] using hCS
    rw [hd2] at hCS'
    exact hCS'
  have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  have hhalfnonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) := hhalfpos.le
  have hpow : Tendsto (fun m => (l2 m) ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    by simpa using hL2'.ennrpow_const (1 / 2 : ℝ)
  have hμhalf : μ univ ^ (1 / 2 : ℝ) ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg hhalfnonneg hμfinite
  have hroot : Tendsto (fun m => μ univ ^ (1 / 2 : ℝ) *
      (l2 m) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (ENNReal.continuous_const_mul hμhalf).continuousAt.tendsto.comp hpow
  have hq : Tendsto q atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hroot
      (fun _ => zero_le) hqBound
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ.continuousOn
  have hCnonneg : 0 ≤ C := by
    have h := hC α ⟨le_rfl, hαβ⟩
    exact (norm_nonneg _).trans h
  have hpoint (m : ℕ) (t : ℝ) (ht : t ∈ Ioc α β) :
      ENNReal.ofReal (|(S m t - h t) * φ t|) ≤ ENNReal.ofReal C * d m t := by
    have hφbound : |φ t| ≤ C := hC t ⟨ht.1.le, ht.2⟩
    have hleft : ENNReal.ofReal (|(S m t - h t) * φ t|) =
        ENNReal.ofReal (|S m t - h t| * |φ t|) := by
      rw [abs_mul]
    have hright : ENNReal.ofReal C * d m t =
        ENNReal.ofReal (C * |h t - S m t|) := by
      change ENNReal.ofReal C * ENNReal.ofReal |h t - S m t| = _
      rw [ENNReal.ofReal_mul hCnonneg]
    have habs : |S m t - h t| = |h t - S m t| := by rw [abs_sub_comm]
    rw [hleft, hright]
    apply ENNReal.ofReal_le_ofReal
    calc
      |S m t - h t| * |φ t| ≤ |S m t - h t| * C :=
        mul_le_mul_of_nonneg_left hφbound (abs_nonneg _)
      _ = C * |h t - S m t| := by rw [habs, mul_comm]
  have hscaled : Tendsto (fun m => ENNReal.ofReal C * q m) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).continuousAt.tendsto.comp hq
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscaled
    (fun _ => zero_le) ?_
  intro m
  calc
    ∫⁻ t in Ioc α β, ENNReal.ofReal (|(S m t - h t) * φ t|) ≤
        ∫⁻ t, ENNReal.ofReal C * d m t ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hpoint m t ht
    _ = ENNReal.ofReal C * q m := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem e2_rep2_modePairing (hpair : E2CosineKernelPairingStatement)
    (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (hdata : IsLacunaryData a N)
    (φ : FourierSpace 0 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (j : ℕ) :
    ∫ x, (((ε * (a j / Real.sqrt (N j)) : ℝ) : ℂ) *
        ((Real.cos (N j * timeCoordinate 0 x) : ℂ) *
          testKernel (realCompactTest φ hφ hc) x)) =
      ∫ x, (((Real.sqrt (2 * Real.pi))⁻¹ * ε * a j : ℝ) : ℂ) *
        ((Real.cos (N j * timeCoordinate 0 x) : ℂ) * (φ x : ℂ)) := by
  have hNjpos : 0 < (N j : ℝ) := by exact_mod_cast hdata.frequency_pos j
  have hNsqrt : 0 < Real.sqrt (N j : ℝ) := Real.sqrt_pos.2 hNjpos
  have hPisqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hcoef : ε * (a j / Real.sqrt (N j)) *
        Real.sqrt ((N j : ℝ) / (2 * Real.pi)) =
      (Real.sqrt (2 * Real.pi))⁻¹ * ε * a j := by
    rw [Real.sqrt_div (Nat.cast_nonneg _)]
    field_simp [hNsqrt.ne', hPisqrt.ne']
  rw [integral_const_mul, integral_const_mul]
  have hfreq : |(N j : ℝ)| = (N j : ℝ) := abs_of_nonneg hNjpos.le
  have hmode := hpair φ hφ hc (N j : ℝ)
  rw [hfreq] at hmode
  rw [hmode]
  calc
    ((ε * (a j / Real.sqrt (N j)) : ℝ) : ℂ) *
        (((Real.sqrt ((N j : ℝ) / (2 * Real.pi)) : ℝ) : ℂ) *
          ∫ x, (Real.cos (N j * timeCoordinate 0 x) : ℂ) * (φ x : ℂ)) =
      ((ε * (a j / Real.sqrt (N j)) *
        Real.sqrt ((N j : ℝ) / (2 * Real.pi)) : ℝ) : ℂ) *
          ∫ x, (Real.cos (N j * timeCoordinate 0 x) : ℂ) * (φ x : ℂ) := by
        calc
          _ = (((ε * (a j / Real.sqrt (N j)) : ℝ) : ℂ) *
              ((Real.sqrt ((N j : ℝ) / (2 * Real.pi)) : ℝ) : ℂ)) *
                ∫ x, (Real.cos (N j * timeCoordinate 0 x) : ℂ) * (φ x : ℂ) := by
              rw [mul_assoc]
          _ = ((ε * (a j / Real.sqrt (N j)) *
              Real.sqrt ((N j : ℝ) / (2 * Real.pi)) : ℝ) : ℂ) *
                ∫ x, (Real.cos (N j * timeCoordinate 0 x) : ℂ) * (φ x : ℂ) := by
              exact congrArg (fun z : ℂ => z *
                (∫ x, (Real.cos (N j * timeCoordinate 0 x) : ℂ) * (φ x : ℂ)))
                (Complex.ofReal_mul _ _).symm
    _ = (((Real.sqrt (2 * Real.pi))⁻¹ * ε * a j : ℝ) : ℂ) *
          ∫ x, (Real.cos (N j * timeCoordinate 0 x) : ℂ) * (φ x : ℂ) := by
        exact congrArg (fun z : ℂ => z *
          (∫ x, (Real.cos (N j * timeCoordinate 0 x) : ℂ) * (φ x : ℂ)))
          (congrArg (fun z : ℝ => (z : ℂ)) hcoef)

private theorem e2_rep2_finitePairing (hpair : E2CosineKernelPairingStatement)
    (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (hdata : IsLacunaryData a N)
    (φ : FourierSpace 0 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (m : ℕ) :
    ∫ x, ((ε * ∑ j ∈ Finset.range m,
        a j / Real.sqrt (N j) * Real.cos (N j * timeCoordinate 0 x) : ℝ) : ℂ) *
          testKernel (realCompactTest φ hφ hc) x =
      ∫ x, (e2_halfDerivPartialSum ε a N m (timeCoordinate 0 x) : ℂ) * (φ x : ℂ) := by
  let K : FourierSpace 0 → ℂ := testKernel (realCompactTest φ hφ hc)
  let F (j : ℕ) (x : FourierSpace 0) : ℂ :=
    (((ε * (a j / Real.sqrt (N j)) : ℝ) : ℂ) *
      ((Real.cos (N j * timeCoordinate 0 x) : ℂ) * K x))
  let G (j : ℕ) (x : FourierSpace 0) : ℂ :=
    (((Real.sqrt (2 * Real.pi))⁻¹ * ε * a j : ℝ) : ℂ) *
      ((Real.cos (N j * timeCoordinate 0 x) : ℂ) * (φ x : ℂ))
  have hKint : Integrable K volume := by
    dsimp [K]
    exact integrable_testKernel_of_hasCompactSupport _ (by
      change IsCompact (tsupport (realCompactTest φ hφ hc))
      rw [tsupport_realCompactTest]
      exact hc)
  have hcos (j : ℕ) : AEStronglyMeasurable
      (fun x : FourierSpace 0 => (Real.cos (N j * timeCoordinate 0 x) : ℂ)) volume := by
    exact (Complex.continuous_ofReal.comp (by fun_prop)).aestronglyMeasurable
  have hcosBound (j : ℕ) : ∀ᵐ x ∂volume,
      ‖(Real.cos (N j * timeCoordinate 0 x) : ℂ)‖ ≤ 1 := by
    filter_upwards [] with x
    rw [Complex.norm_real]
    exact Real.abs_cos_le_one _
  have hFint (j : ℕ) : Integrable (F j) volume := by
    apply (hKint.bdd_mul (hcos j) (hcosBound j)).const_mul
  have hφint : Integrable (fun x : FourierSpace 0 => (φ x : ℂ)) volume :=
    (hφ.continuous.integrable_of_hasCompactSupport hc).ofReal
  have hGint (j : ℕ) : Integrable (G j) volume := by
    apply (hφint.bdd_mul (hcos j) (hcosBound j)).const_mul
  have hleftPoint (x : FourierSpace 0) :
      ((ε * ∑ j ∈ Finset.range m,
          a j / Real.sqrt (N j) * Real.cos (N j * timeCoordinate 0 x) : ℝ) : ℂ) * K x =
        ∑ j ∈ Finset.range m, F j x := by
    simp only [F, Complex.ofReal_mul, Complex.ofReal_sum]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hrightPoint (x : FourierSpace 0) :
      (e2_halfDerivPartialSum ε a N m (timeCoordinate 0 x) : ℂ) * (φ x : ℂ) =
        ∑ j ∈ Finset.range m, G j x := by
    simp only [G, e2_halfDerivPartialSum, Complex.ofReal_mul, Complex.ofReal_sum]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    ∫ x, ((ε * ∑ j ∈ Finset.range m,
        a j / Real.sqrt (N j) * Real.cos (N j * timeCoordinate 0 x) : ℝ) : ℂ) * K x =
      ∫ x, ∑ j ∈ Finset.range m, F j x :=
        integral_congr_ae (Eventually.of_forall fun x => hleftPoint x)
    _ = ∑ j ∈ Finset.range m, ∫ x, F j x :=
      integral_finsetSum _ (fun j hj => hFint j)
    _ = ∑ j ∈ Finset.range m, ∫ x, G j x := by
      apply Finset.sum_congr rfl
      intro j hj
      exact e2_rep2_modePairing hpair ε a N hdata φ hφ hc j
    _ = ∫ x, ∑ j ∈ Finset.range m, G j x :=
      (integral_finsetSum _ (fun j hj => hGint j)).symm
    _ = ∫ x, (e2_halfDerivPartialSum ε a N m (timeCoordinate 0 x) : ℂ) * (φ x : ℂ) :=
      integral_congr_ae (Eventually.of_forall fun x => (hrightPoint x).symm)

private theorem e2_rep2_rightPartialTendsto (hlocal : E2PeriodicLocalStatement)
    (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (h : ℝ → ℝ)
    (hh : E2IsPeriodicHalfDerivative ε a N h)
    (φ : FourierSpace 0 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Tendsto (fun m => ∫ x,
      (e2_halfDerivPartialSum ε a N m (timeCoordinate 0 x) : ℂ) * (φ x : ℂ)) atTop
      (𝓝 (∫ x, (h (timeCoordinate 0 x) : ℂ) * (φ x : ℂ))) := by
  let ψ : ℝ → ℝ := e2_rep2_timeTest φ
  let S : ℕ → ℝ → ℝ := fun m t => e2_halfDerivPartialSum ε a N m t
  let U (m : ℕ) (t : ℝ) : ℝ := S m t * ψ t
  let V (t : ℝ) : ℝ := h t * ψ t
  have hψcont : Continuous ψ := by
    dsimp [ψ, e2_rep2_timeTest]
    exact hφ.continuous.comp e2_rep2_timeHomeomorph.continuous_toFun
  have hψcompact : HasCompactSupport ψ := by
    exact e2_rep2_timeTest_hasCompactSupport φ hφ hc
  obtain ⟨R, hRpos, hR⟩ := (hψcompact.image continuous_id).isBounded.exists_pos_norm_le
  have hRsupport (t : ℝ) (ht : t ∈ tsupport ψ) : |t| ≤ R := by
    simpa only [Real.norm_eq_abs] using hR t ⟨t, ht, rfl⟩
  let α : ℝ := -(R + 1)
  let β : ℝ := R + 1
  have hαβ : α ≤ β := by dsimp [α, β]; linarith
  have hψzero (t : ℝ) (ht : t ∉ Ioc α β) : ψ t = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro ht'
    have htb := hRsupport t ht'
    have hnot : ¬(α < t ∧ t ≤ β) := by simpa only [mem_Ioc] using ht
    rcases not_and_or.mp hnot with hleft | hright
    · have hleft' : t ≤ α := le_of_not_gt hleft
      have hlow := (abs_le.mp htb).1
      dsimp [α] at hleft'
      linarith
    · have hright' : β < t := lt_of_not_ge hright
      have hupp := (abs_le.mp htb).2
      dsimp [β] at hright'
      linarith
  obtain ⟨hlocalInt, hlocalIntervals⟩ := hlocal ε a N h hh
  have hL2 := (hlocalIntervals α β).2
  have hScont (m : ℕ) : Continuous (S m) := by
    dsimp [S, e2_halfDerivPartialSum]
    fun_prop
  have hL1local : Tendsto (fun m => ∫⁻ t in Ioc α β,
      ENNReal.ofReal (|(S m t - h t) * ψ t|)) atTop (𝓝 0) := by
    apply e2_rep2_local_l1_tendsto hαβ hh.1 hScont hψcont
    simpa only [S] using hL2
  have hVint : Integrable V volume :=
    hlocalInt.integrable_smul_right_of_hasCompactSupport hψcont hψcompact
  have hUint (m : ℕ) : Integrable (U m) volume :=
    (hScont m).locallyIntegrable.integrable_smul_right_of_hasCompactSupport hψcont hψcompact
  have herrorSupport (m : ℕ) :
      Function.support (fun t => ‖U m t - V t‖ₑ) ⊆ Ioc α β := by
    intro t ht
    by_contra hout
    have hzero : U m t - V t = 0 := by simp [U, V, hψzero t hout]
    exact ht (by simp [hzero])
  have hnormEq (m : ℕ) : (fun t => ‖U m t - V t‖ₑ) =
      (fun t => ENNReal.ofReal (|(S m t - h t) * ψ t|)) := by
    funext t
    rw [Real.enorm_eq_ofReal_abs]
    congr 1
    dsimp [U, V]
    rw [← sub_mul]
  have hglobalL1Eq (m : ℕ) :
      ∫⁻ t, ‖U m t - V t‖ₑ ∂volume =
        ∫⁻ t in Ioc α β, ENNReal.ofReal (|(S m t - h t) * ψ t|) := by
    rw [← setLIntegral_eq_of_support_subset (herrorSupport m), hnormEq]
  have hL1global : Tendsto (fun m => ∫⁻ t, ‖U m t - V t‖ₑ ∂volume) atTop (𝓝 0) := by
    apply hL1local.congr'
    filter_upwards [] with m
    exact (hglobalL1Eq m).symm
  have hIreal : Tendsto (fun m => ∫ t, U m t) atTop (𝓝 (∫ t, V t)) :=
    tendsto_integral_of_L1 V hVint.aestronglyMeasurable
      (Eventually.of_forall hUint) hL1global
  have hIcomplex : Tendsto (fun m => ∫ t, ((U m t : ℝ) : ℂ)) atTop
      (𝓝 (∫ t, ((V t : ℝ) : ℂ))) := by
    simpa only [Function.comp_def, integral_complex_ofReal] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hIreal)
  have htimeEq : ∫ x, (h (timeCoordinate 0 x) : ℂ) * (φ x : ℂ) =
      ∫ t, ((V t : ℝ) : ℂ) := by
    rw [e2_rep2_timeIntegral]
    simp [V, ψ, e2_rep2_timeTest, e2_rep2_toFourier, e2_rep2_toCoordinates,
      Complex.ofReal_mul]
  convert hIcomplex using 1
  · funext m
    rw [e2_rep2_timeIntegral]
    simp [U, S, ψ, e2_rep2_timeTest, e2_rep2_toFourier, e2_rep2_toCoordinates,
      Complex.ofReal_mul]
  · exact congrArg (fun z : ℂ => 𝓝 z) htimeEq

theorem e2_series_pairing_proof :
    LacunaryConvergenceStatement → E2CosineKernelPairingStatement →
      E2PeriodicLocalStatement → E2SeriesPairingStatement := by
  intro hconv hpair hlocal ε a N hε hε' hdata h hperiodic φ hφ hc
  have hleft := e2_rep2_left_partial_tendsto hconv ε a N hε hε' hdata φ hφ hc
  have hright := e2_rep2_rightPartialTendsto hlocal ε a N h hperiodic φ hφ hc
  have hfinite (m : ℕ) := e2_rep2_finitePairing hpair ε a N hdata φ hφ hc m
  have hleft' : Tendsto (fun m => ∫ x,
      (e2_halfDerivPartialSum ε a N m (timeCoordinate 0 x) : ℂ) * (φ x : ℂ)) atTop
      (𝓝 (∫ x, (lacunaryFunction ε a N (timeCoordinate 0 x) : ℂ) *
        testKernel (realCompactTest φ hφ hc) x)) := by
    apply hleft.congr'
    filter_upwards [] with m
    exact hfinite m
  exact tendsto_nhds_unique hleft' hright

end ParabolicRectifiability.Examples

end
