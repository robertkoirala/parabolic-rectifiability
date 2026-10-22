import ParabolicRectifiability.Analysis.HalfTimeDerivative.LocalRepresentation

/-! # A real L2 inverse representative

The weighted Fourier transform is required to belong to L2. Its inverse is
identified as a distribution before realness is deduced by compact-test uniqueness.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory SchwartzMap FourierTransform
open scoped SchwartzMap ContDiff

namespace ParabolicRectifiability.HalfTimeDerivative

variable {m : ℕ}

/-- The actual weighted Fourier class; membership is an explicit hypothesis. -/
def inverseFrequency {f : Lp ℂ 2 (volume : Measure (FourierSpace m))}
    (hf : MemLp (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    Lp ℂ 2 (volume : Measure (FourierSpace m)) := hf.toLp _

theorem coeFn_inverseFrequency {f : Lp ℂ 2 (volume : Measure (FourierSpace m))}
    (hf : MemLp (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    (inverseFrequency (f := f) hf : FourierSpace m → ℂ) =ᵐ[volume] fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z :=
  hf.coeFn_toLp

/-- The inverse L2 Fourier transform of the weighted class. -/
def inverseHalf {f : Lp ℂ 2 (volume : Measure (FourierSpace m))}
    (hf : MemLp (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    Lp ℂ 2 (volume : Measure (FourierSpace m)) := 𝓕⁻ (inverseFrequency (f := f) hf)

/-- Changing the Fourier representative on a null set changes no weighted class. -/
theorem inverseFrequency_representative
    {f : Lp ℂ 2 (volume : Measure (FourierSpace m))}
    (hf : MemLp (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume)
    {v : FourierSpace m → ℂ} (hv : v =ᵐ[volume] (𝓕 f : Lp ℂ 2 volume)) :
    ∃ hvw : MemLp (fun z => (symbol z : ℂ) * v z) 2 volume,
      hvw.toLp (fun z => (symbol z : ℂ) * v z) = inverseFrequency (f := f) hf := by
  have he : (fun z => (symbol z : ℂ) * v z) =ᵐ[volume]
      (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) := (Filter.EventuallyEq.refl _ _).mul hv
  refine ⟨hf.ae_eq he.symm, ?_⟩
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans (he.trans (coeFn_inverseFrequency (f := f) hf).symm)

/-- The embedded weighted class has an absolutely integrable product with every Schwartz test. -/
theorem integrable_inverseFrequency_test
    {f : Lp ℂ 2 (volume : Measure (FourierSpace m))}
    (hf : MemLp (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 volume) z) 2 volume)
    (η : 𝓢(FourierSpace m, ℂ)) :
    Integrable (fun z => inverseFrequency hf z * η z) volume :=
  (Lp.memLp _).integrable_mul (η.memLp 2 volume)

theorem frequencyDistribution_eq_inverseFrequency
    {f : Lp ℂ 2 (volume : Measure (FourierSpace m))}
    (hf : MemLp (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    frequencyDistribution f = (inverseFrequency (f := f) hf : 𝓢'(FourierSpace m, ℂ)) := by
  ext η
  change frequencyFunctional f η = _
  rw [frequencyFunctional_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [coeFn_inverseFrequency (f := f) hf] with z hz
  simp only [hz, smul_eq_mul]
  ring

/-- Compatibility of the inverse class with the half-time distribution. -/
theorem inverseHalf_distribution {f : Lp ℂ 2 (volume : Measure (FourierSpace m))}
    (hf : MemLp (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    (inverseHalf (f := f) hf : 𝓢'(FourierSpace m, ℂ)) = halfTimeDistribution f := by
  rw [halfTimeDistribution_eq_fourierInv, frequencyDistribution_eq_inverseFrequency (f := f) hf,
    Lp.fourierInv_toTemperedDistribution_eq]
  rfl

theorem integrable_inverseHalf_test {f : Lp ℂ 2 (volume : Measure (FourierSpace m))}
    (hf : MemLp (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume)
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    Integrable (fun x => inverseHalf (f := f) hf x * ψ x) volume :=
  (Lp.memLp _).integrable_mul (ψ.memLp 2 volume)

theorem inverseHalf_pairing {f : Lp ℂ 2 (volume : Measure (FourierSpace m))}
    (hf : MemLp (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume)
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    (∫ x, inverseHalf (f := f) hf x * ψ x) = halfTimeFunctional f ψ := by
  have h := congrArg (fun T : 𝓢'(FourierSpace m, ℂ) => T ψ) (inverseHalf_distribution hf)
  simpa only [Lp.toTemperedDistribution_apply, smul_eq_mul, mul_comm,
    halfTimeDistribution_apply] using h

/-- Real source data force the imaginary part of the inverse to vanish almost everywhere. -/
theorem inverseHalf_ae_im_eq_zero {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    ∀ᵐ x, (inverseHalf hA x).im = 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((Complex.imCLM.comp_memLp (inverseHalf hA)).locallyIntegrable (by norm_num))
  intro φ hφ hc
  have hi := integral_im (integrable_inverseHalf_test hA (realCompactTest φ hφ hc))
  change (∫ x, (inverseHalf hA x * realCompactTest φ hφ hc x).im) =
    (∫ x, inverseHalf hA x * realCompactTest φ hφ hc x).im at hi
  have hr := halfTimeFunctional_real_im_eq_zero hH (realCompactTest φ hφ hc)
    (fun x => by simp)
  rw [← inverseHalf_pairing hA] at hr
  rw [← hi] at hr
  simpa [Complex.mul_im, mul_comm] using hr

/-- A strongly measurable representative of the inverse complex L2 class. -/
def inverseRepresentative {f : Lp ℂ 2 (volume : Measure (FourierSpace m))}
    (hf : MemLp (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) : FourierSpace m → ℂ :=
  (Lp.aestronglyMeasurable (inverseHalf (f := f) hf)).mk (inverseHalf (f := f) hf)

theorem stronglyMeasurable_inverseRepresentative
    {f : Lp ℂ 2 (volume : Measure (FourierSpace m))}
    (hf : MemLp (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    StronglyMeasurable (inverseRepresentative (f := f) hf) :=
  AEStronglyMeasurable.stronglyMeasurable_mk _

theorem inverseRepresentative_ae {f : Lp ℂ 2 (volume : Measure (FourierSpace m))}
    (hf : MemLp (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    inverseRepresentative (f := f) hf =ᵐ[volume] inverseHalf (f := f) hf :=
  (AEStronglyMeasurable.ae_eq_mk _).symm

/-- The real representative, used after the imaginary-part theorem. -/
def realInverse {H : FourierSpace m → ℝ} {hH : MemLp H 2 volume}
    (hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    FourierSpace m → ℝ := fun x => (inverseRepresentative hA x).re

theorem measurable_realInverse {H : FourierSpace m → ℝ} {hH : MemLp H 2 volume}
    (hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    Measurable (realInverse hA) :=
  Complex.measurable_re.comp (stronglyMeasurable_inverseRepresentative hA).measurable

theorem realInverse_complexification {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    (fun x => (realInverse hA x : ℂ)) =ᵐ[volume] inverseRepresentative hA := by
  filter_upwards [inverseHalf_ae_im_eq_zero hH hA, inverseRepresentative_ae hA] with x hi hx
  apply Complex.ext
  · rfl
  · simpa [hx] using hi.symm

theorem memLp_realInverse {H : FourierSpace m → ℝ} {hH : MemLp H 2 volume}
    (hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    MemLp (realInverse hA) 2 volume :=
  (Complex.reCLM.comp_memLp' ((Lp.memLp (inverseHalf hA)).ae_eq
    (inverseRepresentative_ae hA).symm))

theorem realLp_realInverse {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    realLp (memLp_realInverse hA) = inverseHalf hA := by
  apply Lp.ext
  exact (coeFn_realLp _).trans
    ((realInverse_complexification hH hA).trans (inverseRepresentative_ae hA))

theorem norm_inverseHalf {f : Lp ℂ 2 (volume : Measure (FourierSpace m))}
    (hf : MemLp (fun z => (symbol z : ℂ) * (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    ‖inverseHalf (f := f) hf‖ = ‖inverseFrequency (f := f) hf‖ :=
  (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm.norm_map _

theorem norm_realInverse {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    ‖(memLp_realInverse hA).toLp (realInverse hA)‖ = ‖inverseHalf hA‖ := by
  rw [← norm_realLp, realLp_realInverse hH]

/-- The global complex-test identity consists of absolutely convergent integrals. -/
theorem realInverse_test_identity {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume)
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    Integrable (fun x => (H x : ℂ) * halfTimeDeriv m ψ x) volume ∧
    Integrable (fun x => (realInverse hA x : ℂ) * ψ x) volume ∧
    (∫ x, (H x : ℂ) * halfTimeDeriv m ψ x) = ∫ x, (realInverse hA x : ℂ) * ψ x := by
  refine ⟨integrable_real_halfTime hH ψ,
    (memLp_realInverse hA).ofReal.integrable_mul (ψ.memLp 2 volume), ?_⟩
  rw [← halfTimeFunctional_real_apply hH, ← inverseHalf_pairing hA]
  apply integral_congr_ae
  exact (((realInverse_complexification hH hA).trans
    (inverseRepresentative_ae hA)).symm.mul (Filter.EventuallyEq.refl _ _))

/-- Restriction of the global representative to any open set. -/
theorem repHalf_realInverse {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume)
    {Ω : Set (FourierSpace m)} (hΩ : IsOpen Ω) : RepHalf hH (realInverse hA) Ω := by
  refine ⟨hΩ, ((memLp_realInverse hA).locallyIntegrable (by norm_num)).locallyIntegrableOn Ω, ?_⟩
  intro φ hφ hc _
  exact (realInverse_test_identity hH hA (realCompactTest φ hφ hc)).2.2

/-- The endpoint for arbitrary real L2 data, with the weighted-L2 hypothesis retained. -/
theorem exists_real_inverse {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume) :
    ∃ (w₀ : FourierSpace m → ℂ) (g : FourierSpace m → ℝ) (hg : MemLp g 2 volume),
      StronglyMeasurable w₀ ∧ w₀ =ᵐ[volume] inverseHalf hA ∧ Measurable g ∧
      (fun x => (g x : ℂ)) =ᵐ[volume] w₀ ∧ realLp hg = inverseHalf hA ∧
      RepHalf hH g Set.univ ∧
      ‖hg.toLp g‖ = ‖inverseHalf hA‖ ∧ ‖inverseHalf hA‖ = ‖inverseFrequency hA‖ :=
  ⟨inverseRepresentative hA, realInverse hA, memLp_realInverse hA,
    stronglyMeasurable_inverseRepresentative hA, inverseRepresentative_ae hA,
    measurable_realInverse hA, realInverse_complexification hH hA, realLp_realInverse hH hA,
    repHalf_realInverse hH hA isOpen_univ, norm_realInverse hH hA, norm_inverseHalf hA⟩

/-- Changes of source and represented function on the relevant null sets preserve representation. -/
theorem repHalf_realInverse_congr {H H' : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (hH' : MemLp H' 2 volume)
    (hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume)
    (hsource : H =ᵐ[volume] H') {g : FourierSpace m → ℝ}
    {Ω : Set (FourierSpace m)} (hΩ : IsOpen Ω)
    (hg : realInverse hA =ᵐ[volume.restrict Ω] g) : RepHalf hH' g Ω :=
  (repHalf_congr hH hH' hsource hg).mp (repHalf_realInverse hH hA hΩ)

/-- Source a.e. equality transports the weighted membership and the actual inverse class. -/
theorem inverseHalf_source_congr {H H' : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (hH' : MemLp H' 2 volume)
    (hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume)
    (hsource : H =ᵐ[volume] H') :
    ∃ hA' : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH') : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume,
      inverseFrequency hA' = inverseFrequency hA ∧ inverseHalf hA' = inverseHalf hA ∧
      realInverse hA' =ᵐ[volume] realInverse hA := by
  have he := realLp_congr hH hH' hsource
  have hA' : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH') : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume := by
    rwa [← he]
  have hfreq : inverseFrequency hA' = inverseFrequency hA := by
    apply Lp.ext
    filter_upwards [coeFn_inverseFrequency hA', coeFn_inverseFrequency hA] with z hz hz'
    rw [hz, hz', he]
  have hinv : inverseHalf hA' = inverseHalf hA := congrArg (𝓕⁻ ·) hfreq
  refine ⟨hA', hfreq, hinv, ?_⟩
  have ha := (realInverse_complexification hH hA).trans (inverseRepresentative_ae hA)
  have ha' := (realInverse_complexification hH' hA').trans (inverseRepresentative_ae hA')
  filter_upwards [ha, ha'] with x hx hx'
  apply Complex.ofReal_injective
  rw [hx, hx', hinv]

/-- Schwartz input satisfies the weighted-L2 condition through Fourier compatibility. -/
theorem memLp_symbol_fourier_toLp (ψ : 𝓢(FourierSpace m, ℂ)) :
    MemLp (fun z => (symbol z : ℂ) * (𝓕 (ψ.toLp 2 volume) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume := by
  rw [SchwartzMap.toLp_fourier_eq]
  exact (memLp_symbol_mul (𝓕 ψ)).ae_eq
    ((Filter.EventuallyEq.refl _ _).mul ((𝓕 ψ).coeFn_toLp 2 volume).symm)

theorem inverseHalf_toLp (ψ : 𝓢(FourierSpace m, ℂ)) :
    inverseHalf (memLp_symbol_fourier_toLp ψ) = halfTimeDeriv m ψ := by
  have he : inverseFrequency (memLp_symbol_fourier_toLp ψ) = weightedLp (𝓕 ψ) := by
    apply Lp.ext
    filter_upwards [coeFn_inverseFrequency (memLp_symbol_fourier_toLp ψ),
      coeFn_weightedLp (𝓕 ψ), (𝓕 ψ).coeFn_toLp 2 volume] with z hz hz' hψ
    rw [hz, hz', SchwartzMap.toLp_fourier_eq, hψ]
  change (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm _ = _
  rw [he, halfTimeDeriv_apply]

/-- Actual real smooth compact input agrees with its complex Schwartz L2 class. -/
theorem realLp_realCompactTest (H : FourierSpace m → ℝ) (hH : MemLp H 2 volume)
    (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) :
    realLp hH = (realCompactTest H hs hc).toLp 2 volume := by
  apply Lp.ext
  exact (coeFn_realLp hH).trans ((realCompactTest H hs hc).coeFn_toLp 2 volume).symm

/-- The inverse construction agrees with the half-time derivative on real compact tests. -/
theorem realInverse_compactTest {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) :
    ∃ hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume,
      realLp (memLp_realInverse hA) = halfTimeDeriv m (realCompactTest H hs hc) := by
  have he := realLp_realCompactTest H hH hs hc
  have hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume := by
    rw [he]
    exact memLp_symbol_fourier_toLp _
  refine ⟨hA, (realLp_realInverse hH hA).trans ?_⟩
  have hi : inverseHalf hA = inverseHalf (memLp_symbol_fourier_toLp (realCompactTest H hs hc)) := by
    unfold inverseHalf
    congr 1
  exact hi.trans (inverseHalf_toLp _)

end ParabolicRectifiability.HalfTimeDerivative
