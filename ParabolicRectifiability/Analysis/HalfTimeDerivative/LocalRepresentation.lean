import ParabolicRectifiability.Analysis.HalfTimeDerivative.Distribution

/-! # Local representation on compact tests

Test admissibility consists only of smoothness, compact support, and support
inside the open set. In particular no L2 hypothesis is imposed on the local
representative. Uniqueness and gluing are not asserted here.
-/

noncomputable section

open MeasureTheory SchwartzMap FourierTransform
open scoped SchwartzMap ContDiff

namespace ParabolicRectifiability.HalfTimeDerivative

variable {m : ℕ}

/-- A complex smooth compact test, with its genuine Schwartz membership. -/
def compactTest (φ : FourierSpace m → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : 𝓢(FourierSpace m, ℂ) :=
  hc.toSchwartzMap hφ

@[simp] theorem compactTest_apply (φ : FourierSpace m → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (x : FourierSpace m) : compactTest φ hφ hc x = φ x := rfl

/-- Complexification of a real smooth compact test. -/
def realCompactTest (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : 𝓢(FourierSpace m, ℂ) :=
  compactTest (fun x => (φ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hφ)
    (hc.comp_left (g := Complex.ofReal) rfl)

@[simp] theorem realCompactTest_apply (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (x : FourierSpace m) :
    realCompactTest φ hφ hc x = (φ x : ℂ) := rfl

theorem tsupport_realCompactTest (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : tsupport (realCompactTest φ hφ hc) = tsupport φ :=
  tsupport_comp_eq (g := Complex.ofReal) (by simp) φ

/-- Localization to the compact support supplies actual absolute integrability. -/
theorem integrable_local_mul_test {g : FourierSpace m → ℝ} {Ω : Set (FourierSpace m)}
    (hg : LocallyIntegrableOn g Ω volume) {φ : FourierSpace m → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun x => (g x : ℂ) * φ x) volume := by
  let K := tsupport φ
  have hK : IsCompact K := hc
  have hgi : Integrable (K.indicator (fun x => (g x : ℂ))) volume := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact (hg.integrableOn_compact_subset hs hc).ofReal
  have hint := hgi.mul_of_top_right (hφ.memLp_top_of_hasCompactSupport hc volume)
  apply hint.congr
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · simp [Set.indicator_of_mem hx, mul_comm]
  · simp [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]

/-- Real compact-test representation of the half derivative on an open set. -/
def RepHalf {H : FourierSpace m → ℝ} (_hH : MemLp H 2 volume)
    (g : FourierSpace m → ℝ) (Ω : Set (FourierSpace m)) : Prop :=
  IsOpen Ω ∧ LocallyIntegrableOn g Ω volume ∧
    ∀ (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      tsupport φ ⊆ Ω →
        (∫ x, (H x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x) =
          ∫ x, (g x : ℂ) * (φ x : ℂ)

/-- Local representation of an actual tempered distribution on all complex compact tests. -/
def RepresentsLocally (T : 𝓢'(FourierSpace m, ℂ))
    (g : FourierSpace m → ℝ) (Ω : Set (FourierSpace m)) : Prop :=
  IsOpen Ω ∧ LocallyIntegrableOn g Ω volume ∧
    ∀ (φ : FourierSpace m → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      tsupport φ ⊆ Ω → T (compactTest φ hφ hc) = ∫ x, (g x : ℂ) * φ x

theorem repHalf_iff_real_distribution_tests {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (g : FourierSpace m → ℝ) (Ω : Set (FourierSpace m)) :
    RepHalf hH g Ω ↔ IsOpen Ω ∧ LocallyIntegrableOn g Ω volume ∧
      ∀ (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
        tsupport φ ⊆ Ω → halfTimeDistribution (realLp hH) (realCompactTest φ hφ hc) =
          ∫ x, (g x : ℂ) * (φ x : ℂ) := by
  simp only [RepHalf, halfTimeDistribution_apply, halfTimeFunctional_real_apply]

/-- Real and imaginary parts preserve the compact-test conditions. -/
theorem compactTest_split (φ : FourierSpace m → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    compactTest φ hφ hc =
      realCompactTest (fun x => (φ x).re) (Complex.reCLM.contDiff.comp hφ)
        (hc.comp_left (g := Complex.re) rfl) +
      Complex.I • realCompactTest (fun x => (φ x).im) (Complex.imCLM.contDiff.comp hφ)
        (hc.comp_left (g := Complex.im) rfl) := by
  ext x
  change φ x = ((φ x).re : ℂ) + Complex.I * ((φ x).im : ℂ)
  exact (Complex.re_add_im (φ x)).symm.trans (by ring)

set_option backward.isDefEq.respectTransparency false in
/-- Real tests determine precisely the same representation as their complex extensions. -/
theorem repHalf_iff_representsLocally {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (g : FourierSpace m → ℝ) (Ω : Set (FourierSpace m)) :
    RepHalf hH g Ω ↔ RepresentsLocally (halfTimeDistribution (realLp hH)) g Ω := by
  rw [repHalf_iff_real_distribution_tests]
  constructor
  · rintro ⟨hΩ, hg, hrep⟩
    refine ⟨hΩ, hg, ?_⟩
    intro φ hφ hc hs
    have hr := (tsupport_comp_subset (g := Complex.re) rfl φ).trans hs
    have hi := (tsupport_comp_subset (g := Complex.im) rfl φ).trans hs
    have hri := integrable_local_mul_test hg
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hφ.continuous))
      ((hc.comp_left (g := Complex.re) rfl).comp_left (g := Complex.ofReal) rfl)
      ((tsupport_comp_subset (g := Complex.ofReal) rfl _).trans hr)
    have hii := integrable_local_mul_test hg
      (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hφ.continuous))
      ((hc.comp_left (g := Complex.im) rfl).comp_left (g := Complex.ofReal) rfl)
      ((tsupport_comp_subset (g := Complex.ofReal) rfl _).trans hi)
    simp only [Function.comp_def] at hr hi hri hii
    rw [compactTest_split, map_add, map_smul, hrep _ _ _ hr, hrep _ _ _ hi]
    rw [smul_eq_mul, ← integral_const_mul, ← integral_add hri (hii.const_mul Complex.I)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    calc
      _ = (g x : ℂ) * ((φ x).re + (φ x).im * Complex.I) := by ring
      _ = _ := by rw [Complex.re_add_im]
  · rintro ⟨hΩ, hg, hrep⟩
    refine ⟨hΩ, hg, ?_⟩
    intro φ hφ hc hs
    exact hrep (fun x => (φ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hφ)
      (hc.comp_left (g := Complex.ofReal) rfl)
      ((tsupport_comp_subset (g := Complex.ofReal) rfl φ).trans hs)

theorem repHalf_test_integrable {H g : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    {Ω : Set (FourierSpace m)} (hrep : RepHalf hH g Ω)
    (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) :
    Integrable (fun x => (H x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x) volume ∧
      Integrable (fun x => (g x : ℂ) * (φ x : ℂ)) volume := by
  refine ⟨integrable_real_halfTime hH _, ?_⟩
  exact integrable_local_mul_test hrep.2.1
    (Complex.continuous_ofReal.comp hφ.continuous)
    (hc.comp_left (g := Complex.ofReal) rfl)
    ((tsupport_comp_subset (g := Complex.ofReal) rfl φ).trans hs)

/-- Restricted almost-everywhere equality suffices because the test vanishes outside Ω. -/
theorem integral_local_mul_congr {g g' : FourierSpace m → ℝ} {Ω : Set (FourierSpace m)}
    (hΩ : IsOpen Ω) (h : g =ᵐ[volume.restrict Ω] g')
    {φ : FourierSpace m → ℂ} (hs : tsupport φ ⊆ Ω) :
    (∫ x, (g x : ℂ) * φ x) = ∫ x, (g' x : ℂ) * φ x := by
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hΩ.measurableSet).mp h] with x hx
  by_cases hxo : x ∈ Ω
  · rw [hx hxo]
  · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hxt => hxo (hs hxt))
    simp only [hz, mul_zero]

theorem representsLocally_congr {T : 𝓢'(FourierSpace m, ℂ)}
    {g g' : FourierSpace m → ℝ} {Ω : Set (FourierSpace m)}
    (h : g =ᵐ[volume.restrict Ω] g') :
    RepresentsLocally T g Ω ↔ RepresentsLocally T g' Ω := by
  constructor
  · rintro ⟨hΩ, hg, hrep⟩
    refine ⟨hΩ, hg.congr h, ?_⟩
    intro φ hφ hc hs
    exact (hrep φ hφ hc hs).trans (integral_local_mul_congr hΩ h hs)
  · rintro ⟨hΩ, hg, hrep⟩
    refine ⟨hΩ, hg.congr h.symm, ?_⟩
    intro φ hφ hc hs
    exact (hrep φ hφ hc hs).trans (integral_local_mul_congr hΩ h.symm hs)

theorem repHalf_congr {H H' g g' : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (hH' : MemLp H' 2 volume) {Ω : Set (FourierSpace m)}
    (hh : H =ᵐ[volume] H') (hg : g =ᵐ[volume.restrict Ω] g') :
    RepHalf hH g Ω ↔ RepHalf hH' g' Ω := by
  rw [repHalf_iff_representsLocally, repHalf_iff_representsLocally, realLp_congr hH hH' hh]
  exact representsLocally_congr hg

theorem repHalf_zero {Ω : Set (FourierSpace m)} (hΩ : IsOpen Ω) :
    RepHalf (H := fun _ : FourierSpace m => (0 : ℝ)) MemLp.zero (fun _ => 0) Ω := by
  refine ⟨hΩ, locallyIntegrableOn_zero, ?_⟩
  intro φ hφ hc hs
  simp

end ParabolicRectifiability.HalfTimeDerivative

