import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements

/-! # The high-pass convolution of a BMO function

Proof of `fhpbc_c1_convolution`, in implication form over `FhpbcBMOLogGrowthStatement` and the
kernel facts (`FhpbcKernelFactsStatement`).

Let `K = fhp_highPassKernel η` and `e = timeVector m`.

* **Checkpoint A** (`fhpbc1k_aestronglyMeasurable_shift`): `(x, s) ↦ g (x - s e)` is a.e.
  strongly measurable for `volume.prod volume`. The skew map `(s, x) ↦ (s, x - s e)` is measure
  preserving (`MeasurePreserving.skew_product` and translation invariance of `volume`), and
  `g ∘ snd` is a.e. strongly measurable.
* **Checkpoint B** (`fhpbc1k_logWeight_lt_top`): `∫⁻ |K s| C (1 + log (3 + |s|)) ds < ∞`. Since
  `1 + log (3 + |s|) ≤ 3 + |s|`, it suffices that `|K s| (3 + |s|)` is integrable, which follows
  from `K ∈ L¹` and the tail `|K s| ≤ T |s|^{-3}` for `|s| ≥ 1`:
  `|K s| (3 + |s|) ≤ 4 |K s| + 2 max(T,0) (1 + s²)⁻¹`.
* **Shift bound** (`fhpbc1k_shift_le`): for `j = ⌊-s⌋`,
  `[a - s, b - s] ⊆ [a + j, b + 1 + j]`, so `FhpbcBMOLogGrowthStatement` applied to the fixed
  interval `[a, b + 1]` gives
  `∫⁻_{A × [a,b]} |g (x - s e)| dx ≤ max(C,0) (1 + log (3 + |s|))`, using `|j| ≤ |s| + 1`.
* The four clauses: Tonelli (`lintegral_lintegral_swap`) for the local bound on a compact `S`
  inside `closedBall 0 R × [-R, R]`; a.e. finiteness on the exhaustion `closedBall 0 n`; local
  integrability through `AEStronglyMeasurable.integral_prod_right'`; constants through `∫ K = 0`
  at every point of absolute convergence.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- Proof-only shortcut, as in the construction of `testKernel`: the default
instance search for `ContinuousSMul ℝ (FourierSpace m)` on the `L²` product exceeds the heartbeat
budget. -/
local instance fhpbc1k_continuousSMul (m : ℕ) : ContinuousSMul ℝ (FourierSpace m) :=
  IsBoundedSMul.continuousSMul

/-! ## Measurability -/

/-- A function with finite parabolic BMO seminorm (which includes local integrability on
`Space m`) is a.e. strongly measurable in ordinary coordinates. -/
theorem fhpbc1k_aestronglyMeasurable {m : ℕ} {g : FourierSpace m → ℝ}
    (hg : ∃ B : ℝ, HasStandardParabolicBMOBound m (g ∘ (fourierToParabolic m).symm) B) :
    AEStronglyMeasurable g (volume : Measure (FourierSpace m)) := by
  obtain ⟨B, -, hloc, -⟩ := hg
  have h := hloc.aestronglyMeasurable.comp_measurePreserving
    (fourierToParabolic_measurePreserving m)
  convert h using 1
  funext x
  show g x = g ((fourierToParabolic m).symm (fourierToParabolic m x))
  rw [Homeomorph.symm_apply_apply]

/-- **Checkpoint A.** The time-shifted function `(x, s) ↦ g (x - s e)` is a.e. strongly
measurable on the product, via the measure-preserving skew map `(s, x) ↦ (s, x - s e)`. -/
theorem fhpbc1k_aestronglyMeasurable_shift {m : ℕ} {g : FourierSpace m → ℝ}
    (hg : AEStronglyMeasurable g (volume : Measure (FourierSpace m))) :
    AEStronglyMeasurable (fun p : FourierSpace m × ℝ => g (p.1 - p.2 • timeVector m))
      ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) := by
  have hP : MeasurePreserving (fun p : ℝ × FourierSpace m => (id p.1, p.2 - p.1 • timeVector m))
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m)))
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) := by
    refine MeasurePreserving.skew_product (MeasurePreserving.id volume)
      (g := fun s x => x - s • timeVector m) ?_ ?_
    · exact (continuous_snd.sub (continuous_fst.smul continuous_const)).measurable
    · exact Filter.Eventually.of_forall fun s =>
        (measurePreserving_sub_right (volume : Measure (FourierSpace m)) (s • timeVector m)).map_eq
  have h1 : AEStronglyMeasurable (fun p : ℝ × FourierSpace m => g p.2)
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) :=
    hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have h2 := h1.comp_measurePreserving hP
  exact h2.comp_measurePreserving
    (Measure.measurePreserving_swap (μ := (volume : Measure (FourierSpace m)))
      (ν := (volume : Measure ℝ)))

/-! ## Checkpoint B: the logarithmically weighted kernel integral -/

/-- The real inequality `1 + log (3 + a) ≤ 3 + a` and its positivity, for `0 ≤ a`. -/
theorem fhpbc1k_logWeight_bounds {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ 1 + Real.log (3 + a) ∧ 1 + Real.log (3 + a) ≤ 3 + a := by
  have hlog0 : 0 ≤ Real.log (3 + a) := Real.log_nonneg (by linarith)
  have hlog : Real.log (3 + a) ≤ 3 + a - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  exact ⟨by linarith, by linarith⟩

/-- First moment of the kernel: `|K s| (3 + |s|)` is integrable for an integrable `K` with the
tail `|K s| ≤ T |s|^{-3}` on `|s| ≥ 1`. -/
theorem fhpbc1k_integrable_moment {K : ℝ → ℝ} (hK : Integrable K) {T : ℝ}
    (hT : ∀ t : ℝ, 1 ≤ |t| → |K t| ≤ T * |t| ^ (-((3 : ℕ) : ℝ))) :
    Integrable (fun s => |K s| * (3 + |s|)) := by
  set T' := max T 0 with hT'
  have hT'0 : 0 ≤ T' := le_max_right _ _
  have hb : Integrable (fun s : ℝ => 4 * |K s| + 2 * T' * (1 + s ^ 2)⁻¹) :=
    (hK.abs.const_mul 4).add (integrable_inv_one_add_sq.const_mul (2 * T'))
  refine hb.mono' (hK.abs.aestronglyMeasurable.mul
    ((continuous_const.add continuous_abs).aestronglyMeasurable)) ?_
  refine Filter.Eventually.of_forall fun s => ?_
  have hKs0 : 0 ≤ |K s| := abs_nonneg _
  have hs0 : 0 ≤ |s| := abs_nonneg _
  have hq0 : 0 ≤ 2 * T' * (1 + s ^ 2)⁻¹ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmain : |s| * |K s| ≤ |K s| + 2 * T' * (1 + s ^ 2)⁻¹ := by
    rcases lt_or_ge |s| 1 with hs | hs
    · have : |s| * |K s| ≤ 1 * |K s| := mul_le_mul_of_nonneg_right hs.le hKs0
      linarith
    · have hpos : 0 < |s| := by linarith
      have hk : |K s| ≤ T' * (|s| ^ 3)⁻¹ := by
        have h := hT s hs
        rw [Real.rpow_neg hs0, Real.rpow_natCast] at h
        calc |K s| ≤ T * (|s| ^ 3)⁻¹ := h
          _ ≤ T' * (|s| ^ 3)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have h1 : |s| * |K s| ≤ T' / |s| ^ 2 := by
        calc |s| * |K s| ≤ |s| * (T' * (|s| ^ 3)⁻¹) := mul_le_mul_of_nonneg_left hk hs0
          _ = T' / |s| ^ 2 := by
            field_simp
      have h2 : T' / |s| ^ 2 ≤ 2 * T' * (1 + s ^ 2)⁻¹ := by
        rw [← sq_abs s, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
        have hsq : 1 ≤ |s| ^ 2 := by nlinarith
        nlinarith [mul_nonneg hT'0 (sub_nonneg.2 hsq)]
      linarith
  nlinarith [hmain]

/-- **Checkpoint B.** `∫⁻ |K s| C (1 + log (3 + |s|)) ds < ∞` for an integrable `K` with the tail
`|K s| ≤ T |s|^{-3}` on `|s| ≥ 1`, for every real `C`. -/
theorem fhpbc1k_logWeight_lt_top {K : ℝ → ℝ} (hK : Integrable K) {T : ℝ}
    (hT : ∀ t : ℝ, 1 ≤ |t| → |K t| ≤ T * |t| ^ (-((3 : ℕ) : ℝ))) (C : ℝ) :
    ∫⁻ s, ‖K s‖ₑ * ENNReal.ofReal (C * (1 + Real.log (3 + |s|))) < ⊤ := by
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hint := (fhpbc1k_integrable_moment hK hT).const_mul C'
  refine lt_of_le_of_lt (lintegral_mono fun s => ?_) hint.2
  obtain ⟨hw0, hw⟩ := fhpbc1k_logWeight_bounds (abs_nonneg s)
  rw [Real.enorm_eq_ofReal_abs (K s), ← ENNReal.ofReal_mul (abs_nonneg _),
    Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  refine le_trans ?_ (le_abs_self _)
  have hKs0 : 0 ≤ |K s| := abs_nonneg _
  calc |K s| * (C * (1 + Real.log (3 + |s|)))
      ≤ |K s| * (C' * (3 + |s|)) := by
        refine mul_le_mul_of_nonneg_left ?_ hKs0
        calc C * (1 + Real.log (3 + |s|)) ≤ C' * (1 + Real.log (3 + |s|)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hw0
          _ ≤ C' * (3 + |s|) := mul_le_mul_of_nonneg_left hw hC'0
    _ = C' * (|K s| * (3 + |s|)) := by ring

/-! ## The shift bound -/

/-- **The shift bound.** If `FhpbcBMOLogGrowthStatement` holds on the fixed interval `[a, b + 1]` with constant `C`, then
for every real shift `s`, `∫⁻_{A × [a,b]} |g (x - s e)| dx ≤ max(C,0) (1 + log (3 + |s|))`: with
`j = ⌊-s⌋`, the shifted cylinder lies in `A × [a + j, b + 1 + j]`, and `|j| ≤ |s| + 1`. -/
theorem fhpbc1k_shift_le {m : ℕ} {g : FourierSpace m → ℝ} {A : Set (Spatial m)} {a b C : ℝ}
    (hC : ∀ j : ℤ, ∫⁻ x in fhp_cylinder A (Set.Icc (a + j) (b + 1 + j)), ‖g x‖ₑ ≤
      ENNReal.ofReal (C * (1 + Real.log (2 + |(j : ℝ)|)))) (s : ℝ) :
    ∫⁻ x in fhp_cylinder A (Set.Icc a b), ‖g (x - s • timeVector m)‖ₑ ≤
      ENNReal.ofReal (max C 0 * (1 + Real.log (3 + |s|))) := by
  set j : ℤ := ⌊-s⌋ with hj
  have hj1 : (j : ℝ) ≤ -s := Int.floor_le _
  have hj2 : -s < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hsub : fhp_cylinder A (Set.Icc a b) ⊆
      (fun x : FourierSpace m => x - s • timeVector m) ⁻¹'
        fhp_cylinder A (Set.Icc (a + j) (b + 1 + j)) := by
    intro x hx
    obtain ⟨hxA, hxa, hxb⟩ := hx
    show (WithLp.ofLp (x - s • timeVector m)).1 ∈ A ∧
      (WithLp.ofLp (x - s • timeVector m)).2 ∈ Set.Icc (a + j) (b + 1 + j)
    rw [coordinates_sub_timeVector]
    exact ⟨hxA, by linarith, by linarith⟩
  have hjabs : |(j : ℝ)| ≤ |s| + 1 := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self s, neg_abs_le s]
  have hlog : Real.log (2 + |(j : ℝ)|) ≤ Real.log (3 + |s|) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (2 + |(j : ℝ)|) := Real.log_nonneg (by linarith [abs_nonneg (j : ℝ)])
  calc ∫⁻ x in fhp_cylinder A (Set.Icc a b), ‖g (x - s • timeVector m)‖ₑ
      ≤ ∫⁻ x in (fun x : FourierSpace m => x - s • timeVector m) ⁻¹'
          fhp_cylinder A (Set.Icc (a + j) (b + 1 + j)), ‖g (x - s • timeVector m)‖ₑ :=
        lintegral_mono_set hsub
    _ = ∫⁻ y in fhp_cylinder A (Set.Icc (a + j) (b + 1 + j)), ‖g y‖ₑ :=
        (measurePreserving_sub_right (volume : Measure (FourierSpace m))
          (s • timeVector m)).setLIntegral_comp_preimage_emb
          (measurableEmbedding_subRight _) (fun y => ‖g y‖ₑ) _
    _ ≤ ENNReal.ofReal (C * (1 + Real.log (2 + |(j : ℝ)|))) := hC j
    _ ≤ ENNReal.ofReal (max C 0 * (1 + Real.log (3 + |s|))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc C * (1 + Real.log (2 + |(j : ℝ)|))
            ≤ max C 0 * (1 + Real.log (2 + |(j : ℝ)|)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
          _ ≤ max C 0 * (1 + Real.log (3 + |s|)) :=
              mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)

/-! ## The statement -/

/-- **The high-pass convolution of a BMO function**: the type of `fhpbc_c1_convolution`, in
implication form over `FhpbcBMOLogGrowthStatement` and the kernel facts. -/
theorem fhpbc_c1_convolution_proof : FhpbcBMOLogGrowthStatement → FhpbcKernelFactsStatement →
    ∀ (m : ℕ) (g : FourierSpace m → ℝ),
      (∃ B : ℝ, HasStandardParabolicBMOBound m (g ∘ (fourierToParabolic m).symm) B) →
      ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
        (∀ S : Set (FourierSpace m), IsCompact S →
          ∫⁻ x in S, ∫⁻ s : ℝ, ‖fhp_highPassKernel η s‖ₑ * ‖g (x - s • timeVector m)‖ₑ < ⊤) ∧
        (∀ᵐ x ∂(volume : Measure (FourierSpace m)),
          Integrable (fun s : ℝ => fhp_highPassKernel η s * g (x - s • timeVector m))) ∧
        LocallyIntegrable (fhp_timeConvolution (fhp_highPassKernel η) g) ∧
        ∀ c : ℝ, fhp_timeConvolution (fhp_highPassKernel η) (fun x => g x + c) =ᵐ[volume]
          fhp_timeConvolution (fhp_highPassKernel η) g := by
  intro hc1g hkf m g hg η hη
  obtain ⟨-, hKi, hK0, -, -, htail, -⟩ := hkf η hη
  set K := fhp_highPassKernel η with hKdef
  obtain ⟨T, hT⟩ := htail 0 3
  simp only [iteratedDeriv_zero] at hT
  have hgm : AEStronglyMeasurable g (volume : Measure (FourierSpace m)) :=
    fhpbc1k_aestronglyMeasurable hg
  have hKF : AEStronglyMeasurable
      (fun p : FourierSpace m × ℝ => K p.2 * g (p.1 - p.2 • timeVector m))
      ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) :=
    (hKi.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd).mul (fhpbc1k_aestronglyMeasurable_shift hgm)
  have hmeas : AEMeasurable
      (fun p : FourierSpace m × ℝ => ‖K p.2‖ₑ * ‖g (p.1 - p.2 • timeVector m)‖ₑ)
      ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) := by
    simpa only [enorm_mul] using hKF.enorm
  have hac : ∀ S : Set (FourierSpace m),
      ((volume : Measure (FourierSpace m)).restrict S).prod (volume : Measure ℝ) ≪
        (volume : Measure (FourierSpace m)).prod (volume : Measure ℝ) := fun S =>
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod
      Measure.AbsolutelyContinuous.rfl
  -- clause 1: the absolute local bound
  have h1 : ∀ S : Set (FourierSpace m), IsCompact S →
      ∫⁻ x in S, ∫⁻ s : ℝ, ‖K s‖ₑ * ‖g (x - s • timeVector m)‖ₑ < ⊤ := by
    intro S hS
    obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall (0 : FourierSpace m)
    obtain ⟨C, hC⟩ := hc1g m g hg (Metric.closedBall (0 : Spatial m) R)
      Metric.isBounded_closedBall measurableSet_closedBall (-R) (R + 1)
    have hSsub : S ⊆ fhp_cylinder (Metric.closedBall (0 : Spatial m) R) (Set.Icc (-R) R) := by
      intro x hx
      have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx)
      have hfst := WithLp.norm_fst_le (p := 2) (α := Spatial m) (β := ℝ) x
      have hsnd := WithLp.norm_snd_le (p := 2) (α := Spatial m) (β := ℝ) x
      rw [Real.norm_eq_abs] at hsnd
      refine ⟨mem_closedBall_zero_iff.2 (hfst.trans hxR), ?_⟩
      exact abs_le.1 (hsnd.trans hxR)
    calc ∫⁻ x in S, ∫⁻ s : ℝ, ‖K s‖ₑ * ‖g (x - s • timeVector m)‖ₑ
        = ∫⁻ s : ℝ, ∫⁻ x in S, ‖K s‖ₑ * ‖g (x - s • timeVector m)‖ₑ :=
          lintegral_lintegral_swap (hmeas.mono_ac (hac S))
      _ = ∫⁻ s : ℝ, ‖K s‖ₑ * ∫⁻ x in S, ‖g (x - s • timeVector m)‖ₑ :=
          lintegral_congr fun s => lintegral_const_mul' _ _ enorm_ne_top
      _ ≤ ∫⁻ s : ℝ, ‖K s‖ₑ * ENNReal.ofReal (max C 0 * (1 + Real.log (3 + |s|))) :=
          lintegral_mono fun s => by
            gcongr
            exact (lintegral_mono_set hSsub).trans (fhpbc1k_shift_le hC s)
      _ < ⊤ := fhpbc1k_logWeight_lt_top hKi hT _
  -- clause 2: almost-everywhere absolute convergence
  have h2 : ∀ᵐ x ∂(volume : Measure (FourierSpace m)),
      Integrable (fun s : ℝ => K s * g (x - s • timeVector m)) := by
    have hn : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure (FourierSpace m)),
        x ∈ Metric.closedBall (0 : FourierSpace m) n →
          ∫⁻ s : ℝ, ‖K s‖ₑ * ‖g (x - s • timeVector m)‖ₑ < ⊤ := by
      intro n
      have hae : ∀ᵐ x ∂((volume : Measure (FourierSpace m)).restrict
          (Metric.closedBall (0 : FourierSpace m) n)),
          ∫⁻ s : ℝ, ‖K s‖ₑ * ‖g (x - s • timeVector m)‖ₑ < ⊤ :=
        ae_lt_top' (hmeas.mono_ac (hac _)).lintegral_prod_right'
          (h1 _ (isCompact_closedBall _ _)).ne
      exact (ae_restrict_iff' measurableSet_closedBall).1 hae
    have hfin : ∀ᵐ x ∂(volume : Measure (FourierSpace m)),
        ∫⁻ s : ℝ, ‖K s‖ₑ * ‖g (x - s • timeVector m)‖ₑ < ⊤ := by
      filter_upwards [ae_all_iff.2 hn] with x hx
      obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
      exact hx n (mem_closedBall_zero_iff.2 hn)
    filter_upwards [hfin, hKF.prodMk_left] with x hx hxm
    refine ⟨hxm, ?_⟩
    show ∫⁻ s : ℝ, ‖K s * g (x - s • timeVector m)‖ₑ < ⊤
    simpa only [enorm_mul] using hx
  refine ⟨h1, h2, ?_, ?_⟩
  -- clause 3: local integrability
  · rw [locallyIntegrable_iff]
    intro S hS
    refine ⟨hKF.integral_prod_right'.restrict, ?_⟩
    show ∫⁻ x in S, ‖fhp_timeConvolution K g x‖ₑ < ⊤
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (h1 S hS)
    have hx : fhp_timeConvolution K g x = ∫ s : ℝ, K s * g (x - s • timeVector m) := rfl
    rw [hx]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp only [enorm_mul]
  -- clause 4: invariance under adding constants
  · intro c
    filter_upwards [h2] with x hx
    show ∫ s : ℝ, K s * (g (x - s • timeVector m) + c) = ∫ s : ℝ, K s * g (x - s • timeVector m)
    simp_rw [mul_add]
    rw [integral_add hx (hKi.mul_const c), integral_mul_const, hK0, zero_mul, add_zero]

end ParabolicRectifiability.Foundations
