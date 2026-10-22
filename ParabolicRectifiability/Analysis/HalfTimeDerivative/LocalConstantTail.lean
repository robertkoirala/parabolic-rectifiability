import ParabolicRectifiability.Analysis.HalfTimeDerivative.TestKernel
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! # Half-time tails away from a local constant

Ordinary product volume is used throughout. The tail is an actual integral,
not a pointwise assertion about the selected representative of an Lp class.
-/

noncomputable section

-- Function arithmetic in Mathlib uses reducible pointwise operations.
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Filter Set SchwartzMap FourierTransform
open scoped Topology SchwartzMap ContDiff ENNReal

namespace ParabolicRectifiability.HalfTimeDerivative
open FractionalKernel

local instance (m : ℕ) : ContinuousSMul ℝ (FourierSpace m) :=
  IsBoundedSMul.continuousSMul

/-- The two-sided power tail, including its harmless endpoints. -/
def separatedPower (δ a h : ℝ) : ℝ := if δ ≤ |h| then |h| ^ a else 0

theorem measurable_separatedPower (δ a : ℝ) : Measurable (separatedPower δ a) := by
  exact (measurable_abs.pow_const a).ite
    (measurableSet_le measurable_const measurable_abs) measurable_const

theorem separatedPower_nonneg (δ a h : ℝ) : 0 ≤ separatedPower δ a h := by
  unfold separatedPower
  split_ifs <;> positivity

private theorem integrable_even_of_positive {f : ℝ → ℝ} (he : ∀ h, f (-h) = f h)
    (hf : IntegrableOn f (Ioi 0) volume) : Integrable f volume := by
  have hn : IntegrableOn f (Iic 0) volume := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding (fun h : ℝ => -h) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simpa only [Function.comp_def, he, neg_preimage, neg_Iic, neg_zero] using
      (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf)
  simpa only [Iic_union_Ioi, integrableOn_univ] using hn.union hf

/-- Both tails are integrable precisely in the range used below. -/
theorem integrable_separatedPower {δ a : ℝ} (hδ : 0 < δ) (ha : a < -1) :
    Integrable (separatedPower δ a) volume := by
  apply integrable_even_of_positive (fun h => by simp [separatedPower])
  have hi : Integrable ((Ici δ).indicator (fun h : ℝ => h ^ a)) volume :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).2
      (integrableOn_Ioi_rpow_of_lt ha hδ)).integrable_indicator measurableSet_Ici
  apply hi.integrableOn.congr_fun (fun h hh => ?_) measurableSet_Ioi
  simp [separatedPower, abs_of_pos (show 0 < h from hh), Set.indicator, Set.mem_Ici]

/-- Exact two-sided tail integral, with no finite-volume hypothesis on time. -/
theorem integral_separatedPower {δ a : ℝ} (hδ : 0 < δ) (ha : a < -1) :
    (∫ h, separatedPower δ a h) = 2 * (-δ ^ (a + 1) / (a + 1)) := by
  change (∫ h : ℝ, (fun r : ℝ => if δ ≤ r then r ^ a else 0) |h|) = _
  rw [integral_comp_abs (f := fun r : ℝ => if δ ≤ r then r ^ a else 0)]
  congr 1
  change (∫ h in Ioi (0 : ℝ), (Ici δ).indicator (fun r : ℝ => r ^ a) h) = _
  rw [setIntegral_indicator measurableSet_Ici]
  have hs : Ioi (0 : ℝ) ∩ Ici δ = Ici δ := by
    ext h
    simp only [mem_inter_iff, mem_Ioi, mem_Ici]
    exact ⟨fun hh => hh.2, fun hh => ⟨hδ.trans_le hh, hh⟩⟩
  rw [hs, integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt ha hδ]

/-- The first tail has the constant four. -/
theorem integral_separatedPower_three_halves {δ : ℝ} (hδ : 0 < δ) :
    (∫ h, separatedPower δ (-3 / 2) h) = 4 * δ ^ (-1 / 2 : ℝ) := by
  rw [integral_separatedPower hδ (by norm_num : (-3 / 2 : ℝ) < -1)]
  norm_num
  ring

/-- The squared kernel has integral δ⁻², not a δ⁻³ tail. -/
theorem integral_separatedPower_three {δ : ℝ} (hδ : 0 < δ) :
    (∫ h, separatedPower δ (-3) h) = δ ^ (-2 : ℝ) := by
  rw [integral_separatedPower hδ (by norm_num : (-3 : ℝ) < -1)]
  norm_num
  ring

@[simp] theorem separatedPower_three_halves_sq (δ h : ℝ) :
    separatedPower δ (-3 / 2) h ^ 2 = separatedPower δ (-3) h := by
  unfold separatedPower
  split_ifs
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg h)]
    norm_num
  · simp

theorem memLp_separatedPower_three_halves {δ : ℝ} (hδ : 0 < δ) :
    MemLp (separatedPower δ (-3 / 2)) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    (measurable_separatedPower δ _).aestronglyMeasurable).2
  simpa only [separatedPower_three_halves_sq] using
    (integrable_separatedPower hδ (by norm_num : (-3 : ℝ) < -1))

/-- The actual L2 norm of a time slice, expressed without a choice of Lp representative. -/
def timeSliceNorm {m : ℕ} (H : FourierSpace m → ℝ) (u : Spatial m) : ℝ :=
  Real.sqrt (∫ t : ℝ, H (WithLp.toLp 2 (u, t)) ^ 2)

theorem timeSliceNorm_nonneg {m : ℕ} (H : FourierSpace m → ℝ) (u : Spatial m) :
    0 ≤ timeSliceNorm H u := Real.sqrt_nonneg _

theorem timeSliceNorm_sq {m : ℕ} (H : FourierSpace m → ℝ) (u : Spatial m) :
    timeSliceNorm H u ^ 2 = ∫ t : ℝ, H (WithLp.toLp 2 (u, t)) ^ 2 :=
  Real.sq_sqrt (integral_nonneg (fun _t => sq_nonneg _))

/-- Global L2 gives both actual slice measurability and slice L2 membership. -/
theorem memLp_timeSlice_ae {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) :
    ∀ᵐ u : Spatial m ∂volume, MemLp (fun t : ℝ => H (WithLp.toLp 2 (u, t))) 2 volume := by
  have hp : MemLp (fun p : Spatial m × ℝ => H (WithLp.toLp 2 p)) 2
      (volume.prod volume) := by
    rw [← volume_coordinates_eq_prod]
    exact (memLp_fourierCoordinates_symm_iff H 2).mpr hH
  filter_upwards [hp.aestronglyMeasurable.prodMk_left, hp.integrable_sq.prod_right_ae] with u hm hi
  exact (memLp_two_iff_integrable_sq hm).2 hi

/-- The slice norm itself belongs to L2 in space, including rank zero. -/
theorem memLp_timeSliceNorm {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) : MemLp (timeSliceNorm H) 2 volume := by
  have hp : Integrable (fun p : Spatial m × ℝ => H (WithLp.toLp 2 p) ^ 2)
      (volume.prod volume) := by
    rw [← volume_coordinates_eq_prod]
    exact (integrable_fourierCoordinates_symm_iff (fun x => H x ^ 2)).mpr hH.integrable_sq
  have hm : AEStronglyMeasurable (timeSliceNorm H) volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hp.integral_prod_left.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).2
  simpa only [timeSliceNorm_sq] using hp.integral_prod_left

/-- Fubini identifies the squared slice norms with the original L2 mass. -/
theorem integral_timeSliceNorm_sq {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) :
    (∫ u : Spatial m, timeSliceNorm H u ^ 2) = ∫ x, H x ^ 2 := by
  simp only [timeSliceNorm_sq]
  have hp : Integrable (fun p : Spatial m × ℝ => H (WithLp.toLp 2 p) ^ 2)
      (volume.prod volume) := by
    rw [← volume_coordinates_eq_prod]
    exact (integrable_fourierCoordinates_symm_iff (fun x => H x ^ 2)).mpr hH.integrable_sq
  rw [← integral_prod _ hp, ← volume_coordinates_eq_prod]
  exact integral_fourierCoordinates_symm (fun x => H x ^ 2)

/-- The required representative formula, with the normalization `kappa`. -/
def localConstantTail {m : ℕ} (H : FourierSpace m → ℝ) (c : ℝ) (I : Set ℝ)
    (u : Spatial m) (t : ℝ) : ℝ :=
  kappa * ∫ s in Iᶜ, (c - H (WithLp.toLp 2 (u, s))) * |t - s| ^ (-3 / 2 : ℝ)


/-- Translation and reflection preserve the time-tail integrals. -/
theorem integral_separatedPower_sub {δ a : ℝ} (hδ : 0 < δ) (ha : a < -1) (t : ℝ) :
    (∫ s, separatedPower δ a (t - s)) = 2 * (-δ ^ (a + 1) / (a + 1)) := by
  rw [integral_sub_left_eq_self, integral_separatedPower hδ ha]

theorem memLp_separatedPower_sub {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    MemLp (fun s => separatedPower δ (-3 / 2) (t - s)) 2 volume :=
  (memLp_separatedPower_three_halves hδ).comp_measurePreserving
    (volume.measurePreserving_sub_left t)

theorem integrable_separatedPower_sub {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    Integrable (fun s => separatedPower δ (-3 / 2) (t - s)) volume :=
  (integrable_comp_sub_left _ t).2 (integrable_separatedPower hδ (by norm_num))

/-- Cauchy--Schwarz uses the square-tail integral, hence the factor δ⁻¹. -/
theorem integral_abs_mul_separatedPower_le {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    (∫ s, |f s| * separatedPower δ (-3 / 2) (t - s)) ≤
      Real.sqrt (∫ s, f s ^ 2) * δ⁻¹ := by
  have hw := memLp_separatedPower_sub hδ t
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf) (by simpa using hw)
  simp only [Real.norm_eq_abs, abs_of_nonneg (separatedPower_nonneg _ _ _),
    Real.rpow_two, sq_abs, separatedPower_three_halves_sq] at h
  rw [integral_sub_left_eq_self, integral_separatedPower_three hδ,
    ← Real.sqrt_eq_rpow] at h
  have he : (δ ^ (-2 : ℝ)) ^ (1 / 2 : ℝ) = δ⁻¹ := by
    rw [← Real.rpow_mul hδ.le]
    norm_num [Real.rpow_neg_one]
  rwa [he] at h

/-- Absolute convergence for any L2 time fiber separated from the outside set. -/
theorem integrable_localConstantTail_fiber {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (c : ℝ) {I : Set ℝ} (hI : MeasurableSet I) {δ t : ℝ} (hδ : 0 < δ)
    (hsep : ∀ s ∉ I, δ ≤ |t - s|) :
    IntegrableOn (fun s => (c - f s) * |t - s| ^ (-3 / 2 : ℝ)) Iᶜ volume := by
  have hw := integrable_separatedPower_sub hδ t
  have hw2 := memLp_separatedPower_sub hδ t
  have hi := (hw.const_mul c).sub (hf.integrable_mul hw2)
  apply hi.integrableOn.congr_fun_ae
  filter_upwards [ae_restrict_mem hI.compl] with s hs
  change c * separatedPower δ (-3 / 2) (t - s) - f s * separatedPower δ (-3 / 2) (t - s) = _
  rw [separatedPower, ite_eq_left (hsep s hs)]
  ring

/-- A pointwise estimate for the actual fiber integral, before normalization. -/
theorem abs_integral_localConstantTail_fiber_le {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (c : ℝ) {I : Set ℝ} (hI : MeasurableSet I) {δ t : ℝ} (hδ : 0 < δ)
    (hsep : ∀ s ∉ I, δ ≤ |t - s|) :
    |∫ s in Iᶜ, (c - f s) * |t - s| ^ (-3 / 2 : ℝ)| ≤
      4 * |c| * δ ^ (-1 / 2 : ℝ) + δ⁻¹ * Real.sqrt (∫ s, f s ^ 2) := by
  let w := fun s => separatedPower δ (-3 / 2) (t - s)
  have hw : Integrable w volume := integrable_separatedPower_sub hδ t
  have hw2 : MemLp w 2 volume := memLp_separatedPower_sub hδ t
  have hb : Integrable (fun s => |c| * w s + |f s| * w s) volume :=
    (hw.const_mul |c|).add (hf.norm.integrable_mul hw2)
  rw [← integral_indicator hI.compl]
  calc
    _ ≤ ∫ s, ‖Iᶜ.indicator (fun s => (c - f s) * |t - s| ^ (-3 / 2 : ℝ)) s‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s, |c| * w s + |f s| * w s := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun s => norm_nonneg _) hb
      apply Eventually.of_forall
      intro s
      by_cases hs : s ∈ I
      · simp only [Set.indicator_of_notMem (show s ∉ Iᶜ from not_not.mpr hs), norm_zero]
        exact add_nonneg (mul_nonneg (abs_nonneg _) (separatedPower_nonneg _ _ _))
          (mul_nonneg (abs_nonneg _) (separatedPower_nonneg _ _ _))
      · simp only [Set.indicator_of_mem (show s ∈ Iᶜ from hs), Real.norm_eq_abs,
          abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        dsimp [w]
        rw [separatedPower, ite_eq_left (hsep s hs), ← add_mul]
        exact mul_le_mul_of_nonneg_right (abs_sub c (f s)) (by positivity)
    _ = |c| * (4 * δ ^ (-1 / 2 : ℝ)) +
        ∫ s, |f s| * separatedPower δ (-3 / 2) (t - s) := by
      have habs : Integrable (fun s => |f s| * w s) volume := by
        apply (hf.norm.integrable_mul hw2).congr
        exact Eventually.of_forall fun s => by
          change ‖f s‖ * w s = |f s| * w s
          rw [Real.norm_eq_abs]
      rw [integral_add (hw.const_mul _) habs, integral_const_mul]
      dsimp [w]
      rw [integral_sub_left_eq_self, integral_separatedPower_three_halves hδ]
    _ ≤ _ := by
      have h := integral_abs_mul_separatedPower_le hf hδ t
      nlinarith

/-- One exceptional spatial set works simultaneously for every separated time. -/
theorem localConstantTail_ae_bound {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (c : ℝ) {I J : Set ℝ} (hI : MeasurableSet I)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ t ∈ J, ∀ s ∉ I, δ ≤ |t - s|) :
    ∀ᵐ u : Spatial m ∂volume, ∀ t ∈ J,
      IntegrableOn (fun s => (c - H (WithLp.toLp 2 (u, s))) *
        |t - s| ^ (-3 / 2 : ℝ)) Iᶜ volume ∧
      |localConstantTail H c I u t| ≤
        kappa * (4 * |c| * δ ^ (-1 / 2 : ℝ) + δ⁻¹ * timeSliceNorm H u) := by
  filter_upwards [memLp_timeSlice_ae hH] with u hu
  intro t ht
  refine ⟨integrable_localConstantTail_fiber hu c hI hδ (hsep t ht), ?_⟩
  rw [localConstantTail, abs_mul, abs_of_pos kappa_pos]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_localConstantTail_fiber_le hu c hI hδ (hsep t ht)) kappa_pos.le

/-- A strongly measurable source has a strongly measurable actual tail integral. -/
theorem stronglyMeasurable_localConstantTail {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : StronglyMeasurable H) (c : ℝ) (I : Set ℝ) :
    StronglyMeasurable (fun p : Spatial m × ℝ => localConstantTail H c I p.1 p.2) := by
  have hm : StronglyMeasurable (fun q : (Spatial m × ℝ) × ℝ =>
      (c - H (WithLp.toLp 2 (q.1.1, q.2))) * |q.1.2 - q.2| ^ (-3 / 2 : ℝ)) := by
    apply StronglyMeasurable.mul
    · exact stronglyMeasurable_const.sub (hH.comp_measurable
        ((fourierCoordinatesMeasurableEquiv m).symm.measurable.comp
          (measurable_fst.fst.prodMk measurable_snd)))
    · exact (((measurable_fst.snd.sub measurable_snd).abs).pow_const _).stronglyMeasurable
  exact stronglyMeasurable_const.mul
    (hm.integral_prod_right' (ν := volume.restrict Iᶜ))

/-- Changing a source on a null set changes no tail at any time on almost every spatial fiber. -/
theorem localConstantTail_congr_ae_fibers {m : ℕ} {H H' : FourierSpace m → ℝ}
    (he : H =ᵐ[volume] H') (c : ℝ) (I : Set ℝ) :
    ∀ᵐ u : Spatial m ∂volume, ∀ t : ℝ,
      localConstantTail H c I u t = localConstantTail H' c I u t := by
  have hp : ∀ᵐ p : Spatial m × ℝ ∂(volume.prod volume),
      H (WithLp.toLp 2 p) = H' (WithLp.toLp 2 p) := by
    rw [← volume_coordinates_eq_prod]
    exact (ae_fourierCoordinates_symm_iff (fun x => H x = H' x)).mpr he
  filter_upwards [ae_ae_of_ae_prod hp] with u hu
  intro t
  unfold localConstantTail
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hu] with s hs
  rw [hs]

/-- A Borel representative, defined using a measurable version of the actual L2 source. -/
def measurableLocalConstantTail {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (c : ℝ) (I : Set ℝ) (u : Spatial m) (t : ℝ) : ℝ :=
  localConstantTail (hH.aestronglyMeasurable.mk H) c I u t

theorem measurable_measurableLocalConstantTail {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (c : ℝ) (I : Set ℝ) :
    Measurable (fun p : Spatial m × ℝ => measurableLocalConstantTail hH c I p.1 p.2) :=
  (stronglyMeasurable_localConstantTail hH.aestronglyMeasurable.stronglyMeasurable_mk c I).measurable

/-- The Borel version has the required genuine formula on one common set of good spatial fibers. -/
theorem measurableLocalConstantTail_eq_ae_fibers {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (c : ℝ) (I : Set ℝ) :
    ∀ᵐ u : Spatial m ∂volume, ∀ t : ℝ,
      measurableLocalConstantTail hH c I u t = localConstantTail H c I u t :=
  localConstantTail_congr_ae_fibers hH.aestronglyMeasurable.ae_eq_mk.symm c I

/-- The literal integral is a.e. measurable even for a merely a.e. measurable source. -/
theorem aestronglyMeasurable_localConstantTail {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (c : ℝ) (I : Set ℝ) :
    AEStronglyMeasurable (fun p : Spatial m × ℝ => localConstantTail H c I p.1 p.2)
      (volume.prod volume) := by
  apply (measurable_measurableLocalConstantTail hH c I).aestronglyMeasurable.congr
  have he := measurableLocalConstantTail_eq_ae_fibers hH c I
  filter_upwards [quasiMeasurePreserving_fst.ae he] with p hp
  exact hp p.2

/-- Compact containment supplies finite spatial and time volumes, without a rank guard. -/
theorem finite_volume_cylinder {m : ℕ} {V : Set (Spatial m)} {J : Set ℝ}
    (hV : IsCompact (closure V)) (hJ : IsCompact (closure J)) :
    volume V < ⊤ ∧ volume J < ⊤ ∧ (volume.prod volume) (V ×ˢ J) < ⊤ := by
  have hv : volume V < ⊤ := (measure_mono (subset_closure : V ⊆ closure V)).trans_lt hV.measure_lt_top
  have hj : volume J < ⊤ := (measure_mono (subset_closure : J ⊆ closure J)).trans_lt hJ.measure_lt_top
  exact ⟨hv, hj, by rw [Measure.prod_prod]; exact ENNReal.mul_lt_top hv hj⟩

/-- Local L2 follows from the derived slice norm and finite-volume facts. -/
theorem memLp_localConstantTail {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (c : ℝ) {I J : Set ℝ} (hI : MeasurableSet I)
    {V : Set (Spatial m)} (hV : IsCompact (closure V)) (hJ : IsCompact (closure J))
    (hJm : MeasurableSet J) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ t ∈ J, ∀ s ∉ I, δ ≤ |t - s|) :
    MemLp (fun p : Spatial m × ℝ => localConstantTail H c I p.1 p.2) 2
      ((volume.restrict V).prod (volume.restrict J)) := by
  obtain ⟨hv, hj, _⟩ := finite_volume_cylinder hV hJ
  let : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hv⟩
  let : IsFiniteMeasure (volume.restrict J) := ⟨by simpa using hj⟩
  have hn := ((memLp_timeSliceNorm hH).mono_measure (restrict_le_self (s := V))).comp_fst
    (volume.restrict J)
  have hb : MemLp (fun p : Spatial m × ℝ =>
      kappa * (4 * |c| * δ ^ (-1 / 2 : ℝ) + δ⁻¹ * timeSliceNorm H p.1)) 2
      ((volume.restrict V).prod (volume.restrict J)) :=
    ((memLp_const _).add (hn.const_mul _)).const_mul _
  apply hb.mono' ((aestronglyMeasurable_localConstantTail hH c I).mono_measure
    (Measure.prod_mono restrict_le_self restrict_le_self))
  have hu := ae_restrict_of_ae (s := V) (localConstantTail_ae_bound hH c hI hδ hsep)
  have ht : ∀ᵐ t ∂volume.restrict J, t ∈ J := ae_restrict_mem hJm
  filter_upwards [quasiMeasurePreserving_fst.ae hu, quasiMeasurePreserving_snd.ae ht] with p hp ht
  exact (hp p.2 ht).2

/-- The scalar slice formula equals the norm of its genuine L2 class. -/
theorem timeSliceNorm_eq_norm_toLp {m : ℕ} {H : FourierSpace m → ℝ} {u : Spatial m}
    (hu : MemLp (fun t : ℝ => H (WithLp.toLp 2 (u, t))) 2 volume) :
    timeSliceNorm H u = ‖hu.toLp (fun t : ℝ => H (WithLp.toLp 2 (u, t)))‖ := by
  apply (sq_eq_sq₀ (timeSliceNorm_nonneg H u) (norm_nonneg _)).mp
  rw [timeSliceNorm_sq, ← integral_sq_norm_eq_norm_toLp_sq hu]
  simp

/-- L2 convergence of the truncations gives the distributional pairing limit for arbitrary real L2 data. -/
theorem tendsto_integral_physicalTruncation {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (ψ : 𝓢(FourierSpace m, ℂ)) :
    Tendsto (fun j : ℕ => ∫ x, (H x : ℂ) * physicalTruncation j ψ x)
      atTop (𝓝 (halfTimeDistribution (realLp hH) ψ)) := by
  have he (j : ℕ) : (∫ x, (H x : ℂ) * physicalTruncation j ψ x) =
      l2Pairing m (realLp hH) (physicalTruncationLp j ψ) := by
    rw [l2Pairing_apply]
    apply integral_congr_ae
    filter_upwards [coeFn_realLp hH, coeFn_physicalTruncationLp j ψ] with x hx hy
    rw [hx, hy]
  simp_rw [he]
  exact ((l2Pairing m (realLp hH)).continuous.tendsto _).comp
    (tendsto_physicalTruncationLp ψ)

/-- Local equality also has a single spatial exceptional set; it is derived by Fubini. -/
theorem localConstant_timeSlice_ae {m : ℕ} {H : FourierSpace m → ℝ} {c : ℝ}
    {U : Set (Spatial m)} {I : Set ℝ} (_hU : MeasurableSet U) (_hI : MeasurableSet I)
    (hloc : ∀ᵐ x ∂volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (U ×ˢ I)),
      H x = c) :
    ∀ᵐ u ∂volume.restrict U, ∀ᵐ t ∂volume.restrict I,
      H (WithLp.toLp 2 (u, t)) = c := by
  have hp := (ae_fourierCoordinates_symm_restrict_iff (U ×ˢ I)
    (fun x => H x = c)).mpr hloc
  rw [volume_coordinates_eq_prod, ← Measure.prod_restrict U I] at hp
  exact ae_ae_of_ae_prod hp

/-- A compact test's support condition gives the time separation used in the tail limit. -/
theorem test_support_time_separation {m : ℕ} {φ : FourierSpace m → ℝ}
    {V : Set (Spatial m)} {J I : Set ℝ} {δ : ℝ}
    (hs : tsupport φ ⊆ (fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ J))
    (hsep : ∀ t ∈ J, ∀ s ∉ I, δ ≤ |t - s|) {u : Spatial m} {t : ℝ}
    (hφ : φ (WithLp.toLp 2 (u, t)) ≠ 0) :
    u ∈ V ∧ t ∈ J ∧ ∀ s ∉ I, δ ≤ |t - s| := by
  have hp := hs (subset_tsupport φ hφ)
  exact ⟨hp.1, hp.2, hsep t hp.2⟩


/-- Cauchy--Schwarz for an actual complex L2 function and a Schwartz test. -/
theorem integral_norm_L2_test_le {m : ℕ} {f : FourierSpace m → ℂ}
    (hf : MemLp f 2 volume) (ψ : 𝓢(FourierSpace m, ℂ)) :
    (∫ x, ‖f x‖ * ‖ψ x‖) ≤ ‖hf.toLp f‖ * ‖ψ.toLp 2 volume‖ := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf) (by simpa using ψ.memLp 2 volume)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at h
  rw [integral_sq_norm_eq_norm_toLp_sq hf,
    integral_sq_norm_eq_norm_toLp_sq (ψ.memLp 2 volume)] at h
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, SchwartzMap.toLp] using h

/-- The expanded truncated pairing is absolutely integrable for arbitrary L2 data.
The uniform translated-test bound is proved before Fubini is used. -/
theorem integrable_truncated_L2_test_pair {m : ℕ} {f : FourierSpace m → ℂ}
    (hf : MemLp f 2 volume) (j : ℕ) (u : ℝ → 𝓢(FourierSpace m, ℂ))
    (hu : StronglyMeasurable (fun p : ℝ × FourierSpace m => u p.1 p.2))
    (C : ℝ) (hC : ∀ h, ‖(u h).toLp 2 volume‖ ≤ C) :
    Integrable (fun p : ℝ × FourierSpace m =>
      (truncatedKernel j p.1 : ℂ) * (f p.2 * u p.1 p.2)) (volume.prod volume) := by
  have hfm : AEStronglyMeasurable (fun p : ℝ × FourierSpace m => f p.2)
      (volume.prod volume) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_snd
  have hm : AEStronglyMeasurable (fun p : ℝ × FourierSpace m =>
      (truncatedKernel j p.1 : ℂ) * (f p.2 * u p.1 p.2)) (volume.prod volume) :=
    (((Complex.continuous_ofReal.measurable.comp (measurable_truncatedKernel j)).comp measurable_fst).aestronglyMeasurable).mul
      (hfm.mul hu.aestronglyMeasurable)
  apply (integrable_prod_iff hm).2
  constructor
  · apply Eventually.of_forall
    intro h
    exact ((hf.integrable_mul ((u h).memLp 2 volume)).const_mul
      (truncatedKernel j h : ℂ)).congr (Eventually.of_forall fun x => rfl)
  apply ((integrable_truncatedKernel j).mul_const (‖hf.toLp f‖ * C)).mono'
    hm.norm.integral_prod_right'
  apply Eventually.of_forall
  intro h
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (truncatedKernel_nonneg j _), integral_const_mul]
  rw [abs_of_nonneg (integral_nonneg (fun x => mul_nonneg (norm_nonneg (f x)) (norm_nonneg (u h x))))]
  exact mul_le_mul_of_nonneg_left ((integral_norm_L2_test_le hf (u h)).trans
    (mul_le_mul_of_nonneg_left (hC h) (norm_nonneg _))) (truncatedKernel_nonneg j h)

/-- Both expanded terms have an actual Fubini justification before any truncation limit. -/
theorem integrable_truncated_pairing_terms {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    Integrable (fun p : ℝ × FourierSpace m =>
      (truncatedKernel j p.1 : ℂ) * ((H p.2 : ℂ) * ψ p.2)) (volume.prod volume) ∧
    Integrable (fun p : ℝ × FourierSpace m =>
      (truncatedKernel j p.1 : ℂ) * ((H p.2 : ℂ) *
        ψ (p.2 - p.1 • timeVector m))) (volume.prod volume) := by
  constructor
  · exact integrable_truncated_L2_test_pair hH.ofReal j (fun _ => ψ)
      (ψ.continuous.comp continuous_snd).stronglyMeasurable _ (fun _ => le_rfl)
  · apply integrable_truncated_L2_test_pair hH.ofReal j (fun h => timeTranslate h ψ)
      (ψ.continuous.comp (continuous_snd.sub (continuous_fst.smul continuous_const))).stronglyMeasurable
      ‖ψ.toLp 2 volume‖
    intro h
    exact (norm_timeTranslate_toLp h ψ).le

/-- Genuine truncated Fubini, in the negative time-shift convention. -/
theorem integral_physicalTruncation_fubini {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    (∫ x, (H x : ℂ) * physicalTruncation j ψ x) =
      (kappa : ℂ) * ∫ h, ∫ x, (truncatedKernel j h : ℂ) *
        ((H x : ℂ) * (ψ x - ψ (x - h • timeVector m))) := by
  obtain ⟨h₁, h₂⟩ := integrable_truncated_pairing_terms hH j ψ
  have hi : Integrable (fun p : ℝ × FourierSpace m =>
      (truncatedKernel j p.1 : ℂ) * ((H p.2 : ℂ) *
        (ψ p.2 - ψ (p.2 - p.1 • timeVector m)))) (volume.prod volume) := by
    convert h₁.sub h₂ using 1
    ext p
    simp only [Pi.sub_apply]
    ring
  calc
    _ = (kappa : ℂ) * ∫ x, ∫ h, (truncatedKernel j h : ℂ) *
        ((H x : ℂ) * (ψ x - ψ (x - h • timeVector m))) := by
      simp_rw [physicalTruncation, ← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      apply integral_congr_ae
      exact Eventually.of_forall fun h => by ring
    _ = _ := by
      congr 1
      exact (integral_integral_swap hi).symm

/-- The involution exchanging the two time arguments of a symmetric truncated pairing. -/
def timePairSwap (m : ℕ) : (ℝ × FourierSpace m) ≃ᵐ (ℝ × FourierSpace m) where
  toFun p := (-p.1, p.2 - p.1 • timeVector m)
  invFun p := (-p.1, p.2 - p.1 • timeVector m)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := measurable_fst.neg.prodMk
    (continuous_snd.sub (continuous_fst.smul continuous_const)).measurable
  measurable_invFun := measurable_fst.neg.prodMk
    (continuous_snd.sub (continuous_fst.smul continuous_const)).measurable

theorem measurePreserving_timePairSwap (m : ℕ) :
    MeasurePreserving (timePairSwap m) (volume.prod volume) (volume.prod volume) :=
  (measurePreserving_neg (volume : Measure ℝ)).skew_product
    (continuous_snd.sub (continuous_fst.smul continuous_const)).measurable
    (Eventually.of_forall fun h => (measurePreserving_sub_right volume (h • timeVector m)).map_eq)

/-- Symmetry is a measure-preserving substitution in an absolutely integrable double integral. -/
theorem truncated_pairing_symmetry {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    Integrable (fun p : ℝ × FourierSpace m => (truncatedKernel j p.1 : ℂ) *
      ((H (p.2 - p.1 • timeVector m) : ℂ) * ψ p.2)) (volume.prod volume) ∧
    (∫ p : ℝ × FourierSpace m, (truncatedKernel j p.1 : ℂ) *
      ((H p.2 : ℂ) * ψ (p.2 - p.1 • timeVector m)) ∂(volume.prod volume)) =
    ∫ p : ℝ × FourierSpace m, (truncatedKernel j p.1 : ℂ) *
      ((H (p.2 - p.1 • timeVector m) : ℂ) * ψ p.2) ∂(volume.prod volume) := by
  let f := fun p : ℝ × FourierSpace m => (truncatedKernel j p.1 : ℂ) *
    ((H p.2 : ℂ) * ψ (p.2 - p.1 • timeVector m))
  have hi : Integrable f (volume.prod volume) := (integrable_truncated_pairing_terms hH j ψ).2
  have he : (f ∘ timePairSwap m) = fun p : ℝ × FourierSpace m =>
      (truncatedKernel j p.1 : ℂ) * ((H (p.2 - p.1 • timeVector m) : ℂ) * ψ p.2) := by
    funext p
    simp [f, timePairSwap]
  constructor
  · rw [← he]
    exact ((measurePreserving_timePairSwap m).integrable_comp hi.aestronglyMeasurable).2 hi
  · rw [← he]
    exact ((measurePreserving_timePairSwap m).integral_comp' f).symm

/-- Truncated self-adjointness with an actual real L2 source, before localization. -/
theorem integral_physicalTruncation_selfAdjoint {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    (∫ x, (H x : ℂ) * physicalTruncation j ψ x) =
      (kappa : ℂ) * ∫ x, ∫ h, (truncatedKernel j h : ℂ) *
        (((H x : ℂ) - (H (x - h • timeVector m) : ℂ)) * ψ x) := by
  obtain ⟨h₁, h₂⟩ := integrable_truncated_pairing_terms hH j ψ
  obtain ⟨h₃, he⟩ := truncated_pairing_symmetry hH j ψ
  have hd : Integrable (fun p : ℝ × FourierSpace m =>
      (truncatedKernel j p.1 : ℂ) * ((H p.2 : ℂ) * ψ p.2) -
      (truncatedKernel j p.1 : ℂ) * ((H p.2 : ℂ) * ψ (p.2 - p.1 • timeVector m)))
      (volume.prod volume) := (h₁.sub h₂).congr (Eventually.of_forall fun p => rfl)
  have hd' : Integrable (fun p : ℝ × FourierSpace m =>
      (truncatedKernel j p.1 : ℂ) * ((H p.2 : ℂ) * ψ p.2) -
      (truncatedKernel j p.1 : ℂ) * ((H (p.2 - p.1 • timeVector m) : ℂ) * ψ p.2))
      (volume.prod volume) := (h₁.sub h₃).congr (Eventually.of_forall fun p => rfl)
  rw [integral_physicalTruncation_fubini hH j ψ]
  congr 1
  calc
    _ = ∫ p : ℝ × FourierSpace m,
        (truncatedKernel j p.1 : ℂ) * ((H p.2 : ℂ) * ψ p.2) -
        (truncatedKernel j p.1 : ℂ) * ((H p.2 : ℂ) * ψ (p.2 - p.1 • timeVector m))
        ∂(volume.prod volume) := by
      rw [integral_prod _ hd]
      congr 1
      funext h
      congr 1
      funext x
      ring
    _ = ∫ p : ℝ × FourierSpace m,
        (truncatedKernel j p.1 : ℂ) * ((H p.2 : ℂ) * ψ p.2) -
        (truncatedKernel j p.1 : ℂ) * ((H (p.2 - p.1 • timeVector m) : ℂ) * ψ p.2)
        ∂(volume.prod volume) := by
      rw [integral_sub h₁ h₂, he, ← integral_sub h₁ h₃]
    _ = _ := by
      rw [integral_prod_symm _ hd']
      congr 1
      funext x
      congr 1
      funext h
      ring


/-- The actual local tail with the same symmetric physical truncations. -/
def truncatedLocalConstantTail {m : ℕ} (H : FourierSpace m → ℝ) (c : ℝ)
    (I : Set ℝ) (j : ℕ) (u : Spatial m) (t : ℝ) : ℝ :=
  kappa * ∫ s in Iᶜ, (c - H (WithLp.toLp 2 (u, s))) * truncatedKernel j (t - s)

theorem truncatedKernel_le_power (j : ℕ) (h : ℝ) :
    truncatedKernel j h ≤ |h| ^ (-3 / 2 : ℝ) := by
  unfold truncatedKernel
  by_cases hh : h ∈ symmetricAnnulus j
  · simp [hh]
  · simp only [indicator_of_notMem hh]
    positivity

/-- The exact annuli eventually contain every nonzero shift. -/
theorem truncatedKernel_eventually_eq (h : ℝ) (hh : h ≠ 0) :
    ∀ᶠ j in atTop, truncatedKernel j h = |h| ^ (-3 / 2 : ℝ) := by
  have hm : h ∈ ⋃ j, symmetricAnnulus j := by simpa [iUnion_symmetricAnnulus] using hh
  obtain ⟨j, hj⟩ := mem_iUnion.mp hm
  filter_upwards [eventually_ge_atTop j] with n hn
  simp [truncatedKernel, monotone_symmetricAnnulus hn hj]

/-- The separated tail limit is justified absolutely on each good L2 fiber. -/
theorem tendsto_truncatedLocalConstantTail {m : ℕ} {H : FourierSpace m → ℝ}
    {u : Spatial m} (hu : MemLp (fun s : ℝ => H (WithLp.toLp 2 (u, s))) 2 volume)
    (c : ℝ) {I : Set ℝ} (hI : MeasurableSet I) {δ t : ℝ} (hδ : 0 < δ)
    (hsep : ∀ s ∉ I, δ ≤ |t - s|) :
    Tendsto (fun j => truncatedLocalConstantTail H c I j u t) atTop
      (𝓝 (localConstantTail H c I u t)) := by
  have hi := integrable_localConstantTail_fiber hu c hI hδ hsep
  have ht : Tendsto (fun j => ∫ s in Iᶜ,
      (c - H (WithLp.toLp 2 (u, s))) * truncatedKernel j (t - s)) atTop
      (𝓝 (∫ s in Iᶜ, (c - H (WithLp.toLp 2 (u, s))) * |t - s| ^ (-3 / 2 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun s => ‖(c - H (WithLp.toLp 2 (u, s))) * |t - s| ^ (-3 / 2 : ℝ)‖)
    · intro j
      exact (aestronglyMeasurable_const.sub hu.aestronglyMeasurable).mul
        (((measurable_truncatedKernel j).comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
        |>.restrict
    · exact hi.norm
    · intro j
      apply Eventually.of_forall
      intro s
      simp only [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (truncatedKernel_nonneg j _),
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact mul_le_mul_of_nonneg_left (truncatedKernel_le_power j _) (abs_nonneg _)
    · filter_upwards [ae_restrict_mem hI.compl] with s hs
      have hn : t - s ≠ 0 := by
        intro he
        have hp := hsep s hs
        rw [he, abs_zero] at hp
        exact hδ.not_ge hp
      exact tendsto_const_nhds.congr' ((truncatedKernel_eventually_eq (t - s) hn).mono
        fun j hj => by dsimp only; rw [hj])
  exact ht.const_mul kappa

/-- A finite physical truncation is in L2 as well as L1. -/
theorem memLp_truncatedKernel_two (j : ℕ) : MemLp (truncatedKernel j) 2 volume := by
  apply (memLp_separatedPower_three_halves (by positivity : 0 < 1 / ((j : ℝ) + 1))).mono'
    (measurable_truncatedKernel j).aestronglyMeasurable
  apply Eventually.of_forall
  intro h
  rw [Real.norm_eq_abs, abs_of_nonneg (truncatedKernel_nonneg j h)]
  by_cases hh : h ∈ symmetricAnnulus j
  · rw [truncatedKernel, indicator_of_mem hh, separatedPower, ite_eq_left hh.1.le]
  · rw [truncatedKernel, indicator_of_notMem hh]
    exact separatedPower_nonneg _ _ _

/-- Local constancy removes the entire interior time integral at every truncation. -/
theorem truncated_fiber_localization {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {c : ℝ} {I : Set ℝ} (hI : MeasurableSet I)
    (hloc : ∀ᵐ s ∂volume.restrict I, f s = c) (j : ℕ) (t : ℝ) :
    (∫ h, truncatedKernel j h * (c - f (t - h))) =
      ∫ s in Iᶜ, (c - f s) * truncatedKernel j (t - s) := by
  have hk : Integrable (fun s => truncatedKernel j (t - s)) volume :=
    (integrable_truncatedKernel j).comp_sub_left t
  have hk2 : MemLp (fun s => truncatedKernel j (t - s)) 2 volume :=
    (memLp_truncatedKernel_two j).comp_measurePreserving (volume.measurePreserving_sub_left t)
  have hi : Integrable (fun s => (c - f s) * truncatedKernel j (t - s)) volume := by
    convert (hk.const_mul c).sub (hf.integrable_mul hk2) using 1
    ext s
    change (c - f s) * truncatedKernel j (t - s) = c * truncatedKernel j (t - s) - f s * truncatedKernel j (t - s)
    ring
  have hz : (∫ s in I, (c - f s) * truncatedKernel j (t - s)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hloc] with s hs
    simp [hs]
  calc
    _ = ∫ s, (c - f s) * truncatedKernel j (t - s) := by
      rw [← integral_sub_left_eq_self (fun s => (c - f s) * truncatedKernel j (t - s)) volume t]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro h
      simp [mul_comm]
    _ = _ := by
      have he := integral_add_compl hI hi
      rw [hz, zero_add] at he
      exact he.symm

/-- The Borel representative has the same local L2 membership as the literal tail. -/
theorem memLp_measurableLocalConstantTail {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (c : ℝ) {I J : Set ℝ} (hI : MeasurableSet I)
    {V : Set (Spatial m)} (hV : IsCompact (closure V)) (hJ : IsCompact (closure J))
    (hJm : MeasurableSet J) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ t ∈ J, ∀ s ∉ I, δ ≤ |t - s|) :
    MemLp (fun p : Spatial m × ℝ => measurableLocalConstantTail hH c I p.1 p.2) 2
      ((volume.restrict V).prod (volume.restrict J)) := by
  apply (memLp_localConstantTail hH c hI hV hJ hJm hδ hsep).ae_eq
  have he := ae_restrict_of_ae (s := V) (measurableLocalConstantTail_eq_ae_fibers hH c I)
  filter_upwards [quasiMeasurePreserving_fst.ae he] with p hp
  exact (hp p.2).symm

/-- The literal tail in ordinary Fourier coordinates. -/
def localConstantTailFourier {m : ℕ} (H : FourierSpace m → ℝ) (c : ℝ) (I : Set ℝ)
    (x : FourierSpace m) : ℝ := localConstantTail H c I (WithLp.ofLp x).1 (WithLp.ofLp x).2

/-- The local L2 statement transported through the volume-preserving coordinate equivalence. -/
theorem memLp_localConstantTailFourier {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (c : ℝ) {I J : Set ℝ} (hI : MeasurableSet I)
    {V : Set (Spatial m)} (hV : IsCompact (closure V)) (hJ : IsCompact (closure J))
    (hJm : MeasurableSet J) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ t ∈ J, ∀ s ∉ I, δ ≤ |t - s|) :
    MemLp (localConstantTailFourier H c I) 2
      (volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ J))) := by
  have hg := memLp_localConstantTail hH c hI hV hJ hJm hδ hsep
  rw [Measure.prod_restrict, ← volume_coordinates_eq_prod] at hg
  exact (memLp_fourierCoordinates_restrict_iff (V ×ˢ J) _ 2).mpr hg


/-- Measurability of each truncated tail for a strongly measurable source. -/
theorem stronglyMeasurable_truncatedLocalConstantTail {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : StronglyMeasurable H) (c : ℝ) (I : Set ℝ) (j : ℕ) :
    StronglyMeasurable (fun p : Spatial m × ℝ => truncatedLocalConstantTail H c I j p.1 p.2) := by
  have hm : StronglyMeasurable (fun q : (Spatial m × ℝ) × ℝ =>
      (c - H (WithLp.toLp 2 (q.1.1, q.2))) * truncatedKernel j (q.1.2 - q.2)) := by
    apply StronglyMeasurable.mul
    · exact stronglyMeasurable_const.sub (hH.comp_measurable
        ((fourierCoordinatesMeasurableEquiv m).symm.measurable.comp
          (measurable_fst.fst.prodMk measurable_snd)))
    · exact ((measurable_truncatedKernel j).comp (measurable_fst.snd.sub measurable_snd)).stronglyMeasurable
  exact stronglyMeasurable_const.mul (hm.integral_prod_right' (ν := volume.restrict Iᶜ))

/-- A positive tail dominates all truncations; it will be paired with the compact test. -/
theorem abs_truncatedLocalConstantTail_le {m : ℕ} {H : FourierSpace m → ℝ}
    {u : Spatial m} (hu : MemLp (fun s : ℝ => H (WithLp.toLp 2 (u, s))) 2 volume)
    (c : ℝ) {I : Set ℝ} (hI : MeasurableSet I) {δ t : ℝ} (hδ : 0 < δ)
    (hsep : ∀ s ∉ I, δ ≤ |t - s|) (j : ℕ) :
    |truncatedLocalConstantTail H c I j u t| ≤
      localConstantTail (fun x => -|H x|) |c| I u t := by
  have hplus : MemLp (fun s : ℝ => -|H (WithLp.toLp 2 (u, s))|) 2 volume := by
    apply hu.norm.neg.ae_eq
    exact Eventually.of_forall fun s => by change -‖H (WithLp.toLp 2 (u, s))‖ = _; rw [Real.norm_eq_abs]
  have hi := integrable_localConstantTail_fiber hplus |c| hI hδ hsep
  rw [truncatedLocalConstantTail, localConstantTail, abs_mul, abs_of_pos kappa_pos]
  apply mul_le_mul_of_nonneg_left _ kappa_pos.le
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Eventually.of_forall fun s => norm_nonneg _) hi
  apply Eventually.of_forall
  intro s
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (truncatedKernel_nonneg j _), sub_neg_eq_add]
  exact (mul_le_mul_of_nonneg_right (abs_sub _ _) (truncatedKernel_nonneg j _)).trans
    (mul_le_mul_of_nonneg_left (truncatedKernel_le_power j _) (by positivity))

/-- The tail limit is integrable after multiplication by a compact smooth test. -/
theorem tendsto_truncatedLocalConstantTail_pairing {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (hHm : StronglyMeasurable H) (c : ℝ)
    {I J : Set ℝ} (hI : MeasurableSet I) {V : Set (Spatial m)}
    (hV : IsCompact (closure V)) (hJ : IsCompact (closure J)) (hJm : MeasurableSet J)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ t ∈ J, ∀ s ∉ I, δ ≤ |t - s|)
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    Tendsto (fun j => ∫ p : Spatial m × ℝ,
      (truncatedLocalConstantTail H c I j p.1 p.2 : ℂ) * ψ (WithLp.toLp 2 p)
      ∂((volume.restrict V).prod (volume.restrict J))) atTop
      (𝓝 (∫ p : Spatial m × ℝ,
        (localConstantTail H c I p.1 p.2 : ℂ) * ψ (WithLp.toLp 2 p)
        ∂((volume.restrict V).prod (volume.restrict J)))) := by
  let μ := (volume.restrict V).prod (volume.restrict J)
  have hplus : MemLp (fun x => -|H x|) 2 volume := by
    apply hH.norm.neg.ae_eq
    exact Eventually.of_forall fun x => by change -‖H x‖ = _; rw [Real.norm_eq_abs]
  have hg := memLp_localConstantTail hplus |c| hI hV hJ hJm hδ hsep
  have hp : MemLp (fun p : Spatial m × ℝ => ψ (WithLp.toLp 2 p)) 2 μ := by
    apply MemLp.mono_measure (Measure.prod_mono restrict_le_self restrict_le_self)
    rw [← volume_coordinates_eq_prod]
    exact (memLp_fourierCoordinates_symm_iff ψ 2).mpr (ψ.memLp 2 volume)
  have hbound : Integrable (fun p : Spatial m × ℝ =>
      localConstantTail (fun x => -|H x|) |c| I p.1 p.2 * ‖ψ (WithLp.toLp 2 p)‖) μ :=
    hg.integrable_mul hp.norm
  have hu := ae_restrict_of_ae (s := V) (memLp_timeSlice_ae hH)
  have ht : ∀ᵐ t ∂volume.restrict J, t ∈ J := ae_restrict_mem hJm
  refine tendsto_integral_of_dominated_convergence _ ?_ hbound ?_ ?_
  · intro j
    exact ((Complex.continuous_ofReal.comp_stronglyMeasurable (stronglyMeasurable_truncatedLocalConstantTail hHm c I j)).mul
      (ψ.continuous.stronglyMeasurable.comp_measurable
        (fourierCoordinatesMeasurableEquiv m).symm.measurable)).aestronglyMeasurable
  · intro j
    filter_upwards [quasiMeasurePreserving_fst.ae hu, quasiMeasurePreserving_snd.ae ht] with p hpu hpt
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (abs_truncatedLocalConstantTail_le hpu c hI hδ (hsep _ hpt) j) (norm_nonneg _)
  · filter_upwards [quasiMeasurePreserving_fst.ae hu, quasiMeasurePreserving_snd.ae ht] with p hpu hpt
    exact (Complex.continuous_ofReal.tendsto _ |>.comp
      (tendsto_truncatedLocalConstantTail hpu c hI hδ (hsep _ hpt))).mul_const _

/-- Positive separation forces the interior time set to lie in the constant interval. -/
theorem subset_of_time_separation {I J : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ t ∈ J, ∀ s ∉ I, δ ≤ |t - s|) : J ⊆ I := by
  intro t ht
  by_contra hn
  have hh := hsep t ht t hn
  have hh' : δ ≤ 0 := by simpa using hh
  exact hδ.not_ge hh'

/-- At each finite truncation, local constancy converts the pairing into the actual tail. -/
theorem integral_physicalTruncation_localized {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) {c : ℝ} {I J : Set ℝ} {V : Set (Spatial m)}
    (hV : MeasurableSet V) (hI : MeasurableSet I) (_hJ : MeasurableSet J) (hJI : J ⊆ I)
    (hloc : ∀ᵐ x ∂volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ I)), H x = c)
    (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ))
    (hs : tsupport ψ ⊆ (fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ J)) :
    (∫ x, (H x : ℂ) * physicalTruncation j ψ x) =
      ∫ p : Spatial m × ℝ, (truncatedLocalConstantTail H c I j p.1 p.2 : ℂ) *
        ψ (WithLp.toLp 2 p) ∂((volume.restrict V).prod (volume.restrict J)) := by
  let F := fun x : FourierSpace m => ∫ h, (truncatedKernel j h : ℂ) *
    (((H x : ℂ) - (H (x - h • timeVector m) : ℂ)) * ψ x)
  have hzero : ∀ x, x ∉ (fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ J) → F x = 0 := by
    intro x hx
    have hψ : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
    simp [F, hψ]
  have hpoint : ∀ᵐ p : Spatial m × ℝ ∂((volume.restrict V).prod (volume.restrict J)),
      H (WithLp.toLp 2 p) = c := by
    have hloc' := ae_restrict_of_ae_restrict_of_subset
      (show (fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ J) ⊆
        (fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ I) from
        fun x hx => ⟨hx.1, hJI hx.2⟩) hloc
    have hp := (ae_fourierCoordinates_symm_restrict_iff (V ×ˢ J) (fun x => H x = c)).mpr hloc'
    rw [volume_coordinates_eq_prod, ← Measure.prod_restrict] at hp
    filter_upwards [hp] with p hp
    exact hp
  have hslice := localConstant_timeSlice_ae hV hI hloc
  have hslice2 := ae_restrict_of_ae (s := V) (memLp_timeSlice_ae hH)
  rw [integral_physicalTruncation_selfAdjoint hH j ψ]
  change (kappa : ℂ) * (∫ x, F x) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← integral_fourierCoordinates_symm_restrict (V ×ˢ J) F,
    volume_coordinates_eq_prod, ← Measure.prod_restrict, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hpoint, quasiMeasurePreserving_fst.ae hslice,
    quasiMeasurePreserving_fst.ae hslice2] with p hp hc hf
  rcases p with ⟨u, t⟩
  dsimp [F]
  simp_rw [timeShift_toLp, hp]
  have he : (fun h : ℝ => (truncatedKernel j h : ℂ) *
      (((c : ℂ) - (H (WithLp.toLp 2 (u, t - h)) : ℂ)) * ψ (WithLp.toLp 2 (u, t)))) =
      fun h : ℝ => ((truncatedKernel j h * (c - H (WithLp.toLp 2 (u, t - h))) : ℝ) : ℂ) *
        ψ (WithLp.toLp 2 (u, t)) := by
    funext h
    push_cast
    ring
  rw [he, integral_mul_const, integral_complex_ofReal,
    truncated_fiber_localization hf hI hc j t]
  simp [truncatedLocalConstantTail, Complex.ofReal_mul, mul_assoc]


/-- Distributional equality, first for a strongly measurable actual source. -/
theorem localConstantTail_pairing_of_stronglyMeasurable {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (hHm : StronglyMeasurable H) {c : ℝ}
    {I J : Set ℝ} {V : Set (Spatial m)} (hVm : MeasurableSet V) (hI : MeasurableSet I)
    (hJm : MeasurableSet J) (hV : IsCompact (closure V)) (hJ : IsCompact (closure J))
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ t ∈ J, ∀ s ∉ I, δ ≤ |t - s|)
    (hloc : ∀ᵐ x ∂volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ I)), H x = c)
    (ψ : 𝓢(FourierSpace m, ℂ))
    (hs : tsupport ψ ⊆ (fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ J)) :
    halfTimeDistribution (realLp hH) ψ = ∫ x, (localConstantTailFourier H c I x : ℂ) * ψ x := by
  have ht := tendsto_truncatedLocalConstantTail_pairing hH hHm c hI hV hJ hJm hδ hsep ψ
  have hp := tendsto_integral_physicalTruncation hH ψ
  have he := integral_physicalTruncation_localized hH hVm hI hJm
    (subset_of_time_separation hδ hsep) hloc
  have hp' : Tendsto (fun j => ∫ p : Spatial m × ℝ,
      (truncatedLocalConstantTail H c I j p.1 p.2 : ℂ) * ψ (WithLp.toLp 2 p)
      ∂((volume.restrict V).prod (volume.restrict J))) atTop
      (𝓝 (halfTimeDistribution (realLp hH) ψ)) := by
    have hj (j : ℕ) := he j ψ hs
    simpa only [hj] using hp
  have hlim := tendsto_nhds_unique hp' ht
  rw [hlim, Measure.prod_restrict, ← volume_coordinates_eq_prod]
  have heq := integral_fourierCoordinates_symm_restrict (V ×ˢ J)
    (fun x => (localConstantTailFourier H c I x : ℂ) * ψ x)
  simp only [fourierCoordinatesMeasurableEquiv_symm_apply, localConstantTailFourier,
    WithLp.ofLp_toLp] at heq
  change (∫ p : Coordinates m in V ×ˢ J,
    (localConstantTail H c I p.1 p.2 : ℂ) * ψ (WithLp.toLp 2 p)) = _
  rw [heq]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]

/-- The Borel representative in Fourier coordinates. -/
def measurableLocalConstantTailFourier {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (c : ℝ) (I : Set ℝ) (x : FourierSpace m) : ℝ :=
  measurableLocalConstantTail hH c I (WithLp.ofLp x).1 (WithLp.ofLp x).2

theorem measurable_measurableLocalConstantTailFourier {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (c : ℝ) (I : Set ℝ) :
    Measurable (measurableLocalConstantTailFourier hH c I) :=
  (measurable_measurableLocalConstantTail hH c I).comp (fourierCoordinatesMeasurableEquiv m).measurable

/-- The representative equals the local tail and represents the half-time distribution.
No global L2 derivative or spatial regularity is assumed. -/
theorem measurableLocalConstantTail_pairing {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) {c : ℝ} {I J : Set ℝ} {V : Set (Spatial m)}
    (hVm : MeasurableSet V) (hI : MeasurableSet I) (hJm : MeasurableSet J)
    (hV : IsCompact (closure V)) (hJ : IsCompact (closure J))
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ t ∈ J, ∀ s ∉ I, δ ≤ |t - s|)
    (hloc : ∀ᵐ x ∂volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ I)), H x = c)
    (ψ : 𝓢(FourierSpace m, ℂ))
    (hs : tsupport ψ ⊆ (fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ J)) :
    halfTimeDistribution (realLp hH) ψ =
      ∫ x, (measurableLocalConstantTailFourier hH c I x : ℂ) * ψ x := by
  let H' := hH.aestronglyMeasurable.mk H
  have he : H =ᵐ[volume] H' := hH.aestronglyMeasurable.ae_eq_mk
  have hH' : MemLp H' 2 volume := hH.ae_eq he
  have hloc' : ∀ᵐ x ∂volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ I)),
      H' x = c := by
    filter_upwards [hloc, ae_restrict_of_ae he] with x hx heq
    exact heq.symm.trans hx
  rw [realLp_congr hH hH' he]
  exact localConstantTail_pairing_of_stronglyMeasurable hH'
    hH.aestronglyMeasurable.stronglyMeasurable_mk hVm hI hJm hV hJ hδ hsep hloc' ψ hs

/-- Local L2 for the Borel representative, in Fourier coordinates. -/
theorem memLp_measurableLocalConstantTailFourier {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (c : ℝ) {I J : Set ℝ} (hI : MeasurableSet I)
    {V : Set (Spatial m)} (hV : IsCompact (closure V)) (hJ : IsCompact (closure J))
    (hJm : MeasurableSet J) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ t ∈ J, ∀ s ∉ I, δ ≤ |t - s|) :
    MemLp (measurableLocalConstantTailFourier hH c I) 2
      (volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ J))) := by
  have hg := memLp_measurableLocalConstantTail hH c hI hV hJ hJm hδ hsep
  rw [Measure.prod_restrict, ← volume_coordinates_eq_prod] at hg
  exact (memLp_fourierCoordinates_restrict_iff (V ×ˢ J) _ 2).mpr hg

/-- Representation on all real and complex compact smooth tests on the open interior cylinder. -/
theorem repHalf_measurableLocalConstantTail {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) {c : ℝ} {I J : Set ℝ} {V : Set (Spatial m)}
    (hVo : IsOpen V) (hI : MeasurableSet I) (hJo : IsOpen J)
    (hV : IsCompact (closure V)) (hJ : IsCompact (closure J))
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ t ∈ J, ∀ s ∉ I, δ ≤ |t - s|)
    (hloc : ∀ᵐ x ∂volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ I)), H x = c) :
    RepHalf hH (measurableLocalConstantTailFourier hH c I)
      ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ J)) := by
  apply (repHalf_iff_real_distribution_tests hH _ _).2
  have hg := memLp_measurableLocalConstantTailFourier hH c hI hV hJ hJo.measurableSet hδ hsep
  have hfinite : volume ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ J)) < ⊤ := by
    rw [(fourierCoordinates_measurePreserving m).measure_preimage
      (hVo.measurableSet.prod hJo.measurableSet).nullMeasurableSet, volume_coordinates_eq_prod]
    exact (finite_volume_cylinder hV hJ).2.2
  let : IsFiniteMeasure (volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ J))) :=
    ⟨by simpa using hfinite⟩
  refine ⟨(hVo.prod hJo).preimage (fourierCoordinatesHomeomorph m).continuous,
    (IntegrableOn.locallyIntegrableOn (hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))), ?_⟩
  intro φ hφ hc hs
  apply measurableLocalConstantTail_pairing hH hVo.measurableSet hI hJo.measurableSet hV hJ hδ hsep hloc
    (realCompactTest φ hφ hc)
  simpa only [tsupport_realCompactTest] using hs

/-- The local-constant tail theorem in every spatial rank, including zero.
The genuine integral, its single spatial exceptional set, local L2 membership,
and the compact-test distributional representation are all retained. -/
theorem exists_localConstantTail {m : ℕ} {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (c : ℝ) {U V : Set (Spatial m)}
    (_hU : IsOpen U) (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVU : closure V ⊆ U)
    {a b : ℝ} (_hab : a < b) {J : Set ℝ} (hJ : IsOpen J)
    (hJc : IsCompact (closure J)) (_hJI : closure J ⊆ Ioo a b)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ t ∈ J, ∀ s ∉ Ioo a b, δ ≤ |t - s|)
    (hloc : ∀ᵐ x ∂volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (U ×ˢ Ioo a b)), H x = c) :
    ∃ g : FourierSpace m → ℝ, Measurable g ∧
      MemLp g 2 (volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ J))) ∧
      RepHalf hH g ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ J)) ∧
      ∀ᵐ u : Spatial m ∂volume, ∀ t ∈ J,
        IntegrableOn (fun s => (c - H (WithLp.toLp 2 (u, s))) *
          |t - s| ^ (-3 / 2 : ℝ)) (Ioo a b)ᶜ volume ∧
        g (WithLp.toLp 2 (u, t)) = kappa *
          ∫ s in (Ioo a b)ᶜ, (c - H (WithLp.toLp 2 (u, s))) * |t - s| ^ (-3 / 2 : ℝ) ∧
        |g (WithLp.toLp 2 (u, t))| ≤
          kappa * (4 * |c| * δ ^ (-1 / 2 : ℝ) + δ⁻¹ * timeSliceNorm H u) := by
  have hlocV : ∀ᵐ x ∂volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ Ioo a b)),
      H x = c := by
    apply ae_restrict_of_ae_restrict_of_subset _ hloc
    intro x hx
    exact ⟨hVU (subset_closure hx.1), hx.2⟩
  refine ⟨measurableLocalConstantTailFourier hH c (Ioo a b),
    measurable_measurableLocalConstantTailFourier hH c _,
    memLp_measurableLocalConstantTailFourier hH c measurableSet_Ioo hVc hJc hJ.measurableSet hδ hsep,
    repHalf_measurableLocalConstantTail hH hV measurableSet_Ioo hJ hVc hJc hδ hsep hlocV, ?_⟩
  filter_upwards [localConstantTail_ae_bound hH c measurableSet_Ioo hδ hsep,
    measurableLocalConstantTail_eq_ae_fibers hH c (Ioo a b)] with u hu he
  intro t ht
  change _ ∧ measurableLocalConstantTail hH c (Ioo a b) u t = _ ∧
    |measurableLocalConstantTail hH c (Ioo a b) u t| ≤ _
  rw [he t]
  exact ⟨(hu t ht).1, rfl, (hu t ht).2⟩

end ParabolicRectifiability.HalfTimeDerivative
