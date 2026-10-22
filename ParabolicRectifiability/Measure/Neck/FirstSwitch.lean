import ParabolicRectifiability.Measure.Neck.Definitions

/-! # The first change of the preferred type

A proof of the statement `firstSwitchCutoff_spec` for the
dyadic first-switch cutoff `f = firstSwitchCutoff ν k T R`.

Write `I_F(x,r) = typeFittingError ν k F x r` (the unnormalized fitting infimum) and
`p = k + 2`, so `b_F(x,r) = r^{-p} I_F(x,r)`. The mixed family is the disjoint union of
the two typed families, so `I_mixed = min(I_T, I_{T'})` (`typeFittingError_mixed`).
Each `I_F(x, ·)` is nondecreasing in the radius.

* **Cutoff.** The positive fibers of `f` are Borel; `{a < f}` is a countable union of
  strict-preference events (`measurable_firstSwitchCutoff`). Positive values lie in
  `{R 2^{-j}}`, hence finitely many above every `b > 0`.
* **Minimization.** At radius `2R` and above the whole source is seen from every point
  of `S`, so `T` minimizes there (global choice of `T`). At a dyadic radius `R 2^{-j}`
  above `f(x)` the other type is not strictly preferred, so `T` minimizes there too.
* **Tail.** For `f(x) < s ≤ 2R` take the dyadic `u ∈ [s, 2s]` above `f(x)`:
  `b_T(s) ≤ s^{-p} I_T(u) ≤ s^{-p} I_mixed(u) ≤ s^{-p} I_mixed(2s) = 2^p b_mixed(2s)`.
  For `s > 2R`, `b_T(s) ≤ b_mixed(s)`. Changing variables `s ↦ 2s` (which preserves
  `ds/s`) gives the budget `(2^p + 1) B ≤ (4^p + 1) B`.
* **Two tubes.** At `d = f(c) > 0` the other type is strictly preferred at `d`, and `T`
  minimizes at `2d` (an earlier dyadic radius, or `2R`). On `(2d, 4d]`,
  `b_mixed(s) ≥ (4d)^{-p} I_mixed(2d)`, and `(2d, 4d]` has `ds/s`-measure at least `1/2`,
  so `I_mixed(2d) ≤ 2 (4d)^p B`. Near-minimizers of the other type at `d` and of `T` at
  `2d`, restricted to `P(c,d)`, then give the joint error `≤ (4^{p+1} + 2) B d^p`. When
  `B = 0` there is no positive cutoff at all: the strict preference at `d` would be
  below `I_T(d) ≤ I_mixed(2d) = 0`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-! ## The scale measure -/

/-- The change of variables `u = 2s` preserves `ds/s` and doubles a nonnegative
lower endpoint (including `0`). -/
theorem lintegral_comp_two_mul_Ioi_scaleMeasure {b : ℝ} (hb : 0 ≤ b)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ s in Ioi b, g (2 * s) ∂scaleMeasure) =
      ∫⁻ u in Ioi (2 * b), g u ∂scaleMeasure := by
  have hpre : (fun s : ℝ => 2 * s) ⁻¹' Ioi (2 * b) = Ioi b := by
    ext s
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  have hf : Measurable (fun u : ℝ => ENNReal.ofReal (1 / u) * g u) :=
    measurable_scaleDensity.mul hg
  have he := setLIntegral_map (μ := (volume : Measure ℝ))
    (g := fun s : ℝ => 2 * s) (s := Ioi (2 * b)) measurableSet_Ioi hf
    (measurable_const_mul 2)
  rw [hpre, Real.map_volume_mul_left (by norm_num : (2 : ℝ) ≠ 0),
    setLIntegral_smul_measure] at he
  simp only [smul_eq_mul] at he
  have hcoef : (2 : ℝ≥0∞) * ENNReal.ofReal |(2 : ℝ)⁻¹| = 1 := by
    rw [abs_of_pos (inv_pos.mpr (by norm_num : (0 : ℝ) < 2)),
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  calc
    _ = ∫⁻ s in Ioi b, ENNReal.ofReal (1 / s) * g (2 * s) ∂volume :=
      setLIntegral_scaleMeasure measurableSet_Ioi (Ioi_subset_Ioi hb) _
        (hg.comp (measurable_const_mul 2))
    _ = (2 : ℝ≥0∞) * ∫⁻ s in Ioi b,
        ENNReal.ofReal (1 / (2 * s)) * g (2 * s) ∂volume := by
      rw [← lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num)]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s hs
      dsimp only
      have hsd : 1 / s = 2 * (1 / (2 * s)) := by field_simp [ne_of_gt (hb.trans_lt hs)]
      rw [hsd, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num only [ENNReal.ofReal_ofNat]
      ac_rfl
    _ = (2 : ℝ≥0∞) * (ENNReal.ofReal |(2 : ℝ)⁻¹| *
        ∫⁻ u in Ioi (2 * b), ENNReal.ofReal (1 / u) * g u ∂volume) := by rw [← he]
    _ = ∫⁻ u in Ioi (2 * b), ENNReal.ofReal (1 / u) * g u ∂volume := by
      rw [← mul_assoc, hcoef, one_mul]
    _ = _ := (setLIntegral_scaleMeasure measurableSet_Ioi
      (Ioi_subset_Ioi (mul_nonneg (by norm_num) hb)) g hg).symm

/-- A dyadic annulus has `ds/s`-measure at least `1/2`. -/
theorem half_le_scaleMeasure_Ioc {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal (1 / 2) ≤ scaleMeasure (Ioc a (2 * a)) := by
  rw [scaleMeasure_apply _ measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc a (2 * a) ⊆ Ioi 0 from fun _ hx => ha.trans hx.1)]
  calc ENNReal.ofReal (1 / 2) = ENNReal.ofReal (1 / (2 * a)) * volume (Ioc a (2 * a)) := by
        have h2a : (0 : ℝ) ≤ 1 / (2 * a) := by positivity
        rw [Real.volume_Ioc, ← ENNReal.ofReal_mul h2a]
        congr 1
        first | (field_simp; done) | (field_simp; ring)
    _ = ∫⁻ _ in Ioc a (2 * a), ENNReal.ofReal (1 / (2 * a)) ∂volume :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in Ioc a (2 * a), ENNReal.ofReal (1 / r) ∂volume :=
        setLIntegral_mono' measurableSet_Ioc fun r hr =>
          ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (ha.trans hr.1) hr.2)

/-! ## Fitting infima -/

section Fitting

variable {n k : ℕ} (ν : Measure (Space n))

/-- The mixed fitting infimum is the smaller of the two typed infima. -/
theorem typeFittingError_mixed (x : Space n) (r : ℝ) :
    typeFittingError ν k .mixed x r =
      typeFittingError ν k .horizontal x r ⊓ typeFittingError ν k .vertical x r := by
  show (⨅ L : HorizontalModel n k ⊕ VerticalModel n k, fit (T := .mixed) ν L x r) = _
  rw [iInf_sum]
  rfl

theorem typeFittingError_mixed_eq (T : NeckType) (x : Space n) (r : ℝ) :
    typeFittingError ν k .mixed x r =
      typeFittingError ν k T.toFamilyKind x r ⊓
        typeFittingError ν k T.other.toFamilyKind x r := by
  rw [typeFittingError_mixed]
  cases T
  · rfl
  · exact inf_comm _ _

/-- Fitting infima are nondecreasing in the radius. -/
theorem typeFittingError_mono (F : FamilyKind) (x : Space n) {r s : ℝ} (h : r ≤ s) :
    typeFittingError ν k F x r ≤ typeFittingError ν k F x s :=
  iInf_mono fun L => fit_mono_ball ν L (Metric.ball_subset_ball h)

theorem betaSq_eq_typeFittingError (F : FamilyKind) (x : Space n) {r : ℝ} (hr : 0 < r) :
    betaSq ν k F x r = (ENNReal.ofReal r)⁻¹ ^ (k + 2) * typeFittingError ν k F x r :=
  betaSq_of_pos ν k F x hr

theorem measurable_typeFittingError [IsFiniteMeasureOnCompacts ν] (F : FamilyKind) (r : ℝ) :
    Measurable (fun x => typeFittingError ν k F x r) := by
  have h := (measurable_iInf_fit (k := k) (T := F) ν).comp
    ((measurable_id (α := Space n)).prodMk (measurable_const (a := r)))
  exact h

theorem measurableSet_prefersOtherType [IsFiniteMeasureOnCompacts ν] (T : NeckType) (r : ℝ) :
    MeasurableSet {x | PrefersOtherType ν k T x r} :=
  measurableSet_lt (measurable_typeFittingError ν _ r) (measurable_typeFittingError ν _ r)

end Fitting

/-! ## The cutoff -/

section Cutoff

variable {n k : ℕ} {ν : Measure (Space n)} {T : NeckType} {R : ℝ}

theorem firstSwitchCutoff_eq_of_pos {x : Space n} (h : 0 < firstSwitchCutoff ν k T R x) :
    ∃ J : ℕ, firstSwitchCutoff ν k T R x = R / 2 ^ J ∧
      PrefersOtherType ν k T x (R / 2 ^ J) := by
  classical
  unfold firstSwitchCutoff at h ⊢
  split_ifs at h ⊢ with hex
  · exact ⟨_, rfl, Nat.find_spec hex⟩
  · exact absurd h (lt_irrefl 0)

theorem firstSwitchCutoff_of_exists {x : Space n}
    (h : ∃ j : ℕ, PrefersOtherType ν k T x (R / 2 ^ j)) :
    ∃ J : ℕ, firstSwitchCutoff ν k T R x = R / 2 ^ J ∧
      PrefersOtherType ν k T x (R / 2 ^ J) := by
  classical
  unfold firstSwitchCutoff
  split_ifs with hex
  · exact ⟨_, rfl, Nat.find_spec hex⟩
  · exact absurd h hex

theorem firstSwitchCutoff_eq_zero_of_not {x : Space n}
    (h : ¬ ∃ j : ℕ, PrefersOtherType ν k T x (R / 2 ^ j)) :
    firstSwitchCutoff ν k T R x = 0 := by
  unfold firstSwitchCutoff
  split_ifs with hex
  · exact absurd hex h
  · rfl

theorem le_firstSwitchCutoff (hR : 0 < R) {x : Space n} {j : ℕ}
    (h : PrefersOtherType ν k T x (R / 2 ^ j)) :
    R / 2 ^ j ≤ firstSwitchCutoff ν k T R x := by
  classical
  unfold firstSwitchCutoff
  split_ifs with hex
  · exact div_le_div_of_nonneg_left hR.le (by positivity)
      (pow_le_pow_right₀ one_le_two (Nat.find_min' hex h))
  · exact absurd ⟨j, h⟩ hex

theorem firstSwitchCutoff_nonneg (hR : 0 ≤ R) (x : Space n) :
    0 ≤ firstSwitchCutoff ν k T R x := by
  unfold firstSwitchCutoff
  split_ifs
  · positivity
  · exact le_rfl

theorem firstSwitchCutoff_le (hR : 0 ≤ R) (x : Space n) :
    firstSwitchCutoff ν k T R x ≤ R := by
  unfold firstSwitchCutoff
  split_ifs
  · exact div_le_self hR (one_le_pow₀ one_le_two)
  · exact hR

/-- At a dyadic radius above the cutoff the fixed type minimizes. -/
theorem typeFittingError_le_other_of_lt (hR : 0 < R) {x : Space n} {j : ℕ}
    (h : firstSwitchCutoff ν k T R x < R / 2 ^ j) :
    typeFittingError ν k T.toFamilyKind x (R / 2 ^ j) ≤
      typeFittingError ν k T.other.toFamilyKind x (R / 2 ^ j) := by
  by_contra hlt
  exact absurd (le_firstSwitchCutoff hR (not_le.mp hlt)) (not_le.mpr h)

theorem measurable_firstSwitchCutoff [IsFiniteMeasureOnCompacts ν] (hR : 0 < R) :
    Measurable (firstSwitchCutoff ν k T R) := by
  apply measurable_of_Ioi
  intro a
  have hset : firstSwitchCutoff ν k T R ⁻¹' Ioi a = {_x | a < 0} ∪
      ⋃ j : ℕ, ({_x | a < R / 2 ^ j} ∩ {x | PrefersOtherType ν k T x (R / 2 ^ j)}) := by
    ext x
    simp only [mem_preimage, mem_Ioi, mem_union, Set.mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      by_cases hex : ∃ j : ℕ, PrefersOtherType ν k T x (R / 2 ^ j)
      · obtain ⟨J, hJ, hP⟩ := firstSwitchCutoff_of_exists hex
        rw [hJ] at h
        exact Or.inr ⟨J, h, hP⟩
      · left
        rwa [firstSwitchCutoff_eq_zero_of_not hex] at h
    · rintro (h | ⟨j, h1, h2⟩)
      · exact h.trans_le (firstSwitchCutoff_nonneg hR.le x)
      · exact h1.trans_le (le_firstSwitchCutoff hR h2)
  rw [hset]
  exact (MeasurableSet.const _).union
    (MeasurableSet.iUnion fun j => (MeasurableSet.const _).inter
      (measurableSet_prefersOtherType ν T _))

theorem finite_values_firstSwitchCutoff (S : Set (Space n)) {b : ℝ}
    (hb : 0 < b) : (firstSwitchCutoff ν k T R '' S ∩ Ici b).Finite := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (R / b) one_lt_two
  refine ((Set.finite_lt_nat N).image (fun j : ℕ => R / 2 ^ j)).subset ?_
  rintro y ⟨⟨x, -, rfl⟩, hy⟩
  have hpos : 0 < firstSwitchCutoff ν k T R x := hb.trans_le hy
  obtain ⟨J, hJ, -⟩ := firstSwitchCutoff_eq_of_pos hpos
  refine ⟨J, ?_, hJ.symm⟩
  show J < N
  by_contra hJN
  push Not at hJN
  have h2 : (2 : ℝ) ^ N ≤ 2 ^ J := pow_le_pow_right₀ one_le_two hJN
  have hyb : b ≤ R / 2 ^ J := by rw [← hJ]; exact hy
  rw [le_div_iff₀ (by positivity)] at hyb
  rw [div_lt_iff₀ hb] at hN
  nlinarith

theorem isSourceCutoff_firstSwitchCutoff [IsFiniteMeasureOnCompacts ν] (hR : 0 < R)
    (S : Set (Space n)) : IsSourceCutoff S R (firstSwitchCutoff ν k T R) where
  measurable := measurable_firstSwitchCutoff hR
  nonneg := fun x _ => firstSwitchCutoff_nonneg hR.le x
  le_radius := fun x _ => firstSwitchCutoff_le hR.le x
  finite_values := fun _ hb => finite_values_firstSwitchCutoff S hb

end Cutoff

/-! ## Minimization and the pointwise comparisons -/

section Pointwise

variable {n k : ℕ} {ν : Measure (Space n)} {S : Set (Space n)} {q : Space n} {R : ℝ}

/-- From `2R` on, every point of `S ⊆ P(q,R)` sees the whole source. -/
theorem typeFittingError_eq_global (hS : S ⊆ Metric.ball q R) (hSc : ν Sᶜ = 0)
    (F : FamilyKind) {x : Space n} (hx : x ∈ S) {s : ℝ} (hs : 2 * R ≤ s) :
    typeFittingError ν k F x s = globalFittingError ν k F := by
  unfold typeFittingError globalFittingError
  refine iInf_congr fun L => fit_eq_global_of_ae_mem_ball ν L x s ?_
  filter_upwards [mem_ae_iff.mpr hSc] with w hw
  have h1 := Metric.mem_ball.mp (hS hw)
  have h2 := Metric.mem_ball.mp (hS hx)
  rw [Metric.mem_ball]
  linarith [dist_triangle w q x, dist_comm x q]

theorem typeFittingError_le_other_of_global (hS : S ⊆ Metric.ball q R) (hSc : ν Sᶜ = 0)
    {T : NeckType}
    (hglob : globalFittingError ν k T.toFamilyKind ≤ globalFittingError ν k T.other.toFamilyKind)
    {x : Space n} (hx : x ∈ S) {s : ℝ} (hs : 2 * R ≤ s) :
    typeFittingError ν k T.toFamilyKind x s ≤ typeFittingError ν k T.other.toFamilyKind x s := by
  rw [typeFittingError_eq_global hS hSc _ hx hs, typeFittingError_eq_global hS hSc _ hx hs]
  exact hglob

/-- If the fixed type minimizes at `u`, it is below the mixed infimum at `u`. -/
theorem typeFittingError_le_mixed_of_le {T : NeckType} {x : Space n} {u : ℝ}
    (h : typeFittingError ν k T.toFamilyKind x u ≤
      typeFittingError ν k T.other.toFamilyKind x u) :
    typeFittingError ν k T.toFamilyKind x u ≤ typeFittingError ν k .mixed x u := by
  rw [typeFittingError_mixed_eq ν T]
  exact le_inf le_rfl h

variable {T : NeckType}

/-- Above the cutoff and up to `2R`, the fixed-type beta is controlled by the mixed beta
at twice the radius. -/
theorem betaSq_le_two_pow_mixed (hR : 0 < R) (hS : S ⊆ Metric.ball q R) (hSc : ν Sᶜ = 0)
    (hglob : globalFittingError ν k T.toFamilyKind ≤ globalFittingError ν k T.other.toFamilyKind)
    {x : Space n} (hx : x ∈ S) {s : ℝ} (hs : s ∈ Ioc (firstSwitchCutoff ν k T R x) (2 * R)) :
    betaSq ν k T.toFamilyKind x s ≤ 2 ^ (k + 2) * betaSq ν k .mixed x (2 * s) := by
  have hs0 : 0 < s := (firstSwitchCutoff_nonneg hR.le x).trans_lt hs.1
  have hs2 : 0 < 2 * s := by linarith
  -- A dyadic radius `u ∈ [s, 2s]` above the cutoff at which `T` minimizes.
  have hu : ∃ u : ℝ, s ≤ u ∧ u ≤ 2 * s ∧
      typeFittingError ν k T.toFamilyKind x u ≤
        typeFittingError ν k T.other.toFamilyKind x u := by
    have hex : ∃ m : ℕ, R / 2 ^ m < s := by
      obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (R / s) one_lt_two
      exact ⟨m, by rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hs0] at hm; linarith⟩
    classical
    rcases hm : Nat.find hex with _ | j
    · have h0 := Nat.find_spec hex
      rw [hm, pow_zero, div_one] at h0
      exact ⟨2 * R, hs.2, by linarith,
        typeFittingError_le_other_of_global hS hSc hglob hx le_rfl⟩
    · have hlt := Nat.find_spec hex
      rw [hm] at hlt
      have hge : ¬ R / 2 ^ j < s := Nat.find_min hex (by omega)
      push Not at hge
      have h2 : R / 2 ^ j = 2 * (R / 2 ^ (j + 1)) := by rw [pow_succ]; ring
      exact ⟨R / 2 ^ j, hge, by linarith,
        typeFittingError_le_other_of_lt hR (hs.1.trans_le hge)⟩
  obtain ⟨u, hsu, hu2, hmin⟩ := hu
  have hn := radius_ratio_normalization hs0 hs2 (k + 2) (typeFittingError ν k .mixed x (2 * s))
  have hr : (2 * s) / s = 2 := by field_simp
  norm_num only [hr, ENNReal.ofReal_ofNat] at hn
  rw [betaSq_eq_typeFittingError ν _ x hs0, betaSq_eq_typeFittingError ν _ x hs2, hn]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  calc typeFittingError ν k T.toFamilyKind x s
      ≤ typeFittingError ν k T.toFamilyKind x u := typeFittingError_mono ν _ x hsu
    _ ≤ typeFittingError ν k .mixed x u := typeFittingError_le_mixed_of_le hmin
    _ ≤ typeFittingError ν k .mixed x (2 * s) := typeFittingError_mono ν _ x hu2

/-- Beyond `2R` the fixed-type beta is at most the mixed beta. -/
theorem betaSq_le_mixed_of_global (hR : 0 < R) (hS : S ⊆ Metric.ball q R) (hSc : ν Sᶜ = 0)
    (hglob : globalFittingError ν k T.toFamilyKind ≤ globalFittingError ν k T.other.toFamilyKind)
    {x : Space n} (hx : x ∈ S) {s : ℝ} (hs : 2 * R < s) :
    betaSq ν k T.toFamilyKind x s ≤ betaSq ν k .mixed x s := by
  have hs0 : 0 < s := by linarith
  rw [betaSq_eq_typeFittingError ν _ x hs0, betaSq_eq_typeFittingError ν _ x hs0]
  exact mul_le_mul_of_nonneg_left (typeFittingError_le_mixed_of_le
    (typeFittingError_le_other_of_global hS hSc hglob hx hs.le)) zero_le

end Pointwise

/-! ## The fixed-type budget -/

theorem tailEnergy_firstSwitchCutoff_le {n k : ℕ} {ν : Measure (Space n)}
    [IsFiniteMeasureOnCompacts ν] {S : Set (Space n)} {q : Space n} {R B : ℝ} {T : NeckType}
    (hR : 0 < R) (hB : 0 ≤ B) (hS : S ⊆ Metric.ball q R) (hSc : ν Sᶜ = 0)
    (hglob : globalFittingError ν k T.toFamilyKind ≤ globalFittingError ν k T.other.toFamilyKind)
    {x : Space n} (hx : x ∈ S) (hE : allScaleEnergy ν k .mixed x ≤ ENNReal.ofReal B) :
    tailEnergy ν k T.toFamilyKind (firstSwitchCutoff ν k T R x) x ≤
      ENNReal.ofReal ((4 ^ (k + 2) + 1) * B) := by
  set f := firstSwitchCutoff ν k T R x
  have hf0 : 0 ≤ f := firstSwitchCutoff_nonneg hR.le x
  have hmeas : Measurable (fun u => betaSq ν k .mixed x u) := by
    have h := (measurable_betaSq ν k .mixed).comp
      ((measurable_const (a := x)).prodMk (measurable_id (α := ℝ)))
    exact h
  have hsub : Ioi f ⊆ Ioc f (2 * R) ∪ Ioi (2 * R) := by
    intro s hs
    rcases le_or_gt s (2 * R) with h | h
    · exact Or.inl ⟨hs, h⟩
    · exact Or.inr h
  have h2p : (2 : ℝ≥0∞) ^ (k + 2) ≠ ⊤ := by finiteness
  have h2r : (0 : ℝ) ≤ 2 ^ (k + 2) := by positivity
  have h2B : (0 : ℝ) ≤ 2 ^ (k + 2) * B := by positivity
  have hEdef : allScaleEnergy ν k .mixed x =
      ∫⁻ u in Ioi 0, betaSq ν k .mixed x u ∂scaleMeasure := rfl
  unfold tailEnergy
  calc ∫⁻ s in Ioi f, betaSq ν k T.toFamilyKind x s ∂scaleMeasure
      ≤ ∫⁻ s in Ioc f (2 * R) ∪ Ioi (2 * R), betaSq ν k T.toFamilyKind x s ∂scaleMeasure :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ s in Ioc f (2 * R), betaSq ν k T.toFamilyKind x s ∂scaleMeasure) +
          ∫⁻ s in Ioi (2 * R), betaSq ν k T.toFamilyKind x s ∂scaleMeasure :=
        lintegral_union_le _ _ _
    _ ≤ (∫⁻ s in Ioc f (2 * R), 2 ^ (k + 2) * betaSq ν k .mixed x (2 * s) ∂scaleMeasure) +
          ∫⁻ s in Ioi (2 * R), betaSq ν k .mixed x s ∂scaleMeasure :=
        add_le_add
          (setLIntegral_mono' measurableSet_Ioc fun s hs =>
            betaSq_le_two_pow_mixed hR hS hSc hglob hx hs)
          (setLIntegral_mono' measurableSet_Ioi fun s hs =>
            betaSq_le_mixed_of_global hR hS hSc hglob hx hs)
    _ ≤ 2 ^ (k + 2) * (∫⁻ s in Ioi f, betaSq ν k .mixed x (2 * s) ∂scaleMeasure) +
          allScaleEnergy ν k .mixed x := by
        rw [lintegral_const_mul' _ _ h2p, hEdef]
        exact add_le_add (mul_le_mul_of_nonneg_left (lintegral_mono_set Ioc_subset_Ioi_self)
          zero_le) (lintegral_mono_set (Ioi_subset_Ioi (by linarith)))
    _ = 2 ^ (k + 2) * (∫⁻ u in Ioi (2 * f), betaSq ν k .mixed x u ∂scaleMeasure) +
          allScaleEnergy ν k .mixed x := by
        rw [lintegral_comp_two_mul_Ioi_scaleMeasure hf0 _ hmeas]
    _ ≤ 2 ^ (k + 2) * allScaleEnergy ν k .mixed x + allScaleEnergy ν k .mixed x := by
        rw [hEdef]
        exact add_le_add (mul_le_mul_of_nonneg_left
          (lintegral_mono_set (Ioi_subset_Ioi (by linarith))) zero_le) le_rfl
    _ ≤ 2 ^ (k + 2) * ENNReal.ofReal B + ENNReal.ofReal B :=
        add_le_add (mul_le_mul_of_nonneg_left hE zero_le) hE
    _ = ENNReal.ofReal (2 ^ (k + 2) * B + B) := by
        rw [ENNReal.ofReal_add h2B hB, ENNReal.ofReal_mul h2r,
          ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal ((4 ^ (k + 2) + 1) * B) := by
        apply ENNReal.ofReal_le_ofReal
        have h24 : (2 : ℝ) ^ (k + 2) ≤ 4 ^ (k + 2) :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
        nlinarith [mul_le_mul_of_nonneg_right h24 hB]

/-! ## Two tubes -/

/-- The mixed infimum at `a` is controlled by the mixed energy on `(a, 2a]`. -/
theorem typeFittingError_mixed_le_energy {n k : ℕ} (ν : Measure (Space n)) (x : Space n)
    {a : ℝ} (ha : 0 < a) {B : ℝ}
    (hE : allScaleEnergy ν k .mixed x ≤ ENNReal.ofReal B) :
    typeFittingError ν k .mixed x a ≤ ENNReal.ofReal (2 * (2 * a) ^ (k + 2) * B) := by
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * a) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  set I := typeFittingError ν k .mixed x a
  have hlow : c⁻¹ ^ (k + 2) * I * ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal B := by
    calc c⁻¹ ^ (k + 2) * I * ENNReal.ofReal (1 / 2)
        ≤ c⁻¹ ^ (k + 2) * I * scaleMeasure (Ioc a (2 * a)) :=
          mul_le_mul_of_nonneg_left (half_le_scaleMeasure_Ioc ha) zero_le
      _ = ∫⁻ _ in Ioc a (2 * a), c⁻¹ ^ (k + 2) * I ∂scaleMeasure := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ s in Ioc a (2 * a), betaSq ν k .mixed x s ∂scaleMeasure := by
          refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
          have hs0 : 0 < s := ha.trans hs.1
          rw [betaSq_eq_typeFittingError ν _ x hs0]
          refine mul_le_mul' (pow_le_pow_left₀ zero_le ?_ _)
            (typeFittingError_mono ν _ x hs.1.le)
          exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hs.2)
      _ ≤ ∫⁻ s in Ioi 0, betaSq ν k .mixed x s ∂scaleMeasure :=
          lintegral_mono_set fun s hs => ha.trans hs.1
      _ ≤ ENNReal.ofReal B := hE
  have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 1 := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  calc I = (2 * c ^ (k + 2)) * (c⁻¹ ^ (k + 2) * I * ENNReal.ofReal (1 / 2)) := by
        rw [show (2 * c ^ (k + 2)) * (c⁻¹ ^ (k + 2) * I * ENNReal.ofReal (1 / 2)) =
            (c * c⁻¹) ^ (k + 2) * (2 * ENNReal.ofReal (1 / 2)) * I by ring,
          ENNReal.mul_inv_cancel hc0 hctop, one_pow, h2, one_mul, one_mul]
    _ ≤ (2 * c ^ (k + 2)) * ENNReal.ofReal B := mul_le_mul_of_nonneg_left hlow zero_le
    _ = ENNReal.ofReal (2 * (2 * a) ^ (k + 2) * B) := by
        have h1 : (0 : ℝ) ≤ 2 * (2 * a) ^ (k + 2) := by positivity
        rw [ENNReal.ofReal_mul h1, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 2 * a), ENNReal.ofReal_ofNat]

/-- The two-tube estimate at a positive cutoff, with a model of each type. -/
theorem two_tubes {n k : ℕ} {ν : Measure (Space n)} {S : Set (Space n)} {q : Space n}
    {R B : ℝ} {T : NeckType} (hR : 0 < R) (hB : 0 ≤ B) (hS : S ⊆ Metric.ball q R)
    (hSc : ν Sᶜ = 0)
    (hglob : globalFittingError ν k T.toFamilyKind ≤ globalFittingError ν k T.other.toFamilyKind)
    {c : Space n} (hc : c ∈ S) (hE : allScaleEnergy ν k .mixed c ≤ ENNReal.ofReal B)
    (hpos : 0 < firstSwitchCutoff ν k T R c) :
    ∃ (LT : Models n k T.toFamilyKind) (LO : Models n k T.other.toFamilyKind),
      fit ν LT c (firstSwitchCutoff ν k T R c) + fit ν LO c (firstSwitchCutoff ν k T R c) ≤
        ENNReal.ofReal ((4 * 4 ^ (k + 2) + 2) * B * firstSwitchCutoff ν k T R c ^ (k + 2)) := by
  set d := firstSwitchCutoff ν k T R c with hd
  obtain ⟨J, hJ0, hP0⟩ := firstSwitchCutoff_eq_of_pos hpos
  have hJ : d = R / 2 ^ J := hJ0
  have hd2 : 0 < 2 * d := by linarith
  -- The fixed type minimizes at `2d`.
  have hmin2 : typeFittingError ν k T.toFamilyKind c (2 * d) ≤
      typeFittingError ν k T.other.toFamilyKind c (2 * d) := by
    rcases J with _ | j
    · rw [hJ, pow_zero, div_one]
      exact typeFittingError_le_other_of_global hS hSc hglob hc le_rfl
    · have h2d : 2 * d = R / 2 ^ j := by rw [hJ, pow_succ]; ring
      rw [h2d]
      exact typeFittingError_le_other_of_lt hR (by rw [← hd, ← h2d]; linarith)
  set M : ℝ := 2 * (2 * (2 * d)) ^ (k + 2) * B with hM
  have hmix : typeFittingError ν k .mixed c (2 * d) ≤ ENNReal.ofReal M :=
    typeFittingError_mixed_le_energy ν c hd2 hE
  have hT2 : typeFittingError ν k T.toFamilyKind c (2 * d) ≤ ENNReal.ofReal M :=
    (typeFittingError_le_mixed_of_le hmin2).trans hmix
  have hP : typeFittingError ν k T.other.toFamilyKind c d <
      typeFittingError ν k T.toFamilyKind c d := by
    rw [hJ]
    exact hP0
  have hO : typeFittingError ν k T.other.toFamilyKind c d < ENNReal.ofReal M :=
    lt_of_lt_of_le hP ((typeFittingError_mono ν _ c (by linarith)).trans hT2)
  -- Hence `B > 0`.
  have hBpos : 0 < B := by
    rcases hB.lt_or_eq with h | h
    · exact h
    · exfalso
      have : ENNReal.ofReal M = 0 := by rw [hM, ← h, mul_zero, ENNReal.ofReal_zero]
      rw [this] at hO
      exact absurd hO (not_lt.mpr zero_le)
  set η : ℝ≥0∞ := ENNReal.ofReal (B * d ^ (k + 2)) with hη
  have hη0 : η ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hOtop : typeFittingError ν k T.other.toFamilyKind c d ≠ ⊤ :=
    (hO.trans ENNReal.ofReal_lt_top).ne
  have hTtop : typeFittingError ν k T.toFamilyKind c (2 * d) ≠ ⊤ :=
    (hT2.trans_lt ENNReal.ofReal_lt_top).ne
  obtain ⟨LO, hLO⟩ := iInf_lt_iff.mp (ENNReal.lt_add_right hOtop hη0)
  obtain ⟨LT, hLT⟩ := iInf_lt_iff.mp (ENNReal.lt_add_right hTtop hη0)
  refine ⟨LT, LO, ?_⟩
  have hLT' : fit ν LT c d ≤ ENNReal.ofReal M + η :=
    (fit_mono_ball ν LT (Metric.ball_subset_ball (by linarith))).trans
      (hLT.le.trans (add_le_add hT2 le_rfl))
  have hLO' : fit ν LO c d ≤ ENNReal.ofReal M + η := hLO.le.trans (add_le_add hO.le le_rfl)
  have hM0 : 0 ≤ M := by positivity
  have hBd : 0 ≤ B * d ^ (k + 2) := by positivity
  calc fit ν LT c d + fit ν LO c d
      ≤ (ENNReal.ofReal M + η) + (ENNReal.ofReal M + η) := add_le_add hLT' hLO'
    _ = ENNReal.ofReal (2 * (M + B * d ^ (k + 2))) := by
        rw [hη, ← ENNReal.ofReal_add hM0 hBd, ← ENNReal.ofReal_add (add_nonneg hM0 hBd)
          (add_nonneg hM0 hBd), two_mul]
    _ ≤ ENNReal.ofReal ((4 * 4 ^ (k + 2) + 2) * B * d ^ (k + 2)) := by
        apply le_of_eq
        congr 1
        rw [hM, show 2 * (2 * d) = 4 * d by ring, mul_pow]
        ring

/-! ## The first-switch statement -/

/-- **First-switch cutoff**: the statement `firstSwitchCutoff_spec`. -/
theorem firstSwitchCutoff_spec_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k → k ≤ n →
      ∀ (q : Space n) (R B : ℝ) (ν : Measure (Space n)) (S : Set (Space n)) (T : NeckType),
        0 < R → 0 ≤ B → IsFiniteMeasure ν → MeasurableSet S → S ⊆ Metric.ball q R →
        ν Sᶜ = 0 →
        (∀ x ∈ S, allScaleEnergy ν k .mixed x ≤ ENNReal.ofReal B) →
        globalFittingError ν k T.toFamilyKind ≤ globalFittingError ν k T.other.toFamilyKind →
        IsSourceCutoff S R (firstSwitchCutoff ν k T R) ∧
          (∀ x ∈ S, tailEnergy ν k T.toFamilyKind (firstSwitchCutoff ν k T R x) x ≤
            ENNReal.ofReal ((4 ^ (k + 2) + 1) * B)) ∧
          ∀ c ∈ S, 0 < firstSwitchCutoff ν k T R c →
            ∃ (LH : HorizontalModel n k) (LV : VerticalModel n k),
              ∫⁻ z in Metric.ball c (firstSwitchCutoff ν k T R c),
                  (modelCost (T := .horizontal) LH z + modelCost (T := .vertical) LV z) ∂ν ≤
                ENNReal.ofReal (C * B * firstSwitchCutoff ν k T R c ^ (k + 2)) := by
  refine ⟨4 ^ (n + 3) + 2, by positivity, ?_⟩
  intro k hk hkn q R B ν S T hR hB hfin hSm hS hSc hE hglob
  refine ⟨isSourceCutoff_firstSwitchCutoff hR S,
    fun x hx => tailEnergy_firstSwitchCutoff_le hR hB hS hSc hglob hx (hE x hx), ?_⟩
  intro c hc hpos
  obtain ⟨LT, LO, hfit⟩ := two_tubes hR hB hS hSc hglob hc (hE c hc) hpos
  have hd0 : 0 ≤ firstSwitchCutoff ν k T R c := hpos.le
  have hC : (4 * 4 ^ (k + 2) + 2) * B * firstSwitchCutoff ν k T R c ^ (k + 2) ≤
      (4 ^ (n + 3) + 2) * B * firstSwitchCutoff ν k T R c ^ (k + 2) := by
    have h4 : (4 : ℝ) * 4 ^ (k + 2) ≤ 4 ^ (n + 3) := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hB)
      (pow_nonneg hd0 _)
  have hbound := hfit.trans (ENNReal.ofReal_le_ofReal hC)
  cases T with
  | horizontal =>
    refine ⟨LT, LO, ?_⟩
    rw [lintegral_add_left (measurable_modelCost (T := .horizontal) LT)]
    exact hbound
  | vertical =>
    refine ⟨LO, LT, ?_⟩
    rw [lintegral_add_left (measurable_modelCost (T := .horizontal) LO)]
    exact (add_comm _ _).le.trans hbound

end ParabolicRectifiability
