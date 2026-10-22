import ParabolicRectifiability.Decomposition.Interfaces
import ParabolicRectifiability.Metric.BaseVolume
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-! # Core density for a Euclidean parameter set

Core-density estimates for a horizontal chart with Euclidean parameter space `ℝ^k`. The chart
`φ : A → Space n` is defined only on the compact parameter set `A`; it is
`L`-Lipschitz and `L`-antilipschitz for the parabolic metric. The measure is the
image's own Hausdorff measure `η = (hausdorffP n k).restrict (range φ)`.

* `horizontalChart_hausdorff_upper_proof`: `η` is finite and has upper `k`-growth;
  an ambient ball meeting the image pulls back into a parameter ball of radius `2Mr`.
* `ae_volume_density_half_proof`: Lebesgue density one half at almost every point of
  an arbitrary set, for open balls and every dimension `k`, including `k = 0`.
* `horizontalChart_ae_lowerDensity_proof`: `η(P(φ a, r)) ≥ ½ M^{-2k} r^k` for small
  `r` at every Lebesgue density point `a`; the remaining parameters form a
  Lebesgue-null set whose image is `η`-null.
* `horizontalChart_coreDensity_proof`: the conjunction.

Throughout, `M = max 1 L` replaces `L`, so that no division by zero occurs. -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-- An antilipschitz constant may be enlarged. -/
theorem antilipschitzWith_of_le {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {K K' : ℝ≥0} {f : α → β} (hf : AntilipschitzWith K f) (h : K ≤ K') :
    AntilipschitzWith K' f := fun x y =>
  (hf x y).trans (mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.2 h) zero_le)

/-- Lebesgue density in `ℝ^k` with open balls: at almost every point `u` of an
arbitrary set `A`, the relative volume of `A` in all small balls is at least one half.
The set `A` need not be measurable, and `k = 0` is included. -/
theorem ae_volume_density_half_proof {k : ℕ} (A : Set (Spatial k)) :
    ∀ᵐ u ∂(volume : Measure (Spatial k)).restrict A, ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        volume (Metric.ball u r) ≤ 2 * volume (A ∩ Metric.ball u r) := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (Spatial k)) A]
    with u hu
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (2 : ℝ≥0∞)⁻¹ < volume (A ∩ Metric.closedBall u r) / volume (Metric.closedBall u r) :=
    hu.eventually_const_lt (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
  obtain ⟨ε, hε, hεr⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨ε / 2, half_pos hε, fun r hr hrε => ?_⟩
  have hdist : dist r 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hr]
    linarith
  have hlt := hεr hdist (show r ∈ Ioi (0 : ℝ) from hr)
  -- Open and closed balls have the same positive finite volume.
  have hball : volume (Metric.ball u r) = volume (Metric.closedBall u r) := by
    rw [volume_spatial_ball u hr, volume_spatial_closedBall u hr.le]
  have hpos : volume (Metric.closedBall u r) ≠ 0 := by
    rw [← hball]; exact (Metric.measure_ball_pos volume u hr).ne'
  have hfin : volume (Metric.closedBall u r) ≠ ∞ := ne_of_lt MeasureTheory.measure_closedBall_lt_top
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hpos) (Or.inl hfin)] at hlt
  -- The sphere is null, so the closed ball can be replaced by the open ball.
  have hsphere : volume (A ∩ Metric.closedBall u r) ≤ volume (A ∩ Metric.ball u r) := by
    calc volume (A ∩ Metric.closedBall u r)
        ≤ volume ((A ∩ Metric.ball u r) ∪ Metric.sphere u r) := by
          refine measure_mono fun y hy => ?_
          rw [← Metric.ball_union_sphere] at hy
          rcases hy.2 with h | h
          · exact Or.inl ⟨hy.1, h⟩
          · exact Or.inr h
      _ ≤ volume (A ∩ Metric.ball u r) + volume (Metric.sphere u r) := measure_union_le _ _
      _ = volume (A ∩ Metric.ball u r) := by
          rw [Measure.addHaar_sphere_of_ne_zero volume u hr.ne', add_zero]
  calc volume (Metric.ball u r) = 2 * ((2 : ℝ≥0∞)⁻¹ * volume (Metric.closedBall u r)) := by
        rw [hball, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * volume (A ∩ Metric.closedBall u r) := by gcongr
    _ ≤ 2 * volume (A ∩ Metric.ball u r) := by gcongr

/-- The image of a compact parameter set under a parabolic bi-Lipschitz map has finite
own `k`-dimensional Hausdorff measure and upper `k`-growth for all radii. -/
theorem horizontalChart_hausdorff_upper_proof {n k : ℕ} {A : Set (Spatial k)}
    (hA : IsCompact A)
    {φ : A → Space n} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hφ' : AntilipschitzWith L φ) :
    hausdorffP n k (Set.range φ) < ⊤ ∧
      ∃ U : ℝ, 0 ≤ U ∧ ∀ (q : Space n) (r : ℝ), 0 < r →
        (hausdorffP n k).restrict (Set.range φ) (Metric.ball q r) ≤
          ENNReal.ofReal (U * r ^ k) := by
  set M : ℝ≥0 := max 1 L
  have hM : LipschitzWith M φ := hφ.weaken (le_max_right _ _)
  have hM' : AntilipschitzWith M φ := antilipschitzWith_of_le hφ' (le_max_right _ _)
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (by exact_mod_cast le_max_left 1 L)
  have hC : horizontalHausdorffConstant k ≠ ∞ := (horizontalHausdorffConstant_lt_top k).ne
  -- Hausdorff measure of an image, through the chart and the volume comparison.
  have himage : ∀ E : Set A, hausdorffP n k (φ '' E) ≤
      (M : ℝ≥0∞) ^ k * (horizontalHausdorffConstant k *
        volume ((Subtype.val : A → Spatial k) '' E)) := by
    intro E
    calc hausdorffP n k (φ '' E)
        ≤ (M : ℝ≥0∞) ^ k *
            Measure.hausdorffMeasure (k : ℝ) ((Subtype.val : A → Spatial k) '' E) :=
          hausdorffMeasure_subtype_image_le hM k E
      _ ≤ _ := by gcongr; exact (spatial_hausdorff_comparison k _).2
  constructor
  · rw [← Set.image_univ]
    refine (himage univ).trans_lt
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
        (ENNReal.mul_lt_top hC.lt_top ((measure_mono ?_).trans_lt hA.measure_lt_top)))
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  · have hX : (M : ℝ≥0∞) ^ k * (horizontalHausdorffConstant k * omega k) ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
        (ENNReal.mul_ne_top hC (omega_lt_top k).ne)
    refine ⟨((M : ℝ≥0∞) ^ k * (horizontalHausdorffConstant k * omega k)).toReal *
      (2 * M) ^ k, by positivity, fun q r hr => ?_⟩
    rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet]
    rcases (Metric.ball q r ∩ range φ).eq_empty_or_nonempty with h | ⟨_, hq, a₀, rfl⟩
    · rw [h, measure_empty]
      exact zero_le
    have hball : (Subtype.val : A → Spatial k) '' (φ ⁻¹' Metric.ball q r) ⊆
        Metric.ball (a₀ : Spatial k) (2 * M * r) := by
      rintro _ ⟨a, ha, rfl⟩
      rw [Metric.mem_ball]
      have h2 : dist (φ a) (φ a₀) < 2 * r := by
        calc dist (φ a) (φ a₀) ≤ dist (φ a) q + dist q (φ a₀) := dist_triangle _ _ _
          _ < r + r := add_lt_add (Metric.mem_ball.1 ha) (by rw [dist_comm]; exact hq)
          _ = 2 * r := by ring
      calc dist (a : Spatial k) a₀ ≤ M * dist (φ a) (φ a₀) := hM'.le_mul_dist a a₀
        _ < M * (2 * r) := mul_lt_mul_of_pos_left h2 hMpos
        _ = 2 * M * r := by ring
    have hR : (0 : ℝ) < 2 * M * r := by positivity
    calc hausdorffP n k (Metric.ball q r ∩ range φ)
        = hausdorffP n k (φ '' (φ ⁻¹' Metric.ball q r)) := by
          rw [image_preimage_eq_inter_range]
      _ ≤ (M : ℝ≥0∞) ^ k * (horizontalHausdorffConstant k *
            volume ((Subtype.val : A → Spatial k) '' (φ ⁻¹' Metric.ball q r))) := himage _
      _ ≤ (M : ℝ≥0∞) ^ k * (horizontalHausdorffConstant k *
            volume (Metric.ball (a₀ : Spatial k) (2 * M * r))) := by
          gcongr
      _ = (M : ℝ≥0∞) ^ k * (horizontalHausdorffConstant k * omega k) *
            ENNReal.ofReal ((2 * M * r) ^ k) := by
          rw [volume_spatial_ball _ hR, ENNReal.ofReal_pow hR.le]
          ring
      _ = ENNReal.ofReal (((M : ℝ≥0∞) ^ k * (horizontalHausdorffConstant k * omega k)).toReal *
            (2 * M) ^ k * r ^ k) := by
          have hreal : ((M : ℝ≥0∞) ^ k * (horizontalHausdorffConstant k * omega k)).toReal *
              (2 * M) ^ k * r ^ k =
              ((M : ℝ≥0∞) ^ k * (horizontalHausdorffConstant k * omega k)).toReal *
                (2 * M * r) ^ k := by
            ring
          rw [hreal, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hX]

/-- The own Hausdorff measure of the image of a compact parameter set under a
parabolic bi-Lipschitz map has positive lower `k`-density almost everywhere. -/
theorem horizontalChart_ae_lowerDensity_proof {n k : ℕ} {A : Set (Spatial k)}
    (hA : IsCompact A)
    {φ : A → Space n} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hφ' : AntilipschitzWith L φ) :
    ∀ᵐ z ∂(hausdorffP n k).restrict (Set.range φ),
      HasPositiveLowerDensity ((hausdorffP n k).restrict (Set.range φ)) k z := by
  classical
  set M : ℝ≥0 := max 1 L
  have hM : LipschitzWith M φ := hφ.weaken (le_max_right _ _)
  have hM' : AntilipschitzWith M φ := antilipschitzWith_of_le hφ' (le_max_right _ _)
  have hMpos' : (0 : ℝ≥0) < M := lt_of_lt_of_le one_pos (le_max_left 1 L)
  have hMpos : (0 : ℝ) < M := NNReal.coe_pos.2 hMpos'
  -- Lebesgue density points of `A`.
  set G : Set (Spatial k) := {u | ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
    volume (Metric.ball u r) ≤ 2 * volume (A ∩ Metric.ball u r)}
  have hAm : MeasurableSet A := hA.isClosed.measurableSet
  have hN : volume (A \ G) = 0 := by
    have h := ae_volume_density_half_proof A
    rw [ae_restrict_iff' hAm, ae_iff] at h
    refine measure_mono_null ?_ h
    intro u hu h'
    exact hu.2 (h' hu.1)
  -- The non-density parameters have Hausdorff-null image.
  set S : Set A := {a | (a : Spatial k) ∉ G}
  have hS : hausdorffP n k (φ '' S) = 0 := by
    have h2 : Measure.hausdorffMeasure (k : ℝ) ((Subtype.val : A → Spatial k) '' S) = 0 := by
      refine measure_mono_null ?_ (le_antisymm ((spatial_hausdorff_comparison k (A \ G)).2.trans
        (by rw [hN, mul_zero])) zero_le)
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a.2, ha⟩
    exact le_antisymm ((hausdorffMeasure_subtype_image_le hM k S).trans
      (by rw [h2, mul_zero])) zero_le
  -- The image is compact, hence measurable.
  have hRm : MeasurableSet (range φ) := by
    have : CompactSpace A := isCompact_iff_compactSpace.mp hA
    exact (isCompact_range hM.continuous).isClosed.measurableSet
  -- Density at the image of a Lebesgue density point.
  have hgoodpt : ∀ a : A, (a : Spatial k) ∈ G →
      HasPositiveLowerDensity ((hausdorffP n k).restrict (Set.range φ)) k (φ a) := by
    rintro a ⟨r₀, hr₀, hgood⟩
    refine ⟨((M : ℝ)⁻¹) ^ k * ((M : ℝ)⁻¹) ^ k / 2, M * r₀, by positivity, by positivity,
      fun r hr hrr => ?_⟩
    have hrM : 0 < r / M := div_pos hr hMpos
    have hrM' : r / M ≤ r₀ := by
      rw [div_le_iff₀ hMpos]
      linarith [mul_comm (M : ℝ) r₀]
    set T : Set A := {b | dist (b : Spatial k) (a : Spatial k) < r / M}
    have hT : φ '' T ⊆ Metric.ball (φ a) r ∩ range φ := by
      rintro _ ⟨b, hb, rfl⟩
      refine ⟨?_, mem_range_self b⟩
      rw [Metric.mem_ball]
      calc dist (φ b) (φ a) ≤ M * dist b a := hM.dist_le_mul b a
        _ < M * (r / M) := mul_lt_mul_of_pos_left hb hMpos
        _ = r := mul_div_cancel₀ r hMpos.ne'
    have hTval : (Subtype.val : A → Spatial k) '' T = A ∩ Metric.ball (a : Spatial k) (r / M) := by
      ext u
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b.2, hb⟩
      · rintro ⟨hu, hu'⟩
        exact ⟨⟨u, hu⟩, hu', rfl⟩
    have hlow := hausdorffMeasure_subtype_image_ge (l := M⁻¹) (inv_pos.2 hMpos')
      (by rw [inv_inv]; exact hM') k T
    rw [hTval] at hlow
    have hcmp := (spatial_hausdorff_comparison k (A ∩ Metric.ball (a : Spatial k) (r / M))).1
    have hdens := hgood (r / M) hrM hrM'
    rw [volume_spatial_ball _ hrM] at hdens
    -- Arithmetic: `ofReal (a r^k) = M^{-k} (x / 2)` with `x = (r/M)^k ≤ 2 ω⁻¹ vol`.
    have hx : ENNReal.ofReal (r / M) ^ k / 2 ≤
        (omega k)⁻¹ * volume (A ∩ Metric.ball (a : Spatial k) (r / M)) := by
      refine ENNReal.div_le_of_le_mul ?_
      calc ENNReal.ofReal (r / M) ^ k
          = (omega k)⁻¹ * (omega k * ENNReal.ofReal (r / M) ^ k) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel (omega_pos k).ne' (omega_lt_top k).ne,
              one_mul]
        _ ≤ (omega k)⁻¹ * (2 * volume (A ∩ Metric.ball (a : Spatial k) (r / M))) := by
            gcongr
        _ = _ := by ring
    have hval : ENNReal.ofReal (((M : ℝ)⁻¹) ^ k * ((M : ℝ)⁻¹) ^ k / 2 * r ^ k) =
        ((M⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * (ENNReal.ofReal (r / M) ^ k / 2) := by
      have : ((M : ℝ)⁻¹) ^ k * ((M : ℝ)⁻¹) ^ k / 2 * r ^ k =
          ((M : ℝ)⁻¹) ^ k * ((r / M) ^ k / 2) := by
        rw [div_eq_mul_inv r, mul_pow]
        ring
      rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos two_pos,
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow hrM.le, ENNReal.ofReal_ofNat,
        ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
    rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet, hval]
    calc ((M⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * (ENNReal.ofReal (r / M) ^ k / 2)
        ≤ ((M⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k *
            Measure.hausdorffMeasure (k : ℝ) (A ∩ Metric.ball (a : Spatial k) (r / M)) := by
          gcongr
          exact hx.trans hcmp
      _ ≤ hausdorffP n k (φ '' T) := hlow
      _ ≤ hausdorffP n k (Metric.ball (φ a) r ∩ range φ) := measure_mono hT
  rw [ae_restrict_iff' hRm]
  refine ae_iff.2 (measure_mono_null ?_ hS)
  intro z hz
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hz
  obtain ⟨⟨a, rfl⟩, hz⟩ := hz
  refine ⟨a, ?_, rfl⟩
  intro ha
  exact hz (hgoodpt a ha)

/-- **Core density** for the Euclidean parameter space `B = ℝ^k`:
finiteness, upper `k`-growth and positive lower `k`-density almost everywhere for the
core's own Hausdorff measure. -/
theorem horizontalChart_coreDensity_proof {n k : ℕ} {A : Set (Spatial k)} (hA : IsCompact A)
    {φ : A → Space n} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hφ' : AntilipschitzWith L φ) :
    hausdorffP n k (Set.range φ) < ⊤ ∧
      (∃ U : ℝ, 0 ≤ U ∧ ∀ (q : Space n) (r : ℝ), 0 < r →
        (hausdorffP n k).restrict (Set.range φ) (Metric.ball q r) ≤
          ENNReal.ofReal (U * r ^ k)) ∧
      ∀ᵐ z ∂(hausdorffP n k).restrict (Set.range φ),
        HasPositiveLowerDensity ((hausdorffP n k).restrict (Set.range φ)) k z :=
  ⟨(horizontalChart_hausdorff_upper_proof hA hφ hφ').1,
    (horizontalChart_hausdorff_upper_proof hA hφ hφ').2,
    horizontalChart_ae_lowerDensity_proof hA hφ hφ'⟩

end ParabolicRectifiability
