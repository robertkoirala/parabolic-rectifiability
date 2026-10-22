import ParabolicRectifiability.Metric.Measure

/-!
# Density localization of trace pieces

`exists_density_trace_pieces_proof`: if `G` contains almost every point of a compact `K`, then
countably many compact `P_j ⊆ K ∩ G ∩ closedBall(x_j, ρ_j)`, `0 < ρ_j ≤ 1/64`, cover `K`
up to a null set, and every point of `P_j` has half ambient density in `K` at every
radius `r ≤ 64 ρ_j`.

Proof: ambient volume is uniformly locally doubling, so Lebesgue's density theorem
applies; the half-density levels are closed (upper semicontinuity of closed-ball masses
of a finite measure, and null spheres); a measurable null superset of `K \ G` is removed
and compact inner approximations are taken in the cells of a dense sequence.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-- Ambient volume is uniformly locally doubling, with constant `2^(m+2)`. -/
instance instIsUnifLocDoublingMeasureParabolicVolume (m : ℕ) :
    IsUnifLocDoublingMeasure (parabolicVolume m) := by
  refine ⟨⟨2 ^ (m + 2), ?_⟩⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) x
  rw [parabolicVolume_closedBall x (2 * ε) (by positivity), parabolicVolume_closedBall x ε hε.le,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_pow]
  apply le_of_eq
  push_cast
  ring

/-- Open and closed balls carry the same ambient mass of any set. -/
theorem parabolicVolume_inter_ball_eq_closedBall {m : ℕ} (K : Set (Space m)) (p : Space m)
    (r : ℝ) :
    parabolicVolume m (K ∩ Metric.ball p r) = parabolicVolume m (K ∩ Metric.closedBall p r) := by
  refine le_antisymm (measure_mono (inter_subset_inter_right _ Metric.ball_subset_closedBall)) ?_
  calc parabolicVolume m (K ∩ Metric.closedBall p r)
      ≤ parabolicVolume m ((K ∩ Metric.ball p r) ∪ Metric.sphere p r) := by
        apply measure_mono
        intro x hx
        have hx2 : x ∈ Metric.ball p r ∪ Metric.sphere p r := by
          rw [Metric.ball_union_sphere]
          exact hx.2
        rcases hx2 with h | h
        · exact Or.inl ⟨hx.1, h⟩
        · exact Or.inr h
    _ ≤ parabolicVolume m (K ∩ Metric.ball p r) + parabolicVolume m (Metric.sphere p r) :=
        measure_union_le _ _
    _ = parabolicVolume m (K ∩ Metric.ball p r) := by rw [parabolicVolume_sphere, add_zero]

/-- For a finite measure, closed-ball masses are upper semicontinuous in the center. -/
theorem isOpen_setOf_finiteMeasure_closedBall_lt {m : ℕ} (ν : Measure (Space m))
    [IsFiniteMeasure ν] (r : ℝ) (x : ℝ≥0∞) :
    IsOpen {z : Space m | ν (Metric.closedBall z r) < x} := by
  rw [Metric.isOpen_iff]
  intro z hz
  have hz' : ν (Metric.closedBall z r) < x := hz
  have hinter : (⋂ ε > r, Metric.closedBall z ε) = Metric.closedBall z r := by
    ext w
    simp only [mem_iInter, Metric.mem_closedBall]
    constructor
    · intro h
      exact le_of_forall_gt_imp_ge_of_dense fun ε hε => h ε hε
    · intro h ε hε
      exact h.trans hε.le
  rw [← hinter] at hz'
  have htend := tendsto_measure_biInter_gt (μ := ν) (s := fun ε => Metric.closedBall z ε)
    (a := r) (fun ε _ => measurableSet_closedBall.nullMeasurableSet)
    (fun i j _ hij => Metric.closedBall_subset_closedBall hij)
    ⟨r + 1, by linarith, measure_ne_top _ _⟩
  have hev : ∀ᶠ ε in 𝓝[>] r, ν (Metric.closedBall z ε) < x :=
    htend.eventually (p := fun y => y < x) (Iio_mem_nhds hz')
  obtain ⟨ε, hε', hεr'⟩ := (hev.and (self_mem_nhdsWithin : Ioi r ∈ 𝓝[>] r)).exists
  have hεr : r < ε := hεr'
  refine ⟨ε - r, sub_pos.mpr hεr, fun w hw => ?_⟩
  have hw' : dist w z < ε - r := hw
  show ν (Metric.closedBall w r) < x
  exact (measure_mono (Metric.closedBall_subset_closedBall' (by linarith))).trans_lt hε'

/-- The half-density level of `K` up to radius `R`. -/
def halfDensityLevel (m : ℕ) (K : Set (Space m)) (R : ℝ) : Set (Space m) :=
  {p | ∀ r : ℝ, 0 < r → r ≤ R →
    parabolicVolume m (Metric.ball p r) ≤ 2 * parabolicVolume m (K ∩ Metric.ball p r)}

theorem isClosed_setOf_le_two_mul_inter_closedBall {m : ℕ} {K : Set (Space m)}
    (hK : IsCompact K) (r : ℝ) (x : ℝ≥0∞) :
    IsClosed {p : Space m | x ≤ 2 * parabolicVolume m (K ∩ Metric.closedBall p r)} := by
  have hfin : IsFiniteMeasure ((parabolicVolume m).restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hset : {p : Space m | x ≤ 2 * parabolicVolume m (K ∩ Metric.closedBall p r)} =
      {p : Space m | (parabolicVolume m).restrict K (Metric.closedBall p r) < x / 2}ᶜ := by
    ext p
    have e : (parabolicVolume m).restrict K (Metric.closedBall p r) =
        parabolicVolume m (K ∩ Metric.closedBall p r) := by
      rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt, e]
    rw [ENNReal.div_le_iff_le_mul (Or.inl two_ne_zero) (Or.inl (by simp)), mul_comm]
  rw [hset]
  exact (isOpen_setOf_finiteMeasure_closedBall_lt _ r (x / 2)).isClosed_compl

/-- Half-density levels of a compact set are closed. -/
theorem isClosed_halfDensityLevel {m : ℕ} {K : Set (Space m)} (hK : IsCompact K) (R : ℝ) :
    IsClosed (halfDensityLevel m K R) := by
  have heq : halfDensityLevel m K R = ⋂ (r : ℝ) (_ : 0 < r) (_ : r ≤ R),
      {p : Space m | 2 * omega m * ENNReal.ofReal r ^ (m + 2) ≤
        2 * parabolicVolume m (K ∩ Metric.closedBall p r)} := by
    ext p
    simp only [halfDensityLevel, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h r hr hrR
      have h' := h r hr hrR
      rwa [parabolicVolume_ball p r hr, parabolicVolume_inter_ball_eq_closedBall] at h'
    · intro h r hr hrR
      have h' := h r hr hrR
      rwa [parabolicVolume_ball p r hr, parabolicVolume_inter_ball_eq_closedBall]
  rw [heq]
  exact isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_setOf_le_two_mul_inter_closedBall hK r _

/-- Lebesgue density for the doubling ambient volume: almost every point of `K` has half
density in `K` at all small radii. -/
theorem ae_half_density {m : ℕ} (K : Set (Space m)) (hK : IsCompact K) :
    ∀ᵐ p ∂parabolicVolume m, p ∈ K → ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      parabolicVolume m (Metric.ball p r) ≤ 2 * parabolicVolume m (K ∩ Metric.ball p r) := by
  have h := IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div (parabolicVolume m) K 1
  rw [ae_restrict_iff' hK.isClosed.measurableSet] at h
  filter_upwards [h] with p hp hpK
  have hevmem : ∀ᶠ j in 𝓝[>] (0 : ℝ), p ∈ Metric.closedBall ((fun _ => p) j) (1 * id j) := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    exact Metric.mem_closedBall_self (by simp only [one_mul, id]; exact hr.le)
  have ht := hp hpK (fun _ => p) id tendsto_id hevmem
  have hhalf : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.mpr ENNReal.one_lt_two
  have hev := ht.eventually (eventually_gt_nhds hhalf)
  obtain ⟨R, hR, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨R, hR, fun r hr hrR => ?_⟩
  have h1 : (2⁻¹ : ℝ≥0∞) < parabolicVolume m (K ∩ Metric.closedBall p r) /
      parabolicVolume m (Metric.closedBall p r) := hsub ⟨hr, hrR⟩
  have hb0 : parabolicVolume m (Metric.closedBall p r) ≠ 0 := by
    rw [parabolicVolume_closedBall p r hr.le]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (omega_pos m).ne')
      (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr).ne')
  have hbt : parabolicVolume m (Metric.closedBall p r) ≠ ⊤ :=
    (measure_closedBall_lt_top (μ := parabolicVolume m)).ne
  have h2 := (ENNReal.lt_div_iff_mul_lt (Or.inl hb0) (Or.inl hbt)).mp h1
  have h3 : parabolicVolume m (Metric.closedBall p r) ≤
      2 * parabolicVolume m (K ∩ Metric.closedBall p r) := by
    calc parabolicVolume m (Metric.closedBall p r)
        = 2 * (2⁻¹ * parabolicVolume m (Metric.closedBall p r)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero (by simp), one_mul]
      _ ≤ 2 * parabolicVolume m (K ∩ Metric.closedBall p r) := mul_le_mul_right h2.le 2
  rw [parabolicVolume_inter_ball_eq_closedBall, parabolicVolume_ball p r hr,
    ← parabolicVolume_closedBall p r hr.le]
  exact h3

theorem ae_mem_halfDensityLevel {m : ℕ} (K : Set (Space m)) (hK : IsCompact K) :
    ∀ᵐ p ∂parabolicVolume m, p ∈ K → ∃ N : ℕ, p ∈ halfDensityLevel m K (1 / ((N : ℝ) + 1)) := by
  filter_upwards [ae_half_density K hK] with p hp hpK
  obtain ⟨R, hR, hR'⟩ := hp hpK
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hR
  exact ⟨N, fun r hr hrN => hR' r hr (hrN.trans_lt hN)⟩

/-- **Density localization.** If `G` contains almost every point of the compact set `K`,
then countably many compact pieces `P_j ⊆ K ∩ G ∩ P̄(x_j, ρ_j)`, `0 < ρ_j ≤ 1/64`, cover
`K` up to a null set, and every point of `P_j` has half ambient density in `K` at every
radius `r ≤ 64 ρ_j`. -/
theorem exists_density_trace_pieces_proof (m : ℕ) (K G : Set (Space m)) (hK : IsCompact K)
    (hG : parabolicVolume m (K \ G) = 0) :
    ∃ (I : Set ℕ) (P : I → Set (Space m)) (x₀ : I → Space m) (ρ : I → ℝ),
      (∀ j, IsCompact (P j) ∧ P j ⊆ K ∩ G ∧ P j ⊆ Metric.closedBall (x₀ j) (ρ j) ∧
        0 < ρ j ∧ ρ j ≤ 1 / 64 ∧
        ∀ p ∈ P j, ∀ r : ℝ, 0 < r → r ≤ 64 * ρ j →
          parabolicVolume m (Metric.ball p r) ≤ 2 * parabolicVolume m (K ∩ Metric.ball p r)) ∧
      parabolicVolume m (K \ ⋃ j, P j) = 0 := by
  classical
  have : Nonempty (Space m) := ⟨point 0 0⟩
  obtain ⟨Z, hKGZ, hZm, hZ0⟩ := exists_measurable_superset_of_null hG
  -- the measurable cells: good points of `K` outside `Z`, in a small closed ball
  have hAm : ∀ N i : ℕ, MeasurableSet ((K ∩ halfDensityLevel m K (1 / ((N : ℝ) + 1)) ∩
      Metric.closedBall (TopologicalSpace.denseSeq (Space m) i) (1 / (64 * ((N : ℝ) + 1)))) \ Z) :=
    fun N i => ((hK.isClosed.measurableSet.inter
      (isClosed_halfDensityLevel hK _).measurableSet).inter measurableSet_closedBall).diff hZm
  have hAfin : ∀ N i : ℕ, parabolicVolume m ((K ∩ halfDensityLevel m K (1 / ((N : ℝ) + 1)) ∩
      Metric.closedBall (TopologicalSpace.denseSeq (Space m) i) (1 / (64 * ((N : ℝ) + 1)))) \ Z)
        ≠ ⊤ := fun N i =>
    ((measure_mono (sdiff_subset.trans inter_subset_right)).trans_lt
      (measure_closedBall_lt_top (μ := parabolicVolume m))).ne
  have hcpt : ∀ N i j : ℕ, ∃ P : Set (Space m),
      P ⊆ (K ∩ halfDensityLevel m K (1 / ((N : ℝ) + 1)) ∩
        Metric.closedBall (TopologicalSpace.denseSeq (Space m) i) (1 / (64 * ((N : ℝ) + 1)))) \ Z ∧
      IsCompact P ∧
      parabolicVolume m (((K ∩ halfDensityLevel m K (1 / ((N : ℝ) + 1)) ∩
        Metric.closedBall (TopologicalSpace.denseSeq (Space m) i) (1 / (64 * ((N : ℝ) + 1)))) \ Z)
          \ P) < (j : ℝ≥0∞)⁻¹ :=
    fun N i j => (hAm N i).exists_isCompact_sdiff_lt (hAfin N i)
      (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top j))
  choose Pc hPcA hPcK hPcε using hcpt
  refine ⟨univ, fun q => Pc (Nat.unpair q.1).1 (Nat.unpair (Nat.unpair q.1).2).1
      (Nat.unpair (Nat.unpair q.1).2).2,
    fun q => TopologicalSpace.denseSeq (Space m) (Nat.unpair (Nat.unpair q.1).2).1,
    fun q => 1 / (64 * (((Nat.unpair q.1).1 : ℕ) + 1 : ℝ)), fun q => ?_, ?_⟩
  · -- properties of each piece
    set N := (Nat.unpair q.1).1
    set i := (Nat.unpair (Nat.unpair q.1).2).1
    set j := (Nat.unpair (Nat.unpair q.1).2).2
    have hsub := hPcA N i j
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    refine ⟨hPcK N i j, fun p hp => ⟨(hsub hp).1.1.1, ?_⟩, fun p hp => (hsub hp).1.2,
      by positivity, ?_, fun p hp r hr hrR => (hsub hp).1.1.2 r hr ?_⟩
    · by_contra hpG
      exact (hsub hp).2 (hKGZ ⟨(hsub hp).1.1.1, hpG⟩)
    · exact one_div_le_one_div_of_le (by norm_num)
        (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
    · calc r ≤ 64 * (1 / (64 * ((N : ℝ) + 1))) := hrR
        _ = 1 / ((N : ℝ) + 1) := by
          rw [mul_one_div, ← div_div, div_self (by norm_num : (64 : ℝ) ≠ 0)]
  · -- the pieces cover `K` up to a null set
    have hbad : parabolicVolume m {p | p ∈ K ∧ ¬ ∃ N : ℕ,
        p ∈ halfDensityLevel m K (1 / ((N : ℝ) + 1))} = 0 := by
      have h := ae_iff.mp (ae_mem_halfDensityLevel K hK)
      refine measure_mono_null (fun p hp => ?_) h
      exact fun hcon => hp.2 (hcon hp.1)
    have hres : ∀ N i : ℕ, parabolicVolume m (((K ∩ halfDensityLevel m K (1 / ((N : ℝ) + 1)) ∩
        Metric.closedBall (TopologicalSpace.denseSeq (Space m) i) (1 / (64 * ((N : ℝ) + 1)))) \ Z)
          \ ⋃ j, Pc N i j) = 0 := by
      intro N i
      refine le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun j => ?_) zero_le
      exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion _ j))).trans (hPcε N i j).le
    refine measure_mono_null ?_ (measure_union_null (measure_union_null hbad hZ0)
      (measure_iUnion_null fun N => measure_iUnion_null fun i => hres N i))
    rintro p ⟨hpK, hpP⟩
    by_cases hpZ : p ∈ Z
    · exact Or.inl (Or.inr hpZ)
    by_cases hpD : ∃ N : ℕ, p ∈ halfDensityLevel m K (1 / ((N : ℝ) + 1))
    swap
    · exact Or.inl (Or.inl ⟨hpK, hpD⟩)
    obtain ⟨N, hpN⟩ := hpD
    have hρ : (0 : ℝ) < 1 / (64 * ((N : ℝ) + 1)) := by positivity
    obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq (Space m))
      p _ hρ
    right
    have hpA : p ∈ (K ∩ halfDensityLevel m K (1 / ((N : ℝ) + 1)) ∩
        Metric.closedBall (TopologicalSpace.denseSeq (Space m) i) (1 / (64 * ((N : ℝ) + 1)))) \ Z :=
      ⟨⟨⟨hpK, hpN⟩, le_of_lt hi⟩, hpZ⟩
    have hpnot : p ∉ ⋃ j, Pc N i j := by
      intro hpU
      obtain ⟨j, hj⟩ := mem_iUnion.mp hpU
      apply hpP
      refine mem_iUnion.mpr ⟨⟨Nat.pair N (Nat.pair i j), mem_univ _⟩, ?_⟩
      simp only [Nat.unpair_pair]
      exact hj
    exact mem_iUnion.mpr ⟨N, mem_iUnion.mpr ⟨i, ⟨hpA, hpnot⟩⟩⟩

end ParabolicRectifiability
