import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Boxes.Maximal

/-! # Overlap of the enlarged Whitney boxes

The open enlargements by the factor `3/2` of the maximal eligible boxes (`whitneyBoxes`): meeting enlargements have comparable scales and close centers,
at most `N_m` enlargements contain a point (volume packing of the disjoint original
boxes), every point off `F₀` has a neighborhood meeting finitely many, and no
enlargement meets `F₀`. This file assembles these facts as
`whitneyBoxes_enlarged_overlap_proof`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability

/-- Volume packing: the number of pairwise disjoint measurable sets of measure at least `c`
inside `B`, times `c`, is at most `μ B`. -/
theorem encard_mul_le_measure {X ι : Type*} [MeasurableSpace X] [Countable ι] (μ : Measure X)
    {f : ι → Set X} (hmeas : ∀ i, MeasurableSet (f i))
    (hdisj : Pairwise (Function.onFun Disjoint f))
    {S : Set ι} {c : ℝ≥0∞} (hc : ∀ i ∈ S, c ≤ μ (f i)) {B : Set X}
    (hB : ∀ i ∈ S, f i ⊆ B) : (S.encard : ℝ≥0∞) * c ≤ μ B := by
  rw [← ENNReal.tsum_set_const]
  calc ∑' _ : S, c ≤ ∑' i : S, μ (f i) := ENNReal.tsum_le_tsum fun i => hc i i.2
    _ = μ (⋃ i : S, f i) :=
        (measure_iUnion (μ := μ) (f := fun i : S => f i)
          (fun i j hij => hdisj (Subtype.coe_ne_coe.mpr hij)) fun i => hmeas i).symm
    _ ≤ μ B := measure_mono (Set.iUnion_subset fun i => hB i i.2)

/-- The overlap constant `2 ω_m (32 D_m)^(m+2)`. -/
def whitneyOverlapConst (m : ℕ) : ℝ≥0∞ :=
  2 * omega m * ENNReal.ofReal ((32 * whitneyD m) ^ (m + 2))

theorem whitneyOverlapConst_ne_top (m : ℕ) : whitneyOverlapConst m ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (omega_lt_top m).ne)
    ENNReal.ofReal_ne_top

namespace ParabolicDyadicBox

variable {m : ℕ} {F₀ : Set (Space m)}

/-- Points of the `3/2`-enlargement are within `D_m r_Q` of the center. -/
theorem dist_center_le_of_mem_enlarged {Q : ParabolicDyadicBox m} {z : Space m}
    (hz : z ∈ Q.enlarged (3 / 2)) : dist z Q.center ≤ whitneyD m * Q.radius := by
  simp only [enlarged, Set.mem_ofPred_eq] at hz
  obtain ⟨hx, ht⟩ := hz
  have hr := Q.radius_pos
  have hr2 : 0 < Q.radius ^ 2 := pow_pos hr 2
  exact dist_center_le_of_abs_le (fun i => (hx i).le.trans (by linarith))
    (ht.le.trans (by linarith))

/-- Meeting enlargements of Whitney boxes have comparable scales and close centers. -/
theorem enlarged_comparable {Q Q' : ParabolicDyadicBox m} (hQ : Q ∈ whitneyBoxes F₀)
    (hQ' : Q' ∈ whitneyBoxes F₀) {z : Space m} (hz : z ∈ Q.enlarged (3 / 2))
    (hz' : z ∈ Q'.enlarged (3 / 2)) :
    Q.radius ≤ 4 * Q'.radius ∧
      dist Q.center Q'.center ≤ 3 * whitneyD m * (Q.radius + Q'.radius) := by
  have hD := whitneyD_pos m
  have hDr := mul_pos hD Q.radius_pos
  have hDr' := mul_pos hD Q'.radius_pos
  have h1 : dist Q.center z ≤ whitneyD m * Q.radius := by
    rw [dist_comm]
    exact dist_center_le_of_mem_enlarged hz
  have h2 := dist_center_le_of_mem_enlarged hz'
  have hpp : dist Q.center Q'.center ≤ whitneyD m * Q.radius + whitneyD m * Q'.radius :=
    (dist_triangle _ z _).trans (by linarith)
  refine ⟨?_, by linarith⟩
  have hel : whitneyA m * Q.radius < Metric.infDist Q.center F₀ := hQ.1
  have hup := infDist_center_le hQ'
  have htri : Metric.infDist Q.center F₀ ≤
      Metric.infDist Q'.center F₀ + dist Q.center Q'.center :=
    Metric.infDist_le_infDist_add_dist
  rw [whitneyA_eq] at hel hup
  rw [← not_lt]
  intro hlt
  have h3 : whitneyD m * (4 * Q'.radius) < whitneyD m * Q.radius :=
    mul_lt_mul_of_pos_left hlt hD
  linarith

/-- No enlargement of an eligible box meets `F₀`. -/
theorem enlarged_inter_eq_empty {Q : ParabolicDyadicBox m} (hQ : IsWhitneyEligible F₀ Q) :
    Q.enlarged (3 / 2) ∩ F₀ = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨z, hz, hzF⟩
  have h1 : Metric.infDist Q.center F₀ ≤ Metric.infDist z F₀ + dist Q.center z :=
    Metric.infDist_le_infDist_add_dist
  rw [Metric.infDist_zero_of_mem hzF, dist_comm] at h1
  have h2 := dist_center_le_of_mem_enlarged hz
  have h3 : whitneyA m * Q.radius < Metric.infDist Q.center F₀ := hQ
  have hDr := mul_pos (whitneyD_pos m) Q.radius_pos
  rw [whitneyA_eq] at h3
  linarith

/-- Bounded overlap: at most `2 ω_m (32 D_m)^(m+2)` enlargements contain a point. -/
theorem encard_enlarged_mem_le (q : Space m) :
    ({Q : whitneyBoxes F₀ | q ∈ Q.1.enlarged (3 / 2)}.encard : ℝ≥0∞) ≤
      whitneyOverlapConst m := by
  rcases Set.eq_empty_or_nonempty {Q : whitneyBoxes F₀ | q ∈ Q.1.enlarged (3 / 2)} with
    h | ⟨Q₀, hQ₀⟩
  · rw [h, Set.encard_empty]
    simp
  have hρ := Q₀.1.radius_pos
  have hD := whitneyD_pos m
  have hQ₀' : q ∈ Q₀.1.enlarged (3 / 2) := hQ₀
  have hcomp : ∀ Q ∈ {Q : whitneyBoxes F₀ | q ∈ Q.1.enlarged (3 / 2)},
      Q.1.radius ≤ 4 * Q₀.1.radius ∧ Q₀.1.radius ≤ 4 * Q.1.radius :=
    fun Q (hQ : q ∈ Q.1.enlarged (3 / 2)) =>
      ⟨(enlarged_comparable Q.2 Q₀.2 hQ hQ₀').1, (enlarged_comparable Q₀.2 Q.2 hQ₀' hQ).1⟩
  have hc : ∀ Q ∈ {Q : whitneyBoxes F₀ | q ∈ Q.1.enlarged (3 / 2)},
      ENNReal.ofReal ((Q₀.1.radius / 4) ^ (m + 2)) ≤ parabolicVolume m Q.1.toSet := by
    intro Q hQ
    rw [Q.1.volume_toSet]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith) ?_ _)
    linarith [(hcomp Q hQ).2]
  have hB : ∀ Q ∈ {Q : whitneyBoxes F₀ | q ∈ Q.1.enlarged (3 / 2)},
      Q.1.toSet ⊆ Metric.closedBall q (8 * whitneyD m * Q₀.1.radius) := by
    rintro Q (hQ : q ∈ Q.1.enlarged (3 / 2)) w hw
    rw [Metric.mem_closedBall]
    have h1 := dist_center_le_of_mem hw
    have h2 := dist_center_le_of_mem_enlarged hQ
    have h4 : whitneyD m * Q.1.radius ≤ whitneyD m * (4 * Q₀.1.radius) :=
      mul_le_mul_of_nonneg_left (hcomp Q hQ).1 hD.le
    calc dist w q ≤ dist w Q.1.center + dist q Q.1.center := dist_triangle_right _ _ _
      _ ≤ 8 * whitneyD m * Q₀.1.radius := by linarith
  have hpack := encard_mul_le_measure (parabolicVolume m)
    (f := fun Q : whitneyBoxes F₀ => Q.1.toSet) (fun Q => Q.1.measurableSet_toSet)
    (fun Q Q' hne => whitneyBoxes_disjoint Q.2 Q'.2 fun h => hne (Subtype.ext h)) hc hB
  have h8 : 0 ≤ 8 * whitneyD m * Q₀.1.radius := by
    have := mul_pos hD hρ
    linarith
  have h32 : 0 ≤ (32 * whitneyD m) ^ (m + 2) := pow_nonneg (by linarith) _
  rw [parabolicVolume_closedBall _ _ h8] at hpack
  have hsplit : 2 * omega m * ENNReal.ofReal (8 * whitneyD m * Q₀.1.radius) ^ (m + 2) =
      whitneyOverlapConst m * ENNReal.ofReal ((Q₀.1.radius / 4) ^ (m + 2)) := by
    rw [whitneyOverlapConst, mul_assoc (2 * omega m), ← ENNReal.ofReal_mul h32,
      ← ENNReal.ofReal_pow h8, ← mul_pow]
    congr 3
    ring
  rw [hsplit] at hpack
  have hc0 : ENNReal.ofReal ((Q₀.1.radius / 4) ^ (m + 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos (by linarith) _)).ne'
  exact (ENNReal.mul_le_mul_iff_left hc0 ENNReal.ofReal_ne_top).mp hpack

/-- Local finiteness: a point off the closed nonempty set `F₀` has a neighborhood meeting
only finitely many enlargements. -/
theorem finite_enlarged_inter_ball (hF : IsClosed F₀) (hne : F₀.Nonempty) {q : Space m}
    (hq : q ∉ F₀) :
    ∃ U ∈ 𝓝 q, {Q : whitneyBoxes F₀ | (U ∩ Q.1.enlarged (3 / 2)).Nonempty}.Finite := by
  have hδ : 0 < Metric.infDist q F₀ := (hF.notMem_iff_infDist_pos hne).mp hq
  refine ⟨Metric.ball q (Metric.infDist q F₀ / 2), Metric.ball_mem_nhds q (by linarith), ?_⟩
  have hD := whitneyD_pos m
  have hK : 0 < 4 * whitneyA m + 8 * whitneyD m := by
    rw [whitneyA_eq]
    linarith
  have hprop : ∀ Q ∈ {Q : whitneyBoxes F₀ |
      (Metric.ball q (Metric.infDist q F₀ / 2) ∩ Q.1.enlarged (3 / 2)).Nonempty},
      Metric.infDist q F₀ / (4 * whitneyA m + 8 * whitneyD m) ≤ Q.1.radius ∧
      Q.1.toSet ⊆ Metric.closedBall q (3 * Metric.infDist q F₀) := by
    rintro Q ⟨z, hzU, hzQ⟩
    rw [Metric.mem_ball] at hzU
    have h1 : Metric.infDist q F₀ ≤ Metric.infDist z F₀ + dist q z :=
      Metric.infDist_le_infDist_add_dist
    have h2 : Metric.infDist z F₀ ≤ Metric.infDist q F₀ + dist z q :=
      Metric.infDist_le_infDist_add_dist
    have h3 : Metric.infDist z F₀ ≤ Metric.infDist Q.1.center F₀ + dist z Q.1.center :=
      Metric.infDist_le_infDist_add_dist
    have h4 : Metric.infDist Q.1.center F₀ ≤ Metric.infDist z F₀ + dist Q.1.center z :=
      Metric.infDist_le_infDist_add_dist
    have h5 := dist_center_le_of_mem_enlarged hzQ
    have h5' : dist Q.1.center z ≤ whitneyD m * Q.1.radius := by
      rw [dist_comm]
      exact h5
    have h6 := infDist_center_le Q.2
    have h7 : whitneyA m * Q.1.radius < Metric.infDist Q.1.center F₀ := Q.2.1
    rw [dist_comm] at h1
    have hDr := mul_pos hD Q.1.radius_pos
    rw [whitneyA_eq] at h6 h7 ⊢
    constructor
    · rw [div_le_iff₀ (by linarith)]
      linarith
    · intro w hw
      rw [Metric.mem_closedBall]
      have h8 := dist_center_le_of_mem hw
      calc dist w q ≤ dist w Q.1.center + dist Q.1.center z + dist z q :=
            dist_triangle4 _ _ _ _
        _ ≤ 3 * Metric.infDist q F₀ := by linarith
  have hc0 : ENNReal.ofReal ((Metric.infDist q F₀ / (4 * whitneyA m + 8 * whitneyD m)) ^ (m + 2))
      ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos (div_pos hδ hK) _)).ne'
  have hc : ∀ Q ∈ {Q : whitneyBoxes F₀ |
      (Metric.ball q (Metric.infDist q F₀ / 2) ∩ Q.1.enlarged (3 / 2)).Nonempty},
      ENNReal.ofReal ((Metric.infDist q F₀ / (4 * whitneyA m + 8 * whitneyD m)) ^ (m + 2)) ≤
        parabolicVolume m Q.1.toSet := by
    intro Q hQ
    rw [Q.1.volume_toSet]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (div_nonneg hδ.le hK.le) (hprop Q hQ).1 _)
  have hB : ∀ Q ∈ {Q : whitneyBoxes F₀ |
      (Metric.ball q (Metric.infDist q F₀ / 2) ∩ Q.1.enlarged (3 / 2)).Nonempty},
      Q.1.toSet ⊆ Metric.closedBall q (3 * Metric.infDist q F₀) :=
    fun Q hQ => (hprop Q hQ).2
  have hpack := encard_mul_le_measure (parabolicVolume m)
    (f := fun Q : whitneyBoxes F₀ => Q.1.toSet) (fun Q => Q.1.measurableSet_toSet)
    (fun Q Q' hne => whitneyBoxes_disjoint Q.2 Q'.2 fun h => hne (Subtype.ext h)) hc hB
  rw [parabolicVolume_closedBall q (3 * Metric.infDist q F₀) (by linarith)] at hpack
  refine Set.encard_ne_top_iff.mp (ENat.toENNReal_ne_top.mp fun htop => ?_)
  rw [htop, ENNReal.top_mul hc0, top_le_iff] at hpack
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (omega_lt_top m).ne)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hpack

end ParabolicDyadicBox

open ParabolicDyadicBox in
/-- **Overlap of the enlarged Whitney boxes**: comparable scales, bounded overlap, local
finiteness and avoidance of `F₀` for the `3/2`-enlargements. -/
theorem whitneyBoxes_enlarged_overlap_proof (m : ℕ) :
    ∃ N : ℕ, ∀ F₀ : Set (Space m), IsCompact F₀ → F₀.Nonempty →
      (∀ Q Q' : whitneyBoxes F₀, (Q.1.enlarged (3 / 2) ∩ Q'.1.enlarged (3 / 2)).Nonempty →
        Q.1.radius ≤ 4 * Q'.1.radius ∧
          dist Q.1.center Q'.1.center ≤ 3 * whitneyD m * (Q.1.radius + Q'.1.radius)) ∧
      (∀ q : Space m, {Q : whitneyBoxes F₀ | q ∈ Q.1.enlarged (3 / 2)}.encard ≤ N) ∧
      (∀ q ∉ F₀, ∃ U ∈ 𝓝 q,
        {Q : whitneyBoxes F₀ | (U ∩ Q.1.enlarged (3 / 2)).Nonempty}.Finite) ∧
      (∀ Q : whitneyBoxes F₀, Q.1.enlarged (3 / 2) ∩ F₀ = ∅) := by
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (whitneyOverlapConst_ne_top m)
  refine ⟨N, fun F₀ hF₀ hne => ⟨?_, fun q => ?_, fun q hq => ?_, fun Q => ?_⟩⟩
  · rintro Q Q' ⟨z, hz, hz'⟩
    exact enlarged_comparable Q.2 Q'.2 hz hz'
  · exact ENat.toENNReal_le_natCast.mp ((encard_enlarged_mem_le q).trans hN.le)
  · exact finite_enlarged_inter_ball hF₀.isClosed hne hq
  · exact enlarged_inter_eq_empty Q.2.1

end ParabolicRectifiability
