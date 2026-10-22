import ParabolicRectifiability.Foundations.Statements.Ambient
import ParabolicRectifiability.Decomposition.AmbientEndpoint

/-! # The ambient local core at every cylinder `P(q,R)`

`f3_ambient_local_core_bounds_proof : AmbientLocalCoreStatement` has exactly the type of
`ambient_local_core_bounds`.

Route: direct. The volume lemmas used by `ambientRetainedDecomposition_proof` are stated
for an arbitrary radius (`hausdorffP_inter_ball_le_of_isometry`,
`card_le_of_separated_of_isometry`, `sum_radius_pow_le_of_disjoint_balls`), so they apply at
scale `R` with the identity isometry of `Space n` and the measure `parabolicVolume n`
(ball volume `2 ω_n r^{n+2}`, `H_P^{n+2} ≤ c_n L^{n+1}`). Only the tube bound is reproved,
since the existing version is normalized to `P̄(c,1)`: at `k = n + 2` the `r`-neighbourhood of
`K ⊆ P̄(q,R)` lies in `P(q,2R)` for `r ≤ R`. The vertical cover is the zero function on the full
spatial direction, which is general regular because the normal space is zero (the
half-derivative condition is vacuous); its Lipschitz and BMO data are read off
`isRegularVerticalFunction_zero`.

The constant `f3_amb5_constant n = A 4^{n+2} + 6^{n+2} + 2^{n+2} + 2 ω_n 2^{n+2}`, with
`A = c_n · 2 ω_n`, depends only on `n`; it is chosen before `μ`, `q`, `R`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- The dimensional constant of the ambient local core. -/
def f3_amb5_constant (n : ℕ) : ℝ :=
  (verticalHausdorffConstant n * (2 * omega n)).toReal * 4 ^ (n + 2) + 6 ^ (n + 2) +
    2 ^ (n + 2) + 2 * (omega n).toReal * 2 ^ (n + 2)

theorem f3_amb5_constant_pos (n : ℕ) : 0 < f3_amb5_constant n := by
  unfold f3_amb5_constant
  have := (omega n).toReal_nonneg
  have := (verticalHausdorffConstant n * (2 * omega n)).toReal_nonneg
  positivity

/-- Disjoint balls of radii at most `s` centred in `P(q,s)` lie in `P(q,2s)`, so the sum of
their `(n+2)`-th powers is at most `2^{n+2} s^{n+2}`. -/
theorem f3_amb5_finset_packing {n : ℕ} {ι : Type*} (t : Finset ι) (z : ι → Space n)
    (r : ι → ℝ) (q : Space n) {s : ℝ} (hs : 0 < s) (hz : ∀ i ∈ t, z i ∈ Metric.ball q s)
    (hr : ∀ i ∈ t, 0 < r i ∧ r i ≤ s)
    (hd : (t : Set ι).PairwiseDisjoint fun i => Metric.ball (z i) (r i)) :
    ∑ i ∈ t, ENNReal.ofReal (r i) ^ (n + 2) ≤ ENNReal.ofReal (2 ^ (n + 2) * s ^ (n + 2)) := by
  have hv0 : 2 * omega n ≠ 0 := (ENNReal.mul_pos (by norm_num) (omega_pos n).ne').ne'
  have hvfin : 2 * omega n ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (omega_lt_top n).ne
  refine (sum_radius_pow_le_of_disjoint_balls (ν := parabolicVolume n) hv0 hvfin
    (fun y r hr => parabolicVolume_ball y r hr) t z r (fun i hi => (hr i hi).1) hd q
    (by positivity : (0 : ℝ) < 2 * s) ?_).trans_eq ?_
  · intro i hi
    apply Metric.ball_subset_ball'
    have := Metric.mem_ball.mp (hz i hi)
    linarith [(hr i hi).2]
  · rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * s), mul_pow]

/-- The full vertical graph of the zero function is general regular at every nonnegative
tolerance and covers every set. -/
theorem f3_amb5_generalVerticalCover {n : ℕ} (K : Set (Space n)) {ε : ℝ} (hε : 0 ≤ ε) :
    HasGeneralRegularVerticalGraphCover (n + 2) K ε := by
  have hrank : Module.finrank ℝ (⊤ : Submodule ℝ (Spatial n)) + 2 = n + 2 := by
    rw [finrank_top, finrank_euclideanSpace_fin]
  obtain ⟨-, -, g, L, B, -, -, hL, hB, -, hle⟩ :=
    isRegularVerticalFunction_zero (⊤ : Submodule ℝ (Spatial n)) hε
  have h0 : Module.finrank ℝ (⊤ : Submodule ℝ (Spatial n)).orthogonal = 0 := by
    rw [Submodule.top_orthogonal_eq_bot]
    exact finrank_bot ℝ (Spatial n)
  have hreg : IsGeneralRegularVerticalFunction (⊤ : Submodule ℝ (Spatial n))
      (fun _ => 0) ε :=
    ⟨g, L, B, hL, hB, fun i => absurd (i.2.trans_eq h0) (Nat.not_lt_zero _), hle⟩
  let G : GeneralRegularVerticalGraph n (n + 2) ε :=
    { vertical_dimension := by omega
      direction := ⊤
      rank_eq := hrank
      offset := 0
      function := fun _ => 0
      regular := hreg }
  have hcov : K ⊆ G.image := by
    intro z _
    refine ⟨(⟨z.1, Submodule.mem_top⟩, z.2), ?_⟩
    simp [G, GeneralRegularVerticalGraph.map]
  exact ⟨{0}, fun _ => G, measure_mono_null
    (fun x hx => (hx.2 (mem_iUnion.mpr ⟨⟨0, rfl⟩, hcov hx.1⟩)).elim) measure_empty⟩

/-- At `k = n + 2` the `r`-neighbourhood of `K ⊆ P̄(q,R)` lies in `P(q,2R)` for `r ≤ R`. -/
theorem f3_amb5_thickening_subset {n : ℕ} {K : Set (Space n)} {q : Space n} {R r : ℝ}
    (hK : K ⊆ Metric.closedBall q R) (hr : 0 < r) (hrR : r ≤ R) :
    {z | Metric.infEDist z K < ENNReal.ofReal r} ⊆ Metric.ball q (2 * R) := by
  intro z hz
  obtain ⟨w, hwK, hzw⟩ := Metric.infEDist_lt_iff.mp hz
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr] at hzw
  rw [Metric.mem_ball]
  linarith [dist_triangle z w q, Metric.mem_closedBall.mp (hK hwK)]

/-- The support bundle at `k = n + 2` for any closed `K ⊆ P̄(q,R)`, horizontal support `∅`. -/
theorem f3_amb5_supportBounds {n : ℕ} {K : Set (Space n)} {q : Space n} {R : ℝ}
    (hKc : IsClosed K) (hK : K ⊆ Metric.closedBall q R) (hR : 0 < R) :
    HasRegularSupportBounds (n + 2) (f3_amb5_constant n) q R ∅ K := by
  have hv0 : 2 * omega n ≠ 0 := (ENNReal.mul_pos (by norm_num) (omega_pos n).ne').ne'
  have hvfin : 2 * omega n ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (omega_lt_top n).ne
  have hball : ∀ (y : Space n) r, 0 < r →
      parabolicVolume n (Metric.ball y r) = 2 * omega n * ENNReal.ofReal r ^ (n + 2) :=
    fun y r hr => parabolicVolume_ball y r hr
  have hH : ∀ E : Set (Space n), Measure.hausdorffMeasure ((n + 2 : ℕ) : ℝ) E ≤
      verticalHausdorffConstant n * parabolicVolume n E :=
    fun E => (parabolic_hausdorff_comparison n E).2
  have hhfin := (verticalHausdorffConstant_lt_top n).ne
  have hKι : K ⊆ range (id : Space n → Space n) := fun z _ => ⟨z, rfl⟩
  set A := (verticalHausdorffConstant n * (2 * omega n)).toReal with hA
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hw0 : 0 ≤ (omega n).toReal := ENNReal.toReal_nonneg
  have hC : f3_amb5_constant n =
      A * 4 ^ (n + 2) + 6 ^ (n + 2) + 2 ^ (n + 2) + 2 * (omega n).toReal * 2 ^ (n + 2) := rfl
  have h24 : (2 : ℝ) ^ (n + 2) ≤ 4 ^ (n + 2) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h6 : (0 : ℝ) ≤ 6 ^ (n + 2) := by positivity
  have h2 : (0 : ℝ) ≤ 2 ^ (n + 2) := by positivity
  have hc1 : A * 4 ^ (n + 2) ≤ f3_amb5_constant n := by
    rw [hC]; have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hw0) h2; linarith
  have hc2 : A * 2 ^ (n + 2) ≤ f3_amb5_constant n :=
    (mul_le_mul_of_nonneg_left h24 hA0).trans hc1
  have hc3 : (6 : ℝ) ^ (n + 2) ≤ f3_amb5_constant n := by
    rw [hC]; have := mul_nonneg hA0 (by positivity : (0 : ℝ) ≤ 4 ^ (n + 2))
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hw0) h2; linarith
  have hc4 : (2 : ℝ) ^ (n + 2) ≤ f3_amb5_constant n := by
    rw [hC]; have := mul_nonneg hA0 (by positivity : (0 : ℝ) ≤ 4 ^ (n + 2))
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hw0) h2; linarith
  have hc5 : 2 * (omega n).toReal * 2 ^ (n + 2) ≤ f3_amb5_constant n := by
    rw [hC]; have := mul_nonneg hA0 (by positivity : (0 : ℝ) ≤ 4 ^ (n + 2)); linarith
  have hloc : ∀ q' s, 0 < s →
      hausdorffP n (n + 2) (K ∩ Metric.ball q' s) ≤ ENNReal.ofReal (A * 2 ^ (n + 2) * s ^ (n + 2)) :=
    fun q' s hs => hausdorffP_inter_ball_le_of_isometry (K := K) hvfin hball hH hhfin
      isometry_id hKι q' hs
  exact
    { horizontal_compact := isCompact_empty
      vertical_compact := (isCompact_closedBall q R).of_isClosed_subset hKc hK
      horizontal_subset := empty_subset _
      vertical_subset := hK
      horizontal_unavailable := fun _ => rfl
      vertical_unavailable := fun h => absurd ⟨by omega, le_rfl⟩ h
      horizontal_graphs := fun ε _ => ⟨∅, fun i => absurd i.2 (Set.notMem_empty _), by simp⟩
      vertical_graphs := fun ε hε => f3_amb5_generalVerticalCover K hε.le
      hausdorff_total := by
        rw [empty_union]
        have hsub : K ⊆ K ∩ Metric.ball q (2 * R) := fun z hz =>
          ⟨hz, Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp (hK hz))
            (by linarith))⟩
        refine (measure_mono hsub).trans ((hloc q (2 * R) (by positivity)).trans ?_)
        apply ENNReal.ofReal_le_ofReal
        have h4 : (4 : ℝ) ^ (n + 2) = 2 ^ (n + 2) * 2 ^ (n + 2) := by
          rw [← mul_pow]; norm_num
        calc A * 2 ^ (n + 2) * (2 * R) ^ (n + 2) = A * 4 ^ (n + 2) * R ^ (n + 2) := by
              rw [mul_pow, h4]; ring
          _ ≤ f3_amb5_constant n * R ^ (n + 2) :=
              mul_le_mul_of_nonneg_right hc1 (by positivity)
      hausdorff_local := fun q' s hs _ => by
        rw [empty_union]
        exact (hloc q' s hs).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc2 (by positivity)))
      separated := fun q' s r hs _ hr hrs F hF hsep => by
        rw [empty_union] at hF
        exact (card_le_of_separated_of_isometry hv0 hvfin hball isometry_id hKι q' hr hrs F hF
          hsep).trans (mul_le_mul_of_nonneg_right hc3 (by positivity))
      minkowski := fun r hr hrR => by
        rw [empty_union, Nat.sub_self, pow_zero, mul_one]
        refine (measure_mono (f3_amb5_thickening_subset hK hr hrR)).trans ?_
        rw [hball q (2 * R) (by positivity),
          ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * R),
          ← ENNReal.ofReal_toReal hvfin, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        apply ENNReal.ofReal_le_ofReal
        have hv : (2 * omega n).toReal = 2 * (omega n).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
        calc (2 * omega n).toReal * (2 * R) ^ (n + 2)
            = 2 * (omega n).toReal * 2 ^ (n + 2) * R ^ (n + 2) := by
              rw [hv, mul_pow]; ring
          _ ≤ f3_amb5_constant n * R ^ (n + 2) :=
              mul_le_mul_of_nonneg_right hc5 (by positivity)
      finite_packing := fun q' s hs _ l z r hz hr hd =>
        (f3_amb5_finset_packing Finset.univ z r q' hs (fun i _ => (hz i).2) (fun i _ => hr i)
          (fun i _ j _ hij => hd i j hij)).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc4 (by positivity)))
      countable_packing := fun q' s hs _ I z r hz hr hd => by
        rw [ENNReal.tsum_eq_iSup_sum]
        exact iSup_le fun t =>
          (f3_amb5_finset_packing t z r q' hs (fun i _ => (hz i).2) (fun i _ => hr i)
            (fun i _ j _ hij => hd i j hij)).trans
            (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc4 (by positivity))) }

/-- **The ambient local core**: exactly `AmbientLocalCoreStatement`, the type of
`ambient_local_core_bounds`. -/
theorem f3_ambient_local_core_bounds_proof : AmbientLocalCoreStatement := by
  intro n _hn
  refine ⟨f3_amb5_constant n, f3_amb5_constant_pos n, fun μ _ _ q R hR => ⟨?_, ?_, ?_⟩⟩
  · rw [add_comm, Measure.restrict_add_restrict_compl measurableSet_ball]
  · rw [Measure.restrict_apply measurableSet_ball, inter_compl_self, measure_empty]
  · exact f3_amb5_supportBounds Measure.isClosed_support
      (support_restrict_subset_of_isClosed μ Metric.ball_subset_closedBall
        Metric.isClosed_closedBall) hR

end ParabolicRectifiability.Foundations
