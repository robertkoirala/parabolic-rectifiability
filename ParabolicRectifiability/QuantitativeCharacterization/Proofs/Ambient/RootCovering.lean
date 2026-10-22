import ParabolicRectifiability.QuantitativeCharacterization.Coverings

/-! # The ambient root covering

Proof of `ambient_root_covering` (the covering part of the ambient case `k = n + 2`).

At `k = n + 2` and a support-centred root `P(a,R)`, the covering `damb_covering` has the single
index `0`, the ambient reference `Reference.ambient rfl` (carrier `univ`, vertical type), centre
`a`, radius `2R`, empty bad set and the whole tested cylinder `rootPairs μ a R` as its only scale
set. Its multiplicity is `1` on `P(a,R) ⊆ P(a,2R)`, so at level `0` the residual is `μ⌊P(a,R)`
and at every level `N ≥ 1` the vertical approximant is `μ⌊P(a,R)` and the residual vanishes.
No growth, energy or absolute continuity hypothesis is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- The tested cylinder `(P(a,R) ∩ supp μ) × (0,R)` is Borel. -/
theorem damb_measurableSet_rootPairs {n : ℕ} (μ : Measure (Space n)) (a : Space n) (R : ℝ) :
    MeasurableSet (rootPairs μ a R) :=
  (measurableSet_ball.inter (Measure.isClosed_support (μ := μ)).measurableSet).prod
    measurableSet_Ioo

/-- A sum over the one-point index set `{0}` is its single term. -/
theorem damb_tsum_singleton (f : ({0} : Set ℕ) → ℝ≥0∞) :
    ∑' i, f i = f ⟨0, Set.mem_singleton 0⟩ :=
  tsum_eq_single _ fun i hi =>
    absurd (Subtype.ext (Set.mem_singleton_iff.mp i.2)) hi

/-- The single-ball ambient covering of the root `P(a,R)`: the model ball `P(a,2R)` with the
ambient reference `(X, L^{n+1})`, empty bad set and the whole tested cylinder as its scale set. -/
def damb_covering {n : ℕ} (μ : Measure (Space n)) (a : Space n) (ha : a ∈ μ.support) (R : ℝ)
    (hR : 0 < R) : RegularMixedCovering (n + 2) ((2 : ℝ) ^ (n + 2)) 2 μ a R where
  index := {0}
  reference := fun _ => Reference.ambient rfl
  center := fun _ => a
  radius := fun _ => 2 * R
  badSet := ∅
  scaleSet := fun _ => rootPairs μ a R
  center_mem_support := fun _ => ha
  radius_pos := fun _ => by positivity
  ball_subset := fun _ => Subset.rfl
  ball_meets_carrier := fun _ => ⟨a, Metric.mem_ball_self (by positivity), Set.mem_univ a⟩
  root_packing := by
    rw [damb_tsum_singleton]
    show ENNReal.ofReal (2 * R) ^ (n + 2) ≤ ENNReal.ofReal ((2 : ℝ) ^ (n + 2) * R ^ (n + 2))
    rw [← ENNReal.ofReal_pow (by positivity), mul_pow]
  local_packing := fun b s hs => by
    rw [damb_tsum_singleton]
    split_ifs with h
    · have h2 : 2 * R ≤ s := h.2
      show ENNReal.ofReal (2 * R) ^ (n + 2) ≤ ENNReal.ofReal ((2 : ℝ) ^ (n + 2) * s ^ (n + 2))
      rw [← ENNReal.ofReal_pow (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (2 * R) ^ (n + 2) ≤ s ^ (n + 2) := by gcongr
        _ ≤ (2 : ℝ) ^ (n + 2) * s ^ (n + 2) :=
          le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    · exact zero_le
  measurable_badSet := MeasurableSet.empty
  measurable_scaleSet := fun _ => damb_measurableSet_rootPairs μ a R
  badSet_subset := empty_subset _
  scaleSet_subset := fun _ => Subset.rfl
  bad_inter_scale_null := fun _ => measure_mono_null (fun _ hp => hp.1) measure_empty
  scale_inter_scale_null := fun i j hij =>
    (hij (Subtype.ext ((Set.mem_singleton_iff.mp i.2).trans
      (Set.mem_singleton_iff.mp j.2).symm))).elim
  cover_null := measure_mono_null
    (fun _ hp => (hp.2 (Or.inr (Set.mem_iUnion.mpr ⟨⟨0, Set.mem_singleton 0⟩, hp.1⟩))).elim)
    measure_empty
  scaleSet_cover := fun _ p hp => by
    have hp' : p.1 ∈ Metric.ball a R ∩ μ.support ∧ p.2 ∈ Ioo 0 R := hp
    obtain ⟨⟨hball, -⟩, hpos, hlt⟩ := hp'
    have h2 : p.1 ∈ Metric.ball a (2 * R) := Metric.ball_subset_ball (by linarith) hball
    have hdist : (2 : ℝ)⁻¹ * Metric.infDist p.1 (Set.univ : Set (Space n)) ≤ p.2 := by
      rw [Metric.infDist_zero_of_mem (Set.mem_univ _), mul_zero]
      exact hpos.le
    have hlt2 : p.2 < 2 * R := by linarith
    exact ⟨⟨hball, h2⟩, hdist, hlt2⟩
  bad_bound := measure_empty.trans_le (zero_le)

/-- The multiplicity of `damb_covering` is `1` on the root `P(a,R)`. -/
theorem damb_multiplicity_eq_one {n : ℕ} {μ : Measure (Space n)} {a : Space n}
    (ha : a ∈ μ.support) {R : ℝ} (hR : 0 < R) {z : Space n} (hz : z ∈ Metric.ball a R) :
    (damb_covering μ a ha R hR).multiplicity z = 1 := by
  rw [RegularMixedCovering.multiplicity, Set.encard_eq_one]
  refine ⟨⟨0, Set.mem_singleton 0⟩, ?_⟩
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro _
    exact Subtype.ext (Set.mem_singleton_iff.mp i.2)
  · intro _
    have h2 : z ∈ Metric.ball a (2 * R) := Metric.ball_subset_ball (by linarith) hz
    exact h2

theorem damb_le_of_one_le {n : ℕ} {μ : Measure (Space n)} {a : Space n}
    (ha : a ∈ μ.support) {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : 1 ≤ N) :
    Metric.ball a R ∩ {z | (damb_covering μ a ha R hR).multiplicity z ≤ (N : ℕ∞)} =
      Metric.ball a R :=
  Set.inter_eq_left.mpr fun z hz => by
    show (damb_covering μ a ha R hR).multiplicity z ≤ (N : ℕ∞)
    rw [damb_multiplicity_eq_one ha hR hz]
    exact_mod_cast hN

theorem damb_lt_of_one_le {n : ℕ} {μ : Measure (Space n)} {a : Space n}
    (ha : a ∈ μ.support) {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : 1 ≤ N) :
    Metric.ball a R ∩ {z | (N : ℕ∞) < (damb_covering μ a ha R hR).multiplicity z} = ∅ := by
  refine Set.subset_empty_iff.mp fun z hz => ?_
  have h : (N : ℕ∞) < (damb_covering μ a ha R hR).multiplicity z := hz.2
  rw [damb_multiplicity_eq_one ha hR hz.1] at h
  have h1 : (1 : ℕ∞) ≤ (N : ℕ∞) := by exact_mod_cast hN
  exact absurd h (not_lt.mpr h1)

theorem damb_le_of_eq_zero {n : ℕ} {μ : Measure (Space n)} {a : Space n}
    (ha : a ∈ μ.support) {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : N = 0) :
    Metric.ball a R ∩ {z | (damb_covering μ a ha R hR).multiplicity z ≤ (N : ℕ∞)} = ∅ := by
  refine Set.subset_empty_iff.mp fun z hz => ?_
  have h : (damb_covering μ a ha R hR).multiplicity z ≤ (N : ℕ∞) := hz.2
  rw [damb_multiplicity_eq_one ha hR hz.1, hN, Nat.cast_zero] at h
  exact absurd h (not_le.mpr zero_lt_one)

theorem damb_lt_of_eq_zero {n : ℕ} {μ : Measure (Space n)} {a : Space n}
    (ha : a ∈ μ.support) {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : N = 0) :
    Metric.ball a R ∩ {z | (N : ℕ∞) < (damb_covering μ a ha R hR).multiplicity z} =
      Metric.ball a R :=
  Set.inter_eq_left.mpr fun z hz => by
    show (N : ℕ∞) < (damb_covering μ a ha R hR).multiplicity z
    rw [damb_multiplicity_eq_one ha hR hz, hN, Nat.cast_zero]
    exact zero_lt_one

/-- **The ambient root covering**: the type of `ambient_root_covering`. -/
theorem damb_ambient_root_covering_proof :
    ∀ n : ℕ, 1 ≤ n →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R →
      ∃ 𝒞 : RegularMixedCovering (n + 2) ((2 : ℝ) ^ (n + 2)) 2 μ a R,
        𝒞.index = {0} ∧ (∀ i, 𝒞.center i = a ∧ 𝒞.radius i = 2 * R) ∧
        𝒞.IsTypedTraceSplit ∅ (Metric.ball a R) ∧
        𝒞.MeasureIdentity ∅ (Metric.ball a R) ∧
        (∀ c : ℝ, 𝒞.RelativeTail c) ∧
        ∀ N : ℕ, 1 ≤ N →
          𝒞.approximant (Metric.ball a R) N = μ.restrict (Metric.ball a R) ∧
            𝒞.approximant ∅ N = 0 ∧ 𝒞.residual N = 0 := by
  intro n _ μ _ _ a ha R hR
  refine ⟨damb_covering μ a ha R hR, rfl, fun _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · -- the typed trace split `F_H = ∅`, `F_V = P(a,R)`
    exact
      { measurable_horizontal := MeasurableSet.empty
        measurable_vertical := measurableSet_ball
        disjoint := Set.empty_disjoint _
        horizontal_subset_root := empty_subset _
        vertical_subset_root := Subset.rfl
        horizontal_subset_trace := empty_subset _
        vertical_subset_trace := fun z hz => by
          simp only [RegularMixedCovering.typedTrace, Set.mem_iUnion]
          have h2 : z ∈ Metric.ball a (2 * R) := Metric.ball_subset_ball (by linarith) hz
          exact ⟨⟨0, Set.mem_singleton 0⟩, rfl, h2, Set.mem_univ z⟩
        null_remainder := by rw [Set.empty_union, Set.sdiff_self, measure_empty] }
  · -- the measure identity at every level
    intro N
    simp only [RegularMixedCovering.approximant, RegularMixedCovering.residual]
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · rw [damb_le_of_eq_zero ha hR h0, damb_lt_of_eq_zero ha hR h0, Set.empty_inter,
        Measure.restrict_empty, zero_add, zero_add]
    · rw [damb_le_of_one_le ha hR hN, damb_lt_of_one_le ha hR hN, Set.empty_inter,
        Measure.restrict_empty, zero_add, add_zero]
  · -- the relative tail for every tail constant
    intro c N
    simp only [RegularMixedCovering.residual]
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · rw [damb_lt_of_eq_zero ha hR h0, Measure.restrict_apply_self, h0, Nat.cast_zero, neg_zero,
        zero_div, Real.exp_zero, mul_one]
      exact le_mul_of_one_le_left (zero_le) (ENNReal.one_le_ofReal.mpr one_le_two)
    · rw [damb_lt_of_one_le ha hR hN, Measure.restrict_empty, Measure.coe_zero, Pi.zero_apply]
      exact zero_le
  · -- the approximants for `N ≥ 1`
    intro N hN
    simp only [RegularMixedCovering.approximant, RegularMixedCovering.residual]
    rw [damb_le_of_one_le ha hR hN, damb_lt_of_one_le ha hR hN, Set.empty_inter,
      Measure.restrict_empty]
    exact ⟨rfl, rfl, rfl⟩

end ParabolicRectifiability.QuantitativeCharacterization
