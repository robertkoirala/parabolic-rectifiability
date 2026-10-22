import ParabolicRectifiability.Analysis.TraceExtension.Whitney.BoxCutoff
import ParabolicRectifiability.Analysis.SmoothCutoff.NormalizedWeights

/-!
# The smooth Whitney partition

For the actual
Whitney boxes `whitneyBoxes F₀` let `θ_Q` be the product cutoff of `Q`
(`WhitneyCutoff.boxCutoff`), `Θ = Σ_Q θ_Q`, and

    φ_Q = θ_Q · f(Θ),

with the normalizer `f(s) = χ(s)/s` of `SmoothCutoff.Profile`. Off `F₀` the boxes
cover, `θ_Q = 1` on `Q`, so `Θ ≥ 1` and `φ_Q = θ_Q / Θ`; on `F₀` every `θ_Q`
vanishes near the point. Local finiteness of the enlarged boxes turns `Θ` near
every point of a support into a finite sum, so near such a point `φ_Q` is the
finite normalized weight of `SmoothCutoff.NormalizedWeights`, and the abstract
quotient-rule bound there applies with the comparable scales `r_Q ≤ 4 r_{Q'}` of
overlapping enlargements and at most `N` active cutoffs.

The overlap facts and the upper center distance of the Whitney boxes are taken as
hypotheses: the final theorem `exists_whitneyBoxes_partition_proof` assumes the
statements `exists_whitneyBoxes_data` and `whitneyBoxes_enlarged_overlap`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace ParabolicRectifiability

namespace WhitneyCutoff

open SmoothCutoff

variable {m : ℕ} {F₀ : Set (Space m)}

/-- The total mass `Θ = Σ_Q θ_Q` of the cutoffs of the Whitney boxes. -/
def whitneyMass (F₀ : Set (Space m)) (p : Coordinates m) : ℝ :=
  ∑' Q : whitneyBoxes F₀, boxCutoff Q.1 p

/-- The normalized weight `θ_Q f(Θ)` on ordinary coordinates. -/
def whitneyWeightCoord (F₀ : Set (Space m)) (Q : whitneyBoxes F₀) (p : Coordinates m) : ℝ :=
  boxCutoff Q.1 p * normalizer (whitneyMass F₀ p)

/-- The normalized weight as a function on parabolic space. -/
def whitneyWeight (F₀ : Set (Space m)) (Q : whitneyBoxes F₀) (z : Space m) : ℝ :=
  whitneyWeightCoord F₀ Q (z.1, z.2.val)

theorem whitneyWeight_nonneg (Q : whitneyBoxes F₀) (z : Space m) : 0 ≤ whitneyWeight F₀ Q z :=
  mul_nonneg (boxCutoff_nonneg _ _) (normalizer_nonneg _)

theorem mem_enlarged_of_whitneyWeight_ne_zero {Q : whitneyBoxes F₀} {z : Space m}
    (hz : whitneyWeight F₀ Q z ≠ 0) : z ∈ Q.1.enlarged (3 / 2) := by
  refine mem_enlarged_of_boxCutoff_ne_zero fun h => hz ?_
  simp only [whitneyWeight, whitneyWeightCoord, h, zero_mul]

theorem not_mem_of_mem_enlarged (havoid : ∀ Q : whitneyBoxes F₀, Q.1.enlarged (3 / 2) ∩ F₀ = ∅)
    {Q : whitneyBoxes F₀} {q : Space m} (hq : q ∈ Q.1.enlarged (3 / 2)) : q ∉ F₀ :=
  fun hF => Set.eq_empty_iff_forall_notMem.1 (havoid Q) q ⟨hq, hF⟩

/-- A weight whose cutoff vanishes near a point vanishes near that point. -/
theorem whitneyWeightCoord_eventuallyEq_zero {Q : whitneyBoxes F₀} {p : Coordinates m}
    (hp : p ∉ boxSupportSet Q.1.radius Q.1.center) :
    whitneyWeightCoord F₀ Q =ᶠ[𝓝 p] fun _ => 0 := by
  filter_upwards [boxBump_eventuallyEq_zero (radius_pos Q.1) hp] with y hy
  simp only [whitneyWeightCoord, boxCutoff, hy, zero_mul]

/-! ### Local finiteness -/

section LocalFinite

variable (hfin : ∀ q ∉ F₀, ∃ U ∈ 𝓝 q,
    {Q : whitneyBoxes F₀ | (U ∩ Q.1.enlarged (3 / 2)).Nonempty}.Finite)

include hfin in
/-- Near a point off `F₀` only finitely many cutoffs are nonzero, and every box whose
enlargement contains the point is among them. -/
theorem exists_finset_boxCutoff_eventually_eq_zero {q : Space m} (hq : q ∉ F₀) :
    ∃ I : Finset (whitneyBoxes F₀),
      (∀ᶠ y in 𝓝 ((q.1, q.2.val) : Coordinates m), ∀ Q ∉ I, boxCutoff Q.1 y = 0) ∧
      ∀ Q : whitneyBoxes F₀, q ∈ Q.1.enlarged (3 / 2) → Q ∈ I := by
  obtain ⟨U, hU, hS⟩ := hfin q hq
  refine ⟨hS.toFinset, ?_, fun Q hQ => hS.mem_toFinset.2 ⟨q, mem_of_mem_nhds hU, hQ⟩⟩
  have hV : {y : Coordinates m | point y.1 y.2 ∈ U} ∈ 𝓝 ((q.1, q.2.val) : Coordinates m) :=
    continuous_point.continuousAt.preimage_mem_nhds hU
  filter_upwards [hV] with y hy Q hQ
  by_contra hne
  exact hQ (hS.mem_toFinset.2 ⟨point y.1 y.2, hy, mem_enlarged_of_boxCutoff_ne_zero hne⟩)

include hfin in
/-- Near a point off `F₀` every weight is a finite normalized weight. -/
theorem exists_finset_whitneyWeightCoord_eventuallyEq {q : Space m} (hq : q ∉ F₀) :
    ∃ I : Finset (whitneyBoxes F₀),
      (∀ Q, whitneyWeightCoord F₀ Q =ᶠ[𝓝 ((q.1, q.2.val) : Coordinates m)]
        normalizedWeight I (fun b : whitneyBoxes F₀ => boxCutoff b.1) Q) ∧
      (∀ Q ∉ I, boxCutoff Q.1 (q.1, q.2.val) = 0) ∧
      ∀ Q : whitneyBoxes F₀, q ∈ Q.1.enlarged (3 / 2) → Q ∈ I := by
  obtain ⟨I, hI, hmem⟩ := exists_finset_boxCutoff_eventually_eq_zero hfin hq
  refine ⟨I, fun Q => ?_, hI.self_of_nhds, hmem⟩
  filter_upwards [hI] with y hy
  simp only [whitneyWeightCoord, normalizedWeight, whitneyMass, tsum_eq_sum hy]

end LocalFinite

/-! ### Smoothness and derivative bounds -/

section Bounds

variable {N : ℕ}
  (hfin : ∀ q ∉ F₀, ∃ U ∈ 𝓝 q,
    {Q : whitneyBoxes F₀ | (U ∩ Q.1.enlarged (3 / 2)).Nonempty}.Finite)
  (havoid : ∀ Q : whitneyBoxes F₀, Q.1.enlarged (3 / 2) ∩ F₀ = ∅)
  (hover : ∀ q : Space m, {Q : whitneyBoxes F₀ | q ∈ Q.1.enlarged (3 / 2)}.encard ≤ N)

include hfin havoid in
theorem contDiff_whitneyWeightCoord (Q : whitneyBoxes F₀) :
    ContDiff ℝ ∞ (whitneyWeightCoord F₀ Q) := by
  refine contDiff_iff_contDiffAt.2 fun p => ?_
  by_cases hsupp : p ∈ boxSupportSet Q.1.radius Q.1.center
  · have hQ : point p.1 p.2 ∈ Q.1.enlarged (3 / 2) := mem_enlarged_of_mem_boxSupportSet hsupp
    obtain ⟨I, hI, -, -⟩ :=
      exists_finset_whitneyWeightCoord_eventuallyEq hfin (not_mem_of_mem_enlarged havoid hQ)
    exact (contDiff_normalizedWeight I (fun b _ => contDiff_boxCutoff b.1)
      (contDiff_boxCutoff Q.1)).contDiffAt.congr_of_eventuallyEq (hI Q)
  · exact contDiffAt_const.congr_of_eventuallyEq (whitneyWeightCoord_eventuallyEq_zero hsupp)

include hfin havoid hover in
/-- The pointwise quotient-rule bound along a smooth slice `g`, at the scale `lam`
of the active cutoffs. -/
theorem norm_iteratedFDeriv_whitneyWeightCoord_comp_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → Coordinates m} (hg : ContDiff ℝ ∞ g) (x : E) (Q : whitneyBoxes F₀)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hB : point (g x).1 (g x).2 ∈ Q.1.enlarged (3 / 2) → ∀ b : whitneyBoxes F₀,
      point (g x).1 (g x).2 ∈ b.1.enlarged (3 / 2) → ∀ i : ℕ, 1 ≤ i → i ≤ 2 →
        ‖iteratedFDeriv ℝ i (boxCutoff b.1 ∘ g) x‖ ≤ boxBumpBound m * lam ^ i)
    {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (whitneyWeightCoord F₀ Q ∘ g) x‖ ≤
      weightConstant N (boxBumpBound m) (normalizerBound N) * lam ^ k := by
  classical
  have hcont : ContinuousAt g x := hg.continuous.continuousAt
  by_cases hsupp : g x ∈ boxSupportSet Q.1.radius Q.1.center
  · have hQ : point (g x).1 (g x).2 ∈ Q.1.enlarged (3 / 2) :=
      mem_enlarged_of_mem_boxSupportSet hsupp
    obtain ⟨I, hI, -, hmem⟩ :=
      exists_finset_whitneyWeightCoord_eventuallyEq hfin (not_mem_of_mem_enlarged havoid hQ)
    have heq : whitneyWeightCoord F₀ Q ∘ g =ᶠ[𝓝 x]
        normalizedWeight I (fun b : whitneyBoxes F₀ => boxCutoff b.1 ∘ g) Q :=
      (hI Q).comp_tendsto hcont
    set A := I.filter fun b : whitneyBoxes F₀ => g x ∈ boxSupportSet b.1.radius b.1.center
      with hA
    have hout : ∀ b ∈ I, b ∉ A → (boxCutoff b.1 ∘ g) =ᶠ[𝓝 x] fun _ => 0 := by
      intro b hb hbA
      have hgb : g x ∉ boxSupportSet b.1.radius b.1.center := fun h =>
        hbA (Finset.mem_filter.2 ⟨hb, h⟩)
      exact (boxBump_eventuallyEq_zero (radius_pos b.1) hgb).comp_tendsto hcont
    have hN : (A.card : ℝ) ≤ N := by
      have hsub : (A : Set (whitneyBoxes F₀)) ⊆
          {b : whitneyBoxes F₀ | point (g x).1 (g x).2 ∈ b.1.enlarged (3 / 2)} := by
        intro b hb
        show point (g x).1 (g x).2 ∈ b.1.enlarged (3 / 2)
        exact mem_enlarged_of_mem_boxSupportSet (Finset.mem_filter.1 hb).2
      have h1 := (Set.encard_le_encard hsub).trans (hover _)
      rw [Set.encard_coe_eq_coe_finsetCard] at h1
      exact_mod_cast h1
    have hψB : ∀ b ∈ A, ∀ i : ℕ, 1 ≤ i → i ≤ 2 →
        ‖iteratedFDeriv ℝ i (boxCutoff b.1 ∘ g) x‖ ≤ boxBumpBound m * lam ^ i :=
      fun b hb => hB hQ b (mem_enlarged_of_mem_boxSupportSet (Finset.mem_filter.1 hb).2)
    have hsum := sum_norm_iteratedFDeriv_normalizedWeight_le
      (ψ := fun b : whitneyBoxes F₀ => boxCutoff b.1 ∘ g)
      (fun b _ => (contDiff_boxCutoff b.1).comp hg)
      (fun b _ => boxCutoff_nonneg b.1 _) (fun b _ => boxCutoff_le_one b.1 _)
      (Finset.filter_subset _ I) hout hN (boxBumpBound_nonneg m) hlam hψB
      (fun i hi s hs => norm_iteratedFDeriv_normalizer_le hi hs) hk
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
    exact le_trans (Finset.single_le_sum (f := fun a => ‖iteratedFDeriv ℝ k
      (normalizedWeight I (fun b : whitneyBoxes F₀ => boxCutoff b.1 ∘ g) a) x‖)
      (fun a _ => norm_nonneg _) (hmem Q hQ)) hsum
  · have h0 : whitneyWeightCoord F₀ Q ∘ g =ᶠ[𝓝 x] fun _ => 0 :=
      (whitneyWeightCoord_eventuallyEq_zero hsupp).comp_tendsto hcont
    rw [iteratedFDeriv_eq_zero_of_eventuallyEq_zero h0 k, norm_zero]
    exact mul_nonneg (weightConstant_nonneg (Nat.cast_nonneg N) (boxBumpBound_nonneg m)
      (normalizerBound_nonneg _)) (pow_nonneg hlam k)

variable (hcomp : ∀ Q Q' : whitneyBoxes F₀,
    (Q.1.enlarged (3 / 2) ∩ Q'.1.enlarged (3 / 2)).Nonempty → Q.1.radius ≤ 4 * Q'.1.radius)

include hcomp in
/-- Spatial derivatives of the active cutoffs, at the scale `4/r_Q`. -/
theorem norm_iteratedFDeriv_boxCutoff_spatial_le (Q : whitneyBoxes F₀) (t : ℝ) (u : Spatial m)
    (hQ : point u t ∈ Q.1.enlarged (3 / 2)) (b : whitneyBoxes F₀)
    (hb : point u t ∈ b.1.enlarged (3 / 2)) (i : ℕ) (hi : i ≤ 2) :
    ‖iteratedFDeriv ℝ i (boxCutoff b.1 ∘ fun v : Spatial m => ((v, t) : Coordinates m)) u‖ ≤
      boxBumpBound m * (4 * Q.1.radius⁻¹) ^ i := by
  have hrQ := radius_pos Q.1
  have hrb := radius_pos b.1
  have hle : Q.1.radius ≤ 4 * b.1.radius := hcomp Q b ⟨_, hQ, hb⟩
  have key : b.1.radius⁻¹ ≤ 4 * Q.1.radius⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hrb hrQ]
    linarith
  calc ‖iteratedFDeriv ℝ i (boxCutoff b.1 ∘ fun v : Spatial m => ((v, t) : Coordinates m)) u‖
      ≤ boxBumpBound m * b.1.radius⁻¹ ^ i :=
        norm_iteratedFDeriv_boxBump_spatial_le hrb b.1.center t u hi
    _ ≤ boxBumpBound m * (4 * Q.1.radius⁻¹) ^ i :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.2 hrb.le) key i)
          (boxBumpBound_nonneg m)

include hcomp in
/-- Time derivatives of the active cutoffs, at the scale `16/r_Q²`. -/
theorem norm_iteratedFDeriv_boxCutoff_time_le (Q : whitneyBoxes F₀) (u : Spatial m) (t : ℝ)
    (hQ : point u t ∈ Q.1.enlarged (3 / 2)) (b : whitneyBoxes F₀)
    (hb : point u t ∈ b.1.enlarged (3 / 2)) (i : ℕ) (hi : i ≤ 2) :
    ‖iteratedFDeriv ℝ i (boxCutoff b.1 ∘ fun s : ℝ => ((u, s) : Coordinates m)) t‖ ≤
      boxBumpBound m * (16 * (Q.1.radius ^ 2)⁻¹) ^ i := by
  have hrQ := radius_pos Q.1
  have hrb := radius_pos b.1
  have hle : Q.1.radius ≤ 4 * b.1.radius := hcomp Q b ⟨_, hQ, hb⟩
  have hrQ2 : 0 < Q.1.radius ^ 2 := by positivity
  have hrb2 : 0 < b.1.radius ^ 2 := by positivity
  have key : (b.1.radius ^ 2)⁻¹ ≤ 16 * (Q.1.radius ^ 2)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hrb2 hrQ2]
    nlinarith
  calc ‖iteratedFDeriv ℝ i (boxCutoff b.1 ∘ fun s : ℝ => ((u, s) : Coordinates m)) t‖
      ≤ boxBumpBound m * (b.1.radius ^ 2)⁻¹ ^ i :=
        norm_iteratedFDeriv_boxBump_time_le hrb b.1.center u t hi
    _ ≤ boxBumpBound m * (16 * (Q.1.radius ^ 2)⁻¹) ^ i :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.2 hrb2.le) key i)
          (boxBumpBound_nonneg m)

include hfin havoid hover hcomp in
/-- Own-scale parabolic `C^{2,1}` bounds of every weight, with the dimensional
constant `16 C(N, B, F)` of the abstract normalization bound. -/
theorem hasParabolicDerivBounds_whitneyWeight (Q : whitneyBoxes F₀) :
    HasParabolicDerivBounds (whitneyWeight F₀ Q)
      (16 * weightConstant N (boxBumpBound m) (normalizerBound N)) Q.1.radius where
  contDiff := contDiff_infty.1 (contDiff_whitneyWeightCoord hfin havoid Q) 2
  spatial_le u t := by
    have hr := radius_pos Q.1
    have hwc := weightConstant_nonneg (Nat.cast_nonneg N) (boxBumpBound_nonneg m)
      (normalizerBound_nonneg (N : ℝ))
    have h := norm_iteratedFDeriv_whitneyWeightCoord_comp_le hfin havoid hover
      (contDiff_id.prodMk contDiff_const) u Q
      (mul_nonneg (by norm_num) (inv_nonneg.2 hr.le))
      (fun hQ b hb i _ hi => norm_iteratedFDeriv_boxCutoff_spatial_le hcomp Q t u hQ b hb i hi)
      (k := 1) (by norm_num)
    show ‖fderiv ℝ (whitneyWeightCoord F₀ Q ∘ fun v : Spatial m => ((v, t) : Coordinates m)) u‖
      ≤ _
    rw [← norm_iteratedFDeriv_one]
    refine h.trans ?_
    rw [pow_one, div_eq_mul_inv]
    nlinarith [mul_nonneg hwc (inv_nonneg.2 hr.le)]
  spatial₂_le u t := by
    have h := norm_iteratedFDeriv_whitneyWeightCoord_comp_le hfin havoid hover
      (contDiff_id.prodMk contDiff_const) u Q
      (mul_nonneg (by norm_num) (inv_nonneg.2 (radius_pos Q.1).le))
      (fun hQ b hb i _ hi => norm_iteratedFDeriv_boxCutoff_spatial_le hcomp Q t u hQ b hb i hi)
      (k := 2) le_rfl
    show ‖fderiv ℝ (fderiv ℝ
      (whitneyWeightCoord F₀ Q ∘ fun v : Spatial m => ((v, t) : Coordinates m))) u‖ ≤ _
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    refine h.trans_eq ?_
    ring
  time_le u t := by
    have h := norm_iteratedFDeriv_whitneyWeightCoord_comp_le hfin havoid hover
      (contDiff_const.prodMk contDiff_id) t Q
      (mul_nonneg (by norm_num) (inv_nonneg.2 (pow_nonneg (radius_pos Q.1).le 2)))
      (fun hQ b hb i _ hi => norm_iteratedFDeriv_boxCutoff_time_le hcomp Q u t hQ b hb i hi)
      (k := 1) (by norm_num)
    rw [← Real.norm_eq_abs, norm_deriv_eq_norm_fderiv]
    show ‖fderiv ℝ (whitneyWeightCoord F₀ Q ∘ fun s : ℝ => ((u, s) : Coordinates m)) t‖ ≤ _
    rw [← norm_iteratedFDeriv_one]
    refine h.trans_eq ?_
    ring

end Bounds


end WhitneyCutoff

/-! ### The smooth Whitney partition -/

section Partition

open WhitneyCutoff SmoothCutoff

variable {m : ℕ} {F₀ : Set (Space m)} {N : ℕ}

/-- The smooth Whitney partition built from the cutoffs, for Whitney data whose cells,
centers and radii are the boxes' own, under the overlap facts of
`whitneyBoxes_enlarged_overlap` and the upper center distance of `exists_whitneyBoxes_data`. -/
def whitneyPartitionOfCutoffs
    (W : WhitneyData m (whitneyBoxes F₀) F₀ (whitneyD m) (whitneyA m - whitneyD m))
    (hW : ∀ Q, W.cell Q = Q.1.toSet ∧ W.center Q = Q.1.center ∧ W.radius Q = Q.1.radius)
    (hcomp : ∀ Q Q' : whitneyBoxes F₀, (Q.1.enlarged (3 / 2) ∩ Q'.1.enlarged (3 / 2)).Nonempty →
      Q.1.radius ≤ 4 * Q'.1.radius ∧
        dist Q.1.center Q'.1.center ≤ 3 * whitneyD m * (Q.1.radius + Q'.1.radius))
    (hover : ∀ q : Space m, {Q : whitneyBoxes F₀ | q ∈ Q.1.enlarged (3 / 2)}.encard ≤ N)
    (hfin : ∀ q ∉ F₀, ∃ U ∈ 𝓝 q,
      {Q : whitneyBoxes F₀ | (U ∩ Q.1.enlarged (3 / 2)).Nonempty}.Finite)
    (havoid : ∀ Q : whitneyBoxes F₀, Q.1.enlarged (3 / 2) ∩ F₀ = ∅)
    (hcenter : ∀ Q : whitneyBoxes F₀,
      Metric.infDist Q.1.center F₀ ≤ (2 * whitneyA m + 3 * whitneyD m) * Q.1.radius) :
    WhitneyPartition W (15 * whitneyD m) (2 * whitneyA m + 3 * whitneyD m)
      (16 * weightConstant N (boxBumpBound m) (normalizerBound N)) N where
  weight := whitneyWeight F₀
  nonneg := whitneyWeight_nonneg
  measurable Q := ((contDiff_whitneyWeightCoord hfin havoid Q).continuous.measurable).comp
    (measurable_spatial.prodMk measurable_time)
  locallyFinite q hq := by
    obtain ⟨U, hU, hS⟩ := hfin q hq
    refine ⟨U, hU, hS.subset ?_⟩
    rintro Q ⟨x, hxU, hx⟩
    show (U ∩ Q.1.enlarged (3 / 2)).Nonempty
    exact ⟨x, hxU, mem_enlarged_of_whitneyWeight_ne_zero hx⟩
  hasSum_one q hq := by
    obtain ⟨I, -, hzero, hmem⟩ := exists_finset_whitneyWeightCoord_eventuallyEq hfin hq
    have hcov : q ∈ ⋃ j, W.cell j := by
      rw [W.iUnion_cell]
      exact hq
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hcov
    rw [(hW j).1] at hj
    have hj1 : boxCutoff j.1 (q.1, q.2.val) = 1 := boxCutoff_eq_one hj
    have hjI : j ∈ I := hmem j (toSet_subset_enlarged j.1 hj)
    have hmass : whitneyMass F₀ (q.1, q.2.val) = ∑ b ∈ I, boxCutoff b.1 (q.1, q.2.val) :=
      tsum_eq_sum hzero
    have hge : 1 / 2 ≤ ∑ b ∈ I, boxCutoff b.1 (q.1, q.2.val) := by
      have h1 := Finset.single_le_sum
        (f := fun b : whitneyBoxes F₀ => boxCutoff b.1 (q.1, q.2.val))
        (fun b _ => boxCutoff_nonneg b.1 _) hjI
      simp only [hj1] at h1
      linarith
    have hsum : ∑ b ∈ I, whitneyWeight F₀ b q = 1 := by
      simp only [whitneyWeight, whitneyWeightCoord, hmass, ← Finset.sum_mul, mul_normalizer]
      exact activation_eq_one hge
    rw [← hsum]
    exact hasSum_sum_of_ne_finset_zero fun b hb => by
      simp only [whitneyWeight, whitneyWeightCoord, hzero b hb, zero_mul]
  center_dist_le i j q hq hne := by
    rw [(hW j).1] at hq
    have hi := mem_enlarged_of_whitneyWeight_ne_zero hne
    have hj := toSet_subset_enlarged j.1 hq
    obtain ⟨h1, h2⟩ := hcomp i j ⟨q, hi, hj⟩
    rw [(hW i).2.1, (hW j).2.1, (hW j).2.2]
    have hD : 0 ≤ whitneyD m := zero_le_one.trans (le_max_left _ _)
    calc dist i.1.center j.1.center ≤ 3 * whitneyD m * (i.1.radius + j.1.radius) := h2
      _ ≤ 15 * whitneyD m * j.1.radius := by
        nlinarith [mul_nonneg hD (sub_nonneg.2 h1)]
  radius_comparable i j q hq hne := by
    rw [(hW j).1] at hq
    have hi := mem_enlarged_of_whitneyWeight_ne_zero hne
    have hj := toSet_subset_enlarged j.1 hq
    rw [(hW i).2.2, (hW j).2.2]
    exact ⟨(hcomp i j ⟨q, hi, hj⟩).1, (hcomp j i ⟨q, hj, hi⟩).1⟩
  overlap_le q := by
    refine le_trans (Set.encard_le_encard ?_) (hover q)
    intro Q hQ
    show q ∈ Q.1.enlarged (3 / 2)
    exact mem_enlarged_of_whitneyWeight_ne_zero hQ
  infDist_center_le j := by
    rw [(hW j).2.1, (hW j).2.2]
    exact hcenter j
  derivBounds Q := by
    rw [(hW Q).2.2]
    exact hasParabolicDerivBounds_whitneyWeight hfin havoid hover
      (fun Q Q' h => (hcomp Q Q' h).1) Q

end Partition

/-- **Smooth Whitney partition**, proved from the statements `exists_whitneyBoxes_data`
and `whitneyBoxes_enlarged_overlap`, taken as hypotheses. The constants are
`H = 15 D_m`, `b = 2 A_W + 3 D_m`, the overlap number `N` of the enlarged boxes, and
`K = 16 C(N, B_m, F_N)` with the abstract normalization constant of
`SmoothCutoff.NormalizedWeights`. The weights are `θ_Q f(Σ θ)` for the product cutoffs
`θ_Q` of `WhitneyCutoff.boxCutoff`. -/
theorem exists_whitneyBoxes_partition_proof
    (hdata : ∀ (m : ℕ) (F₀ : Set (Space m)) (_hF₀ : IsCompact F₀) (_hne : F₀.Nonempty),
      ∃ W : WhitneyData m (whitneyBoxes F₀) F₀ (whitneyD m) (whitneyA m - whitneyD m),
        (∀ Q, W.cell Q = Q.1.toSet ∧ W.center Q = Q.1.center ∧ W.radius Q = Q.1.radius) ∧
        (∀ Q : whitneyBoxes F₀,
          Metric.infDist Q.1.center F₀ ≤ (2 * whitneyA m + 3 * whitneyD m) * Q.1.radius) ∧
        (∀ Q : whitneyBoxes F₀, ∀ q ∈ Q.1.toSet,
          Metric.infDist q F₀ ≤ (2 * whitneyA m + 4 * whitneyD m) * Q.1.radius) ∧
        (∀ Q Q' : whitneyBoxes F₀, Q ≠ Q' →
          max Q.1.radius Q'.1.radius / 2 ≤ dist Q.1.center Q'.1.center))
    (hoverlap : ∀ m : ℕ, ∃ N : ℕ, ∀ F₀ : Set (Space m), IsCompact F₀ → F₀.Nonempty →
      (∀ Q Q' : whitneyBoxes F₀, (Q.1.enlarged (3 / 2) ∩ Q'.1.enlarged (3 / 2)).Nonempty →
        Q.1.radius ≤ 4 * Q'.1.radius ∧
          dist Q.1.center Q'.1.center ≤ 3 * whitneyD m * (Q.1.radius + Q'.1.radius)) ∧
      (∀ q : Space m, {Q : whitneyBoxes F₀ | q ∈ Q.1.enlarged (3 / 2)}.encard ≤ N) ∧
      (∀ q ∉ F₀, ∃ U ∈ 𝓝 q,
        {Q : whitneyBoxes F₀ | (U ∩ Q.1.enlarged (3 / 2)).Nonempty}.Finite) ∧
      (∀ Q : whitneyBoxes F₀, Q.1.enlarged (3 / 2) ∩ F₀ = ∅))
    (m : ℕ) :
    ∃ (H b K : ℝ) (N : ℕ), 0 ≤ H ∧ ∀ (F₀ : Set (Space m)), IsCompact F₀ → F₀.Nonempty →
      ∀ W : WhitneyData m (whitneyBoxes F₀) F₀ (whitneyD m) (whitneyA m - whitneyD m),
        (∀ Q, W.cell Q = Q.1.toSet ∧ W.center Q = Q.1.center ∧ W.radius Q = Q.1.radius) →
        ∃ P : WhitneyPartition W H b K N,
          ∀ Q q, P.weight Q q ≠ 0 → q ∈ Q.1.enlarged (3 / 2) := by
  obtain ⟨N, hN⟩ := hoverlap m
  refine ⟨15 * whitneyD m, 2 * whitneyA m + 3 * whitneyD m,
    16 * SmoothCutoff.weightConstant N (SmoothCutoff.boxBumpBound m)
      (SmoothCutoff.normalizerBound N), N,
    mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left _ _)), ?_⟩
  intro F₀ hF₀ hne W hW
  obtain ⟨hcomp, hover, hfin, havoid⟩ := hN F₀ hF₀ hne
  obtain ⟨-, -, hcenter, -, -⟩ := hdata m F₀ hF₀ hne
  exact ⟨whitneyPartitionOfCutoffs W hW hcomp hover hfin havoid hcenter,
    fun Q q hq => WhitneyCutoff.mem_enlarged_of_whitneyWeight_ne_zero hq⟩

end ParabolicRectifiability
