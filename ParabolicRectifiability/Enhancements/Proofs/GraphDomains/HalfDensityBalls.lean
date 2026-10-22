import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-! # Disjoint half-density balls

Proof of `Enhancements.GraphDomainTree.exists_disjoint_halfDensity_balls`, under the name
`exists_disjoint_halfDensity_balls_proof`.

The only covering or selection argument is the hypothesis `hfive : FivefoldSelectionStatement`
(never proved or restated here). The density step uses mathlib's Lebesgue
density theorem for uniformly locally doubling measures,
`IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div`.

Route.
1. For `r > 0`, `μ(closedBall p r) = v r^k = μ(ball p r)` (squeeze between `μ(ball p r)` and
   `μ(ball p s) = v s^k`, `s ↓ r`); hence the shell `closedBall p r \ ball p r` is null for
   `r > 0` only.
2. The ball law gives local finiteness and uniform local doubling (constant `2^k`); `B` is
   proper, hence second countable. Mathlib's density theorem, restricted to `E`, applies.
3. At each good point one radius `0 < r ≤ δ/5` with `v r^k ≤ 2 μ(E ∩ B(p,r))` (the threshold
   `1/2 ≤ ratio` is non-strict).
4. `hfive` with index type the good points of `E`, these centres and these radii.
5. The countable selection is reindexed by an equivalence with a subset of `ℕ`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ParabolicRectifiability.Enhancements.GraphDomainTree

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.Characterization (FivefoldSelectionStatement)

section BallLaw

variable {B : Type} [MetricSpace B] [MeasurableSpace B] [BorelSpace B]
  {μ : Measure B} {k : ℕ} {v : ℝ≥0∞}

omit [BorelSpace B] in
/-- Step 1. Closed balls of positive radius obey the same exact law as open balls. -/
theorem gdb1_measure_closedBall (hvt : v ≠ ⊤)
    (hball : ∀ (p : B) (r : ℝ), 0 < r → μ (Metric.ball p r) = v * ENNReal.ofReal r ^ k)
    (p : B) {r : ℝ} (hr : 0 < r) :
    μ (Metric.closedBall p r) = v * ENNReal.ofReal r ^ k := by
  refine le_antisymm ?_ ?_
  · have hcont : Filter.Tendsto (fun s : ℝ => v * ENNReal.ofReal s ^ k) (𝓝[>] r)
        (𝓝 (v * ENNReal.ofReal r ^ k)) :=
      (((ENNReal.continuous_const_mul hvt).comp
        ((ENNReal.continuous_pow k).comp ENNReal.continuous_ofReal)).tendsto r).mono_left
        nhdsWithin_le_nhds
    refine ge_of_tendsto hcont (eventually_nhdsWithin_of_forall fun s hs => ?_)
    have hs' : r < s := hs
    rw [← hball p s (hr.trans hs')]
    exact measure_mono (Metric.closedBall_subset_ball hs')
  · rw [← hball p r hr]
    exact measure_mono Metric.ball_subset_closedBall

/-- Step 1. The shell `closedBall p r \ ball p r` is null for `r > 0` (not at `r = 0`). -/
theorem gdb1_measure_closedBall_diff_ball (hvt : v ≠ ⊤)
    (hball : ∀ (p : B) (r : ℝ), 0 < r → μ (Metric.ball p r) = v * ENNReal.ofReal r ^ k)
    (p : B) {r : ℝ} (hr : 0 < r) :
    μ (Metric.closedBall p r \ Metric.ball p r) = 0 := by
  have hfin : μ (Metric.ball p r) ≠ ⊤ := by
    rw [hball p r hr]
    exact ENNReal.mul_ne_top hvt (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  rw [measure_sdiff Metric.ball_subset_closedBall measurableSet_ball.nullMeasurableSet hfin,
    gdb1_measure_closedBall hvt hball p hr, hball p r hr, tsub_self]

/-- Step 1. For `r > 0`, the closed-ball trace of `E` has no more mass than the open one. -/
theorem gdb1_measure_inter_closedBall_le (hvt : v ≠ ⊤)
    (hball : ∀ (p : B) (r : ℝ), 0 < r → μ (Metric.ball p r) = v * ENNReal.ofReal r ^ k)
    (E : Set B) (p : B) {r : ℝ} (hr : 0 < r) :
    μ (E ∩ Metric.closedBall p r) ≤ μ (E ∩ Metric.ball p r) := by
  calc μ (E ∩ Metric.closedBall p r)
      ≤ μ ((E ∩ Metric.ball p r) ∪ (Metric.closedBall p r \ Metric.ball p r)) := by
        refine measure_mono fun y hy => ?_
        by_cases hyb : y ∈ Metric.ball p r
        · exact Or.inl ⟨hy.1, hyb⟩
        · exact Or.inr ⟨hy.2, hyb⟩
    _ ≤ μ (E ∩ Metric.ball p r) + μ (Metric.closedBall p r \ Metric.ball p r) :=
        measure_union_le _ _
    _ = μ (E ∩ Metric.ball p r) := by
        rw [gdb1_measure_closedBall_diff_ball hvt hball p hr, add_zero]

omit [BorelSpace B] in
/-- Step 2. The ball law makes `μ` locally finite. -/
theorem gdb1_isLocallyFiniteMeasure (hvt : v ≠ ⊤)
    (hball : ∀ (p : B) (r : ℝ), 0 < r → μ (Metric.ball p r) = v * ENNReal.ofReal r ^ k) :
    IsLocallyFiniteMeasure μ :=
  ⟨fun x => ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, by
    rw [hball x 1 one_pos, ENNReal.ofReal_one, one_pow, mul_one]
    exact hvt.lt_top⟩⟩

omit [BorelSpace B] in
/-- Step 2. The ball law makes `μ` uniformly locally doubling, with constant `2^k`. -/
theorem gdb1_isUnifLocDoublingMeasure (hvt : v ≠ ⊤)
    (hball : ∀ (p : B) (r : ℝ), 0 < r → μ (Metric.ball p r) = v * ENNReal.ofReal r ^ k) :
    IsUnifLocDoublingMeasure μ := by
  refine ⟨⟨2 ^ k, eventually_nhdsWithin_of_forall fun ε hε x => ?_⟩⟩
  have hε' : (0 : ℝ) < ε := hε
  rw [gdb1_measure_closedBall hvt hball x (mul_pos two_pos hε'),
    gdb1_measure_closedBall hvt hball x hε',
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_pow]
  push_cast
  exact le_of_eq (by ring)

/-- Step 3. At `μ.restrict E`-almost every point there is **one** radius
`0 < r ≤ δ/5` with `v r^k ≤ 2 μ(E ∩ B(p,r))`. -/
theorem gdb1_ae_halfDensity_radius [ProperSpace B] (hv0 : v ≠ 0) (hvt : v ≠ ⊤)
    (hball : ∀ (p : B) (r : ℝ), 0 < r → μ (Metric.ball p r) = v * ENNReal.ofReal r ^ k)
    (E : Set B) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ x ∂μ.restrict E, ∃ r : ℝ, 0 < r ∧ r ≤ δ / 5 ∧
      v * ENNReal.ofReal r ^ k ≤ 2 * μ (E ∩ Metric.ball x r) := by
  have := gdb1_isLocallyFiniteMeasure hvt hball
  have := gdb1_isUnifLocDoublingMeasure hvt hball
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ E 1] with x hx
  have hlim : Filter.Tendsto
      (fun r : ℝ => μ (E ∩ Metric.closedBall x r) / μ (Metric.closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    hx (ι := ℝ) (l := 𝓝[>] (0 : ℝ)) (fun _ => x) id Filter.tendsto_id
      (eventually_nhdsWithin_of_forall fun j hj => by
        show x ∈ Metric.closedBall x (1 * j)
        rw [Metric.mem_closedBall, dist_self, one_mul]
        exact (Set.mem_Ioi.mp hj).le)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (2 : ℝ≥0∞)⁻¹ ≤ μ (E ∩ Metric.closedBall x r) / μ (Metric.closedBall x r) :=
    hlim.eventually (Ici_mem_nhds (ENNReal.inv_lt_one.2 ENNReal.one_lt_two))
  obtain ⟨r, hr, hrI⟩ :=
    (hev.and (Ioc_mem_nhdsGT (div_pos hδ (by norm_num : (0 : ℝ) < 5)))).exists
  have hr0 : 0 < r := hrI.1
  refine ⟨r, hr0, hrI.2, ?_⟩
  have hcb := gdb1_measure_closedBall hvt hball x hr0
  have hb0 : μ (Metric.closedBall x r) ≠ 0 := by
    rw [hcb]
    exact mul_ne_zero hv0 (pow_ne_zero _ (ENNReal.ofReal_pos.2 hr0).ne')
  have hbt : μ (Metric.closedBall x r) ≠ ⊤ := by
    rw [hcb]
    exact ENNReal.mul_ne_top hvt (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbt)] at hr
  calc v * ENNReal.ofReal r ^ k = μ (Metric.closedBall x r) := hcb.symm
    _ = 2 * (2⁻¹ * μ (Metric.closedBall x r)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * μ (E ∩ Metric.closedBall x r) := mul_le_mul_right hr 2
    _ ≤ 2 * μ (E ∩ Metric.ball x r) :=
        mul_le_mul_right (gdb1_measure_inter_closedBall_le hvt hball E x hr0) 2

end BallLaw

  -- `hE` (measurability) and `hEb` (boundedness) are unused by the proof; the linter is
  -- silenced here only, keeping the binder names of the statement.
set_option linter.unusedVariables false in
/-- Proof of `Enhancements.GraphDomainTree.exists_disjoint_halfDensity_balls`. The selection is
`hfive` applied to the good points of `E`, each with its one half-density radius; the selected
countable subtype is reindexed by an equivalence with a subset of `ℕ`. -/
theorem exists_disjoint_halfDensity_balls_proof (hfive : FivefoldSelectionStatement)
    {B : Type} [MetricSpace B] [ProperSpace B] [MeasurableSpace B] [BorelSpace B]
    (μ : Measure B) (k : ℕ) (v : ℝ≥0∞) (hv0 : v ≠ 0) (hvt : v ≠ ⊤)
    (hball : ∀ (p : B) (r : ℝ), 0 < r → μ (Metric.ball p r) = v * ENNReal.ofReal r ^ k)
    (E : Set B) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (L : Set ℕ) (p : L → B) (r : L → ℝ),
      (∀ l, p l ∈ E) ∧ (∀ l, 0 < r l ∧ 5 * r l ≤ δ) ∧
      (Pairwise fun l l' => Disjoint (Metric.ball (p l) (r l)) (Metric.ball (p l') (r l'))) ∧
      (∀ l, v * ENNReal.ofReal (r l) ^ k ≤ 2 * μ (E ∩ Metric.ball (p l) (r l))) ∧
      μ (E \ ⋃ l, Metric.ball (p l) (5 * r l)) = 0 := by
  -- good points: those carrying a half-density radius `≤ δ/5`
  let P : B → Prop := fun x => ∃ r : ℝ, 0 < r ∧ r ≤ δ / 5 ∧
      v * ENNReal.ofReal r ^ k ≤ 2 * μ (E ∩ Metric.ball x r)
  have hae : ∀ᵐ x ∂μ.restrict E, P x := gdb1_ae_halfDensity_radius hv0 hvt hball E hδ
  -- the index type of the selection: the good points of `E`, each with one chosen radius
  let ι : Type := {x : B // x ∈ E ∧ P x}
  let z : ι → B := fun i => i.1
  let ρ : ι → ℝ := fun i => Classical.choose i.2.2
  have hρ : ∀ i : ι, 0 < ρ i ∧ ρ i ≤ δ / 5 ∧
      v * ENNReal.ofReal (ρ i) ^ k ≤ 2 * μ (E ∩ Metric.ball (z i) (ρ i)) :=
    fun i => Classical.choose_spec i.2.2
  obtain ⟨J, hJc, hJd, hJcov⟩ :=
    hfive B ι z ρ (fun i => (hρ i).1) ⟨δ / 5, fun i => (hρ i).2.1⟩
  -- reindex the countable selection by an equivalence with a subset of `ℕ`
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_injective.1 hJc
  let e : J ≃ Set.range f := Equiv.ofInjective f hf
  refine ⟨Set.range f, fun l => z (e.symm l).1, fun l => ρ (e.symm l).1,
    fun l => (e.symm l).1.2.1, fun l => ⟨(hρ (e.symm l).1).1, ?_⟩, ?_,
    fun l => (hρ (e.symm l).1).2.2, ?_⟩
  · show 5 * ρ (e.symm l).1 ≤ δ
    have h5 := (hρ (e.symm l).1).2.1
    linarith
  · intro l l' hll'
    have hne : (e.symm l).1 ≠ (e.symm l').1 := fun h =>
      hll' (e.symm.injective (Subtype.ext h))
    exact hJd (e.symm l).2 (e.symm l').2 hne
  · refine measure_mono_null (t := {x | ¬ P x} ∩ E) ?_ ?_
    · rintro x ⟨hxE, hxU⟩
      refine ⟨fun hPx => hxU ?_, hxE⟩
      obtain ⟨j, hjJ, hxj⟩ := hJcov ⟨x, hxE, hPx⟩
      refine Set.mem_iUnion.2 ⟨e ⟨j, hjJ⟩, ?_⟩
      show x ∈ Metric.ball (z (e.symm (e ⟨j, hjJ⟩)).1) (5 * ρ (e.symm (e ⟨j, hjJ⟩)).1)
      rw [Equiv.symm_apply_apply]
      exact hxj
    · exact nonpos_iff_eq_zero.1
        ((Measure.le_restrict_apply _ _).trans (ae_iff.1 hae).le)

end ParabolicRectifiability.Enhancements.GraphDomainTree
