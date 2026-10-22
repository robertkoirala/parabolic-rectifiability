import ParabolicRectifiability.Analysis.TraceExtension.Reservoirs.Sets
import ParabolicRectifiability.Analysis.TraceExtension.Hall.Allocation
import ParabolicRectifiability.Analysis.TraceExtension.SourceAllocation

/-! # Simultaneous allocation to all Whitney holes

`exists_whitney_source_allocation_proof` allocates a diffuse source to all Whitney cells
at once. Two analytic inputs enter as leading hypotheses at the universes of the target:
finite real-capacity transport (proved by `exists_transport_of_hall_condition_proof`) and
weak compactness of bounded densities (proved by
`exists_weakly_convergent_density_subseq_proof`). The reductions
`hall_allocation_iff_proof` and `exists_countable_hall_allocation_proof` turn them into the
countable Hall allocation.

Construction. Choose a nearest anchor `a_i ∈ F₀` for each
center and put `C_B = |D| + |b| + 1 > D + b`, so the cell `Q_i ⊆ P(a_i, C_B r_i) = B_i`.
`exists_reservoir_sets_proof` gives reservoirs `S_{i,l} ⊆ B_i` of mass at
least `c₁ (C_B r_i)^k`. For finitely many requests, a Vitali subfamily of disjoint
balls whose fivefold enlargements cover, the disjoint cells with exact volumes and the
masses of the selected reservoirs give Hall's inequality with
`A = (m + 1) 2 ω_m 5^k / c₁` (`hall_inequality_of_reservoirs`). The countable Hall
allocation gives the densities; normalizing them to probability measures and applying
the robust simplex bound of the reservoirs gives the allocated simplex constant `c₂ C_B`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace ParabolicRectifiability

namespace Reservoirs

/-- The Hall ratio `2 ω_m 5^(m+2) / c₁`. -/
def hallRatio (m : ℕ) (c₁ : ℝ) : ℝ := 2 * (omega m).toReal * 5 ^ (m + 2) / c₁

/-- The Hall constant `(m + 1) · 2 ω_m 5^(m+2) / c₁`. -/
def hallConst (m : ℕ) (c₁ : ℝ) : ℝ := (m + 1) * hallRatio m c₁

theorem hallRatio_pos {m : ℕ} {c₁ : ℝ} (hc₁ : 0 < c₁) : 0 < hallRatio m c₁ := by
  have : 0 < (omega m).toReal := ENNReal.toReal_pos (omega_pos m).ne' (omega_lt_top m).ne
  unfold hallRatio
  positivity

theorem hallConst_pos {m : ℕ} {c₁ : ℝ} (hc₁ : 0 < c₁) : 0 < hallConst m c₁ := by
  have := hallRatio_pos (m := m) hc₁
  unfold hallConst
  positivity

/-- **Hall's inequality for reservoirs.** Disjoint measurable
cells `Q_i` of volume `r_i^k` inside balls `P(p_i, δ_i)`, carrying sets `S_{i,l}` of mass
at least `c₁ δ_i^k` inside the same balls: every finite request family `I` satisfies
`Σ_{(i,l) ∈ I} r_i^k ≤ A σ(⋃_{(i,l) ∈ I} S_{i,l})` with `A = hallConst m c₁`. -/
theorem hall_inequality_of_reservoirs {m : ℕ} {ι : Type*} (σ : Measure (Space m))
    (Q : ι → Set (Space m)) (hQm : ∀ i, MeasurableSet (Q i))
    (hQd : Pairwise fun i j => Disjoint (Q i) (Q j))
    (r : ι → ℝ) (hQvol : ∀ i, parabolicVolume m (Q i) = ENNReal.ofReal (r i ^ (m + 2)))
    (p : ι → Space m) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (hQB : ∀ i, Q i ⊆ Metric.ball (p i) (δ i))
    (S : ι → Fin (m + 1) → Set (Space m)) (hSm : ∀ i l, MeasurableSet (S i l))
    (hSB : ∀ i l, S i l ⊆ Metric.ball (p i) (δ i))
    {c₁ : ℝ} (hc₁ : 0 < c₁) (hS : ∀ i l, ENNReal.ofReal (c₁ * δ i ^ (m + 2)) ≤ σ (S i l))
    (I : Finset (ι × Fin (m + 1))) :
    ∑ q ∈ I, ENNReal.ofReal (r q.1 ^ (m + 2)) ≤
      ENNReal.ofReal (hallConst m c₁) * σ (⋃ q ∈ I, S q.1 q.2) := by
  classical
  have hK0 : 0 < hallRatio m c₁ := hallRatio_pos hc₁
  set I' : Finset ι := I.image Prod.fst with hI'
  -- Each cell carries at most `m + 1` requests.
  have h1 : ∑ q ∈ I, ENNReal.ofReal (r q.1 ^ (m + 2)) ≤
      ((m : ℝ≥0∞) + 1) * ∑ i ∈ I', ENNReal.ofReal (r i ^ (m + 2)) := by
    calc ∑ q ∈ I, ENNReal.ofReal (r q.1 ^ (m + 2))
        ≤ ∑ q ∈ I' ×ˢ (Finset.univ : Finset (Fin (m + 1))), ENNReal.ofReal (r q.1 ^ (m + 2)) :=
          Finset.sum_le_sum_of_subset fun q hq =>
            Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hq, Finset.mem_univ _⟩
      _ = ∑ i ∈ I', ∑ _l : Fin (m + 1), ENNReal.ofReal (r i ^ (m + 2)) :=
          Finset.sum_product _ _ _
      _ = ((m : ℝ≥0∞) + 1) * ∑ i ∈ I', ENNReal.ofReal (r i ^ (m + 2)) := by
          rw [Finset.mul_sum]
          simp
  -- The disjoint cells lie in their balls.
  have h2 : ∑ i ∈ I', ENNReal.ofReal (r i ^ (m + 2)) ≤
      parabolicVolume m (⋃ i ∈ I', Metric.ball (p i) (δ i)) := by
    calc ∑ i ∈ I', ENNReal.ofReal (r i ^ (m + 2)) = ∑ i ∈ I', parabolicVolume m (Q i) := by
          simp only [hQvol]
      _ = parabolicVolume m (⋃ i ∈ I', Q i) :=
          (measure_biUnion_finset (hQd.set_pairwise _) fun i _ => hQm i).symm
      _ ≤ _ := measure_mono (iUnion₂_mono fun i _ => hQB i)
  -- A Vitali subfamily of disjoint balls whose fivefold enlargements cover.
  obtain ⟨u, huI, hudisj, hucover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun i => Metric.ball (p i) (δ i)) (I' : Set ι) δ 2 one_lt_two (fun i _ => (hδ i).le)
    (∑ i ∈ I', δ i) (fun i hi => Finset.single_le_sum (fun j _ => (hδ j).le) hi)
    (fun i _ => Metric.nonempty_ball.mpr (hδ i))
  have hufin : u.Finite := I'.finite_toSet.subset huI
  set U : Finset ι := hufin.toFinset with hU
  have hUu : ∀ {j}, j ∈ U ↔ j ∈ u := fun {j} => hufin.mem_toFinset
  have hUI : ∀ j ∈ U, j ∈ I' := fun j hj => huI (hUu.mp hj)
  have h3 : ⋃ i ∈ I', Metric.ball (p i) (δ i) ⊆ ⋃ j ∈ U, Metric.ball (p j) (5 * δ j) := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
    obtain ⟨j, hju, ⟨w, hwi, hwj⟩, hij⟩ := hucover i (Finset.mem_coe.mpr hi)
    refine mem_iUnion₂.mpr ⟨j, hUu.mpr hju, ?_⟩
    simp only [Metric.mem_ball] at hyi hwi hwj ⊢
    calc dist y (p j) ≤ dist y (p i) + dist (p i) w + dist w (p j) := dist_triangle4 _ _ _ _
      _ < δ i + δ i + δ j := by
          rw [dist_comm (p i) w]
          exact add_lt_add (add_lt_add hyi hwi) hwj
      _ ≤ 5 * δ j := by linarith
  -- One request of each selected cell.
  have hl : ∀ j ∈ I', ∃ l, (j, l) ∈ I := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨q.2, hq⟩
  choose! lsel hlsel using hl
  have hdisjS : (U : Set ι).PairwiseDisjoint fun j => S j (lsel j) := by
    intro j hj j' hj' hne
    exact Disjoint.mono (hSB _ _) (hSB _ _)
      (hudisj (hUu.mp (Finset.mem_coe.mp hj)) (hUu.mp (Finset.mem_coe.mp hj')) hne)
  have hball : ∀ j, parabolicVolume m (Metric.ball (p j) (5 * δ j)) ≤
      ENNReal.ofReal (hallRatio m c₁) * σ (S j (lsel j)) := by
    intro j
    have hδj := hδ j
    rw [parabolicVolume_ball _ _ (by positivity)]
    have e1 : 2 * omega m * ENNReal.ofReal (5 * δ j) ^ (m + 2) =
        ENNReal.ofReal (2 * (omega m).toReal * (5 * δ j) ^ (m + 2)) := by
      rw [ENNReal.ofReal_mul (p := 2 * (omega m).toReal) (by positivity),
        ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_toReal (omega_lt_top m).ne,
        ENNReal.ofReal_pow (p := 5 * δ j) (by positivity)]
      norm_num
    have e2 : ENNReal.ofReal (2 * (omega m).toReal * (5 * δ j) ^ (m + 2)) =
        ENNReal.ofReal (hallRatio m c₁) * ENNReal.ofReal (c₁ * δ j ^ (m + 2)) := by
      rw [← ENNReal.ofReal_mul hK0.le]
      congr 1
      unfold hallRatio
      field_simp
      try ring
    rw [e1, e2]
    gcongr
    exact hS j (lsel j)
  have h4 : parabolicVolume m (⋃ j ∈ U, Metric.ball (p j) (5 * δ j)) ≤
      ENNReal.ofReal (hallRatio m c₁) * σ (⋃ j ∈ U, S j (lsel j)) := by
    calc parabolicVolume m (⋃ j ∈ U, Metric.ball (p j) (5 * δ j))
        ≤ ∑ j ∈ U, parabolicVolume m (Metric.ball (p j) (5 * δ j)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ U, ENNReal.ofReal (hallRatio m c₁) * σ (S j (lsel j)) :=
          Finset.sum_le_sum fun j _ => hball j
      _ = ENNReal.ofReal (hallRatio m c₁) * ∑ j ∈ U, σ (S j (lsel j)) :=
          (Finset.mul_sum _ _ _).symm
      _ = ENNReal.ofReal (hallRatio m c₁) * σ (⋃ j ∈ U, S j (lsel j)) := by
          rw [measure_biUnion_finset hdisjS fun j _ => hSm _ _]
  have h5 : ⋃ j ∈ U, S j (lsel j) ⊆ ⋃ q ∈ I, S q.1 q.2 :=
    iUnion₂_subset fun j hj y hy => mem_iUnion₂.mpr ⟨(j, lsel j), hlsel j (hUI j hj), hy⟩
  calc ∑ q ∈ I, ENNReal.ofReal (r q.1 ^ (m + 2))
      ≤ ((m : ℝ≥0∞) + 1) * ∑ i ∈ I', ENNReal.ofReal (r i ^ (m + 2)) := h1
    _ ≤ ((m : ℝ≥0∞) + 1) *
          (ENNReal.ofReal (hallRatio m c₁) * σ (⋃ q ∈ I, S q.1 q.2)) := by
        gcongr
        calc ∑ i ∈ I', ENNReal.ofReal (r i ^ (m + 2))
            ≤ parabolicVolume m (⋃ i ∈ I', Metric.ball (p i) (δ i)) := h2
          _ ≤ parabolicVolume m (⋃ j ∈ U, Metric.ball (p j) (5 * δ j)) := measure_mono h3
          _ ≤ ENNReal.ofReal (hallRatio m c₁) * σ (⋃ j ∈ U, S j (lsel j)) := h4
          _ ≤ ENNReal.ofReal (hallRatio m c₁) * σ (⋃ q ∈ I, S q.1 q.2) :=
              mul_le_mul_of_nonneg_left (measure_mono h5) zero_le
    _ = ENNReal.ofReal (hallConst m c₁) * σ (⋃ q ∈ I, S q.1 q.2) := by
        rw [← mul_assoc, hallConst, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
          ENNReal.ofReal_one]

end Reservoirs

open Reservoirs

-- The input hypotheses keep their binder names.
set_option linter.unusedVariables false in
open Classical in
/-- **Whitney source allocation**: simultaneous
allocation to all Whitney holes, with constants `A, C_B, c₂` depending only on
`m, c, D, a, b`. The hypotheses `hA2a` and `hC` are finite real-capacity transport and
weak compactness of bounded densities (the statements proved by
`exists_transport_of_hall_condition_proof` and
`exists_weakly_convergent_density_subseq_proof`) at the universes of the target. -/
theorem exists_whitney_source_allocation_proof
    (hA2a : ∀ {J T : Type u} [Fintype J] [Fintype T]
      (adj : J → T → Prop) (w : J → ℝ) (κ : T → ℝ) (hw : ∀ j, 0 ≤ w j) (hκ : ∀ t, 0 ≤ κ t)
      (hH : ∀ I : Finset J,
        ∑ j ∈ I, w j ≤ ∑ t ∈ Finset.univ.filter (fun t => ∃ j ∈ I, adj j t), κ t),
      ∃ x : J → T → ℝ, (∀ j t, 0 ≤ x j t) ∧ (∀ j t, ¬ adj j t → x j t = 0) ∧
        (∀ j, ∑ t, x j t = w j) ∧ ∀ t, ∑ j, x j t ≤ κ t)
    (hC : ∀ {X : Type} [MeasurableSpace X]
      (σ : Measure X) [IsFiniteMeasure σ] [TopologicalSpace.SeparableSpace (Lp ℝ 1 σ)]
      (A : ℝ) (h : ℕ → X → ℝ) (hm : ∀ n, Measurable (h n))
      (hb : ∀ n x, 0 ≤ h n x ∧ h n x ≤ A),
      ∃ (φ : ℕ → ℕ) (h₀ : X → ℝ), StrictMono φ ∧ Measurable h₀ ∧ (∀ x, 0 ≤ h₀ x ∧ h₀ x ≤ A) ∧
        ∀ ψ : X → ℝ, Integrable ψ σ →
          Tendsto (fun n => ∫ x, h (φ n) x * ψ x ∂σ) atTop (𝓝 (∫ x, h₀ x * ψ x ∂σ)))
    (m : ℕ) (c D a b : ℝ) (hc : 0 < c) :
    ∃ A C_B c₂ : ℝ, 0 < A ∧ 0 < C_B ∧ 0 < c₂ ∧ ∀ {ι : Type u} [Countable ι]
      {F₀ : Set (Space m)} (W : WhitneyData m ι F₀ D a), IsCompact F₀ → F₀.Nonempty →
      (∀ j, Metric.infDist (W.center j) F₀ ≤ b * W.radius j) →
      ∀ σ : Measure (Space m), σ ≤ parabolicVolume m →
      (∀ x ∈ F₀, ∀ r : ℝ, 0 < r → ENNReal.ofReal (c * r ^ (m + 2)) ≤ σ (Metric.ball x r)) →
      Nonempty (WhitneySourceAllocation W σ A C_B c₂) := by
  obtain ⟨c₁, c₂', hc₁, hc₂', hres⟩ := exists_reservoir_sets_proof m c hc
  refine ⟨hallConst m c₁, |D| + |b| + 1, c₂' * (|D| + |b| + 1), hallConst_pos hc₁,
    by positivity, mul_pos hc₂' (by positivity), ?_⟩
  intro ι _ F₀ W hF₀ hne hb σ hσ hdens
  set C_B : ℝ := |D| + |b| + 1 with hC_B
  have hC_Bpos : 0 < C_B := by positivity
  -- Nearest anchors.
  have hanc : ∀ i, ∃ y ∈ F₀, Metric.infDist (W.center i) F₀ = dist (W.center i) y :=
    fun i => hF₀.exists_infDist_eq_dist hne (W.center i)
  choose anchor hanchor hdist using hanc
  -- Reservoir sets in the balls `P(a_i, C_B r_i)`.
  have hδ : ∀ i, 0 < C_B * W.radius i := fun i => mul_pos hC_Bpos (W.radius_pos i)
  choose S hS1 hS2 using fun i => hres (anchor i) (C_B * W.radius i) σ (hδ i) hσ
    (hdens (anchor i) (hanchor i) _ (hδ i))
  -- Cells lie in the reservoir balls.
  have hQB : ∀ i, W.cell i ⊆ Metric.ball (anchor i) (C_B * W.radius i) := by
    intro i q hq
    have h1 : dist q (W.center i) ≤ D * W.radius i :=
      Metric.mem_closedBall.mp (W.cell_subset i hq)
    have h2 : dist (W.center i) (anchor i) ≤ b * W.radius i := by
      rw [← hdist i]
      exact hb i
    have hr := W.radius_pos i
    rw [Metric.mem_ball]
    calc dist q (anchor i) ≤ dist q (W.center i) + dist (W.center i) (anchor i) :=
          dist_triangle _ _ _
      _ ≤ D * W.radius i + b * W.radius i := add_le_add h1 h2
      _ < C_B * W.radius i := by
          rw [hC_B]
          nlinarith [le_abs_self D, le_abs_self b]
  -- The countable Hall allocation.
  set w : ι × Fin (m + 1) → ℝ≥0 := fun q => (W.radius q.1 ^ (m + 2)).toNNReal with hwdef
  have hwpos : ∀ q, 0 < w q := fun q => Real.toNNReal_pos.mpr (pow_pos (W.radius_pos _) _)
  set A : ℝ≥0 := (hallConst m c₁).toNNReal with hAdef
  have hApos : 0 < A := Real.toNNReal_pos.mpr (hallConst_pos hc₁)
  have hSfin : ∀ q : ι × Fin (m + 1), σ (S q.1 q.2) < ⊤ := fun q =>
    ((measure_mono (hS1 q.1 q.2).2.1).trans (Measure.le_iff'.mp hσ _)).trans_lt
      MeasureTheory.measure_ball_lt_top
  have hsep : ∀ q : ι × Fin (m + 1),
      TopologicalSpace.SeparableSpace (Lp ℝ 1 (σ.restrict (S q.1 q.2))) := by
    intro q
    have : IsFiniteMeasure (σ.restrict (S q.1 q.2)) :=
      isFiniteMeasure_restrict.mpr (hSfin q).ne
    have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
    have : SFinite (σ.restrict (S q.1 q.2)) := inferInstance
    have : MeasureTheory.IsSeparable (σ.restrict (S q.1 q.2)) := inferInstance
    have : SecondCountableTopology (Lp ℝ 1 (σ.restrict (S q.1 q.2))) :=
      MeasureTheory.Lp.SecondCountableTopology
    infer_instance
  have hH : ∀ I : Finset (ι × Fin (m + 1)),
      ∑ q ∈ I, (w q : ℝ≥0∞) ≤ A * σ (⋃ q ∈ I, S q.1 q.2) := fun I =>
    hall_inequality_of_reservoirs σ W.cell W.measurableSet_cell W.pairwise_disjoint W.radius
      W.volume_cell anchor (fun i => C_B * W.radius i) hδ hQB S (fun i l => (hS1 i l).1)
      (fun i l => (hS1 i l).2.1) hc₁ (fun i l => (hS1 i l).2.2) I
  obtain ⟨h, hmeas, hzero, hint, hsum⟩ := HallAllocation.exists_countable_hall_allocation_proof
    (HallAllocation.hall_allocation_iff_proof hA2a) hC σ (fun q => S q.1 q.2)
    (fun q => (hS1 q.1 q.2).1) hSfin hsep w hwpos A hApos hH
  refine ⟨{ anchor := anchor
            anchor_mem := hanchor
            dist_anchor := fun i => (hdist i).symm
            reservoir := S
            measurableSet_reservoir := fun i l => (hS1 i l).1
            reservoir_subset := fun i l => (hS1 i l).2.1
            density := fun i l => h (i, l)
            measurable_density := fun i l => hmeas (i, l)
            density_eq_zero := fun i l => hzero (i, l)
            lintegral_density := fun i l => hint (i, l)
            sum_density_le := hsum
            simplex := ?_ }⟩
  -- The allocated barycenters are probability barycenters on the reservoirs.
  intro i v
  set rk : ℝ := W.radius i ^ (m + 2) with hrk
  have hrk0 : 0 < rk := pow_pos (W.radius_pos i) _
  have hlt : ∀ l, ∀ᵐ x ∂σ, h (i, l) x < ⊤ := fun l =>
    ae_lt_top (hmeas (i, l)) (by rw [hint (i, l)]; exact ENNReal.coe_ne_top)
  have hρ : ∀ l, IsProbabilityMeasure ((ENNReal.ofReal rk)⁻¹ • σ.withDensity (h (i, l))) ∧
      ((ENNReal.ofReal rk)⁻¹ • σ.withDensity (h (i, l))) (S i l)ᶜ = 0 := by
    intro l
    refine ⟨⟨?_⟩, ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ, hint (i, l)]
      exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hrk0).ne' ENNReal.ofReal_ne_top
    · rw [Measure.smul_apply, smul_eq_mul]
      have hnull : σ.withDensity (h (i, l)) (S i l)ᶜ = 0 := by
        rw [withDensity_apply_eq_zero' (hmeas (i, l)).aemeasurable]
        have : {x | h (i, l) x ≠ 0} ∩ (S i l)ᶜ = ∅ := by
          refine Set.subset_empty_iff.mp ?_
          rintro x ⟨hx, hxS⟩
          exact (hx (hzero (i, l) x hxS)).elim
        rw [this, measure_empty]
      rw [hnull, mul_zero]
  have hbary : ∀ l, ∫ z, z.1 ∂((ENNReal.ofReal rk)⁻¹ • σ.withDensity (h (i, l))) =
      rk⁻¹ • ∫ x, (h (i, l) x).toReal • x.1 ∂σ := by
    intro l
    rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul (hmeas (i, l))
      (hlt l), ENNReal.toReal_inv, ENNReal.toReal_ofReal hrk0.le]
  have key := hS2 i (fun l => (ENNReal.ofReal rk)⁻¹ • σ.withDensity (h (i, l))) hρ v
  calc c₂' * C_B * W.radius i * ‖WithLp.toLp 2 v‖
      = c₂' * (C_B * W.radius i) * ‖WithLp.toLp 2 v‖ := by ring
    _ ≤ _ := by simpa only [hbary] using key

end ParabolicRectifiability
