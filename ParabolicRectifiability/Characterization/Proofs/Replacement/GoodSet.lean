import ParabolicRectifiability.Characterization.Proofs.Replacement.Statements

/-! # The good set: closedness, nonemptiness and bad mass

Proof of `RpGoodSetStatement`. Fivefold selection enters as the statement's own first
hypothesis.

* closedness of `G_A`: `Γ` is closed, and for `z ∈ closure G_A` and `r > 0` every ball
  `P(z, r - r/(m+2))` lies in a ball `P(w, r)` with `w ∈ G_A`; continuity from below
  (`Monotone.measure_iUnion`) gives `ν(P(z,r)) ≤ A r^k` (lower semicontinuity of
  `z ↦ ν(P(z,r))`);
* bad mass: every `z ∈ Ω_A` has a radius `r_z > 0` with `A r_z^k < ν(P(z,r_z)) ≤ ν(X) < ∞`;
  since `k ≥ 1` the radii are bounded; fivefold selection gives a countable disjoint subfamily whose
  fivefold dilates cover `Ω_A`, and upper ADR at the centres gives
  `σ(Ω_A) ≤ (C 5^k / A) Σ ν(P(z_j,r_j)) ≤ (C 5^k / A) ν(Γ)`;
* nonempty: `σ(Γ) = ∞` (lower ADR, `k > 0`, `σ(Γᶜ) = 0`), while `σ(Ω_A) < ∞`.
-/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.ReplacementTree

open ParabolicRectifiability.Foundations

/-- `σ(Γᶜ) = 0` for an ADR carrier (inner regularity and `supp σ = Γ`). -/
theorem b3rpg_compl_null {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hΓ : IsADRCarrier k c C Γ σ) : σ Γᶜ = 0 := by
  have := hΓ.innerRegular
  rw [← hΓ.support_eq]
  exact Measure.measure_compl_support_of_innerRegular

/-- A measure carried by `Γ` gives every set at most the mass of `Γ`. -/
theorem b3rpg_le_carrier {n : ℕ} {Γ : Set (Space n)} {μ : Measure (Space n)}
    (hμ : μ Γᶜ = 0) (s : Set (Space n)) : μ s ≤ μ Γ :=
  calc μ s ≤ μ (Γ ∪ Γᶜ) := measure_mono (by rw [union_compl_self]; exact subset_univ _)
    _ ≤ μ Γ + μ Γᶜ := measure_union_le _ _
    _ = μ Γ := by rw [hμ, add_zero]

/-- The open ball `P(z,r)` is the increasing union of the balls `P(z, r - r/(m+2))`. -/
theorem b3rpg_ball_eq_iUnion {n : ℕ} (z : Space n) {r : ℝ} (hr : 0 < r) :
    Metric.ball z r = ⋃ m : ℕ, Metric.ball z (r - r / ((m : ℝ) + 2)) := by
  apply Subset.antisymm
  · intro y hy
    rw [Metric.mem_ball] at hy
    have hε : 0 < r - dist y z := sub_pos.2 hy
    obtain ⟨m, hm⟩ := exists_nat_gt (r / (r - dist y z))
    refine mem_iUnion.2 ⟨m, ?_⟩
    rw [Metric.mem_ball]
    have h1 : r < (m : ℝ) * (r - dist y z) := (div_lt_iff₀ hε).1 hm
    have h2 : r / ((m : ℝ) + 2) < r - dist y z := by
      rw [div_lt_iff₀ (by positivity)]
      have h3 : (r - dist y z) * ((m : ℝ) + 2) = (m : ℝ) * (r - dist y z) + 2 * (r - dist y z) := by
        ring
      rw [h3]
      linarith
    linarith
  · refine iUnion_subset fun m => Metric.ball_subset_ball ?_
    have : 0 ≤ r / ((m : ℝ) + 2) := by positivity
    linarith

/-- **Closedness of `G_A`** (lower semicontinuity of `z ↦ ν(P(z,r))`). -/
theorem b3rpg_isClosed {n k : ℕ} {Γ : Set (Space n)} (hΓc : IsClosed Γ)
    (ν : Measure (Space n)) (A : ℝ) : IsClosed (adrGoodSet Γ ν k A) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  have hzΓ : z ∈ Γ := hΓc.closure_subset_iff.2 (fun w hw => hw.1) hz
  refine ⟨hzΓ, fun r hr => ?_⟩
  have hmono : Monotone fun m : ℕ => Metric.ball z (r - r / ((m : ℝ) + 2)) := by
    intro a b hab
    apply Metric.ball_subset_ball
    have hab' : (a : ℝ) + 2 ≤ (b : ℝ) + 2 := by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have : r / ((b : ℝ) + 2) ≤ r / ((a : ℝ) + 2) :=
      div_le_div_of_nonneg_left hr.le (by positivity) hab'
    linarith
  rw [b3rpg_ball_eq_iUnion z hr, hmono.measure_iUnion]
  refine iSup_le fun m => ?_
  have hδ : 0 < r / ((m : ℝ) + 2) := by positivity
  obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.1 hz _ hδ
  calc ν (Metric.ball z (r - r / ((m : ℝ) + 2))) ≤ ν (Metric.ball w r) := by
        apply measure_mono
        apply Metric.ball_subset_ball'
        linarith
    _ ≤ ENNReal.ofReal (A * r ^ k) := hw.2 r hr

/-- **Bad-mass estimate** with the sharp constant: `σ(Ω_A) ≤ (C 5^k / A) ν(Γ)`, from fivefold selection. -/
theorem b3rpg_badMass (h5 : FivefoldSelectionStatement) {n k : ℕ} {c C : ℝ}
    {Γ : Set (Space n)} {σ : Measure (Space n)} (hΓ : IsADRCarrier k c C Γ σ)
    (ν : Measure (Space n)) [IsFiniteMeasure ν] (hν : ν Γᶜ = 0) {A : ℝ} (hA : 0 < A) :
    σ (Γ \ adrGoodSet Γ ν k A) ≤ ENNReal.ofReal (C * 5 ^ k / A) * ν Γ := by
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Set (Space n), Ω = Γ \ adrGoodSet Γ ν k A := ⟨_, rfl⟩
  rw [← hΩ]
  have hmem : ∀ z : Ω, (z : Space n) ∈ Γ \ adrGoodSet Γ ν k A := fun z => hΩ ▸ z.2
  have hbad : ∀ z : Ω, ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal (A * r ^ k) < ν (Metric.ball (z : Space n) r) := by
    intro z
    have hzΓ : (z : Space n) ∈ Γ := (hmem z).1
    have hng : (z : Space n) ∉ adrGoodSet Γ ν k A := (hmem z).2
    by_contra hcon
    push Not at hcon
    exact hng ⟨hzΓ, fun r hr => hcon r hr⟩
  choose rad hrad hlt using hbad
  have hk : k ≠ 0 := hΓ.dimension_pos.ne'
  have hbound : ∀ z : Ω, rad z ≤ max 1 ((ν univ).toReal / A) := by
    intro z
    have h1 : ENNReal.ofReal (A * rad z ^ k) < ENNReal.ofReal (ν univ).toReal := by
      rw [ENNReal.ofReal_toReal (measure_ne_top ν univ)]
      exact (hlt z).trans_le (measure_mono (subset_univ _))
    have h2 : A * rad z ^ k < (ν univ).toReal := (ENNReal.ofReal_lt_ofReal_iff'.1 h1).1
    rcases le_or_gt (rad z) 1 with h | h
    · exact h.trans (le_max_left _ _)
    · have h3 : rad z ≤ rad z ^ k := le_self_pow₀ h.le hk
      have h4 : rad z ^ k < (ν univ).toReal / A := by
        rw [lt_div_iff₀ hA]
        linarith
      exact (h3.trans h4.le).trans (le_max_right _ _)
  obtain ⟨J, hJc, hJd, hJcov⟩ :=
    h5 (Space n) Ω Subtype.val rad hrad ⟨_, hbound⟩
  have hcov : Ω ⊆ ⋃ j ∈ J, Metric.ball (j : Space n) (5 * rad j) := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := hJcov ⟨x, hx⟩
    exact mem_biUnion hj hxj
  have hK : 0 ≤ C * 5 ^ k / A :=
    div_nonneg (mul_nonneg hΓ.upper_pos.le (by positivity)) hA.le
  have hA0 : A ≠ 0 := hA.ne'
  have hterm : ∀ j : Ω, σ (Metric.ball (j : Space n) (5 * rad j)) ≤
      ENNReal.ofReal (C * 5 ^ k / A) * ν (Metric.ball (j : Space n) (rad j)) := by
    intro j
    have hjΓ : (j : Space n) ∈ Γ := (hmem j).1
    calc σ (Metric.ball (j : Space n) (5 * rad j)) ≤ ENNReal.ofReal (C * (5 * rad j) ^ k) :=
          hΓ.upper _ hjΓ _ (by linarith [hrad j])
      _ = ENNReal.ofReal (C * 5 ^ k / A) * ENNReal.ofReal (A * rad j ^ k) := by
          rw [← ENNReal.ofReal_mul hK]
          congr 1
          rw [mul_pow]
          field_simp
      _ ≤ ENNReal.ofReal (C * 5 ^ k / A) * ν (Metric.ball (j : Space n) (rad j)) := by
          exact mul_le_mul_right (hlt j).le _
  have hdisj : ν (⋃ j ∈ J, Metric.ball (j : Space n) (rad j)) =
      ∑' j : J, ν (Metric.ball ((j : Ω) : Space n) (rad j)) :=
    measure_biUnion hJc hJd (fun j _ => Metric.isOpen_ball.measurableSet)
  calc σ Ω ≤ σ (⋃ j ∈ J, Metric.ball (j : Space n) (5 * rad j)) := measure_mono hcov
    _ ≤ ∑' j : J, σ (Metric.ball ((j : Ω) : Space n) (5 * rad j)) :=
        measure_biUnion_le σ hJc _
    _ ≤ ∑' j : J, ENNReal.ofReal (C * 5 ^ k / A) * ν (Metric.ball ((j : Ω) : Space n) (rad j)) :=
        ENNReal.tsum_le_tsum fun j => hterm j
    _ = ENNReal.ofReal (C * 5 ^ k / A) * ν (⋃ j ∈ J, Metric.ball (j : Space n) (rad j)) := by
        rw [ENNReal.tsum_mul_left, hdisj]
    _ ≤ ENNReal.ofReal (C * 5 ^ k / A) * ν Γ := by
        exact mul_le_mul_right (b3rpg_le_carrier hν _) _

/-- `σ(Γ) = ∞` for an ADR carrier of positive dimension. -/
theorem b3rpg_measure_carrier_eq_top {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)}
    {σ : Measure (Space n)} (hΓ : IsADRCarrier k c C Γ σ) : σ Γ = ⊤ := by
  obtain ⟨z, hz⟩ := hΓ.nonempty
  by_contra hne
  have hc := hΓ.lower_pos
  have hr1 : (1 : ℝ) ≤ max 1 (((σ Γ).toReal + 1) / c) := le_max_left _ _
  have hr0 : (0 : ℝ) < max 1 (((σ Γ).toReal + 1) / c) := lt_of_lt_of_le one_pos hr1
  have h1 : ENNReal.ofReal (c * (max 1 (((σ Γ).toReal + 1) / c)) ^ k) ≤
      ENNReal.ofReal (σ Γ).toReal := by
    rw [ENNReal.ofReal_toReal hne]
    exact (hΓ.lower z hz _ hr0).trans (b3rpg_le_carrier (b3rpg_compl_null hΓ) _)
  have h2 : c * (max 1 (((σ Γ).toReal + 1) / c)) ^ k ≤ (σ Γ).toReal :=
    (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h1
  have h3 : max 1 (((σ Γ).toReal + 1) / c) ≤ (max 1 (((σ Γ).toReal + 1) / c)) ^ k :=
    le_self_pow₀ hr1 hΓ.dimension_pos.ne'
  have h4 : ((σ Γ).toReal + 1) / c ≤ max 1 (((σ Γ).toReal + 1) / c) := le_max_right _ _
  have h5 : (σ Γ).toReal + 1 ≤ max 1 (((σ Γ).toReal + 1) / c) * c := (div_le_iff₀ hc).1 h4
  have h6 : c * max 1 (((σ Γ).toReal + 1) / c) ≤ c * (max 1 (((σ Γ).toReal + 1) / c)) ^ k :=
    mul_le_mul_of_nonneg_left h3 hc.le
  linarith

/-- The good set: `RpGoodSetStatement`. -/
theorem b3_rp_goodSet_proof : RpGoodSetStatement := by
  intro h5 n _hn k c C Γ σ hΓ ν hνfin hν A hA
  have hbad : σ (Γ \ adrGoodSet Γ ν k A) ≤
      ENNReal.ofReal (max (C * 5 ^ k) 1 / A) * ν Γ :=
    (b3rpg_badMass h5 hΓ ν hν hA).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (le_max_left _ _) hA.le)) _)
  refine ⟨b3rpg_isClosed hΓ.isClosed ν A, ?_, hbad⟩
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  rw [hne, sdiff_empty, b3rpg_measure_carrier_eq_top hΓ] at hbad
  exact absurd hbad (not_le.2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν Γ)))

end ParabolicRectifiability.Characterization.ReplacementTree
