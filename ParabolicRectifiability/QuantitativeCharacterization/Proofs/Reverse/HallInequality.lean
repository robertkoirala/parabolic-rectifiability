import ParabolicRectifiability.QuantitativeCharacterization.Statements.ReverseBound

/-! # The capacitated Hall inequality

Proof of `d2_hall_inequality : HallInequalityStatement` under the name `d2_hall_inequality_proof`.

Constants: `Ch = 2(3 + 2C₀)` and `D₁ = A A_ref Ch^k`; the cell enlargement radius is
`R_j* = (3 + 2C₀) s_j`.

Proof idea: Mathlib's radius-aware Vitali selection
`Vitali.exists_disjoint_subfamily_covering_enlargement` (with `τ = 2`, `δ = s`) applied to the
balls `P(g_j, s_j)`, `j ∈ I`, gives a disjoint subfamily `S ⊆ I` such that every `P(g_i, s_i)`
meets some `P(g_j, s_j)`, `j ∈ S`, with `s_i ≤ 2 s_j`; then `Q_i ⊆ P(g_j, R_j*)`. Each
`P(g_j, R_j*)` of positive mass contains a point `b ∈ supp μ` (the support is conull on the
hereditarily Lindelöf `Space n`, so no regularity of `μ` is used) and lies in `P(b, Ch s_j)`;
the growth hypothesis bounds it by `A (Ch s_j)^k`, and lower ADR at `g_j ∈ Γ = supp σ` gives
`s_j^k ≤ A_ref σ(P(g_j, s_j))`. The selected balls are disjoint and `σ(Γᶜ) = 0`. The fivefold
selection statement is not used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization.ReverseTree

open ParabolicRectifiability.Foundations

/-- Radius-aware Vitali selection on a finite family of open balls of positive radii: a
disjoint subfamily `S ⊆ I` such that every ball of `I` meets a selected ball whose radius is at
least half its own. -/
theorem d2hall_select {α ι : Type*} [PseudoMetricSpace α] (g : ι → α) (s : ι → ℝ)
    (hs : ∀ j, 0 < s j) (I : Finset ι) :
    ∃ S : Finset ι, S ⊆ I ∧
      (S : Set ι).PairwiseDisjoint (fun j => Metric.ball (g j) (s j)) ∧
      ∀ i ∈ I, ∃ j ∈ S, dist (g i) (g j) < s i + s j ∧ s i ≤ 2 * s j := by
  classical
  obtain ⟨u, hut, hud, hu⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun j => Metric.ball (g j) (s j)) (I : Set ι) s 2 one_lt_two
    (fun a _ => (hs a).le) (∑ j ∈ I, s j)
    (fun a ha => Finset.single_le_sum (fun j _ => (hs j).le) (Finset.mem_coe.1 ha))
    (fun a _ => ⟨g a, Metric.mem_ball_self (hs a)⟩)
  refine ⟨I.filter (· ∈ u), Finset.filter_subset _ _, ?_, ?_⟩
  · intro i hi j hj hij
    exact hud (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
      (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).2 hij
  · intro i hi
    obtain ⟨j, hju, hne, hle⟩ := hu i (Finset.mem_coe.2 hi)
    exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_coe.1 (hut hju), hju⟩,
      Metric.dist_lt_add_of_nonempty_ball_inter_ball hne, hle⟩

/-- The enlarged cell ball `P(g_j, (3 + 2C₀) s_j)` has `μ`-mass at most `A (Ch s_j)^k`,
`Ch = 2(3 + 2C₀)`: if it has positive mass it contains a point `b ∈ supp μ`, and it lies in
`P(b, Ch s_j)`, whose centre and radius are admissible for the growth hypothesis. -/
theorem d2hall_enlarged_ball_le {n k : ℕ} {C₀ A : ℝ} (hC₀ : 1 ≤ C₀)
    (μ : Measure (Space n)) (g : Space n) (s : ℝ) (hs : 0 < s)
    (hgrowth : ∀ b ∈ μ.support ∩ Metric.ball g (2 * (3 + 2 * C₀) * s), ∀ t : ℝ, 0 < t →
      t ≤ 2 * (3 + 2 * C₀) * s → μ (Metric.ball b t) ≤ ENNReal.ofReal (A * t ^ k)) :
    μ (Metric.ball g ((3 + 2 * C₀) * s)) ≤
      ENNReal.ofReal (A * (2 * (3 + 2 * C₀) * s) ^ k) := by
  rcases eq_zero_or_pos (μ (Metric.ball g ((3 + 2 * C₀) * s))) with h0 | hpos
  · rw [h0]
    exact zero_le
  obtain ⟨b, hbB, hbS⟩ := Measure.nonempty_inter_support_of_pos hpos
  have hR : 0 < (3 + 2 * C₀) * s := by
    have : 0 < 3 + 2 * C₀ := by linarith
    exact mul_pos this hs
  have hb : dist b g < (3 + 2 * C₀) * s := Metric.mem_ball.1 hbB
  have hbig : b ∈ Metric.ball g (2 * (3 + 2 * C₀) * s) := by
    rw [Metric.mem_ball]
    linarith
  have hsub : Metric.ball g ((3 + 2 * C₀) * s) ⊆ Metric.ball b (2 * (3 + 2 * C₀) * s) := by
    apply Metric.ball_subset_ball'
    rw [dist_comm]
    linarith
  have ht : 0 < 2 * (3 + 2 * C₀) * s := by linarith
  exact (measure_mono hsub).trans (hgrowth b ⟨hbS, hbig⟩ _ ht le_rfl)

/-- The growth bound of an enlarged ball is at most `D₁ σ(P(g_j, s_j))`,
`D₁ = A A_ref Ch^k`, by lower ADR at `g_j ∈ supp σ`. -/
theorem d2hall_growth_le_ref {n k : ℕ} {Aref C₀ A : ℝ} (hAref : 1 ≤ Aref) (hC₀ : 1 ≤ C₀)
    (hA : 1 ≤ A) {σ : Measure (Space n)} (hADR : IsADR Aref k σ) (g : Space n)
    (hg : g ∈ σ.support) (s : ℝ) (hs : 0 < s) :
    ENNReal.ofReal (A * (2 * (3 + 2 * C₀) * s) ^ k) ≤
      ENNReal.ofReal (A * Aref * (2 * (3 + 2 * C₀)) ^ k) * σ (Metric.ball g s) := by
  have hA0 : Aref ≠ 0 := (lt_of_lt_of_le one_pos hAref).ne'
  have hCh : 0 ≤ 2 * (3 + 2 * C₀) := by linarith
  have hD : 0 ≤ A * Aref * (2 * (3 + 2 * C₀)) ^ k := by
    have h1 : 0 ≤ A := by linarith
    have h2 : 0 ≤ Aref := by linarith
    exact mul_nonneg (mul_nonneg h1 h2) (pow_nonneg hCh k)
  have heq : A * (2 * (3 + 2 * C₀) * s) ^ k =
      A * Aref * (2 * (3 + 2 * C₀)) ^ k * (Aref⁻¹ * s ^ k) := by
    calc A * (2 * (3 + 2 * C₀) * s) ^ k
        = A * (2 * (3 + 2 * C₀)) ^ k * s ^ k * (Aref * Aref⁻¹) := by
          rw [mul_inv_cancel₀ hA0, mul_pow (2 * (3 + 2 * C₀)) s k]; ring
      _ = A * Aref * (2 * (3 + 2 * C₀)) ^ k * (Aref⁻¹ * s ^ k) := by ring
  rw [heq, ENNReal.ofReal_mul hD]
  gcongr
  exact (hADR g hg s hs).1

/-- The selected disjoint balls carry at most the reference mass of the union of the target
sets `Γ ∩ P̄(g_i, s_i)`, `i ∈ I`, because `σ(Γᶜ) = 0`. -/
theorem d2hall_selected_le {n : ℕ} {σ : Measure (Space n)} {Γ : Set (Space n)}
    (hsupp : σ.support = Γ) {ι : Type} (g : ι → Space n) (s : ι → ℝ) {I S : Finset ι}
    (hSI : S ⊆ I)
    (hSd : (S : Set ι).PairwiseDisjoint (fun j => Metric.ball (g j) (s j))) :
    ∑ j ∈ S, σ (Metric.ball (g j) (s j)) ≤
      σ (⋃ j ∈ I, Γ ∩ Metric.closedBall (g j) (s j)) := by
  have hnull : σ Γᶜ = 0 := by
    rw [← hsupp]
    exact Measure.measure_compl_support
  calc ∑ j ∈ S, σ (Metric.ball (g j) (s j))
      = σ (⋃ j ∈ S, Metric.ball (g j) (s j)) :=
        (measure_biUnion_finset hSd (fun j _ => Metric.isOpen_ball.measurableSet)).symm
    _ ≤ σ ((⋃ j ∈ I, Γ ∩ Metric.closedBall (g j) (s j)) ∪ Γᶜ) := by
        apply measure_mono
        intro y hy
        obtain ⟨j, hjS, hyj⟩ := mem_iUnion₂.1 hy
        by_cases hyΓ : y ∈ Γ
        · exact Or.inl (mem_iUnion₂.2 ⟨j, hSI hjS, hyΓ, Metric.ball_subset_closedBall hyj⟩)
        · exact Or.inr hyΓ
    _ ≤ σ (⋃ j ∈ I, Γ ∩ Metric.closedBall (g j) (s j)) + σ Γᶜ := measure_union_le _ _
    _ = σ (⋃ j ∈ I, Γ ∩ Metric.closedBall (g j) (s j)) := by rw [hnull, add_zero]

/-- **The capacitated Hall inequality**  with explicit constants
`Ch = 2(3 + 2C₀)` and `D₁ = A A_ref Ch^k`, for one finite demand set `I`. -/
theorem d2hall_finite_bound {n k : ℕ} {Aref C₀ A : ℝ} (hAref : 1 ≤ Aref) (hC₀ : 1 ≤ C₀)
    (hA : 1 ≤ A) {μ σ : Measure (Space n)} {Γ : Set (Space n)} (hsupp : σ.support = Γ)
    (hADR : IsADR Aref k σ) {ι : Type} {Q : ι → Set (Space n)} {g : ι → Space n}
    {s : ι → ℝ} (hQm : ∀ j, MeasurableSet (Q j))
    (hQd : Pairwise fun i j => Disjoint (Q i) (Q j)) (hg : ∀ j, g j ∈ Γ)
    (hs : ∀ j, 0 < s j) (hQsub : ∀ j, Q j ⊆ Metric.ball (g j) (C₀ * s j))
    (hgrowth : ∀ j, ∀ b ∈ μ.support ∩ Metric.ball (g j) (2 * (3 + 2 * C₀) * s j), ∀ t : ℝ,
      0 < t → t ≤ 2 * (3 + 2 * C₀) * s j → μ (Metric.ball b t) ≤ ENNReal.ofReal (A * t ^ k))
    (I : Finset ι) :
    ∑ j ∈ I, μ (Q j) ≤ ENNReal.ofReal (A * Aref * (2 * (3 + 2 * C₀)) ^ k) *
      σ (⋃ j ∈ I, Γ ∩ Metric.closedBall (g j) (s j)) := by
  obtain ⟨S, hSI, hSd, hcov⟩ := d2hall_select g s hs I
  -- every source cell of `I` lies in a fixed enlargement of a selected ball
  have hcell : ∀ i ∈ I, ∃ j ∈ S, Q i ⊆ Metric.ball (g j) ((3 + 2 * C₀) * s j) := by
    intro i hi
    obtain ⟨j, hjS, hdist, hle⟩ := hcov i hi
    refine ⟨j, hjS, fun y hy => ?_⟩
    have hy' : dist y (g i) < C₀ * s i := Metric.mem_ball.1 (hQsub i hy)
    have hC : C₀ * s i ≤ C₀ * (2 * s j) :=
      mul_le_mul_of_nonneg_left hle (by linarith)
    rw [Metric.mem_ball]
    calc dist y (g j) ≤ dist y (g i) + dist (g i) (g j) := dist_triangle _ _ _
      _ < C₀ * s i + (s i + s j) := add_lt_add hy' hdist
      _ ≤ (3 + 2 * C₀) * s j := by linarith
  have hQdisj : (I : Set ι).PairwiseDisjoint Q := fun i _ j _ hij => hQd hij
  calc ∑ j ∈ I, μ (Q j)
      = μ (⋃ j ∈ I, Q j) := (measure_biUnion_finset hQdisj (fun j _ => hQm j)).symm
    _ ≤ μ (⋃ j ∈ S, Metric.ball (g j) ((3 + 2 * C₀) * s j)) := by
        apply measure_mono
        intro y hy
        obtain ⟨i, hiI, hyi⟩ := mem_iUnion₂.1 hy
        obtain ⟨j, hjS, hsub⟩ := hcell i hiI
        exact mem_iUnion₂.2 ⟨j, hjS, hsub hyi⟩
    _ ≤ ∑ j ∈ S, μ (Metric.ball (g j) ((3 + 2 * C₀) * s j)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ S, ENNReal.ofReal (A * Aref * (2 * (3 + 2 * C₀)) ^ k) *
          σ (Metric.ball (g j) (s j)) := by
        apply Finset.sum_le_sum
        intro j _
        exact (d2hall_enlarged_ball_le hC₀ μ (g j) (s j) (hs j) (hgrowth j)).trans
          (d2hall_growth_le_ref hAref hC₀ hA hADR (g j) (by rw [hsupp]; exact hg j) (s j) (hs j))
    _ = ENNReal.ofReal (A * Aref * (2 * (3 + 2 * C₀)) ^ k) *
          ∑ j ∈ S, σ (Metric.ball (g j) (s j)) := (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal (A * Aref * (2 * (3 + 2 * C₀)) ^ k) *
          σ (⋃ j ∈ I, Γ ∩ Metric.closedBall (g j) (s j)) :=
        by gcongr; exact d2hall_selected_le hsupp g s hSI hSd

/-- **Proof of the statement `d2_hall_inequality`** (`HallInequalityStatement`), with
`Ch = 2(3 + 2C₀)` and `D₁ = A A_ref Ch^k`. -/
theorem d2_hall_inequality_proof : HallInequalityStatement := by
  intro n _hn k _hk _hkn Aref hAref C₀ hC₀
  refine ⟨2 * (3 + 2 * C₀), by linarith, ?_⟩
  intro A hA
  refine ⟨A * Aref * (2 * (3 + 2 * C₀)) ^ k, ?_, ?_⟩
  · have h1 : 0 < A := by linarith
    have h2 : 0 < Aref := by linarith
    have h3 : 0 < 2 * (3 + 2 * C₀) := by linarith
    exact mul_pos (mul_pos h1 h2) (pow_pos h3 k)
  · intro μ σ Γ hsupp hADR ι Q g s hQm hQd hg hs hQsub hgrowth I
    exact d2hall_finite_bound hAref hC₀ hA hsupp hADR hQm hQd hg hs hQsub hgrowth I

end ParabolicRectifiability.QuantitativeCharacterization.ReverseTree
