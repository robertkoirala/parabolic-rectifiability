import ParabolicRectifiability.QuantitativeCharacterization.Statements.ReverseBound

/-! # The on-carrier comparison `μ⌊(Γ ∩ P(c,ρ)) ≤ D σ`

Proof of `d2_on_carrier : OnCarrierStatement` under the name `d2_on_carrier_proof`.

Constant: `D = 3^k A A_ref`.

Proof idea: fix a Borel `E` and put `F = E ∩ Γ ∩ P(c,ρ)`. For an open `U ⊇ F`, the
points of `F` outside `supp μ` are `μ`-null. At every remaining point `v` choose
`0 < s_v ≤ ρ/3` with `P(v,s_v) ⊆ U ∩ P(c,ρ)`. Mathlib's radius-aware Vitali selection
`Vitali.exists_disjoint_subfamily_covering_enlargement` (`τ = 2`) gives a disjoint subfamily,
countable by separability (`Set.PairwiseDisjoint.countable_of_isOpen`), whose balls
`P(v_j, 3 s_j)` contain every remaining point. The growth hypothesis (centre `v_j`, radius
`3 s_j ≤ ρ`) and lower ADR at `v_j ∈ Γ = supp σ` give
`μ(F) ≤ 3^k A A_ref Σ_j σ(P(v_j,s_j)) ≤ 3^k A A_ref σ(U ∩ P(c,ρ))`. Outer regularity of the
finite measure `3^k A A_ref · σ⌊P(c,ρ)` (`Set.measure_eq_iInf_isOpen`) finishes. The inner
regularity of `μ` and the fivefold selection statement are not used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization.ReverseTree

open ParabolicRectifiability.Foundations

/-- The growth bound of a tripled ball is at most `3^k A A_ref σ(P(g,s))`, by lower ADR at
`g ∈ supp σ`. -/
theorem d2onc_growth_le_ref {n k : ℕ} {Aref A : ℝ} (hAref : 1 ≤ Aref) (hA : 1 ≤ A)
    {σ : Measure (Space n)} (hADR : IsADR Aref k σ) (g : Space n) (hg : g ∈ σ.support)
    (s : ℝ) (hs : 0 < s) :
    ENNReal.ofReal (A * (3 * s) ^ k) ≤
      ENNReal.ofReal (3 ^ k * A * Aref) * σ (Metric.ball g s) := by
  have hA0 : Aref ≠ 0 := (lt_of_lt_of_le one_pos hAref).ne'
  have hD : 0 ≤ 3 ^ k * A * Aref := by
    have h1 : 0 ≤ A := by linarith
    have h2 : 0 ≤ Aref := by linarith
    exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) k) h1) h2
  have heq : A * (3 * s) ^ k = 3 ^ k * A * Aref * (Aref⁻¹ * s ^ k) := by
    calc A * (3 * s) ^ k = 3 ^ k * A * s ^ k * (Aref * Aref⁻¹) := by
          rw [mul_inv_cancel₀ hA0, mul_pow (3 : ℝ) s k]; ring
      _ = 3 ^ k * A * Aref * (Aref⁻¹ * s ^ k) := by ring
  rw [heq, ENNReal.ofReal_mul hD]
  gcongr
  exact (hADR g hg s hs).1

/-- **The covering bound for one open set.** For `F ⊆ Γ ∩ P(c,ρ)` and an open `U ⊇ F`,
`μ(F) ≤ 3^k A A_ref σ(U ∩ P(c,ρ))`. -/
theorem d2onc_open_bound {n k : ℕ} {Aref A : ℝ} (hAref : 1 ≤ Aref) (hA : 1 ≤ A)
    {μ σ : Measure (Space n)} {Γ : Set (Space n)} (hsupp : σ.support = Γ)
    (hADR : IsADR Aref k σ) {c : Space n} {ρ : ℝ} (hρ : 0 < ρ)
    (hgrowth : ∀ b ∈ μ.support ∩ Metric.ball c ρ, ∀ s : ℝ, 0 < s → s ≤ ρ →
      μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k))
    {F U : Set (Space n)} (hFΓ : F ⊆ Γ ∩ Metric.ball c ρ) (hU : IsOpen U) (hFU : F ⊆ U) :
    μ F ≤ ENNReal.ofReal (3 ^ k * A * Aref) * σ (U ∩ Metric.ball c ρ) := by
  classical
  have hWo : IsOpen (U ∩ Metric.ball c ρ) := hU.inter Metric.isOpen_ball
  have hex : ∀ v ∈ U ∩ Metric.ball c ρ, ∃ ε > 0, Metric.ball v ε ⊆ U ∩ Metric.ball c ρ :=
    fun v hv => Metric.isOpen_iff.1 hWo v hv
  choose! ε hεpos hεsub using hex
  -- the points of `F` in the support of `μ`
  have htW : ∀ v ∈ F ∩ μ.support, v ∈ U ∩ Metric.ball c ρ :=
    fun v hv => ⟨hFU hv.1, (hFΓ hv.1).2⟩
  obtain ⟨r, hrpos, hrle, hrsub⟩ : ∃ r : Space n → ℝ, (∀ v ∈ F ∩ μ.support, 0 < r v) ∧
      (∀ v, r v ≤ ρ / 3) ∧
      (∀ v ∈ F ∩ μ.support, Metric.ball v (r v) ⊆ U ∩ Metric.ball c ρ) := by
    refine ⟨fun v => min (ε v) (ρ / 3), fun v hv => ?_, fun v => min_le_right _ _,
      fun v hv => ?_⟩
    · exact lt_min (hεpos v (htW v hv)) (by linarith)
    · exact (Metric.ball_subset_ball (min_le_left _ _)).trans (hεsub v (htW v hv))
  obtain ⟨u, hut, hud, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun v => Metric.ball v (r v)) (F ∩ μ.support) r 2 one_lt_two
    (fun a ha => (hrpos a ha).le) (ρ / 3) (fun a _ => hrle a)
    (fun a ha => ⟨a, Metric.mem_ball_self (hrpos a ha)⟩)
  have hucount : u.Countable := hud.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
    (fun a ha => ⟨a, Metric.mem_ball_self (hrpos a (hut ha))⟩)
  have htcov : F ∩ μ.support ⊆ ⋃ j ∈ u, Metric.ball j (3 * r j) := by
    intro a ha
    obtain ⟨b, hbu, hne, hle⟩ := hcov a ha
    have hd : dist a b < r a + r b := Metric.dist_lt_add_of_nonempty_ball_inter_ball hne
    refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
    rw [Metric.mem_ball]
    linarith
  have hnull : μ (μ.support)ᶜ = 0 := Measure.measure_compl_support
  have hball : ∀ j ∈ u, μ (Metric.ball j (3 * r j)) ≤
      ENNReal.ofReal (3 ^ k * A * Aref) * σ (Metric.ball j (r j)) := by
    intro j hj
    have hjt := hut hj
    have hjr := hrpos j hjt
    have hjF := hFΓ hjt.1
    have hj3 : 3 * r j ≤ ρ := by linarith [hrle j]
    refine (hgrowth j ⟨hjt.2, hjF.2⟩ (3 * r j) (by linarith) hj3).trans ?_
    exact d2onc_growth_le_ref hAref hA hADR j (by rw [hsupp]; exact hjF.1) (r j) hjr
  calc μ F ≤ μ ((μ.support)ᶜ ∪ ⋃ j ∈ u, Metric.ball j (3 * r j)) := by
        apply measure_mono
        intro y hy
        by_cases hys : y ∈ μ.support
        · exact Or.inr (htcov ⟨hy, hys⟩)
        · exact Or.inl hys
    _ ≤ μ (μ.support)ᶜ + μ (⋃ j ∈ u, Metric.ball j (3 * r j)) := measure_union_le _ _
    _ = μ (⋃ j ∈ u, Metric.ball j (3 * r j)) := by rw [hnull, zero_add]
    _ ≤ ∑' j : u, μ (Metric.ball (j : Space n) (3 * r j)) :=
        measure_biUnion_le μ hucount _
    _ ≤ ∑' j : u, ENNReal.ofReal (3 ^ k * A * Aref) * σ (Metric.ball (j : Space n) (r j)) :=
        ENNReal.tsum_le_tsum fun j => hball j j.2
    _ = ENNReal.ofReal (3 ^ k * A * Aref) * ∑' j : u, σ (Metric.ball (j : Space n) (r j)) :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (3 ^ k * A * Aref) * σ (⋃ j ∈ u, Metric.ball j (r j)) := by
        rw [measure_biUnion hucount hud (fun _ _ => Metric.isOpen_ball.measurableSet)]
    _ ≤ ENNReal.ofReal (3 ^ k * A * Aref) * σ (U ∩ Metric.ball c ρ) := by
        gcongr
        exact iUnion₂_subset fun j hj => hrsub j (hut hj)

/-- **Outer regularity step.** If `μ(F) ≤ D σ(U ∩ P(c,ρ))` for every open `U ⊇ F`, then
`μ(F) ≤ D σ(F ∩ P(c,ρ))`: the measure `D · σ⌊P(c,ρ)` is finite, hence outer regular. -/
theorem d2onc_outer {n : ℕ} {μ σ : Measure (Space n)} [IsFiniteMeasureOnCompacts σ]
    (c : Space n) (ρ : ℝ) (D : ℝ≥0∞) (hD : D ≠ ∞) (F : Set (Space n))
    (hF : ∀ U : Set (Space n), F ⊆ U → IsOpen U → μ F ≤ D * σ (U ∩ Metric.ball c ρ)) :
    μ F ≤ D * σ (F ∩ Metric.ball c ρ) := by
  have : IsFiniteMeasure (D • σ.restrict (Metric.ball c ρ)) := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hD) MeasureTheory.measure_ball_lt_top
  have h : μ F ≤ (D • σ.restrict (Metric.ball c ρ)) F := by
    rw [Set.measure_eq_iInf_isOpen F (D • σ.restrict (Metric.ball c ρ))]
    refine le_iInf₂ fun U hFU => le_iInf fun hU => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hU.measurableSet]
    exact hF U hFU hU
  rwa [Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' Metric.isOpen_ball.measurableSet] at h

/-- **Proof of the statement `d2_on_carrier`** (`OnCarrierStatement`), with
`D = 3^k A A_ref`. -/
theorem d2_on_carrier_proof : OnCarrierStatement := by
  intro n _hn k _hk _hkn Aref hAref A hA
  refine ⟨3 ^ k * A * Aref, ?_, ?_⟩
  · have h1 : 0 < A := by linarith
    have h2 : 0 < Aref := by linarith
    exact mul_pos (mul_pos (pow_pos (by norm_num) k) h1) h2
  · intro μ _hμf _hμr Γ σ hσf hsupp hADR c ρ hρ hgrowth
    have := hσf
    rw [Measure.le_iff]
    intro E hE
    rw [Measure.restrict_apply hE, Measure.smul_apply, smul_eq_mul]
    have hFΓ : E ∩ (Γ ∩ Metric.ball c ρ) ⊆ Γ ∩ Metric.ball c ρ := inter_subset_right
    calc μ (E ∩ (Γ ∩ Metric.ball c ρ))
        ≤ ENNReal.ofReal (3 ^ k * A * Aref) *
            σ (E ∩ (Γ ∩ Metric.ball c ρ) ∩ Metric.ball c ρ) :=
          d2onc_outer c ρ _ ENNReal.ofReal_ne_top _ fun U hFU hU =>
            d2onc_open_bound hAref hA hsupp hADR hρ hgrowth hFΓ hU hFU
      _ ≤ ENNReal.ofReal (3 ^ k * A * Aref) * σ E := by
          gcongr
          exact fun y hy => hy.1.1

end ParabolicRectifiability.QuantitativeCharacterization.ReverseTree
