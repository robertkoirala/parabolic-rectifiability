import ParabolicRectifiability.Characterization.Proofs.Fivefold

/-! # Domination of the source on the good set

Proves `GoodDominationStatement` (`good_set_domination_proof`). For an ADR reference `IsADRCarrier k c C Γ σ`, a measure `ν` and `A > 0`, the good set
`G_A = adrGoodSet Γ ν k A` satisfies `ν⌊G_A ≤ (5^k / c) A σ`.

Proof.
* `b3good_ball_bound`: at a good centre `z ∈ G_A` and a radius `r > 0`,
  `ν(P(z,5r)) ≤ A (5r)^k = (5^k/c) A · c r^k ≤ (5^k/c) A σ(P(z,r))` (lower ADR bound at
  `z ∈ Γ`).
* `b3good_cover_bound`: for every set `E ⊆ G_A` and every open `O ⊇ E`,
  `ν(E) ≤ (5^k/c) A σ(O)`. Each `z ∈ E` gets an ambient ball `P(z,ρ_z) ⊆ O` with
  `0 < ρ_z ≤ 1`; the fivefold selection (the hypothesis `FivefoldSelectionStatement`)
  gives a countable disjoint subfamily whose fivefold dilates cover `E`; countable
  subadditivity for `ν`, the ball bound, and countable additivity of `σ` on the disjoint open
  balls inside `O` conclude.
* `good_set_domination_proof_of`: for a Borel `S`, `ν⌊G_A(S) = ν(S ∩ G_A)`; outer regularity of
  `(5^k/c) A σ` (`σ` is finite on compacts in the proper space `Space n`, hence regular)
  gives an open `U ⊇ S` of nearly minimal mass, and the cover bound with `E = S ∩ G_A ⊆ U`
  closes the inequality.

Neither closedness nor Borel measurability of `G_A`, finiteness of `ν`, nor `ν(Γᶜ) = 0` is
used: the argument is an outer-measure covering argument with ambient balls.

The hypothesis `FivefoldSelectionStatement` is instantiated with
`fivefold_ball_selection_proof` in `good_set_domination_proof`. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- At a good centre, the fivefold ball has `ν`-mass at most `(5^k/c) A σ(P(z,r))`. -/
theorem b3good_ball_bound {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hΓ : IsADRCarrier k c C Γ σ) (ν : Measure (Space n)) {A : ℝ} (hA : 0 < A)
    {z : Space n} (hz : z ∈ adrGoodSet Γ ν k A) {r : ℝ} (hr : 0 < r) :
    ν (Metric.ball z (5 * r)) ≤ ENNReal.ofReal (5 ^ k / c * A) * σ (Metric.ball z r) := by
  have hc : 0 < c := hΓ.lower_pos
  have hreal : A * (5 * r) ^ k = 5 ^ k / c * A * (c * r ^ k) := by
    rw [mul_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hc.ne']
    ring
  calc ν (Metric.ball z (5 * r)) ≤ ENNReal.ofReal (A * (5 * r) ^ k) := hz.2 _ (by positivity)
    _ = ENNReal.ofReal (5 ^ k / c * A) * ENNReal.ofReal (c * r ^ k) := by
        rw [hreal, ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (5 ^ k / c * A) * σ (Metric.ball z r) :=
        mul_le_mul_right (hΓ.lower z hz.1 r hr) _

/-- Fivefold covering bound: every subset `E` of the good set lying in an open set `O` has
`ν(E) ≤ (5^k/c) A σ(O)`. Ambient balls; `E` need not be measurable. -/
theorem b3good_cover_bound (hF : FivefoldSelectionStatement) {n k : ℕ} {c C : ℝ}
    {Γ : Set (Space n)} {σ : Measure (Space n)} (hΓ : IsADRCarrier k c C Γ σ)
    (ν : Measure (Space n)) {A : ℝ} (hA : 0 < A) {E O : Set (Space n)}
    (hEG : E ⊆ adrGoodSet Γ ν k A) (hO : IsOpen O) (hEO : E ⊆ O) :
    ν E ≤ ENNReal.ofReal (5 ^ k / c * A) * σ O := by
  set K := ENNReal.ofReal (5 ^ k / c * A) with hK
  have hrad : ∀ z : E, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ Metric.ball (z : Space n) ρ ⊆ O := by
    intro z
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hO z (hEO z.2)
    exact ⟨min ε 1, lt_min hε one_pos, min_le_right _ _,
      (Metric.ball_subset_ball (min_le_left _ _)).trans hsub⟩
  choose ρ hρpos hρle hρO using hrad
  obtain ⟨J, hJc, hJd, hJcov⟩ :=
    hF (Space n) E (fun z => (z : Space n)) ρ hρpos ⟨1, hρle⟩
  let f5 : E → Set (Space n) := fun i => Metric.ball (i : Space n) (5 * ρ i)
  let f1 : E → Set (Space n) := fun i => Metric.ball (i : Space n) (ρ i)
  have hJd' : J.PairwiseDisjoint f1 := hJd
  have hcov : E ⊆ ⋃ j ∈ J, f5 j := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := hJcov ⟨x, hx⟩
    exact mem_biUnion hj hxj
  have hunion : (⋃ j ∈ J, f1 j) ⊆ O := iUnion₂_subset fun j _ => hρO j
  calc ν E ≤ ν (⋃ j ∈ J, f5 j) := measure_mono hcov
    _ ≤ ∑' j : J, ν (f5 j) := measure_biUnion_le ν hJc f5
    _ ≤ ∑' j : J, K * σ (f1 j) :=
        ENNReal.tsum_le_tsum fun j => b3good_ball_bound hΓ ν hA (hEG (j : E).2) (hρpos j)
    _ = K * ∑' j : J, σ (f1 j) := ENNReal.tsum_mul_left
    _ = K * σ (⋃ j ∈ J, f1 j) := by
        rw [measure_biUnion hJc hJd' fun j _ => Metric.isOpen_ball.measurableSet]
    _ ≤ K * σ O := mul_le_mul_right (measure_mono hunion) _

/-- Good-set domination in implication form: the fivefold selection
`FivefoldSelectionStatement` implies `GoodDominationStatement`. -/
theorem good_set_domination_proof_of (hF : FivefoldSelectionStatement) :
    GoodDominationStatement := by
  intro n _ k c C Γ σ hΓ ν _ _ A hA
  have : IsFiniteMeasureOnCompacts σ := hΓ.finiteOnCompacts
  have hOR : (ENNReal.ofReal (5 ^ k / c * A) • σ).OuterRegular :=
    Measure.OuterRegular.smul σ ENNReal.ofReal_ne_top
  refine Measure.le_iff.2 fun S hS => ?_
  rw [Measure.restrict_apply hS]
  by_contra hlt
  obtain ⟨U, hSU, hU, hUlt⟩ := Set.exists_isOpen_lt_of_lt S _ (not_le.1 hlt)
  have hle := b3good_cover_bound hF hΓ ν hA (E := S ∩ adrGoodSet Γ ν k A)
    inter_subset_right hU (inter_subset_left.trans hSU)
  rw [Measure.smul_apply, smul_eq_mul] at hUlt
  exact absurd hle (not_le.2 hUlt)

/-- **Good-set domination** (`GoodDominationStatement`): `ν⌊G_A ≤ (5^k / c) A σ`, with the
fivefold selection supplied by `fivefold_ball_selection_proof`. -/
theorem good_set_domination_proof : GoodDominationStatement :=
  good_set_domination_proof_of fivefold_ball_selection_proof

end ParabolicRectifiability.Characterization
