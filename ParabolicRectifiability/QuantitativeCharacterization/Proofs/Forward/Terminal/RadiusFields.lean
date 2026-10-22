import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # Radii, separations and the cutoff field (`d1c_radiusFields`)

Proof of `d1c_radiusFields_proof`: the six radius fields of
`TerminalNeck` for the defined centres and radii.

* `0 ≤ d_c ≤ 6 ℓ_*`: a terminal radius is `r_{stage} ≤ r_1 = 4.8 ℓ_*`; elsewhere `d_c = 0`.
* `{d = 0} ∩ 𝒞 = 𝒞₀`: terminal centres have `d_c > 0` (stage facts); a core point has `ρ = 0`,
  while a terminal centre has `ρ ≥ 100 d_c > 0`, so core points are not terminal centres.
* Stop separation: of two distinct terminal centres, the later one (in stage, then selection
  order) lies outside the earlier open hole `P(c, f(c))`, whose radius `r_j` is the larger one
  (`term_mem` at one stage; `S_{j'-1} ⊆ S_j` across stages, `S_j` avoiding the stage-`j` holes).
* Core separation and cutoff: `100 d_c ≤ ρ(c) ≤ ρ(z) + d_P(c, z) = d_P(c, z)` for `z ∈ 𝒞₀`.

The statements `StopScaleLipschitzStatement`, `StopScaleZeroStatement`, `CutoffStatement` and
`StageFactsStatement` enter as hypotheses (implication form); `CutoffStatement` is not needed
by this proof (the stage facts already carry the cutoff values at terminal centres). -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section D1CRadii

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

theorem d1cradii_stageScale_anti (𝒢 : GoodRegion P μ k Λ b) {j j' : ℕ} (h : j ≤ j') :
    stageScale 𝒢 j' ≤ stageScale 𝒢 j := by
  unfold stageScale coherentScale
  have := d1c_rootScale_pos 𝒢
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ (by norm_num) h)

theorem d1cradii_kept_anti {C : Choice n} {𝒢 : GoodRegion P μ k Λ b} (hsf : C.StageFacts 𝒢)
    {j j' : ℕ} (h : j ≤ j') : C.kept 𝒢 j' ⊆ C.kept 𝒢 j := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact (hsf.kept_succ_subset _).trans ih

/-- A point of `S_j` (`j ≥ 1`) lies in no terminal hole of stage `j`. -/
theorem d1cradii_not_mem_hole (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) {j i : ℕ} (hj : 1 ≤ j)
    (hi : i < C.termCount j) {z : Space n} (hz : z ∈ C.kept 𝒢 j) :
    z ∉ Metric.ball (C.term j i) (stageCutoff 𝒢 (C.term j i)) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  intro hzb
  have hz' : z ∈ C.kept 𝒢 m \ ⋃ (l : ℕ) (_ : l < C.termCount (m + 1)),
      Metric.ball (C.term (m + 1) l) (stageCutoff 𝒢 (C.term (m + 1) l)) := hz
  exact hz'.2 (mem_iUnion₂.mpr ⟨i, hi, hzb⟩)

theorem d1cradii_radius_of_isTermCenter {C : Choice n} {𝒢 : GoodRegion P μ k Λ b}
    {c : Space n} (h : C.IsTermCenter c) : C.radius 𝒢 c = stageCutoff 𝒢 c := by
  unfold Choice.radius
  exact ite_eq_left_of_eq_true _ _ (eq_true h)

theorem d1cradii_radius_of_not {C : Choice n} {𝒢 : GoodRegion P μ k Λ b}
    {c : Space n} (h : ¬ C.IsTermCenter c) : C.radius 𝒢 c = 0 := by
  unfold Choice.radius
  exact ite_eq_right_of_eq_false _ _ (eq_false h)

/-- Of two terminal centres `c = term j i`, `c' = term j' i'` with `(j, i)` earlier than
`(j', i')` (lexicographically), `c'` lies outside the open hole `P(c, r_j)`. -/
theorem d1cradii_later_outside (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (hsel : C.IsSelection 𝒢)
    (hsf : C.StageFacts 𝒢) {j i j' i' : ℕ} (hj : 1 ≤ j) (hi : i < C.termCount j) (hj' : 1 ≤ j')
    (hi' : i' < C.termCount j') (hlex : j < j' ∨ (j = j' ∧ i < i')) :
    stageScale 𝒢 j ≤ dist (C.term j' i') (C.term j i) := by
  have hnot : C.term j' i' ∉ Metric.ball (C.term j i) (stageCutoff 𝒢 (C.term j i)) := by
    rcases hlex with h | ⟨rfl, h⟩
    · have hmem : C.term j' i' ∈ C.kept 𝒢 j :=
        d1cradii_kept_anti hsf (by omega : j ≤ j' - 1) (hsel.term_mem j' hj' i' hi').1
      exact d1cradii_not_mem_hole C 𝒢 hj hi hmem
    · exact fun hb => (hsel.term_mem j hj' i' hi').2 (mem_iUnion₂.mpr ⟨i, h, hb⟩)
  rw [hsf.term_radius j hj i hi, Metric.mem_ball, not_lt] at hnot
  exact hnot

end D1CRadii

/-- **Radii, separations and the cutoff field**: the six radius fields of `TerminalNeck`. -/
theorem d1c_radiusFields_proof :
    StopScaleLipschitzStatement → StopScaleZeroStatement → CutoffStatement →
      StageFactsStatement → RadiusFieldsStatement := by
  intro hLip hZero _hCut hSF n E ℓ₀ P μ k Λ b 𝒢 C hsel
  have hsf := hSF n E ℓ₀ P μ k Λ b 𝒢 C hsel
  obtain ⟨-, hLipD, -, -⟩ := hLip n E ℓ₀ P μ k Λ b 𝒢
  have hZ := hZero n E ℓ₀ P μ k Λ b 𝒢
  have htc_of_pos : ∀ c, 0 < C.radius 𝒢 c → C.IsTermCenter c := by
    intro c hc
    by_contra h
    rw [d1cradii_radius_of_not h] at hc
    exact lt_irrefl _ hc
  have hcore_of_zero : ∀ c ∈ C.centers 𝒢, C.radius 𝒢 c = 0 → c ∈ 𝒢.limitCore := by
    rintro c (hc | hc) h0
    · exact hc
    · exact absurd h0 (hsf.term_center c hc).1.ne'
  have hnot_tc_core : ∀ c ∈ 𝒢.limitCore, ¬ C.IsTermCenter c := by
    intro c hc htc
    have h := hsf.term_center c htc
    rw [(hZ c).mpr hc] at h
    linarith [h.1, h.2.1]
  have hradius_term : ∀ {j i : ℕ}, 1 ≤ j → i < C.termCount j →
      C.radius 𝒢 (C.term j i) = stageScale 𝒢 j := by
    intro j i hj hi
    rw [d1cradii_radius_of_isTermCenter ⟨j, hj, i, hi, rfl⟩, hsf.term_radius j hj i hi]
  refine
    { radius_nonneg := ?_
      radius_le := ?_
      core_eq := ?_
      stop_separation := ?_
      core_separation := ?_
      cutoff := ?_ }
  · -- `0 ≤ d_c`
    intro c _
    by_cases h : C.IsTermCenter c
    · exact (hsf.term_center c h).1.le
    · exact le_of_eq (d1cradii_radius_of_not h).symm
  · -- `d_c ≤ 6 ℓ_*`
    intro c _
    have hℓ := d1c_rootScale_pos 𝒢
    by_cases h : C.IsTermCenter c
    · obtain ⟨h1, -, -, hr⟩ := hsf.termStage_spec c h
      rw [hr]
      have h1s : stageScale 𝒢 1 = 48 * 𝒢.rootScale / 10 := by
        rw [stageScale, coherentScale, pow_one]
      have hanti := d1cradii_stageScale_anti 𝒢 h1
      rw [h1s] at hanti
      linarith
    · rw [d1cradii_radius_of_not h]
      linarith
  · -- `{d = 0} ∩ 𝒞 = 𝒞₀`
    ext c
    show c ∈ C.centers 𝒢 ∧ C.radius 𝒢 c = 0 ↔ c ∈ 𝒢.limitCore
    constructor
    · rintro ⟨hc, h0⟩
      exact hcore_of_zero c hc h0
    · intro hc
      exact ⟨Or.inl hc, d1cradii_radius_of_not (hnot_tc_core c hc)⟩
  · -- stop separation
    intro c _ c' _ hc hc' hne
    obtain ⟨j, hj, i, hi, rfl⟩ := htc_of_pos c hc
    obtain ⟨j', hj', i', hi', rfl⟩ := htc_of_pos c' hc'
    rw [hradius_term hj hi, hradius_term hj' hi']
    rcases lt_trichotomy j j' with h | rfl | h
    · rw [max_eq_left (d1cradii_stageScale_anti 𝒢 h.le), dist_comm]
      exact d1cradii_later_outside C 𝒢 hsel hsf hj hi hj' hi' (Or.inl h)
    · rw [max_self]
      rcases lt_trichotomy i i' with h' | rfl | h'
      · rw [dist_comm]
        exact d1cradii_later_outside C 𝒢 hsel hsf hj hi hj' hi' (Or.inr ⟨rfl, h'⟩)
      · exact absurd rfl hne
      · exact d1cradii_later_outside C 𝒢 hsel hsf hj' hi' hj hi (Or.inr ⟨rfl, h'⟩)
    · rw [max_eq_right (d1cradii_stageScale_anti 𝒢 h.le)]
      exact d1cradii_later_outside C 𝒢 hsel hsf hj' hi' hj hi (Or.inl h)
  · -- core separation
    intro c _ hc z hzC hz0
    have hρz := (hZ z).mpr (hcore_of_zero z hzC hz0)
    have h := (hsf.term_center c (htc_of_pos c hc)).2.1
    have hd := hLipD c z
    linarith
  · -- the cutoff field
    intro c _ hc
    exact (hsf.term_center c (htc_of_pos c hc)).2.1

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
