import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # The exact source identity (`d1c_assignmentFields`)

Proof of `d1c_assignmentFields_proof`: the four assignment fields of
`TerminalNeck` for the defined Borel terminal assignments.

* Each terminal piece `S_{j-1} ∩ P(c, f(c)) \ ⋃_{l<i} P(c_l, f(c_l))` is Borel (the surviving set is
  Borel by `StageFacts.kept_measurable`, the rest is a difference of open sets).
* Pieces of distinct indices `(j, i) ≠ (j', i')` are disjoint: at one stage by the first-ball
  rule, across stages because a later piece lies in `S_j`, outside every stage-`j` hole.
* `S = (S ∩ 𝒞₀) ∪ ⋃_{c ∈ 𝒞₊} A_c`: a point removed first at stage `j` lies in the piece of the
  first stage-`j` hole containing it; a point surviving every stage has `f < r_j` for all `j ≥ 1`,
  hence `f = 0`, hence `ρ = 0` (the cutoff on `0 < ρ ≤ ℓ_*`), i.e. it lies in `𝒞₀`.

The statements `StopScaleLipschitzStatement`, `StopScaleZeroStatement`, `CutoffStatement` and
`StageFactsStatement` enter as hypotheses (implication form). All sets are subsets of the root
cell `S`; no measure enters (the identity `μ⌞S = μ⌞(S ∩ 𝒞₀) + ∑ μ⌞A_c` follows). -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section D1CAssign

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

theorem d1cassign_stageScale_pos (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) : 0 < stageScale 𝒢 j := by
  unfold stageScale coherentScale
  have := d1c_rootScale_pos 𝒢
  positivity

theorem d1cassign_stageScale_anti (𝒢 : GoodRegion P μ k Λ b) {j j' : ℕ} (h : j ≤ j') :
    stageScale 𝒢 j' ≤ stageScale 𝒢 j := by
  unfold stageScale coherentScale
  have := d1c_rootScale_pos 𝒢
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ (by norm_num) h)

theorem d1cassign_kept_anti {C : Choice n} {𝒢 : GoodRegion P μ k Λ b} (hsf : C.StageFacts 𝒢)
    {j j' : ℕ} (h : j ≤ j') : C.kept 𝒢 j' ⊆ C.kept 𝒢 j := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact (hsf.kept_succ_subset _).trans ih

/-- A point of `S_j` (`j ≥ 1`) lies in no terminal hole of stage `j`. -/
theorem d1cassign_not_mem_hole (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) {j i : ℕ} (hj : 1 ≤ j)
    (hi : i < C.termCount j) {z : Space n} (hz : z ∈ C.kept 𝒢 j) :
    z ∉ Metric.ball (C.term j i) (stageCutoff 𝒢 (C.term j i)) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  intro hzb
  have hz' : z ∈ C.kept 𝒢 m \ ⋃ (l : ℕ) (_ : l < C.termCount (m + 1)),
      Metric.ball (C.term (m + 1) l) (stageCutoff 𝒢 (C.term (m + 1) l)) := hz
  exact hz'.2 (mem_iUnion₂.mpr ⟨i, hi, hzb⟩)

theorem d1cassign_measurableSet_termPiece (C : Choice n) (𝒢 : GoodRegion P μ k Λ b)
    (hsf : C.StageFacts 𝒢) (j i : ℕ) : MeasurableSet (C.termPiece 𝒢 j i) :=
  (hsf.kept_measurable (j - 1)).inter (Metric.isOpen_ball.measurableSet.diff
    (isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball).measurableSet)

/-- Terminal pieces of distinct indices are disjoint. -/
theorem d1cassign_termPiece_disjoint (C : Choice n) (𝒢 : GoodRegion P μ k Λ b)
    (hsf : C.StageFacts 𝒢) {j i j' i' : ℕ} (hj : 1 ≤ j) (hi : i < C.termCount j) (hj' : 1 ≤ j')
    (hi' : i' < C.termCount j') (hne : (j, i) ≠ (j', i')) :
    Disjoint (C.termPiece 𝒢 j i) (C.termPiece 𝒢 j' i') := by
  rw [Set.disjoint_left]
  rintro z ⟨hz1, hb1, hn1⟩ ⟨hz2, hb2, hn2⟩
  rcases lt_trichotomy j j' with h | rfl | h
  · have hzj : z ∈ C.kept 𝒢 j := d1cassign_kept_anti hsf (by omega : j ≤ j' - 1) hz2
    exact d1cassign_not_mem_hole C 𝒢 hj hi hzj hb1
  · rcases lt_trichotomy i i' with h' | rfl | h'
    · exact hn2 (mem_iUnion₂.mpr ⟨i, h', hb1⟩)
    · exact hne rfl
    · exact hn1 (mem_iUnion₂.mpr ⟨i', h', hb2⟩)
  · have hzj : z ∈ C.kept 𝒢 j' := d1cassign_kept_anti hsf (by omega : j' ≤ j - 1) hz1
    exact d1cassign_not_mem_hole C 𝒢 hj' hi' hzj hb2

theorem d1cassign_mem_assignment {C : Choice n} {𝒢 : GoodRegion P μ k Λ b} {c z : Space n} :
    z ∈ C.assignment 𝒢 c ↔
      ∃ j, 1 ≤ j ∧ ∃ i, (i < C.termCount j ∧ C.term j i = c) ∧ z ∈ C.termPiece 𝒢 j i := by
  simp only [Choice.assignment, mem_iUnion, exists_prop]

theorem d1cassign_radius_of_isTermCenter {C : Choice n} {𝒢 : GoodRegion P μ k Λ b}
    {c : Space n} (h : C.IsTermCenter c) : C.radius 𝒢 c = stageCutoff 𝒢 c := by
  unfold Choice.radius
  exact ite_eq_left_of_eq_true _ _ (eq_true h)

end D1CAssign

/-- **The exact source identity**: the four assignment fields of `TerminalNeck`. -/
theorem d1c_assignmentFields_proof :
    StopScaleLipschitzStatement → StopScaleZeroStatement → CutoffStatement →
      StageFactsStatement → AssignmentFieldsStatement := by
  intro hLip hZero hCut hSF n E ℓ₀ P μ k Λ b 𝒢 C hsel
  classical
  have hsf := hSF n E ℓ₀ P μ k Λ b 𝒢 C hsel
  obtain ⟨hLip0, -, -, hLip4⟩ := hLip n E ℓ₀ P μ k Λ b 𝒢
  obtain ⟨-, -, hCut3, hCut4⟩ := hCut n E ℓ₀ P μ k Λ b 𝒢
  refine
    { measurable_assignment := ?_
      assignment_subset := ?_
      assignment_disjoint := ?_
      source_eq := ?_ }
  · -- Borel assignments
    intro c
    unfold Choice.assignment
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ =>
        d1cassign_measurableSet_termPiece C 𝒢 hsf j i
  · -- `A_c ⊆ S ∩ P(c, d_c)`
    intro c _ _ z hz
    obtain ⟨j, hj, i, ⟨hi, rfl⟩, hzp⟩ := d1cassign_mem_assignment.mp hz
    have htc : C.IsTermCenter (C.term j i) := ⟨j, hj, i, hi, rfl⟩
    refine ⟨hsf.kept_subset _ hzp.1, ?_⟩
    rw [d1cassign_radius_of_isTermCenter htc]
    exact hzp.2.1
  · -- disjointness
    intro c _ c' _ _ _ hcc'
    rw [Set.disjoint_left]
    intro z hz hz'
    obtain ⟨j, hj, i, ⟨hi, rfl⟩, hzp⟩ := d1cassign_mem_assignment.mp hz
    obtain ⟨j', hj', i', ⟨hi', rfl⟩, hzp'⟩ := d1cassign_mem_assignment.mp hz'
    have hne : (j, i) ≠ (j', i') := by
      intro h
      apply hcc'
      simp only [Prod.mk.injEq] at h
      rw [h.1, h.2]
    exact Set.disjoint_left.mp (d1cassign_termPiece_disjoint C 𝒢 hsf hj hi hj' hi' hne) hzp hzp'
  · -- the source identity
    apply Set.Subset.antisymm
    · intro z hz
      by_cases hall : ∀ j, z ∈ C.kept 𝒢 j
      · -- surviving every stage: `f = 0`, hence `ρ = 0`, hence `z ∈ 𝒞₀`
        left
        refine ⟨hz, ?_⟩
        apply (hZero n E ℓ₀ P μ k Λ b 𝒢 z).mp
        have hcut0 : stageCutoff 𝒢 z = 0 := by
          rcases hCut3 z with h | ⟨m, hm⟩
          · exact h
          · exfalso
            have h1 := hsel.term_done (m + 1) (by omega) z (hall (m + 1))
            rw [hm] at h1
            exact absurd h1 (not_lt.mpr (d1cassign_stageScale_anti 𝒢 (Nat.le_succ m)))
        by_contra hne
        have hpos : 0 < 𝒢.stopScale z := lt_of_le_of_ne (hLip0 z) (Ne.symm hne)
        have hle : 𝒢.stopScale z ≤ 𝒢.rootScale := hLip4 𝒢.root 𝒢.root_mem z hz
        obtain ⟨j, _, hj, -⟩ := hCut4 z hpos hle
        rw [hcut0] at hj
        exact (d1cassign_stageScale_pos 𝒢 j).ne hj
      · -- removed first at some stage `m + 1`
        right
        push Not at hall
        have hj0 : Nat.find hall ≠ 0 := by
          intro h
          have hspec := Nat.find_spec hall
          rw [h] at hspec
          exact hspec hz
        obtain ⟨m, hm⟩ : ∃ m, Nat.find hall = m + 1 := ⟨Nat.find hall - 1, by omega⟩
        have hzm : z ∈ C.kept 𝒢 m := by
          by_contra hc
          exact Nat.find_min hall (show m < Nat.find hall by omega) hc
        have hzm1 : z ∉ C.kept 𝒢 (m + 1) := by
          have hspec := Nat.find_spec hall
          rwa [hm] at hspec
        have hex : ∃ i, i < C.termCount (m + 1) ∧
            z ∈ Metric.ball (C.term (m + 1) i) (stageCutoff 𝒢 (C.term (m + 1) i)) := by
          by_contra hc
          push Not at hc
          apply hzm1
          show z ∈ C.kept 𝒢 m \ ⋃ (l : ℕ) (_ : l < C.termCount (m + 1)),
            Metric.ball (C.term (m + 1) l) (stageCutoff 𝒢 (C.term (m + 1) l))
          refine ⟨hzm, fun hu => ?_⟩
          obtain ⟨l, hl, hzl⟩ := mem_iUnion₂.mp hu
          exact hc l hl hzl
        obtain ⟨hi, hzi⟩ := Nat.find_spec hex
        have htc : C.IsTermCenter (C.term (m + 1) (Nat.find hex)) :=
          ⟨m + 1, by omega, Nat.find hex, hi, rfl⟩
        refine mem_iUnion₂.mpr ⟨C.term (m + 1) (Nat.find hex), ?_, ?_⟩
        · show C.term (m + 1) (Nat.find hex) ∈ C.centers 𝒢 ∧
            0 < C.radius 𝒢 (C.term (m + 1) (Nat.find hex))
          exact ⟨Or.inr htc, (hsf.term_center _ htc).1⟩
        · refine d1cassign_mem_assignment.mpr ⟨m + 1, by omega, Nat.find hex, ⟨hi, rfl⟩, ?_⟩
          show z ∈ C.kept 𝒢 (m + 1 - 1) ∩
            (Metric.ball (C.term (m + 1) (Nat.find hex))
                (stageCutoff 𝒢 (C.term (m + 1) (Nat.find hex))) \
              ⋃ (l : ℕ) (_ : l < Nat.find hex),
                Metric.ball (C.term (m + 1) l) (stageCutoff 𝒢 (C.term (m + 1) l)))
          refine ⟨by rw [Nat.add_sub_cancel]; exact hzm, hzi, fun hu => ?_⟩
          obtain ⟨l, hl, hzl⟩ := mem_iUnion₂.mp hu
          exact Nat.find_min hex hl ⟨hl.trans hi, hzl⟩
    · rintro z (hz | hz)
      · exact hz.1
      · obtain ⟨c, _, hzc⟩ := mem_iUnion₂.mp hz
        obtain ⟨j, _, i, _, hzp⟩ := d1cassign_mem_assignment.mp hzc
        exact hsf.kept_subset _ hzp.1

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
