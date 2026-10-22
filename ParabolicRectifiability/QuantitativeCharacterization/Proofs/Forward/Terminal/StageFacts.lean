import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # Stage facts of the terminal selection

Proof of `d1c_stageFacts_proof`, in implication form:

`d1c_stageFacts_proof : StopScaleLipschitzStatement → CutoffStatement → StageFactsStatement`.

The stages, the grid quantization `f(c) = r_j`, the stored parents, stop parents (stage one is
empty) and survival histories.

Route:
* `kept` is antitone, lies inside `S` and is Borel (`P.measurable_cell` and open holes);
* on `S`, `f ≤ ρ/100 ≤ ℓ_*/100 < r_1`, so stage `1` has no terminal centre;
* for `j ≥ 2`, `f < r_{j-1}` on `S_{j-1}` (`term_done`) and `f ≥ r_j` (`term_large`) with the
  values of `f` on the grid `{0} ∪ {r_m}` give `f(c) = r_j` exactly;
* at a terminal centre, `100 f(c) ≤ ρ(c)` and the quantization `ρ(c)/100 < 10 f(c)` of the cutoff;
* candidates: `f < r_j` on `S_j` and the quantization give `ρ < 1000 r_j`;
* stored parents: `cand_cover` and `Nat.find`;
* histories: `s ≤ r_{l+1}` with `s = r_j` forces `l + 1 ≤ j`, so `S_j ⊆ S_l`.

The two statements enter as hypotheses. Helpers carry the
prefix `d1cstage_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section StageFactsProof

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-! ### The construction scales `r_j = 10^{-j} · 48 ℓ_*` -/

/-- `r_j > 0`. -/
theorem d1cstage_stageScale_pos (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) : 0 < stageScale 𝒢 j := by
  have h := d1c_rootScale_pos 𝒢
  unfold stageScale coherentScale
  exact div_pos (by linarith) (pow_pos (by norm_num) j)

/-- `r_j = 10 r_{j+1}`. -/
theorem d1cstage_stageScale_succ (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    stageScale 𝒢 j = 10 * stageScale 𝒢 (j + 1) := by
  unfold stageScale coherentScale
  ring

/-- The scales are strictly decreasing in the level. -/
theorem d1cstage_strictAnti (𝒢 : GoodRegion P μ k Λ b) : StrictAnti (stageScale 𝒢) :=
  strictAnti_nat_of_succ_lt fun j => by
    have h1 := d1cstage_stageScale_succ 𝒢 j
    have h2 := d1cstage_stageScale_pos 𝒢 (j + 1)
    linarith

/-- `r_1 = 48 ℓ_* / 10`. -/
theorem d1cstage_stageScale_one (𝒢 : GoodRegion P μ k Λ b) :
    stageScale 𝒢 1 = 48 * 𝒢.rootScale / 10 := by
  unfold stageScale coherentScale
  norm_num

/-! ### The stopping scale and the cutoff on the root cell -/

/-- On the root cell `S`, `ρ ≤ ℓ_*` (the fourth clause of the Lipschitz statement at the root). -/
theorem d1cstage_stopScale_le (hL : StopScaleLipschitzStatement) (𝒢 : GoodRegion P μ k Λ b)
    {z : Space n} (hz : z ∈ 𝒢.rootCell) : 𝒢.stopScale z ≤ 𝒢.rootScale :=
  (hL n E ℓ₀ P μ k Λ b 𝒢).2.2.2 𝒢.root 𝒢.root_mem z hz

/-- On `S`, `f ≤ ρ/100 ≤ ℓ_*/100 < r_1`: stage `1` has no terminal centre. -/
theorem d1cstage_cutoff_lt_one (hL : StopScaleLipschitzStatement) (hC : CutoffStatement)
    (𝒢 : GoodRegion P μ k Λ b) {z : Space n} (hz : z ∈ 𝒢.rootCell) :
    stageCutoff 𝒢 z < stageScale 𝒢 1 := by
  have h1 := ((hC n E ℓ₀ P μ k Λ b 𝒢).1 z).2
  have h2 := d1cstage_stopScale_le hL 𝒢 hz
  have h3 := d1cstage_stageScale_one 𝒢
  have h4 := d1c_rootScale_pos 𝒢
  rw [h3]
  linarith

/-! ### The surviving sets -/

/-- `S_{j+1} ⊆ S_j`. -/
theorem d1cstage_kept_succ_subset (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    C.kept 𝒢 (j + 1) ⊆ C.kept 𝒢 j := by
  intro z hz
  exact hz.1

/-- The surviving sets are antitone. -/
theorem d1cstage_kept_anti (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) : Antitone (C.kept 𝒢) :=
  antitone_nat_of_succ_le fun j => d1cstage_kept_succ_subset C 𝒢 j

/-- `S_j ⊆ S`. -/
theorem d1cstage_kept_subset (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    C.kept 𝒢 j ⊆ 𝒢.rootCell := by
  intro z hz
  exact d1cstage_kept_anti C 𝒢 (Nat.zero_le j) hz

/-- The surviving sets are Borel: the root cell minus finitely many open holes at each stage. -/
theorem d1cstage_kept_measurable (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    MeasurableSet (C.kept 𝒢 j) := by
  induction j with
  | zero => exact P.measurable_cell 𝒢.root.1 𝒢.root.2
  | succ j ih =>
    have hopen : IsOpen (⋃ (i : ℕ) (_ : i < C.termCount (j + 1)),
        Metric.ball (C.term (j + 1) i) (stageCutoff 𝒢 (C.term (j + 1) i))) :=
      isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball
    exact ih.diff hopen.measurableSet

/-! ### Terminal centres -/

/-- The radius of a terminal centre is its cutoff. -/
theorem d1cstage_radius_eq (𝒢 : GoodRegion P μ k Λ b) (C : Choice n) {c : Space n}
    (hc : C.IsTermCenter c) : C.radius 𝒢 c = stageCutoff 𝒢 c := by
  unfold Choice.radius
  exact ite_eq_left hc

/-- **Grid quantization**: every terminal centre of stage `j` has `f(c) = r_j`. -/
theorem d1cstage_term_radius (hL : StopScaleLipschitzStatement) (hC : CutoffStatement)
    (𝒢 : GoodRegion P μ k Λ b) (C : Choice n) (hsel : C.IsSelection 𝒢)
    (j : ℕ) (hj : 1 ≤ j) (i : ℕ) (hi : i < C.termCount j) :
    stageCutoff 𝒢 (C.term j i) = stageScale 𝒢 j := by
  have hmem : C.term j i ∈ C.kept 𝒢 (j - 1) := (hsel.term_mem j hj i hi).1
  have hlarge := hsel.term_large j hj i hi
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · -- stage one is empty
    exfalso
    obtain rfl : j = 1 := by omega
    have hS : C.term 1 i ∈ 𝒢.rootCell := d1cstage_kept_subset C 𝒢 _ hmem
    have := d1cstage_cutoff_lt_one hL hC 𝒢 hS
    linarith
  · -- `r_j ≤ f(c) < r_{j-1}` and `f(c)` on the grid
    have hdone := hsel.term_done (j - 1) (by omega) (C.term j i) hmem
    have hpos := d1cstage_stageScale_pos 𝒢 j
    rcases (hC n E ℓ₀ P μ k Λ b 𝒢).2.2.1 (C.term j i) with h0 | ⟨m, hm⟩
    · exfalso
      linarith
    · rw [hm] at hlarge hdone ⊢
      have hmj : m ≤ j := (d1cstage_strictAnti 𝒢).le_iff_ge.1 hlarge
      have hjm : j - 1 < m := (d1cstage_strictAnti 𝒢).lt_iff_gt.1 hdone
      have hmj' : m = j := by omega
      rw [hmj']

/-- The first stage of a terminal centre is a stage at which it is selected. -/
theorem d1cstage_termStage_mem (C : Choice n) {c : Space n} (hc : C.IsTermCenter c) :
    1 ≤ C.termStage c ∧ ∃ i, i < C.termCount (C.termStage c) ∧ C.term (C.termStage c) i = c := by
  have hne : {j : ℕ | 1 ≤ j ∧ ∃ i, i < C.termCount j ∧ C.term j i = c}.Nonempty := hc
  exact Nat.sInf_mem hne

/-- `termStage_spec`. -/
theorem d1cstage_termStage_spec (hL : StopScaleLipschitzStatement) (hC : CutoffStatement)
    (𝒢 : GoodRegion P μ k Λ b) (C : Choice n) (hsel : C.IsSelection 𝒢)
    (c : Space n) (hc : C.IsTermCenter c) :
    1 ≤ C.termStage c ∧ (∃ i, i < C.termCount (C.termStage c) ∧ C.term (C.termStage c) i = c) ∧
      c ∈ C.kept 𝒢 (C.termStage c - 1) ∧ C.radius 𝒢 c = stageScale 𝒢 (C.termStage c) := by
  obtain ⟨h1, i, hi, hci⟩ := d1cstage_termStage_mem C hc
  refine ⟨h1, ⟨i, hi, hci⟩, ?_, ?_⟩
  · have hmem := (hsel.term_mem _ h1 i hi).1
    rw [hci] at hmem
    exact hmem
  · have hrad := d1cstage_term_radius hL hC 𝒢 C hsel _ h1 i hi
    rw [hci] at hrad
    rw [d1cstage_radius_eq 𝒢 C hc]
    exact hrad

/-- `term_center`: `0 < d_c`, `100 d_c ≤ ρ(c) < 1000 d_c`. -/
theorem d1cstage_term_center (hL : StopScaleLipschitzStatement) (hC : CutoffStatement)
    (𝒢 : GoodRegion P μ k Λ b) (C : Choice n) (hsel : C.IsSelection 𝒢)
    (c : Space n) (hc : C.IsTermCenter c) :
    0 < C.radius 𝒢 c ∧ 100 * C.radius 𝒢 c ≤ 𝒢.stopScale c ∧
      𝒢.stopScale c < 1000 * C.radius 𝒢 c := by
  rw [d1cstage_radius_eq 𝒢 C hc]
  obtain ⟨j, hj, i, hi, hci⟩ := hc
  have hlarge := hsel.term_large j hj i hi
  have hS := d1cstage_kept_subset C 𝒢 (j - 1) (hsel.term_mem j hj i hi).1
  rw [hci] at hlarge hS
  have hpos := d1cstage_stageScale_pos 𝒢 j
  have hf : 0 < stageCutoff 𝒢 c := lt_of_lt_of_le hpos hlarge
  have h100 := ((hC n E ℓ₀ P μ k Λ b 𝒢).1 c).2
  have hρpos : 0 < 𝒢.stopScale c := by linarith
  have hρle := d1cstage_stopScale_le hL 𝒢 hS
  obtain ⟨m, -, hm, -, hlt⟩ := (hC n E ℓ₀ P μ k Λ b 𝒢).2.2.2 c hρpos hρle
  refine ⟨hf, h100, ?_⟩
  linarith

/-! ### Candidates and stored parents -/

/-- `cand_admissible`: a candidate of stage `j` lies in `S` with `ρ < 1000 r_j`. -/
theorem d1cstage_cand_admissible (hL : StopScaleLipschitzStatement) (hC : CutoffStatement)
    (𝒢 : GoodRegion P μ k Λ b) (C : Choice n) (hsel : C.IsSelection 𝒢)
    (j : ℕ) (hj : 1 ≤ j) (i : ℕ) (hi : i < C.candCount j) :
    Admissible 𝒢 j (C.cand j i) := by
  have hmem := hsel.cand_mem j hj i hi
  have hS := d1cstage_kept_subset C 𝒢 j hmem
  show C.cand j i ∈ 𝒢.rootCell ∧ 𝒢.stopScale (C.cand j i) < 1000 * stageScale 𝒢 j
  refine ⟨hS, ?_⟩
  have hdone := hsel.term_done j hj (C.cand j i) hmem
  have hpos := d1cstage_stageScale_pos 𝒢 j
  have hnn := (hL n E ℓ₀ P μ k Λ b 𝒢).1 (C.cand j i)
  rcases hnn.lt_or_eq with hρ | hρ
  · obtain ⟨m, -, hm, -, hlt⟩ :=
      (hC n E ℓ₀ P μ k Λ b 𝒢).2.2.2 _ hρ (d1cstage_stopScale_le hL 𝒢 hS)
    linarith
  · linarith

/-- `Nat.find_spec` for an arbitrary decidability instance (so that the instance stored in
`Choice.parentOf` is found by unification). -/
theorem d1cstage_find_spec {p : ℕ → Prop} (inst : DecidablePred p) (h : ∃ i, p i) :
    p (@Nat.find p inst h) :=
  @Nat.find_spec p inst h

/-- `parentOf_spec`: the stored parent is the first candidate whose open net ball contains `z`. -/
theorem d1cstage_parentOf_spec (𝒢 : GoodRegion P μ k Λ b) (C : Choice n)
    (hsel : C.IsSelection 𝒢) (j : ℕ) (hj : 1 ≤ j) (z : Space n) (hz : z ∈ C.kept 𝒢 j) :
    ∃ i, i < C.candCount j ∧ C.parentOf 𝒢 j z = C.cand j i ∧
      dist z (C.parentOf 𝒢 j z) < 𝒢.type.sourceSeparation * stageScale 𝒢 j := by
  have hcov := hsel.cand_cover j hj hz
  simp only [Set.mem_iUnion] at hcov
  obtain ⟨i₀, hi₀, hz₀⟩ := hcov
  have h : ∃ i, i < C.candCount j ∧
      z ∈ Metric.ball (C.cand j i) (𝒢.type.sourceSeparation * stageScale 𝒢 j) :=
    ⟨i₀, hi₀, hz₀⟩
  unfold Choice.parentOf
  rw [dite_eq_left h]
  refine ⟨_, ?_, rfl, ?_⟩
  · exact (d1cstage_find_spec _ h).1
  · exact (d1cstage_find_spec _ h).2

/-! ### Survival histories -/

/-- `cand_history`: a candidate of stage `j` survives every stage `l` with `r_j ≤ r_{l+1}`. -/
theorem d1cstage_cand_history (𝒢 : GoodRegion P μ k Λ b) (C : Choice n)
    (hsel : C.IsSelection 𝒢) (j : ℕ) (hj : 1 ≤ j) (i : ℕ) (hi : i < C.candCount j) :
    C.HasHistory 𝒢 (C.cand j i) (stageScale 𝒢 j) := by
  have hmem := hsel.cand_mem j hj i hi
  refine ⟨d1cstage_stageScale_pos 𝒢 j, d1cstage_kept_subset C 𝒢 j hmem, fun l _ hl => ?_⟩
  have hlj : l + 1 ≤ j := (d1cstage_strictAnti 𝒢).le_iff_ge.1 hl
  exact d1cstage_kept_anti C 𝒢 (by omega : l ≤ j) hmem

/-- `term_history`: a terminal centre of stage `J` survives every stage `l` with
`r_J ≤ r_{l+1}`, since it lies in `S_{J-1}`. -/
theorem d1cstage_term_history (hL : StopScaleLipschitzStatement) (hC : CutoffStatement)
    (𝒢 : GoodRegion P μ k Λ b) (C : Choice n) (hsel : C.IsSelection 𝒢)
    (c : Space n) (hc : C.IsTermCenter c) :
    C.HasHistory 𝒢 c (C.radius 𝒢 c) := by
  obtain ⟨-, -, hmem, hrad⟩ := d1cstage_termStage_spec hL hC 𝒢 C hsel c hc
  refine ⟨(d1cstage_term_center hL hC 𝒢 C hsel c hc).1,
    d1cstage_kept_subset C 𝒢 _ hmem, fun l _ hl => ?_⟩
  rw [hrad] at hl
  have hlj : l + 1 ≤ C.termStage c := (d1cstage_strictAnti 𝒢).le_iff_ge.1 hl
  exact d1cstage_kept_anti C 𝒢 (by omega : l ≤ C.termStage c - 1) hmem

end StageFactsProof

/-! ### The statement -/

/-- **Stage facts** (`StageFactsStatement`), proved in implication form
from the two statements `StopScaleLipschitzStatement` and `CutoffStatement`. -/
theorem d1c_stageFacts_proof :
    StopScaleLipschitzStatement → CutoffStatement → StageFactsStatement := by
  intro hL hC n E ℓ₀ P μ k Λ b 𝒢 C hsel
  exact
    { kept_succ_subset := d1cstage_kept_succ_subset C 𝒢
      kept_subset := d1cstage_kept_subset C 𝒢
      kept_measurable := d1cstage_kept_measurable C 𝒢
      term_radius := d1cstage_term_radius hL hC 𝒢 C hsel
      termStage_spec := d1cstage_termStage_spec hL hC 𝒢 C hsel
      term_center := d1cstage_term_center hL hC 𝒢 C hsel
      cand_admissible := d1cstage_cand_admissible hL hC 𝒢 C hsel
      parentOf_spec := d1cstage_parentOf_spec 𝒢 C hsel
      cand_history := d1cstage_cand_history 𝒢 C hsel
      term_history := d1cstage_term_history hL hC 𝒢 C hsel }

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
