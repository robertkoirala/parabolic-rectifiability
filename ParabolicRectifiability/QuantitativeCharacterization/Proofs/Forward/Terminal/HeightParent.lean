import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # Centre heights, stop parents and the container (`d1c_heightParent`)

This module proves `d1c_heightParent_proof`, in implication form:

`ThinnessStatement → RootThinnessStatement → StageFactsStatement → HeightParentStatement`.

Route. Constants: `Λ₀ = max Λ₀(thin) Λ₀(root)`, `B = max B(thin) B(root)` (local ADR in the larger
buffer restricts to the smaller ones), both hypotheses applied at tolerance `η' = min(η, 1)`, and
`b₀ = min b₀(thin) b₀(root)`.
* `initialPoint_near`: root thinness, `η' ℓ_* ≤ 48 ℓ_*`.
* `center_mem`: level `0` is the artificial root, within `η' ℓ_* < 48 ℓ_*` of `q` (root thinness);
  levels `j ≥ 1` are candidates in `S_j ⊆ S ⊆ P(q, 2 ℓ_*)`.
* `centerHeight`: level `0` has height `0` (`π_{L_*} x_q ∈ L_*`); a level-`j ≥ 1` candidate `g`
  is admissible and thinness at `(j, g)` for `z = g` bounds `dist(x_g, L_g)` by `η' r_j`.
* `stoppingParent_spec`: a centre of positive radius is a terminal centre of stage `J ≥ 1` with
  `c ∈ S_{J-1}` and `d_c = r_J`. For `J ≥ 2` the stored parent `g = parentOf (J-1) c` is a
  level-`(J-1)` candidate with `d_P(c, g) < κ_net r_{J-1} ≤ r_{J-1}`; thinness at `(J-1, g)` for
  `z = c` gives the tube bound, and `r_{J-1}/10 = r_J = d_c`. For `J = 1` the initial tube (root
  thinness on `closure S`) gives `dist(x_c, L_*) ≤ η' ℓ_* ≤ η r_0`, and `r_0/10 = r_1 = d_c`.

The three statements enter only as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section HeightHelpers

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The level-`j` index set of the coherent family. -/
theorem d1cheight_index (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (fits : LocalFits 𝒢)
    (j : ℕ) :
    (C.family 𝒢 fits).index j = if j = 0 then {rootCenter 𝒢} else C.candSet j := rfl

/-- The family is indexed by physical points. -/
theorem d1cheight_center (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (fits : LocalFits 𝒢)
    (j : ℕ) (a : Space n) : (C.family 𝒢 fits).center j a = a := rfl

/-- The level-`j` plane of the coherent family. -/
theorem d1cheight_plane (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (fits : LocalFits 𝒢)
    (j : ℕ) (a : Space n) :
    (C.family 𝒢 fits).plane j a =
      if j = 0 then rootPlane 𝒢 else NeckSelection.modelPlane 𝒢.type (fits.model j a) := rfl

/-- The family scales are the construction scales `r_j`. -/
theorem d1cheight_scale (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (fits : LocalFits 𝒢)
    (j : ℕ) : (C.family 𝒢 fits).scale j = stageScale 𝒢 j := rfl

/-- Positive-level index sets are the candidate nets. -/
theorem d1cheight_mem_index_pos (C : Choice n) (𝒢 : GoodRegion P μ k Λ b)
    (fits : LocalFits 𝒢) {j : ℕ} (hj : j ≠ 0) (a : Space n) :
    a ∈ (C.family 𝒢 fits).index j ↔ ∃ i, i < C.candCount j ∧ C.cand j i = a := by
  rw [d1cheight_index, ite_eq_right hj]
  simp only [Choice.candSet, Finset.mem_image, Finset.mem_range]

/-- Level `0` consists of the artificial root. -/
theorem d1cheight_mem_index_zero (C : Choice n) (𝒢 : GoodRegion P μ k Λ b)
    (fits : LocalFits 𝒢) (a : Space n) :
    a ∈ (C.family 𝒢 fits).index 0 ↔ a = rootCenter 𝒢 := by
  rw [d1cheight_index, ite_eq_left rfl, Finset.mem_singleton]

/-- The spatial part of the artificial root lies on `L_*` (both branches). -/
theorem d1cheight_rootCenter_mem (𝒢 : GoodRegion P μ k Λ b) :
    (rootCenter 𝒢).1 ∈ (rootPlane 𝒢).toSet := by
  unfold rootCenter
  split_ifs
  · exact (rootPlane 𝒢).projection_mem 𝒢.root.2.1
  · exact (rootPlane 𝒢).projection_mem 𝒢.root.2.1

/-- The root cell lies in the partitioned set. -/
theorem d1cheight_rootCell_subset (𝒢 : GoodRegion P μ k Λ b) : 𝒢.rootCell ⊆ E := by
  intro x hx
  rw [← P.cell_cover 𝒢.root.1]
  exact Set.mem_biUnion (t := fun z => P.cell 𝒢.root.1 z)
    (show 𝒢.root.2 ∈ P.center 𝒢.root.1 from 𝒢.root_isCell)
    (show x ∈ P.cell 𝒢.root.1 𝒢.root.2 from hx)

/-- The root cell lies in `P(q, 2 ℓ_*)`. -/
theorem d1cheight_rootCell_subset_ball (𝒢 : GoodRegion P μ k Λ b) :
    𝒢.rootCell ⊆ Metric.ball 𝒢.root.2 (2 * 𝒢.rootScale) :=
  P.cell_subset_ball 𝒢.root.1 𝒢.root.2 𝒢.root_isCell

/-- The construction scales are positive. -/
theorem d1cheight_stageScale_pos (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) : 0 < stageScale 𝒢 j := by
  unfold stageScale coherentScale
  have := d1c_rootScale_pos 𝒢
  positivity

/-- `r_{m+1} = r_m / 10`. -/
theorem d1cheight_stageScale_succ (𝒢 : GoodRegion P μ k Λ b) (m : ℕ) :
    stageScale 𝒢 (m + 1) = stageScale 𝒢 m / 10 := by
  unfold stageScale coherentScale
  rw [pow_succ, div_div]

end HeightHelpers

/-- The net separation constant is at most `1`. -/
theorem d1cheight_sourceSeparation_le_one (T : NeckType) : T.sourceSeparation ≤ 1 := by
  cases T <;> norm_num [NeckType.sourceSeparation]

/-- Local ADR in a buffer restricts to every smaller buffer. -/
theorem d1cheight_localADR_mono {n : ℕ} {μ : Measure (Space n)} {k : ℕ} {A : ℝ} {a : Space n}
    {ρ ρ' : ℝ} (h : LocalADR μ k A a ρ) (hρ : ρ' ≤ ρ) : LocalADR μ k A a ρ' := by
  intro y hy s hs hsρ
  exact h y ⟨hy.1, Metric.ball_subset_ball hρ hy.2⟩ s hs (hsρ.trans hρ)

/-- **Centre heights, stop parents and the container** (`HeightParentStatement`): centre heights, stop parents
and the container at every tolerance `η` for small `b`, from thinness, root thinness and the
stage facts (all as hypotheses). -/
theorem d1c_heightParent_proof :
    ThinnessStatement → RootThinnessStatement → StageFactsStatement →
      HeightParentStatement := by
  intro hThin hRoot hStage n hn k hk hkn A hA
  obtain ⟨Λ₁, hΛ₁, hT⟩ := hThin n hn k hk hkn A hA
  obtain ⟨Λ₂, -, hR⟩ := hRoot n hn k hk hkn A hA
  refine ⟨max Λ₁ Λ₂, le_max_of_le_left hΛ₁, fun Λ hΛ => ?_⟩
  obtain ⟨B₁, hB₁, hT⟩ := hT Λ (le_of_max_le_left hΛ)
  obtain ⟨B₂, -, hR⟩ := hR Λ (le_of_max_le_right hΛ)
  refine ⟨max B₁ B₂, le_max_of_le_left hB₁, fun η hη => ?_⟩
  have hη' : 0 < min η 1 := lt_min hη one_pos
  obtain ⟨b₁, hb₁, hT⟩ := hT (min η 1) hη'
  obtain ⟨b₂, hb₂, hR⟩ := hR (min η 1) hη'
  refine ⟨min b₁ b₂, lt_min hb₁ hb₂, ?_⟩
  intro b hb hbb μ hfin hreg a ha R hRpos hADR P 𝒢 hfor fits C hC
  have hADR₁ : LocalADR μ k A a (B₁ * R) :=
    d1cheight_localADR_mono hADR (mul_le_mul_of_nonneg_right (le_max_left _ _) hRpos.le)
  have hADR₂ : LocalADR μ k A a (B₂ * R) :=
    d1cheight_localADR_mono hADR (mul_le_mul_of_nonneg_right (le_max_right _ _) hRpos.le)
  have hT' := hT b hb (hbb.trans (min_le_left _ _)) μ hfin hreg a ha R hRpos hADR₁ P 𝒢 hfor fits
  obtain ⟨hRtube, hRc, hRn⟩ :=
    hR b hb (hbb.trans (min_le_right _ _)) μ hfin hreg a ha R hRpos hADR₂ P 𝒢 hfor
  have sf := hStage n μ.support R P μ k Λ b 𝒢 C hC
  have hℓ := d1c_rootScale_pos 𝒢
  have hmin1 : min η 1 ≤ 1 := min_le_right _ _
  have hminη : min η 1 ≤ η := min_le_left _ _
  have hroot1 : min η 1 * 𝒢.rootScale ≤ 𝒢.rootScale := by
    calc min η 1 * 𝒢.rootScale ≤ 1 * 𝒢.rootScale := mul_le_mul_of_nonneg_right hmin1 hℓ.le
      _ = 𝒢.rootScale := one_mul _
  -- the full tube test at a candidate, for points of the root cell within `r_j`
  have htube : ∀ j, 1 ≤ j → ∀ i, i < C.candCount j → ∀ z ∈ 𝒢.rootCell,
      dist z (C.cand j i) < stageScale 𝒢 j →
      Metric.infDist z.1 (NeckSelection.modelPlane 𝒢.type (fits.model j (C.cand j i))).toSet ≤
        η * stageScale 𝒢 j := by
    intro j hj i hi z hz hzd
    have hpos := d1cheight_stageScale_pos 𝒢 j
    have hzb : z ∈ Metric.ball (C.cand j i) (2 * stageScale 𝒢 j) := by
      rw [Metric.mem_ball]
      linarith
    have h := (hT' j (C.cand j i) hj (sf.cand_admissible j hj i hi) z
      ⟨d1cheight_rootCell_subset 𝒢 hz, hzb⟩).2.1
    exact h.trans (mul_le_mul_of_nonneg_right hminη hpos.le)
  refine
    { initialPoint_near := ?_
      center_mem := ?_
      centerHeight := ?_
      stoppingParent_spec := ?_ }
  · -- the anchor of the initial plane is near `x_q`
    exact hRn.trans (hroot1.trans (by linarith))
  · -- every centre lies in `P(q, 48 ℓ_*)`
    intro j a' ha'
    rw [d1cheight_center]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [(d1cheight_mem_index_zero C 𝒢 fits a').1 ha', Metric.mem_ball]
      exact hRc.trans_lt (hroot1.trans_lt (by linarith))
    · obtain ⟨i, hi, rfl⟩ := (d1cheight_mem_index_pos C 𝒢 fits hj.ne' a').1 ha'
      have hmem := sf.kept_subset j (hC.cand_mem j hj i hi)
      exact Metric.ball_subset_ball (by linarith) (d1cheight_rootCell_subset_ball 𝒢 hmem)
  · -- centre heights
    intro j a' ha'
    rw [d1cheight_center, d1cheight_plane, d1cheight_scale]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [ite_eq_left rfl, (d1cheight_mem_index_zero C 𝒢 fits a').1 ha',
        Metric.infDist_zero_of_mem (d1cheight_rootCenter_mem 𝒢)]
      exact (mul_pos hη (d1cheight_stageScale_pos 𝒢 0)).le
    · rw [ite_eq_right hj.ne']
      obtain ⟨i, hi, rfl⟩ := (d1cheight_mem_index_pos C 𝒢 fits hj.ne' a').1 ha'
      refine htube j hj i hi _ (sf.kept_subset j (hC.cand_mem j hj i hi)) ?_
      rw [dist_self]
      exact d1cheight_stageScale_pos 𝒢 j
  · -- stop parents
    intro c _ hrad
    have hterm : C.IsTermCenter c := by
      by_contra hnt
      have h0 : C.radius 𝒢 c = 0 := by
        unfold Choice.radius
        rw [ite_eq_right hnt]
      linarith
    obtain ⟨hJ1, -, hkept, hradJ⟩ := sf.termStage_spec c hterm
    unfold Choice.stoppingParent
    by_cases h2 : 2 ≤ C.termStage c
    · rw [ite_eq_left h2]
      set J := C.termStage c with hJdef
      have hJm : 1 ≤ J - 1 := by omega
      have hJ0 : J - 1 ≠ 0 := by omega
      obtain ⟨i, hi, hpar, hpd⟩ := sf.parentOf_spec (J - 1) hJm c hkept
      have hpos := d1cheight_stageScale_pos 𝒢 (J - 1)
      have hsep : 𝒢.type.sourceSeparation * stageScale 𝒢 (J - 1) ≤ stageScale 𝒢 (J - 1) :=
        mul_le_of_le_one_left hpos.le (d1cheight_sourceSeparation_le_one _)
      have hdist : dist c (C.parentOf 𝒢 (J - 1) c) < stageScale 𝒢 (J - 1) := hpd.trans_le hsep
      have hdist' : dist c (C.cand (J - 1) i) < stageScale 𝒢 (J - 1) := by
        rw [← hpar]
        exact hdist
      simp only [CoherentFamily.IsStoppingParent]
      rw [d1cheight_center, d1cheight_plane, d1cheight_scale, ite_eq_right hJ0]
      refine ⟨?_, hdist.le, ?_, ?_⟩
      · exact (d1cheight_mem_index_pos C 𝒢 fits hJ0 _).2 ⟨i, hi, hpar.symm⟩
      · rw [hpar]
        exact htube (J - 1) hJm i hi c (sf.kept_subset _ hkept) hdist'
      · have hsucc := d1cheight_stageScale_succ 𝒢 (J - 1)
        rw [show J - 1 + 1 = J by omega] at hsucc
        rw [hradJ, hsucc]
    · rw [ite_eq_right h2]
      have hJ : C.termStage c = 1 := by omega
      rw [hJ] at hkept hradJ
      have hcl : c ∈ closure 𝒢.rootCell := subset_closure (sf.kept_subset _ hkept)
      simp only [CoherentFamily.IsStoppingParent]
      refine ⟨?_, ?_⟩
      · show Metric.infDist c.1 (rootPlane 𝒢).toSet ≤ η * (48 * 𝒢.rootScale)
        calc Metric.infDist c.1 (rootPlane 𝒢).toSet ≤ min η 1 * 𝒢.rootScale := (hRtube c hcl).2.1
          _ ≤ η * 𝒢.rootScale := mul_le_mul_of_nonneg_right hminη hℓ.le
          _ ≤ η * (48 * 𝒢.rootScale) := by nlinarith
      · rw [hradJ]
        show 48 * 𝒢.rootScale / 10 ≤ stageScale 𝒢 1
        rw [stageScale, coherentScale, pow_one]

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
