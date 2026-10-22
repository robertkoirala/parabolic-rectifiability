import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.Metric.ProperSpace

/-! # The centre set of the terminal construction (`d1c_centerSetFields`)

Proof of `d1c_centerSetFields_proof`; the five
statements it depends on enter as hypotheses (implication form).

The centre set `𝒞 = 𝒞₀ ∪ 𝒞₊` is
* contained in `closure S`: `𝒞₀ ⊆ closure G_0` and `G_0 ⊆ S` (every member lies below the root);
  the terminal centres lie in `S_{stage - 1} ⊆ S`;
* contained in `closedBall(q, 6 ℓ_*)`: `S ⊆ P(q, 2 ℓ_*)`;
* nonempty: `q ∈ S` (`inner_subset`) and the source identity places `q` in `𝒞₀` or in a terminal
  assignment;
* closed: near a point `x ∉ 𝒞` we have `ρ(x) > 0` (zero set), so no core point and, since
  `ρ(c) < 1000 d_c = 1000 r_{stage(c)}` and `ρ` is `1`-Lipschitz, only terminal centres of the
  finitely many stages `< N` (a finite, closed set missing `x`);
* hence compact (bounded in the proper space `Space n`).

The `AncestorStatement` premise is not needed: `G_0 ⊆ S` follows from `below_root`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section Helpers

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The stage scales in product form: `r_j = 48 ℓ_* (1/10)^j`. -/
theorem d1ccenters_stageScale_eq (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    stageScale 𝒢 j = 48 * 𝒢.rootScale * (1 / 10 : ℝ) ^ j := by
  unfold stageScale coherentScale
  rw [one_div_pow, mul_one_div]

/-- The stage scales decrease. -/
theorem d1ccenters_stageScale_anti (𝒢 : GoodRegion P μ k Λ b) {j j' : ℕ} (h : j ≤ j') :
    stageScale 𝒢 j' ≤ stageScale 𝒢 j := by
  have hpos : 0 < 48 * 𝒢.rootScale := by
    have := d1c_rootScale_pos 𝒢
    linarith
  rw [d1ccenters_stageScale_eq, d1ccenters_stageScale_eq]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) h) hpos.le

/-- The stage scales become smaller than any positive number. -/
theorem d1ccenters_exists_stageScale_lt (𝒢 : GoodRegion P μ k Λ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, stageScale 𝒢 N < ε := by
  have hpos : 0 < 48 * 𝒢.rootScale := by
    have := d1c_rootScale_pos 𝒢
    linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hpos) (by norm_num : (1 / 10 : ℝ) < 1)
  refine ⟨N, ?_⟩
  rw [d1ccenters_stageScale_eq]
  calc 48 * 𝒢.rootScale * (1 / 10 : ℝ) ^ N < 48 * 𝒢.rootScale * (ε / (48 * 𝒢.rootScale)) :=
        mul_lt_mul_of_pos_left hN hpos
    _ = ε := mul_div_cancel₀ ε hpos.ne'

/-- `G_0 ⊆ S`: every member lies below the root. -/
theorem d1ccenters_levelSet_zero_subset (𝒢 : GoodRegion P μ k Λ b) :
    𝒢.levelSet 0 ⊆ 𝒢.rootCell := by
  intro z hz
  simp only [GoodRegion.levelSet, mem_iUnion, exists_prop] at hz
  obtain ⟨Q, ⟨hQ, -⟩, hzQ⟩ := hz
  exact (𝒢.below_root Q hQ).2.2 hzQ

/-- `𝒞₀ ⊆ closure G_0 ⊆ closure S`. -/
theorem d1ccenters_limitCore_subset (𝒢 : GoodRegion P μ k Λ b) :
    𝒢.limitCore ⊆ closure 𝒢.rootCell := by
  intro z hz
  have h0 : z ∈ closure (𝒢.levelSet 0) := mem_iInter.1 hz 0
  exact closure_mono (d1ccenters_levelSet_zero_subset 𝒢) h0

/-- `closure S ⊆ closedBall(q, 6 ℓ_*)`, from `S ⊆ P(q, 2 ℓ_*)`. -/
theorem d1ccenters_closure_rootCell_subset (𝒢 : GoodRegion P μ k Λ b) :
    closure 𝒢.rootCell ⊆ Metric.closedBall 𝒢.root.2 (6 * 𝒢.rootScale) := by
  have hpos : 0 < coherentScale ℓ₀ 𝒢.root.1 := d1c_rootScale_pos 𝒢
  have hs : 𝒢.rootScale = coherentScale ℓ₀ 𝒢.root.1 := rfl
  have h1 : 𝒢.rootCell ⊆ Metric.closedBall 𝒢.root.2 (6 * 𝒢.rootScale) := by
    intro z hz
    have hb := P.cell_subset_ball 𝒢.root.1 𝒢.root.2 𝒢.root_isCell hz
    rw [Metric.mem_ball] at hb
    rw [Metric.mem_closedBall, hs]
    linarith
  exact closure_minimal h1 Metric.isClosed_closedBall

/-- The root point `q` lies in its cell `S` (`inner_subset`). -/
theorem d1ccenters_root_mem (𝒢 : GoodRegion P μ k Λ b) : 𝒢.root.2 ∈ 𝒢.rootCell := by
  have hc : 𝒢.root.2 ∈ P.center 𝒢.root.1 := 𝒢.root_isCell
  have hE : 𝒢.root.2 ∈ E := P.center_subset _ hc
  have hpos : 0 < coherentScale ℓ₀ 𝒢.root.1 := d1c_rootScale_pos 𝒢
  exact P.inner_subset _ _ hc ⟨hE, Metric.mem_ball_self (by linarith)⟩

variable (C : Choice n) (𝒢 : GoodRegion P μ k Λ b)

/-- **Containment**: `𝒞 ⊆ closure S`. -/
theorem d1ccenters_subset_closure (hSF : C.StageFacts 𝒢) : C.centers 𝒢 ⊆ closure 𝒢.rootCell := by
  rintro c (hc | hc)
  · exact d1ccenters_limitCore_subset 𝒢 hc
  · exact subset_closure (hSF.kept_subset _ (hSF.termStage_spec c hc).2.2.1)

/-- **Nonemptiness**, from `q ∈ S` and the source identity. -/
theorem d1ccenters_nonempty (hAF : C.AssignmentFields 𝒢) : (C.centers 𝒢).Nonempty := by
  have hq := hAF.source_eq.subset (d1ccenters_root_mem 𝒢)
  rcases hq with ⟨-, hq⟩ | hq
  · exact ⟨_, Or.inl hq⟩
  · obtain ⟨c, hc, -⟩ := mem_iUnion₂.1 hq
    exact ⟨c, hc.1⟩

/-- **Closedness**: near a point outside `𝒞` the stopping scale is positive, so only terminal
centres of finitely many stages come close. -/
theorem d1ccenters_isClosed (hSF : C.StageFacts 𝒢)
    (hnn : ∀ z, 0 ≤ 𝒢.stopScale z) (hlip : ∀ z w, 𝒢.stopScale z ≤ 𝒢.stopScale w + dist z w)
    (hZ : ∀ z, 𝒢.stopScale z = 0 ↔ z ∈ 𝒢.limitCore) : IsClosed (C.centers 𝒢) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  by_contra hxc
  have hx0 : x ∉ 𝒢.limitCore := fun h => hxc (Or.inl h)
  have hxT : ¬ C.IsTermCenter x := fun h => hxc (Or.inr h)
  have hρpos : 0 < 𝒢.stopScale x :=
    lt_of_le_of_ne (hnn x) (fun h => hx0 ((hZ x).1 h.symm))
  obtain ⟨N, hN⟩ := d1ccenters_exists_stageScale_lt 𝒢 (ε := 𝒢.stopScale x / 2000) (by positivity)
  -- the terminal centres of the stages `1 ≤ j < N`: a finite set
  let F : Set (Space n) :=
    ⋃ j ∈ Set.Ico 1 N, ⋃ i ∈ {i : ℕ | i < C.termCount j}, {C.term j i}
  have hFfin : F.Finite :=
    Set.Finite.biUnion (Set.finite_Ico 1 N) fun j _ =>
      Set.Finite.biUnion (Set.finite_lt_nat _) fun i _ => Set.finite_singleton _
  have hxF : x ∉ F := by
    intro h
    simp only [F, mem_iUnion, exists_prop, mem_Ico, mem_ofPred_eq, mem_singleton_iff] at h
    obtain ⟨j, ⟨hj1, -⟩, i, hi, hxi⟩ := h
    exact hxT ⟨j, hj1, i, hi, hxi.symm⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hFfin.isClosed.isOpen_compl x hxF
  obtain ⟨y, hy, hxy⟩ :=
    Metric.mem_closure_iff.1 hx (min δ (𝒢.stopScale x / 2)) (lt_min hδ (by positivity))
  have hyδ : dist x y < δ := lt_of_lt_of_le hxy (min_le_left _ _)
  have hyη : dist x y < 𝒢.stopScale x / 2 := lt_of_lt_of_le hxy (min_le_right _ _)
  have hρy : 𝒢.stopScale x / 2 < 𝒢.stopScale y := by
    have := hlip x y
    linarith
  rcases hy with hy0 | hyT
  · have := (hZ y).2 hy0
    linarith
  · obtain ⟨h1, ⟨i, hi, hti⟩, -, hrad⟩ := hSF.termStage_spec y hyT
    have hc := (hSF.term_center y hyT).2.2
    rw [hrad] at hc
    have hs : C.termStage y < N := by
      by_contra hs
      have := d1ccenters_stageScale_anti 𝒢 (not_lt.1 hs)
      linarith
    have hyF : y ∈ F := by
      simp only [F, mem_iUnion, exists_prop, mem_Ico, mem_ofPred_eq, mem_singleton_iff]
      exact ⟨_, ⟨h1, hs⟩, i, hi, hti.symm⟩
    exact hball (Metric.mem_ball'.2 hyδ) hyF

end Helpers

/-- **The centre set is compact, nonempty and in `closure S ⊆ closedBall(q, 6 ℓ_*)`**:
proof of `d1c_centerSetFields_proof`. -/
theorem d1c_centerSetFields_proof :
    AncestorStatement → StopScaleLipschitzStatement → StopScaleZeroStatement →
      StageFactsStatement → AssignmentFieldsStatement → CenterSetFieldsStatement := by
  intro _hAnc hLip hZero hStage hAssign n E ℓ₀ P μ k Λ b 𝒢 C hSel
  have hSF := hStage n E ℓ₀ P μ k Λ b 𝒢 C hSel
  have hAF := hAssign n E ℓ₀ P μ k Λ b 𝒢 C hSel
  obtain ⟨hnn, hlip, -, -⟩ := hLip n E ℓ₀ P μ k Λ b 𝒢
  have hZ := hZero n E ℓ₀ P μ k Λ b 𝒢
  have hsub := d1ccenters_subset_closure C 𝒢 hSF
  have hsub6 := hsub.trans (d1ccenters_closure_rootCell_subset 𝒢)
  have hcl := d1ccenters_isClosed C 𝒢 hSF hnn hlip hZ
  exact
    { isCompact_centers :=
        Metric.isCompact_of_isClosed_isBounded hcl (Metric.isBounded_closedBall.subset hsub6)
      centers_nonempty := d1ccenters_nonempty C 𝒢 hAF
      centers_subset_closure := hsub
      centers_subset := hsub6 }

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
