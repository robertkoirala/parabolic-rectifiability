import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Measure.ScaleEnergy
import ParabolicRectifiability.Metric.Hausdorff
import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import ParabolicRectifiability.Enhancements.Statements.ScaledCore
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # The actual supports carry the retained measures

Proves `b4_cover_of_localCoreDecomposition_proof`, with exactly the type of
`b4_cover_of_localCoreDecomposition`: the cover clause of the threshold input.

Witness. With `K_H = supp(μ⌊E_H)` and `K_V = supp(μ⌊E_V)`, take
`U = K_H` for `T = horizontal`, `U = K_V` for `T = vertical` and `U = K_H ∪ K_V` for
`T = mixed`. The typed cover of `U` at tolerance `ε` comes from the `supports` bundle (for
`mixed`, the two families with one common Hausdorff-null remainder). For the mass bound,
`μ(S) = μ⌊(E_H ∪ E_V)ᶜ(S) + μ⌊E_H(S) + μ⌊E_V(S)` for `S = P(a,R) \ U` (the decomposition
field, applied to an arbitrary set); `μ⌊E_T(S) ≤ μ⌊E_T(K_Tᶜ) = 0` when `K_T ⊆ U`
(`Measure.measure_compl_support`, `Space n` second countable), and for a fixed family the
other support is empty (`horizontal_only`, `vertical_only`). Since `U` contains the supports
themselves, the Hausdorff-null graph exceptions only enter the cover clause, so the absolute
continuity hypothesis is not needed. No measurability of graph images is used.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- A horizontal cover of `K_H` and a general regular vertical cover of `K_V` at the same
tolerance give a mixed typed cover of `K_H ∪ K_V`, with the union of the two Hausdorff-null
remainders as common remainder. -/
theorem b4p4_mixed_cover {n k : ℕ} {KH KV : Set (Space n)} {ε : ℝ}
    (hH : HasHorizontalGraphCover k KH ε) (hV : HasGeneralRegularVerticalGraphCover k KV ε) :
    HasTypedGraphCover FamilyKind.mixed k (KH ∪ KV) ε := by
  obtain ⟨I, H, hHnull⟩ := hH
  obtain ⟨J, V, hVnull⟩ := hV
  have hcover : ∃ (I J : Set ℕ) (H : I → HorizontalGraph n k ε)
      (V : J → GeneralRegularVerticalGraph n k ε),
      hausdorffP n k ((KH ∪ KV) \ ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)) = 0 := by
    refine ⟨I, J, H, V, ?_⟩
    refine measure_mono_null ?_ (measure_union_null hHnull hVnull)
    intro z hz
    rcases hz with ⟨hzK | hzK, hzU⟩
    · exact Or.inl ⟨hzK, fun h => hzU (Or.inl h)⟩
    · exact Or.inr ⟨hzK, fun h => hzU (Or.inr h)⟩
  exact hcover

/-- A measure vanishes on every set disjoint from a superset of its support
(`Measure.measure_compl_support`, `Space n` is second countable). -/
theorem b4p4_measure_diff_eq_zero {n : ℕ} (ν : Measure (Space n)) (B U : Set (Space n))
    (hU : ν.support ⊆ U) : ν (B \ U) = 0 := by
  refine measure_mono_null ?_ (Measure.measure_compl_support (μ := ν))
  intro z hz hzK
  exact hz.2 (hU hzK)

/-- The restriction decomposition `μ = μ⌊(E_H ∪ E_V)ᶜ + μ⌊E_H + μ⌊E_V`, evaluated on the
arbitrary set `B \ U`: if both retained parts vanish there, then
`μ(B \ U) ≤ μ⌊(E_H ∪ E_V)ᶜ(B)`. -/
theorem b4p4_measure_diff_le {n : ℕ} (μ : Measure (Space n)) (EH EV B U : Set (Space n))
    (hEq : μ = μ.restrict (EH ∪ EV)ᶜ + μ.restrict EH + μ.restrict EV)
    (hH : μ.restrict EH (B \ U) = 0) (hV : μ.restrict EV (B \ U) = 0) :
    μ (B \ U) ≤ μ.restrict (EH ∪ EV)ᶜ B := by
  have h1 := congrArg (fun m : Measure (Space n) => m (B \ U)) hEq
  simp only [Measure.add_apply] at h1
  rw [h1, hH, hV, add_zero, add_zero]
  exact measure_mono sdiff_subset

/-- **Cover by the actual supports**: the statement of `b4_cover_of_localCoreDecomposition`.
For every `ε > 0` the set `U` (the permitted actual support, or
the union of both actual supports for `T = mixed`) has a typed graph cover of type `T` at
tolerance `ε` modulo `H_P^k`, and `μ(P(a,R) \ U) ≤ μ⌊(E_H ∪ E_V)ᶜ(P(a,R))`. -/
theorem b4_cover_of_localCoreDecomposition_proof :
    ∀ (n k : ℕ) (T : FamilyKind) (C : ℝ) (a : Space n) (R : ℝ) (μ : Measure (Space n))
      (EH EV : Set (Space n)), μ ≪ hausdorffP n k →
      Enhancements.IsLocalCoreDecomposition k T C a R μ EH EV →
      ∀ ε : ℝ, 0 < ε → ∃ U : Set (Space n), HasTypedGraphCover T k U ε ∧
        μ (Metric.ball a R \ U) ≤ μ.restrict (EH ∪ EV)ᶜ (Metric.ball a R) := by
  intro n k T C a R μ EH EV _hac hD ε hε
  cases T with
  | horizontal =>
    refine ⟨(μ.restrict EH).support, hD.supports.horizontal_graphs ε hε, ?_⟩
    refine b4p4_measure_diff_le μ EH EV _ _ hD.measure_eq ?_ ?_
    · exact b4p4_measure_diff_eq_zero _ _ _ subset_rfl
    · refine b4p4_measure_diff_eq_zero _ _ _ ?_
      rw [(hD.horizontal_only rfl).2]
      exact empty_subset _
  | vertical =>
    refine ⟨(μ.restrict EV).support, hD.supports.vertical_graphs ε hε, ?_⟩
    refine b4p4_measure_diff_le μ EH EV _ _ hD.measure_eq ?_ ?_
    · refine b4p4_measure_diff_eq_zero _ _ _ ?_
      rw [(hD.vertical_only rfl).2]
      exact empty_subset _
    · exact b4p4_measure_diff_eq_zero _ _ _ subset_rfl
  | mixed =>
    refine ⟨(μ.restrict EH).support ∪ (μ.restrict EV).support,
      b4p4_mixed_cover (hD.supports.horizontal_graphs ε hε) (hD.supports.vertical_graphs ε hε),
      ?_⟩
    refine b4p4_measure_diff_le μ EH EV _ _ hD.measure_eq ?_ ?_
    · exact b4p4_measure_diff_eq_zero _ _ _ subset_union_left
    · exact b4p4_measure_diff_eq_zero _ _ _ subset_union_right

end ParabolicRectifiability.Characterization
