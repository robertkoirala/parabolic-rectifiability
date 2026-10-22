import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Measure.ScaleEnergy
import ParabolicRectifiability.Metric.Hausdorff
import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import ParabolicRectifiability.Enhancements.Statements.ScaledCore
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # Fivefold selection of dense balls

Proves `b4_fivefold_density_selection_proof`, with exactly the type of
`b4_fivefold_density_selection`. `FivefoldSelectionStatement` is the first argument of that
type and is used as a hypothesis; it is discharged by `fivefold_ball_selection_proof`.

Route. Let `P(z)` be the density property at `z`; the exceptional set
`{z | ¬ P(z)}` is `ν`-null by `ae_iff` (no measurability is used). Fivefold selection is applied once in
`X = Space n` (balls of `X`) to the index type of all pairs `(z, r)` with `0 < r`,
`10 r < s` and `ν(P(z,r)) ≥ c r^k`, centres `z`, radii `r`, bound `s/10`. It returns a
countable pairwise disjoint `J₀`. **Injective reindexing**: choose an
injection `q : J₀ → ℕ`, set `J = range q`, and transport centres and radii through the
equivalence `Equiv.ofInjective q : J₀ ≃ J`; pairwise disjointness transfers because the
equivalence is injective. The bounds `0 < r_j`, `10 r_j < s` and the mass bound hold because
every selected ball is an original member. Every `z` with `P(z)` is the centre of a member
(take its density radius below `s/10`), so it lies in some selected `P(z_j, 5 r_j)`; hence the
complement of the union lies in the null exceptional set.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- **Fivefold selection of dense balls**: the statement of `b4_fivefold_density_selection`. -/
theorem b4_fivefold_density_selection_proof :
    FivefoldSelectionStatement →
    ∀ (n k : ℕ) (ν : Measure (Space n)) (c s : ℝ), 0 < s →
      (∀ᵐ z ∂ν, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < δ ∧
        ENNReal.ofReal (c * r ^ k) ≤ ν (Metric.ball z r)) →
      ∃ (J : Set ℕ) (z : J → Space n) (r : J → ℝ), (∀ j, 0 < r j) ∧ (∀ j, 10 * r j < s) ∧
        (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) ∧
        (∀ j, ENNReal.ofReal (c * r j ^ k) ≤ ν (Metric.ball (z j) (r j))) ∧
        ν (⋃ j, Metric.ball (z j) (5 * r j))ᶜ = 0 := by
  intro h5 n k ν c s hs hae
  -- The density exception, `ν`-null as an outer-measure statement.
  have hnull := ae_iff.1 hae
  -- Fivefold selection once, in `X = Space n`, on all dense balls with `10 r < s`.
  obtain ⟨J₀, hJc, hJd, hJcov⟩ := h5 (Space n)
    {p : Space n × ℝ // 0 < p.2 ∧ 10 * p.2 < s ∧
      ENNReal.ofReal (c * p.2 ^ k) ≤ ν (Metric.ball p.1 p.2)}
    (fun p => p.1.1) (fun p => p.1.2) (fun p => p.2.1)
    ⟨s / 10, fun p => by
      have h10 : 10 * p.1.2 < s := p.2.2.1
      show p.1.2 ≤ s / 10
      linarith⟩
  -- Injective reindexing: `q : J₀ → ℕ` injective, `J = range q`, `E : J₀ ≃ J`.
  have : Countable J₀ := hJc.to_subtype
  obtain ⟨q, hq⟩ := Countable.exists_injective_nat J₀
  obtain ⟨E, -⟩ : ∃ E : J₀ ≃ Set.range q, E = Equiv.ofInjective q hq := ⟨_, rfl⟩
  refine ⟨Set.range q, fun j => (E.symm j).1.1.1, fun j => (E.symm j).1.1.2,
    fun j => (E.symm j).1.2.1, fun j => (E.symm j).1.2.2.1, ?_,
    fun j => (E.symm j).1.2.2.2, ?_⟩
  · -- Disjointness transfers through the injective `E.symm`.
    intro i j hij
    have hne : (E.symm i).1 ≠ (E.symm j).1 := fun h =>
      hij (E.symm.injective (Subtype.ext h))
    exact hJd (E.symm i).2 (E.symm j).2 hne
  · -- Every non-exceptional point is a centre, hence covered by a fivefold dilate.
    refine measure_mono_null (fun z hz => ?_) hnull
    simp only [Set.mem_ofPred_eq]
    intro hP
    apply hz
    obtain ⟨ρ, hρ0, hρs, hρm⟩ := hP (s / 10) (by positivity)
    obtain ⟨j, hj, hzj⟩ := hJcov ⟨(z, ρ), hρ0, by linarith, hρm⟩
    refine Set.mem_iUnion.2 ⟨E ⟨j, hj⟩, ?_⟩
    show z ∈ Metric.ball (E.symm (E ⟨j, hj⟩)).1.1.1 (5 * (E.symm (E ⟨j, hj⟩)).1.1.2)
    rw [Equiv.symm_apply_apply]
    exact hzj

end ParabolicRectifiability.Characterization
