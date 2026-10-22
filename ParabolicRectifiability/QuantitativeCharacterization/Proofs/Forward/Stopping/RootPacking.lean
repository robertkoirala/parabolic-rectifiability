import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Stopping

/-! # Root packing

Proof of `d1b_rootPacking_proof`, in implication form
`PartitionTreeStatement → RootContentStatement → RootPackingStatement`.

Route. Every root is a forest cell, hence lies below a top cell (level `0`, meeting `P(a,R)`).
Regroup the sum over the roots under the tops (each root counted under at least one top), apply
root content at each top (a forest cell): `∑_{S ⊂ top} (4ℓ_S)^k ≤ 16^k A (1 + 4M/b) μ(top)`.
The tops are disjoint Borel cells of level `0` inside `P(a, 5R)` (`inForest_subset`, `ℓ₀ = R`),
and `LocalADR` at the support point `a` with `5R ≤ ρ` gives `μ(P(a, 5R)) ≤ A (5R)^k`; then
`16^k · 5^k = 80^k`. Helpers carry the prefix `d1brootpack_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

section RootPacking

/-- Regrouping: if every element of `s` lies in some `D i`, the sum over `s` is at most the sum
over `i` of the sums over `D i` (`ℝ≥0∞`-valued, no countability needed). -/
theorem d1brootpack_regroup {β ι : Type*} (f : β → ℝ≥0∞) (s : Set β) (D : ι → Set β)
    (hcov : ∀ x ∈ s, ∃ i, x ∈ D i) :
    (∑' x : s, f x) ≤ ∑' i, ∑' x : D i, f x := by
  rw [tsum_subtype s f]
  calc ∑' x, s.indicator f x ≤ ∑' x, ∑' i, (D i).indicator f x := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ s
        · obtain ⟨i, hi⟩ := hcov x hx
          rw [Set.indicator_of_mem hx]
          calc f x = (D i).indicator f x := (Set.indicator_of_mem hi f).symm
            _ ≤ ∑' i, (D i).indicator f x := ENNReal.le_tsum (f := fun i => (D i).indicator f x) i
        · rw [Set.indicator_of_notMem hx]
          exact zero_le
    _ = ∑' i, ∑' x, (D i).indicator f x := ENNReal.tsum_comm
    _ = ∑' i, ∑' x : D i, f x := tsum_congr fun i => (tsum_subtype (D i) f).symm

/-- **Root packing** (`RootPackingStatement`, in implication form). -/
theorem d1b_rootPacking_proof :
    PartitionTreeStatement → RootContentStatement → RootPackingStatement := by
  intro hTree hRC n k μ A a R ρ Λ b M hA ha hR h5 hb hM hADR P F hE
  have hT := hTree n μ.support R P
  -- the top cells: level `0`, meeting `P(a, R)`
  let tops : Set (Space n) := {z₀ | z₀ ∈ P.center 0 ∧ (P.cell 0 z₀ ∩ Metric.ball a R).Nonempty}
  have hforest : ∀ t : tops, P.InForest a R (0, t.1) :=
    fun t => ⟨t.1, t.2.1, t.2.2, hT.isBelow_refl (0, t.1) t.2.1⟩
  have hApos : 0 < A := by linarith
  have hMb : (0 : ℝ) ≤ 4 * M / b := div_nonneg (mul_nonneg (by norm_num) hM) hb.le
  have hC : (0 : ℝ) ≤ 16 ^ k * A * (1 + 4 * M / b) :=
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) k) hApos.le) (by linarith)
  -- step 1: regroup the roots under the tops
  have step1 : (∑' S : F.roots, ENNReal.ofReal (4 * P.scale S.1.1) ^ k) ≤
      ∑' t : tops, ∑' S : {S : ℕ × Space n // S ∈ F.roots ∧ P.IsBelow S (0, t.1)},
        ENNReal.ofReal (4 * P.scale S.1.1) ^ k := by
    have h := d1brootpack_regroup (fun S : ℕ × Space n => ENNReal.ofReal (4 * P.scale S.1) ^ k)
      F.roots (fun t : tops => {S | S ∈ F.roots ∧ P.IsBelow S (0, t.1)}) (fun S hS => by
        obtain ⟨z₀, hz₀, hne, hbelow⟩ := F.roots_forest S hS
        exact ⟨⟨z₀, hz₀, hne⟩, hS, hbelow⟩)
    exact h
  -- step 2: root content at each top
  have step2 : (∑' t : tops, ∑' S : {S : ℕ × Space n // S ∈ F.roots ∧ P.IsBelow S (0, t.1)},
        ENNReal.ofReal (4 * P.scale S.1.1) ^ k) ≤
      ENNReal.ofReal (16 ^ k * A * (1 + 4 * M / b)) * ∑' t : tops, μ (P.cellOf (0, t.1)) := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun t =>
      hRC n k μ A a R ρ Λ b M hA hR h5 hb hM hADR P F hE (0, t.1) (hforest t)
  -- step 3: the tops are disjoint and lie in `P(a, 5R)`
  have step3 : (∑' t : tops, μ (P.cellOf (0, t.1))) ≤ μ (Metric.ball a (5 * R)) := by
    have hdisj : Pairwise (Function.onFun Disjoint fun t : tops => P.cellOf (0, t.1)) := by
      intro t t' hne
      exact P.cell_disjoint 0 t.1 t.2.1 t'.1 t'.2.1 (fun h => hne (Subtype.ext h))
    refine (tsum_meas_le_meas_iUnion_of_disjoint μ (fun t => P.measurable_cell _ _) hdisj).trans ?_
    refine measure_mono (Set.iUnion_subset fun t => ?_)
    refine (hT.inForest_subset a R (0, t.1) (hforest t)).trans (Metric.ball_subset_ball ?_)
    linarith
  -- step 4: upper ADR at the support point `a`
  have hρ : 0 < ρ := by linarith
  have step4 : μ (Metric.ball a (5 * R)) ≤ ENNReal.ofReal (A * (5 * R) ^ k) :=
    (hADR a ⟨ha, Metric.mem_ball_self hρ⟩ (5 * R) (by linarith) h5).2
  calc (∑' S : F.roots, ENNReal.ofReal (4 * P.scale S.1.1) ^ k)
      ≤ ENNReal.ofReal (16 ^ k * A * (1 + 4 * M / b)) * ∑' t : tops, μ (P.cellOf (0, t.1)) :=
        step1.trans step2
    _ ≤ ENNReal.ofReal (16 ^ k * A * (1 + 4 * M / b)) * ENNReal.ofReal (A * (5 * R) ^ k) := by
        gcongr
        exact step3.trans step4
    _ = ENNReal.ofReal (80 ^ k * A ^ 2 * (1 + 4 * M / b) * R ^ k) := by
        rw [← ENNReal.ofReal_mul hC]
        congr 1
        rw [mul_pow, show (80 : ℝ) ^ k = 16 ^ k * 5 ^ k by rw [← mul_pow]; norm_num]
        ring

end RootPacking

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
