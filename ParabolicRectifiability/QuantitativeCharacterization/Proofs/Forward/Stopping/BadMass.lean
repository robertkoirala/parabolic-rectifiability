import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Stopping

/-! # The bad mass

Proof of `d1b_badMass_proof`, in implication form `PartitionTreeStatement → BadMassStatement`.

Route. `∑_{Q bad} μ(Q) ≤ (2M/b) A (5R)^k`: a bad block has `a_Q > b/2`, so
`μ(Q) ≤ (2/b) a_Q μ(Q)` (`bad_coeff`); every bad block is a forest cell, hence lies below a top
cell (level `0`, meeting `P(a,R)`); regroup the bad blocks under the tops (each bad block counted
under at least one top), so the bad energy is at most `∑_tops ∑_{Q ⊂ top} a_Q μ(Q) ≤
M ∑_tops μ(top)` (forest energy at each top); the tops are disjoint Borel cells of level `0`
inside `P(a, 5R)` (`inForest_subset`, `ℓ₀ = R`), and `LocalADR` at the support point `a` with
`5R ≤ ρ` gives `μ(P(a, 5R)) ≤ A (5R)^k`. Helpers carry the prefix `d1bbad_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

section BadMass

/-- Regrouping: if every element of `s` lies in some `D i`, the sum over `s` is at most the sum
over `i` of the sums over `D i` (`ℝ≥0∞`-valued, no countability needed). -/
theorem d1bbad_regroup {β ι : Type*} (f : β → ℝ≥0∞) (s : Set β) (D : ι → Set β)
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

/-- A bad block pays its mass by its energy: `μ(Q) ≤ (2/b) a_Q μ(Q)` when `a_Q > b/2`. -/
theorem d1bbad_mass_le_energy {b : ℝ} (hb : 0 < b) {a m : ℝ≥0∞}
    (ha : ENNReal.ofReal (b / 2) < a) : m ≤ ENNReal.ofReal (2 / b) * (a * m) := by
  have hle := ha.le
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 / b) * a := by
    calc (1 : ℝ≥0∞) = ENNReal.ofReal (2 / b) * ENNReal.ofReal (b / 2) := by
          rw [← ENNReal.ofReal_mul (div_nonneg (by norm_num) hb.le)]
          rw [show 2 / b * (b / 2) = 1 by field_simp]
          exact ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (2 / b) * a := by gcongr
  calc m = 1 * m := (one_mul m).symm
    _ ≤ (ENNReal.ofReal (2 / b) * a) * m := by gcongr
    _ = ENNReal.ofReal (2 / b) * (a * m) := mul_assoc _ _ _

/-- **Bad mass** (`BadMassStatement`, in implication form). -/
theorem d1b_badMass_proof : PartitionTreeStatement → BadMassStatement := by
  intro hTree n k μ A a R ρ Λ b M hA ha hR h5 hb hM hADR P F hE
  have hT := hTree n μ.support R P
  -- the top cells: level `0`, meeting `P(a, R)`
  let tops : Set (Space n) := {z₀ | z₀ ∈ P.center 0 ∧ (P.cell 0 z₀ ∩ Metric.ball a R).Nonempty}
  have hforest : ∀ t : tops, P.InForest a R (0, t.1) :=
    fun t => ⟨t.1, t.2.1, t.2.2, hT.isBelow_refl (0, t.1) t.2.1⟩
  -- step 1: each bad block pays its mass by its energy
  have step1 : (∑' Q : F.bad, μ (P.cellOf Q.1)) ≤
      ENNReal.ofReal (2 / b) * ∑' Q : F.bad, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun Q => d1bbad_mass_le_energy hb (F.bad_coeff Q.1 Q.2)
  -- step 2: regroup the bad blocks under the tops
  have step2 : (∑' Q : F.bad, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1)) ≤
      ∑' t : tops, P.descendantEnergy μ k Λ (0, t.1) := by
    have h := d1bbad_regroup (fun Q => P.coeff μ k Λ Q * μ (P.cellOf Q)) F.bad
      (fun t : tops => {Q | P.IsBelow Q (0, t.1)}) (fun Q hQ => by
        obtain ⟨z₀, hz₀, hne, hbelow⟩ := F.bad_forest Q hQ
        exact ⟨⟨z₀, hz₀, hne⟩, hbelow⟩)
    exact h
  -- step 3: the forest energy at each top
  have step3 : (∑' t : tops, P.descendantEnergy μ k Λ (0, t.1)) ≤
      ENNReal.ofReal M * ∑' t : tops, μ (P.cellOf (0, t.1)) := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun t => hE _ (hforest t)
  -- step 4: the tops are disjoint and lie in `P(a, 5R)`
  have step4 : (∑' t : tops, μ (P.cellOf (0, t.1))) ≤ μ (Metric.ball a (5 * R)) := by
    have hdisj : Pairwise (Function.onFun Disjoint fun t : tops => P.cellOf (0, t.1)) := by
      intro t t' hne
      exact P.cell_disjoint 0 t.1 t.2.1 t'.1 t'.2.1 (fun h => hne (Subtype.ext h))
    refine (tsum_meas_le_meas_iUnion_of_disjoint μ (fun t => P.measurable_cell _ _) hdisj).trans ?_
    refine measure_mono (Set.iUnion_subset fun t => ?_)
    refine (hT.inForest_subset a R (0, t.1) (hforest t)).trans (Metric.ball_subset_ball ?_)
    linarith
  -- step 5: upper ADR at the support point `a`
  have hρ : 0 < ρ := by linarith
  have step5 : μ (Metric.ball a (5 * R)) ≤ ENNReal.ofReal (A * (5 * R) ^ k) :=
    (hADR a ⟨ha, Metric.mem_ball_self hρ⟩ (5 * R) (by linarith) h5).2
  calc (∑' Q : F.bad, μ (P.cellOf Q.1))
      ≤ ENNReal.ofReal (2 / b) * ∑' Q : F.bad, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1) := step1
    _ ≤ ENNReal.ofReal (2 / b) * (ENNReal.ofReal M * ∑' t : tops, μ (P.cellOf (0, t.1))) := by
        gcongr
        exact step2.trans step3
    _ ≤ ENNReal.ofReal (2 / b) * (ENNReal.ofReal M * ENNReal.ofReal (A * (5 * R) ^ k)) := by
        gcongr
        exact step4.trans step5
    _ = ENNReal.ofReal (2 * M / b * (A * (5 * R) ^ k)) := by
        rw [← ENNReal.ofReal_mul hM, ← ENNReal.ofReal_mul (div_nonneg (by norm_num) hb.le)]
        congr 1
        ring

end BadMass

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
