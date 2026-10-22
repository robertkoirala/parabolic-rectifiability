import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Stopping

/-! # Root content below a forest cell

Proof of `d1b_rootContent_proof`, in implication form
`PartitionTreeStatement → PartitionEnergy.CellMassStatement → FirstEntranceStatement →
RootContentStatement`.

Route. A root `S` is a forest cell, so its centre lies in its cell, inside `P(a, R + 4R)`
(`inForest_subset`, `ℓ₀ = R`), hence in `P(a, ρ)`; and `2 ℓ_S ≤ 2R ≤ ρ`. The lower cell mass
bound gives `A⁻¹ (ℓ_S/4)^k ≤ μ(S)`, i.e. `(4ℓ_S)^k ≤ 16^k A μ(S)`. Summing over the roots below
`T` (a subfamily of the roots and bad blocks below `T`), the first-entrance inequality and
the forest energy `∑_{Q ⊂ T} a_Q μ(Q) ≤ M μ(T)` give `16^k A (μ(T) + (4/b) M μ(T))`. Helpers
carry the prefix `d1bcontent_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

section RootContent

/-- Every side is at most the top side: `ℓ_j ≤ ℓ₀`. -/
theorem d1bcontent_scale_le {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    (hT : PartitionTree P) (j : ℕ) : P.scale j ≤ ℓ₀ := by
  induction j with
  | zero => exact hT.scale_zero.le
  | succ j ih =>
    rw [hT.scale_succ]
    have := hT.scale_pos j
    linarith

/-- Lower cell mass in content form: `A⁻¹ (ℓ/4)^k ≤ m` gives `(4ℓ)^k ≤ 16^k A m`. -/
theorem d1bcontent_content_le {A ℓ : ℝ} {k : ℕ} {m : ℝ≥0∞} (hA : 0 < A) (hℓ : 0 ≤ ℓ)
    (h : ENNReal.ofReal (A⁻¹ * (ℓ / 4) ^ k) ≤ m) :
    ENNReal.ofReal (4 * ℓ) ^ k ≤ ENNReal.ofReal (16 ^ k * A) * m := by
  have hid : (4 * ℓ) ^ k = (16 ^ k * A) * (A⁻¹ * (ℓ / 4) ^ k) := by
    calc (4 * ℓ) ^ k = (16 * (ℓ / 4)) ^ k := by rw [show 16 * (ℓ / 4) = 4 * ℓ by ring]
      _ = 16 ^ k * (ℓ / 4) ^ k := mul_pow _ _ _
      _ = 16 ^ k * (A * A⁻¹) * (ℓ / 4) ^ k := by rw [mul_inv_cancel₀ hA.ne', mul_one]
      _ = (16 ^ k * A) * (A⁻¹ * (ℓ / 4) ^ k) := by ring
  have hC : (0 : ℝ) ≤ 16 ^ k * A := mul_nonneg (pow_nonneg (by norm_num) k) hA.le
  rw [← ENNReal.ofReal_pow (show (0 : ℝ) ≤ 4 * ℓ by linarith), hid, ENNReal.ofReal_mul hC]
  gcongr

/-- **Root content below a forest cell** (`RootContentStatement`, in implication form). -/
theorem d1b_rootContent_proof :
    PartitionTreeStatement → PartitionEnergy.CellMassStatement → FirstEntranceStatement →
      RootContentStatement := by
  intro hTree hCell hFirst n k μ A a R ρ Λ b M hA hR h5 hb hM hADR P F hE T hTf
  have hT := hTree n μ.support R P
  have hApos : 0 < A := by linarith
  have hTc : P.IsCell T := by
    obtain ⟨z₀, -, -, hb'⟩ := hTf
    exact hb'.1
  -- each root below `T`: `(4ℓ_S)^k ≤ 16^k A μ(S)`
  have hroot : ∀ S : {S : ℕ × Space n // S ∈ F.roots ∧ P.IsBelow S T},
      ENNReal.ofReal (4 * P.scale S.1.1) ^ k ≤
        ENNReal.ofReal (16 ^ k * A) * μ (P.cellOf S.1) := by
    intro S
    have hfor := F.roots_forest S.1 S.2.1
    have hcell : P.IsCell S.1 := S.2.2.1
    have hz : S.1.2 ∈ Metric.ball a ρ :=
      Metric.ball_subset_ball (by linarith)
        (hT.inForest_subset a R S.1 hfor (hT.center_mem_cell S.1 hcell))
    have hsc := d1bcontent_scale_le hT S.1.1
    have hpos := hT.scale_pos S.1.1
    have h2 : 2 * P.scale S.1.1 ≤ ρ := by linarith
    exact d1bcontent_content_le hApos hpos.le
      (hCell n k μ A a ρ R P hADR S.1 hcell hz h2).1
  -- the roots below `T` are among the roots and bad blocks below `T`
  let f : {S : ℕ × Space n // S ∈ F.roots ∧ P.IsBelow S T} →
      {S : ℕ × Space n // (S ∈ F.roots ∨ S ∈ F.bad) ∧ P.IsBelow S T} :=
    fun S => ⟨S.1, Or.inl S.2.1, S.2.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext h
  have hsub : (∑' S : {S : ℕ × Space n // S ∈ F.roots ∧ P.IsBelow S T}, μ (P.cellOf S.1)) ≤
      ∑' S : {S : ℕ × Space n // (S ∈ F.roots ∨ S ∈ F.bad) ∧ P.IsBelow S T},
        μ (P.cellOf S.1) :=
    ENNReal.tsum_comp_le_tsum_of_injective hf (fun S => μ (P.cellOf S.1))
  have hfirst := hFirst n μ.support R P μ k Λ b a R hb F T hTc
  have hen := hE T hTf
  have hC : (0 : ℝ) ≤ 16 ^ k * A := mul_nonneg (pow_nonneg (by norm_num) k) hApos.le
  have hMb : (0 : ℝ) ≤ 4 * M / b := div_nonneg (mul_nonneg (by norm_num) hM) hb.le
  have h4b : (0 : ℝ) ≤ 4 / b := div_nonneg (by norm_num) hb.le
  calc (∑' S : {S : ℕ × Space n // S ∈ F.roots ∧ P.IsBelow S T},
          ENNReal.ofReal (4 * P.scale S.1.1) ^ k)
      ≤ ∑' S : {S : ℕ × Space n // S ∈ F.roots ∧ P.IsBelow S T},
          ENNReal.ofReal (16 ^ k * A) * μ (P.cellOf S.1) := ENNReal.tsum_le_tsum hroot
    _ = ENNReal.ofReal (16 ^ k * A) *
          ∑' S : {S : ℕ × Space n // S ∈ F.roots ∧ P.IsBelow S T}, μ (P.cellOf S.1) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (16 ^ k * A) *
          (μ (P.cellOf T) + ENNReal.ofReal (4 / b) * P.descendantEnergy μ k Λ T) := by
        gcongr
        exact hsub.trans hfirst
    _ ≤ ENNReal.ofReal (16 ^ k * A) *
          (μ (P.cellOf T) + ENNReal.ofReal (4 / b) * (ENNReal.ofReal M * μ (P.cellOf T))) := by
        gcongr
    _ = ENNReal.ofReal (16 ^ k * A * (1 + 4 * M / b)) * μ (P.cellOf T) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_add zero_le_one hMb, ENNReal.ofReal_one,
          show 4 * M / b = 4 / b * M by ring, ENNReal.ofReal_mul h4b]
        ring

end RootContent

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
