import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Stopping.Forest
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Stopping.PartitionTree
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Stopping.ExactModel
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Stopping.MixedAttainment
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Stopping.AdjacentType
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Stopping.BadMass
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Stopping.FirstEntrance
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Stopping.ExitMass
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Stopping.RootContent
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Stopping.RootPacking
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Stopping.LocalPacking
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Stopping.RegionTyping
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.CellMass

/-! # The stopping-packing statement: composition in implication form

`d1bcomp_stoppingPacking_of` and the four constant lemmas assemble the stopping-packing
estimate from its ingredient statements. The final theorem
`d1bcomp_stoppingPacking_of_fittingGap` supplies every ingredient by its proof,
`d1b_input_cellMass` by `d1a_cellMass_proof`, and
`d1b_input_fittingGap` by the hypothesis `PartitionEnergy.FittingGapStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

/-- Elementary: `1 + 4x ≤ 4 (1 + x)` for `x = M/b ≥ 0`. -/
theorem d1bcomp_factor_le {M b : ℝ} (hM : 0 ≤ M) (hb : 0 < b) :
    1 + 4 * M / b ≤ 4 * (1 + M / b) := by
  have hx : 0 ≤ M / b := div_nonneg hM hb.le
  have h4 : 4 * M / b = 4 * (M / b) := by ring
  rw [h4]
  linarith

/-- Root-packing constant: `80^k A² (1 + 4M/b) R^k ≤ 4·192^k A² (1 + M/b) R^k`. -/
theorem d1bcomp_rootConst_le (k : ℕ) {A M b R : ℝ} (hM : 0 ≤ M) (hb : 0 < b) (hR : 0 ≤ R) :
    80 ^ k * A ^ 2 * (1 + 4 * M / b) * R ^ k ≤ 4 * 192 ^ k * A ^ 2 * (1 + M / b) * R ^ k := by
  have hp : (80 : ℝ) ^ k ≤ 192 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
  have hRk : 0 ≤ R ^ k := pow_nonneg hR k
  have hf := d1bcomp_factor_le hM hb
  have hf0 : 0 ≤ 1 + 4 * M / b := by
    have : 0 ≤ 4 * M / b := div_nonneg (by linarith) hb.le
    linarith
  have h1 : 80 ^ k * A ^ 2 ≤ 192 ^ k * A ^ 2 := mul_le_mul_of_nonneg_right hp hA2
  have h2 : 80 ^ k * A ^ 2 * (1 + 4 * M / b) ≤ 192 ^ k * A ^ 2 * (4 * (1 + M / b)) :=
    mul_le_mul h1 hf hf0 (by positivity)
  calc 80 ^ k * A ^ 2 * (1 + 4 * M / b) * R ^ k
      ≤ 192 ^ k * A ^ 2 * (4 * (1 + M / b)) * R ^ k := mul_le_mul_of_nonneg_right h2 hRk
    _ = 4 * 192 ^ k * A ^ 2 * (1 + M / b) * R ^ k := by ring

/-- Local-packing constant: `192^k A² (1 + 4M/b) s^k ≤ 4·192^k A² (1 + M/b) s^k`. -/
theorem d1bcomp_localConst_le (k : ℕ) {A M b s : ℝ} (hM : 0 ≤ M) (hb : 0 < b) (hs : 0 ≤ s) :
    192 ^ k * A ^ 2 * (1 + 4 * M / b) * s ^ k ≤ 4 * 192 ^ k * A ^ 2 * (1 + M / b) * s ^ k := by
  have hc : 0 ≤ (192 : ℝ) ^ k * A ^ 2 := by positivity
  have hsk : 0 ≤ s ^ k := pow_nonneg hs k
  have hf := d1bcomp_factor_le hM hb
  have h2 : 192 ^ k * A ^ 2 * (1 + 4 * M / b) ≤ 192 ^ k * A ^ 2 * (4 * (1 + M / b)) :=
    mul_le_mul_of_nonneg_left hf hc
  calc 192 ^ k * A ^ 2 * (1 + 4 * M / b) * s ^ k
      ≤ 192 ^ k * A ^ 2 * (4 * (1 + M / b)) * s ^ k := mul_le_mul_of_nonneg_right h2 hsk
    _ = 4 * 192 ^ k * A ^ 2 * (1 + M / b) * s ^ k := by ring

/-- Bad-mass constant: `(2M/b) A (5R)^k ≤ 4·192^k A² (1 + M/b) R^k` for `A ≥ 1`. -/
theorem d1bcomp_badConst_le (k : ℕ) {A M b R : ℝ} (hA : 1 ≤ A) (hM : 0 ≤ M) (hb : 0 < b)
    (hR : 0 ≤ R) :
    2 * M / b * (A * (5 * R) ^ k) ≤ 4 * 192 ^ k * A ^ 2 * (1 + M / b) * R ^ k := by
  have hx : 0 ≤ M / b := div_nonneg hM hb.le
  have e : 2 * M / b * (A * (5 * R) ^ k) = 2 * (M / b) * (A * 5 ^ k) * R ^ k := by
    rw [mul_pow]; ring
  have h2x : 2 * (M / b) ≤ 4 * (1 + M / b) := by linarith
  have hp : (5 : ℝ) ^ k ≤ 192 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hAA : A ≤ A ^ 2 := by nlinarith
  have hA5 : A * 5 ^ k ≤ A ^ 2 * 192 ^ k :=
    mul_le_mul hAA hp (by positivity) (by positivity)
  have h3 : 2 * (M / b) * (A * 5 ^ k) ≤ 4 * (1 + M / b) * (A ^ 2 * 192 ^ k) :=
    mul_le_mul h2x hA5 (by positivity) (by positivity)
  have hRk : 0 ≤ R ^ k := pow_nonneg hR k
  rw [e]
  calc 2 * (M / b) * (A * 5 ^ k) * R ^ k
      ≤ 4 * (1 + M / b) * (A ^ 2 * 192 ^ k) * R ^ k := mul_le_mul_of_nonneg_right h3 hRk
    _ = 4 * 192 ^ k * A ^ 2 * (1 + M / b) * R ^ k := by ring

/-- **Assembly.** The combinatorial stopping, root packing, same-family local packing, bad mass and
region typing give `StoppingPackingStatement` with `Λ₀ = 3`, `C = 4·192^k·A²`, `B = 12` and
the typing threshold `b₀`. -/
theorem d1bcomp_stoppingPacking_of (hForest : StoppingForestStatement)
    (hRoot : RootPackingStatement) (hLocal : LocalPackingStatement) (hBad : BadMassStatement)
    (hType : RegionTypingStatement) : StoppingPackingStatement := by
  intro n hn k hk hkn A hA
  refine ⟨3, by norm_num, fun Λ hΛ => ?_⟩
  obtain ⟨b₀, hb₀, htyp⟩ := hType n hn k hk hkn A hA Λ hΛ
  have hC : (1 : ℝ) ≤ 4 * 192 ^ k * A ^ 2 := by
    have h1 : (1 : ℝ) ≤ 192 ^ k := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ A ^ 2 := one_le_pow₀ hA
    nlinarith
  refine ⟨4 * 192 ^ k * A ^ 2, hC, 12, by norm_num, b₀, hb₀, ?_⟩
  intro b hb hbb μ hμc _hμi a ha R hR M hM hADR P hE
  obtain ⟨F⟩ := hForest n μ.support R P μ k Λ b a R hb
  have hreg : ∀ S : F.roots,
      ∃ G : GoodRegion P μ k Λ b, G.root = S.1 ∧ G.members = F.members S.1 := fun S =>
    htyp b hb hbb μ hμc a R (12 * R) hR (by linarith) hADR P F S.1 S.2
  choose G hGroot hGmem using hreg
  refine ⟨{
    bad := F.bad
    roots := F.roots
    region := G
    region_root := hGroot
    bad_forest := F.bad_forest
    roots_forest := F.roots_forest
    bad_coeff := F.bad_coeff
    classify := ?_
    root_packing := ?_
    local_packing := ?_
    bad_mass := ?_ }⟩
  · intro Q hQ
    rcases F.classify Q hQ with ⟨hQb, hQn⟩ | ⟨hQb, hQex⟩
    · exact Or.inl ⟨hQb, fun S => by rw [hGmem S]; exact hQn S⟩
    · refine Or.inr ⟨hQb, ?_⟩
      simpa only [hGmem] using hQex
  · exact (hRoot n k μ A a R (12 * R) Λ b M hA ha hR (by linarith) hb hM hADR P F hE).trans
      (ENNReal.ofReal_le_ofReal (d1bcomp_rootConst_le k hM hb hR.le))
  · intro w s hs
    exact (hLocal n k μ A a R (12 * R) Λ b M hA ha hR le_rfl hb hM hADR P F hE w s hs).trans
      (ENNReal.ofReal_le_ofReal (d1bcomp_localConst_le k hM hb hs.le))
  · exact (hBad n k μ A a R (12 * R) Λ b M hA ha hR (by linarith) hb hM hADR P F hE).trans
      (ENNReal.ofReal_le_ofReal (d1bcomp_badConst_le k hA hM hb hR.le))

/-- **The stopping-packing estimate** (`StoppingPackingStatement`, the type of `d1_hub_stoppingPacking`) from the
proofs of its ingredients, with the one remaining hypothesis `PartitionEnergy.FittingGapStatement`
(proved by `d1a_fittingGap_proof`). -/
theorem d1bcomp_stoppingPacking_of_fittingGap (hGap : PartitionEnergy.FittingGapStatement) :
    StoppingPackingStatement := by
  have hExit : ExitMassStatement := d1b_exitMass_proof d1b_partitionTree_proof
  have hEntrance : FirstEntranceStatement :=
    d1b_firstEntrance_proof d1b_partitionTree_proof hExit
  have hContent : RootContentStatement :=
    d1b_rootContent_proof d1b_partitionTree_proof PartitionEnergy.d1a_cellMass_proof hEntrance
  have hRootPacking : RootPackingStatement :=
    d1b_rootPacking_proof d1b_partitionTree_proof hContent
  have hLocalPacking : LocalPackingStatement :=
    d1b_localPacking_proof d1b_partitionTree_proof hContent hRootPacking
  have hTyping : RegionTypingStatement :=
    d1b_regionTyping_proof d1b_partitionTree_proof d1b_exactModel_proof
      (d1b_mixedAttainment_proof d1b_exactModel_proof)
      (d1b_adjacentType_proof d1b_partitionTree_proof hGap)
  exact d1bcomp_stoppingPacking_of (d1b_stoppingForest_proof d1b_partitionTree_proof)
    hRootPacking hLocalPacking (d1b_badMass_proof d1b_partitionTree_proof) hTyping

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
