import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Total labelled length of the segment tree

The total length is a sum over labels, with multiplicities retained.  Coding a
label and recording its length gives a complete partition into generations,
including the empty label at generation zero. -/

noncomputable section

open scoped ENNReal

namespace ParabolicRectifiability.Examples

/-- Denumerable coding restricts to a bijection on valid labels. -/
private def e2_sapValidCodeEquiv :
    {l : List (ℕ × ℕ) // e2_sapValid l} ≃ e2_sapIndex where
  toFun l := ⟨Denumerable.eqv (List (ℕ × ℕ)) l.1, by
    simpa [e2_sapIndex, e2_sapLabel, Denumerable.eqv] using l.2⟩
  invFun i := ⟨e2_sapLabel i, i.2⟩
  left_inv := by
    intro l
    apply Subtype.ext
    change Denumerable.ofNat (List (ℕ × ℕ)) (Encodable.encode l.1) = l.1
    exact Denumerable.ofNat_encode _
  right_inv := by
    intro i
    apply Subtype.ext
    change Encodable.encode (Denumerable.ofNat (List (ℕ × ℕ)) i.1) = i.1
    exact Denumerable.encode_ofNat _

/-- Recording the length partitions all valid labels, including length zero.
No segment geometry enters this equivalence, so coincident segments remain distinct. -/
private def e2_sapGenerationLabelEquiv :
    (Σ g : ℕ, {l : List (ℕ × ℕ) // e2_sapValid l ∧ l.length = g}) ≃
      {l : List (ℕ × ℕ) // e2_sapValid l} where
  toFun l := ⟨l.2.1, l.2.2.1⟩
  invFun l := ⟨l.1.length, ⟨l.1, l.2, rfl⟩⟩
  left_inv := by
    rintro ⟨g, l, hl, hg⟩
    cases hg
    rfl
  right_inv _ := rfl

private def e2_sapGenerationCodeEquiv :=
  e2_sapGenerationLabelEquiv.trans e2_sapValidCodeEquiv

/-- The weights and exact generation identities bound the full labelled length. -/
theorem e2_sap_treeLength_proof (hW : E2sapWeights) (hGen : E2sapGeneration) :
    E2sapTreeLength := by
  have hD : (∑' j : ℕ, ENNReal.ofReal (e2_sapDelta (j + 1))) ≤
      ENNReal.ofReal (1 / 100) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => (hW.1 (j + 1)).1.le) hW.2.1]
    exact ENNReal.ofReal_le_ofReal hW.2.2
  unfold E2sapTreeLength
  calc
    (∑' i : e2_sapIndex, ENNReal.ofReal (e2_sapLength i)) =
        ∑' l : (Σ g : ℕ, {l : List (ℕ × ℕ) // e2_sapValid l ∧ l.length = g}),
          ENNReal.ofReal (e2_sapSeg l.2.1).2.1 := by
      rw [← e2_sapGenerationCodeEquiv.tsum_eq
        (fun i : e2_sapIndex => ENNReal.ofReal (e2_sapLength i))]
      apply tsum_congr
      intro l
      change ENNReal.ofReal (e2_sapSeg
        (Denumerable.ofNat (List (ℕ × ℕ)) (Encodable.encode l.2.1))).2.1 = _
      rw [Denumerable.ofNat_encode]
    _ = ∑' g : ℕ, (∑' j : ℕ, ENNReal.ofReal (e2_sapDelta (j + 1))) ^ g := by
      rw [ENNReal.tsum_sigma']
      exact tsum_congr hGen
    _ ≤ ∑' g : ℕ, (ENNReal.ofReal (1 / 100)) ^ g := by
      exact ENNReal.tsum_le_tsum fun g => pow_le_pow_left' hD g
    _ = ENNReal.ofReal (100 / 99) := by
      rw [ENNReal.tsum_geometric]
      calc
        (1 - ENNReal.ofReal (1 / 100))⁻¹ =
            (ENNReal.ofReal ((1 : ℝ) - 1 / 100))⁻¹ := by
          rw [ENNReal.ofReal_sub _ (by norm_num), ENNReal.ofReal_one]
        _ = ENNReal.ofReal (((1 : ℝ) - 1 / 100)⁻¹) :=
          (ENNReal.ofReal_inv_of_pos (by norm_num)).symm
        _ = ENNReal.ofReal (100 / 99) := by norm_num

end ParabolicRectifiability.Examples
