import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Labelled generation lengths

The children of a fixed parent at scale `j` have total length `δ_j L`.
A bijection with parent labels, positive scale indices and all child indices
then turns the generation sum into multiplication by `D`. This is a sum with
labelled multiplicity; no equality of set measure with that sum is used.
-/

noncomputable section

open scoped ENNReal

namespace ParabolicRectifiability.Examples

private abbrev Generation (g : ℕ) :=
  {l : List (ℕ × ℕ) // e2_sapValid l ∧ l.length = g}

private def generationCons (g : ℕ)
    (p : Σ _l : Generation g, Σ j : ℕ, Fin (e2_sapN (j + 1))) : Generation (g + 1) :=
  ⟨(p.2.1 + 1, p.2.2.val) :: p.1.val, by
    constructor
    · intro q hq
      rcases List.mem_cons.mp hq with hq | hq
      · subst q
        exact ⟨Nat.le_add_left 1 p.2.1, p.2.2.isLt⟩
      · exact p.1.property.1 q hq
    · simp only [List.length_cons, p.1.property.2]⟩

private theorem generationCons_bijective (g : ℕ) : Function.Bijective (generationCons g) := by
  constructor
  · rintro ⟨l, j, m⟩ ⟨l', j', m'⟩ h
    have hlist := congrArg Subtype.val h
    change (j + 1, m.val) :: l.val = (j' + 1, m'.val) :: l'.val at hlist
    have hp := List.cons.inj hlist
    have hl : l = l' := Subtype.ext hp.2
    cases hl
    have hj : j = j' := Nat.add_right_cancel (congrArg Prod.fst hp.1)
    cases hj
    have hm : m = m' := Fin.ext (congrArg Prod.snd hp.1)
    cases hm
    rfl
  · rintro ⟨l, hv, hl⟩
    cases l with
    | nil => simp at hl
    | cons q l =>
      rcases q with ⟨j, m⟩
      have hq := hv (j, m) (List.mem_cons_self ..)
      have htail : e2_sapValid l := fun q hq => hv q (List.mem_cons_of_mem _ hq)
      have hlen : l.length = g := Nat.add_right_cancel hl
      cases j with
      | zero => omega
      | succ j =>
        refine ⟨⟨⟨l, htail, hlen⟩, j, ⟨m, hq.2⟩⟩, ?_⟩
        rfl

private def generationEquiv (g : ℕ) :
    (Σ _l : Generation g, Σ j : ℕ, Fin (e2_sapN (j + 1))) ≃ Generation (g + 1) :=
  Equiv.ofBijective (generationCons g) (generationCons_bijective g)

/-- Each of the `N_j` labelled children contributes, including the last child. -/
private theorem generation_child_sum (hW : E2sapWeights) (L : ℝ) (j : ℕ) :
    (∑' _m : Fin (e2_sapN j), ENNReal.ofReal (e2_sapDelta j * (L / (e2_sapN j : ℝ)))) =
      ENNReal.ofReal L * ENNReal.ofReal (e2_sapDelta j) := by
  have hN : (e2_sapN j : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero (j + 1) (by norm_num : (8 : ℕ) ≠ 0))
  calc
    _ = (e2_sapN j : ℝ≥0∞) *
        ENNReal.ofReal (e2_sapDelta j * (L / (e2_sapN j : ℝ))) := by
      simp [tsum_fintype, nsmul_eq_mul]
    _ = ENNReal.ofReal ((e2_sapN j : ℝ) *
        (e2_sapDelta j * (L / (e2_sapN j : ℝ)))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp
    _ = ENNReal.ofReal (e2_sapDelta j * L) := by
      congr 1
      field_simp
    _ = ENNReal.ofReal L * ENNReal.ofReal (e2_sapDelta j) := by
      rw [ENNReal.ofReal_mul (hW.1 j).1.le, mul_comm]

private theorem generation_zero :
    (∑' l : Generation 0, ENNReal.ofReal (e2_sapSeg l.val).2.1) = 1 := by
  let root : Generation 0 := ⟨[], by simp [e2_sapValid]⟩
  have hroot (l : Generation 0) : l = root := by
    apply Subtype.ext
    exact List.length_eq_zero_iff.mp l.property.2
  rw [tsum_eq_single root]
  · simp [root, e2_sapSeg]
  · intro l hl
    exact (hl (hroot l)).elim

/-- The generation identity for labelled segment lengths, using only the weight bounds
`E2sapWeights` and the recursive labelled segment definitions. -/
theorem e2_sap_generation_proof (hW : E2sapWeights) : E2sapGeneration := by
  intro g
  induction g with
  | zero => simpa only [pow_zero] using generation_zero
  | succ g ih =>
    change (∑' l : Generation (g + 1), ENNReal.ofReal (e2_sapSeg l.val).2.1) = _
    calc
      _ = ∑' p : (Σ _l : Generation g, Σ j : ℕ, Fin (e2_sapN (j + 1))),
          ENNReal.ofReal (e2_sapSeg ((generationEquiv g p).val)).2.1 :=
        (Equiv.tsum_eq (generationEquiv g) _).symm
      _ = ∑' l : Generation g, ∑' j : ℕ, ∑' _m : Fin (e2_sapN (j + 1)),
          ENNReal.ofReal (e2_sapDelta (j + 1) * ((e2_sapSeg l.val).2.1 /
            (e2_sapN (j + 1) : ℝ))) := by
        rw [ENNReal.tsum_sigma']
        apply tsum_congr
        intro l
        rw [ENNReal.tsum_sigma']
        rfl
      _ = ∑' l : Generation g, ∑' j : ℕ,
          ENNReal.ofReal (e2_sapSeg l.val).2.1 * ENNReal.ofReal (e2_sapDelta (j + 1)) := by
        apply tsum_congr
        intro l
        apply tsum_congr
        intro j
        exact generation_child_sum hW _ _
      _ = (∑' l : Generation g, ENNReal.ofReal (e2_sapSeg l.val).2.1) *
          (∑' j : ℕ, ENNReal.ofReal (e2_sapDelta (j + 1))) := by
        simp_rw [ENNReal.tsum_mul_left]
        exact ENNReal.tsum_mul_right
      _ = (∑' j : ℕ, ENNReal.ofReal (e2_sapDelta (j + 1))) ^ (g + 1) := by
        rw [ih, pow_succ]

end ParabolicRectifiability.Examples
