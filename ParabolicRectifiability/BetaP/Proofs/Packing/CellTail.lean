import ParabolicRectifiability.BetaP.Proofs.Packing.VariantsStatements
import ParabolicRectifiability.BetaP.Proofs.Localization.Tail
import ParabolicRectifiability.BetaP.Proofs.Localization.AllScale
import ParabolicRectifiability.Measure.ScaleEnergy

/-! # The cell tail

Proves `c2_cellTail_proof : c2_CellTailStatement`, the exact `p`-tail applied to an atomic
source.

Proof:
* the support of the atomic source `λ = Σ_j b_j r_j^k δ_{z_j}` lies in the finite set of centres
  (`c2p4_support_subset_range`), so it is compact, of diameter `< 1`
  (`c2p4_diam_range_lt_one`, pairwise centre distance `< 1`), and contains `z_i`
  (`c2p4_mem_support`, positive weight and radius);
* the proved exact tail `cloc_pTail_proof` gives `∫_{(2,∞)} = (2^q-1)^{-1} ∫_{(1,2)}`, the factor
  is at most one (`clocp_tailFactor_le_one`), and `(1,2) ⊆ (r_i,2)` since `r_i ≤ 1`;
* `Ioi (r_i) ⊆ Ioo (r_i) 2 ∪ Ici 2`, with the null endpoint `2`, as in `cloc_allScale_proof`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- The value of an atomic source on a set: `λ(U) = Σ_j b_j r_j^k δ_{z_j}(U)`. -/
theorem c2p4_atomicSource_apply {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ)
    (U : Set (Space n)) :
    atomicSource k z r w U = ∑ j, ENNReal.ofReal (w j * r j ^ k) * Measure.dirac (z j) U := by
  simp only [atomicSource, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]

/-- The support of an atomic source lies in the (finite, closed) set of its centres. -/
theorem c2p4_support_subset_range {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) :
    (atomicSource k z r w).support ⊆ range z := by
  apply Measure.support_subset_of_isClosed (finite_range z).isClosed
  rw [mem_ae_iff, c2p4_atomicSource_apply]
  apply Finset.sum_eq_zero
  intro j _
  have hj : z j ∉ (range z)ᶜ := fun h => h (mem_range_self j)
  rw [Measure.dirac_apply, Set.indicator_of_notMem hj, mul_zero]

/-- A centre of positive weight and radius lies in the support of the atomic source. -/
theorem c2p4_mem_support {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ)
    (i : Fin N) (hri : 0 < r i) (hwi : 0 < w i) : z i ∈ (atomicSource k z r w).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have hpos : 0 < ENNReal.ofReal (w i * r i ^ k) :=
    ENNReal.ofReal_pos.mpr (mul_pos hwi (pow_pos hri k))
  rw [c2p4_atomicSource_apply]
  calc
    (0 : ℝ≥0∞) < ENNReal.ofReal (w i * r i ^ k) * Measure.dirac (z i) U := by
      rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU), mul_one]
      exact hpos
    _ ≤ ∑ j, ENNReal.ofReal (w j * r j ^ k) * Measure.dirac (z j) U :=
      Finset.single_le_sum
        (f := fun j => ENNReal.ofReal (w j * r j ^ k) * Measure.dirac (z j) U)
        (fun j _ => zero_le) (Finset.mem_univ i)

/-- Pairwise distance `< 1` of finitely many (and at least one) centres: the set of centres has
diameter `< 1`. -/
theorem c2p4_diam_range_lt_one {n N : ℕ} (z : Fin N → Space n) (i : Fin N)
    (hz : ∀ j j', dist (z j) (z j') < 1) : Metric.diam (range z) < 1 := by
  have hne : (Finset.univ : Finset (Fin N × Fin N)).Nonempty := ⟨(i, i), Finset.mem_univ _⟩
  have hD : (Finset.univ : Finset (Fin N × Fin N)).sup' hne
      (fun pq => dist (z pq.1) (z pq.2)) < 1 :=
    (Finset.sup'_lt_iff hne).mpr (fun pq _ => hz pq.1 pq.2)
  have hD0 : 0 ≤ (Finset.univ : Finset (Fin N × Fin N)).sup' hne
      (fun pq => dist (z pq.1) (z pq.2)) :=
    Finset.le_sup'_of_le _ (Finset.mem_univ (i, i)) dist_nonneg
  refine lt_of_le_of_lt (Metric.diam_le_of_forall_dist_le hD0 ?_) hD
  rintro _ ⟨j, rfl⟩ _ ⟨j', rfl⟩
  exact Finset.le_sup' (fun pq : Fin N × Fin N => dist (z pq.1) (z pq.2))
    (Finset.mem_univ (j, j'))

/-- **Cell tail** (`c2_CellTailStatement`). -/
theorem c2_cellTail_proof : c2_CellTailStatement := by
  intro n N k T p hp z r w hr hw hz i hri
  have hsub := c2p4_support_subset_range k z r w
  have hc : IsCompact (atomicSource k z r w).support :=
    (finite_range z).isCompact.of_isClosed_subset Measure.isClosed_support hsub
  have hd : Metric.diam (atomicSource k z r w).support < 1 :=
    (Metric.diam_mono hsub (finite_range z).isBounded).trans_lt (c2p4_diam_range_lt_one z i hz)
  have hzi : z i ∈ (atomicSource k z r w).support := c2p4_mem_support k z r w i (hr i) (hw i)
  -- the exact tail identity, with factor at most one
  have htail := cloc_pTail_proof (atomicSource k z r w) k T p hp hc hd hzi
  have h12 : ∫⁻ s in Ioo (1 : ℝ) 2,
        betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure ≤
      ∫⁻ s in Ioo (r i) 2,
        betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure :=
    lintegral_mono_set (Ioo_subset_Ioo_left hri)
  have hhigh : ∫⁻ s in Ioi (2 : ℝ),
        betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure ≤
      ∫⁻ s in Ioo (r i) 2,
        betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure := by
    rw [htail]
    calc
      _ ≤ 1 * ∫⁻ s in Ioo (1 : ℝ) 2,
            betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure := by
        gcongr
        exact clocp_tailFactor_le_one k hp
      _ = ∫⁻ s in Ioo (1 : ℝ) 2,
            betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure := one_mul _
      _ ≤ _ := h12
  -- split the scales above `r_i` at the null endpoint `2`
  have hsplit : Ioi (r i) ⊆ Ioo (r i) 2 ∪ Ici 2 := by
    intro s hs
    by_cases h : s < 2
    · exact Or.inl ⟨hs, h⟩
    · exact Or.inr (le_of_not_gt h)
  have hIci : ∫⁻ s in Ici (2 : ℝ),
        betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure =
      ∫⁻ s in Ioi (2 : ℝ),
        betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure :=
    setLIntegral_congr (Ioi_ae_eq_Ici' (scaleMeasure_singleton 2)).symm
  calc
    _ ≤ ∫⁻ s in Ioo (r i) 2 ∪ Ici 2,
          betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure :=
      lintegral_mono_set hsplit
    _ ≤ (∫⁻ s in Ioo (r i) 2,
          betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure) +
        ∫⁻ s in Ici (2 : ℝ),
          betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure :=
      lintegral_union_le _ _ _
    _ ≤ (∫⁻ s in Ioo (r i) 2,
          betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure) +
        ∫⁻ s in Ioo (r i) 2,
          betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure := by
      rw [hIci]
      exact add_le_add le_rfl hhigh
    _ = _ := (two_mul _).symm

end ParabolicRectifiability.BetaP
