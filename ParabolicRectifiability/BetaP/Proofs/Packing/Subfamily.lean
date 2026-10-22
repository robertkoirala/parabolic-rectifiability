import ParabolicRectifiability.BetaP.Proofs.Packing.VariantsStatements

/-! # Subfamilies (`c2_subfamily`)

Proof of `c2_subfamily_proof : c2_SubfamilyStatement`.

Proof: unfold `atomicSource`;
`Measure.finsetSum_apply` and the Dirac `measure_univ` give the mass identities; the finset sum
over `I` is reindexed along `I.equivFin`; the domination is an injective sub-sum of labelled
summands (pattern `cpk2_subSource_le`); the packing clause is checked field by field, disjointness
by injectivity of `fun m => (I.equivFin.symm m).1`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- The enumeration `m ↦ (I.equivFin.symm m).1` of `I` is injective. -/
theorem c2p3_enum_injective {N : ℕ} (I : Finset (Fin N)) :
    Function.Injective (fun m : Fin I.card => (I.equivFin.symm m).1) := by
  intro a b hab
  exact I.equivFin.symm.injective (Subtype.ext hab)

/-- Reindexing a finset sum along its enumeration `I.equivFin` (values in `ℝ≥0∞`). -/
theorem c2p3_sum_finset_eq_sum_fin {N : ℕ} (I : Finset (Fin N)) (f : Fin N → ℝ≥0∞) :
    ∑ i ∈ I, f i = ∑ m : Fin I.card, f (I.equivFin.symm m : Fin N) := by
  rw [← Finset.sum_coe_sort I]
  exact Fintype.sum_equiv I.equivFin _ _ (fun x => by rw [Equiv.symm_apply_apply])

/-- Total mass of an atomic source: the sum of the termwise `ofReal` masses. -/
theorem c2p3_atomicSource_univ {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) :
    atomicSource k z r w univ = ∑ i, ENNReal.ofReal (w i * r i ^ k) := by
  unfold atomicSource
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]

/-- The atomic source of an injectively reindexed subfamily is dominated by the full one. -/
theorem c2p3_atomicSource_le {n N l : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ)
    (e : Fin l → Fin N) (he : Function.Injective e) :
    atomicSource k (fun m => z (e m)) (fun m => r (e m)) (fun m => w (e m)) ≤
      atomicSource k z r w := by
  classical
  rw [Measure.le_iff']
  intro A
  unfold atomicSource
  rw [Measure.finsetSum_apply, Measure.finsetSum_apply]
  calc ∑ m : Fin l, (ENNReal.ofReal (w (e m) * r (e m) ^ k) • Measure.dirac (z (e m))) A
      = ∑ i ∈ (Finset.univ : Finset (Fin l)).image e,
          (ENNReal.ofReal (w i * r i ^ k) • Measure.dirac (z i)) A :=
        (Finset.sum_image
          (f := fun i => (ENNReal.ofReal (w i * r i ^ k) • Measure.dirac (z i)) A)
          (fun a _ b _ hab => he hab)).symm
    _ ≤ ∑ i : Fin N, (ENNReal.ofReal (w i * r i ^ k) • Measure.dirac (z i)) A :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **Subfamilies**: proof of `c2_SubfamilyStatement`. -/
theorem c2_subfamily_proof : c2_SubfamilyStatement := by
  intro n N k z r w I
  refine ⟨?_, ?_, c2p3_atomicSource_univ k z r w, ?_⟩
  · exact c2p3_atomicSource_le k z r w _ (c2p3_enum_injective I)
  · rw [c2p3_atomicSource_univ, c2p3_sum_finset_eq_sum_fin I]
    rfl
  · intro q R b h
    exact
      { radius_pos := fun m => h.radius_pos _
        ball_subset := fun m => h.ball_subset _
        pairwise_disjoint := fun a b hab =>
          h.pairwise_disjoint _ _ (fun e => hab (c2p3_enum_injective I e))
        weight_pos := fun m => h.weight_pos _
        weight_le := fun m => h.weight_le _ }

end ParabolicRectifiability.BetaP
