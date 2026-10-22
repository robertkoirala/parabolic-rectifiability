import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import Mathlib.Analysis.MeanInequalities

/-! Weighted Jensen for nonnegative summable kernel weights. -/

noncomputable section

open Filter Topology

namespace ParabolicRectifiability.Examples

/-- The kernel Jensen estimate follows from finite weighted Hölder and passage to the limit.
The exponent identities also apply at `q = 1` and when the total kernel weight vanishes. -/
theorem e2_kernelJensen_proof : E2KernelJensenStatement := by
  intro q hq x K M hx hxone hK hKsum hM
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hxK : Summable (fun j => x j * K j) :=
    hKsum.of_nonneg_of_le (fun j => mul_nonneg (hx j) (hK j))
      (fun j => by simpa using mul_le_mul_of_nonneg_right (hxone j) (hK j))
  have hxqK : Summable (fun j => x j ^ q * K j) :=
    hKsum.of_nonneg_of_le (fun j => mul_nonneg (Real.rpow_nonneg (hx j) q) (hK j))
      (fun j => by
        simpa using mul_le_mul_of_nonneg_right
          (Real.rpow_le_one (hx j) (hxone j) hq0) (hK j))
  refine ⟨hxK, hxqK, ?_⟩
  have hexp : (1 - q⁻¹) * q = q - 1 := by field_simp
  have hfinite : ∀ n : ℕ,
      (∑ j ∈ Finset.range n, x j * K j) ^ q ≤
        M ^ (q - 1) * ∑' j, x j ^ q * K j := by
    intro n
    have hsumK0 : 0 ≤ ∑ j ∈ Finset.range n, K j :=
      Finset.sum_nonneg fun j _ => hK j
    have hsumx0 : 0 ≤ ∑ j ∈ Finset.range n, x j * K j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hx j) (hK j)
    have hsumxq0 : 0 ≤ ∑ j ∈ Finset.range n, x j ^ q * K j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (Real.rpow_nonneg (hx j) q) (hK j)
    have hholder := Real.inner_le_weight_mul_Lp_of_nonneg (Finset.range n) hq K x hK hx
    simp only [mul_comm (K _) (x _), mul_comm (K _) (x _ ^ q)] at hholder
    have hraised := Real.rpow_le_rpow hsumx0 hholder hq0
    rw [Real.mul_rpow (Real.rpow_nonneg hsumK0 _) (Real.rpow_nonneg hsumxq0 _),
      ← Real.rpow_mul hsumK0, ← Real.rpow_mul hsumxq0,
      hexp, inv_mul_cancel₀ hqne, Real.rpow_one] at hraised
    refine hraised.trans (mul_le_mul ?_ ?_ hsumxq0 ?_)
    · exact Real.rpow_le_rpow hsumK0
        ((hKsum.sum_le_tsum (Finset.range n) (fun j _ => hK j)).trans hM) (sub_nonneg.mpr hq)
    · exact hxqK.sum_le_tsum (Finset.range n)
        (fun j _ => mul_nonneg (Real.rpow_nonneg (hx j) q) (hK j))
    · exact Real.rpow_nonneg (le_trans (tsum_nonneg hK) hM) _
  exact le_of_tendsto ((Real.continuous_rpow_const hq0).tendsto _ |>.comp
    hxK.hasSum.tendsto_sum_nat) (Filter.Eventually.of_forall hfinite)

end ParabolicRectifiability.Examples
