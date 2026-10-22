import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements

/-! # Little half-Hölder modulus of the lacunary primitive

The finite head of the kernel sum vanishes linearly in the radius. On the tail,
convergence of the amplitudes to zero combines with the uniform kernel-sum bound.
The cutoff `3η / (32 * (ε + 1))` works for every nonnegative `ε`.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace ParabolicRectifiability.Examples

/-- The little half-Hölder conclusion, conditional only on the three
kernel estimates. The scale is uniform in both time variables, including its
closed endpoint. -/
theorem e2_lacunary_littleHolder_proof :
    E2KernelBoundStatement → E2KernelSumStatement → E2InvSqrtDecayStatement →
      E2LittleHolderStatement := by
  intro hmod hsum hdec ε a N hε hd ha η hη
  have hε1 : 0 < ε + 1 := by linarith
  let c : ℝ := η / (4 * (ε + 1))
  have hc : 0 < c := div_pos hη (mul_pos (by norm_num) hε1)
  let δ : ℝ := 3 * η / (32 * (ε + 1))
  have hδ : 0 < δ := div_pos (mul_pos (by norm_num) hη)
    (mul_pos (by norm_num) hε1)
  have hδc : δ * (8 / 3) = c := by
    dsimp [δ, c]
    field_simp
    ring
  obtain ⟨J, hJ⟩ := eventually_atTop.1 ((tendsto_order.1 ha).2 δ hδ)
  let C : ℝ := ∑ j ∈ Finset.range J, Real.sqrt (N j : ℝ)
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
  let ρ : ℝ := c / (C + 1)
  have hC1 : 0 < C + 1 := by linarith
  have hρ : 0 < ρ := div_pos hc hC1
  have hρC : ρ * C ≤ c := by
    have heq : ρ * (C + 1) = c := div_mul_cancel₀ c (ne_of_gt hC1)
    nlinarith
  refine ⟨ρ ^ 2, sq_pos_of_pos hρ, ?_⟩
  intro t s hts
  by_cases heq : t = s
  · subst s
    simp
  have hdist : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr heq)
  let r : ℝ := Real.sqrt |t - s|
  have hr : 0 < r := Real.sqrt_pos.2 hdist
  have hrρ : r ≤ ρ := (Real.sqrt_le_iff).2 ⟨hρ.le, hts⟩
  have hr2 : |t - s| ≤ r ^ 2 := by
    rw [show r ^ 2 = |t - s| from Real.sq_sqrt hdist.le]
  have hb : ∀ j, 0 < e2_invSqrtFreq N j := by
    intro j
    exact inv_pos.mpr (Real.sqrt_pos.2 (by exact_mod_cast hd.frequency_pos j))
  have hK : ∀ j, 0 ≤ e2_kernelAt (e2_invSqrtFreq N j) r := by
    intro j
    exact le_min (div_nonneg hr.le (hb j).le) (div_nonneg (hb j).le hr.le)
  obtain ⟨hw, hbound⟩ := hmod ε a N hε hd t s r hr hr2
  have hhead : (∑ j ∈ Finset.range J, a j * e2_kernelAt (e2_invSqrtFreq N j) r) ≤ c := by
    calc
      (∑ j ∈ Finset.range J, a j * e2_kernelAt (e2_invSqrtFreq N j) r)
          ≤ ∑ j ∈ Finset.range J, r * Real.sqrt (N j : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        calc
          a j * e2_kernelAt (e2_invSqrtFreq N j) r
              ≤ e2_kernelAt (e2_invSqrtFreq N j) r :=
            mul_le_of_le_one_left (hK j) (hd.amplitude_le_one j)
          _ ≤ r / e2_invSqrtFreq N j := min_le_left _ _
          _ = r * Real.sqrt (N j : ℝ) := by simp
      _ = r * C := by rw [Finset.mul_sum]
      _ ≤ ρ * C := mul_le_mul_of_nonneg_right hrρ hC
      _ ≤ c := hρC
  have hbTail : ∀ j, e2_invSqrtFreq N (j + 1 + J) ≤ e2_invSqrtFreq N (j + J) / 4 := by
    intro j
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hdec a N hd (j + J)
  obtain ⟨hkTail, hkTailBound⟩ := hsum (fun j => e2_invSqrtFreq N (j + J))
    (fun j => hb (j + J)) hbTail r hr
  have hwTail := (summable_nat_add_iff J).2 hw
  have htail : (∑' j, a (j + J) * e2_kernelAt (e2_invSqrtFreq N (j + J)) r) ≤ c := by
    calc
      (∑' j, a (j + J) * e2_kernelAt (e2_invSqrtFreq N (j + J)) r)
          ≤ ∑' j, δ * e2_kernelAt (e2_invSqrtFreq N (j + J)) r := by
        apply hwTail.tsum_le_tsum _ (hkTail.mul_left δ)
        intro j
        exact mul_le_mul_of_nonneg_right (hJ (j + J) (Nat.le_add_left J j)).le (hK (j + J))
      _ = δ * ∑' j, e2_kernelAt (e2_invSqrtFreq N (j + J)) r :=
        hkTail.tsum_mul_left δ
      _ ≤ δ * (8 / 3) := mul_le_mul_of_nonneg_left hkTailBound hδ.le
      _ = c := hδc
  have htotal : e2_lacunaryKernelSum a N r ≤ c + c := by
    unfold e2_lacunaryKernelSum
    rw [← hw.sum_add_tsum_nat_add J]
    exact add_le_add hhead htail
  have hscale : 2 * ε * (c + c) ≤ η := by
    have hcEq : c * (4 * (ε + 1)) = η :=
      div_mul_cancel₀ η (ne_of_gt (mul_pos (by norm_num) hε1))
    nlinarith [hc.le]
  calc
    |lacunaryFunction ε a N t - lacunaryFunction ε a N s|
        ≤ 2 * ε * r * e2_lacunaryKernelSum a N r := hbound
    _ ≤ 2 * ε * r * (c + c) :=
      mul_le_mul_of_nonneg_left htotal (mul_nonneg (mul_nonneg (by norm_num) hε) hr.le)
    _ = (2 * ε * (c + c)) * r := by ring
    _ ≤ η * r := mul_le_mul_of_nonneg_right hscale hr.le

end ParabolicRectifiability.Examples
