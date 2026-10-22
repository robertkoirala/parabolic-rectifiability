import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements
import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements

/-! # The lacunary half-Hölder modulus

The kernel bound reduces the oscillation to the amplitude-weighted kernel sum.
The amplitudes are bounded by their supremum, while the kernel-sum and reciprocal-frequency
decay estimates give the uniform bound `8 / 3`. -/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Examples

theorem e2_sup_modulus_proof :
    E2KernelBoundStatement → E2KernelSumStatement → E2InvSqrtDecayStatement →
      E2SupModulusStatement := by
  intro hKernelBound hKernelSum hInvSqrtDecay ε a N hε hData t s
  by_cases hts : t = s
  · subst s
    simp
  · let r : ℝ := Real.sqrt |t - s|
    have hdiff : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr hts)
    have hr : 0 < r := by
      dsimp [r]
      exact Real.sqrt_pos.2 hdiff
    have hrsq : r ^ 2 = |t - s| := by
      dsimp [r]
      exact Real.sq_sqrt (abs_nonneg _)
    obtain ⟨hWeightedSummable, hModulus⟩ :=
      hKernelBound ε a N hε hData t s r hr (by rw [hrsq])

    have hAmplitudeBounded : BddAbove (Set.range a) := by
      refine ⟨1, ?_⟩
      rintro y ⟨j, rfl⟩
      exact hData.amplitude_le_one j
    let A : ℝ := ⨆ j, a j
    have hANonneg : 0 ≤ A := by
      dsimp [A]
      exact (hData.amplitude_pos 0).le.trans (le_ciSup hAmplitudeBounded 0)

    have hScalePos (j : ℕ) : 0 < e2_invSqrtFreq N j := by
      unfold e2_invSqrtFreq
      exact inv_pos.mpr <| Real.sqrt_pos.2 <| Nat.cast_pos.mpr (hData.frequency_pos j)
    have hKernelNonneg (j : ℕ) :
        0 ≤ e2_kernelAt (e2_invSqrtFreq N j) r := by
      unfold e2_kernelAt
      exact le_min
        (div_nonneg hr.le (hScalePos j).le)
        (div_nonneg (hScalePos j).le hr.le)

    obtain ⟨hKernelSummable, hKernelBounded⟩ :=
      hKernelSum (e2_invSqrtFreq N) hScalePos (hInvSqrtDecay a N hData) r hr
    have hScaledKernelSummable :
        Summable (fun j => A * e2_kernelAt (e2_invSqrtFreq N j) r) :=
      hKernelSummable.mul_left A
    have hWeightedBound :
        e2_lacunaryKernelSum a N r ≤ A * (8 / 3) := by
      calc
        e2_lacunaryKernelSum a N r =
            ∑' j, a j * e2_kernelAt (e2_invSqrtFreq N j) r := rfl
        _ ≤ ∑' j, A * e2_kernelAt (e2_invSqrtFreq N j) r :=
          hWeightedSummable.tsum_le_tsum
            (fun j => mul_le_mul_of_nonneg_right
              (le_ciSup hAmplitudeBounded j) (hKernelNonneg j))
            hScaledKernelSummable
        _ = A * ∑' j, e2_kernelAt (e2_invSqrtFreq N j) r :=
          hKernelSummable.tsum_mul_left A
        _ ≤ A * (8 / 3) := mul_le_mul_of_nonneg_left hKernelBounded hANonneg

    have hFactorNonneg : 0 ≤ 2 * ε * r := by positivity
    have hProductNonneg : 0 ≤ ε * A * r :=
      mul_nonneg (mul_nonneg hε hANonneg) hr.le
    calc
      |lacunaryFunction ε a N t - lacunaryFunction ε a N s| ≤
          2 * ε * r * e2_lacunaryKernelSum a N r := hModulus
      _ ≤ 2 * ε * r * (A * (8 / 3)) :=
        mul_le_mul_of_nonneg_left hWeightedBound hFactorNonneg
      _ = (16 / 3) * (ε * A * r) := by ring
      _ ≤ 16 * (ε * A * r) :=
        mul_le_mul_of_nonneg_right (by norm_num : (16 / 3 : ℝ) ≤ 16) hProductNonneg
      _ = 16 * ε * (⨆ j, a j) * Real.sqrt |t - s| := by
        simp [A, r]
        ring

end ParabolicRectifiability.Examples

end
