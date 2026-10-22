import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements

/-! # Isometry of the lacunary time graph

The modulus estimate at `r = √|t-s|` is bounded by the kernel sum `8/3`.
The amplitude endpoint `ε ≤ 3/16` makes the spatial displacement at most `r`,
so the time coordinate determines the parabolic distance.
-/

noncomputable section

namespace ParabolicRectifiability.Examples

/-- The modulus, kernel-sum, and frequency-decay statements imply the exact
snowflake isometry, including the amplitude endpoint and coincident times. -/
theorem e2_lacunary_isometry_proof :
    E2KernelBoundStatement → E2KernelSumStatement → E2InvSqrtDecayStatement →
      LacunaryIsometryStatement := by
  intro hmodulus hkernel hdecay ε a N hε hεsmall hdata t s
  by_cases hts : t = s
  · subst s
    simp
  have hr : 0 < Real.sqrt |t - s| :=
    Real.sqrt_pos.2 (abs_pos.2 (sub_ne_zero.mpr hts))
  have hb : ∀ j, 0 < e2_invSqrtFreq N j := by
    intro j
    exact inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (hdata.frequency_pos j)))
  obtain ⟨hsum, hsum_le⟩ := hkernel (e2_invSqrtFreq N) hb (hdecay a N hdata)
    (Real.sqrt |t - s|) hr
  obtain ⟨hweighted, hmod⟩ := hmodulus ε a N hε.le hdata t s
    (Real.sqrt |t - s|) hr (by rw [Real.sq_sqrt (abs_nonneg _)])
  have hcompare : e2_lacunaryKernelSum a N (Real.sqrt |t - s|) ≤
      ∑' j, e2_kernelAt (e2_invSqrtFreq N j) (Real.sqrt |t - s|) := by
    apply hweighted.tsum_le_tsum _ hsum
    intro j
    have hnonneg : 0 ≤ e2_kernelAt (e2_invSqrtFreq N j) (Real.sqrt |t - s|) :=
      le_min (div_nonneg hr.le (hb j).le) (div_nonneg (hb j).le hr.le)
    calc
      a j * e2_kernelAt (e2_invSqrtFreq N j) (Real.sqrt |t - s|) ≤
          1 * e2_kernelAt (e2_invSqrtFreq N j) (Real.sqrt |t - s|) :=
        mul_le_mul_of_nonneg_right (hdata.amplitude_le_one j) hnonneg
      _ = _ := one_mul _
  have hspatial : |lacunaryFunction ε a N t - lacunaryFunction ε a N s| ≤
      Real.sqrt |t - s| := by
    calc
      _ ≤ 2 * ε * Real.sqrt |t - s| *
          e2_lacunaryKernelSum a N (Real.sqrt |t - s|) := hmod
      _ ≤ 2 * ε * Real.sqrt |t - s| * (8 / 3) :=
        mul_le_mul_of_nonneg_left (hcompare.trans hsum_le) (by positivity)
      _ ≤ Real.sqrt |t - s| := by
        nlinarith [mul_le_mul_of_nonneg_right hεsmall hr.le]
  simp only [lacunaryGraphMap, dist_point, EuclideanSpace.single,
    ← PiLp.single_sub, PiLp.norm_single, Real.norm_eq_abs]
  exact max_eq_right hspatial

end ParabolicRectifiability.Examples
