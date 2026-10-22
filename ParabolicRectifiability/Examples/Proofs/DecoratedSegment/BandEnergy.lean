import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements
import ParabolicRectifiability.Decomposition.Carrier.BetaPointBoundAndRankZero

/-! # Divergent energy from separated logarithmic bands

The closed bands have a strict gap, each has scale measure `log 2`, and a tail
lies below any positive cutoff. Lower integrals over these measurable disjoint
sets are additive even when the integrand is not measurable.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

private theorem sapN_pos (j : ℕ) : (0 : ℝ) < (e2_sapN j : ℝ) := by
  have : 0 < e2_sapN j := by unfold e2_sapN; positivity
  exact_mod_cast this

private theorem sapN_mono : Monotone (fun j => (e2_sapN j : ℝ)) := by
  intro j k hjk
  dsimp only [e2_sapN]
  exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 0 < 8) (Nat.add_le_add_right hjk 1))

/-- The strict gap between consecutive closed bands. -/
private theorem sapBand_gap (H : ℝ) (hH : 0 < H) (j : ℕ) :
    4 * (H / (e2_sapN (j + 1) : ℝ)) < 2 * (H / (e2_sapN j : ℝ)) := by
  have h8 : (e2_sapN (j + 1) : ℝ) = 8 * (e2_sapN j : ℝ) := by
    simp only [e2_sapN]; push_cast; ring
  rw [h8]
  have heq : 4 * (H / (8 * (e2_sapN j : ℝ))) = (H / (e2_sapN j : ℝ)) / 2 := by
    field_simp; ring
  rw [heq]
  have hp := div_pos hH (sapN_pos j)
  linarith

private theorem sapBand_separated (H : ℝ) (hH : 0 < H) {j k : ℕ} (hjk : j < k) :
    4 * (H / (e2_sapN k : ℝ)) < 2 * (H / (e2_sapN j : ℝ)) := by
  exact (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left hH.le (sapN_pos (j + 1)) (sapN_mono hjk))
    (by norm_num : (0 : ℝ) ≤ 4)).trans_lt (sapBand_gap H hH j)

/-- The band-energy estimate `E2sapBandEnergy`: separated logarithmic bands of radii with a
uniform lower bound give a divergent scale integral, with no measurability hypothesis on `f`. -/
theorem e2_sap_bandEnergy_proof : E2sapBandEnergy := by
  intro f d H A p a j₀ hH hA hp ha hd hdiv hbound
  have hq : 0 < 2 / p := div_pos (by norm_num) (by linarith)
  obtain ⟨M, hM⟩ := exists_nat_gt (4 * H / a)
  let J := max j₀ M
  let B : ℕ → Set ℝ := fun i =>
    Icc (2 * (H / (e2_sapN (i + J) : ℝ))) (4 * (H / (e2_sapN (i + J) : ℝ)))
  have hcut (i : ℕ) : B i ⊆ Ioo 0 a := by
    intro r hr
    have hN : (M : ℝ) < (e2_sapN (i + J) : ℝ) := by
      have hn : M < e2_sapN (i + J) := by
        have hpow : i + J + 1 < 8 ^ (i + J + 1) := Nat.lt_pow_self (by norm_num)
        have hMJ : M ≤ J := le_max_right _ _
        unfold e2_sapN
        omega
      exact_mod_cast hn
    have hlarge : 4 * H / a < (e2_sapN (i + J) : ℝ) := hM.trans hN
    have htop : 4 * (H / (e2_sapN (i + J) : ℝ)) < a := by
      have := (div_lt_iff₀ ha).mp hlarge
      rw [← mul_div_assoc, div_lt_iff₀ (sapN_pos (i + J))]
      nlinarith
    exact ⟨(mul_pos (by norm_num) (div_pos hH (sapN_pos _))).trans_le hr.1,
      hr.2.trans_lt htop⟩
  have hdisjoint : Pairwise (fun i k => Disjoint (B i) (B k)) := by
    intro i k hik
    rw [Set.disjoint_left]
    intro r hri hrk
    rcases lt_or_gt_of_ne hik with h | h
    · have hg := sapBand_separated H hH (Nat.add_lt_add_right h J)
      exact (not_lt_of_ge (hri.1.trans hrk.2)) hg
    · have hg := sapBand_separated H hH (Nat.add_lt_add_right h J)
      exact (not_lt_of_ge (hrk.1.trans hri.2)) hg
  have hmass (i : ℕ) : scaleMeasure (B i) = ENNReal.ofReal (Real.log 2) := by
    have hs : 0 < 2 * (H / (e2_sapN (i + J) : ℝ)) :=
      mul_pos (by norm_num) (div_pos hH (sapN_pos _))
    have htwice : 2 * (2 * (H / (e2_sapN (i + J) : ℝ))) =
        4 * (H / (e2_sapN (i + J) : ℝ)) := by ring
    simpa only [B, htwice] using scaleMeasure_Icc_two_mul hs
  have htail : (∑' i : ℕ, ENNReal.ofReal (d (i + J) ^ (2 / p))) = ⊤ := by
    have hs : (∑ j ∈ Finset.range J, ENNReal.ofReal (d j ^ (2 / p))) +
        (∑' i : ℕ, ENNReal.ofReal (d (i + J) ^ (2 / p))) =
        ∑' j : ℕ, ENNReal.ofReal (d j ^ (2 / p)) :=
      ENNReal.summable.sum_add_tsum_nat_add'
    rw [hdiv, ENNReal.add_eq_top] at hs
    exact hs.resolve_left (by simp)
  have hband (i : ℕ) :
      ENNReal.ofReal ((A * d (i + J)) ^ (2 / p)) * ENNReal.ofReal (Real.log 2) ≤
        ∫⁻ r in B i, f r ^ (2 / p) ∂scaleMeasure := by
    rw [← hmass i, ← setLIntegral_const]
    apply setLIntegral_mono' measurableSet_Icc
    intro r hr
    rw [← ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hA.le (hd _)) hq.le]
    exact ENNReal.rpow_le_rpow (hbound _ (le_trans (le_max_left _ _) (Nat.le_add_left _ _)) r hr.1 hr.2) hq.le
  have hsum : (∑' i : ℕ,
      ENNReal.ofReal ((A * d (i + J)) ^ (2 / p)) * ENNReal.ofReal (Real.log 2)) = ⊤ := by
    simp_rw [Real.mul_rpow hA.le (hd _), ENNReal.ofReal_mul (Real.rpow_nonneg hA.le _)]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, htail,
      ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hA _)),
      ENNReal.top_mul (ENNReal.ofReal_ne_zero_iff.mpr (Real.log_pos one_lt_two))]
  apply top_unique
  calc
    ⊤ = ∑' i : ℕ, ENNReal.ofReal ((A * d (i + J)) ^ (2 / p)) *
        ENNReal.ofReal (Real.log 2) := hsum.symm
    _ ≤ ∑' i : ℕ, ∫⁻ r in B i, f r ^ (2 / p) ∂scaleMeasure := ENNReal.tsum_le_tsum hband
    _ = ∫⁻ r in ⋃ i, B i, f r ^ (2 / p) ∂scaleMeasure :=
      (lintegral_iUnion (fun _ => measurableSet_Icc) hdisjoint _).symm
    _ ≤ ∫⁻ r in Ioo 0 a, f r ^ (2 / p) ∂scaleMeasure :=
      lintegral_mono_set (iUnion_subset hcut)

end ParabolicRectifiability.Examples
