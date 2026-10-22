import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements

/-! # All-scale upper energy of a lacunary graph

The pointwise estimate is integrated after weighted Jensen. Only the radius-wise
weighted real series is converted to `ℝ≥0∞`; the amplitude series remains an
extended nonnegative sum, so no global summability assumption is needed.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

private theorem e2_measurable_kernelAt_ofReal (b : ℝ) :
    Measurable (fun r : ℝ => ENNReal.ofReal (e2_kernelAt b r)) := by
  exact ((measurable_id.div_const b).min (measurable_const.div measurable_id)).ennreal_ofReal

/-- The five independent upper-energy inputs give the all-scale estimate.
The constant is `2^(q+2) (8/3)^(q-1)`, chosen before all graph data. -/
theorem e2_lacunary_upperEnergy_proof :
    E2TestBoundStatement → E2KernelJensenStatement → E2KernelLogIntegralStatement →
      E2KernelSumStatement → E2InvSqrtDecayStatement → LacunaryUpperEnergyStatement := by
  intro htest hjensen hlog hsum hdecay q hq
  let C : ℝ := 2 ^ (q + 2) * (8 / 3 : ℝ) ^ (q - 1)
  refine ⟨C, mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro ε a N hε hεbound hd E _hE _hEJ t
  let b : ℕ → ℝ := e2_invSqrtFreq N
  let D : ℝ := 2 ^ (q + 1) * ε ^ q * (8 / 3 : ℝ) ^ (q - 1)
  have hb : ∀ j, 0 < b j := fun j =>
    inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hd.frequency_pos j)))
  have hD : 0 ≤ D := by
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hε.le _)) (Real.rpow_nonneg (by norm_num) _)
  have hcoeff : D * 2 = C * ε ^ q := by
    have hp : (2 : ℝ) ^ (q + 2) = 2 ^ (q + 1) * 2 := by
      calc
        (2 : ℝ) ^ (q + 2) = 2 ^ ((q + 1) + 1) := by congr 1; ring
        _ = 2 ^ (q + 1) * 2 := by rw [Real.rpow_add (by norm_num), Real.rpow_one]
    dsimp [D, C]
    rw [hp]
    ring
  have hkm : ∀ j, Measurable (fun r => ENNReal.ofReal (e2_kernelAt (b j) r)) :=
    fun j => e2_measurable_kernelAt_ofReal (b j)
  have hint :
      (∫⁻ r in Ioi 0, ∑' j, ENNReal.ofReal (a j ^ q) *
        ENNReal.ofReal (e2_kernelAt (b j) r) ∂scaleMeasure) =
        2 * ∑' j, ENNReal.ofReal (a j ^ q) := by
    rw [lintegral_tsum (f := fun j r => ENNReal.ofReal (a j ^ q) *
      ENNReal.ofReal (e2_kernelAt (b j) r))
      (fun j => (measurable_const.mul (hkm j)).aemeasurable)]
    calc
      (∑' j, ∫⁻ r in Ioi 0, ENNReal.ofReal (a j ^ q) *
          ENNReal.ofReal (e2_kernelAt (b j) r) ∂scaleMeasure) =
          ∑' j, ENNReal.ofReal (a j ^ q) * 2 := by
        apply tsum_congr
        intro j
        rw [lintegral_const_mul _ (hkm j), hlog (b j) (hb j)]
      _ = 2 * ∑' j, ENNReal.ofReal (a j ^ q) := by
        rw [ENNReal.tsum_mul_right, mul_comm]
  have hpoint (r : ℝ) (hr : 0 < r) :
      betaPow (lacunarySource ε a N E) 2 .mixed q (lacunaryGraphMap ε a N t) r ≤
        ENNReal.ofReal D * ∑' j, ENNReal.ofReal (a j ^ q) *
          ENNReal.ofReal (e2_kernelAt (b j) r) := by
    have hK : ∀ j, 0 ≤ e2_kernelAt (b j) r := fun j =>
      le_min (div_nonneg hr.le (hb j).le) (div_nonneg (hb j).le hr.le)
    obtain ⟨hKs, hKsum⟩ := hsum b hb (hdecay a N hd) r hr
    obtain ⟨_, hws, hJ⟩ := hjensen q hq a (fun j => e2_kernelAt (b j) r)
      (8 / 3) (fun j => (hd.amplitude_pos j).le) hd.amplitude_le_one hK hKs hKsum
    have hnonneg : ∀ j, 0 ≤ a j ^ q * e2_kernelAt (b j) r := fun j =>
      mul_nonneg (Real.rpow_nonneg (hd.amplitude_pos j).le _) (hK j)
    calc
      _ ≤ ENNReal.ofReal (2 ^ (q + 1) * ε ^ q * e2_lacunaryKernelSum a N r ^ q) :=
        htest ε a N hε hεbound hd E t r q hr (lt_of_lt_of_le zero_lt_one hq)
      _ ≤ ENNReal.ofReal (D * ∑' j, a j ^ q * e2_kernelAt (b j) r) := by
        apply ENNReal.ofReal_le_ofReal
        simpa only [D, b, e2_lacunaryKernelSum, mul_assoc] using
          mul_le_mul_of_nonneg_left hJ
            (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hε.le _))
      _ = _ := by
        rw [ENNReal.ofReal_mul hD, ENNReal.ofReal_tsum_of_nonneg hnonneg hws]
        congr 1
        apply tsum_congr
        intro j
        exact ENNReal.ofReal_mul (Real.rpow_nonneg (hd.amplitude_pos j).le _)
  apply iSup_le
  intro R
  calc
    energyT (lacunarySource ε a N E) 2 .mixed q R (lacunaryGraphMap ε a N t) ≤
        ∫⁻ r in Ioo 0 R, ENNReal.ofReal D * ∑' j, ENNReal.ofReal (a j ^ q) *
          ENNReal.ofReal (e2_kernelAt (b j) r) ∂scaleMeasure := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hpoint r hr.1
    _ ≤ ∫⁻ r in Ioi 0, ENNReal.ofReal D * ∑' j, ENNReal.ofReal (a j ^ q) *
          ENNReal.ofReal (e2_kernelAt (b j) r) ∂scaleMeasure :=
      lintegral_mono_set Ioo_subset_Ioi_self
    _ = ENNReal.ofReal (C * ε ^ q) * ∑' j, ENNReal.ofReal (a j ^ q) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hint, ← mul_assoc]
      have hc : ENNReal.ofReal D * 2 = ENNReal.ofReal (C * ε ^ q) := by
        calc
          _ = ENNReal.ofReal D * ENNReal.ofReal (2 : ℝ) := by norm_num
          _ = ENNReal.ofReal (D * 2) := (ENNReal.ofReal_mul hD).symm
          _ = _ := congrArg ENNReal.ofReal hcoeff
      rw [hc]

end ParabolicRectifiability.Examples
