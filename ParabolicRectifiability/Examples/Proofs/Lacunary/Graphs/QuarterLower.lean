import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements

/-! # A uniform positive energy bound on the inner quarter graph

The fixed index `2` has frequency at least `256`. Its period window stays in
the quarter interval for every centre in the eighth interval. Full occupancy
therefore gives one positive beta bound, and one logarithmic band lies inside
the energy's scale interval. No infinite sum of bands is needed.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The plateau and one-band estimates give a uniform positive lower bound
on the inner interval, for every positive real exponent. -/
theorem e2_quarter_energyLower_proof :
    E2PlateauBetaStatement → E2BandStatement → E2QuarterEnergyLowerStatement := by
  intro hplateau hband p hp ε a N hε hεupper hd
  have hNnat : 256 ≤ N 2 := by
    have h0 := hd.frequency_pos 0
    have h1 := hd.frequency_growth 0
    have h2 := hd.frequency_growth 1
    norm_num at h1 h2
    omega
  have hN : (256 : ℝ) ≤ N 2 := by exact_mod_cast hNnat
  have hNpos : (0 : ℝ) < N 2 := by linarith
  have hwidthpos : 0 < Real.pi / N 2 := div_pos Real.pi_pos hNpos
  have hwidth : Real.pi / N 2 < (1 / 8 : ℝ) := by
    apply (div_lt_iff₀ hNpos).2
    nlinarith [Real.pi_lt_four]
  have hrpos : 0 < e2_plateauRadius N 2 := Real.sqrt_pos.2 hwidthpos
  have hrlt : e2_plateauRadius N 2 < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
    nlinarith
  let β₀ : ℝ := 1 / 2 * Real.pi ^ (-(p / 2)) * (12 / 25) ^ p * ε ^ p * a 2 ^ p
  have hβpos : 0 < β₀ := by
    dsimp [β₀]
    have ha := hd.amplitude_pos 2
    positivity
  let c : ℝ := Real.log 2 * ((2 : ℝ) ^ (2 + p))⁻¹
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : 0 < (2 : ℝ) ^ (2 + p) := Real.rpow_pos_of_pos (by norm_num) _
  have hcpos : 0 < c := mul_pos hlog (inv_pos.mpr hpow)
  have hc : ENNReal.ofReal c =
      ENNReal.ofReal (Real.log 2) * ((2 : ℝ≥0∞) ^ ((2 : ℝ) + p))⁻¹ := by
    dsimp [c]
    rw [ENNReal.ofReal_mul hlog.le, ENNReal.ofReal_inv_of_pos hpow,
      ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  refine ⟨c * β₀, mul_pos hcpos hβpos, ?_⟩
  intro t ht
  have hwindow : e2_periodWindow N 2 t ⊆ Icc (-1 / 4 : ℝ) (1 / 4) := by
    intro s hs
    change t - Real.pi / N 2 < s ∧ s < t + Real.pi / N 2 at hs
    constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
  have hoccupancy : ENNReal.ofReal (11 / 12 * (2 * Real.pi / N 2)) ≤
      volume (Icc (-1 / 4 : ℝ) (1 / 4) ∩ e2_periodWindow N 2 t) := by
    rw [inter_eq_right.mpr hwindow, e2_periodWindow, Real.volume_Ioo]
    apply ENNReal.ofReal_le_ofReal
    have hlength : 0 ≤ 2 * Real.pi / (N 2 : ℝ) := by positivity
    calc
      11 / 12 * (2 * Real.pi / (N 2 : ℝ)) ≤ 2 * Real.pi / (N 2 : ℝ) :=
        mul_le_of_le_one_left hlength (by norm_num)
      _ = t + Real.pi / (N 2 : ℝ) - (t - Real.pi / (N 2 : ℝ)) := by ring
  have hβ := hplateau ε a N hε hεupper hd (Icc (-1 / 4 : ℝ) (1 / 4))
    measurableSet_Icc.nullMeasurableSet 2 t hoccupancy p hp
  have hsub : Icc (e2_plateauRadius N 2) (2 * e2_plateauRadius N 2) ⊆
      Ioo (0 : ℝ) 2 := by
    intro r hr
    exact ⟨lt_of_lt_of_le hrpos hr.1, lt_of_le_of_lt hr.2 (by linarith)⟩
  calc
    ENNReal.ofReal (c * β₀) =
        ENNReal.ofReal (Real.log 2) * ((2 : ℝ≥0∞) ^ ((2 : ℝ) + p))⁻¹ *
          ENNReal.ofReal β₀ := by rw [ENNReal.ofReal_mul hcpos.le, hc]
    _ ≤ ENNReal.ofReal (Real.log 2) * ((2 : ℝ≥0∞) ^ ((2 : ℝ) + p))⁻¹ *
        betaPow (lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) 2 .mixed p
          (lacunaryGraphMap ε a N t) (e2_plateauRadius N 2) := by
      exact mul_le_mul_right hβ _
    _ ≤ ∫⁻ r in Icc (e2_plateauRadius N 2) (2 * e2_plateauRadius N 2),
        betaPow (lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) 2 .mixed p
          (lacunaryGraphMap ε a N t) r ∂scaleMeasure :=
      hband 1 _ 2 .mixed p hp.le _ _ hrpos
    _ ≤ energyT (lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) 2 .mixed p 2
        (lacunaryGraphMap ε a N t) := lintegral_mono_set hsub

end ParabolicRectifiability.Examples
