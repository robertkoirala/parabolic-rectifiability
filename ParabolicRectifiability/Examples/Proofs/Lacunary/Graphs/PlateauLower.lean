import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import Mathlib.MeasureTheory.Measure.Real

/-! # Lacunary plateaus survive null-measurable deletion

Exact measure additivity controls the deleted portion of each cosine plateau.
The plateau opposite a proposed fitting constant then supplies a pointwise
lower bound, which is integrated on the retained portion.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

/-- A set of mass at least one third retains at least one quarter after a
null-measurable deletion occupying at most one twelfth of a finite window. -/
private theorem e2_plateau_retained_mass {E P W : Set ℝ} {L : ℝ}
    (hE : NullMeasurableSet E volume) (hW : volume W ≠ ∞)
    (hWL : volume.real W = L) (hPW : P ⊆ W)
    (hP : ENNReal.ofReal (L / 3) ≤ volume P)
    (hocc : ENNReal.ofReal (11 / 12 * L) ≤ volume (E ∩ W)) :
    ENNReal.ofReal (L / 4) ≤ volume (E ∩ P) := by
  have hPf : volume P ≠ ∞ := measure_ne_top_of_subset hPW hW
  have hEWf : volume (E ∩ W) ≠ ∞ := measure_ne_top_of_subset inter_subset_right hW
  have hEPf : volume (E ∩ P) ≠ ∞ := measure_ne_top_of_subset inter_subset_right hPf
  have hWDf : volume (W \ E) ≠ ∞ := measure_ne_top_of_subset sdiff_subset hW
  have hPreal : L / 3 ≤ volume.real P :=
    (ENNReal.ofReal_le_iff_le_toReal hPf).mp hP
  have hEreal : 11 / 12 * L ≤ volume.real (E ∩ W) :=
    (ENNReal.ofReal_le_iff_le_toReal hEWf).mp hocc
  have hWsplit := measureReal_inter_add_sdiff₀ (s := W) hE hW
  have hPsplit := measureReal_inter_add_sdiff₀ (s := P) hE hPf
  have hdeleted : volume.real (P \ E) ≤ volume.real (W \ E) :=
    measureReal_mono (sdiff_subset_sdiff_left hPW) hWDf
  rw [inter_comm W E, hWL] at hWsplit
  rw [inter_comm P E] at hPsplit
  apply (ENNReal.ofReal_le_iff_le_toReal hEPf).mpr
  change L / 4 ≤ volume.real (E ∩ P)
  linarith

/-- The two signed cosine plateaus and the
uniform approximation error yield the exact lower integral after deletion. -/
theorem e2_plateau_lower_proof :
    E2PlateauErrorStatement → E2CosPlateauStatement → E2PlateauLowerStatement := by
  intro herr hcos ε a N hε hd E hE j t hocc q hq c
  have hN : (0 : ℝ) < N j := by exact_mod_cast hd.frequency_pos j
  have hρ : 0 < Real.pi / (N j : ℝ) := div_pos Real.pi_pos hN
  let W := e2_periodWindow N j t
  let L : ℝ := 2 * Real.pi / N j
  let A : ℝ := ε * (a j / Real.sqrt (N j))
  let C : ℝ := e2_plateauCenter ε a N j t
  have hA : 0 ≤ A := mul_nonneg hε (div_nonneg (hd.amplitude_pos j).le
    (Real.sqrt_nonneg _))
  have hWmeas : MeasurableSet W := measurableSet_Ioo
  have hWfin : volume W ≠ ∞ := by
    dsimp [W, e2_periodWindow]
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hWL : volume.real W = L := by
    dsimp [W, e2_periodWindow, L]
    rw [Real.volume_real_Ioo_of_le (by linarith)]
    ring
  have herror (s : ℝ) (hs : s ∈ W) :
      |lacunaryFunction ε a N s - C - A * Real.cos (N j * s)| ≤ A / 50 := by
    apply herr ε a N hε hd j t s
    change t - Real.pi / (N j : ℝ) < s ∧ s < t + Real.pi / (N j : ℝ) at hs
    exact abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hplateaus := hcos (N j) hN t
  have hthird : 2 * Real.pi / (3 * (N j : ℝ)) = L / 3 := by dsimp [L]; ring
  rw [hthird] at hplateaus
  have hchoose : ∃ P : Set ℝ, MeasurableSet P ∧ P ⊆ W ∧
      ENNReal.ofReal (L / 3) ≤ volume P ∧
      ∀ s ∈ P, 12 / 25 * A ≤ |lacunaryFunction ε a N s - c| := by
    by_cases hc : c ≤ C
    · refine ⟨{s : ℝ | 1 / 2 ≤ Real.cos (N j * s)} ∩ W,
        (measurableSet_le measurable_const (Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).measurable).inter hWmeas,
        inter_subset_right, hplateaus.1, ?_⟩
      intro s hs
      have he := (abs_le.mp (herror s hs.2)).1
      have hm := mul_le_mul_of_nonneg_left hs.1 hA
      have ha := le_abs_self (lacunaryFunction ε a N s - c)
      dsimp only [C, A] at hc he hm ⊢
      nlinarith
    · refine ⟨{s : ℝ | Real.cos (N j * s) ≤ -(1 / 2)} ∩ W,
        (measurableSet_le (Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).measurable measurable_const).inter hWmeas,
        inter_subset_right, hplateaus.2, ?_⟩
      intro s hs
      have he := (abs_le.mp (herror s hs.2)).2
      have hm := mul_le_mul_of_nonneg_left hs.1 hA
      have ha := neg_le_abs (lacunaryFunction ε a N s - c)
      have hc' : C ≤ c := (lt_of_not_ge hc).le
      dsimp only [C, A] at hc' he hm ⊢
      nlinarith
  obtain ⟨P, hPmeas, hPW, hPmass, hPbound⟩ := hchoose
  have hmass := e2_plateau_retained_mass hE hWfin hWL hPW hPmass hocc
  have hquarter : L / 4 = Real.pi / (2 * (N j : ℝ)) := by dsimp [L]; ring
  rw [hquarter] at hmass
  have hB : 0 ≤ 12 / 25 * A := mul_nonneg (by norm_num) hA
  have hintegral :
      (∫⁻ _s in E ∩ P, ENNReal.ofReal ((12 / 25 * A) ^ q)) ≤
        ∫⁻ s in E ∩ P, ENNReal.ofReal (|lacunaryFunction ε a N s - c| ^ q) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem₀ (hE.inter hPmeas.nullMeasurableSet)] with s hs
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hB (hPbound s hs.2) hq.le)
  calc
    ENNReal.ofReal (Real.pi / (2 * N j) * (12 / 25 * A) ^ q) =
        ENNReal.ofReal ((12 / 25 * A) ^ q) * ENNReal.ofReal (Real.pi / (2 * N j)) := by
      rw [ENNReal.ofReal_mul (div_nonneg Real.pi_pos.le (by positivity)), mul_comm]
    _ ≤ ENNReal.ofReal ((12 / 25 * A) ^ q) * volume (E ∩ P) :=
      mul_le_mul_right hmass _
    _ = ∫⁻ _s in E ∩ P, ENNReal.ofReal ((12 / 25 * A) ^ q) :=
      (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ s in E ∩ P, ENNReal.ofReal (|lacunaryFunction ε a N s - c| ^ q) := hintegral
    _ ≤ ∫⁻ s in E ∩ W, ENNReal.ofReal (|lacunaryFunction ε a N s - c| ^ q) :=
      lintegral_mono_set (inter_subset_inter_right E hPW)

end ParabolicRectifiability.Examples
