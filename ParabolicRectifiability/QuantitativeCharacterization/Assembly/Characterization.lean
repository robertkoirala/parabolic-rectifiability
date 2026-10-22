import ParabolicRectifiability.QuantitativeCharacterization.Assembly.CoveringSupplies
import ParabolicRectifiability.BetaP.Statements.Laws
import ParabolicRectifiability.Foundations.Statements.Measurability

/-! # The quantitative characterization and its beta-`p` comparison: assembly

* `quantitative_characterization_skeleton : QuantitativeCharacterizationStatement` uses no
  outside statement: part 1 is `exists_mainTheoremBounds` (forward covering of both branches,
  absolute continuity, the reverse bound at the final `L₀`, monotonicity); part 2 is
  `global_reverse` at every `L`.
* `betaPow_carleson_comparison_of_providers` uses the beta-`p` Hölder and clamping laws and the
  identification `B_2 = β²`, with their exact types: the pointwise laws integrate over scales and
  over roots; the forward clause is the forward clause of the quantitative characterization.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **The quantitative characterization**, assembled from `exists_local_forward_covering`, `ambient_root_covering`,
`absolutelyContinuous_of_upper_growth` and `exists_local_reverse_bound`. No outside
statement is used. -/
theorem quantitative_characterization_skeleton : QuantitativeCharacterizationStatement := by
  intro n hn k hk hkn A hA
  refine ⟨exists_mainTheoremBounds n hn k hk hkn A hA, fun L hL => ?_⟩
  obtain ⟨Crev, hCrev, hrev⟩ := global_reverse n hn k hk hkn L hL A hA
  exact ⟨Crev, hCrev, fun μ hfin hreg _ _ hADR K hK hQ =>
    hrev μ hfin hreg (fun z hz r hr => (hADR z hz r hr).2) K hK hQ⟩

/-- Domination of root energies: if `f(R,·) ≤ c g(R,·)` almost everywhere on every tested root,
then the normalized root suprema satisfy the same bound. -/
theorem rootCarlesonSup_le_mul {n k : ℕ} {S : Set (Space n)} {μ : Measure (Space n)}
    {f g : ℝ → Space n → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : ∀ a ∈ S, ∀ R : ℝ, 0 < R → ∀ᵐ z ∂μ.restrict (Metric.ball a R), f R z ≤ c * g R z) :
    rootCarlesonSup S μ k f ≤ c * rootCarlesonSup S μ k g := by
  unfold rootCarlesonSup
  refine iSup₂_le fun a ha => iSup₂_le fun R hR => ?_
  have h1 : (ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball a R, g R z ∂μ ≤
      ⨆ (a : Space n) (_ : a ∈ S) (R : ℝ) (_ : 0 < R),
        (ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball a R, g R z ∂μ :=
    le_iSup₂_of_le a ha (le_iSup₂_of_le R hR le_rfl)
  calc (ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball a R, f R z ∂μ
      ≤ (ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball a R, c * g R z ∂μ :=
        mul_le_mul_right (lintegral_mono_ae (h a ha R hR)) _
    _ = c * ((ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball a R, g R z ∂μ) := by
        rw [lintegral_const_mul' _ _ hc, mul_left_comm]
    _ ≤ c * ⨆ (a : Space n) (_ : a ∈ S) (R : ℝ) (_ : 0 < R),
          (ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball a R, g R z ∂μ :=
        mul_le_mul_right h1 _

/-- `M_β ≤ A^{1-2/p} M_{S_p}` for `p ≥ 2` under support-centred upper growth:
Hölder with the density factor `Θ ≤ A` at support points, integrated over scales and roots. -/
theorem carlesonEnergy_le_energyS (hH : BetaP.BetaPowHolderStatement)
    (h2 : BetaPowTwoStatement) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2) {A : ℝ}
    (hA : 0 ≤ A) {μ : Measure (Space n)} (hfin : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular)
    (hup : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k))
    {p : ℝ} (hp : 2 ≤ p) :
    carlesonEnergy μ k ≤ ENNReal.ofReal (A ^ (1 - 2 / p)) * carlesonEnergyS μ k p := by
  have hT : Nonempty (Models n k .mixed) := AdmissibleModel.nonempty_of_range hn hk hkn
  have hexp : 0 ≤ 1 - 2 / p := by
    have : 2 / p ≤ 1 := (div_le_one (by linarith)).mpr hp
    linarith
  have hpt : ∀ z ∈ μ.support, ∀ R : ℝ, squareEnergy μ k .mixed R z ≤
      ENNReal.ofReal (A ^ (1 - 2 / p)) * energyS μ k .mixed p R z := by
    intro z hz R
    rw [squareEnergy, energyS, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
    have hr0 : 0 < r := hr.1
    have hdens : densityRatio μ k z r ≤ ENNReal.ofReal A := by
      rw [densityRatio, ENNReal.div_le_iff_le_mul
        (Or.inl (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr0).ne'))
        (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)), ← ENNReal.ofReal_pow hr0.le,
        ← ENNReal.ofReal_mul hA]
      exact hup z hz r hr0
    calc betaSq μ k .mixed z r = betaPow μ k .mixed 2 z r := (h2 n hn k hk hkn .mixed μ z r).symm
      _ ≤ densityRatio μ k z r ^ (1 - 2 / p) * betaPow μ k .mixed p z r ^ (2 / p) :=
          (hH n hn k hk hkn .mixed hT μ hfin hreg z r hr0).2 p hp
      _ ≤ ENNReal.ofReal A ^ (1 - 2 / p) * betaPow μ k .mixed p z r ^ (2 / p) :=
          mul_le_mul_left (ENNReal.rpow_le_rpow hdens hexp) _
      _ = ENNReal.ofReal (A ^ (1 - 2 / p)) * betaPow μ k .mixed p z r ^ (2 / p) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hA hexp]
  have := hreg
  have hsupp : ∀ᵐ z ∂μ, z ∈ μ.support := Measure.support_mem_ae_of_innerRegular
  unfold carlesonEnergy carlesonEnergyS
  refine rootCarlesonSup_le_mul ENNReal.ofReal_ne_top fun _ _ R _ => ?_
  filter_upwards [ae_restrict_of_ae hsupp] with z hz using hpt z hz R

/-- `M_β ≤ 2^{2-p} M_{T_p}` for `0 < p ≤ 2`: the density-free clamping law,
integrated over scales and roots. -/
theorem carlesonEnergy_le_energyT (hCl : BetaP.BetaPowClampingStatement)
    (h2 : BetaPowTwoStatement) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (μ : Measure (Space n)) {p : ℝ} (hp0 : 0 < p) (hp2 : p ≤ 2) :
    carlesonEnergy μ k ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 - p)) * carlesonEnergyT μ k p := by
  have hpt : ∀ z : Space n, ∀ R : ℝ, squareEnergy μ k .mixed R z ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 - p)) * energyT μ k .mixed p R z := by
    intro z R
    rw [squareEnergy, energyT, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun r => ?_
    calc betaSq μ k .mixed z r = betaPow μ k .mixed 2 z r := (h2 n hn k hk hkn .mixed μ z r).symm
      _ ≤ (2 : ℝ≥0∞) ^ (2 - p) * betaPow μ k .mixed p z r :=
          (hCl n hn k hk hkn .mixed μ z r).1 p hp0 hp2
      _ = ENNReal.ofReal ((2 : ℝ) ^ (2 - p)) * betaPow μ k .mixed p z r := by
          rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  unfold carlesonEnergy carlesonEnergyT
  exact rootCarlesonSup_le_mul ENNReal.ofReal_ne_top fun _ _ R _ =>
    Filter.Eventually.of_forall fun z => hpt z R

/-- The beta-`p` forward clause with the constants of the quantitative characterization: finiteness of `M_{S_p}`
or `M_{T_p}` gives `M_β < ∞` by the comparisons, then the forward clause of
`MainTheoremBounds`. -/
theorem betaPowForwardBounds_of_main (hH : BetaP.BetaPowHolderStatement)
    (hCl : BetaP.BetaPowClampingStatement) (h2 : BetaPowTwoStatement) {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hkn : k ≤ n + 2) {A L₀ C : ℝ} (hA : 1 ≤ A)
    (hMain : MainTheoremBounds n k A L₀ C) : BetaPowForwardBounds n k A L₀ C := by
  intro μ hfin hreg hμ hunb hADR p
  obtain ⟨-, hfwd, -⟩ := hMain μ hfin hreg hμ hunb hADR
  refine ⟨fun hp hS => ?_, fun hp0 hp2 hT => ?_⟩
  · have hM : carlesonEnergy μ k < ⊤ :=
      (carlesonEnergy_le_energyS hH h2 hn hk hkn (by linarith) hfin hreg
        (fun z hz r hr => (hADR z hz r hr).2) hp).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS)
    exact ⟨hM, hfwd hM⟩
  · have hM : carlesonEnergy μ k < ⊤ :=
      (carlesonEnergy_le_energyT hCl h2 hn hk hkn μ hp0 hp2).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hT)
    exact ⟨hM, hfwd hM⟩

/-- **The beta-`p` comparison**, from `BetaPowHolderStatement`, `BetaPowClampingStatement` and
`BetaPowTwoStatement`, and from part 1 of the quantitative characterization. -/
theorem betaPow_carleson_comparison_of_providers (hH : BetaP.BetaPowHolderStatement)
    (hCl : BetaP.BetaPowClampingStatement) (h2 : BetaPowTwoStatement) :
    BetaPowCarlesonComparisonStatement := by
  intro n hn k hk hkn A hA
  refine ⟨fun μ hfin hreg _ _ hADR p => ⟨fun hp => ?_, fun hp0 hp2 => ?_⟩, ?_⟩
  · exact carlesonEnergy_le_energyS hH h2 hn hk hkn (by linarith) hfin hreg
      (fun z hz r hr => (hADR z hz r hr).2) hp
  · exact carlesonEnergy_le_energyT hCl h2 hn hk hkn μ hp0 hp2
  · obtain ⟨L₀, hL₀, C, hC, hMain⟩ := exists_mainTheoremBounds n hn k hk hkn A hA
    exact ⟨L₀, hL₀, C, hC, betaPowForwardBounds_of_main hH hCl h2 hn hk hkn hA hMain⟩

end ParabolicRectifiability.QuantitativeCharacterization
