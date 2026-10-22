import ParabolicRectifiability.BetaP.Proofs.Counterexamples.RowSupport
import ParabolicRectifiability.BetaP.Proofs.Support.Basic
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.DirectWitnesses

/-! # Qualitative implications, sharp ranges and failure dimensions of the classification

* The six positive table entries follow from the necessity statement and the qualitative
  characterization (hypotheses), the Foundations identities `S_2 = T_2 = squareEnergy` and
  `B_2 = betaSq` (hypotheses), the clamping law, and the two pointwise Hölder comparisons.
* The four negative entries are the row statements applied to their inputs: the witness `E₋`
  (from `directWitnessMinus_of_providers`, over the graph-source statement and
  `S_2 = squareEnergy`), the construction `E₊` and the transfer; the shared lacunary frequency
  existence, the lacunary statements and the qualitative characterization.
* The ambient endpoint follows from the Foundations ambient characterization and zero-graph cover
  (hypotheses) and the vanishing of every available beta-`p` at `k = n+2` (proved here).
* Endpoint invariance follows from the finite-annulus and unavailable-family laws.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## The ambient endpoint: every available beta-`p` vanishes -/

/-- Every model available at `k = n+2` is the whole space. -/
theorem modelSet_ambient {n : ℕ} {T : FamilyKind} (L : Models n (n + 2) T) :
    modelSet L = Set.univ := by
  cases T with
  | horizontal => exact isEmptyElim (α := HorizontalModel n (n + 2)) L
  | vertical => exact VerticalModel.ambient_toSet L
  | mixed => exact AdmissibleModel.ambient_toSet L

/-- At `k = n+2`, `B_p = 0` for every available family, source, centre and radius. -/
theorem betaPow_ambient_eq_zero {n : ℕ} {T : FamilyKind} (hT : Nonempty (Models n (n + 2) T))
    (μ : Measure (Space n)) {p : ℝ} (hp : 0 < p) (z : Space n) (r : ℝ) :
    betaPow μ (n + 2) T p z r = 0 := by
  unfold betaPow
  split_ifs with hr
  · obtain ⟨L⟩ := hT
    have hfit : fitPow μ p L z r = 0 := by
      unfold fitPow
      have h0 : ∀ w : Space n, Metric.infEDist w (modelSet L) ^ p = 0 := fun w => by
        rw [Metric.infEDist_zero_of_mem (by rw [modelSet_ambient L]; exact mem_univ w)]
        exact ENNReal.zero_rpow_of_pos hp
      simp only [h0, lintegral_zero]
    have hinf : (⨅ L' : Models n (n + 2) T, fitPow μ p L' z r) = 0 :=
      le_antisymm ((iInf_le _ L).trans hfit.le) bot_le
    rw [hinf, mul_zero]
  · rfl

theorem energyS_ambient_eq_zero {n : ℕ} {T : FamilyKind} (hT : Nonempty (Models n (n + 2) T))
    (μ : Measure (Space n)) {p : ℝ} (hp : 0 < p) (a : ℝ) (z : Space n) :
    energyS μ (n + 2) T p a z = 0 := by
  unfold energyS
  have h0 : ∀ r : ℝ, betaPow μ (n + 2) T p z r ^ (2 / p) = 0 := fun r => by
    rw [betaPow_ambient_eq_zero hT μ hp z r]
    exact ENNReal.zero_rpow_of_pos (div_pos two_pos hp)
  simp only [h0, lintegral_zero]

theorem energyT_ambient_eq_zero {n : ℕ} {T : FamilyKind} (hT : Nonempty (Models n (n + 2) T))
    (μ : Measure (Space n)) {p : ℝ} (hp : 0 < p) (a : ℝ) (z : Space n) :
    energyT μ (n + 2) T p a z = 0 := by
  unfold energyT
  simp only [betaPow_ambient_eq_zero hT μ hp z, lintegral_zero]

/-! ## Endpoint invariance of finiteness -/

/-- Finiteness on `(0,b)` and on the annulus `(b,b')` gives finiteness on `(0,b')`. -/
theorem setLIntegral_Ioo_lt_top_of {f : ℝ → ℝ≥0∞} {b b' : ℝ} (hbb' : b ≤ b')
    (h0 : ∫⁻ r in Ioo 0 b, f r ∂scaleMeasure < ⊤)
    (hann : b < b' → ∫⁻ r in Ioo b b', f r ∂scaleMeasure < ⊤) :
    ∫⁻ r in Ioo 0 b', f r ∂scaleMeasure < ⊤ := by
  exact c2_setLIntegral_Ioo_lt_top_of hbb' h0 hann

/-- **Endpoint invariance**: from the finite-annulus law
(available family) and the unavailable-family law (both sides `⊤`). -/
theorem betaPEndpointInvariance_skeleton : BetaPEndpointInvarianceStatement := by
  intro n hn k hk hkn T μ hμ hreg p hp z a a' ha ha'
  by_cases hT : Nonempty (Models n k T)
  · have key : ∀ b b' : ℝ, 0 < b → b ≤ b' →
        (energyS μ k T p b z < ⊤ ↔ energyS μ k T p b' z < ⊤) ∧
          (energyT μ k T p b z < ⊤ ↔ energyT μ k T p b' z < ⊤) := by
      intro b b' hb hbb'
      have hann := fun hlt : b < b' =>
        betaPowAnnulus_law n hn k hk hkn T hT μ hμ hreg p hp z b b' hb hlt
      refine ⟨⟨fun h => setLIntegral_Ioo_lt_top_of hbb' h fun hlt => (hann hlt).1,
          fun h => (lintegral_mono_set (Ioo_subset_Ioo_right hbb')).trans_lt h⟩,
        ⟨fun h => setLIntegral_Ioo_lt_top_of hbb' h fun hlt => (hann hlt).2,
          fun h => (lintegral_mono_set (Ioo_subset_Ioo_right hbb')).trans_lt h⟩⟩
    rcases le_total a a' with h | h
    · exact key a a' ha h
    · exact ⟨(key a' a ha' h).1.symm, (key a' a ha' h).2.symm⟩
  · have hE : IsEmpty (Models n k T) := not_nonempty_iff.mp hT
    obtain ⟨-, h⟩ := unavailableFamily_law n hn k hk hkn T hE μ p hp z
    rw [(h a ha).1, (h a' ha').1, (h a ha).2, (h a' ha').2]
    exact ⟨Iff.rfl, Iff.rfl⟩

/-! ## The positive table entries -/

/-- Rectifiability with covers of every norm from a.e. finite mixed square energy at one
endpoint and the density hypothesis, by the qualitative characterization. -/
theorem withCovers_of_squareEnergy (hQC : Characterization.QualitativeCharacterizationStatement)
    {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (hdens : HasPositiveFiniteUpperDensity k μ) {a : ℝ} (ha : 0 < a)
    (hS : ∀ᵐ z ∂μ, squareEnergy μ k .mixed a z < ⊤) : IsRegularlyRectifiableWithCovers k μ := by
  have hdens' : ∀ᵐ z ∂μ, 0 < upperDensity μ k z ∧ upperDensity μ k z < ⊤ := hdens
  have hQ := hQC n hn k hk hkn .mixed (AdmissibleModel.nonempty_of_range hn hk hkn) μ hμ hreg
  have hrect : IsRegularlyRectifiableMeasure .mixed k μ := hQ.2.2.1.mpr
    ⟨a, ha, by filter_upwards [hS, hdens'] with z h1 h2 using ⟨h1, h2.1, h2.2⟩⟩
  exact ⟨hrect, (hQ.2.2.2.2.2.2.1 hrect).2⟩

theorem spBelowTwoNecessary_glue (hNec : Characterization.NecessityStatement) :
    SpBelowTwoNecessaryStatement := by
  intro n hn k hk hkn p hp hp2 a ha μ hμ hreg hdens hrect
  have hav : Nonempty (Models n k .mixed) := AdmissibleModel.nonempty_of_range hn hk hkn.le
  have hdens' : ∀ᵐ z ∂μ, 0 < upperDensity μ k z ∧ upperDensity μ k z < ⊤ := hdens
  obtain ⟨-, hae⟩ := hNec n hn k hk hkn.le .mixed hav μ hμ hreg hrect
  filter_upwards [hae, hdens'] with z h1 h2
  exact energyS_lt_top_of_squareEnergy_lt_top hn hk hkn.le hav hμ hreg hp hp2 ha h2.2
    (h1.2 a ha).1

theorem squareSufficient_glue (hQC : Characterization.QualitativeCharacterizationStatement)
    (hE2 : EnergyTwoStatement) : SquareSufficientStatement := by
  intro n hn k hk hkn a ha μ hμ hreg hdens
  refine ⟨fun hS => withCovers_of_squareEnergy hQC hn hk hkn.le hμ hreg hdens ha ?_,
    fun hT => withCovers_of_squareEnergy hQC hn hk hkn.le hμ hreg hdens ha ?_⟩
  · filter_upwards [hS] with z hz
    rwa [(hE2 n hn k hk hkn.le .mixed μ a ha z).1] at hz
  · filter_upwards [hT] with z hz
    rwa [(hE2 n hn k hk hkn.le .mixed μ a ha z).2] at hz

theorem squareNecessary_glue (hNec : Characterization.NecessityStatement)
    (hE2 : EnergyTwoStatement) : SquareNecessaryStatement := by
  intro n hn k hk hkn a ha μ hμ hreg hdens hrect
  obtain ⟨-, hae⟩ := hNec n hn k hk hkn.le .mixed (AdmissibleModel.nonempty_of_range hn hk hkn.le)
    μ hμ hreg hrect
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with z hz
    rw [(hE2 n hn k hk hkn.le .mixed μ a ha z).1]
    exact (hz.2 a ha).1
  · filter_upwards [hae] with z hz
    rw [(hE2 n hn k hk hkn.le .mixed μ a ha z).2]
    exact (hz.2 a ha).1

theorem spAboveTwoSufficient_glue (hQC : Characterization.QualitativeCharacterizationStatement) :
    SpAboveTwoSufficientStatement := by
  intro n hn k hk hkn p hp2 a ha μ hμ hreg hdens hS
  have hav : Nonempty (Models n k .mixed) := AdmissibleModel.nonempty_of_range hn hk hkn.le
  have hdens' : ∀ᵐ z ∂μ, 0 < upperDensity μ k z ∧ upperDensity μ k z < ⊤ := hdens
  refine withCovers_of_squareEnergy hQC hn hk hkn.le hμ hreg hdens ha ?_
  filter_upwards [hS, hdens'] with z h1 h2
  exact squareEnergy_lt_top_of_energyS_lt_top hn hk hkn.le hav hμ hreg hp2 ha h2.2 h1

theorem tpBelowTwoSufficient_glue (hQC : Characterization.QualitativeCharacterizationStatement)
    (hB2 : BetaPowTwoStatement) : TpBelowTwoSufficientStatement := by
  intro n hn k hk hkn p hp hp2 a ha μ hμ hreg hdens hT
  refine withCovers_of_squareEnergy hQC hn hk hkn.le hμ hreg hdens ha ?_
  filter_upwards [hT] with z hz
  exact (squareEnergy_le_two_rpow_mul_energyT hB2 hn hk hkn.le .mixed μ hp hp2.le a z).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top) hz)

theorem tpAboveTwoNecessary_glue (hNec : Characterization.NecessityStatement)
    (hB2 : BetaPowTwoStatement) : TpAboveTwoNecessaryStatement := by
  intro n hn k hk hkn p hp2 a ha μ hμ hreg hdens hrect
  obtain ⟨-, hae⟩ := hNec n hn k hk hkn.le .mixed (AdmissibleModel.nonempty_of_range hn hk hkn.le)
    μ hμ hreg hrect
  filter_upwards [hae] with z hz
  exact (energyT_le_two_rpow_mul_squareEnergy hB2 hn hk hkn.le .mixed μ hp2.le a z).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
      (hz.2 a ha).1)

/-! ## The ambient endpoint -/

theorem classificationAmbient_glue (hAC : AmbientCharacterizationStatement)
    (hZG : AmbientZeroGraphCoverStatement) : ClassificationAmbientStatement := by
  intro n hn p hp a ha μ hμ hreg hdens
  have hzero : ∀ T : FamilyKind, Nonempty (Models n (n + 2) T) → ∀ z : Space n,
      energyS μ (n + 2) T p a z = 0 ∧ energyT μ (n + 2) T p a z = 0 := fun T hT z =>
    ⟨energyS_ambient_eq_zero hT μ hp a z, energyT_ambient_eq_zero hT μ hp a z⟩
  have hAbs : μ ≪ hausdorffP n (n + 2) := ((hAC n hn μ hμ hreg).2.2).mpr hdens
  have hrect : IsRegularlyRectifiableMeasure .mixed (n + 2) μ := ((hAC n hn μ hμ hreg).1).mpr hAbs
  have hcov : ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover .mixed (n + 2) μ ε := fun ε hε => by
    obtain ⟨G, -, hG⟩ := (hZG n hn).1 ε hε
    refine ⟨∅, {0}, fun i => absurd i.2 (Set.notMem_empty _), fun _ => G, ?_⟩
    refine measure_mono_null (fun z hz => ?_) measure_empty
    refine hz (Or.inr (mem_iUnion.mpr ⟨⟨0, Set.mem_singleton 0⟩, ?_⟩))
    show z ∈ G.image
    rw [hG]
    exact mem_univ z
  have hwc : IsRegularlyRectifiableWithCovers (n + 2) μ := ⟨hrect, hcov⟩
  have hav : Nonempty (Models n (n + 2) .mixed) :=
    AdmissibleModel.nonempty_of_range hn (by omega) le_rfl
  refine ⟨hwc, hzero, fun _ => hwc, fun _ => ?_, fun _ => hwc, fun _ => ?_⟩
  · exact Eventually.of_forall fun z => by
      rw [(hzero .mixed hav z).1]
      exact ENNReal.zero_lt_top
  · exact Eventually.of_forall fun z => by
      rw [(hzero .mixed hav z).2]
      exact ENNReal.zero_lt_top

/-! ## The classification -/

/-- **The classification**, from its inputs.

Hypotheses: `NecessityStatement`, `QualitativeCharacterizationStatement`, `GraphSourceStatement`,
`BetaPowTwoStatement`, `EnergyTwoStatement`, `AmbientCharacterizationStatement`,
`AmbientZeroGraphCoverStatement`, `ExponentWitnessBelowStatement`,
`LacunaryFullIntervalStatement`, `LacunaryHausdorffStatement`,
`ExponentWitnessAboveCarrierStatement`, `ExponentWitnessAboveEnergyStatement` and
`LacunaryDensityLimitStatement`. It also uses the clamping, annulus and unavailable-family laws,
the small-scale comparisons, the time-slice transfer, the direct witnesses, the lacunary
frequency existence, and the four row statements. -/
theorem betaPClassification_of_providers (hNec : Characterization.NecessityStatement)
    (hQC : Characterization.QualitativeCharacterizationStatement)
    (hGS : Characterization.GraphSourceStatement) (hB2 : BetaPowTwoStatement)
    (hE2 : EnergyTwoStatement) (hAC : AmbientCharacterizationStatement)
    (hZG : AmbientZeroGraphCoverStatement) (hEWB : Examples.ExponentWitnessBelowStatement)
    (hLFI : Examples.LacunaryFullIntervalStatement) (hLH : Examples.LacunaryHausdorffStatement)
    (hEWAC : Examples.ExponentWitnessAboveCarrierStatement)
    (hEWAE : Examples.ExponentWitnessAboveEnergyStatement)
    (hLDL : Examples.LacunaryDensityLimitStatement) : BetaPClassificationStatement :=
  ⟨spBelowTwo_notSufficient_of_witness (directWitnessMinus_of_providers hGS hE2)
      timeSliceTransfer_obligation,
    spBelowTwoNecessary_glue hNec, squareSufficient_glue hQC hE2, squareNecessary_glue hNec hE2,
    spAboveTwoSufficient_glue hQC,
    spAboveTwo_notNecessary_of_witness directWitnessPlus_obligation timeSliceTransfer_obligation,
    tpBelowTwoSufficient_glue hQC hB2,
    tpBelowTwo_notNecessary_of_witness lacunaryFrequencyExistence_obligation hEWB hLFI hLH hQC,
    tpAboveTwo_notSufficient_of_witness lacunaryFrequencyExistence_obligation hEWAC hEWAE hLDL,
    tpAboveTwoNecessary_glue hNec hB2, classificationAmbient_glue hAC hZG,
    betaPEndpointInvariance_skeleton⟩

end ParabolicRectifiability.BetaP
