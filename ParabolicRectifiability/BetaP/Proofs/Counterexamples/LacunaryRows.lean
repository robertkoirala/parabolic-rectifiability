import ParabolicRectifiability.BetaP.Proofs.Counterexamples.RowLemmas
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.RowSupport
import ParabolicRectifiability.BetaP.Proofs.Support.Interfaces
import ParabolicRectifiability.Characterization.Statements.Main
import ParabolicRectifiability.Examples.Proofs.Lacunary.GraphEmbeddingLemmas
import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyLemmas

/-! # The `T_p` rows and failures at `n = 1`, `k = 2`, from lacunary witnesses

Each theorem named `c2_…_of_witness` is a statement about the `T_p` conditions at `n = 1`,
`k = 2`, deduced from the lacunary witnesses:

* `c2_tpBelowTwo_notNecessary_of_witness`: for `p < 2` the condition `T_p` is not necessary;
* `c2_tpAboveTwo_notSufficient_of_witness`: for `p > 2` the condition `T_p` is not sufficient;
* `c2_tpAboveTwo_noVanishingRemainder_of_witness` and
  `c2_tpAboveTwo_noIntegratedRemainder_of_witness`: for `p > 2` there is no vanishing, and no
  integrated, remainder.

The `…_of` forms take the consumed statements as hypotheses: the amplitude statements
`Examples.E2ExponentAmplitudeStatement` / `Examples.E2NonregularAmplitudeStatement` and, for the
case `p > 2`, `BetaPowAnnulusStatement`; the closed forms supply the admissibility results
`e2_exponentAmplitude_admissible` / `e2_nonregularAmplitude_admissible` and the annulus statement
`c2_input_betaPowAnnulus`. The frequencies come from the hypothesis `hFreq` (one application
each). The other ingredients are the `Examples.*Statement`s, the qualitative characterization, the
graph-map and zero-base facts, and `c2_tpAbove_endpoint`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## `T_p` is not necessary below two -/

/-- Absolute continuity of `ν_J = F_#(L¹⌊J)` from a Hausdorff identity `H_P²(F(E)) = c_H |E|`
(`c_H > 0`) on measurable `E ⊆ J`, for a measurable embedding `F`. (Take a Borel Hausdorff-null hull `A'` and set
`E' = J ∩ F⁻¹(A')`.) -/
theorem c2_lacunary_ac {F : ℝ → Space 1} (hGE : MeasurableEmbedding F) {cH : ℝ} (hcH : 0 < cH)
    (hH : ∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ Examples.lacunaryInterval →
      hausdorffP 1 2 (F '' E) = ENNReal.ofReal cH * volume E) :
    (volume.restrict Examples.lacunaryInterval).map F ≪ hausdorffP 1 2 := by
  refine Measure.AbsolutelyContinuous.mk fun A hAm hA => ?_
  have hJm : MeasurableSet Examples.lacunaryInterval := measurableSet_Icc
  have hEm : MeasurableSet (F ⁻¹' A ∩ Examples.lacunaryInterval) := (hGE.measurable hAm).inter hJm
  have h1 := hH _ hEm.nullMeasurableSet Set.inter_subset_right
  have h2 : hausdorffP 1 2 (F '' (F ⁻¹' A ∩ Examples.lacunaryInterval)) = 0 :=
    measure_mono_null ((Set.image_mono Set.inter_subset_left).trans (Set.image_preimage_subset F A))
      hA
  rw [h2, eq_comm, mul_eq_zero] at h1
  rw [hGE.map_apply, Measure.restrict_apply (hGE.measurable hAm)]
  rcases h1 with h | h
  · exact absurd h (ENNReal.ofReal_pos.mpr hcH).ne'
  · exact h

/-- **Core of the case `p < 2`.** For a measurable embedding `F` that is the graph map of a
general regular rank-zero time function `g`, a Hausdorff identity on `J`, and divergence of `T_p^a` at every interior point,
`ν_J = F_#(L¹⌊J)` is a witness of the row: locally Radon (finite), positive finite upper density and
covers of every positive norm (the qualitative characterization, through regular rectifiability:
the zero-base carrying and the absolute continuity above), and `T_p^a < ∞` fails on the positive-mass set `F((-1,1))`. -/
theorem c2_tpBelowTwo_notNecessary_core
    (hQC : Characterization.QualitativeCharacterizationStatement) {F : ℝ → Space 1} {g : ℝ → ℝ}
    {η : ℝ} (hFg : F = fun t => point (EuclideanSpace.single (0 : Fin 1) (g t)) t)
    (hGE : MeasurableEmbedding F)
    (hreg : IsGeneralRegularVerticalFunction Examples.zeroDirection (Examples.zeroBaseLift g) η)
    {cH : ℝ} (hcH : 0 < cH)
    (hH : ∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ Examples.lacunaryInterval →
      hausdorffP 1 2 (F '' E) = ENNReal.ofReal cH * volume E)
    {p a : ℝ} (hdiv : ∀ t ∈ Ioo (-1 : ℝ) 1,
      energyT ((volume.restrict Examples.lacunaryInterval).map F) 2 .mixed p a (F t) = ⊤) :
    IsFiniteMeasureOnCompacts ((volume.restrict Examples.lacunaryInterval).map F) ∧
      ((volume.restrict Examples.lacunaryInterval).map F).InnerRegular ∧
      HasPositiveFiniteUpperDensity 2 ((volume.restrict Examples.lacunaryInterval).map F) ∧
      IsRegularlyRectifiableWithCovers 2 ((volume.restrict Examples.lacunaryInterval).map F) ∧
      ¬ (∀ᵐ z ∂((volume.restrict Examples.lacunaryInterval).map F),
        energyT ((volume.restrict Examples.lacunaryInterval).map F) 2 .mixed p a z < ⊤) := by
  have hac := c2_lacunary_ac hGE hcH hH
  have hvol : IsFiniteMeasure (volume.restrict Examples.lacunaryInterval) :=
    ⟨by rw [Measure.restrict_apply_univ, Examples.lacunaryInterval, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  have hμc : IsFiniteMeasureOnCompacts ((volume.restrict Examples.lacunaryInterval).map F) :=
    inferInstance
  have hμr : ((volume.restrict Examples.lacunaryInterval).map F).InnerRegular := inferInstance
  have hcarry : (volume.restrict Examples.lacunaryInterval).map F
      (Set.range fun t : ℝ => point (EuclideanSpace.single (0 : Fin 1) (g t)) t)ᶜ = 0 := by
    rw [← hFg, hGE.map_apply, Set.preimage_compl, Set.preimage_range, Set.compl_univ,
      measure_empty]
  have hrect : IsRegularlyRectifiableMeasure .mixed 2
      ((volume.restrict Examples.lacunaryInterval).map F) :=
    ⟨hac, c2_zeroBase_carried g η hreg _ hcarry⟩
  have hT : Nonempty (Models 1 2 .mixed) :=
    AdmissibleModel.nonempty_of_range le_rfl (by norm_num) (by norm_num)
  obtain ⟨-, -, -, -, -, -, hcons, -⟩ :=
    hQC 1 le_rfl 2 (by norm_num) (by norm_num) .mixed hT _ hμc hμr
  obtain ⟨hdens, hcov⟩ := hcons hrect
  refine ⟨hμc, hμr, hdens.mono fun z hz => ⟨hz.1.trans_le hz.2.1, hz.2.2⟩, ⟨hrect, hcov⟩, ?_⟩
  intro hfin
  have h1 := hGE.ae_map_iff.mp hfin
  have h2 : (volume.restrict Examples.lacunaryInterval) (Ioo (-1 : ℝ) 1) = 0 := by
    refine measure_mono_null (fun t ht => ?_) (ae_iff.mp h1)
    show ¬ (energyT _ 2 .mixed p a _ < ⊤)
    rw [hdiv t ht]
    exact lt_irrefl _
  rw [Measure.restrict_apply measurableSet_Ioo, Examples.lacunaryInterval,
    Set.inter_eq_left.mpr Set.Ioo_subset_Icc_self, Real.volume_Ioo] at h2
  norm_num at h2

/-- **The case `p < 2` in implication form** over the exponent-amplitude statement. The amplitudes
`a_j = c₀/(√(j+1) log(j+2))` with `c₀ = log 2 / 2` are admissible, `hFreq` gives
their frequencies, `ε = 1/16`. -/
theorem c2_tpBelowTwo_notNecessary_of (hAmp : Examples.E2ExponentAmplitudeStatement)
    (hFreq : LacunaryFrequencyExistence) (hEW : Examples.ExponentWitnessBelowStatement)
    (_hFI : Examples.LacunaryFullIntervalStatement) (hHs : Examples.LacunaryHausdorffStatement)
    (hQC : Characterization.QualitativeCharacterizationStatement) :
    TpBelowTwoNotNecessaryStatement := by
  intro p hp hp2 a ha
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨hapos, hale⟩ := hAmp (Real.log 2 / 2) (half_pos hlog)
  obtain ⟨N, hN⟩ := hFreq _ hapos (hale.mpr (half_le_self hlog.le))
  have hε : (0 : ℝ) < 1 / 16 := by norm_num
  have hε' : (1 / 16 : ℝ) ≤ 3 / 16 := by norm_num
  obtain ⟨C, -, hW⟩ := hEW
  obtain ⟨-, -, -, hreg, hdiv⟩ := hW (Real.log 2 / 2) (half_pos hlog) (1 / 16) N hε hε' hN
  obtain ⟨cH, hcH, hH⟩ := hHs
  exact ⟨_, c2_tpBelowTwo_notNecessary_core hQC
    (F := Examples.lacunaryGraphMap (1 / 16) (Examples.exponentAmplitude (Real.log 2 / 2)) N)
    (g := Examples.lacunaryFunction (1 / 16) (Examples.exponentAmplitude (Real.log 2 / 2)) N) rfl
    (Examples.e2_lacunaryGraphMap_measurableEmbedding _ _ N) hreg hcH (hH _ _ N hε hε' hN)
    (fun t ht => hdiv p hp hp2 a ha t ht)⟩

/-- **`T_p` is not necessary below two**, from the lacunary witness: the statement
`tpBelowTwo_notNecessary_of_witness`. -/
theorem c2_tpBelowTwo_notNecessary_of_witness (hFreq : LacunaryFrequencyExistence)
    (hEW : Examples.ExponentWitnessBelowStatement)
    (hFI : Examples.LacunaryFullIntervalStatement) (hHs : Examples.LacunaryHausdorffStatement)
    (hQC : Characterization.QualitativeCharacterizationStatement) :
    TpBelowTwoNotNecessaryStatement :=
  c2_tpBelowTwo_notNecessary_of Examples.e2_exponentAmplitude_admissible hFreq hEW hFI hHs hQC

/-! ## `T_p` is not sufficient above two -/

/-- **Core of the case `p > 2`.** A source `μ = F_#(L¹⌊Q)` (`F` a measurable embedding) supported in
`P(0,1)` with mass `1/2`, whose countably regular carriers with `H_P^2`-null residual are null,
with density limit `2` parameter-almost everywhere and `T_p^2 ≤ B` on its support, is a witness
of the row at every endpoint `a > 0` (`c2_tpAbove_endpoint` over `BetaPowAnnulusStatement` for
the endpoint; the carrier contradiction of `c2_quarter_carrier` for nonrectifiability). -/
theorem c2_tpAboveTwo_notSufficient_core (hL3 : BetaPowAnnulusStatement)
    {μ : Measure (Space 1)} {F : ℝ → Space 1} {Q : Set ℝ} (hμF : μ = (volume.restrict Q).map F)
    (hGE : MeasurableEmbedding F) (hsupp : μ.support ⊆ Metric.ball (point 0 0) 1)
    (hmass : μ univ = ENNReal.ofReal (1 / 2))
    (hcar : ∀ (I I' : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph 1 2 (εH i))
      (εV : I' → ℝ) (V : ∀ j, GeneralRegularVerticalGraph 1 2 (εV j)) (Z : Set (Space 1)),
      hausdorffP 1 2 Z = 0 → μ ((⋃ i, (H i).image) ∪ (⋃ j, (V j).image) ∪ Z) = 0)
    (hdens : ∀ᵐ t ∂(volume.restrict Q), Tendsto (densityRatio μ 2 (F t)) (𝓝[>] 0) (𝓝 2))
    {p B : ℝ} (hp : 0 < p) (hbound : ∀ z ∈ μ.support, energyT μ 2 .mixed p 2 z ≤ ENNReal.ofReal B)
    {a : ℝ} (ha : 0 < a) :
    IsFiniteMeasureOnCompacts μ ∧ μ.InnerRegular ∧ HasPositiveFiniteUpperDensity 2 μ ∧
      (∀ᵐ z ∂μ, energyT μ 2 .mixed p a z < ⊤) ∧ ¬ IsRegularlyRectifiableMeasure .mixed 2 μ := by
  obtain ⟨hfin, -, -⟩ := c2_quarter_basic hsupp hmass
  have hμc : IsFiniteMeasureOnCompacts μ := inferInstance
  have hμr : μ.InnerRegular := inferInstance
  refine ⟨hμc, hμr, ?_, ?_, ?_⟩
  · have hd : ∀ᵐ z ∂μ, Tendsto (densityRatio μ 2 z) (𝓝[>] 0) (𝓝 2) := by
      rw [hμF] at hdens ⊢
      exact hGE.ae_map_iff.mpr hdens
    refine hd.mono fun z hz => ?_
    show 0 < upperDensity μ 2 z ∧ upperDensity μ 2 z < ⊤
    rw [upperDensity, hz.limsup_eq]
    exact ⟨by simp, by simp⟩
  · filter_upwards [Measure.support_mem_ae (μ := μ)] with z hz
    exact c2_tpAbove_endpoint hL3 μ hμc hμr p hp z a ha ((hbound z hz).trans_lt ENNReal.ofReal_lt_top)
  · rintro ⟨-, I, J, εH, H, εV, V, hcarr⟩
    have h0 := c2_quarter_carrier (μplus := 0) (μG := μ) hsupp hmass hcar (zero_add μ).symm hcarr
      ⟨I, J, εH, H, εV, V, by rw [Set.sdiff_self, measure_empty]⟩
    rw [Measure.coe_zero, Pi.zero_apply] at h0
    exact (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).ne' h0.symm

/-- **The case `p > 2` in implication form** over the nonregular-amplitude statement and
`BetaPowAnnulusStatement`. Amplitudes `a_j = (j+1)^{-1/2}`, frequencies from `hFreq`, `ε = 1/16`, the quarter source. -/
theorem c2_tpAboveTwo_notSufficient_of (hNA : Examples.E2NonregularAmplitudeStatement)
    (hL3 : BetaPowAnnulusStatement) (hFreq : LacunaryFrequencyExistence)
    (hC : Examples.ExponentWitnessAboveCarrierStatement)
    (hE : Examples.ExponentWitnessAboveEnergyStatement)
    (hD : Examples.LacunaryDensityLimitStatement) : TpAboveTwoNotSufficientStatement := by
  intro p hp a ha
  obtain ⟨N, hN⟩ := hFreq _ (fun j => (hNA j).1) (fun j => (hNA j).2)
  have hε : (0 : ℝ) < 1 / 16 := by norm_num
  have hε' : (1 / 16 : ℝ) ≤ 3 / 16 := by norm_num
  obtain ⟨hsupp, hmass, hcar⟩ := hC (1 / 16) N hε hε' hN
  obtain ⟨Cp, -, hEp⟩ := hE p hp
  obtain ⟨hbound, -, -⟩ := hEp (1 / 16) N hε hε' hN
  have hQJ : Icc (-1 / 4 : ℝ) (1 / 4) ⊆ Examples.lacunaryInterval :=
    Set.Icc_subset_Icc (by norm_num) (by norm_num)
  exact ⟨_, c2_tpAboveTwo_notSufficient_core hL3 (F := Examples.lacunaryGraphMap (1 / 16)
      Examples.nonregularAmplitude N) (Q := Icc (-1 / 4 : ℝ) (1 / 4)) rfl
    (Examples.e2_lacunaryGraphMap_measurableEmbedding _ _ N) hsupp hmass hcar
    (hD (1 / 16) _ N hε hε' hN _ measurableSet_Icc.nullMeasurableSet hQJ) (by linarith) hbound ha⟩

/-- **`T_p` is not sufficient above two**, from the lacunary witness: the statement
`tpAboveTwo_notSufficient_of_witness`. -/
theorem c2_tpAboveTwo_notSufficient_of_witness (hFreq : LacunaryFrequencyExistence)
    (hC : Examples.ExponentWitnessAboveCarrierStatement)
    (hE : Examples.ExponentWitnessAboveEnergyStatement)
    (hD : Examples.LacunaryDensityLimitStatement) : TpAboveTwoNotSufficientStatement :=
  c2_tpAboveTwo_notSufficient_of Examples.e2_nonregularAmplitude_admissible c2_input_betaPowAnnulus
    hFreq hC hE hD

/-! ## No vanishing `T_p` threshold remainder above two -/

/-- **Core of the threshold remainder** (one source). With zero exceptional mass at the budget `M` (the support bound), any
decomposition granted by `Φ` has remainder `1/2` (`c2_quarter_carrier`), so `1/2 ≤ Φ(M)`. -/
theorem c2_quarter_threshold {μ : Measure (Space 1)}
    (hsupp : μ.support ⊆ Metric.ball (point 0 0) 1) (hmass : μ univ = ENNReal.ofReal (1 / 2))
    (hcar : ∀ (I I' : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph 1 2 (εH i))
      (εV : I' → ℝ) (V : ∀ j, GeneralRegularVerticalGraph 1 2 (εV j)) (Z : Set (Space 1)),
      hausdorffP 1 2 Z = 0 → μ ((⋃ i, (H i).image) ∪ (⋃ j, (V j).image) ∪ Z) = 0)
    {p M : ℝ} (hM : 0 < M)
    (hbound : ∀ z ∈ μ.support, energyT μ 2 .mixed p 2 z ≤ ENNReal.ofReal M) {Φ : ℝ → ℝ}
    (hΦ0 : ∀ M, 0 ≤ Φ M)
    (hΦ : ∀ μ : Measure (Space 1), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 < M → 0 ≤ Γ →
        μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyT μ 2 .mixed p 2 z}) ≤
          ENNReal.ofReal Γ →
        ∃ (μplus μG : Measure (Space 1)) (F : Set (Space 1)),
          μ = μplus + μG ∧ μplus (Metric.ball (point 0 0) 1) ≤ ENNReal.ofReal (Φ M + Γ) ∧
          μG Fᶜ = 0 ∧
          ∃ (I J : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph 1 2 (εH i))
            (εV : J → ℝ) (V : ∀ j, GeneralRegularVerticalGraph 1 2 (εV j)),
            hausdorffP 1 2 (F \ ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)) = 0) :
    1 / 2 ≤ Φ M := by
  obtain ⟨hfin, -, -⟩ := c2_quarter_basic hsupp hmass
  have hexc : μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyT μ 2 .mixed p 2 z}) ≤
      ENNReal.ofReal 0 := by
    rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero]
    refine measure_mono_null ?_ Measure.measure_compl_support
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzs
    exact absurd hz.2 (not_lt.mpr (hbound z hzs))
  obtain ⟨μplus, μG, F, hdec, hrem, hG, hcov⟩ := hΦ μ inferInstance inferInstance M 0 hM le_rfl hexc
  rw [c2_quarter_carrier hsupp hmass hcar hdec hG hcov, add_zero] at hrem
  exact (ENNReal.ofReal_le_ofReal_iff (hΦ0 M)).mp hrem

/-- **No vanishing threshold remainder, in implication form** over the nonregular-amplitude
statement. -/
theorem c2_tpAboveTwo_noVanishingRemainder_of (hNA : Examples.E2NonregularAmplitudeStatement)
    (hFreq : LacunaryFrequencyExistence) (hC : Examples.ExponentWitnessAboveCarrierStatement)
    (hE : Examples.ExponentWitnessAboveEnergyStatement) :
    TpAboveTwoNoVanishingRemainderStatement := by
  rintro p hp ⟨Φ, hΦ0, hΦlim, hΦ⟩
  obtain ⟨N, hN⟩ := hFreq _ (fun j => (hNA j).1) (fun j => (hNA j).2)
  obtain ⟨Cp, hCp, hEp⟩ := hE p hp
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 3 / 16 → 1 / 2 ≤ Φ (Cp * ε ^ p) := by
    intro ε hε hε'
    obtain ⟨hsupp, hmass, hcar⟩ := hC ε N hε hε' hN
    obtain ⟨hbound, -, -⟩ := hEp ε N hε hε' hN
    exact c2_quarter_threshold hsupp hmass hcar (mul_pos hCp (Real.rpow_pos_of_pos hε p)) hbound
      hΦ0 hΦ
  obtain ⟨ε, hε, hε', hlt⟩ := c2_squeeze_limit Φ hΦlim (fun ε => Cp * ε ^ p) Cp p (3 / 16) (1 / 2)
    hCp (by linarith) (by norm_num) (by norm_num)
    (fun ε hε _ => ⟨mul_pos hCp (Real.rpow_pos_of_pos hε p), le_rfl⟩)
  exact absurd (key ε hε hε') (not_le.mpr hlt)

/-- **No vanishing `T_p` threshold remainder above two**, from the lacunary witness: the
statement `tpAboveTwo_noVanishingRemainder_of_witness`. -/
theorem c2_tpAboveTwo_noVanishingRemainder_of_witness (hFreq : LacunaryFrequencyExistence)
    (hC : Examples.ExponentWitnessAboveCarrierStatement)
    (hE : Examples.ExponentWitnessAboveEnergyStatement) :
    TpAboveTwoNoVanishingRemainderStatement :=
  c2_tpAboveTwo_noVanishingRemainder_of Examples.e2_nonregularAmplitude_admissible hFreq hC hE

/-! ## No vanishing integrated `T_p` remainder above two -/

/-- **Core of the integrated remainder** (one source). The actual integrated energy over `P(0,1)` is the full integral
(`μ(P(0,1)ᶜ) = 0`), strictly positive and at most `b/2`; any decomposition granted by `Ψ` has
remainder `1/2`, so `1/2 ≤ Ψ(e)`. -/
theorem c2_quarter_integrated {μ : Measure (Space 1)}
    (hsupp : μ.support ⊆ Metric.ball (point 0 0) 1) (hmass : μ univ = ENNReal.ofReal (1 / 2))
    (hcar : ∀ (I I' : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph 1 2 (εH i))
      (εV : I' → ℝ) (V : ∀ j, GeneralRegularVerticalGraph 1 2 (εV j)) (Z : Set (Space 1)),
      hausdorffP 1 2 Z = 0 → μ ((⋃ i, (H i).image) ∪ (⋃ j, (V j).image) ∪ Z) = 0)
    {p b : ℝ} (hb : 0 ≤ b) (hpos : 0 < ∫⁻ z, energyT μ 2 .mixed p 2 z ∂μ)
    (hle : ∫⁻ z, energyT μ 2 .mixed p 2 z ∂μ ≤ ENNReal.ofReal (b / 2)) {Ψ : ℝ → ℝ}
    (hΨ0 : ∀ e, 0 ≤ Ψ e)
    (hΨ : ∀ μ : Measure (Space 1), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      (∫⁻ z in Metric.ball (point 0 0) 1, energyT μ 2 .mixed p 2 z ∂μ) < ⊤ →
      ∃ (μplus μG : Measure (Space 1)) (F : Set (Space 1)),
        μ = μplus + μG ∧
        μplus (Metric.ball (point 0 0) 1) ≤
          ENNReal.ofReal (Ψ (∫⁻ z in Metric.ball (point 0 0) 1, energyT μ 2 .mixed p 2 z ∂μ).toReal) ∧
        μG Fᶜ = 0 ∧
        ∃ (I J : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph 1 2 (εH i))
          (εV : J → ℝ) (V : ∀ j, GeneralRegularVerticalGraph 1 2 (εV j)),
          hausdorffP 1 2 (F \ ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)) = 0) :
    (0 < (∫⁻ z in Metric.ball (point 0 0) 1, energyT μ 2 .mixed p 2 z ∂μ).toReal ∧
      (∫⁻ z in Metric.ball (point 0 0) 1, energyT μ 2 .mixed p 2 z ∂μ).toReal ≤ b) ∧
    1 / 2 ≤ Ψ (∫⁻ z in Metric.ball (point 0 0) 1, energyT μ 2 .mixed p 2 z ∂μ).toReal := by
  obtain ⟨hfin, hc, -⟩ := c2_quarter_basic hsupp hmass
  have hrestr : μ.restrict (Metric.ball (point 0 0) 1) = μ :=
    Measure.restrict_eq_self_of_ae_mem (Filter.eventually_mem_set.mpr (mem_ae_iff.mpr hc))
  have heq : (∫⁻ z in Metric.ball (point 0 0) 1, energyT μ 2 .mixed p 2 z ∂μ) =
      ∫⁻ z, energyT μ 2 .mixed p 2 z ∂μ := by
    rw [hrestr]
  have hlt : (∫⁻ z in Metric.ball (point 0 0) 1, energyT μ 2 .mixed p 2 z ∂μ) < ⊤ := by
    rw [heq]
    exact hle.trans_lt ENNReal.ofReal_lt_top
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact ENNReal.toReal_pos (by rw [heq]; exact hpos.ne') hlt.ne
  · rw [heq]
    exact (ENNReal.toReal_le_of_le_ofReal (by linarith) hle).trans (by linarith)
  · obtain ⟨μplus, μG, F, hdec, hrem, hG, hcov⟩ := hΨ μ inferInstance inferInstance hlt
    rw [c2_quarter_carrier hsupp hmass hcar hdec hG hcov] at hrem
    exact (ENNReal.ofReal_le_ofReal_iff (hΨ0 _)).mp hrem

/-- **No vanishing integrated remainder, in implication form** over the nonregular-amplitude
statement. -/
theorem c2_tpAboveTwo_noIntegratedRemainder_of (hNA : Examples.E2NonregularAmplitudeStatement)
    (hFreq : LacunaryFrequencyExistence) (hC : Examples.ExponentWitnessAboveCarrierStatement)
    (hE : Examples.ExponentWitnessAboveEnergyStatement) :
    TpAboveTwoNoIntegratedRemainderStatement := by
  rintro p hp ⟨Ψ, hΨ0, hΨlim, hΨ⟩
  obtain ⟨N, hN⟩ := hFreq _ (fun j => (hNA j).1) (fun j => (hNA j).2)
  obtain ⟨Cp, hCp, hEp⟩ := hE p hp
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 3 / 16 →
      (0 < (∫⁻ z in Metric.ball (point 0 0) 1,
          energyT (Examples.lacunarySource ε Examples.nonregularAmplitude N (Icc (-1 / 4) (1 / 4)))
            2 .mixed p 2 z
          ∂(Examples.lacunarySource ε Examples.nonregularAmplitude N (Icc (-1 / 4) (1 / 4)))).toReal ∧
        (∫⁻ z in Metric.ball (point 0 0) 1,
          energyT (Examples.lacunarySource ε Examples.nonregularAmplitude N (Icc (-1 / 4) (1 / 4)))
            2 .mixed p 2 z
          ∂(Examples.lacunarySource ε Examples.nonregularAmplitude N (Icc (-1 / 4) (1 / 4)))).toReal
          ≤ Cp * ε ^ p) ∧
      1 / 2 ≤ Ψ (∫⁻ z in Metric.ball (point 0 0) 1,
          energyT (Examples.lacunarySource ε Examples.nonregularAmplitude N (Icc (-1 / 4) (1 / 4)))
            2 .mixed p 2 z
          ∂(Examples.lacunarySource ε Examples.nonregularAmplitude N (Icc (-1 / 4) (1 / 4)))).toReal := by
    intro ε hε hε'
    obtain ⟨hsupp, hmass, hcar⟩ := hC ε N hε hε' hN
    obtain ⟨-, hpos, hle⟩ := hEp ε N hε hε' hN
    exact c2_quarter_integrated hsupp hmass hcar (mul_pos hCp (Real.rpow_pos_of_pos hε p)).le hpos
      hle hΨ0 hΨ
  obtain ⟨ε, hε, hε', hlt⟩ := c2_squeeze_limit Ψ hΨlim
    (fun ε => (∫⁻ z in Metric.ball (point 0 0) 1,
      energyT (Examples.lacunarySource ε Examples.nonregularAmplitude N (Icc (-1 / 4) (1 / 4)))
        2 .mixed p 2 z
      ∂(Examples.lacunarySource ε Examples.nonregularAmplitude N (Icc (-1 / 4) (1 / 4)))).toReal)
    Cp p (3 / 16) (1 / 2) hCp (by linarith) (by norm_num) (by norm_num)
    (fun ε hε hε' => (key ε hε hε').1)
  exact absurd (key ε hε hε').2 (not_le.mpr hlt)

/-- **No vanishing integrated `T_p` remainder above two**, from the lacunary witness: the
statement `tpAboveTwo_noIntegratedRemainder_of_witness`. -/
theorem c2_tpAboveTwo_noIntegratedRemainder_of_witness (hFreq : LacunaryFrequencyExistence)
    (hC : Examples.ExponentWitnessAboveCarrierStatement)
    (hE : Examples.ExponentWitnessAboveEnergyStatement) :
    TpAboveTwoNoIntegratedRemainderStatement :=
  c2_tpAboveTwo_noIntegratedRemainder_of Examples.e2_nonregularAmplitude_admissible hFreq hC hE

end ParabolicRectifiability.BetaP
