import ParabolicRectifiability.Characterization.Assembly.Branches
import ParabolicRectifiability.Characterization.Statements.Main
import ParabolicRectifiability.Foundations.Statements.DensityBridges
import ParabolicRectifiability.Foundations.Statements.Measurability
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # Assembly of the characterization theorem

`qualitative_characterization_of_providers` proves `QualitativeCharacterizationStatement`,
the qualitative characterization of regularly rectifiable measures, without circular
dependencies between its parts.

Inputs:
* the branches `intrinsic_sufficiency_skeleton` and `necessity_skeleton`;
* four shared statements, taken as hypotheses (implication form): `ACBridgeStatement`,
  `UpperDensityDominationStatement`, `DensityMeasurabilityStatement` (first clause) and
  `AmbientEnergyZeroStatement` (first clause);
* the basic fact `squareEnergy_of_nonpos`.

The encoding of the statement is organized around condition (1). The assembly is:
* (2) with one endpoint ⇒ (4): the AC bridge on `O = X` gives `μ ≪ H_P^k`; upper-density
  domination on the Borel carriers `F_{j,N} = P(0,N) ∩ {Θ^{k,*} ≥ 1/(j+1)}` gives a Borel
  sigma-finite carrier;
* (4) with one endpoint ⇒ (1): intrinsic sufficiency at tolerance one;
* (1) ⇒ (3) and (2), with every endpoint, and (1) ⇒ (4): necessity;
* every endpoint ⇒ one endpoint: take `R = 1`; (3) ⇒ (2): `Θ_* ≤ Θ^*`;
* the consequences: necessity (densities) and intrinsic sufficiency (covers at every
  tolerance);
* `k = n + 2`: the ambient zero energy for positive endpoints, and the empty integral for the
  others.
Because necessity already yields finiteness at every positive endpoint, the finite-annulus
and endpoint-independence clauses of `DensityMeasurabilityStatement` are not needed here.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- Density-level carriers. If `Θ^{k,*}(μ,·) > 0` `μ`-a.e., the Borel sets
`F_{j,N} = P(0,N) ∩ {Θ^{k,*} ≥ 1/(j+1)}` (Borel by the density measurability clause) have
finite `H_P^k` measure by upper-density domination and carry `μ`. -/
theorem hasBorelSigmaFiniteHausdorffCarrier_of_upperDensity_pos
    (hUD : UpperDensityDominationStatement) (hDM : DensityMeasurabilityStatement)
    {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (hpos : ∀ᵐ z ∂μ, 0 < upperDensity μ k z) :
    HasBorelSigmaFiniteHausdorffCarrier k μ := by
  obtain ⟨C, -, hdom⟩ := hUD k hk
  have hmeas : Measurable (upperDensity μ k) := (hDM n hn k hk hkn μ hμ hreg).2
  have hFm : ∀ p : ℕ × ℕ, MeasurableSet (Metric.ball (point 0 0) (p.2 : ℝ) ∩
      {z | ENNReal.ofReal (1 / ((p.1 : ℝ) + 1)) ≤ upperDensity μ k z}) :=
    fun p => measurableSet_ball.inter (measurableSet_le measurable_const hmeas)
  refine hasBorelSigmaFiniteHausdorffCarrier_of_cover
    (fun p : ℕ × ℕ => Metric.ball (point 0 0) (p.2 : ℝ) ∩
      {z | ENNReal.ofReal (1 / ((p.1 : ℝ) + 1)) ≤ upperDensity μ k z}) ?_
    (fun p : ℕ × ℕ => Metric.ball (point 0 0) (p.2 : ℝ) ∩
      {z | ENNReal.ofReal (1 / ((p.1 : ℝ) + 1)) ≤ upperDensity μ k z})
    (fun _ => subset_rfl) hFm ?_
  · refine measure_mono_null ?_ (ae_iff.1 hpos)
    intro z hz
    simp only [mem_compl_iff, mem_iUnion, not_exists] at hz
    show ¬ 0 < upperDensity μ k z
    intro hz0
    obtain ⟨N, hN⟩ := exists_nat_gt (dist z (point 0 0))
    obtain ⟨j, hj⟩ : ∃ j : ℕ, ENNReal.ofReal (1 / ((j : ℝ) + 1)) ≤ upperDensity μ k z := by
      by_cases htop : upperDensity μ k z = ⊤
      · exact ⟨0, by rw [htop]; exact le_top⟩
      · obtain ⟨j, hj⟩ := exists_nat_one_div_lt (ENNReal.toReal_pos hz0.ne' htop)
        refine ⟨j, ?_⟩
        calc ENNReal.ofReal (1 / ((j : ℝ) + 1))
            ≤ ENNReal.ofReal (upperDensity μ k z).toReal := ENNReal.ofReal_le_ofReal hj.le
          _ = upperDensity μ k z := ENNReal.ofReal_toReal htop
    exact hz (j, N) ⟨Metric.mem_ball.2 hN, hj⟩
  · intro p q R
    exact (measure_mono inter_subset_left).trans_lt
      (hdom n hn hkn (Metric.ball (point 0 0) (p.2 : ℝ)) Metric.isOpen_ball
        Metric.isBounded_ball _ (hFm p) inter_subset_left (1 / ((p.1 : ℝ) + 1))
        (by positivity) μ hμ hreg (fun z hz => hz.2)).2

/-- **Qualitative characterization**, from the branches `intrinsic_sufficiency_skeleton` and
`necessity_skeleton` and four shared statements (implication form). The hypotheses are
exactly those used: the AC bridge and upper-density domination for (2) ⇒ (4), density
measurability for the Borel carriers `F_{j,N}`, and the ambient zero energy for the
`k = n + 2` conjunct. -/
theorem qualitative_characterization_of_providers (hAC : ACBridgeStatement)
    (hUD : UpperDensityDominationStatement) (hDM : DensityMeasurabilityStatement)
    (hAZ : AmbientEnergyZeroStatement) : QualitativeCharacterizationStatement := by
  intro n hn k hk hkn T hT μ hμ hreg
  have hIS := intrinsic_sufficiency_skeleton n hn k hk hkn T hT μ hμ hreg
  have hN := necessity_skeleton n hn k hk hkn T hT μ hμ hreg
  -- necessity at a given positive endpoint
  have hNe : IsRegularlyRectifiableMeasure T k μ → ∀ R : ℝ, 0 < R → ∀ᵐ z ∂μ,
      (0 < lowerDensity μ k z ∧ lowerDensity μ k z ≤ upperDensity μ k z ∧
        upperDensity μ k z < ⊤) ∧ squareEnergy μ k T R z < ⊤ :=
    fun h R hR => (hN h).2.mono fun z hz => ⟨hz.1, (hz.2 R hR).2⟩
  -- (4) with one endpoint ⇒ (1): intrinsic sufficiency at tolerance one
  have h41 : μ ≪ hausdorffP n k → HasBorelSigmaFiniteHausdorffCarrier k μ →
      (∃ R : ℝ, 0 < R ∧ ∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) →
      IsRegularlyRectifiableMeasure T k μ := fun hac hcar hR =>
    ⟨hac, isCarriedByFiniteNormGraphs_of_hasTypedMeasureCover (hIS hac hcar hR 1 one_pos)⟩
  -- (2) with one endpoint ⇒ (4) ⇒ (1): the AC bridge and the carriers `F_{j,N}`
  have h21 : (∃ R : ℝ, 0 < R ∧ ∀ᵐ z ∂μ,
        squareEnergy μ k T R z < ⊤ ∧ 0 < upperDensity μ k z ∧ lowerDensity μ k z < ⊤) →
      IsRegularlyRectifiableMeasure T k μ := by
    rintro ⟨R, hR, hae⟩
    have hac : μ ≪ hausdorffP n k := by
      have h := hAC n hn k hk hkn univ isOpen_univ μ hμ hreg R hR T hT
        (hae.mono fun z hz _ => ⟨hz.2.2, hz.1⟩)
      rwa [Measure.restrict_univ] at h
    exact h41 hac
      (hasBorelSigmaFiniteHausdorffCarrier_of_upperDensity_pos hUD hDM hn hk hkn hμ hreg
        (hae.mono fun z hz => hz.2.1))
      ⟨R, hR, hae.mono fun z hz => hz.1⟩
  -- (3) with one endpoint ⇒ (2) with one endpoint ⇒ (1): `Θ_* ≤ Θ^*`
  have h31 : (∃ R : ℝ, 0 < R ∧ ∀ᵐ z ∂μ,
        squareEnergy μ k T R z < ⊤ ∧ 0 < upperDensity μ k z ∧ upperDensity μ k z < ⊤) →
      IsRegularlyRectifiableMeasure T k μ := by
    rintro ⟨R, hR, hae⟩
    exact h21 ⟨R, hR, hae.mono fun z hz =>
      ⟨hz.1, hz.2.1, (lowerDensity_le_upperDensity μ k z).trans_lt hz.2.2⟩⟩
  refine ⟨⟨?_, h21⟩, ⟨?_, ?_⟩, ⟨?_, h31⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  -- (1) ⇒ (2), one endpoint
  · intro h
    exact ⟨1, one_pos, (hNe h 1 one_pos).mono fun z hz =>
      ⟨hz.2, hz.1.1.trans_le hz.1.2.1, hz.1.2.1.trans_lt hz.1.2.2⟩⟩
  -- (1) ⇒ (2), every endpoint
  · intro h R hR
    exact (hNe h R hR).mono fun z hz =>
      ⟨hz.2, hz.1.1.trans_le hz.1.2.1, hz.1.2.1.trans_lt hz.1.2.2⟩
  -- (2), every endpoint ⇒ (1)
  · intro h
    exact h21 ⟨1, one_pos, h 1 one_pos⟩
  -- (1) ⇒ (3), one endpoint
  · intro h
    exact ⟨1, one_pos, (hNe h 1 one_pos).mono fun z hz =>
      ⟨hz.2, hz.1.1.trans_le hz.1.2.1, hz.1.2.2⟩⟩
  -- (1) ⇒ (3), every endpoint
  · intro h R hR
    exact (hNe h R hR).mono fun z hz => ⟨hz.2, hz.1.1.trans_le hz.1.2.1, hz.1.2.2⟩
  -- (3), every endpoint ⇒ (1)
  · intro h
    exact h31 ⟨1, one_pos, h 1 one_pos⟩
  -- (1) ⇒ (4), one endpoint
  · intro h
    exact ⟨h.1, (hN h).1, 1, one_pos, (hNe h 1 one_pos).mono fun z hz => hz.2⟩
  -- (4), one endpoint ⇒ (1)
  · intro h
    exact h41 h.1 h.2.1 h.2.2
  -- (1) ⇒ (4), every endpoint
  · intro h
    exact ⟨h.1, (hN h).1, fun R hR => (hNe h R hR).mono fun z hz => hz.2⟩
  -- (4), every endpoint ⇒ (1)
  · intro h
    exact h41 h.1 h.2.1 ⟨1, one_pos, h.2.2 1 one_pos⟩
  -- consequences: density improvement (necessity) and covers (intrinsic sufficiency)
  · intro h
    exact ⟨(hN h).2.mono fun z hz => hz.1, fun ε hε =>
      hIS h.1 (hN h).1 ⟨1, one_pos, (hNe h 1 one_pos).mono fun z hz => hz.2⟩ ε hε⟩
  -- the ambient endpoint: zero square at every endpoint
  · intro hk2 R z
    subst hk2
    by_cases hR : 0 < R
    · exact (hAZ n hn μ hμ hreg T hT).2 R hR z
    · exact squareEnergy_of_nonpos μ _ T (not_lt.1 hR) z

end ParabolicRectifiability.Characterization
