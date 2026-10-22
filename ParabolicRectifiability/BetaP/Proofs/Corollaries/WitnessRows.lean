import ParabolicRectifiability.BetaP.Proofs.Counterexamples.LacunaryRows
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.SliceRows
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.AboveTwoWitness
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.BelowTwoWitness
import ParabolicRectifiability.BetaP.Proofs.Support.Interfaces
import ParabolicRectifiability.BetaP.Statements.Corollaries
import ParabolicRectifiability.BetaP.Statements.Failures
import ParabolicRectifiability.Examples.Statements.Lacunary
import ParabolicRectifiability.Characterization.Statements.Main
import ParabolicRectifiability.Characterization.Statements.Branches
import ParabolicRectifiability.Foundations.Statements.Measurability
import ParabolicRectifiability.BetaP.Proofs.Comparison.Comparisons
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.DiffuseEnergies
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.LacunaryFrequency
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.TimeSliceTransfer

/-! # Corollaries of the beta-`p` support theorem

The declarations delegate to the comparison and witness constructions of the `BetaP`
development. Witness-based implications keep their inputs as hypotheses.

* Two pointwise energy comparisons under a finite upper density (the analytic content of the
  rows `SpBelowTwoNecessaryStatement` and `SpAboveTwoSufficientStatement`).
* Two shared prerequisites supplied by the `Examples` constructions: the beta-`p` energies of the
  diffuse witness (the input of sharpness), and the existence of admissible lacunary frequencies
  (the single shared input of the four lacunary rows and failures).
* The direct witnesses: for `E₋`, the elementary digit construction and the graph-necessity
  assembly, which consumes `Characterization.GraphSourceStatement`, the time-slice transfer and
  `EnergyTwoStatement`; the construction `E₊`; and the constant-time transfer.
* Four negative table rows and three failure theorems, each in implication form: its
  hypotheses are exactly the statements it consumes (the direct witnesses and transfer, or the
  lacunary statements, the frequency existence and the qualitative characterization).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## Pointwise comparisons under a finite upper density -/

/-- **Comparison below two.** At a point with finite upper `k`-density choose
`r_z, A_z` with `Θ(z,r) ≤ A_z` for `r < r_z`; Hölder (`β_p ≤ Θ^{1/p-1/2} β_2`) gives
`B_p^{2/p} ≤ A_z^{2/p-1} B_2` there, and finite annuli complete the endpoint, so
`S_2^a(z) < ∞ ⇒ S_p^a(z) < ∞` for `0 < p < 2` (no `p ≥ 1` needed). Used for
`SpBelowTwoNecessaryStatement` in `betaPClassification_of_providers`. -/
theorem energyS_lt_top_of_squareEnergy_lt_top {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {T : FamilyKind} (hT : Nonempty (Models n k T)) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) {p : ℝ} (hp : 0 < p) (hp2 : p < 2)
    {a : ℝ} (ha : 0 < a) {z : Space n} (hz : upperDensity μ k z < ⊤)
    (hS : squareEnergy μ k T a z < ⊤) : energyS μ k T p a z < ⊤ := by
  exact ParabolicRectifiability.BetaP.c2_energyS_lt_top_of_squareEnergy_lt_top hn hk hkn hT hμ hreg hp hp2 ha hz hS

/-- **Comparison above two.** With the same point-dependent density bound,
`B_2 ≤ A_z^{1-2/p} B_p^{2/p}` on small scales (Hölder, `p > 2`) and finite annuli give
`S_p^a(z) < ∞ ⇒ S_2^a(z) < ∞`. Used for `SpAboveTwoSufficientStatement`. -/
theorem squareEnergy_lt_top_of_energyS_lt_top {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {T : FamilyKind} (hT : Nonempty (Models n k T)) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) {p : ℝ} (hp2 : 2 < p) {a : ℝ}
    (ha : 0 < a) {z : Space n} (hz : upperDensity μ k z < ⊤)
    (hS : energyS μ k T p a z < ⊤) : squareEnergy μ k T a z < ⊤ := by
  exact ParabolicRectifiability.BetaP.c2_squareEnergy_lt_top_of_energyS_lt_top hn hk hkn hT hμ hreg hp2 ha hz hS

/-! ## The diffuse witness (sharpness of the integrated rates) -/

/-- **Integrated energies of the diffuse witness.** For
`ω = L^{n+1}⌊P(0,1/4)`, `1 ≤ k < n+2`, every available family and every `p > 0`, both
integrated beta-`p` energies at the unit parent (endpoint `2`) are positive and finite:
`B_p(z,r) ≈ r^{n+2-k}` for small balls inside the support, integrable against `dr/r`, and
nonzero because the ambient volume is flat at no scale. Used in
`betaPIntegratedSharpness_of_providers`. -/
theorem diffuse_betaP_integratedEnergy (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k)
    (hkn : k < n + 2) (T : FamilyKind) (hT : Nonempty (Models n k T)) (p : ℝ) (hp : 0 < p) :
    (0 < integratedEnergyS ((parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))) k T p
        (point 0 0) 1 ∧
      integratedEnergyS ((parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))) k T p
        (point 0 0) 1 < ⊤) ∧
    (0 < integratedEnergyT ((parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))) k T p
        (point 0 0) 1 ∧
      integratedEnergyT ((parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))) k T p
        (point 0 0) 1 < ⊤) := by
  exact ParabolicRectifiability.BetaP.c2_diffuse_betaP_integratedEnergy n hn k hk hkn T hT p hp

/-! ## Lacunary frequencies (shared input of the lacunary rows and failures) -/

/-- **Existence of admissible lacunary frequencies** (`LacunaryFrequencyExistence`): for
amplitudes `0 < a_j ≤ 1` the frequencies are chosen recursively above three finite lower bounds
(`16 N_{j-1}`, the low-frequency bound and the amplitude-decay bound). Every lacunary statement
of `Examples` is conditional on `IsLacunaryData`, and none produces the frequencies. This is the
single shared input of the lacunary rows and failures (`tpBelowTwo_notNecessary_of_witness`,
`tpAboveTwo_notSufficient_of_witness`, `tpAboveTwo_noVanishingRemainder_of_witness`,
`tpAboveTwo_noIntegratedRemainder_of_witness`), which take it as a hypothesis instead of each
constructing the frequencies. -/
theorem lacunaryFrequencyExistence_obligation : LacunaryFrequencyExistence := by
  exact ParabolicRectifiability.BetaP.c2_lacunaryFrequencyExistence

/-! ## Direct witnesses -/

/-- **Construction of `E₋`** (part (a) of the direct witnesses, the elementary part): the
dispersed equal-width digit graph `E`
(mixed-radix digits, lifted proportion `δ_j = (j+1)^{-1}` at heights `h_j`, summable tails
`η_j`) has the planar conclusions `IsBelowTwoDigitWitness E`: length exactly one by projection
and cylinder covers; upper density in `[1/2, 2]`; for `p < 2`, the uniform band bound
`β_p^2 ≤ C_p[δ_j^{2/p}(h_j/r)^2 + (η_j/r)^2]` summed over the bands; on one common full set, the
two-height covariance bound `β_2^2 ≥ δ_j/1024` on `[3h_j, 4h_j]`, hence `S_2 = ∞`, and vanishing
lower density. No rectifiability criterion is used. Used in `directWitnessMinus_of_providers`,
through `belowTwoDigitWitness_pure_of_graphSource`. -/
theorem belowTwoDigitWitness_exists : ∃ E : Set Plane, IsBelowTwoDigitWitness E := by
  exact @c2_belowTwoDigitWitness_exists

/-- **Graph-necessity assembly for `E₋`** (part (a) of the direct witnesses): pure
unrectifiability and graph-intersection nullity, where individual-graph full-source necessity
gives graph-intersection nullity.
Inputs: `Characterization.GraphSourceStatement`, the constant-time transfer
`TimeSliceTransferStatement` and `EnergyTwoStatement`.
For `E` with the planar conclusions, `μ = ι_#(H¹⌊E)` is finite, hence locally
Radon. At every point of the common full set, the transfer (`p = 2`, horizontal family) and
`S_2 = squareEnergy` give `S^1_{μ,H}(ιz) = ∞`, so B's statement makes `ι(E) ∩ Γ` `H_P^1`-null
for every horizontal graph `Γ` of every finite slope; the `H¹`-null rest of `E` has null image
by the transfer's Hausdorff clause. The Euclidean small-graph decomposition (Rademacher, the
zero-derivative image estimate, rotated small-slope graphs extended and placed at time zero)
then gives pure one-unrectifiability. Used in `directWitnessMinus_of_providers`. -/
theorem belowTwoDigitWitness_pure_of_graphSource (hGS : Characterization.GraphSourceStatement)
    (hTS : TimeSliceTransferStatement) (hE2 : EnergyTwoStatement) {E : Set Plane}
    (hE : IsBelowTwoDigitWitness E) :
    IsPurelyUnrectifiable E ∧
      ∀ (ε : ℝ) (G : HorizontalGraph 2 1 ε), hausdorffP 2 1 (timeSlice '' E ∩ G.image) = 0 := by
  exact @c2_belowTwoDigitWitness_pure_of_graphSource hGS hTS hE2 E hE

/-- **The witness `E₊`** (part (b) of the direct witnesses): the decorated-segment witness.
Its last conjunct is the exact zero-slope cover. Used, together with the time-slice transfer,
in `SpAboveTwoNotNecessaryStatement`. -/
theorem directWitnessPlus_obligation : DirectWitnessPlusStatement := by
  exact c2_directWitnessPlus

/-- **Constant-time transfer** (`TimeSliceTransferStatement`) at `n = 2`, `k = 1`, for arbitrary
measures, with the Hausdorff-source clause. The general time-slice identity is
`Examples.TimeSliceStatement`, which assumes a locally Radon spatial source and omits the
Hausdorff-source clause, so it does not imply this statement verbatim; this statement is its
`n = 2`, `k = 1` specialization for arbitrary spatial measures (the proof is pointwise),
together with the isometric Hausdorff pushforward of the slice. It does not include the generic
rectifiability-transfer conclusions, which are not used here. Used in
`belowTwoDigitWitness_pure_of_graphSource`, the two `S_p` rows and the `S_p` failure. -/
theorem timeSliceTransfer_obligation : TimeSliceTransferStatement := by
  exact ParabolicRectifiability.BetaP.c2_timeSliceTransfer

/-! ## Negative table rows -/

/-- **Row: `S_p`, `0 < p < 2`, is not sufficient** at `n = 2`, `k = 1`. Push
`λ₋ = H¹⌊E₋` into time zero; the transfer gives the parabolic energies and Hausdorff source,
the planar density bounds give `0 < Θ^{1,*} < ∞` a.e., the uniform `S_p^{a,E}` bound gives
finiteness a.e., and graph-intersection nullity with `μ ≪ H_P^1` excludes regular
rectifiability (no vertical graphs at `k = 1`). -/
theorem spBelowTwo_notSufficient_of_witness (hW : DirectWitnessMinusStatement)
    (hTS : TimeSliceTransferStatement) : SpBelowTwoNotSufficientStatement := by
  exact c2_spBelowTwo_notSufficient_of_witness hW hTS

/-- **Row: `S_p`, `2 < p < ∞`, is not necessary** at `n = 2`, `k = 1`.
Push `λ₊` into time zero (by the transfer); the exact zero-slope cover of `E₊` and
`μ = H_P^1⌊ι(E₊)` give regular rectifiability with covers of every slope; the density limit `2`
of `E₊` gives the density hypothesis directly; divergence of `S_p^{a,E}` off a countable set
gives failure of a.e. finiteness. The generic restricted-Hausdorff density lemmas are not
used. -/
theorem spAboveTwo_notNecessary_of_witness (hW : DirectWitnessPlusStatement)
    (hTS : TimeSliceTransferStatement) : SpAboveTwoNotNecessaryStatement := by
  exact c2_spAboveTwo_notNecessary_of_witness hW hTS

/-- **Row: `T_p`, `0 < p < 2`, is not necessary** at `n = 1`, `k = 2`.
For admissible lacunary data with `a_j = c₀/(√j log(j+1))` (`c₀` small enough
for `a_j ≤ 1`; frequencies from the hypothesis `LacunaryFrequencyExistence`), `ν_J` is
absolutely continuous with respect to `H_P^2` (Hausdorff identity), carried by one general
regular vertical graph, hence regularly rectifiable with covers of every norm (by the
qualitative characterization), has density `2` at interior points, and `T_p^R = ∞` at every
interior point for every `R > 0`. Hypotheses: the frequency existence, the lacunary witness
statements and the qualitative characterization. -/
theorem tpBelowTwo_notNecessary_of_witness (hFreq : LacunaryFrequencyExistence)
    (hEW : Examples.ExponentWitnessBelowStatement)
    (hFI : Examples.LacunaryFullIntervalStatement) (hHs : Examples.LacunaryHausdorffStatement)
    (hQC : Characterization.QualitativeCharacterizationStatement) :
    TpBelowTwoNotNecessaryStatement := by
  exact c2_tpBelowTwo_notNecessary_of_witness hFreq hEW hFI hHs hQC

/-- **Row: `T_p`, `2 < p < ∞`, is not sufficient** at `n = 1`, `k = 2`.
For admissible lacunary data (frequencies from the hypothesis
`LacunaryFrequencyExistence`) the fixed-mass source `ν_ε` on `[-1/4,1/4]` has density `2` a.e.,
`T_p^2 ≤ C_p ε^p` on its support (any positive endpoint by finite annuli), and every countably
regular carrier is `ν_ε`-null, so it is not regularly rectifiable. Hypotheses: the frequency
existence and the lacunary witness statements. -/
theorem tpAboveTwo_notSufficient_of_witness (hFreq : LacunaryFrequencyExistence)
    (hC : Examples.ExponentWitnessAboveCarrierStatement)
    (hE : Examples.ExponentWitnessAboveEnergyStatement)
    (hD : Examples.LacunaryDensityLimitStatement) : TpAboveTwoNotSufficientStatement := by
  exact c2_tpAboveTwo_notSufficient_of_witness hFreq hC hE hD

/-! ## Remainder failures -/

/-- **No vanishing `S_p` remainder below two.** Egorov and compact inner approximation give a compact
`F ⊆ E₋` of positive measure with uniformly small tails; the lower-mass lemma for the same
`ν = H_P^1⌊ι(F)` and normalized rescaling at a lower-mass radius produce sources with zero
exceptional mass, arbitrarily small threshold and unit-ball mass `≥ c₁`, all of whose
admissible good measures vanish. Hypotheses: the direct witness `E₋` and the transfer. -/
theorem spBelowTwo_noVanishingRemainder_of_witness (hW : DirectWitnessMinusStatement)
    (hTS : TimeSliceTransferStatement) : SpBelowTwoNoVanishingRemainderStatement := by
  exact c2_spBelowTwo_noVanishingRemainder_of_witness hW hTS

/-- **No vanishing `T_p` threshold remainder above two.** With admissible lacunary data
(frequencies from the hypothesis `LacunaryFrequencyExistence`), the sources `ν_ε` have zero exceptional mass at the
budget `M_ε = C_p ε^p`, every good measure of a nonnegative decomposition is dominated by `ν_ε`
and carried by a `ν_ε`-null countably regular carrier, so the remainder is the full mass `1/2`
while `M_ε → 0`. Hypotheses: the frequency existence and the lacunary witness statements. -/
theorem tpAboveTwo_noVanishingRemainder_of_witness (hFreq : LacunaryFrequencyExistence)
    (hC : Examples.ExponentWitnessAboveCarrierStatement)
    (hE : Examples.ExponentWitnessAboveEnergyStatement) :
    TpAboveTwoNoVanishingRemainderStatement := by
  exact c2_tpAboveTwo_noVanishingRemainder_of_witness hFreq hC hE

/-- **No vanishing integrated `T_p` remainder above two.** The same sources (frequencies from
the hypothesis `LacunaryFrequencyExistence`) have actual integrated energy `0 < e_ε ≤ C_p ε^p/2 → 0` through
positive values while the remainder stays `1/2`; no monotonicity or value at zero of `Ψ` is
used. Hypotheses: the frequency existence and the lacunary witness statements. -/
theorem tpAboveTwo_noIntegratedRemainder_of_witness (hFreq : LacunaryFrequencyExistence)
    (hC : Examples.ExponentWitnessAboveCarrierStatement)
    (hE : Examples.ExponentWitnessAboveEnergyStatement) :
    TpAboveTwoNoIntegratedRemainderStatement := by
  exact c2_tpAboveTwo_noIntegratedRemainder_of_witness hFreq hC hE

end ParabolicRectifiability.BetaP
