import ParabolicRectifiability.Foundations.Statements.CompactBridge
import ParabolicRectifiability.Foundations.Statements.DensityBridges
import ParabolicRectifiability.Foundations.Statements.Measurability
import ParabolicRectifiability.Foundations.Statements.Ambient
import ParabolicRectifiability.Decomposition.Interfaces
import ParabolicRectifiability.Foundations.Proofs.EnergyRescaling
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.DensityMeasurability
import ParabolicRectifiability.Foundations.Proofs.UpperGrowth
import ParabolicRectifiability.Foundations.Proofs.AmbientCover
import ParabolicRectifiability.Enhancements.Proofs.Domination.EnergyDomination
import ParabolicRectifiability.Foundations.Proofs.RestrictRadon
import ParabolicRectifiability.Foundations.Proofs.AmbientEnergy
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.PackingMass
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.UpperDomination
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.BoundedGrowth
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.BetaPowTwo
import ParabolicRectifiability.Foundations.Proofs.Ambient.LocalCore
import ParabolicRectifiability.Foundations.Proofs.SquareEnergyBounds
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.EnergyTwo
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.EnergySmul
import ParabolicRectifiability.Foundations.Proofs.SquareEnergySmul
import ParabolicRectifiability.Foundations.Proofs.CompactBridge
import ParabolicRectifiability.Foundations.Proofs.Ambient.Characterization
import ParabolicRectifiability.Foundations.Proofs.Ambient.Densities

/-! # Foundational statements, proved

Each theorem below proves one of the foundational statements (`DensityMeasurabilityStatement`,
`PackingMassStatement`, `CompactBridgeRepresentativeStatement`, the ambient statements, and so
on) by delegating to the imported proof named in its body. The bounded-growth result
`exists_boundedGrowth_constant` keeps the core threshold theorem and the packing statement as
explicit hypotheses; no theorem assumes its own conclusion.

Most of these lemmas are independent statements. Two are assembled from others: the
absolute-continuity bridge combines the core threshold theorem
`family_rectifiable_reifenberg`, `PackingMassStatement`, the bounded-growth constant
`exists_boundedGrowth_constant`, the implication
`absolutelyContinuous_hausdorffP_of_growth` and a countable union over level sets; the
compact-bridge function and cover inclusions follow from the identification of representatives.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-! ## Measurability, monotonicity, annuli, scaling -/

/-- **Borel densities.** Exactly `DensityMeasurabilityStatement`: both densities of a
locally Radon source are Borel (limits over rational radii and monotonicity of ball mass). -/
theorem densities_measurable_of_locallyRadon : DensityMeasurabilityStatement := by
  exact fmeas1_density_measurability

/-- **Borel restrictions are locally Radon.** Exactly `RestrictLocallyRadonStatement`. -/
theorem restrict_isFiniteMeasureOnCompacts_innerRegular : RestrictLocallyRadonStatement := by
  exact restrict_isFiniteMeasureOnCompacts_innerRegular_proof

/-- **Domination of beta and energy.** Exactly `BetaEnergyDominationStatement`: `ν ≤ c μ` gives
`b_ν ≤ c b_μ` and `S_ν^R ≤ c S_μ^R` for every family. -/
theorem betaSq_squareEnergy_le_of_le_ofReal_smul : BetaEnergyDominationStatement := by
  exact fmeas3_betaSq_squareEnergy_le_of_le_ofReal_smul

/-- **Finite-annulus bound.** Exactly `AnnulusBoundStatement`. -/
theorem lintegral_betaSq_Ioo_le_annulus : AnnulusBoundStatement := by
  exact ParabolicRectifiability.Foundations.lintegral_betaSq_Ioo_le_annulus_proof

/-- **Endpoint independence of finiteness.** Exactly `SquareFinitenessEndpointStatement`. -/
theorem squareEnergy_lt_top_iff_of_endpoints : SquareFinitenessEndpointStatement := by
  exact ParabolicRectifiability.Foundations.squareEnergy_lt_top_iff_of_endpoints_proof

/-- **Dilation law for the square function.** Exactly `SquareEnergyRescalingStatement`:
`S_{μ_{q,R}}^A(z) = S_μ^{RA}(q + δ_R z)`. The beta-level identity is `betaSq_rescaledSource`;
what remains is the change of variables `r ↦ R r` in the scale integral, carried out in
`squareEnergy_rescaledSource_eq_proof`. -/
theorem squareEnergy_rescaledSource_eq : SquareEnergyRescalingStatement := by
  exact squareEnergy_rescaledSource_eq_proof

/-- **Scalar law for the square function.** Exactly `SquareEnergySmulStatement`. The
available-family case is `squareEnergy_smul`; the remaining case is an unavailable family,
where both sides are `⊤`. -/
theorem squareEnergy_ofReal_smul_eq : SquareEnergySmulStatement := by
  exact ParabolicRectifiability.Foundations.f2i_squareEnergySmul_proof

/-! ## Compatibility of the beta-`p` quantities with `p = 2` -/

/-- **`B_2 = b`.** Exactly `BetaPowTwoStatement`. -/
theorem betaPow_two_eq_betaSq_all : BetaPowTwoStatement := by
  exact f3_betaPow_two_eq_betaSq_proof

/-- **`S_2 = T_2 = S`.** Exactly `EnergyTwoStatement`. -/
theorem energyS_energyT_two_eq : EnergyTwoStatement := by
  exact ParabolicRectifiability.Foundations.f2c_energyTwo_proof

/-- **Amplitude laws of the beta-`p` energies.** Exactly `EnergyPowSmulStatement`. -/
theorem energyS_energyT_ofReal_smul_eq : EnergyPowSmulStatement := by
  exact ParabolicRectifiability.Foundations.f2c_energyPowSmul_proof

/-! ## Packing, domination, bounded growth, absolute continuity -/

/-- **Packing turns lower density into retained mass.** Exactly `PackingMassStatement`. -/
theorem restrict_ball_le_of_packing_lowerDensity : PackingMassStatement := by
  exact fpack_packing_mass

/-- **Positive upper density gives Hausdorff domination.** Exactly
`UpperDensityDominationStatement`. -/
theorem hausdorffP_le_of_upperDensity_ge : UpperDensityDominationStatement := by
  exact fupdom_upper_density_domination

/-- **Bounded square and bounded lower density give growth.**

There is a dimensional constant `C_n > 0`, chosen before `k`, the family and the
source, such that for `1 ≤ k ≤ n + 2`, an available family `T`, a locally Radon `ν`, reals
`A, m ≥ 0` and an endpoint `R > 0`: if `S_{ν,T}^R ≤ m` and `Θ_*^k(ν,·) ≤ A` hold `ν`-almost
everywhere on all of `X`, then `ν(P(q,ρ)) ≤ C_n (A + m) ρ^k` for every centre `q` and
`0 < ρ ≤ R/2`.

Implication form. The proof uses only the core threshold theorem and the packing statement,
which are taken as hypotheses: `hcore` is the type of
`family_rectifiable_reifenberg n hn` (the core threshold theorem in `P(0,1)` with
endpoint `2`), and `hpack` is `PackingMassStatement`. The proof applies the core to the
rescaled source in `P(q,ρ)` with threshold `m` and zero exceptional mass (endpoint
`2ρ ≤ R`), bounds the remainder by `C m ρ^k`, and bounds the retained mass by
`5^k C A ρ^k` through `hpack` applied to the actual compact support, whose packing field has
exactly the shape of the hypothesis of `PackingMassStatement`. The unconditional growth bound
follows once both inputs are supplied; `hcore` alone does not give `hpack`, which is the
separate statement `restrict_ball_le_of_packing_lowerDensity`. -/
theorem exists_boundedGrowth_constant (n : ℕ) (hn : 1 ≤ n)
    (hcore : ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
      μ (Metric.ball (point 0 0) 1 ∩
        {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ →
      HasFamilyDecomposition k T C M Γ μ)
    (hpack : PackingMassStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ ν : Measure (Space n), IsFiniteMeasureOnCompacts ν → ν.InnerRegular →
      ∀ A m R : ℝ, 0 ≤ A → 0 ≤ m → 0 < R →
      (∀ᵐ z ∂ν, squareEnergy ν k T R z ≤ ENNReal.ofReal m ∧
        lowerDensity ν k z ≤ ENNReal.ofReal A) →
      ∀ (q : Space n) (ρ : ℝ), 0 < ρ → ρ ≤ R / 2 →
        ν (Metric.ball q ρ) ≤ ENNReal.ofReal (C * (A + m) * ρ ^ k) := by
  exact fbgrowth_exists_boundedGrowth_constant n hn hcore hpack

/-- **Upper growth implies absolute continuity.**

For `1 ≤ n`, `1 ≤ k ≤ n + 2`, a locally Radon `λ`, a real `B` and a radius
`r₀ > 0` with `λ(P(p,r)) ≤ B r^k` for every centre `p` and `0 < r ≤ r₀`: `λ ≪ H_P^k` (on
arbitrary sets). Proof: cover an `H_P^k`-null set by sets of small diameter and small
`Σ d_i^k`, enlarge each to a ball of twice the diameter centred in the set, and use countable
subadditivity; singletons are `λ`-null by the growth bound. -/
theorem absolutelyContinuous_hausdorffP_of_growth :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ lam : Measure (Space n), IsFiniteMeasureOnCompacts lam → lam.InnerRegular →
    ∀ B r₀ : ℝ, 0 < r₀ →
      (∀ (p : Space n) (r : ℝ), 0 < r → r ≤ r₀ →
        lam (Metric.ball p r) ≤ ENNReal.ofReal (B * r ^ k)) →
      lam ≪ hausdorffP n k := by
  exact fgac_absolutelyContinuous_hausdorffP_of_growth_proof

/-! ## The compact bridge -/

/-- **Representative identification for the compact bridge.** Exactly
`CompactBridgeRepresentativeStatement` (no compact support or Lipschitz hypothesis). The
function and cover inclusions are derived from it. -/
theorem representsGeneral_of_representsHalfTimeDerivative :
    CompactBridgeRepresentativeStatement := by
  exact ParabolicRectifiability.Foundations.compactBridgeRepresentative_proof

/-! ## The ambient case `k = n + 2` -/

/-- **Ambient energies vanish, arbitrary source.** Exactly
`AmbientEnergyZeroArbitrarySourceStatement`: at `k = n + 2` every vertical model is all of
`X`, so every available fitting cost is zero. -/
theorem ambient_betaSq_squareEnergy_eq_zero : AmbientEnergyZeroArbitrarySourceStatement := by
  exact ambient_betaSq_squareEnergy_eq_zero_proof

/-- **The zero-graph cover.** Exactly `AmbientZeroGraphCoverStatement`. -/
theorem ambient_zero_graph_cover_all : AmbientZeroGraphCoverStatement := by
  exact ambient_zero_graph_cover_all_proof

/-- **Ambient characterization.** Exactly `AmbientCharacterizationStatement`. -/
theorem ambient_rectifiable_iff_ac_iff_density : AmbientCharacterizationStatement := by
  exact ParabolicRectifiability.Foundations.f2i_ambient_rectifiable_iff_ac_iff_density

/-- **Differentiation with respect to volume.** Exactly
`AmbientAbsolutelyContinuousDensityStatement`. -/
theorem ambient_densities_pos_finite_of_ac_volume :
    AmbientAbsolutelyContinuousDensityStatement := by
  exact ParabolicRectifiability.Foundations.f2i_ambientDensities_proof

/-- **Ambient core with zero remainder in every cylinder.** Exactly
`AmbientLocalCoreStatement`. The theorem `ambient_retained_decomposition` is its unit-ball
case and is a possible proof input after rescaling. -/
theorem ambient_local_core_bounds : AmbientLocalCoreStatement := by
  exact f3_ambient_local_core_bounds_proof

end ParabolicRectifiability.Foundations
