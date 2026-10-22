import ParabolicRectifiability.QuantitativeCharacterization.Assembly.Characterization
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # Approximants, local, bounded and ambient corollaries of the quantitative characterization

Each theorem takes exactly the outside statements it uses as hypotheses (implication form):
* `measure_approximants_of_providers`: intrinsic sufficiency (typed reference covers) and the
  canonical decomposition;
* `uniform_local_of_providers`: intrinsic sufficiency;
* `bounded_support_of_providers`: intrinsic sufficiency and the canonical decomposition;
* `ambient_endpoint_of_providers`: the vanishing of the ambient energy;
* `quantitative_common_constants_of_providers`: the above together with the beta-`p` Hölder and
  clamping laws and the identification `B_2 = β²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **Approximants of a covering**: `exists_root_approximants` for the prescribed covering, with the relative tail
from the ADR lower bound at the root, and `approximant_canonical_limits` with the canonical
decomposition (density hypothesis from the ADR bounds). -/
theorem measure_approximants_of_providers
    (hIS : Characterization.IntrinsicSufficiencyStatement)
    (hCan : IntegralCanonical.CanonicalDecompositionStatement) :
    MeasureApproximantsStatement := by
  intro n hn k hk hkn A hA μ hfin hreg _ _ hADR _ L hL K hK a ha R hR 𝒞
  have hup : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r →
      μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k) := fun z hz r hr => (hADR z hz r hr).2
  obtain ⟨FH, FV, hs, hid, hrect, htail, -⟩ :=
    exists_root_approximants n hn k hk hkn A hA L hL (reference_typed_covers hIS hn hk hkn hL)
      K hK μ hfin hreg a ha R hR 𝒞 fun b hb s hs _ => hup b hb.1 s hs
  have hdens : HasPositiveFiniteUpperDensity k μ :=
    hasPositiveFiniteUpperDensity_of_growth hreg (by linarith) one_pos
      fun z hz r hr _ => hADR z hz r hr
  exact ⟨FH, FV, hs, hid, htail (hADR a ha R hR).1,
    approximant_canonical_limits n hn k hk hkn A L K hL hK μ hfin hreg
      (hCan n hn k hk hkn μ hfin hreg (Or.inr hdens) 1 one_pos) hup a ha R hR 𝒞 FH FV hs hrect⟩

/-- **The local forward and converse clauses**: the forward part from the local covering supply (buffer enlarged to `2L₀`) and
`localForwardBounds_of_supply` with the typed reference covers; the converse is
`exists_local_reverse_bound`. -/
theorem uniform_local_of_providers (hIS : Characterization.IntrinsicSufficiencyStatement) :
    UniformLocalStatement := by
  intro n hn k hk hkn
  refine ⟨fun A hA => ?_, exists_local_reverse_bound n hn k hk hkn⟩
  obtain ⟨L₀, C₀, Bloc, hL₀, hC₀, hB, hloc⟩ := exists_localCoveringSupply n hn k hk hkn A hA
  refine ⟨max Bloc (2 * L₀), le_max_of_le_left hB, L₀, hL₀, C₀, hC₀, ?_⟩
  exact localForwardBounds_of_supply hn hk hkn hA hL₀ hC₀ (le_max_of_le_left hB)
    (le_max_right _ _) (hloc.mono hL₀ le_rfl le_rfl (le_max_left _ _))
    (reference_typed_covers hIS hn hk hkn hL₀)

/-- **The bounded-support case**: the bounded covering supply, the reverse bound at its `L₀`, and
`boundedSupportBounds_of_supply`, with the absolute-tail constant `C(A,k) = max(2A, 2^k + 1)`,
chosen before `n`. -/
theorem bounded_support_of_providers (hIS : Characterization.IntrinsicSufficiencyStatement)
    (hCan : IntegralCanonical.CanonicalDecompositionStatement) : BoundedSupportStatement := by
  intro k hk A hA
  refine ⟨max (2 * A) ((2 : ℝ) ^ k + 1),
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 ^ k + 1) (le_max_right _ _), fun n hn hkn => ?_⟩
  obtain ⟨L₀, C₀, hL₀, hC₀, hbdd⟩ := exists_boundedCoveringSupply n hn k hk hkn A hA
  obtain ⟨Crev, hCrev, hrev⟩ := global_reverse n hn k hk hkn L₀ hL₀ A hA
  have hprod : 0 < C₀ * Crev := mul_pos (by linarith) hCrev
  refine ⟨L₀, hL₀, C₀ * (1 + Crev) + Crev, by nlinarith, ?_⟩
  exact boundedSupportBounds_of_supply hIS hCan hn hk hkn hA hC₀ hCrev hbdd hrev (by nlinarith)
    (by nlinarith) (by linarith) (by nlinarith)

/-- **The ambient case**: the sole model is `X` (ROOT, `AdmissibleModel.ambient_toSet`); `β_μ = 0` at
positive radii by `AmbientEnergyZeroStatement` and at nonpositive radii by the
definition of `betaSq`; upper growth gives absolute continuity
(`absolutelyContinuous_of_upper_growth`); the one-ball covering is `ambient_root_covering`. -/
theorem ambient_endpoint_of_providers (hAZ : Foundations.AmbientEnergyZeroStatement) :
    AmbientEndpointStatement := by
  intro n hn μ hfin hreg
  refine ⟨fun M => AdmissibleModel.ambient_toSet M, fun z r => ?_,
    fun ⟨A, hA⟩ => absolutelyContinuous_of_upper_growth n hn (n + 2) (by omega) le_rfl μ hfin hreg
      A hA, fun a ha R hR => ?_⟩
  · by_cases hr : 0 < r
    · exact (hAZ n hn μ hfin hreg .mixed
        (AdmissibleModel.nonempty_of_range hn (by omega) le_rfl)).1 z r hr
    · simp [betaSq, hr]
  · obtain ⟨𝒞, hidx, hcr, hs, -, -, hN⟩ := ambient_root_covering n hn μ hfin hreg a ha R hR
    exact ⟨𝒞, hidx, hcr, hs, hN⟩

/-- **Common constants of the quantitative characterization and its corollaries.** The two supplies are raised to the common
`L₀ = max(L_loc, L_bdd)`, `C₀ = max(C_loc, C_bdd)` and `B_loc = max(B, 2L₀)`; the reverse bound is
taken at this final `L₀`, and only then `C = C₀(1 + C_rev) + C_rev` is fixed. The four bodies
follow from the assembly lemmas and `betaPowForwardBounds_of_main`. -/
theorem quantitative_common_constants_of_providers
    (hIS : Characterization.IntrinsicSufficiencyStatement)
    (hCan : IntegralCanonical.CanonicalDecompositionStatement)
    (hH : BetaP.BetaPowHolderStatement) (hCl : BetaP.BetaPowClampingStatement)
    (h2 : Foundations.BetaPowTwoStatement) : QuantitativeCommonConstantsStatement := by
  intro k hk A hA
  refine ⟨max (2 * A) ((2 : ℝ) ^ k + 1),
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 ^ k + 1) (le_max_right _ _), fun n hn hkn => ?_⟩
  obtain ⟨L₁, C₁, B₁, hL₁, hC₁, hB₁, hloc⟩ := exists_localCoveringSupply n hn k hk hkn A hA
  obtain ⟨L₂, C₂, hL₂, hC₂, hbdd⟩ := exists_boundedCoveringSupply n hn k hk hkn A hA
  have hL₀ : 1 ≤ max L₁ L₂ := le_max_of_le_left hL₁
  have hC₀ : 1 ≤ max C₁ C₂ := le_max_of_le_left hC₁
  obtain ⟨Crev, hCrev, hrev⟩ := global_reverse n hn k hk hkn (max L₁ L₂) hL₀ A hA
  have hprod : 0 < max C₁ C₂ * Crev := mul_pos (by linarith) hCrev
  obtain ⟨C, hC1, hCC₀, hCC, hCrevC⟩ : ∃ C : ℝ, 1 ≤ C ∧ max C₁ C₂ ≤ C ∧
      max C₁ C₂ * (1 + Crev) ≤ C ∧ Crev ≤ C :=
    ⟨max C₁ C₂ * (1 + Crev) + Crev, by nlinarith, by nlinarith, by linarith, by nlinarith⟩
  have hloc' : LocalCoveringSupply n k A (max L₁ L₂) C (max B₁ (2 * max L₁ L₂)) :=
    hloc.mono hL₁ (le_max_left _ _) ((le_max_left _ _).trans hCC₀) (le_max_left _ _)
  have hbdd' : BoundedCoveringSupply n k A (max L₁ L₂) (max C₁ C₂) :=
    hbdd.mono hL₂ (by linarith) (le_max_right _ _) (le_max_right _ _)
  have hMain : MainTheoremBounds n k A (max L₁ L₂) C :=
    mainTheoremBounds_of_supply hn hk hkn hloc' hrev hC1 le_rfl hCrevC
  exact ⟨max L₁ L₂, hL₀, C, hC1, max B₁ (2 * max L₁ L₂), le_max_of_le_left hB₁, hMain,
    betaPowForwardBounds_of_main hH hCl h2 hn hk hkn hA hMain,
    localForwardBounds_of_supply hn hk hkn hA hL₀ hC1 (le_max_of_le_left hB₁) (le_max_right _ _)
      hloc' (reference_typed_covers hIS hn hk hkn hL₀),
    boundedSupportBounds_of_supply hIS hCan hn hk hkn hA hC₀ hCrev hbdd' hrev hC1 hCC₀ hCC
      hCrevC⟩

end ParabolicRectifiability.QuantitativeCharacterization
