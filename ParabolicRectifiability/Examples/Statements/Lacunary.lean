import ParabolicRectifiability.Examples.Lacunary
import ParabolicRectifiability.Foundations.BetaPow
import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Foundations.Graphs

/-! # Statements: the lacunary graph examples

The statements concern the lacunary estimates, the nonregular example and the exponent
witnesses.

The proposition definitions specify the public interfaces; their proofs are exported as `lacunary_convergence`,
`lacunary_estimates`, `lacunary_nonregular` and `lacunary_exponent_witnesses`.

Conventions.
* `F = lacunaryGraphMap ε a N`, `ν_E = lacunarySource ε a N E`, `J = lacunaryInterval`.
  Every statement carries the standing hypotheses `0 < ε ≤ 3/16` and `IsLacunaryData a N`.
* "Measurable `E ⊆ J`" is Lebesgue measurable: `NullMeasurableSet E volume` and `E ⊆ J`.
* `n = 1`, `k = 2`. The unsubscripted beta-`p` and square energies use the mixed family
  `FamilyKind.mixed`, the default family `A_k`. At `n = 1`, `k = 2`
  the horizontal family is unavailable (`k ≤ n` fails), so the mixed family consists of the
  vertical lines `{c} × ℝ`.
* `S^R_{2,μ}` is the existing `squareEnergy μ 2 .mixed R`; `T^R_{q,μ}` is
  `Foundations.energyT μ 2 .mixed q R`. The Foundations energies have a real endpoint; the
  endpoint `∞` is written as the supremum `⨆ R : ℝ, energyT μ 2 .mixed q R z`, which equals the
  integral over `(0,∞)` by monotone convergence. `sup_t X(t) ≤ Y` is written `∀ t, X(t) ≤ Y`.
* Real constants are compared through `ENNReal.ofReal`; amplitude sums are extended sums
  `∑' j, ENNReal.ofReal (a j ^ q)`, possibly `⊤`.
* The constants `C_q`, `C_p`, `C` are chosen after their exponent and
  before `ε`, `a`, `N`, `E`, `t`, `R`; the Hausdorff normalization constant `c_H` is chosen
  first. The lower-bound coefficients `c_q` form one function `c : ℝ → ℝ` of the exponent,
  positive on `q > 0`, chosen before all data. The index `j₀ = j₀(t,E,R)` is chosen after the
  data and `t`, `E`, `R` and **before** the exponent `q > 0`, so it does not depend on `q`;
  the full-interval clause uses the same `c` and the same order.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-! ## Lacunary estimates -/

/-- **Isometry.** `F` is an isometry from `(ℝ, √|t-s|)` onto its image in
`(Space 1, d_P)`. -/
def LacunaryIsometryStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ t s : ℝ, dist (lacunaryGraphMap ε a N t) (lacunaryGraphMap ε a N s) = Real.sqrt |t - s|

/-- **Exact ball identity.** `ν_E(P(F(t),r)) = |E ∩ (t-r², t+r²)|` for every measurable
`E ⊆ J`, every `t ∈ ℝ` and every `r > 0`. -/
def LacunaryBallMeasureStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
  ∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ lacunaryInterval →
  ∀ (t r : ℝ), 0 < r →
    lacunarySource ε a N E (Metric.ball (lacunaryGraphMap ε a N t) r) =
      volume (E ∩ Ioo (t - r ^ 2) (t + r ^ 2))

/-- **Hausdorff identity.** There is a positive normalization constant `c_H`, chosen before
all data, with `H_P²(F(E)) = c_H |E|` for every measurable `E ⊆ J`. `H_P²` is the project's
unnormalized `hausdorffP 1 2`. -/
def LacunaryHausdorffStatement : Prop :=
  ∃ cH : ℝ, 0 < cH ∧
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ lacunaryInterval →
      hausdorffP 1 2 (lacunaryGraphMap ε a N '' E) = ENNReal.ofReal cH * volume E

/-- **Density limit.** For almost every `t ∈ E`, the ratio `ν_E(P(F(t),r)) / r²` tends to
`2` as `r ↓ 0`. "Almost every point of `F(E)`" is read in the parameter `t`, with Lebesgue
measure on `E`; this is the same as `ν_E`-almost every point of `F(E)`. -/
def LacunaryDensityLimitStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
  ∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ lacunaryInterval →
    ∀ᵐ t ∂(volume.restrict E),
      Tendsto (densityRatio (lacunarySource ε a N E) 2 (lacunaryGraphMap ε a N t))
        (𝓝[>] (0 : ℝ)) (𝓝 2)

/-- **Full-interval regularity.** `ν_J` is two-Ahlfors regular at the points `F(t)`,
`t ∈ J`, of its support for `0 < r ≤ 1` (some constant `C ≥ 1` with
`r²/C ≤ ν_J(P(F(t),r)) ≤ C r²`), and at every interior point `-1 < t < 1` the density ratio
equals `2` at all sufficiently small radii. -/
def LacunaryFullIntervalStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    (∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ lacunaryInterval, ∀ r : ℝ, 0 < r → r ≤ 1 →
        ENNReal.ofReal (r ^ 2 / C) ≤
            lacunarySource ε a N lacunaryInterval (Metric.ball (lacunaryGraphMap ε a N t) r) ∧
          lacunarySource ε a N lacunaryInterval (Metric.ball (lacunaryGraphMap ε a N t) r) ≤
            ENNReal.ofReal (C * r ^ 2)) ∧
    (∀ t ∈ Ioo (-1 : ℝ) 1, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      densityRatio (lacunarySource ε a N lacunaryInterval) 2 (lacunaryGraphMap ε a N t) r = 2)

/-- **All-scale upper energy.** For every `q ≥ 1` there is `C_q > 0` such that
`sup_{t ∈ ℝ} T^∞_{q,ν_E}(F(t)) ≤ C_q ε^q Σ_j a_j^q` for every measurable `E ⊆ J`. -/
def LacunaryUpperEnergyStatement : Prop :=
  ∀ q : ℝ, 1 ≤ q → ∃ C : ℝ, 0 < C ∧
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ lacunaryInterval →
    ∀ t : ℝ,
      (⨆ R : ℝ, energyT (lacunarySource ε a N E) 2 .mixed q R (lacunaryGraphMap ε a N t)) ≤
        ENNReal.ofReal (C * ε ^ q) * ∑' j, ENNReal.ofReal (a j ^ q)

/-- **Restriction-stable lower energy.** There are coefficients `c_q > 0`
(`q > 0`) such that, for every measurable `E ⊆ J`, every Lebesgue density point
`t ∈ E ∩ (-1,1)` of `E` and every `R > 0`, some `j₀ = j₀(t,E,R)`, independent of `q`, gives
`T^R_{q,ν_E}(F(t)) ≥ c_q ε^q Σ_{j ≥ j₀} a_j^q` for every `q > 0`; and for `E = J` the same
holds at every interior point `-1 < t < 1`, with the same coefficients and the same order of
choice. The coefficients are one function `c : ℝ → ℝ` chosen before all data; the tail sum
`Σ_{j ≥ j₀}` is `∑' j, a (j + j₀)^q`. -/
def LacunaryLowerEnergyStatement : Prop :=
  ∃ c : ℝ → ℝ, (∀ q : ℝ, 0 < q → 0 < c q) ∧
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
      (∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ lacunaryInterval →
        ∀ t ∈ E ∩ Ioo (-1 : ℝ) 1, IsLebesgueDensityPoint E t →
        ∀ R : ℝ, 0 < R → ∃ j₀ : ℕ, ∀ q : ℝ, 0 < q →
          ENNReal.ofReal (c q * ε ^ q) * ∑' j, ENNReal.ofReal (a (j + j₀) ^ q) ≤
            energyT (lacunarySource ε a N E) 2 .mixed q R (lacunaryGraphMap ε a N t)) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 1, ∀ R : ℝ, 0 < R → ∃ j₀ : ℕ, ∀ q : ℝ, 0 < q →
          ENNReal.ofReal (c q * ε ^ q) * ∑' j, ENNReal.ofReal (a (j + j₀) ^ q) ≤
            energyT (lacunarySource ε a N lacunaryInterval) 2 .mixed q R
              (lacunaryGraphMap ε a N t))

/-- **Small slopes.** If `a_j → 0`, then for every `η > 0` the fixed graph `F(J)` is
covered by finitely many restrictions of full ordinary vertical graphs of slope at most `η`.
A restriction of a full graph is a subset of its image, so the cover is
`F(J) ⊆ ⋃_{ℓ < m} image(G_ℓ)` with `G_ℓ : OrdinaryVerticalGraph 1 2 η`; the cover is exact,
not modulo a null set. -/
def LacunarySmallSlopeStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    Tendsto a atTop (𝓝 0) →
    ∀ η : ℝ, 0 < η →
      ∃ (m : ℕ) (G : Fin m → OrdinaryVerticalGraph 1 2 η),
        lacunaryGraphMap ε a N '' lacunaryInterval ⊆ ⋃ ℓ, (G ℓ).image

/-- **The lacunary estimates.** The
conjunction of every displayed claim of the lemma: isometry, exact ball identity, Hausdorff
identity, density limit, full-interval regularity, upper and lower energy bounds, and small
slopes. -/
def LacunaryEstimatesStatement : Prop :=
  LacunaryIsometryStatement ∧ LacunaryBallMeasureStatement ∧ LacunaryHausdorffStatement ∧
    LacunaryDensityLimitStatement ∧ LacunaryFullIntervalStatement ∧
    LacunaryUpperEnergyStatement ∧ LacunaryLowerEnergyStatement ∧ LacunarySmallSlopeStatement

/-! ## The nonregular example -/

/-- **Nonregular example, qualitative part.** With `a_j = j^{-1/2}` (`nonregularAmplitude`), every admissible
`ε`, `N`:
* the single graph `F(J)` is compact;
* `0 < H_P²(F(J)) < ∞`;
* ordinary graph covers of every prescribed small slope: `IsOrdinarilyRectifiableSet 2 F(J)`;
* `S^R_{2,ν_J}(F(t)) = ∞` for `-1 < t < 1` and every `R > 0`;
* for every measurable `E ⊆ J` with `|E| > 0` and every `R > 0`, `S^R_{2,ν_E} = ∞`
  `ν_E`-almost everywhere;
* `ν_J(G) = 0` for every full general regular vertical graph `G` of arbitrary finite norm;
* no countable family of regular graphs (horizontal subset graphs and full general regular
  vertical graphs, each of its own finite slope or norm) covers `F(J)` modulo `H_P²`;
* `ν_J` is not regularly rectifiable (mixed family). -/
def NonregularQualitativeStatement : Prop :=
  ∀ (ε : ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData nonregularAmplitude N →
    IsCompact (lacunaryGraphMap ε nonregularAmplitude N '' lacunaryInterval) ∧
    0 < hausdorffP 1 2 (lacunaryGraphMap ε nonregularAmplitude N '' lacunaryInterval) ∧
    hausdorffP 1 2 (lacunaryGraphMap ε nonregularAmplitude N '' lacunaryInterval) < ⊤ ∧
    IsOrdinarilyRectifiableSet 2 (lacunaryGraphMap ε nonregularAmplitude N '' lacunaryInterval) ∧
    (∀ t ∈ Ioo (-1 : ℝ) 1, ∀ R : ℝ, 0 < R →
      squareEnergy (lacunarySource ε nonregularAmplitude N lacunaryInterval) 2 .mixed R
        (lacunaryGraphMap ε nonregularAmplitude N t) = ⊤) ∧
    (∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ lacunaryInterval → 0 < volume E →
      ∀ R : ℝ, 0 < R →
        ∀ᵐ z ∂(lacunarySource ε nonregularAmplitude N E),
          squareEnergy (lacunarySource ε nonregularAmplitude N E) 2 .mixed R z = ⊤) ∧
    (∀ (η : ℝ) (G : GeneralRegularVerticalGraph 1 2 η),
      lacunarySource ε nonregularAmplitude N lacunaryInterval G.image = 0) ∧
    ¬ (∃ (I I' : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph 1 2 (εH i))
        (εV : I' → ℝ) (V : ∀ j, GeneralRegularVerticalGraph 1 2 (εV j)),
        hausdorffP 1 2 (lacunaryGraphMap ε nonregularAmplitude N '' lacunaryInterval \
          ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)) = 0) ∧
    ¬ IsRegularlyRectifiableMeasure .mixed 2
        (lacunarySource ε nonregularAmplitude N lacunaryInterval)

/-- **The `T_p` bound for `p > 2`.** For every fixed `p > 2` there is `C_p > 0`, independent of `ε` and
`N`, with `sup_t T^∞_{p,ν_J}(F(t)) ≤ C_p ε^p`. -/
def NonregularUpperEnergyStatement : Prop :=
  ∀ p : ℝ, 2 < p → ∃ C : ℝ, 0 < C ∧
    ∀ (ε : ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData nonregularAmplitude N →
    ∀ t : ℝ,
      (⨆ R : ℝ, energyT (lacunarySource ε nonregularAmplitude N lacunaryInterval) 2 .mixed p R
          (lacunaryGraphMap ε nonregularAmplitude N t)) ≤ ENNReal.ofReal (C * ε ^ p)

/-- **The nonregular example:** ordinarily
rectifiable, but no regular graph cover. -/
def NonregularStatement : Prop :=
  NonregularQualitativeStatement ∧ NonregularUpperEnergyStatement

/-! ## Exponent witnesses -/

/-- **Exponent-free part for `p > 2`.** With `a_j = j^{-1/2}` and
`ν_ε = F_#(L¹⌊[-1/4,1/4])`: the support of `ν_ε` lies in `P(0,1)`, its mass is `1/2`, and every
countably regular carrier with a Hausdorff-null residual is `ν_ε`-null. A countably regular
carrier is a countable union of horizontal subset graphs and full general regular vertical
graphs, each of its own finite slope or norm; the residual `Z` has `H_P²(Z) = 0`. -/
def ExponentWitnessAboveCarrierStatement : Prop :=
  ∀ (ε : ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData nonregularAmplitude N →
    (lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4))).support ⊆
        Metric.ball (point 0 0) 1 ∧
    lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4)) univ = ENNReal.ofReal (1 / 2) ∧
    ∀ (I I' : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph 1 2 (εH i))
      (εV : I' → ℝ) (V : ∀ j, GeneralRegularVerticalGraph 1 2 (εV j)) (Z : Set (Space 1)),
      hausdorffP 1 2 Z = 0 →
        lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4))
          ((⋃ i, (H i).image) ∪ (⋃ j, (V j).image) ∪ Z) = 0

/-- **Energy part for `p > 2`.** For every `p > 2` there is
`C_p > 0`, independent of `ε` and `N`, with `sup_{supp ν_ε} T²_{p,ν_ε} ≤ C_p ε^p` and
`0 < ∫ T²_{p,ν_ε} dν_ε ≤ C_p ε^p / 2`. The superscript `2` is the scale endpoint. -/
def ExponentWitnessAboveEnergyStatement : Prop :=
  ∀ p : ℝ, 2 < p → ∃ C : ℝ, 0 < C ∧
    ∀ (ε : ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData nonregularAmplitude N →
      (∀ z ∈ (lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4))).support,
        energyT (lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4))) 2 .mixed p 2 z ≤
          ENNReal.ofReal (C * ε ^ p)) ∧
      0 < ∫⁻ z, energyT (lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4)))
          2 .mixed p 2 z ∂(lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4))) ∧
      ∫⁻ z, energyT (lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4)))
          2 .mixed p 2 z ∂(lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4))) ≤
        ENNReal.ofReal (C * ε ^ p / 2)

/-- **Exponents below `2`.** There is a universal `C > 0` such that for
every `c₀ > 0` with `a_j = c₀/(√j log(j+1)) ≤ 1` (`exponentAmplitude c₀`, the bound being part
of `IsLacunaryData`) and every admissible `ε`, `N`:
* `a ∈ ℓ²` and `a ∉ ℓ^p` for every `0 < p < 2`;
* the full function is general regular on the zero vertical base (`W = 0`, normal target
  `ℝ¹`; `f` read through `zeroBaseLift`): there are a representative `h` of its homogeneous
  half-time derivative and bounds `L`, `B` with `Lip_P f ≤ L ≤ C ε ‖a‖_∞` and
  `[h]_{BMO_P} ≤ B ≤ C ε ‖a‖₂`; this `h` is `2π`-periodic and is the periodic `L²` limit of
  the partial sums of `(2π)^{-1/2} ε Σ_j a_j cos(N_j t)`; consequently `f` is general regular
  with norm at most `C ε (‖a‖_∞ + ‖a‖₂)`;
* `T^R_{p,ν_J}(F(t)) = ∞` for every `0 < p < 2`, `R > 0` and `-1 < t < 1`.
Here `‖a‖_∞ = ⨆ j, a j` and `‖a‖₂ = √(Σ_j a_j²)` (a convergent sum, by the first clause). -/
def ExponentWitnessBelowStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ c₀ : ℝ, 0 < c₀ →
    ∀ (ε : ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData (exponentAmplitude c₀) N →
      Summable (fun j => exponentAmplitude c₀ j ^ 2) ∧
      (∀ p : ℝ, 0 < p → p < 2 → ¬ Summable (fun j => exponentAmplitude c₀ j ^ p)) ∧
      (∃ (h : ℝ → ℝ) (L B : ℝ≥0),
        LipschitzWith L (zeroBaseLift (lacunaryFunction ε (exponentAmplitude c₀) N)) ∧
        HasParabolicBMOBound zeroDirection (zeroBaseLift h) (B : ℝ) ∧
        RepresentsGeneralHalfTimeDerivative zeroDirection
          (zeroBaseLift (lacunaryFunction ε (exponentAmplitude c₀) N)) (zeroBaseLift h) ∧
        (L : ℝ) ≤ C * ε * ⨆ j, exponentAmplitude c₀ j ∧
        (B : ℝ) ≤ C * ε * Real.sqrt (∑' j, exponentAmplitude c₀ j ^ 2) ∧
        Function.Periodic h (2 * Real.pi) ∧
        Tendsto (fun m : ℕ => ∫⁻ t in Ioc 0 (2 * Real.pi),
            ENNReal.ofReal ((h t - (Real.sqrt (2 * Real.pi))⁻¹ * ε *
              ∑ j ∈ Finset.range m, exponentAmplitude c₀ j * Real.cos (N j * t)) ^ 2))
          atTop (𝓝 0)) ∧
      IsGeneralRegularVerticalFunction zeroDirection
        (zeroBaseLift (lacunaryFunction ε (exponentAmplitude c₀) N))
        (C * ε * ((⨆ j, exponentAmplitude c₀ j) +
          Real.sqrt (∑' j, exponentAmplitude c₀ j ^ 2))) ∧
      (∀ p : ℝ, 0 < p → p < 2 → ∀ R : ℝ, 0 < R → ∀ t ∈ Ioo (-1 : ℝ) 1,
        energyT (lacunarySource ε (exponentAmplitude c₀) N lacunaryInterval) 2 .mixed p R
          (lacunaryGraphMap ε (exponentAmplitude c₀) N t) = ⊤)

/-- **The exponent witnesses:** the
complementary exponent witnesses, `p > 2` and `p < 2`. -/
def ExponentWitnessesStatement : Prop :=
  ExponentWitnessAboveCarrierStatement ∧ ExponentWitnessAboveEnergyStatement ∧
    ExponentWitnessBelowStatement

end ParabolicRectifiability.Examples
