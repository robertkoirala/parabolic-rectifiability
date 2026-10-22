import ParabolicRectifiability.BetaP.Statements.Main
import ParabolicRectifiability.BetaP.Statements.Failures
import ParabolicRectifiability.Decomposition.Interfaces
import ParabolicRectifiability.Examples.Lacunary

/-! # Intermediate objects for the beta-`p` support theorem and its corollaries

Definitions only. These are the intermediate objects used in the proofs of the support theorem
and its corollaries (`exists_p_localization`, `exists_p_carrier`, `exists_assembled_p_decomposition`,
the direct witnesses, …), after the model of the interfaces of the weak theorem
(`HasMetricContentBounds`, `HasFiniteBallPacking`, …). None of them is a hypothesis of a public
statement.

* `BetaPUnitClause`, `BetaPLocalizedClause`, `BetaPAmbientClause` are the three conjuncts of the
  conclusion of `BetaPSupportStatement`, copied verbatim; `betaPSupportStatement_iff` checks the
  unfolding by `Iff.rfl`.
* The five `ActiveRadiusPacking…Bound n p C` are the bodies of the five packing statements after
  their constant, copied verbatim; the `…_iff` lemmas check the unfolding by `Iff.rfl`.
* `allScaleEnergyP` is the all-scale quadratic beta-`p` energy `∫_0^∞ β_p^2 ds/s`;
  `pGoodSet` is the good set `P(0,1) ∩ {S_p^2 ≤ M}`.
* `PLocalization`, `PCarrier`, `TypedSplit` are the outputs of small-diameter localization,
  of the `p`-carrier construction and of the Borel typing with the null residual assigned.
* Interfaces for the corollaries (direct witnesses, classification, failures):
  `IsBelowTwoDigitWitness` is the conjunction of the planar conclusions of the digit witness that
  the elementary digit construction proves before any rectifiability input;
  `directWitnessMinusStatement_iff` (proved) splits `DirectWitnessMinusStatement` into these
  conclusions, pure unrectifiability and graph-intersection nullity. `LacunaryFrequencyExistence`
  is the existence of admissible lacunary frequencies.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## The three clauses of the support theorem -/

/-- The unit clause of `BetaPSupportStatement` for one family `T`, constant `C` and source `μ`. -/
def BetaPUnitClause {n : ℕ} (k : ℕ) (T : FamilyKind) (p C : ℝ) (μ : Measure (Space n)) : Prop :=
  ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
    (2 ≤ p →
      μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyS μ k T p 2 z}) ≤
        ENNReal.ofReal Γ →
      ∃ μplus μH μV : Measure (Space n),
        IsBetaPDecomposition k T C (point 0 0) 1 (C * M ^ (p / 2) + Γ) μ μplus μH μV) ∧
    (p ≤ 2 →
      μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyT μ k T p 2 z}) ≤
        ENNReal.ofReal Γ →
      ∃ μplus μH μV : Measure (Space n),
        IsBetaPDecomposition k T C (point 0 0) 1 (C * M + Γ) μ μplus μH μV)

/-- The localized clause of `BetaPSupportStatement`. -/
def BetaPLocalizedClause {n : ℕ} (k : ℕ) (T : FamilyKind) (p C : ℝ) (μ : Measure (Space n)) :
    Prop :=
  ∀ (q : Space n) (R₀ : ℝ), 0 < R₀ → ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
    (2 ≤ p →
      μ (Metric.ball q R₀ ∩ {z | ENNReal.ofReal M < energyS μ k T p (2 * R₀) z}) ≤
        ENNReal.ofReal Γ →
      ∃ μplus μH μV : Measure (Space n),
        IsBetaPDecomposition k T C q R₀ (C * M ^ (p / 2) * R₀ ^ k + Γ) μ μplus μH μV) ∧
    (p ≤ 2 →
      μ (Metric.ball q R₀ ∩ {z | ENNReal.ofReal M < energyT μ k T p (2 * R₀) z}) ≤
        ENNReal.ofReal Γ →
      ∃ μplus μH μV : Measure (Space n),
        IsBetaPDecomposition k T C q R₀ (C * M * R₀ ^ k + Γ) μ μplus μH μV)

/-- The ambient clause of `BetaPSupportStatement`. -/
def BetaPAmbientClause {n : ℕ} (k : ℕ) (T : FamilyKind) (C : ℝ) (μ : Measure (Space n)) : Prop :=
  k = n + 2 →
    ∃ μplus μH μV : Measure (Space n),
      IsBetaPDecomposition k T C (point 0 0) 1 0 μ μplus μH μV

/-- The three clause predicates unfold `BetaPSupportStatement` definitionally. -/
theorem betaPSupportStatement_iff : BetaPSupportStatement ↔
    ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
        BetaPUnitClause k T p C μ ∧ BetaPLocalizedClause k T p C μ ∧ BetaPAmbientClause k T C μ :=
  Iff.rfl

/-! ## The five active-radius packing bounds for a fixed constant -/

/-- Body of `ActiveRadiusPackingStatement` for the constant `C`. -/
def ActiveRadiusPackingBound (n : ℕ) (p C : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ (q : Space n) (R : ℝ), 0 < R →
    ∀ (N : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (b B : ℝ),
      IsWeightedPacking q R z r w b → 0 ≤ B →
      (∀ i, (∫⁻ s in Ioi (r i),
          betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure) ≤
        ENNReal.ofReal B) →
      atomicSource k z r w univ ≤ ENNReal.ofReal (C * (b + B ^ (p / 2)) * R ^ k)

/-- Body of `ActiveRadiusPackingTruncatedStatement` for the constant `C`. -/
def ActiveRadiusPackingTruncatedBound (n : ℕ) (p C : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ (q : Space n) (R : ℝ), 0 < R →
    ∀ (N : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (b B : ℝ),
      IsWeightedPacking q R z r w b → 0 ≤ B →
      (∀ i, (∫⁻ s in Ioi (r i),
          betaPow (truncatedAtomicSource k z r w s) k T p (z i) s ^ (2 / p) ∂scaleMeasure) ≤
        ENNReal.ofReal B) →
      atomicSource k z r w univ ≤ ENNReal.ofReal (C * (b + B ^ (p / 2)) * R ^ k)

/-- Body of `ActiveRadiusPackingUnitParentStatement` for the constant `C`. -/
def ActiveRadiusPackingUnitParentBound (n : ℕ) (p C : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ q : Space n,
    ∀ (N : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (b B : ℝ),
      IsWeightedPacking q 1 z r w b → 0 ≤ B →
      (∀ i, (∫⁻ s in Ioo (r i) 2,
          betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure) ≤
        ENNReal.ofReal B) →
      atomicSource k z r w univ ≤ ENNReal.ofReal (C * (b + B ^ (p / 2)))

/-- Body of `ActiveRadiusPackingExceptionalStatement` for the constant `C`. -/
def ActiveRadiusPackingExceptionalBound (n : ℕ) (p C : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ (q : Space n) (R : ℝ), 0 < R →
    ∀ (N : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (b B : ℝ),
      IsWeightedPacking q R z r w b → 0 ≤ B →
    ∀ (E : Finset (Fin N)) (Γ : ℝ), (∑ i ∈ E, w i * r i ^ k) ≤ Γ →
      (∀ i, i ∉ E → (∫⁻ s in Ioi (r i),
          betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure) ≤
        ENNReal.ofReal B) →
      atomicSource k z r w univ ≤ ENNReal.ofReal (C * (b + B ^ (p / 2)) * R ^ k + Γ)

/-- Body of `ActiveRadiusPackingUnitParentExceptionalStatement` for the constant `C`. -/
def ActiveRadiusPackingUnitParentExceptionalBound (n : ℕ) (p C : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ q : Space n,
    ∀ (N : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (b B : ℝ),
      IsWeightedPacking q 1 z r w b → 0 ≤ B →
    ∀ (E : Finset (Fin N)) (Γ : ℝ), (∑ i ∈ E, w i * r i ^ k) ≤ Γ →
      (∀ i, i ∉ E → (∫⁻ s in Ioo (r i) 2,
          betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure) ≤
        ENNReal.ofReal B) →
      atomicSource k z r w univ ≤ ENNReal.ofReal (C * (b + B ^ (p / 2)) + Γ)

theorem activeRadiusPackingStatement_iff : ActiveRadiusPackingStatement ↔
    ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧ ActiveRadiusPackingBound n p C :=
  Iff.rfl

theorem activeRadiusPackingTruncatedStatement_iff : ActiveRadiusPackingTruncatedStatement ↔
    ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧ ActiveRadiusPackingTruncatedBound n p C :=
  Iff.rfl

theorem activeRadiusPackingUnitParentStatement_iff : ActiveRadiusPackingUnitParentStatement ↔
    ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧ ActiveRadiusPackingUnitParentBound n p C :=
  Iff.rfl

theorem activeRadiusPackingExceptionalStatement_iff : ActiveRadiusPackingExceptionalStatement ↔
    ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧ ActiveRadiusPackingExceptionalBound n p C :=
  Iff.rfl

theorem activeRadiusPackingUnitParentExceptionalStatement_iff :
    ActiveRadiusPackingUnitParentExceptionalStatement ↔
    ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧
      ActiveRadiusPackingUnitParentExceptionalBound n p C :=
  Iff.rfl

/-! ## Localization, carrier and typing interfaces for the positive `S_p` branch -/

/-- The all-scale quadratic beta-`p` energy `∫_0^∞ β_{p,ν}(z,s)^2 ds/s`, with
`β_p^2 = B_p^{2/p}`. -/
def allScaleEnergyP {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p : ℝ)
    (z : Space n) : ℝ≥0∞ :=
  ∫⁻ s in Ioi 0, betaPow ν k T p z s ^ (2 / p) ∂scaleMeasure

/-- The `S_p` good points of the unit ball: `P(0,1) ∩ {S_{p,μ,T}^2 ≤ M}`. Its complement in
`P(0,1)` is exactly the threshold set `P(0,1) ∩ {S_{p,μ,T}^2 > M}` of the support theorem. -/
def pGoodSet {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p M : ℝ) :
    Set (Space n) :=
  Metric.ball (point 0 0) 1 ∩ {z | energyS μ k T p 2 z ≤ ENNReal.ofReal M}

/-- Small-diameter localization of the `S_p` good source: at most `N` disjoint Borel pieces
partitioning the good set, each an actual restriction of `μ`, finite and inner regular, with
support in a closed parabolic ball of radius `1/64`, and with the all-scale `S_p` bound `2M`
almost everywhere for the restricted source itself (`L = M/(1-2^{-q_p}) ≤ 2M`). -/
structure PLocalization {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p M : ℝ)
    (N : ℕ) where
  count : ℕ
  count_le : count ≤ N
  region : Fin count → Set (Space n)
  measurable : ∀ i, MeasurableSet (region i)
  disjoint : ∀ i j, i ≠ j → Disjoint (region i) (region j)
  cover : (⋃ i, region i) = pGoodSet μ k T p M
  center : Fin count → Space n
  support_small : ∀ i, (μ.restrict (region i)).support ⊆ Metric.closedBall (center i) (1 / 64)
  finite : ∀ i, IsFiniteMeasure (μ.restrict (region i))
  innerRegular : ∀ i, (μ.restrict (region i)).InnerRegular
  energy : ∀ i, ∀ᵐ z ∂μ.restrict (region i),
    allScaleEnergyP (μ.restrict (region i)) k T p z ≤ ENNReal.ofReal (2 * M)

/-- The compact `p`-carrier of one localized source (with `a = L^{p/2}`, `L = 2M`): a compact
subset of the actual support losing at most `C M^{p/2}` of the source, with the equal-radius
content bounds and finite variable-radius packing at every scale `≤ 1`, and finite own-Hausdorff
square for `η = H_P^k⌊K` with the same family `T` almost everywhere (by domination and Hölder
with the proved upper growth of `η`). The growth and regularity are statements about `η`, never hypotheses on `ν`. -/
structure PCarrier {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p M C : ℝ) where
  set : Set (Space n)
  compact : IsCompact set
  subset_support : set ⊆ ν.support
  loss : ν setᶜ ≤ ENNReal.ofReal (C * M ^ (p / 2))
  content : HasMetricContentBounds k C set
  packing : HasFiniteBallPacking k C set
  energy : ∀ᵐ z ∂(hausdorffP n k).restrict set,
    squareEnergy ((hausdorffP n k).restrict set) k T 1 z < ⊤

/-- A Borel typing of `K`, fixed before every tolerance, with the Hausdorff-null residual
already assigned to an available type: disjoint Borel
pieces whose union is `K`, empty for an unavailable or disallowed type, each with countable
own-type covers modulo `H_P^k` at every positive tolerance (vertical covers in the general
regular class). -/
structure TypedSplit {n : ℕ} (k : ℕ) (T : FamilyKind) (K : Set (Space n)) where
  horizontal : Set (Space n)
  vertical : Set (Space n)
  measurable_horizontal : MeasurableSet horizontal
  measurable_vertical : MeasurableSet vertical
  disjoint : Disjoint horizontal vertical
  union_eq : horizontal ∪ vertical = K
  horizontal_unavailable : ¬ (1 ≤ k ∧ k ≤ n) → horizontal = ∅
  vertical_unavailable : ¬ (2 ≤ k ∧ k ≤ n + 2) → vertical = ∅
  family : RespectsFamily T horizontal vertical
  horizontal_graphs : ∀ ε : ℝ, 0 < ε → HasHorizontalGraphCover k horizontal ε
  vertical_graphs : ∀ ε : ℝ, 0 < ε → HasGeneralRegularVerticalGraphCover k vertical ε

/-! ## Interfaces for the corollaries -/

/-- The planar conclusions of the digit witness below two, for `λ = H¹⌊E`. The
digit construction proves them without any rectifiability criterion:
* `E` is compact and `H¹(E) = 1`;
* at every point of `E` the planar upper one-density of `λ` lies in `[1/2, 2]`;
* for `0 < p < 2` and `a > 0`, `S_{p,λ}^{a,E}` is bounded on `E` by a constant depending on `p`
  and `a` only;
* on one common set `G` of full `λ`-measure, `S_{2,λ}^{a,E} = ∞` for every `a > 0` and the
  planar lower one-density of `λ` vanishes.
Each clause is the corresponding conjunct of `DirectWitnessMinusStatement`. Its two
remaining conjuncts, pure unrectifiability and graph-intersection nullity, come from graph
necessity. -/
def IsBelowTwoDigitWitness (E : Set Plane) : Prop :=
  IsCompact E ∧ μH[1] E = 1 ∧
    (∀ z ∈ E, (2 : ℝ≥0∞)⁻¹ ≤ planarUpperDensity (μH[1].restrict E) z ∧
      planarUpperDensity (μH[1].restrict E) z ≤ 2) ∧
    (∀ p : ℝ, 0 < p → p < 2 → ∀ a : ℝ, 0 < a →
      ∃ B : ℝ, ∀ z ∈ E, euclideanEnergyS (μH[1].restrict E) 1 p a z ≤ ENNReal.ofReal B) ∧
    (∃ G : Set Plane, μH[1].restrict E Gᶜ = 0 ∧
      ∀ z ∈ G, (∀ a : ℝ, 0 < a → euclideanEnergyS (μH[1].restrict E) 1 2 a z = ⊤) ∧
        planarLowerDensity (μH[1].restrict E) z = 0)

/-- `DirectWitnessMinusStatement` is exactly the planar conclusions of the digit witness together with
pure unrectifiability and graph-intersection nullity: a reordering of its conjuncts. -/
theorem directWitnessMinusStatement_iff : DirectWitnessMinusStatement ↔
    ∃ E : Set Plane, IsBelowTwoDigitWitness E ∧ IsPurelyUnrectifiable E ∧
      ∀ (ε : ℝ) (G : HorizontalGraph 2 1 ε), hausdorffP 2 1 (timeSlice '' E ∩ G.image) = 0 := by
  constructor
  · rintro ⟨E, hc, hm, hp, hd, hS, hG, hn⟩
    exact ⟨E, ⟨hc, hm, hd, hS, hG⟩, hp, hn⟩
  · rintro ⟨E, ⟨hc, hm, hd, hS, hG⟩, hp, hn⟩
    exact ⟨E, hc, hm, hp, hd, hS, hG, hn⟩

/-- Existence of admissible lacunary frequencies: for every amplitude sequence with
`0 < a_j ≤ 1` there are frequencies `N` with `IsLacunaryData a N` (the standing hypotheses of the
lacunary examples). Every lacunary statement of `Examples` is conditional on `IsLacunaryData`,
and none of them produces the frequencies. -/
def LacunaryFrequencyExistence : Prop :=
  ∀ a : ℕ → ℝ, (∀ j, 0 < a j) → (∀ j, a j ≤ 1) → ∃ N : ℕ → ℕ, Examples.IsLacunaryData a N

end ParabolicRectifiability.BetaP
