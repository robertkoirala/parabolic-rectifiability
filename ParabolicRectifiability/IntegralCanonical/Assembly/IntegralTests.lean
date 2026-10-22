import ParabolicRectifiability.IntegralCanonical.Assembly.MeasureHelpers
import ParabolicRectifiability.IntegralCanonical.Assembly.IntegralForwardDirections
import ParabolicRectifiability.IntegralCanonical.Statements.Integral
import ParabolicRectifiability.Characterization.Statements.Main

/-! # The exact integral tests and the integral characterization

Assembly of the proof of
* `integralEquivalences_skeleton : IntegralEquivalencesStatement`, from the forward
  directions in `tendsto_cappedTail_cappedValue_measure_infinite`,
  `compactExhaustionTest_of_ae_lt_top`, `positiveWeightTest_of_ae_lt_top` and
  `adaptiveGaugeTest_of_ae_lt_top`;
* `integralCriterion_of_providers : QualitativeCharacterizationStatement →
  IntegralCriterionStatement`, composing the qualitative characterization (taken as a hypothesis) with the
  endpoint-general equivalences `integralEquivalences_at`.

The assembly carries out:
* cylinder detection and the reduced testing on `P(0,j)`, `j ≥ 1`, by uniqueness of limits
  and countable exhaustion;
* the converse halves of the compact exhaustion, positive weight and adaptive gauge tests
  (a finite integral of a function infinite on `{S = ∞}` makes that set null);
* the endpoint change of the criterion: the forward directions are stated at every positive
  endpoint, so the equivalences hold at every endpoint and `R = 1` is one instance;
* the matching of the structural conditions (a), (b), (c) with conditions (2), (3), (4) of
  the qualitative characterization, and the consequences (density improvement and covers) from its consequence
  clause.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

variable {n : ℕ}

/-- A bounded cylinder is a bounded Borel set. -/
theorem measurableSet_and_isBounded_of_mem_boundedCylinders {A : Set (Space n)}
    (hA : A ∈ boundedCylinders n) : MeasurableSet A ∧ Bornology.IsBounded A := by
  obtain ⟨z, r, -, rfl⟩ := hA
  exact ⟨measurableSet_ball, Metric.isBounded_ball⟩

/-- The reduced family `P(0,j)`, `j ≥ 1`, consists of bounded cylinders. -/
theorem originCylinders_subset_boundedCylinders (n : ℕ) :
    originCylinders n ⊆ boundedCylinders n := by
  rintro A ⟨j, hj, rfl⟩
  exact ⟨point 0 0, j, by exact_mod_cast hj, rfl⟩

/-- Each test is antitone in the family of tested sets. -/
theorem integralTest_anti {j : Fin 5} {μ : Measure (Space n)} {k : ℕ} {T : FamilyKind}
    {R : ℝ} {𝒜 ℬ : Set (Set (Space n))} (h : 𝒜 ⊆ ℬ) :
    IntegralTest j μ k T R ℬ → IntegralTest j μ k T R 𝒜 := by
  fin_cases j
  · exact fun hB A hA => hB A (h hA)
  · exact fun hB A hA => hB A (h hA)
  · exact id
  · rintro ⟨w, hw, hpos, hint⟩
    exact ⟨w, hw, hpos, fun A hA => hint A (h hA)⟩
  · exact fun hB A hA => hB A (h hA)

/-- Countable exhaustion by the cylinders `P(0,m)`, `m ≥ 1`: a set that meets each of them
in a null set is null. -/
theorem measure_eq_zero_of_originCylinders {μ : Measure (Space n)} {N : Set (Space n)}
    (h : ∀ m : ℕ, 1 ≤ m → μ (Metric.ball (point 0 0 : Space n) (m : ℝ) ∩ N) = 0) :
    μ N = 0 := by
  have hsub : N ⊆ ⋃ m : ℕ, Metric.ball (point 0 0 : Space n) ((m + 1 : ℕ) : ℝ) ∩ N := by
    intro z hz
    obtain ⟨m, hm⟩ := exists_nat_gt (dist z (point 0 0 : Space n))
    refine mem_iUnion.2 ⟨m, ?_, hz⟩
    rw [Metric.mem_ball]
    push_cast
    linarith
  exact measure_mono_null hsub (measure_iUnion_null fun m => h (m + 1) (Nat.le_add_left 1 m))

/-- **Endpoint-general exact integral tests.** The three clauses of the integral
equivalences at an arbitrary positive finite endpoint `R`, from the forward directions of
the limits, compact exhaustion, positive weight and adaptive gauge. The case `R = 1` is
`IntegralEquivalencesStatement`; the general case is the endpoint change used by the
criterion. -/
theorem integralEquivalences_at (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (μ : Measure (Space n)) (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (T : FamilyKind) (hT : Nonempty (Models n k T)) {R : ℝ} (hR : 0 < R) :
    (∀ A : Set (Space n), MeasurableSet A → Bornology.IsBounded A →
      Tendsto (fun ρ : ℝ => ∫⁻ z in A, min 1 (squareEnergy μ k T ρ z) ∂μ) (𝓝[>] 0)
          (𝓝 (μ (A ∩ {z | squareEnergy μ k T R z = ⊤}))) ∧
        Tendsto (fun L : ℝ =>
            (ENNReal.ofReal L)⁻¹ *
              ∫⁻ z in A, min (squareEnergy μ k T R z) (ENNReal.ofReal L) ∂μ)
          atTop (𝓝 (μ (A ∩ {z | squareEnergy μ k T R z = ⊤})))) ∧
    (∀ j : Fin 5,
      (∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) ↔ IntegralTest j μ k T R (boundedCylinders n)) ∧
    (∀ j : Fin 5, j ≠ 2 →
      IntegralTest j μ k T R (originCylinders n) → ∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) := by
  have := hμ
  have hN : MeasurableSet {z | squareEnergy μ k T R z = ⊤} :=
    measurableSet_squareEnergy_eq_top μ k T R
  have hlim := tendsto_cappedTail_cappedValue_measure_infinite n hn k hk hkn μ hμ hreg T hT R hR
  have hae := ae_squareEnergy_lt_top_iff μ k T R
  -- reduced testing on `P(0,m)`, `m ≥ 1`
  have hred : ∀ j : Fin 5, j ≠ 2 →
      IntegralTest j μ k T R (originCylinders n) → ∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤ := by
    intro j hj htest
    rw [hae]
    apply measure_eq_zero_of_originCylinders
    intro m hm
    have hA : Metric.ball (point 0 0 : Space n) (m : ℝ) ∈ originCylinders n := ⟨m, hm, rfl⟩
    obtain ⟨hAm, hAb⟩ :=
      measurableSet_and_isBounded_of_mem_boundedCylinders (originCylinders_subset_boundedCylinders n hA)
    fin_cases j
    · exact tendsto_nhds_unique (hlim _ hAm hAb).1 (htest _ hA)
    · exact tendsto_nhds_unique (hlim _ hAm hAb).2 (htest _ hA)
    · exact absurd rfl hj
    · obtain ⟨w, -, hpos, hint⟩ := htest
      refine measure_inter_eq_zero_of_setLIntegral_lt_top hN (hint _ hA) fun z hz => ?_
      rw [show squareEnergy μ k T R z = ⊤ from hz]
      exact ENNReal.mul_top (ENNReal.ofReal_pos.2 (hpos z).1).ne'
    · obtain ⟨Φ, -, hint⟩ := htest _ hA
      refine measure_inter_eq_zero_of_setLIntegral_lt_top hN hint fun z hz => ?_
      rw [show squareEnergy μ k T R z = ⊤ from hz]
      simp [extendedGauge]
  refine ⟨hlim, fun j => ?_, hred⟩
  fin_cases j
  · -- test (1): the vanishing capped tail
    constructor
    · intro hfin A hA
      obtain ⟨hAm, hAb⟩ := measurableSet_and_isBounded_of_mem_boundedCylinders hA
      have h0 : μ (A ∩ {z | squareEnergy μ k T R z = ⊤}) = 0 :=
        measure_mono_null inter_subset_right (hae.1 hfin)
      have h1 := (hlim A hAm hAb).1
      rwa [h0] at h1
    · intro htest
      exact hred 0 (by decide) (integralTest_anti (originCylinders_subset_boundedCylinders n) htest)
  · -- test (2): the vanishing normalized capped energy
    constructor
    · intro hfin A hA
      obtain ⟨hAm, hAb⟩ := measurableSet_and_isBounded_of_mem_boundedCylinders hA
      have h0 : μ (A ∩ {z | squareEnergy μ k T R z = ⊤}) = 0 :=
        measure_mono_null inter_subset_right (hae.1 hfin)
      have h1 := (hlim A hAm hAb).2
      rwa [h0] at h1
    · intro htest
      exact hred 1 (by decide) (integralTest_anti (originCylinders_subset_boundedCylinders n) htest)
  · -- test (3): the compact integrable exhaustion
    constructor
    · exact compactExhaustionTest_of_ae_lt_top n hn k hk hkn μ hμ hreg T hT R hR
    · rintro ⟨K, -, -, hcov, hint⟩
      rw [hae]
      refine measure_eq_zero_of_cover K (measure_mono_null inter_subset_right hcov) fun j => ?_
      exact measure_inter_eq_zero_of_setLIntegral_lt_top hN (hint j) fun _ hz => hz
  · -- test (4): the strictly positive weight
    constructor
    · intro hfin
      obtain ⟨w, hw, hpos, hint⟩ :=
        positiveWeightTest_of_ae_lt_top n hn k hk hkn μ hμ hreg T hT R hR hfin
      exact ⟨w, hw, hpos, fun A hA => hint A (measurableSet_and_isBounded_of_mem_boundedCylinders hA)⟩
    · intro htest
      exact hred 3 (by decide) (integralTest_anti (originCylinders_subset_boundedCylinders n) htest)
  · -- test (5): the adaptive concave gauge
    constructor
    · intro hfin A hA
      exact adaptiveGaugeTest_of_ae_lt_top n hn k hk hkn μ hμ hreg T hT R hR hfin A
        (measurableSet_and_isBounded_of_mem_boundedCylinders hA)
    · intro htest
      exact hred 4 (by decide) (integralTest_anti (originCylinders_subset_boundedCylinders n) htest)

/-- **The exact integral tests**, from the forward directions through
`integralEquivalences_at` at the endpoint `1`. -/
theorem integralEquivalences_skeleton : IntegralEquivalencesStatement :=
  fun _ hn _ hk hkn μ hμ hreg T hT => integralEquivalences_at hn hk hkn μ hμ hreg T hT one_pos

/-- **The integral criterion**, in implication form, from the qualitative characterization
(`Characterization.QualitativeCharacterizationStatement`) and the endpoint-general integral
tests `integralEquivalences_at`.

For each endpoint `R > 0` and structural condition `i`, the qualitative characterization gives
`μ` regularly rectifiable `↔` (condition `i`) `∧ S^R_{μ,T} < ∞` a.e.: (a), (b), (c) are the
density or source parts of conditions (2), (3), (4), with "every endpoint" for the forward
direction and "one endpoint" for the converse. The integral tests then replace the a.e.
finiteness at the same endpoint. The consequences are the consequence clause of Main
theorem 2. The ambient endpoint `k = n + 2` needs no separate branch: the qualitative characterization and the
integral tests include it. -/
theorem integralCriterion_of_providers
    (hMT2 : Characterization.QualitativeCharacterizationStatement) :
    IntegralCriterionStatement := by
  intro n hn k hk hkn μ hμ hreg T hT i j
  obtain ⟨h2one, h2every, h3one, h3every, h4one, h4every, hcons, -⟩ :=
    hMT2 n hn k hk hkn T hT μ hμ hreg
  have key : ∀ R : ℝ, 0 < R → (IsRegularlyRectifiableMeasure T k μ ↔
      StructuralCondition i k μ ∧ ∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) := by
    intro R hR
    fin_cases i
    · show _ ↔ (∀ᵐ z ∂μ, 0 < upperDensity μ k z ∧ lowerDensity μ k z < ⊤) ∧ _
      constructor
      · intro h
        have hall := h2every.1 h R hR
        exact ⟨hall.mono fun _ hz => hz.2, hall.mono fun _ hz => hz.1⟩
      · rintro ⟨hs, hf⟩
        exact h2one.2 ⟨R, hR, hf.and hs⟩
    · show _ ↔ (∀ᵐ z ∂μ, 0 < upperDensity μ k z ∧ upperDensity μ k z < ⊤) ∧ _
      constructor
      · intro h
        have hall := h3every.1 h R hR
        exact ⟨hall.mono fun _ hz => hz.2, hall.mono fun _ hz => hz.1⟩
      · rintro ⟨hs, hf⟩
        exact h3one.2 ⟨R, hR, hf.and hs⟩
    · show _ ↔ (μ ≪ hausdorffP n k ∧ HasBorelSigmaFiniteHausdorffCarrier k μ) ∧ _
      constructor
      · intro h
        obtain ⟨hac, hcar, hall⟩ := h4every.1 h
        exact ⟨⟨hac, hcar⟩, hall R hR⟩
      · rintro ⟨⟨hac, hcar⟩, hf⟩
        exact h4one.2 ⟨hac, hcar, R, hR, hf⟩
  have heq := fun (R : ℝ) (hR : 0 < R) => integralEquivalences_at hn hk hkn μ hμ hreg T hT hR
  refine ⟨fun R hR => ?_, ?_, fun R hR hj hs ht => ?_, fun R hR hs ht => ?_⟩
  · rw [key R hR, (heq R hR).2.1 j]
  · constructor
    · intro h
      exact ⟨((key 1 one_pos).1 h).1, fun R hR => ((heq R hR).2.1 j).1 ((key R hR).1 h).2⟩
    · rintro ⟨hs, ht⟩
      exact (key 1 one_pos).2 ⟨hs, ((heq 1 one_pos).2.1 j).2 (ht 1 one_pos)⟩
  · exact (key R hR).2 ⟨hs, (heq R hR).2.2 j hj ht⟩
  · exact hcons ((key R hR).2 ⟨hs, ((heq R hR).2.1 j).2 ht⟩)

end ParabolicRectifiability.IntegralCanonical
