import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.IntegralAuxiliaryResults
import ParabolicRectifiability.Foundations.Proofs.SquareEnergyBounds

/-! # The integral tests from finiteness of the square energy

Proves the four integral-test statements of the integral characterization, each with the same
type as the corresponding statement in the integral characterization:

* `i2_tendsto_cappedTail_cappedValue_measure_infinite`: on a bounded Borel set the capped tail
  and capped value integrals both converge to `μ(A ∩ {S^R = ∞})`
  (cf. `tendsto_cappedTail_cappedValue_measure_infinite`);
* `i2_compactExhaustionTest_of_ae_lt_top`, `i2_positiveWeightTest_of_ae_lt_top`,
  `i2_adaptiveGaugeTest_of_ae_lt_top`: if `S^R < ∞` a.e., then the compact-exhaustion,
  positive-weight and adaptive-gauge tests hold.

The proofs combine the seven intermediate results `i2_tail_vanishing`, `i2_cappedTail_limit`,
`i2_cappedValue_limit`, `i2_compactExhaustion`, `i2_positiveWeight`,
`i2_gaugeSeries_admissible` and `i2_gaugeSeries_integral`
with `squareEnergy_lt_top_iff_of_endpoints_proof`, which supplies the infinite branch of the
pointwise tail alternative (if `S^R(z) = ∞` then `S^ρ(z) = ∞` for every `ρ > 0`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

/-- The pointwise tail alternative:
`min{1, S^ρ(z)} → 1_{S^R = ∞}(z)` as `ρ ↓ 0`, at every point. Finite branch:
`i2_tail_vanishing`. Infinite branch: `squareEnergy_lt_top_iff_of_endpoints_proof`
(finiteness of the square energy does not depend on the endpoint). -/
theorem i2_tendsto_min_one_tail {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (μ : Measure (Space n)) (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (T : FamilyKind) (hT : Nonempty (Models n k T)) {R : ℝ} (hR : 0 < R) (z : Space n) :
    Tendsto (fun ρ : ℝ => min 1 (squareEnergy μ k T ρ z)) (𝓝[>] 0)
      (𝓝 ({z | squareEnergy μ k T R z = ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) z)) := by
  by_cases hz : squareEnergy μ k T R z = ⊤
  · have hind : {z | squareEnergy μ k T R z = ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) z = 1 :=
      Set.indicator_of_mem (show z ∈ {z | squareEnergy μ k T R z = ⊤} from hz) _
    rw [hind]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have h := squareEnergy_lt_top_iff_of_endpoints_proof n hn k hk hkn T μ hμ hreg z ρ R hρ hR
    have hρtop : squareEnergy μ k T ρ z = ⊤ := by
      by_contra hne
      exact (lt_top_iff_ne_top.1 (h.1 (lt_top_iff_ne_top.2 hne))) hz
    show (1 : ℝ≥0∞) = min 1 (squareEnergy μ k T ρ z)
    rw [hρtop, min_eq_left le_top]
  · have hind : {z | squareEnergy μ k T R z = ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) z = 0 :=
      Set.indicator_of_notMem (show z ∉ {z | squareEnergy μ k T R z = ⊤} from hz) _
    rw [hind]
    have h0 := i2_tail_vanishing n hn k hk hkn μ hμ hreg T hT R hR z (lt_top_iff_ne_top.2 hz)
    have h1 : Tendsto (fun ρ : ℝ => min 1 (squareEnergy μ k T ρ z)) (𝓝[>] 0)
        (𝓝 (min 1 0)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ≥0∞)) (𝓝[>] 0) (𝓝 1)).min h0
    rwa [min_eq_right (zero_le_one : (0 : ℝ≥0∞) ≤ 1)] at h1

/-- **Capped limits.** On a bounded Borel set `A`, `∫_A min{1, S^ρ} dμ → μ(A ∩ {S^R = ∞})` as
`ρ ↓ 0` and `L⁻¹ ∫_A min{S^R, L} dμ → μ(A ∩ {S^R = ∞})` as `L → ∞`. Uses
`i2_tendsto_min_one_tail`, `i2_cappedTail_limit` and `i2_cappedValue_limit`. -/
theorem i2_tendsto_cappedTail_cappedValue_measure_infinite :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ R : ℝ, 0 < R →
    ∀ A : Set (Space n), MeasurableSet A → Bornology.IsBounded A →
      Tendsto (fun ρ : ℝ => ∫⁻ z in A, min 1 (squareEnergy μ k T ρ z) ∂μ) (𝓝[>] 0)
          (𝓝 (μ (A ∩ {z | squareEnergy μ k T R z = ⊤}))) ∧
        Tendsto (fun L : ℝ =>
            (ENNReal.ofReal L)⁻¹ *
              ∫⁻ z in A, min (squareEnergy μ k T R z) (ENNReal.ofReal L) ∂μ)
          atTop (𝓝 (μ (A ∩ {z | squareEnergy μ k T R z = ⊤}))) := by
  intro n hn k hk hkn μ hμ hreg T hT R hR A hAm hAb
  exact ⟨i2_cappedTail_limit n hn k hk hkn μ hμ hreg T hT R hR A hAm hAb
      (i2_tendsto_min_one_tail hn hk hkn μ hμ hreg T hT hR),
    i2_cappedValue_limit n hn k hk hkn μ hμ hreg T hT R hR A hAm hAb⟩

/-- **Compact exhaustion.** `S^R < ∞` a.e. gives the compact-exhaustion test; this is
`i2_compactExhaustion`. -/
theorem i2_compactExhaustionTest_of_ae_lt_top :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ R : ℝ, 0 < R →
      (∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) → CompactExhaustionTest μ k T R :=
  i2_compactExhaustion

/-- **Positive weight.** `S^R < ∞` a.e. gives the positive-weight test on bounded Borel
sets; this is `i2_positiveWeight`. -/
theorem i2_positiveWeightTest_of_ae_lt_top :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ R : ℝ, 0 < R →
      (∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) →
        PositiveWeightTest μ k T R {A | MeasurableSet A ∧ Bornology.IsBounded A} :=
  i2_positiveWeight

/-- **Adaptive gauge.** `S^R < ∞` a.e. gives the adaptive-gauge test on bounded Borel sets:
`i2_gaugeSeries_integral` supplies a positive sequence with summable reciprocals whose gauge
series has finite integral on `A`, and `i2_gaugeSeries_admissible` shows that this gauge series
is admissible. The gauge depends on `μ` and `A`. -/
theorem i2_adaptiveGaugeTest_of_ae_lt_top :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ R : ℝ, 0 < R →
      (∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) →
        AdaptiveGaugeTest μ k T R {A | MeasurableSet A ∧ Bornology.IsBounded A} := by
  intro n hn k hk hkn μ hμ hreg T hT R hR hfin A hA
  obtain ⟨hAm, hAb⟩ := hA
  obtain ⟨t, htpos, hts, hint⟩ :=
    i2_gaugeSeries_integral n hn k hk hkn μ hμ hreg T hT R hR hfin A hAm hAb
  exact ⟨i2_gaugeSeries t, i2_gaugeSeries_admissible t htpos hts, hint⟩

end ParabolicRectifiability.IntegralCanonical
