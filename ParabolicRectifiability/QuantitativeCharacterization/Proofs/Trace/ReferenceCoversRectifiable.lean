import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Trace.ComponentTheorems
import ParabolicRectifiability.Foundations.Proofs.Rectifiability.SumsFromRestrictions

/-! # Quantitative mixed rectifiability from reference covers: assembly

`dp2_qmr_rectifiable_of_reference_covers` has exactly the type of
`QuantitativeCharacterization.qmr_rectifiable_of_reference_covers`. It is assembled from the
auxiliary statements `dp2_infinite_multiplicity_null`, `dp2_trace_carriage` and
`dp2_restrict_carrier_rectifiable` and the rectifiability lemmas for countable sums and
restricted covers.

Proof:
* one root (`dp2_root_rectifiable`): the null set of infinite multiplicity and `μ ≪ H_P^k` give
  finite multiplicity a.e.; trace carriage puts `μ`-a.e. point of the root on a trace
  `P_i ∩ Γ_i`; reference-null transfer makes every `(μ⌊P₀)⌊Γ_i` regularly rectifiable of the
  reference type, hence mixed; the countable-sum and restricted-cover lemmas (through
  `f2i_isRegularlyRectifiableMeasure_of_restrict_cover`) give `μ⌊P₀`;
* root exhaustion: one support point `a` and the roots `P(a, m + 1)`, `m ∈ ℕ`, cover `X`
  (`Metric.iUnion_ball_nat_succ`); every root has a covering by the `(K,L)` property. If
  `supp μ = ∅`, inner regularity gives `μ = 0` on `X`.

No ADR or upper growth of `μ` is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **One root.** Under the typed reference covers, the restriction of `μ ≪ H_P^k` to a root
`P(a,R)` with a `(K,L)` regular mixed covering is regularly mixed rectifiable. -/
theorem dp2_root_rectifiable {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2) {K L : ℝ}
    (hL : 1 ≤ L)
    (hcov : ∀ ρ : Reference n k L, ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover ρ.kind k ρ.measure ε)
    {μ : Measure (Space n)} (hfin : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (hac : μ ≪ hausdorffP n k) {a : Space n} {R : ℝ} (𝒞 : RegularMixedCovering k K L μ a R) :
    IsRegularlyRectifiableMeasure .mixed k (μ.restrict (Metric.ball a R)) := by
  have hnull : μ {z | 𝒞.multiplicity z = ⊤} = 0 :=
    hac (dp2_infinite_multiplicity_null n k hk K L μ a R 𝒞)
  have hfinite : ∀ᵐ z ∂μ, 𝒞.multiplicity z ≠ ⊤ := by
    rw [ae_iff]
    simpa only [ne_eq, not_not] using hnull
  have hmult : ∀ᵐ z ∂μ, z ∈ Metric.ball a R → 𝒞.multiplicity z < ⊤ := by
    filter_upwards [hfinite] with z hz _
    exact lt_top_iff_ne_top.mpr hz
  have htrace := dp2_trace_carriage n k K L hL μ hfin hreg a R 𝒞 hmult
  refine f2i_isRegularlyRectifiableMeasure_of_restrict_cover .mixed
    (fun i : 𝒞.index => (𝒞.reference i).carrier) ?_ fun i => ?_
  · rw [Measure.restrict_apply' measurableSet_ball]
    refine measure_mono_null ?_ htrace
    rintro z ⟨hz, hzb⟩
    refine ⟨hzb, fun hz' => hz ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz'
    exact mem_iUnion.mpr ⟨i, hi.2⟩
  · exact f2i_isRegularlyRectifiableMeasure_mixed_of_typed _
      (dp2_restrict_carrier_rectifiable n hn k hk hkn L hL (𝒞.reference i) (hcov _ 1 one_pos)
        (μ.restrict (Metric.ball a R))
        ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hac))

/-- **Regular rectifiability from reference covers**: exactly the type of
`qmr_rectifiable_of_reference_covers`. The reference-cover hypothesis remains an explicit input of this implication. -/
theorem dp2_qmr_rectifiable_of_reference_covers :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ L : ℝ, 1 ≤ L →
    (∀ ρ : Reference n k L, ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover ρ.kind k ρ.measure ε) →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ K : ℝ, 1 ≤ K → IsQuantitativelyMixedRectifiable k K L μ →
      IsRegularlyRectifiableMeasure .mixed k μ := by
  intro n hn k hk hkn L hL hcov μ hfin hreg K _ hQ
  obtain ⟨hac, hroots⟩ := hQ
  rcases μ.support.eq_empty_or_nonempty with h0 | ⟨a, ha⟩
  · -- empty support: `μ` vanishes (inner regularity gives a conull support)
    have hU : μ univ = 0 := by
      have h := Measure.measure_compl_support_of_innerRegular (μ := μ)
      rwa [h0, compl_empty] at h
    exact f2i_isRegularlyRectifiableMeasure_of_restrict_cover (ι := Empty) .mixed
      (fun _ => ∅) (measure_mono_null (subset_univ _) hU) fun i => i.elim
  · refine f2i_isRegularlyRectifiableMeasure_of_restrict_cover .mixed
      (fun m : ℕ => Metric.ball a ((m : ℝ) + 1)) ?_ fun m => ?_
    · simp only [Metric.iUnion_ball_nat_succ, compl_univ, measure_empty]
    · obtain ⟨𝒞⟩ := hroots a ha ((m : ℝ) + 1) (by positivity)
      exact dp2_root_rectifiable hn hk hkn hL hcov hfin hreg hac 𝒞

end ParabolicRectifiability.QuantitativeCharacterization
