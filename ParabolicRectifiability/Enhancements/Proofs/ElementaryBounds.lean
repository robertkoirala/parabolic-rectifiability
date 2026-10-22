import ParabolicRectifiability.Enhancements.Decomposition
import ParabolicRectifiability.Measure.BetaLaws

/-! # Global Hausdorff bound, Markov bound for gauge energies, density off a carrier

Three elementary lemmas used in the rectifiable Reifenberg theorem, the energy rates and the
density corollaries:

* `exists_hausdorffP_le_of_local_bound_proof`: local Hausdorff bounds on the unit closure
  give a global one, by a finite cover of the compact unit closure by open radius-one
  balls and finite subadditivity of the outer measure.
* `measure_lt_squareEnergy_le_gaugeEnergy_div_proof`: Markov's inequality for the
  restricted measure, after `Φ(M) ≤ Φ(S)` on the exceptional set.
* `upperDensity_eq_of_not_mem_closed_carrier_proof`: the density ratios of `μ` and `μ⁺`
  agree at all radii below the distance from `z` to the closed carrier.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Enhancements

open ParabolicRectifiability.Foundations

/-- `m · ofReal C ≤ ofReal ((m + 1) C)` for every real `C` (both sides vanish-or-compare:
for `C ≤ 0` the left side is zero). -/
theorem acond_card_mul_ofReal_le (m : ℕ) (C : ℝ) :
    (m : ℝ≥0∞) * ENNReal.ofReal C ≤ ENNReal.ofReal (((m : ℝ) + 1) * C) := by
  rcases le_or_gt C 0 with hC | hC
  · rw [ENNReal.ofReal_of_nonpos hC, mul_zero]
    exact zero_le
  · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (Nat.cast_nonneg m) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    gcongr
    exact le_self_add

/-- There is `N = N(n) > 0` such that every `K ⊆ P̄(0,1)` with
`H_P^k(K ∩ P(q,R)) ≤ C R^k` for all `q` and `0 < R ≤ 1` satisfies `H_P^k(K) ≤ N C`. -/
theorem exists_hausdorffP_le_of_local_bound_proof (n : ℕ) :
    ∃ N : ℝ, 0 < N ∧ ∀ (k : ℕ) (C : ℝ) (K : Set (Space n)),
      K ⊆ Metric.closedBall (point 0 0) 1 →
      (∀ (q : Space n) (R : ℝ), 0 < R → R ≤ 1 →
        hausdorffP n k (K ∩ Metric.ball q R) ≤ ENNReal.ofReal (C * R ^ k)) →
      hausdorffP n k K ≤ ENNReal.ofReal (N * C) := by
  obtain ⟨t, ht⟩ := (isCompact_closedBall (point 0 0 : Space n) 1).elim_finite_subcover
    (fun q : Space n => Metric.ball q 1) (fun _ => Metric.isOpen_ball)
    (fun z _ => Set.mem_iUnion.mpr ⟨z, Metric.mem_ball_self one_pos⟩)
  refine ⟨(t.card : ℝ) + 1, by positivity, ?_⟩
  intro k C K hK hloc
  have hcov : K ⊆ ⋃ q ∈ t, K ∩ Metric.ball q 1 := by
    intro z hz
    obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.mp (ht (hK hz))
    exact Set.mem_iUnion₂.mpr ⟨q, hq, hz, hzq⟩
  calc hausdorffP n k K ≤ hausdorffP n k (⋃ q ∈ t, K ∩ Metric.ball q 1) := measure_mono hcov
    _ ≤ ∑ q ∈ t, hausdorffP n k (K ∩ Metric.ball q 1) := measure_biUnion_finset_le t _
    _ ≤ ∑ _q ∈ t, ENNReal.ofReal C := by
        refine Finset.sum_le_sum fun q _ => ?_
        simpa using hloc q 1 one_pos le_rfl
    _ = (t.card : ℝ≥0∞) * ENNReal.ofReal C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (((t.card : ℝ) + 1) * C) := acond_card_mul_ofReal_le t.card C

/-- Markov bound: for a nondecreasing Borel gauge `Φ` with `0 < Φ(M) < ∞`,
`μ(P(a,R) ∩ {S^{2R}_{μ,T} > M}) ≤ Λ_Φ / Φ(M)`. -/
theorem measure_lt_squareEnergy_le_gaugeEnergy_div_proof {n : ℕ} (k : ℕ)
    (μ : Measure (Space n))
    (hμ : IsFiniteMeasureOnCompacts μ) (T : FamilyKind) (a : Space n) (R : ℝ)
    (Φ : ℝ≥0∞ → ℝ≥0∞) (hΦ : Monotone Φ) (hΦm : Measurable Φ) (M : ℝ)
    (hpos : 0 < Φ (ENNReal.ofReal M)) (hfin : Φ (ENNReal.ofReal M) ≠ ⊤) :
    μ (Metric.ball a R ∩ {z | ENNReal.ofReal M < squareEnergy μ k T (2 * R) z}) ≤
      gaugeEnergy Φ μ k T a R / Φ (ENNReal.ofReal M) := by
  have := hμ
  have hmeas : Measurable fun z => Φ (squareEnergy μ k T (2 * R) z) :=
    hΦm.comp (measurable_squareEnergy μ k T (2 * R))
  calc μ (Metric.ball a R ∩ {z | ENNReal.ofReal M < squareEnergy μ k T (2 * R) z})
      ≤ μ ({z | Φ (ENNReal.ofReal M) ≤ Φ (squareEnergy μ k T (2 * R) z)} ∩
          Metric.ball a R) := by
        apply measure_mono
        rintro z ⟨hzb, hz⟩
        exact ⟨hΦ (le_of_lt hz), hzb⟩
    _ = (μ.restrict (Metric.ball a R))
          {z | Φ (ENNReal.ofReal M) ≤ Φ (squareEnergy μ k T (2 * R) z)} :=
        (Measure.restrict_apply' Metric.isOpen_ball.measurableSet).symm
    _ ≤ (∫⁻ z, Φ (squareEnergy μ k T (2 * R) z) ∂(μ.restrict (Metric.ball a R))) /
          Φ (ENNReal.ofReal M) :=
        meas_ge_le_lintegral_div hmeas.aemeasurable hpos.ne' hfin
    _ = gaugeEnergy Φ μ k T a R / Φ (ENNReal.ofReal M) := rfl

/-- If `μ = μ⁺ + μ_g` with `μ_g` carried by a closed set `K`, then
`Θ^{k,*}(μ⁺,z) = Θ^{k,*}(μ,z)` at every `z ∉ K`. -/
theorem upperDensity_eq_of_not_mem_closed_carrier_proof {n : ℕ} (k : ℕ)
    (μ μp μg : Measure (Space n)) (K : Set (Space n)) (hK : IsClosed K)
    (hsum : μ = μp + μg) (hcarried : μg Kᶜ = 0) {z : Space n} (hz : z ∉ K) :
    upperDensity μp k z = upperDensity μ k z := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl z hz
  subst hsum
  unfold upperDensity
  apply Filter.limsup_congr
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ε := nhdsWithin_le_nhds (Iio_mem_nhds hε)
  filter_upwards [hsmall] with r hr
  have h0 : μg (Metric.ball z r) = 0 :=
    measure_mono_null ((Metric.ball_subset_ball hr.le).trans hball) hcarried
  simp only [densityRatio, Measure.add_apply, h0, add_zero]

end ParabolicRectifiability.Enhancements
