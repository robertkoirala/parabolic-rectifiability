import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Measure.Beta

/-! # Measurability of the densities

Proofs of two statements, with the types of `fmeas1_measurable_ball_measure` and
`fmeas1_densities_eq_rat`:

* `fmeas1_measurable_ball_measure_proof`: for a source finite on compacts, the moving-ball
  mass `z ↦ μ(P(z,r))` is measurable. The moving-ball
  argument of `measurable_fit`: `μ` is sigma-finite (`source_sigmaFinite`), the set
  `{(z,w) | dist w z < r}` is measurable in the product, and
  `measurable_measure_prodMk_left` gives the measurability of its slice masses.
* `fmeas1_densities_eq_rat_proof`: for every measure, both densities are computed by
  rational radii. No regularity or finiteness is used.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- Moving-ball mass is Borel. -/
theorem fmeas1_measurable_ball_measure_proof {n : ℕ} (μ : Measure (Space n))
    (hμ : IsFiniteMeasureOnCompacts μ) (r : ℝ) :
    Measurable (fun z : Space n => μ (Metric.ball z r)) := by
  have := hμ
  have : SigmaFinite μ := source_sigmaFinite μ
  have hs : MeasurableSet {p : Space n × Space n | dist p.2 p.1 < r} :=
    measurableSet_lt (measurable_snd.dist measurable_fst) measurable_const
  exact measurable_measure_prodMk_left hs

/-- The countable basis `Ioo 0 (1/(j+1))` of `𝓝[>] 0`. -/
theorem bf1meas1_hasBasis_nhdsGT_zero :
    (𝓝[>] (0 : ℝ)).HasBasis (fun _ : ℕ => True) (fun j => Ioo 0 (1 / ((j : ℝ) + 1))) :=
  (nhdsGT_basis (0 : ℝ)).to_hasBasis
    (fun δ hδ => by
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
      exact ⟨j, trivial, Ioo_subset_Ioo_right hj.le⟩)
    (fun j _ => ⟨1 / ((j : ℝ) + 1), Nat.one_div_pos_of_nat, subset_rfl⟩)

/-- Infimum step: on `(0,δ)` the real and the rational infima of the ratio agree. -/
theorem bf1meas1_iInf_eq_rat {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n) (δ : ℝ) :
    (⨅ r ∈ Ioo (0 : ℝ) δ, densityRatio μ k z r) =
      ⨅ q : {q : ℚ // 0 < q ∧ (q : ℝ) < δ}, densityRatio μ k z (q.1 : ℝ) := by
  refine le_antisymm
    (le_iInf fun q => iInf₂_le (q.1 : ℝ) ⟨by exact_mod_cast q.2.1, q.2.2⟩)
    (le_iInf₂ fun r hr => ?_)
  set IQ := ⨅ q : {q : ℚ // 0 < q ∧ (q : ℝ) < δ}, densityRatio μ k z (q.1 : ℝ)
  have key : ∀ x ∈ Ioo (0 : ℝ) r,
      IQ ≤ μ (Metric.ball z r) / ENNReal.ofReal x ^ k := by
    intro x hx
    obtain ⟨q, hxq, hqr⟩ := exists_rat_btwn hx.2
    have hq0 : (0 : ℚ) < q := by exact_mod_cast hx.1.trans hxq
    calc IQ ≤ densityRatio μ k z (q : ℝ) :=
          iInf_le (fun q : {q : ℚ // 0 < q ∧ (q : ℝ) < δ} => densityRatio μ k z (q.1 : ℝ))
            ⟨q, hq0, hqr.trans hr.2⟩
      _ ≤ μ (Metric.ball z r) / ENNReal.ofReal x ^ k :=
        ENNReal.div_le_div (measure_mono (Metric.ball_subset_ball hqr.le))
          (pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal hxq.le) k)
  have hne0 : ENNReal.ofReal r ^ k ≠ 0 := pow_ne_zero k (ENNReal.ofReal_pos.2 hr.1).ne'
  have hnetop : ENNReal.ofReal r ^ k ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hpow : Tendsto (fun x : ℝ => ENNReal.ofReal x ^ k) (𝓝[<] r)
      (𝓝 (ENNReal.ofReal r ^ k)) :=
    (((ENNReal.continuous_pow k).comp ENNReal.continuous_ofReal).tendsto r).mono_left
      nhdsWithin_le_nhds
  have ht : Tendsto (fun x : ℝ => μ (Metric.ball z r) / ENNReal.ofReal x ^ k) (𝓝[<] r)
      (𝓝 (densityRatio μ k z r)) :=
    ENNReal.Tendsto.div tendsto_const_nhds (Or.inr hne0) hpow (Or.inl hnetop)
  exact ge_of_tendsto ht (Filter.mem_of_superset (Ioo_mem_nhdsLT hr.1) key)

/-- Supremum step: on `(0,δ)` the real and the rational suprema of the ratio agree. -/
theorem bf1meas1_iSup_eq_rat {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n) (δ : ℝ) :
    (⨆ r ∈ Ioo (0 : ℝ) δ, densityRatio μ k z r) =
      ⨆ q : {q : ℚ // 0 < q ∧ (q : ℝ) < δ}, densityRatio μ k z (q.1 : ℝ) := by
  refine le_antisymm (iSup₂_le fun r hr => ?_)
    (iSup_le fun q => le_iSup₂_of_le (q.1 : ℝ) ⟨by exact_mod_cast q.2.1, q.2.2⟩ le_rfl)
  have hU : Metric.ball z r =
      ⋃ q : {q : ℚ // 0 < q ∧ (q : ℝ) < r}, Metric.ball z (q.1 : ℝ) := by
    ext x
    simp only [Metric.mem_ball, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨q, h1, h2⟩ := exists_rat_btwn hx
      exact ⟨⟨q, by exact_mod_cast dist_nonneg.trans_lt h1, h2⟩, h1⟩
    · rintro ⟨q, hq⟩
      exact hq.trans q.2.2
  have hD : Directed (· ⊆ ·)
      (fun q : {q : ℚ // 0 < q ∧ (q : ℝ) < r} => Metric.ball z (q.1 : ℝ)) := by
    intro a b
    refine ⟨⟨max a.1 b.1, lt_max_of_lt_left a.2.1, ?_⟩,
      Metric.ball_subset_ball ?_, Metric.ball_subset_ball ?_⟩
    · rw [Rat.cast_max]; exact max_lt a.2.2 b.2.2
    · exact_mod_cast le_max_left a.1 b.1
    · exact_mod_cast le_max_right a.1 b.1
  calc densityRatio μ k z r = μ (Metric.ball z r) / ENNReal.ofReal r ^ k := rfl
    _ = (⨆ q : {q : ℚ // 0 < q ∧ (q : ℝ) < r}, μ (Metric.ball z (q.1 : ℝ))) /
          ENNReal.ofReal r ^ k := by rw [hU, hD.measure_iUnion]
    _ = ⨆ q : {q : ℚ // 0 < q ∧ (q : ℝ) < r},
          μ (Metric.ball z (q.1 : ℝ)) / ENNReal.ofReal r ^ k := ENNReal.iSup_div _ _
    _ ≤ ⨆ q : {q : ℚ // 0 < q ∧ (q : ℝ) < δ}, densityRatio μ k z (q.1 : ℝ) :=
        iSup_le fun q => le_iSup_of_le ⟨q.1, q.2.1, q.2.2.trans hr.2⟩
          (ENNReal.div_le_div_left
            (pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal q.2.2.le) k) _)

/-- Rational radii compute both densities. -/
theorem fmeas1_densities_eq_rat_proof (n : ℕ) (μ : Measure (Space n)) (k : ℕ) (z : Space n) :
    lowerDensity μ k z =
        ⨆ j : ℕ, ⨅ q : {q : ℚ // 0 < q ∧ (q : ℝ) < 1 / ((j : ℝ) + 1)},
          densityRatio μ k z (q.1 : ℝ) ∧
      upperDensity μ k z =
        ⨅ j : ℕ, ⨆ q : {q : ℚ // 0 < q ∧ (q : ℝ) < 1 / ((j : ℝ) + 1)},
          densityRatio μ k z (q.1 : ℝ) := by
  constructor
  · rw [lowerDensity, bf1meas1_hasBasis_nhdsGT_zero.liminf_eq_iSup_iInf]
    exact iSup_congr fun j => by rw [iSup_pos trivial, bf1meas1_iInf_eq_rat]
  · rw [upperDensity, bf1meas1_hasBasis_nhdsGT_zero.limsup_eq_iInf_iSup]
    exact iInf_congr fun j => by rw [iInf_pos trivial, bf1meas1_iSup_eq_rat]

end ParabolicRectifiability.Foundations
