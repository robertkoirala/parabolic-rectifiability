import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements

/-! # Transfer of periodic `L²` convergence to bounded intervals

The integrand `|h - S_m|²` is periodic with period `2π`. A bounded interval fits inside an
integer number of periods, and the periodic interval-integral theorem transfers its integral to
that many copies of the base-period integral. The same periodic integrability argument first
gives local square integrability of `h`, hence local integrability.
-/

noncomputable section

open MeasureTheory Set Filter Function Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

private abbrev e2_per_period : ℝ := 2 * Real.pi

private theorem e2_per_period_pos : 0 < e2_per_period := by
  dsimp [e2_per_period]
  positivity

private theorem e2_per_partial_continuous (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (m : ℕ) :
    Continuous (e2_halfDerivPartialSum ε a N m) := by
  unfold e2_halfDerivPartialSum
  fun_prop

private theorem e2_per_partial_periodic (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (m : ℕ) :
    Function.Periodic (e2_halfDerivPartialSum ε a N m) e2_per_period := by
  intro t
  simp [e2_halfDerivPartialSum, e2_per_period, mul_add, Real.cos_add_nat_mul_two_pi]

private theorem e2_per_lintegral_eq_ofReal_interval {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hInt : IntervalIntegrable f volume a b) (hNonneg : ∀ x, 0 ≤ f x) :
    (∫⁻ x in Ioc a b, ENNReal.ofReal (f x)) =
      ENNReal.ofReal (∫ x in a..b, f x) := by
  simpa only [intervalIntegral.integral_of_le hab] using
    (ofReal_integral_eq_lintegral_ofReal hInt.1 (ae_of_all _ hNonneg)).symm

private theorem e2_per_lintegral_n_periods {f : ℝ → ℝ}
    (hper : Function.Periodic f e2_per_period)
    (hInt : ∀ a b, IntervalIntegrable f volume a b)
    (hNonneg : ∀ x, 0 ≤ f x) (n : ℕ) (a : ℝ) :
    (∫⁻ x in Ioc a (a + (n : ℝ) * e2_per_period), ENNReal.ofReal (f x)) =
      (n : ℝ≥0∞) * ∫⁻ x in Ioc 0 e2_per_period, ENNReal.ofReal (f x) := by
  have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hend : a ≤ a + (n : ℝ) * e2_per_period := by
    exact le_add_of_nonneg_right (mul_nonneg hnnonneg e2_per_period_pos.le)
  have hreal : (∫ x in a..a + (n : ℝ) * e2_per_period, f x) =
      (n : ℝ) * ∫ x in 0..e2_per_period, f x := by
    rw [show a + (n : ℝ) * e2_per_period = a + (n : ℤ) • e2_per_period by simp]
    rw [hper.intervalIntegral_add_zsmul_eq (n : ℤ) a hInt,
      hper.intervalIntegral_add_eq a 0]
    simp [zsmul_eq_mul]
  have hbaseNonneg : 0 ≤ ∫ x in 0..e2_per_period, f x := by
    rw [intervalIntegral.integral_of_le e2_per_period_pos.le]
    exact integral_nonneg (fun x => hNonneg x)
  have hlarge := e2_per_lintegral_eq_ofReal_interval hend (hInt a _) hNonneg
  have hbase := e2_per_lintegral_eq_ofReal_interval e2_per_period_pos.le
    (hInt 0 e2_per_period) hNonneg
  calc
    (∫⁻ x in Ioc a (a + (n : ℝ) * e2_per_period), ENNReal.ofReal (f x)) =
        ENNReal.ofReal (∫ x in a..a + (n : ℝ) * e2_per_period, f x) := hlarge
    _ = ENNReal.ofReal ((n : ℝ) * ∫ x in 0..e2_per_period, f x) := by rw [hreal]
    _ = (n : ℝ≥0∞) * ∫⁻ x in Ioc 0 e2_per_period, ENNReal.ofReal (f x) := by
      rw [ENNReal.ofReal_mul hnnonneg, ENNReal.ofReal_natCast, ← hbase]

theorem e2_periodic_local_proof : E2PeriodicLocalStatement := by
  intro ε a N h hh
  rcases hh with ⟨hmeas, hperiodic, hconv⟩
  let S : ℕ → ℝ → ℝ := fun m => e2_halfDerivPartialSum ε a N m
  let q : ℕ → ℝ → ℝ := fun m t => (h t - S m t) ^ 2
  have hScont (m : ℕ) : Continuous (S m) := by
    simpa [S] using e2_per_partial_continuous ε a N m
  have hSper (m : ℕ) : Function.Periodic (S m) e2_per_period := by
    simpa [S] using e2_per_partial_periodic ε a N m
  have hqmeas (m : ℕ) : Measurable (q m) := by
    change Measurable (fun t => (h t - S m t) ^ 2)
    exact (hmeas.sub (hScont m).measurable).pow_const 2
  have hqper (m : ℕ) : Function.Periodic (q m) e2_per_period := by
    intro t
    simp [q, hperiodic t, hSper m t]
  let μ : Measure ℝ := volume.restrict (Ioc 0 e2_per_period)
  let A : ℕ → ℝ≥0∞ := fun m => ∫⁻ t in Ioc 0 e2_per_period, ENNReal.ofReal (q m t)
  have hA : Tendsto A atTop (𝓝 0) := by
    simpa [A, q, S, e2_per_period, e2_halfDerivPartialSum] using hconv
  have hAeventually : ∀ᶠ m : ℕ in atTop, A m < 1 :=
    hA.eventually (p := fun x => x < 1) (Iio_mem_nhds (by norm_num))
  obtain ⟨m₀, hm₀⟩ := hAeventually.exists
  have hq₀Int : Integrable (q m₀) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (μ := μ) (f := q m₀) (hqmeas m₀).aestronglyMeasurable
      (ae_of_all _ fun t => sq_nonneg (h t - S m₀ t))).mp
    simpa [A, μ] using ne_of_lt (lt_trans hm₀ (by norm_num))
  have hS2Int (m : ℕ) : Integrable (fun t => (S m t) ^ 2) μ := by
    have hc : Continuous (fun t => (S m t) ^ 2) := (hScont m).pow 2
    change Integrable (fun t => (S m t) ^ 2) (volume.restrict (Ioc 0 e2_per_period))
    exact (hc.intervalIntegrable 0 e2_per_period).1
  have hsum₀Int : Integrable
      (fun t => (q m₀ t + (S m₀ t) ^ 2) + (q m₀ t + (S m₀ t) ^ 2)) μ :=
    (hq₀Int.add (hS2Int m₀)).add (hq₀Int.add (hS2Int m₀))
  have hSqInt : Integrable (fun t => h t ^ 2) μ := by
    apply hsum₀Int.mono'
      ((hmeas.pow_const 2).aestronglyMeasurable)
    filter_upwards with t
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (h t))]
    dsimp [q, S]
    nlinarith [sq_nonneg (h t - 2 * e2_halfDerivPartialSum ε a N m₀ t)]
  have hqBaseInt (m : ℕ) : Integrable (q m) μ := by
    have hsumInt : Integrable
        (fun t => (h t ^ 2 + (S m t) ^ 2) + (h t ^ 2 + (S m t) ^ 2)) μ :=
      (hSqInt.add (hS2Int m)).add (hSqInt.add (hS2Int m))
    apply hsumInt.mono' (hqmeas m).aestronglyMeasurable
    filter_upwards with t
    change |(h t - S m t) ^ 2| ≤
      (h t ^ 2 + (S m t) ^ 2) + (h t ^ 2 + (S m t) ^ 2)
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (h t + S m t)]
  have hqBaseInterval (m : ℕ) : IntervalIntegrable (q m) volume 0 e2_per_period := by
    refine ⟨?_, ?_⟩
    · change Integrable (q m) (volume.restrict (Ioc 0 e2_per_period))
      exact hqBaseInt m
    · rw [Ioc_eq_empty_of_le e2_per_period_pos.le]
      exact IntegrableOn.of_measure_zero (by simp)
  have hqEvery (m : ℕ) (α β : ℝ) : IntervalIntegrable (q m) volume α β := by
    exact (hqper m).intervalIntegrable₀ e2_per_period_pos.ne' (hqBaseInterval m) α β
  have hSqper : Function.Periodic (fun t => h t ^ 2) e2_per_period := by
    intro t
    simp [hperiodic t]
  have hSqBaseInterval : IntervalIntegrable (fun t => h t ^ 2) volume 0 e2_per_period := by
    refine ⟨?_, ?_⟩
    · change Integrable (fun t => h t ^ 2) (volume.restrict (Ioc 0 e2_per_period))
      exact hSqInt
    · rw [Ioc_eq_empty_of_le e2_per_period_pos.le]
      exact IntegrableOn.of_measure_zero (by simp)
  have hSqEvery : ∀ α β, IntervalIntegrable (fun t => h t ^ 2) volume α β := by
    intro α β
    exact hSqper.intervalIntegrable₀ e2_per_period_pos.ne' hSqBaseInterval α β
  have hOneInt : Integrable (fun _ : ℝ => (1 : ℝ)) μ := by
    have hc : Continuous (fun _ : ℝ => (1 : ℝ)) := continuous_const
    change Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 e2_per_period))
    exact (hc.intervalIntegrable 0 e2_per_period).1
  have hdomh : Integrable (fun t => 1 + h t ^ 2) μ := hOneInt.add hSqInt
  have hBaseInt : Integrable (fun t => h t) μ := by
    apply hdomh.mono' hmeas.aestronglyMeasurable
    filter_upwards with t
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|h t| - (1 / 2 : ℝ)), sq_abs (h t)]
  have hBaseInterval : IntervalIntegrable h volume 0 e2_per_period := by
    refine ⟨?_, ?_⟩
    · change Integrable h (volume.restrict (Ioc 0 e2_per_period))
      exact hBaseInt
    · rw [Ioc_eq_empty_of_le e2_per_period_pos.le]
      exact IntegrableOn.of_measure_zero (by simp)
  have hIntEvery : ∀ α β, IntervalIntegrable h volume α β := by
    intro α β
    exact hperiodic.intervalIntegrable₀ e2_per_period_pos.ne' hBaseInterval α β
  have hloc : LocallyIntegrable h volume := by
    intro x
    refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    exact (hIntEvery (x - 1) (x + 1)).1.mono_set Ioo_subset_Ioc_self
  refine ⟨hloc, ?_⟩
  intro α β
  refine ⟨?_, ?_⟩
  · exact (hSqEvery α β).1.setLIntegral_lt_top
  · let localInt : ℕ → ℝ≥0∞ := fun m =>
      ∫⁻ t in Ioc α β, ENNReal.ofReal (q m t)
    obtain ⟨n, hn⟩ := exists_nat_ge ((β - α) / e2_per_period)
    have hend : β ≤ α + (n : ℝ) * e2_per_period := by
      have h := (div_le_iff₀ e2_per_period_pos).mp hn
      linarith
    have hsubset : Ioc α β ⊆ Ioc α (α + (n : ℝ) * e2_per_period) := by
      intro t ht
      exact ⟨ht.1, ht.2.trans hend⟩
    have hbound (m : ℕ) : localInt m ≤ (n : ℝ≥0∞) * A m := by
      calc
        localInt m ≤ ∫⁻ t in Ioc α (α + (n : ℝ) * e2_per_period),
            ENNReal.ofReal (q m t) := lintegral_mono_set hsubset
        _ = (n : ℝ≥0∞) * A m := by
          exact e2_per_lintegral_n_periods (hqper m)
            (hqEvery m)
            (fun t => sq_nonneg (h t - S m t)) n α
    have hupper : Tendsto (fun m => (n : ℝ≥0∞) * A m) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hA (Or.inr (ENNReal.natCast_ne_top n))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun m => zero_le) hbound

end ParabolicRectifiability.Examples
