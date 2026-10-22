import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyStatements

/-! # The quarter-interval lacunary graph lies in the open unit ball

The positive weights have total mass at most `1000 / 999`: split off the zeroth
weight and use the supplied tail estimate. Since `N 0 ≥ 1` and `a 0 ≤ 1`, that
weight is at most one. The cosine series is absolutely dominated by the weights,
so its spatial amplitude is at most `(3 / 16) * (1000 / 999) < 1`.
The closed quarter interval gives the separate bound `sqrt |t| ≤ 1 / 2`.
-/

noncomputable section

open Set

namespace ParabolicRectifiability.Examples

/-- The graph over the closed quarter interval lies strictly in the unit ball. -/
theorem e2_quarter_mem_ball_proof :
    E2LacunaryWeightStatement →
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ t ∈ Icc (-1 / 4 : ℝ) (1 / 4), lacunaryGraphMap ε a N t ∈ Metric.ball (point 0 0) 1 := by
  intro hweight ε a N hε hε' hd t ht
  obtain ⟨hpos, _, _, hsum, htail⟩ := hweight a N hd
  have hN : (1 : ℝ) ≤ N 0 := by exact_mod_cast hd.frequency_pos 0
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (N 0) := by
    simpa using Real.sqrt_le_sqrt hN
  have hw0 : a 0 / Real.sqrt (N 0) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (N 0))).2
    simpa using (hd.amplitude_le_one 0).trans hsqrt
  have htail0 : (∑' i, a (i + 1) / Real.sqrt (N (i + 1))) ≤
      a 0 / Real.sqrt (N 0) / 999 := by
    simpa only [Nat.zero_add, Nat.add_comm 1] using htail 0
  have htotal : (∑' j, a j / Real.sqrt (N j)) ≤ 1000 / 999 := by
    rw [hsum.tsum_eq_zero_add]
    linarith
  have hterm : ∀ j, ‖a j / Real.sqrt (N j) * Real.cos (N j * t)‖ ≤
      a j / Real.sqrt (N j) := by
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hpos j)]
    exact mul_le_of_le_one_right (hpos j).le (Real.abs_cos_le_one _)
  have hnorm : Summable (fun j => ‖a j / Real.sqrt (N j) * Real.cos (N j * t)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum
  have hseries : ‖∑' j, a j / Real.sqrt (N j) * Real.cos (N j * t)‖ ≤ 1000 / 999 :=
    (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum hterm hsum).trans htotal)
  have hspatial : |lacunaryFunction ε a N t| < 1 := by
    rw [lacunaryFunction, abs_mul, abs_of_pos hε]
    have hb := mul_le_mul_of_nonneg_left hseries hε.le
    rw [Real.norm_eq_abs] at hb
    have hεbound : ε * (1000 / 999 : ℝ) ≤ (3 / 16) * (1000 / 999) :=
      mul_le_mul_of_nonneg_right hε' (by norm_num)
    exact (hb.trans hεbound).trans_lt (by norm_num)
  have htAbs : |t| ≤ (1 / 4 : ℝ) := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have htime : Real.sqrt |t| ≤ (1 / 2 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  rw [lacunaryGraphMap, Metric.mem_ball, dist_point, max_lt_iff]
  constructor
  · simpa only [sub_zero, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs]
      using hspatial
  · simpa only [sub_zero] using htime.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)

end ParabolicRectifiability.Examples
