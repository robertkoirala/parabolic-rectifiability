import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ProjectionEnergy

/-! # The sequence lemma for the level majorants

Proof of `d1e2_MajorantSumStatement`. Pure sequences:

* (a) `b_{j+1}² ≤ b_j²/2 + 2C² d_j²`, so the finite partial sums satisfy
  `∑_{j<N} b_j² ≤ 4C² ∑_{j<N} d_j²` (real arithmetic, `b_0 = 0`), hence
  `∑ b_j² ≤ 4C² ∑ d_j²` in `ℝ≥0∞`;
* (b) `∑_j ∑_ℓ h^ℓ d_{j+ℓ}² = ∑_ℓ h^ℓ ∑_j d_{j+ℓ}² ≤ (∑_ℓ h^ℓ) ∑ d² ≤ 2 ∑ d²`;
* (c) both bounds are `ℝ≥0∞` multiples of `∑ d² ≤ ofReal D`, and
  `ofReal (4C²) * ofReal D + 2 * ofReal D = ofReal ((4C² + 2) * D)` holds for every real `D`
  (`ENNReal.ofReal_mul` needs only `0 ≤ 4C² + 2`). A negative budget therefore needs no
  separate real inequality: both sides are then `0`. -/

set_option autoImplicit false

noncomputable section

open Filter
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-- One step of the square recurrence: `0 ≤ z ≤ x/2 + C y` gives `z² ≤ x²/2 + 2C² y²`. -/
theorem d1e2maj_sq_step {x y z C : ℝ} (hz : 0 ≤ z) (hzle : z ≤ 1 / 2 * x + C * y) :
    z ^ 2 ≤ 1 / 2 * x ^ 2 + 2 * C ^ 2 * y ^ 2 := by
  have h1 : z ^ 2 ≤ (1 / 2 * x + C * y) ^ 2 := pow_le_pow_left₀ hz hzle 2
  have h2 : (1 / 2 * x + C * y) ^ 2 = 1 / 2 * x ^ 2 + 2 * C ^ 2 * y ^ 2 - (1 / 2 * x - C * y) ^ 2 := by
    ring
  have h3 : 0 ≤ (1 / 2 * x - C * y) ^ 2 := sq_nonneg _
  linarith

/-- Finite partial sums: `∑_{j<N} b_j² ≤ 4C² ∑_{j<N} d_j²`. -/
theorem d1e2maj_partial (b d : ℕ → ℝ) (C : ℝ) (hb : ∀ j, 0 ≤ b j) (hb0 : b 0 = 0)
    (hrec : ∀ j, b (j + 1) ≤ 1 / 2 * b j + C * d j) (N : ℕ) :
    ∑ j ∈ Finset.range N, b j ^ 2 ≤ 4 * C ^ 2 * ∑ j ∈ Finset.range N, d j ^ 2 := by
  have hstep : ∑ j ∈ Finset.range (N + 1), b j ^ 2 ≤
      ∑ j ∈ Finset.range N, (1 / 2 * b j ^ 2 + 2 * C ^ 2 * d j ^ 2) := by
    rw [Finset.sum_range_succ', hb0]
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h0, add_zero]
    exact Finset.sum_le_sum fun j _ => d1e2maj_sq_step (hb (j + 1)) (hrec j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hstep
  have hmono : ∑ j ∈ Finset.range N, b j ^ 2 ≤ ∑ j ∈ Finset.range (N + 1), b j ^ 2 := by
    rw [Finset.sum_range_succ]
    linarith [sq_nonneg (b N)]
  linarith

/-- (a) The square sum of the majorants: `∑ b_j² ≤ 4C² ∑ d_j²` in `ℝ≥0∞`. -/
theorem d1e2maj_sq_sum (b d : ℕ → ℝ) (C : ℝ) (hb : ∀ j, 0 ≤ b j) (hb0 : b 0 = 0)
    (hrec : ∀ j, b (j + 1) ≤ 1 / 2 * b j + C * d j) :
    ∑' j, ENNReal.ofReal (b j ^ 2) ≤
      ENNReal.ofReal (4 * C ^ 2) * ∑' j, ENNReal.ofReal (d j ^ 2) := by
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg (b j))]
  calc ENNReal.ofReal (∑ j ∈ Finset.range N, b j ^ 2)
      ≤ ENNReal.ofReal (4 * C ^ 2 * ∑ j ∈ Finset.range N, d j ^ 2) :=
        ENNReal.ofReal_le_ofReal (d1e2maj_partial b d C hb hb0 hrec N)
    _ = ENNReal.ofReal (4 * C ^ 2) * ∑ j ∈ Finset.range N, ENNReal.ofReal (d j ^ 2) := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg (d j))]
    _ ≤ ENNReal.ofReal (4 * C ^ 2) * ∑' j, ENNReal.ofReal (d j ^ 2) := by
        gcongr
        exact ENNReal.sum_le_tsum _

/-- The geometric weights: `∑_ℓ h^ℓ = 10/9 ≤ 2` in `ℝ≥0∞`. -/
theorem d1e2maj_geom : ∑' ℓ : ℕ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ) ≤ 2 := by
  have h0 : (0 : ℝ) ≤ CoherentChart.ratio := by norm_num [CoherentChart.ratio]
  have h1 : CoherentChart.ratio < 1 := by norm_num [CoherentChart.ratio]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun ℓ => pow_nonneg h0 ℓ)
      (summable_geometric_of_lt_one h0 h1), tsum_geometric_of_lt_one h0 h1]
  calc ENNReal.ofReal (1 - CoherentChart.ratio)⁻¹ ≤ ENNReal.ofReal 2 :=
        ENNReal.ofReal_le_ofReal (by norm_num [CoherentChart.ratio])
    _ = 2 := ENNReal.ofReal_ofNat 2

/-- (b) The double tail sum: `∑_j ∑_ℓ h^ℓ d_{j+ℓ}² ≤ 2 ∑ d_j²` in `ℝ≥0∞`. -/
theorem d1e2maj_tail_sum (d : ℕ → ℝ) :
    ∑' j, ∑' ℓ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ * d (j + ℓ) ^ 2) ≤
      2 * ∑' j, ENNReal.ofReal (d j ^ 2) := by
  have h0 : (0 : ℝ) ≤ CoherentChart.ratio := by norm_num [CoherentChart.ratio]
  calc ∑' j, ∑' ℓ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ * d (j + ℓ) ^ 2)
      = ∑' ℓ, ∑' j, ENNReal.ofReal (CoherentChart.ratio ^ ℓ) *
          ENNReal.ofReal (d (j + ℓ) ^ 2) := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun ℓ => tsum_congr fun j => ?_
        exact ENNReal.ofReal_mul (pow_nonneg h0 ℓ)
    _ = ∑' ℓ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ) *
          ∑' j, ENNReal.ofReal (d (j + ℓ) ^ 2) := by
        refine tsum_congr fun ℓ => ?_
        exact ENNReal.tsum_mul_left
    _ ≤ ∑' ℓ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ) * ∑' j, ENNReal.ofReal (d j ^ 2) := by
        refine ENNReal.tsum_le_tsum fun ℓ => ?_
        gcongr _ * ?_
        exact ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective ℓ)
          (fun i => ENNReal.ofReal (d i ^ 2))
    _ = (∑' ℓ : ℕ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ)) *
          ∑' j, ENNReal.ofReal (d j ^ 2) :=
        ENNReal.tsum_mul_right
    _ ≤ 2 * ∑' j, ENNReal.ofReal (d j ^ 2) := by
        gcongr
        exact d1e2maj_geom

/-- **The sequence lemma for the level majorants**: `∑ b_j² + ∑_j ∑_ℓ h^ℓ d_{j+ℓ}²` is
bounded by `(4C² + 2)` times the budget for `∑ d_j²`. -/
theorem d1e2_majorant_sum_proof : d1e2_MajorantSumStatement := by
  intro b d C D _hC hb hb0 hrec hD
  rw [ENNReal.tsum_add]
  calc ∑' j, ENNReal.ofReal (b j ^ 2) +
        ∑' j, ∑' ℓ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ * d (j + ℓ) ^ 2)
      ≤ ENNReal.ofReal (4 * C ^ 2) * ∑' j, ENNReal.ofReal (d j ^ 2) +
          2 * ∑' j, ENNReal.ofReal (d j ^ 2) :=
        add_le_add (d1e2maj_sq_sum b d C hb hb0 hrec) (d1e2maj_tail_sum d)
    _ ≤ ENNReal.ofReal (4 * C ^ 2) * ENNReal.ofReal D + 2 * ENNReal.ofReal D := by
        gcongr
    _ = ENNReal.ofReal ((4 * C ^ 2 + 2) * D) := by
        rw [ENNReal.ofReal_mul (p := 4 * C ^ 2 + 2) (by positivity),
          ENNReal.ofReal_add (p := 4 * C ^ 2) (q := 2) (by positivity) (by norm_num),
          ENNReal.ofReal_ofNat, add_mul]

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
