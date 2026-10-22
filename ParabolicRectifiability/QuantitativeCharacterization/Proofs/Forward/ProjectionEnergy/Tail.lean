import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ProjectionEnergy

/-! # The limit tail

Proof of `d1e2_tail_proof : d1e2_TailStatement`. Pure sequences.

Route.
* **Budget.** Put `K = max D 0`. Each term of `∑ d_j² ≤ ofReal D ≤ ofReal K` gives `d_j² ≤ K`
  (a real inequality with the nonnegative right side `K`; for `D < 0` this says every
  `d_j = 0`, so every increment vanishes). Hence `d_j ≤ K + 1`.
* **Convergence.** `r_j = h^j r_0`, so `dist (f j) (f (j+1)) ≤ (c r_0 (K+1)) h^j`; the sequence is
  Cauchy (`cauchySeq_of_le_geometric`), `Spatial n` is complete, and
  `Tendsto f atTop (𝓝 (limUnder atTop f))` (`tendsto_nhds_limUnder`).
* **Finite telescoping and weighted Cauchy-Schwarz.** For every `N`,
  `|f_{j+N} - f_j| ≤ c r_j ∑_{ℓ<N} h^ℓ d_{j+ℓ}` and
  `(∑_{ℓ<N} h^ℓ d_{j+ℓ})² ≤ (∑_{ℓ<N} h^ℓ)(∑_{ℓ<N} h^ℓ d_{j+ℓ}²) ≤ 2 ∑_{ℓ<N} h^ℓ d_{j+ℓ}²`, so
  `‖f_{j+N} - f_j‖ₑ² ≤ ofReal (2c² r_j²) * T_j`. Letting `N → ∞` (`le_of_tendsto'` in `ℝ≥0∞`)
  gives (i).
* (ii) is (i) at `j = 0` with `h^ℓ ≤ 1` and `∑ d² ≤ ofReal D`;
  `ofReal (2c² r_0²) * ofReal D = ofReal (2c² r_0² D)` for every real `D`.

Helpers carry the prefix `d1e2tail_`. -/

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-- The radii are geometric: `r_{j+ℓ} = h^ℓ r_j`. -/
theorem d1e2tail_radius (r : ℕ → ℝ) (hr : ∀ j, r (j + 1) = CoherentChart.ratio * r j)
    (j ℓ : ℕ) : r (j + ℓ) = CoherentChart.ratio ^ ℓ * r j := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [← add_assoc, hr, ih, pow_succ]
    ring

/-- The finite geometric sums of the weights: `∑_{ℓ<N} h^ℓ ≤ 2`. -/
theorem d1e2tail_geom_partial (N : ℕ) :
    ∑ ℓ ∈ Finset.range N, CoherentChart.ratio ^ ℓ ≤ 2 := by
  have h0 : (0 : ℝ) ≤ CoherentChart.ratio := by norm_num [CoherentChart.ratio]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ', pow_zero]
    have hshift : ∑ ℓ ∈ Finset.range N, CoherentChart.ratio ^ (ℓ + 1) =
        CoherentChart.ratio * ∑ ℓ ∈ Finset.range N, CoherentChart.ratio ^ ℓ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => pow_succ' _ _
    rw [hshift]
    have h1 := mul_le_mul_of_nonneg_left ih h0
    have h2 : CoherentChart.ratio * 2 + 1 ≤ 2 := by norm_num [CoherentChart.ratio]
    linarith

/-- Finite weighted Cauchy-Schwarz: `(∑ w a)² ≤ (∑ w)(∑ w a²)` for `w ≥ 0`. -/
theorem d1e2tail_cs (w a : ℕ → ℝ) (hw : ∀ ℓ, 0 ≤ w ℓ) (N : ℕ) :
    (∑ ℓ ∈ Finset.range N, w ℓ * a ℓ) ^ 2 ≤
      (∑ ℓ ∈ Finset.range N, w ℓ) * ∑ ℓ ∈ Finset.range N, w ℓ * a ℓ ^ 2 :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun ℓ _ => hw ℓ)
    (fun ℓ _ => mul_nonneg (hw ℓ) (sq_nonneg _)) (fun ℓ _ => le_of_eq (by ring))

/-- Finite telescoping: `‖f_{j+N} - f_j‖ ≤ c r_j ∑_{ℓ<N} h^ℓ d_{j+ℓ}`. -/
theorem d1e2tail_telescope {n : ℕ} (f : ℕ → Spatial n) (r d : ℕ → ℝ) (c : ℝ)
    (hr : ∀ j, r (j + 1) = CoherentChart.ratio * r j)
    (hf : ∀ j, ‖f (j + 1) - f j‖ ≤ c * r j * d j) (j N : ℕ) :
    ‖f (j + N) - f j‖ ≤
      c * r j * ∑ ℓ ∈ Finset.range N, CoherentChart.ratio ^ ℓ * d (j + ℓ) := by
  have h := dist_le_range_sum_dist (fun ℓ => f (j + ℓ)) N
  simp only [add_zero] at h
  rw [dist_comm, dist_eq_norm] at h
  refine h.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ℓ _ => ?_
  calc dist (f (j + ℓ)) (f (j + (ℓ + 1))) = ‖f (j + ℓ + 1) - f (j + ℓ)‖ := by
        rw [dist_comm, dist_eq_norm]
        rfl
    _ ≤ c * r (j + ℓ) * d (j + ℓ) := hf (j + ℓ)
    _ = c * r j * (CoherentChart.ratio ^ ℓ * d (j + ℓ)) := by
        rw [d1e2tail_radius r hr j ℓ]
        ring

/-- The bound at a finite stage:
`‖f_{j+N} - f_j‖ₑ² ≤ ofReal (2c² r_j²) * ∑_ℓ h^ℓ d_{j+ℓ}²`. -/
theorem d1e2tail_stage_bound {n : ℕ} (f : ℕ → Spatial n) (r d : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hr : ∀ j, r (j + 1) = CoherentChart.ratio * r j) (hrnn : ∀ j, 0 ≤ r j)
    (hd : ∀ j, 0 ≤ d j) (hf : ∀ j, ‖f (j + 1) - f j‖ ≤ c * r j * d j) (j N : ℕ) :
    ‖f (j + N) - f j‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 * c ^ 2 * r j ^ 2) *
        ∑' ℓ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ * d (j + ℓ) ^ 2) := by
  have h0 : (0 : ℝ) ≤ CoherentChart.ratio := by norm_num [CoherentChart.ratio]
  have hw : ∀ ℓ : ℕ, 0 ≤ CoherentChart.ratio ^ ℓ := fun ℓ => pow_nonneg h0 ℓ
  set X : ℝ := ∑ ℓ ∈ Finset.range N, CoherentChart.ratio ^ ℓ * d (j + ℓ) with hX
  set Y : ℝ := ∑ ℓ ∈ Finset.range N, CoherentChart.ratio ^ ℓ * d (j + ℓ) ^ 2 with hY
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun ℓ _ => mul_nonneg (hw ℓ) (hd _)
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun ℓ _ => mul_nonneg (hw ℓ) (sq_nonneg _)
  have hcr : 0 ≤ c * r j := mul_nonneg hc (hrnn j)
  have h1 : ‖f (j + N) - f j‖ ≤ c * r j * X := d1e2tail_telescope f r d c hr hf j N
  have h2 : ‖f (j + N) - f j‖ ^ 2 ≤ (c * r j * X) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : X ^ 2 ≤ 2 * Y := by
    have hcs := d1e2tail_cs (fun ℓ => CoherentChart.ratio ^ ℓ) (fun ℓ => d (j + ℓ)) hw N
    have hg := mul_le_mul_of_nonneg_right (d1e2tail_geom_partial N) hY0
    exact hcs.trans hg
  have h4 : ‖f (j + N) - f j‖ ^ 2 ≤ 2 * c ^ 2 * r j ^ 2 * Y := by
    have e1 : (c * r j * X) ^ 2 = (c * r j) ^ 2 * X ^ 2 := by ring
    have e2 : (c * r j) ^ 2 * (2 * Y) = 2 * c ^ 2 * r j ^ 2 * Y := by ring
    have h5 := mul_le_mul_of_nonneg_left h3 (sq_nonneg (c * r j))
    linarith
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  calc ENNReal.ofReal (‖f (j + N) - f j‖ ^ 2) ≤ ENNReal.ofReal (2 * c ^ 2 * r j ^ 2 * Y) :=
        ENNReal.ofReal_le_ofReal h4
    _ = ENNReal.ofReal (2 * c ^ 2 * r j ^ 2) *
          ∑ ℓ ∈ Finset.range N, ENNReal.ofReal (CoherentChart.ratio ^ ℓ * d (j + ℓ) ^ 2) := by
        rw [ENNReal.ofReal_mul (by positivity), hY,
          ENNReal.ofReal_sum_of_nonneg (fun ℓ _ => mul_nonneg (hw ℓ) (sq_nonneg _))]
    _ ≤ ENNReal.ofReal (2 * c ^ 2 * r j ^ 2) *
          ∑' ℓ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ * d (j + ℓ) ^ 2) := by
        gcongr
        exact ENNReal.sum_le_tsum _

/-- **The limit tail** (`d1e2_TailStatement`). -/
theorem d1e2_tail_proof : d1e2_TailStatement := by
  intro n f r d c D hc hr0 hr hd hD hf
  have hq0 : (0 : ℝ) ≤ CoherentChart.ratio := by norm_num [CoherentChart.ratio]
  have hq1 : CoherentChart.ratio < 1 := by norm_num [CoherentChart.ratio]
  -- the budget `K = max D 0`: for `D < 0` this forces every `d_j = 0`
  have hK0 : 0 ≤ max D 0 := le_max_right _ _
  have hdK : ∀ j, d j ^ 2 ≤ max D 0 := by
    intro j
    have h1 : ENNReal.ofReal (d j ^ 2) ≤ ENNReal.ofReal (max D 0) :=
      (ENNReal.le_tsum j).trans (hD.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    exact (ENNReal.ofReal_le_ofReal_iff hK0).mp h1
  have hdM : ∀ j, d j ≤ max D 0 + 1 := by
    intro j
    nlinarith [sq_nonneg (d j - 1), hdK j, hd j, hK0]
  have hrj : ∀ j, r j = CoherentChart.ratio ^ j * r 0 := fun j => by
    simpa using d1e2tail_radius r hr 0 j
  have hrnn : ∀ j, 0 ≤ r j := fun j => by
    rw [hrj j]
    exact mul_nonneg (pow_nonneg hq0 j) hr0.le
  -- convergence and the identification of the limit
  have hcauchy : CauchySeq f := by
    refine cauchySeq_of_le_geometric CoherentChart.ratio (c * r 0 * (max D 0 + 1)) hq1
      fun j => ?_
    rw [dist_comm, dist_eq_norm]
    calc ‖f (j + 1) - f j‖ ≤ c * r j * d j := hf j
      _ ≤ c * r j * (max D 0 + 1) :=
          mul_le_mul_of_nonneg_left (hdM j) (mul_nonneg hc (hrnn j))
      _ = c * r 0 * (max D 0 + 1) * CoherentChart.ratio ^ j := by
          rw [hrj j]
          ring
  obtain ⟨L0, hL0⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim : Tendsto f atTop (𝓝 (limUnder atTop f)) := tendsto_nhds_limUnder ⟨L0, hL0⟩
  -- (i) at every level
  have hi : ∀ j, ‖limUnder atTop f - f j‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 * c ^ 2 * r j ^ 2) *
        ∑' ℓ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ * d (j + ℓ) ^ 2) := by
    intro j
    have hshift : Tendsto (fun N => f (N + j)) atTop (𝓝 (limUnder atTop f)) :=
      hlim.comp (tendsto_add_atTop_nat j)
    have hcont : Continuous fun x : Spatial n => ‖x - f j‖ₑ ^ 2 :=
      (ENNReal.continuous_pow 2).comp (continuous_enorm.comp (continuous_id.sub continuous_const))
    have hT : Tendsto (fun N => ‖f (N + j) - f j‖ₑ ^ 2) atTop
        (𝓝 (‖limUnder atTop f - f j‖ₑ ^ 2)) :=
      (hcont.tendsto _).comp hshift
    refine le_of_tendsto' hT fun N => ?_
    show ‖f (N + j) - f j‖ₑ ^ 2 ≤ _
    rw [add_comm N j]
    exact d1e2tail_stage_bound f r d c hc hr hrnn hd hf j N
  refine ⟨hi, ?_⟩
  -- (ii) at level `0`
  calc ‖limUnder atTop f - f 0‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * c ^ 2 * r 0 ^ 2) *
        ∑' ℓ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ * d (0 + ℓ) ^ 2) := hi 0
    _ ≤ ENNReal.ofReal (2 * c ^ 2 * r 0 ^ 2) * ENNReal.ofReal D := by
        gcongr
        refine le_trans (ENNReal.tsum_le_tsum fun ℓ => ?_) hD
        refine ENNReal.ofReal_le_ofReal ?_
        rw [zero_add]
        exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hq0 hq1.le)
    _ = ENNReal.ofReal (2 * c ^ 2 * D * r 0 ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
