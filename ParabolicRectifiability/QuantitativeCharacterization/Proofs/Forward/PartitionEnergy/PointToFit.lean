import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # Point-to-fit

If `fit μ L z (2r) ≤ e r^{k+2}`, `A e ≤ 1` and `y ∈ supp μ ∩ P(z, r)`, then
`d_P(y, L) ≤ 2 (A e)^{1/(k+2)} r`. Route, with `d = d_P(y, L)`:
* `d > 2r` is impossible: on `P(y, r) ⊆ P(z, 2r)` the cost is `≥ (d - r)²`, and lower ADR at `y`
  gives `(d - r)² A⁻¹ r^k ≤ e r^{k+2}`, hence `(d - r)² ≤ A e r² ≤ r²`, i.e. `d ≤ 2r`;
* `0 < d ≤ 2r`: on `P(y, d/2) ⊆ P(z, 2r)` the cost is `≥ (d/2)²`, and lower ADR at `y` gives
  `(d/2)^{k+2} ≤ A e r^{k+2}`; take `(k+2)`-th roots;
* `d = 0` is trivial.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

open ParabolicRectifiability.Foundations

/-- A uniform lower bound `c` on `d_P(·, L)` over `P(y, s) ⊆ P(z, R)` bounds the fitting
integral below by `c² μ(P(y, s))`. -/
theorem d1ap2f_fit_lower {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n))
    (L : Models n k T) (z y : Space n) (R s c : ℝ) (hc : 0 ≤ c)
    (hsub : Metric.ball y s ⊆ Metric.ball z R)
    (hcost : ∀ w ∈ Metric.ball y s, c ≤ Metric.infDist w (modelSet L)) :
    ENNReal.ofReal (c ^ 2) * μ (Metric.ball y s) ≤ fit μ L z R := by
  calc
    ENNReal.ofReal (c ^ 2) * μ (Metric.ball y s)
        = ∫⁻ _ in Metric.ball y s, ENNReal.ofReal (c ^ 2) ∂μ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ w in Metric.ball y s, modelCost L w ∂μ := by
      refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
      have hne : Metric.infEDist w (modelSet L) ≠ ⊤ :=
        Metric.infEDist_ne_top (modelSet_nonempty L)
      have hdef : Metric.infDist w (modelSet L) = (Metric.infEDist w (modelSet L)).toReal := rfl
      have h1 : ENNReal.ofReal c ≤ Metric.infEDist w (modelSet L) := by
        rw [← ENNReal.ofReal_toReal hne, ← hdef]
        exact ENNReal.ofReal_le_ofReal (hcost w hw)
      rw [ENNReal.ofReal_pow hc]
      exact pow_le_pow_left' h1 2
    _ ≤ fit μ L z R := lintegral_mono_set hsub

/-- The real inequality `c² (A⁻¹ s^k) ≤ e r^{k+2}` from the fit bound and a lower mass bound. -/
theorem d1ap2f_cost_mass_le {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n))
    (L : Models n k T) (z y : Space n) (R s c A e r : ℝ) (hc : 0 ≤ c)
    (hsub : Metric.ball y s ⊆ Metric.ball z R)
    (hcost : ∀ w ∈ Metric.ball y s, c ≤ Metric.infDist w (modelSet L))
    (hmass : ENNReal.ofReal (A⁻¹ * s ^ k) ≤ μ (Metric.ball y s))
    (hfit : fit μ L z R ≤ ENNReal.ofReal (e * r ^ (k + 2))) (her : 0 ≤ e * r ^ (k + 2)) :
    c ^ 2 * (A⁻¹ * s ^ k) ≤ e * r ^ (k + 2) := by
  have h1 : ENNReal.ofReal (c ^ 2 * (A⁻¹ * s ^ k)) ≤ ENNReal.ofReal (e * r ^ (k + 2)) := by
    rw [ENNReal.ofReal_mul (sq_nonneg c)]
    exact (mul_le_mul_right hmass _).trans
      ((d1ap2f_fit_lower μ L z y R s c hc hsub hcost).trans hfit)
  exact (ENNReal.ofReal_le_ofReal_iff her).1 h1

/-- **Point-to-fit**: if `fit μ L z (2r) ≤ e r^{k+2}`, `A e ≤ 1` and `y ∈ supp μ ∩ P(z, r)`, then `d_P(y, L) ≤ 2 (A e)^{1/(k+2)} r`. -/
theorem d1a_pointToFit_proof : PointToFitStatement := by
  intro n k T μ A a ρ hA hADR z r hr hball h4r L e he hAe hfit y hy
  obtain ⟨hysupp, hyz⟩ := hy
  have hyz' : dist y z < r := Metric.mem_ball.mp hyz
  have hya : y ∈ μ.support ∩ Metric.ball a ρ :=
    ⟨hysupp, hball (Metric.ball_subset_ball (by linarith) hyz)⟩
  have hApos : 0 < A := by linarith
  have hAe0 : 0 ≤ A * e := mul_nonneg hApos.le he
  have her : 0 ≤ e * r ^ (k + 2) := mul_nonneg he (pow_nonneg hr.le _)
  set d := Metric.infDist y (modelSet L) with hd
  have hd0 : 0 ≤ d := Metric.infDist_nonneg
  -- `d_P(w, L) ≥ d - s` on `P(y, s)`.
  have hlow : ∀ s : ℝ, ∀ w ∈ Metric.ball y s, d - s ≤ Metric.infDist w (modelSet L) := by
    intro s w hw
    have h1 := Metric.infDist_le_infDist_add_dist (x := y) (y := w) (s := modelSet L)
    have h2 : dist y w < s := by rw [dist_comm]; exact Metric.mem_ball.mp hw
    linarith
  -- `P(y, s) ⊆ P(z, 2r)` for `s ≤ r`.
  have hsub : ∀ s : ℝ, s ≤ r → Metric.ball y s ⊆ Metric.ball z (2 * r) := by
    intro s hs w hw
    rw [Metric.mem_ball] at hw ⊢
    have := dist_triangle w y z
    linarith
  -- From `c² A⁻¹ s^k ≤ e r^{k+2}` to `c² s^k ≤ (A e) r^{k+2}`.
  have hmulA : ∀ c s : ℝ, c ^ 2 * (A⁻¹ * s ^ k) ≤ e * r ^ (k + 2) →
      c ^ 2 * s ^ k ≤ (A * e) * r ^ (k + 2) := by
    intro c s h
    have h' : c ^ 2 * s ^ k / A ≤ e * r ^ (k + 2) := by
      calc c ^ 2 * s ^ k / A = c ^ 2 * (A⁻¹ * s ^ k) := by ring
        _ ≤ e * r ^ (k + 2) := h
    rw [div_le_iff₀ hApos] at h'
    linarith
  -- Step 1: `d ≤ 2r` (this uses `A e ≤ 1`).
  have hd2 : d ≤ 2 * r := by
    refine le_of_not_gt fun hcon => ?_
    have hmass := (hADR y hya r hr (by linarith)).1
    have key := d1ap2f_cost_mass_le μ L z y (2 * r) r (d - r) A e r (by linarith)
      (hsub r le_rfl) (fun w hw => hlow r w hw) hmass hfit her
    have key2 := hmulA (d - r) r key
    have hp : 0 < r ^ k := pow_pos hr k
    have hrk : r ^ (k + 2) = r ^ 2 * r ^ k := by ring
    have h3 : (d - r) ^ 2 * r ^ k ≤ r ^ 2 * r ^ k := by
      calc (d - r) ^ 2 * r ^ k ≤ (A * e) * r ^ (k + 2) := key2
        _ ≤ 1 * r ^ (k + 2) := mul_le_mul_of_nonneg_right hAe (pow_nonneg hr.le _)
        _ = r ^ 2 * r ^ k := by rw [one_mul, hrk]
    have h4 : (d - r) ^ 2 ≤ r ^ 2 := le_of_mul_le_mul_right h3 hp
    have h5 : r ^ 2 < (d - r) ^ 2 := pow_lt_pow_left₀ (by linarith) hr.le (by norm_num)
    linarith
  -- The root `q = (A e)^{1/(k+2)}`.
  have hq0 : 0 ≤ (A * e) ^ ((1 : ℝ) / (k + 2)) := Real.rpow_nonneg hAe0 _
  rcases hd0.eq_or_lt with hdz | hdpos
  · -- `d = 0`.
    rw [← hdz]
    exact mul_nonneg (mul_nonneg (by norm_num) hq0) hr.le
  · -- Step 2: `0 < d ≤ 2r`, test on `P(y, d/2)`.
    have hs : 0 < d / 2 := by linarith
    have hmass := (hADR y hya (d / 2) hs (by linarith)).1
    have key := d1ap2f_cost_mass_le μ L z y (2 * r) (d / 2) (d / 2) A e r hs.le
      (hsub (d / 2) (by linarith)) (fun w hw => by linarith [hlow (d / 2) w hw]) hmass hfit her
    have key2 := hmulA (d / 2) (d / 2) key
    have hexp : (1 : ℝ) / ((k : ℝ) + 2) = (((k + 2 : ℕ) : ℝ))⁻¹ := by
      push_cast
      rw [one_div]
    have hq : ((A * e) ^ ((1 : ℝ) / ((k : ℝ) + 2))) ^ (k + 2) = A * e := by
      rw [hexp]
      exact Real.rpow_inv_natCast_pow hAe0 (by omega)
    have h3 : (d / 2) ^ (k + 2) ≤ ((A * e) ^ ((1 : ℝ) / ((k : ℝ) + 2)) * r) ^ (k + 2) := by
      calc (d / 2) ^ (k + 2) = (d / 2) ^ 2 * (d / 2) ^ k := by ring
        _ ≤ (A * e) * r ^ (k + 2) := key2
        _ = ((A * e) ^ ((1 : ℝ) / ((k : ℝ) + 2)) * r) ^ (k + 2) := by rw [mul_pow, hq]
    have h4 : d / 2 ≤ (A * e) ^ ((1 : ℝ) / ((k : ℝ) + 2)) * r :=
      (pow_le_pow_iff_left₀ hs.le (mul_nonneg hq0 hr.le) (by omega)).1 h3
    linarith

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
