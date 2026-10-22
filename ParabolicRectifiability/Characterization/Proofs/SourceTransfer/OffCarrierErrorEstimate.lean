import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.TransferStatements
import ParabolicRectifiability.Measure.ScaleIntegrals

/-! # The off-carrier error estimate in Tonelli form

Proves `OffCarrierErrorEstimateStatement` (`b3_offCarrierErrorEstimate_proof`): for a finite
coupling `π` moving each point at most three times its distance to the ADR carrier `Γ`,
`∫ d_P(y,v)^2 w_{σ,Γ}(y,R) dπ(y,v) ≤ 9 C 2^k π.fst(Γᶜ)`.

Proof. Write `d(y) = infEDist y Γ`. `π`-a.e. a
pair `(y,v)` satisfies `d_P(y,v) ≤ 3 d(y)`.

* If `y ∈ Γ`, then `d(y) = 0`, so `v = y` and the integrand is `0 · w = 0` even if `w = ⊤`
  (stationary pairs).
* If `y ∉ Γ`, then `0 < d(y) < ∞` (`Γ` closed and nonempty); write `d(y) = ofReal d`. For
  `r ≤ d`, `Γ ∩ P(y,r) = ∅`; for every `r > 0`, recentring at a point `γ ∈ Γ ∩ P(y,r)`
  (`P(y,r) ⊆ P(γ,2r)`) gives `σ(Γ ∩ P(y,r)) ≤ C (2r)^k` (`b3offest_ball_le`). Hence
  `r^{-k-2} σ(Γ ∩ P(y,r)) ≤ C 2^k r^{-2} 1_{r > d}` (`b3offest_integrand_le`), and
  `w_{σ,Γ}(y,R) ≤ C 2^k ∫_{(d,∞)} r^{-2} dr/r = C 2^k / (2 d^2)` by
  `lintegral_inv_pow_Ioi_scaleMeasure` with exponent `2` (`b3offest_weight_le`). With
  `d_P(y,v)^2 ≤ 9 d^2` the integrand is at most `9 C 2^k / 2` (`b3offest_pair_le`).

So the integrand is `π`-a.e. at most `(9 C 2^k / 2) 1_{Γᶜ}(y)`, and
`∫ ≤ (9 C 2^k / 2) π(Prod.fst ⁻¹' Γᶜ) = (9 C 2^k / 2) π.fst(Γᶜ)` (`b3offest_raw_bound`; the
factor `2` of `CouplingEnergyStatement` is separate). The statement follows from
`9 C 2^k / 2 ≤ 9 C 2^k`. The integrand need not be measurable: only `lintegral_mono_ae` is
used on it, and the dominating function is a measurable indicator.
-/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.SourceTransferTree

open ParabolicRectifiability.Foundations

/-- `r^{-k-2} C (2r)^k = C 2^k r^{-2}` in `[0,∞]`, for `r > 0` and `C ≥ 0`. -/
theorem b3offest_weight_algebra (k : ℕ) {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) * ENNReal.ofReal (C * (2 * r) ^ k) =
      ENNReal.ofReal (C * 2 ^ k) * (ENNReal.ofReal r)⁻¹ ^ 2 := by
  have h0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  rw [mul_pow, ← mul_assoc, ENNReal.ofReal_mul (p := C * 2 ^ k) (q := r ^ k) (by positivity),
    ENNReal.ofReal_pow hr.le]
  calc
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal (C * 2 ^ k) * ENNReal.ofReal r ^ k) =
        ENNReal.ofReal (C * 2 ^ k) * (ENNReal.ofReal r)⁻¹ ^ 2 *
          ((ENNReal.ofReal r)⁻¹ * ENNReal.ofReal r) ^ k := by
      rw [pow_add, mul_pow]
      ring
    _ = ENNReal.ofReal (C * 2 ^ k) * (ENNReal.ofReal r)⁻¹ ^ 2 := by
      rw [ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, one_pow, mul_one]

/-- Recentring: for every centre `y` (not necessarily on `Γ`) and `r > 0`,
`σ(Γ ∩ P(y,r)) ≤ C (2r)^k`, by upper ADR at a point `γ ∈ Γ ∩ P(y,r)` and
`P(y,r) ⊆ P(γ,2r)`. -/
theorem b3offest_ball_le {n k : ℕ} {C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hup : ∀ z ∈ Γ, ∀ r : ℝ, 0 < r → σ (Metric.ball z r) ≤ ENNReal.ofReal (C * r ^ k))
    (y : Space n) {r : ℝ} (hr : 0 < r) :
    σ (Γ ∩ Metric.ball y r) ≤ ENNReal.ofReal (C * (2 * r) ^ k) := by
  rcases (Γ ∩ Metric.ball y r).eq_empty_or_nonempty with h | ⟨γ, hγΓ, hγy⟩
  · rw [h, measure_empty]
    exact zero_le
  · have hsub : Γ ∩ Metric.ball y r ⊆ Metric.ball γ (2 * r) := by
      intro x hx
      have h1 : dist x y < r := Metric.mem_ball.1 hx.2
      have h2 : dist γ y < r := Metric.mem_ball.1 hγy
      rw [Metric.mem_ball]
      linarith [dist_triangle x y γ, dist_comm γ y]
    exact (measure_mono hsub).trans (hup γ hγΓ (2 * r) (by linarith))

/-- The radial integrand of the off-carrier error weight: if `infEDist y Γ = d > 0`, then
`r^{-k-2} σ(Γ ∩ P(y,r)) ≤ C 2^k r^{-2} 1_{r > d}` for every real `r`. -/
theorem b3offest_integrand_le {n k : ℕ} {C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hup : ∀ z ∈ Γ, ∀ r : ℝ, 0 < r → σ (Metric.ball z r) ≤ ENNReal.ofReal (C * r ^ k))
    (hC : 0 ≤ C) {y : Space n} {d : ℝ} (hd : 0 < d)
    (hyd : Metric.infEDist y Γ = ENNReal.ofReal d) (r : ℝ) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) * σ (Γ ∩ Metric.ball y r) ≤
      (Ioi d).indicator
        (fun s : ℝ => ENNReal.ofReal (C * 2 ^ k) * (ENNReal.ofReal s)⁻¹ ^ 2) r := by
  by_cases h : d < r
  · rw [indicator_of_mem (show r ∈ Ioi d from h)]
    have hr : 0 < r := hd.trans h
    calc
      (ENNReal.ofReal r)⁻¹ ^ (k + 2) * σ (Γ ∩ Metric.ball y r) ≤
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) * ENNReal.ofReal (C * (2 * r) ^ k) :=
        mul_le_mul' le_rfl (b3offest_ball_le hup y hr)
      _ = _ := b3offest_weight_algebra k hC hr
  · rw [not_lt] at h
    have hempty : Γ ∩ Metric.ball y r = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      have h1 : Metric.infEDist y Γ ≤ edist y x := Metric.infEDist_le_edist_of_mem hx.1
      have h2 : dist x y < r := Metric.mem_ball.1 hx.2
      rw [hyd, edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg, dist_comm] at h1
      linarith
    rw [hempty, measure_empty, mul_zero]
    exact zero_le

/-- The off-carrier error weight of a point at distance `d > 0` from `Γ`:
`w_{σ,Γ}(y,R) ≤ C 2^k / (2 d^2)` for every `R`. -/
theorem b3offest_weight_le {n k : ℕ} {C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hup : ∀ z ∈ Γ, ∀ r : ℝ, 0 < r → σ (Metric.ball z r) ≤ ENNReal.ofReal (C * r ^ k))
    (hC : 0 ≤ C) {y : Space n} {d : ℝ} (hd : 0 < d)
    (hyd : Metric.infEDist y Γ = ENNReal.ofReal d) (R : ℝ) :
    b3_errorWeight k σ Γ y R ≤ ENNReal.ofReal (C * 2 ^ k) * ENNReal.ofReal ((d ^ 2)⁻¹ / 2) := by
  unfold b3_errorWeight
  calc
    ∫⁻ r in Ioo 0 R, (ENNReal.ofReal r)⁻¹ ^ (k + 2) * σ (Γ ∩ Metric.ball y r) ∂scaleMeasure ≤
        ∫⁻ r in Ioo 0 R, (Ioi d).indicator
          (fun s : ℝ => ENNReal.ofReal (C * 2 ^ k) * (ENNReal.ofReal s)⁻¹ ^ 2) r
            ∂scaleMeasure :=
      setLIntegral_mono' measurableSet_Ioo fun r _ =>
        b3offest_integrand_le hup hC hd hyd r
    _ ≤ ∫⁻ r, (Ioi d).indicator
          (fun s : ℝ => ENNReal.ofReal (C * 2 ^ k) * (ENNReal.ofReal s)⁻¹ ^ 2) r
            ∂scaleMeasure :=
      setLIntegral_le_lintegral _ _
    _ = ∫⁻ r in Ioi d, ENNReal.ofReal (C * 2 ^ k) * (ENNReal.ofReal r)⁻¹ ^ 2 ∂scaleMeasure :=
      lintegral_indicator measurableSet_Ioi _
    _ = ENNReal.ofReal (C * 2 ^ k) * ∫⁻ r in Ioi d, (ENNReal.ofReal r)⁻¹ ^ 2 ∂scaleMeasure :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (C * 2 ^ k) * ENNReal.ofReal ((d ^ 2)⁻¹ / 2) := by
      rw [lintegral_inv_pow_Ioi_scaleMeasure 2 two_pos hd, Nat.cast_ofNat]

/-- The integrand bound for one pair: if `d_P(y,v) ≤ 3 d(y)`, then
`d_P(y,v)^2 w_{σ,Γ}(y,R) ≤ (9 C 2^k / 2) 1_{Γᶜ}(y)`. On `Γ` the pair is stationary and the
product is `0 · w = 0`. -/
theorem b3offest_pair_le {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hΓ : IsADRCarrier k c C Γ σ) {p : Space n × Space n}
    (hdisp : edist p.1 p.2 ≤ 3 * Metric.infEDist p.1 Γ) (R : ℝ) :
    edist p.1 p.2 ^ 2 * b3_errorWeight k σ Γ p.1 R ≤
      (Prod.fst ⁻¹' Γᶜ).indicator (fun _ => ENNReal.ofReal (9 * C * 2 ^ k / 2)) p := by
  by_cases hy : p.1 ∈ Γ
  · rw [Metric.infEDist_zero_of_mem hy, mul_zero, nonpos_iff_eq_zero] at hdisp
    rw [hdisp, zero_pow two_ne_zero, zero_mul]
    exact zero_le
  · rw [indicator_of_mem (show p ∈ Prod.fst ⁻¹' Γᶜ from hy)]
    have hpos : 0 < Metric.infEDist p.1 Γ := by
      rw [Metric.infEDist_pos_iff_notMem_closure, hΓ.isClosed.closure_eq]
      exact hy
    have htop : Metric.infEDist p.1 Γ ≠ ⊤ := Metric.infEDist_ne_top hΓ.nonempty
    have hyd : Metric.infEDist p.1 Γ = ENNReal.ofReal (Metric.infEDist p.1 Γ).toReal :=
      (ENNReal.ofReal_toReal htop).symm
    have hd : 0 < (Metric.infEDist p.1 Γ).toReal := ENNReal.toReal_pos hpos.ne' htop
    set d := (Metric.infEDist p.1 Γ).toReal with hd_def
    have hC : 0 ≤ C := hΓ.upper_pos.le
    have hC2 : 0 ≤ C * 2 ^ k := by positivity
    have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by norm_num
    have h1 : edist p.1 p.2 ^ 2 ≤ ENNReal.ofReal (9 * d ^ 2) := by
      calc
        edist p.1 p.2 ^ 2 ≤ (3 * Metric.infEDist p.1 Γ) ^ 2 := by
          rw [sq, sq]
          exact mul_le_mul' hdisp hdisp
        _ = ENNReal.ofReal (9 * d ^ 2) := by
          rw [hyd, h3, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_pow (by positivity)]
          congr 1
          ring
    have h2 := b3offest_weight_le (k := k) hΓ.upper hC hd hyd R
    calc
      edist p.1 p.2 ^ 2 * b3_errorWeight k σ Γ p.1 R ≤
          ENNReal.ofReal (9 * d ^ 2) *
            (ENNReal.ofReal (C * 2 ^ k) * ENNReal.ofReal ((d ^ 2)⁻¹ / 2)) :=
        mul_le_mul' h1 h2
      _ = ENNReal.ofReal (9 * d ^ 2 * (C * 2 ^ k * ((d ^ 2)⁻¹ / 2))) := by
        rw [← ENNReal.ofReal_mul hC2, ← ENNReal.ofReal_mul (p := 9 * d ^ 2) (by positivity)]
      _ = ENNReal.ofReal (9 * C * 2 ^ k / 2) := by
        congr 1
        rw [show 9 * d ^ 2 * (C * 2 ^ k * ((d ^ 2)⁻¹ / 2)) =
            9 * C * 2 ^ k / 2 * (d ^ 2 * (d ^ 2)⁻¹) by ring,
          mul_inv_cancel₀ (pow_ne_zero 2 hd.ne'), mul_one]

/-- **Raw off-carrier estimate**: under the hypotheses of `OffCarrierErrorEstimateStatement`,
`∫ d_P(y,v)^2 w_{σ,Γ}(y,R) dπ(y,v) ≤ (9 C 2^k / 2) π.fst(Γᶜ)` (the factor `2` of
`CouplingEnergyStatement` is separate). -/
theorem b3offest_raw_bound {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hΓ : IsADRCarrier k c C Γ σ) {π : Measure (Space n × Space n)}
    (hdisp : ∀ᵐ p ∂π, edist p.1 p.2 ≤ 3 * Metric.infEDist p.1 Γ) (R : ℝ) :
    ∫⁻ p, edist p.1 p.2 ^ 2 * b3_errorWeight k σ Γ p.1 R ∂π ≤
      ENNReal.ofReal (9 * C * 2 ^ k / 2) * π.fst Γᶜ := by
  have hmeas : MeasurableSet Γᶜ := hΓ.isClosed.measurableSet.compl
  calc
    _ ≤ ∫⁻ p, (Prod.fst ⁻¹' Γᶜ).indicator
          (fun _ => ENNReal.ofReal (9 * C * 2 ^ k / 2)) p ∂π := by
      refine lintegral_mono_ae ?_
      filter_upwards [hdisp] with p hp
      exact b3offest_pair_le hΓ hp R
    _ = ENNReal.ofReal (9 * C * 2 ^ k / 2) * π (Prod.fst ⁻¹' Γᶜ) :=
      lintegral_indicator_const (measurable_fst hmeas) _
    _ = ENNReal.ofReal (9 * C * 2 ^ k / 2) * π.fst Γᶜ := by
      rw [Measure.fst_apply hmeas]

/-- **Off-carrier error estimate** (`OffCarrierErrorEstimateStatement`). From the raw bound `b3offest_raw_bound` and
`9 C 2^k / 2 ≤ 9 C 2^k`. -/
theorem b3_offCarrierErrorEstimate_proof : OffCarrierErrorEstimateStatement := by
  intro n k c C Γ σ hΓ π _hπ hdisp R
  have hC2 : 0 < C * 2 ^ k := by
    have := hΓ.upper_pos
    positivity
  refine (b3offest_raw_bound hΓ hdisp R).trans ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end ParabolicRectifiability.Characterization.SourceTransferTree
