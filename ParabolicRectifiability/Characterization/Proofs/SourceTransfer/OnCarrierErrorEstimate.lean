import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.TransferStatements
import ParabolicRectifiability.Measure.ScaleIntegrals

/-! # The on-carrier error estimate in Tonelli form

Proves `b3_onCarrierErrorEstimate : OnCarrierErrorEstimateStatement` as
`b3_onCarrierErrorEstimate_proof`.

Route. Write `Ξ_A = ⋃_i P(z_i, 20 r_i)` and
`D = Γ \ Ξ_A`. `π`-a.e. a pair either stays in place (then `d(y,v)^2 = 0` and
`0 · w = 0` even if `w = ⊤`) or has `y ∈ E_i ⊆ P(z_i, 5 r_i)` and `v ∈ P(z_i, r_i)`. In the
second case:

* `d(y,v) < 6 r_i`, so `d(y,v)^2 ≤ 36 r_i^2` (`b3onest_edist_sq_le`);
* a point `x ∈ D ∩ P(y,r)` has `20 r_i ≤ d(x,z_i) < r + 5 r_i`, so `D ∩ P(y,r) = ∅` unless
  `r > 15 r_i`, and then `D ∩ P(y,r) ⊆ P(z_i, 2r)`, whence by upper ADR at `z_i`
  `r^{-k-2} σ(D ∩ P(y,r)) ≤ C 2^k r^{-2} 1_{r > 15 r_i}` (`b3onest_integrand_le`);
* `w_{σ,D}(y,R) ≤ C 2^k ∫_{(15 r_i, ∞)} r^{-2} dr/r = C 2^k / (2 (15 r_i)^2)` by
  `lintegral_inv_pow_Ioi_scaleMeasure` with exponent `2` (`b3onest_weight_le`);
* hence `d(y,v)^2 w(y) ≤ 36 r_i^2 · C 2^k / (450 r_i^2) = 36 C 2^k / 450`
  (`b3onest_pair_le`).

So the integrand is `π`-a.e. at most the constant `36 C 2^k / 450`, and
`∫ ≤ (36 C 2^k / 450) π(univ) = (36 C 2^k / 450) ν(univ) = (36 C 2^k / 450) ν(Γ)`
(`π.fst = ν`, `ν Γᶜ = 0`). This raw bound is `b3onest_raw_bound`; it is kept separate from the
factor `2` of `CouplingEnergyStatement`. The statement follows from `36/450 ≤ 1`.

The disjointness and the measurability of the `E_i` are not needed: the constant bound is
integrated against the whole of `π`, whose total mass is `ν(univ) = ν(Γ)`.
-/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.SourceTransferTree

open ParabolicRectifiability.Foundations

/-- `r^{-k-2} C (2r)^k = C 2^k r^{-2}` in `[0,∞]`, for `r > 0` and `C ≥ 0`. -/
theorem b3onest_weight_algebra (k : ℕ) {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r) :
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

/-- The radial integrand of the error weight: for `y ∈ P(z_i, 5ρ)` and a set `D` avoiding
`P(z_i, 20ρ)`, `r^{-k-2} σ(D ∩ P(y,r)) ≤ C 2^k r^{-2} 1_{r > 15ρ}` for `r > 0`. -/
theorem b3onest_integrand_le {n k : ℕ} {C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hup : ∀ z ∈ Γ, ∀ r : ℝ, 0 < r → σ (Metric.ball z r) ≤ ENNReal.ofReal (C * r ^ k))
    (hC : 0 ≤ C) {D : Set (Space n)} {zi y : Space n} {ρ : ℝ} (hzi : zi ∈ Γ) (hρ : 0 < ρ)
    (hD : ∀ x ∈ D, 20 * ρ ≤ dist x zi) (hy : dist y zi < 5 * ρ) {r : ℝ} (hr : 0 < r) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) * σ (D ∩ Metric.ball y r) ≤
      (Ioi (15 * ρ)).indicator
        (fun s : ℝ => ENNReal.ofReal (C * 2 ^ k) * (ENNReal.ofReal s)⁻¹ ^ 2) r := by
  by_cases h : 15 * ρ < r
  · rw [indicator_of_mem (show r ∈ Ioi (15 * ρ) from h)]
    have hsub : D ∩ Metric.ball y r ⊆ Metric.ball zi (2 * r) := by
      intro x hx
      have hxy : dist x y < r := Metric.mem_ball.1 hx.2
      rw [Metric.mem_ball]
      linarith [dist_triangle x y zi]
    have hmeas : σ (D ∩ Metric.ball y r) ≤ ENNReal.ofReal (C * (2 * r) ^ k) :=
      (measure_mono hsub).trans (hup zi hzi (2 * r) (by linarith))
    calc
      (ENNReal.ofReal r)⁻¹ ^ (k + 2) * σ (D ∩ Metric.ball y r) ≤
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) * ENNReal.ofReal (C * (2 * r) ^ k) :=
        mul_le_mul' le_rfl hmeas
      _ = _ := b3onest_weight_algebra k hC hr
  · rw [not_lt] at h
    have hempty : D ∩ Metric.ball y r = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      have h20 := hD x hx.1
      have hxy : dist x y < r := Metric.mem_ball.1 hx.2
      linarith [dist_triangle x y zi]
    rw [hempty, measure_empty, mul_zero]
    exact zero_le

/-- The error weight of a point `y ∈ P(z_i, 5ρ)` with respect to a set `D` avoiding
`P(z_i, 20ρ)`: `w_{σ,D}(y,R) ≤ C 2^k / (2 (15ρ)^2)` for every `R`. -/
theorem b3onest_weight_le {n k : ℕ} {C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hup : ∀ z ∈ Γ, ∀ r : ℝ, 0 < r → σ (Metric.ball z r) ≤ ENNReal.ofReal (C * r ^ k))
    (hC : 0 ≤ C) {D : Set (Space n)} {zi y : Space n} {ρ : ℝ} (hzi : zi ∈ Γ) (hρ : 0 < ρ)
    (hD : ∀ x ∈ D, 20 * ρ ≤ dist x zi) (hy : dist y zi < 5 * ρ) (R : ℝ) :
    b3_errorWeight k σ D y R ≤
      ENNReal.ofReal (C * 2 ^ k) * ENNReal.ofReal (((15 * ρ) ^ 2)⁻¹ / 2) := by
  unfold b3_errorWeight
  calc
    ∫⁻ r in Ioo 0 R, (ENNReal.ofReal r)⁻¹ ^ (k + 2) * σ (D ∩ Metric.ball y r) ∂scaleMeasure ≤
        ∫⁻ r in Ioo 0 R, (Ioi (15 * ρ)).indicator
          (fun s : ℝ => ENNReal.ofReal (C * 2 ^ k) * (ENNReal.ofReal s)⁻¹ ^ 2) r
            ∂scaleMeasure :=
      setLIntegral_mono' measurableSet_Ioo fun r hr =>
        b3onest_integrand_le hup hC hzi hρ hD hy hr.1
    _ ≤ ∫⁻ r, (Ioi (15 * ρ)).indicator
          (fun s : ℝ => ENNReal.ofReal (C * 2 ^ k) * (ENNReal.ofReal s)⁻¹ ^ 2) r
            ∂scaleMeasure :=
      setLIntegral_le_lintegral _ _
    _ = ∫⁻ r in Ioi (15 * ρ), ENNReal.ofReal (C * 2 ^ k) * (ENNReal.ofReal r)⁻¹ ^ 2
            ∂scaleMeasure :=
      lintegral_indicator measurableSet_Ioi _
    _ = ENNReal.ofReal (C * 2 ^ k) *
          ∫⁻ r in Ioi (15 * ρ), (ENNReal.ofReal r)⁻¹ ^ 2 ∂scaleMeasure :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (C * 2 ^ k) * ENNReal.ofReal (((15 * ρ) ^ 2)⁻¹ / 2) := by
      rw [lintegral_inv_pow_Ioi_scaleMeasure 2 two_pos (by positivity), Nat.cast_ofNat]

/-- The squared displacement of a pair `y ∈ P(z_i, 5ρ)`, `v ∈ P(z_i, ρ)`:
`d(y,v)^2 ≤ 36 ρ^2`. -/
theorem b3onest_edist_sq_le {n : ℕ} {zi y v : Space n} {ρ : ℝ} (hρ : 0 < ρ)
    (hy : dist y zi < 5 * ρ) (hv : dist v zi < ρ) :
    edist y v ^ 2 ≤ ENNReal.ofReal (36 * ρ ^ 2) := by
  rw [edist_dist, ← ENNReal.ofReal_pow dist_nonneg]
  apply ENNReal.ofReal_le_ofReal
  have h6 : dist y v ≤ 6 * ρ := by
    linarith [dist_triangle y zi v, dist_comm zi v]
  have hsq := mul_le_mul h6 h6 dist_nonneg (by linarith : (0 : ℝ) ≤ 6 * ρ)
  nlinarith [hsq]

/-- The integrand bound for a moving pair: `y ∈ P(z_i, 5ρ)`, `v ∈ P(z_i, ρ)` and a set `D`
avoiding `P(z_i, 20ρ)` give `d(y,v)^2 w_{σ,D}(y,R) ≤ 36 C 2^k / 450`. -/
theorem b3onest_pair_le {n k : ℕ} {C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hup : ∀ z ∈ Γ, ∀ r : ℝ, 0 < r → σ (Metric.ball z r) ≤ ENNReal.ofReal (C * r ^ k))
    (hC : 0 ≤ C) {D : Set (Space n)} {zi y v : Space n} {ρ : ℝ} (hzi : zi ∈ Γ) (hρ : 0 < ρ)
    (hD : ∀ x ∈ D, 20 * ρ ≤ dist x zi) (hy : dist y zi < 5 * ρ) (hv : dist v zi < ρ)
    (R : ℝ) :
    edist y v ^ 2 * b3_errorWeight k σ D y R ≤ ENNReal.ofReal (36 * C * 2 ^ k / 450) := by
  have h1 := b3onest_edist_sq_le hρ hy hv
  have h2 := b3onest_weight_le hup hC hzi hρ hD hy R
  have hC2 : 0 ≤ C * 2 ^ k := by positivity
  calc
    edist y v ^ 2 * b3_errorWeight k σ D y R ≤
        ENNReal.ofReal (36 * ρ ^ 2) *
          (ENNReal.ofReal (C * 2 ^ k) * ENNReal.ofReal (((15 * ρ) ^ 2)⁻¹ / 2)) :=
      mul_le_mul' h1 h2
    _ = ENNReal.ofReal (36 * ρ ^ 2 * (C * 2 ^ k * (((15 * ρ) ^ 2)⁻¹ / 2))) := by
      rw [← ENNReal.ofReal_mul hC2, ← ENNReal.ofReal_mul (p := 36 * ρ ^ 2) (by positivity)]
    _ = ENNReal.ofReal (36 * C * 2 ^ k / 450) := by
      have hρ0 : ρ ≠ 0 := hρ.ne'
      congr 1
      rw [show 36 * ρ ^ 2 * (C * 2 ^ k * (((15 * ρ) ^ 2)⁻¹ / 2)) =
          36 * C * 2 ^ k / 450 * (ρ ^ 2 * (ρ ^ 2)⁻¹) by ring,
        mul_inv_cancel₀ (pow_ne_zero 2 hρ0), mul_one]

/-- **Raw on-carrier estimate**: under the hypotheses of `OnCarrierErrorEstimateStatement`,
`∫ d_P(y,v)^2 w_{σ, Γ \ Ξ_A}(y,R) dπ(y,v) ≤ (36 C 2^k / 450) ν(Γ)` (the exact
bound `(36/450) C 2^k ν(Γ)`; the factor `2` of `CouplingEnergyStatement` is separate). -/
theorem b3onest_raw_bound {n k : ℕ} {c C C₀ C₁ : ℝ} {Γ : Set (Space n)}
    {σ : Measure (Space n)} (hΓ : IsADRCarrier k c C Γ σ) {ν : Measure (Space n)}
    (hνc : ν Γᶜ = 0) {A : ℝ} {I : Set ℕ} {z : I → Space n} {r : I → ℝ}
    {E : I → Set (Space n)} (hdata : b3_IsReplacementData k C₀ C₁ Γ σ ν A I z r E)
    {π : Measure (Space n × Space n)} (hfst : π.fst = ν)
    (hsupp : ∀ᵐ p ∂π, (p.2 = p.1 ∧ p.1 ∈ adrGoodSet Γ ν k A) ∨
      ∃ i, p.1 ∈ E i ∧ p.2 ∈ Γ ∩ Metric.ball (z i) (r i)) (R : ℝ) :
    ∫⁻ p, edist p.1 p.2 ^ 2 *
        b3_errorWeight k σ (Γ \ ⋃ i, Metric.ball (z i) (20 * r i)) p.1 R ∂π ≤
      ENNReal.ofReal (36 * C * 2 ^ k / 450) * ν Γ := by
  obtain ⟨hzr, -, -, -, hE, -⟩ := hdata
  have hC : 0 ≤ C := hΓ.upper_pos.le
  have key : ∀ᵐ p ∂π, edist p.1 p.2 ^ 2 *
      b3_errorWeight k σ (Γ \ ⋃ i, Metric.ball (z i) (20 * r i)) p.1 R ≤
        ENNReal.ofReal (36 * C * 2 ^ k / 450) := by
    filter_upwards [hsupp] with p hp
    rcases hp with ⟨heq, -⟩ | ⟨i, hy, hv⟩
    · rw [heq, edist_self, zero_pow two_ne_zero, zero_mul]
      exact zero_le
    · have hD : ∀ x ∈ Γ \ ⋃ j, Metric.ball (z j) (20 * r j), 20 * r i ≤ dist x (z i) :=
        fun x hx => not_lt.1 fun h => hx.2 (mem_iUnion.2 ⟨i, Metric.mem_ball.2 h⟩)
      exact b3onest_pair_le hΓ.upper hC (hzr i).1 (hzr i).2 hD
        (Metric.mem_ball.1 (hE i hy).2) (Metric.mem_ball.1 hv.2) R
  have huniv : ν univ ≤ ν Γ :=
    calc
      ν univ = ν (Γ ∪ Γᶜ) := by rw [union_compl_self]
      _ ≤ ν Γ + ν Γᶜ := measure_union_le _ _
      _ = ν Γ := by rw [hνc, add_zero]
  calc
    _ ≤ ∫⁻ _p, ENNReal.ofReal (36 * C * 2 ^ k / 450) ∂π := lintegral_mono_ae key
    _ = ENNReal.ofReal (36 * C * 2 ^ k / 450) * π univ := lintegral_const _
    _ = ENNReal.ofReal (36 * C * 2 ^ k / 450) * ν univ := by rw [← hfst, Measure.fst_univ]
    _ ≤ ENNReal.ofReal (36 * C * 2 ^ k / 450) * ν Γ := mul_le_mul' le_rfl huniv

/-- **On-carrier error estimate**: `OnCarrierErrorEstimateStatement`. From the raw bound `b3onest_raw_bound` and
`36 C 2^k / 450 ≤ C 2^k`. -/
theorem b3_onCarrierErrorEstimate_proof : OnCarrierErrorEstimateStatement := by
  intro n k c C C₀ C₁ Γ σ hΓ ν _hν hνc A _hA I z r E hdata π _hπ hfst hsupp R
  have hC2 : 0 < C * 2 ^ k := by
    have := hΓ.upper_pos
    positivity
  refine (b3onest_raw_bound hΓ hνc hdata hfst hsupp R).trans ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end ParabolicRectifiability.Characterization.SourceTransferTree
