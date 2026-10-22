import ParabolicRectifiability.QuantitativeCharacterization.Statements.ApproximantComponents
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.MultiplicityBasics

/-! # The exponential tail of the multiplicity

Proof of `dp2_exponential_tail`, whose statement is `dp2_ExponentialTailStatement`: an exponential
series argument combined with Markov's inequality.

The factorial moments enter only as the hypothesis of the statement.
Write `m` for the multiplicity, `P₀ = P(a,R)`, `b = 2^k K`, `S = Σ_i R_i^k`, `A' = ofReal A`.

Proof idea (the nonnegative exponential series, integrated termwise).
1. Weights `c_p = ofReal (1 / (p! s^p))` (`dp2_et_weight`) and
   `E(z) = Σ_{p ≥ 0} m(z)^p c_p ∈ ℝ≥0∞`; this is `exp(m/s)` for finite `m` and `⊤` at `m = ⊤`.
   Since `K ≥ 0` and `s > b ≥ 0`, `s > 0`.
2. `∫_{P₀} E dμ = μ(P₀) + Σ_{p ≥ 0} c_{p+1} ∫_{P₀} m^{p+1} dμ` (`lintegral_tsum`,
   `lintegral_mul_const`, `tsum_eq_zero_add'`), and the moment hypothesis termwise gives
   `≤ μ(P₀) + A' S Σ_p ofReal (b^p / s^{p+1}) = μ(P₀) + A' S ofReal (1 / (s - b))`
   (`dp2_et_lintegral_series_le`; the real geometric series `dp2_et_hasSum_geom` with ratio
   `b / s < 1`). Everything is in `ℝ≥0∞`, so negative `A` (`ofReal A = 0`) and `S = ⊤` need no
   separate case.
3. On `{m > N}`, `m ≥ N`, so `E ≥ Σ_p ofReal ((N/s)^p / p!) = ofReal (exp (N/s))`
   (`dp2_et_exp_le_series`; `Real.exp_eq_exp_ℝ`, `NormedSpace.exp_eq_tsum_div`).
4. Markov (`mul_meas_ge_le_lintegral₀` for `μ⌊P₀`):
   `exp(N/s) μ(P₀ ∩ {m > N}) ≤ ∫_{P₀} E dμ`, and `𝒞.residual N P₀ = μ(P₀ ∩ {m > N})`; divide by
   `exp(N/s)` (finite, nonzero), with `exp(N/s)⁻¹ = exp(-N/s)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- The weight `c_p = 1 / (p! s^p)` of the exponential series of `m / s`, as an extended real. -/
def dp2_et_weight (s : ℝ) (p : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / ((p.factorial : ℝ) * s ^ p))

/-- The real geometric series `Σ_p b^p / s^{p+1} = 1 / (s - b)` for `0 ≤ b < s`. -/
theorem dp2_et_hasSum_geom {b s : ℝ} (hb : 0 ≤ b) (hbs : b < s) :
    HasSum (fun p : ℕ => b ^ p / s ^ (p + 1)) (1 / (s - b)) := by
  have hs : 0 < s := lt_of_le_of_lt hb hbs
  have h := (hasSum_geometric_of_lt_one (div_nonneg hb hs.le) ((div_lt_one hs).mpr hbs)).mul_left
    (1 / s)
  have hfun : (fun p : ℕ => 1 / s * (b / s) ^ p) = fun p : ℕ => b ^ p / s ^ (p + 1) := by
    funext p
    rw [div_pow, pow_succ]
    ring
  have hval : 1 / s * (1 - b / s)⁻¹ = 1 / (s - b) := by
    rw [one_sub_div hs.ne', inv_div, ← mul_div_assoc, one_div_mul_cancel hs.ne']
  rw [← hfun, ← hval]
  exact h

/-- One term of the tail series: `(p+1)! C b^p D c_{p+1} = C D b^p / s^{p+1}`. -/
theorem dp2_et_term_eq {b : ℝ} (hb : 0 ≤ b) (s : ℝ) (C D : ℝ≥0∞) (p : ℕ) :
    ((p + 1).factorial : ℝ≥0∞) * C * ENNReal.ofReal b ^ p * D * dp2_et_weight s (p + 1) =
      C * D * ENNReal.ofReal (b ^ p / s ^ (p + 1)) := by
  have hF : (0 : ℝ) < ((p + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have key : ((p + 1).factorial : ℝ≥0∞) * ENNReal.ofReal b ^ p * dp2_et_weight s (p + 1) =
      ENNReal.ofReal (b ^ p / s ^ (p + 1)) := by
    rw [dp2_et_weight, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow hb,
      ← ENNReal.ofReal_mul hF.le, ← ENNReal.ofReal_mul (mul_nonneg hF.le (pow_nonneg hb p))]
    congr 1
    rw [mul_one_div, mul_div_mul_left _ _ hF.ne']
  calc ((p + 1).factorial : ℝ≥0∞) * C * ENNReal.ofReal b ^ p * D * dp2_et_weight s (p + 1)
      = C * D * (((p + 1).factorial : ℝ≥0∞) * ENNReal.ofReal b ^ p *
          dp2_et_weight s (p + 1)) := by ring
    _ = C * D * ENNReal.ofReal (b ^ p / s ^ (p + 1)) := by rw [key]

/-- **The exponential series bound, abstract form.** If `f` is measurable and its moments satisfy
`∫ f^p dν ≤ p! C b^{p-1} D` for `p ≥ 1`, with `0 ≤ b < s`, then the integral of the exponential
series `Σ_p f^p c_p` is at most `ν(univ) + C D / (s - b)`. -/
theorem dp2_et_lintegral_series_le {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {f : X → ℝ≥0∞} (hf : Measurable f) {b s : ℝ} (hb : 0 ≤ b) (hbs : b < s) (C D : ℝ≥0∞)
    (hmom : ∀ p : ℕ, 1 ≤ p →
      ∫⁻ z, f z ^ p ∂ν ≤ (Nat.factorial p : ℝ≥0∞) * C * ENNReal.ofReal b ^ (p - 1) * D) :
    ∫⁻ z, ∑' p : ℕ, f z ^ p * dp2_et_weight s p ∂ν ≤
      ν univ + C * D * ENNReal.ofReal (1 / (s - b)) := by
  have hs : 0 < s := lt_of_le_of_lt hb hbs
  have hgeom := dp2_et_hasSum_geom hb hbs
  rw [lintegral_tsum fun p => ((hf.pow_const p).mul_const (dp2_et_weight s p)).aemeasurable]
  have hterm : ∀ p : ℕ, ∫⁻ z, f z ^ p * dp2_et_weight s p ∂ν =
      (∫⁻ z, f z ^ p ∂ν) * dp2_et_weight s p := fun p =>
    lintegral_mul_const _ (hf.pow_const p)
  rw [tsum_congr hterm, tsum_eq_zero_add' ENNReal.summable]
  have h0 : (∫⁻ z, f z ^ 0 ∂ν) * dp2_et_weight s 0 = ν univ := by
    simp [dp2_et_weight]
  refine add_le_add (le_of_eq h0) ?_
  calc ∑' p : ℕ, (∫⁻ z, f z ^ (p + 1) ∂ν) * dp2_et_weight s (p + 1)
      ≤ ∑' p : ℕ, C * D * ENNReal.ofReal (b ^ p / s ^ (p + 1)) := by
        refine ENNReal.tsum_le_tsum fun p => ?_
        calc (∫⁻ z, f z ^ (p + 1) ∂ν) * dp2_et_weight s (p + 1)
            ≤ ((Nat.factorial (p + 1) : ℝ≥0∞) * C * ENNReal.ofReal b ^ (p + 1 - 1) * D) *
                dp2_et_weight s (p + 1) := by
              exact mul_le_mul' (hmom (p + 1) (Nat.le_add_left 1 p)) le_rfl
          _ = C * D * ENNReal.ofReal (b ^ p / s ^ (p + 1)) := by
              rw [Nat.add_sub_cancel]
              exact dp2_et_term_eq hb s C D p
    _ = C * D * ∑' p : ℕ, ENNReal.ofReal (b ^ p / s ^ (p + 1)) := ENNReal.tsum_mul_left
    _ = C * D * ENNReal.ofReal (1 / (s - b)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun p => div_nonneg (pow_nonneg hb p) (pow_nonneg hs.le _)) hgeom.summable,
          hgeom.tsum_eq]

/-- The exponential series dominates `exp(N/s)` at every `x ≥ N`:
`ofReal (exp (N/s)) = Σ_p N^p c_p ≤ Σ_p x^p c_p`. -/
theorem dp2_et_exp_le_series {s : ℝ} (hs : 0 < s) (N : ℕ) {x : ℝ≥0∞}
    (hx : (N : ℝ≥0∞) ≤ x) :
    ENNReal.ofReal (Real.exp ((N : ℝ) / s)) ≤ ∑' p : ℕ, x ^ p * dp2_et_weight s p := by
  have hexp : Real.exp ((N : ℝ) / s) = ∑' p : ℕ, ((N : ℝ) / s) ^ p / (p.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hNs : (0 : ℝ) ≤ (N : ℝ) / s := div_nonneg (Nat.cast_nonneg N) hs.le
  rw [hexp, ENNReal.ofReal_tsum_of_nonneg
    (fun p => div_nonneg (pow_nonneg hNs p) (Nat.cast_nonneg _))
    (Real.summable_pow_div_factorial _)]
  refine ENNReal.tsum_le_tsum fun p => ?_
  calc ENNReal.ofReal (((N : ℝ) / s) ^ p / (p.factorial : ℝ))
      = (N : ℝ≥0∞) ^ p * dp2_et_weight s p := by
        rw [dp2_et_weight, ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_pow (Nat.cast_nonneg N),
          ← ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg N) p)]
        congr 1
        rw [div_pow, mul_one_div, div_div, mul_comm ((s : ℝ) ^ p)]
    _ ≤ x ^ p * dp2_et_weight s p := by gcongr

/-- **The exponential tail** (proof of `dp2_exponential_tail`, using Markov's inequality). -/
theorem dp2_exponential_tail_proof : dp2_ExponentialTailStatement := by
  intro n k K _L A μ a R 𝒞 hK hmom s hs N
  have hb : (0 : ℝ) ≤ 2 ^ k * K := mul_nonneg (pow_nonneg zero_le_two k) hK
  have hs0 : 0 < s := lt_of_le_of_lt hb hs
  have hB : (2 : ℝ≥0∞) ^ k * ENNReal.ofReal K = ENNReal.ofReal (2 ^ k * K) := by
    rw [ENNReal.ofReal_mul (pow_nonneg zero_le_two k), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat]
  have hf := dp2_measurable_multiplicity 𝒞
  have hmom' : ∀ p : ℕ, 1 ≤ p →
      ∫⁻ z, (𝒞.multiplicity z : ℝ≥0∞) ^ p ∂(μ.restrict (Metric.ball a R)) ≤
        (Nat.factorial p : ℝ≥0∞) * ENNReal.ofReal A * ENNReal.ofReal (2 ^ k * K) ^ (p - 1) *
          ∑' i, ENNReal.ofReal (𝒞.radius i) ^ k := by
    intro p hp
    rw [← hB]
    exact hmom p hp
  -- the integral of the exponential series over the root
  have hint := dp2_et_lintegral_series_le (μ.restrict (Metric.ball a R)) hf hb hs
    (ENNReal.ofReal A) (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) hmom'
  rw [Measure.restrict_apply_univ] at hint
  -- Markov for `μ⌊P₀` at the level `exp(N/s)`
  have hE : Measurable fun z =>
      ∑' p : ℕ, (𝒞.multiplicity z : ℝ≥0∞) ^ p * dp2_et_weight s p :=
    Measurable.tsum fun p => (hf.pow_const p).mul_const (dp2_et_weight s p)
  have hmarkov : ENNReal.ofReal (Real.exp ((N : ℝ) / s)) *
        μ.restrict (Metric.ball a R) {z | ENNReal.ofReal (Real.exp ((N : ℝ) / s)) ≤
          ∑' p : ℕ, (𝒞.multiplicity z : ℝ≥0∞) ^ p * dp2_et_weight s p} ≤
      ∫⁻ z, ∑' p : ℕ, (𝒞.multiplicity z : ℝ≥0∞) ^ p * dp2_et_weight s p
        ∂(μ.restrict (Metric.ball a R)) :=
    mul_meas_ge_le_lintegral₀ hE.aemeasurable _
  -- on `{m > N}` the series is at least `exp(N/s)`
  have hNle : ∀ z, (N : ℕ∞) < 𝒞.multiplicity z →
      (N : ℝ≥0∞) ≤ (𝒞.multiplicity z : ℝ≥0∞) := by
    intro z hz
    have h := ENat.toENNReal_le.mpr hz.le
    rwa [ENat.toENNReal_coe] at h
  have hX : μ (Metric.ball a R ∩ {z | (N : ℕ∞) < 𝒞.multiplicity z}) ≤
      μ.restrict (Metric.ball a R) {z | ENNReal.ofReal (Real.exp ((N : ℝ) / s)) ≤
        ∑' p : ℕ, (𝒞.multiplicity z : ℝ≥0∞) ^ p * dp2_et_weight s p} := by
    rw [Measure.restrict_apply' Metric.isOpen_ball.measurableSet]
    refine measure_mono fun z hz => ⟨?_, hz.1⟩
    exact dp2_et_exp_le_series hs0 N (hNle z hz.2)
  -- the residual at `P₀`
  have hres : 𝒞.residual N (Metric.ball a R) =
      μ (Metric.ball a R ∩ {z | (N : ℕ∞) < 𝒞.multiplicity z}) := by
    rw [RegularMixedCovering.residual, Measure.restrict_apply Metric.isOpen_ball.measurableSet,
      ← Set.inter_assoc, Set.inter_self]
  have hε0 : ENNReal.ofReal (Real.exp ((N : ℝ) / s)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hεtop : ENNReal.ofReal (Real.exp ((N : ℝ) / s)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hεinv : (ENNReal.ofReal (Real.exp ((N : ℝ) / s)))⁻¹ =
      ENNReal.ofReal (Real.exp (-(N : ℝ) / s)) := by
    rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_div]
  have hM : ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) *
        ENNReal.ofReal (1 / (s - 2 ^ k * K)) =
      ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) /
        ENNReal.ofReal (s - 2 ^ k * K) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (sub_pos.mpr hs), div_eq_mul_inv]
  rw [hres, ← hεinv, ← hM]
  calc μ (Metric.ball a R ∩ {z | (N : ℕ∞) < 𝒞.multiplicity z})
      = (ENNReal.ofReal (Real.exp ((N : ℝ) / s)))⁻¹ *
          (ENNReal.ofReal (Real.exp ((N : ℝ) / s)) *
            μ (Metric.ball a R ∩ {z | (N : ℕ∞) < 𝒞.multiplicity z})) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hε0 hεtop, one_mul]
    _ ≤ (ENNReal.ofReal (Real.exp ((N : ℝ) / s)))⁻¹ *
          (ENNReal.ofReal (Real.exp ((N : ℝ) / s)) *
            μ.restrict (Metric.ball a R) {z | ENNReal.ofReal (Real.exp ((N : ℝ) / s)) ≤
              ∑' p : ℕ, (𝒞.multiplicity z : ℝ≥0∞) ^ p * dp2_et_weight s p}) := by
        exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hX)
    _ ≤ (ENNReal.ofReal (Real.exp ((N : ℝ) / s)))⁻¹ *
          ∫⁻ z, ∑' p : ℕ, (𝒞.multiplicity z : ℝ≥0∞) ^ p * dp2_et_weight s p
            ∂(μ.restrict (Metric.ball a R)) := by
        exact mul_le_mul' le_rfl hmarkov
    _ ≤ (ENNReal.ofReal (Real.exp ((N : ℝ) / s)))⁻¹ *
          (μ (Metric.ball a R) + ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) *
            ENNReal.ofReal (1 / (s - 2 ^ k * K))) := by
        exact mul_le_mul' le_rfl hint

end ParabolicRectifiability.QuantitativeCharacterization
