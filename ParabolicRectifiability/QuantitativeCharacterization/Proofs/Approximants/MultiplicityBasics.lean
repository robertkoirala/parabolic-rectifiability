import ParabolicRectifiability.QuantitativeCharacterization.Coverings

/-! # Multiplicity of a covering: measurability, model-ball growth and tails

Basic facts about the multiplicity of a regular mixed covering, used to build the root
approximants (`exists_root_approximants`, `approximant_canonical_limits`).

* `dp2_multiplicity_eq_tsum`, `dp2_measurable_multiplicity`,
  `dp2_measurableSet_multiplicity_le`, `dp2_measurableSet_lt_multiplicity`: the multiplicity
  `m = Σ_i 1_{P_i}` as a countable sum of indicators, hence Borel.
* `dp2_ball_growth_of_local`, `dp2_ball_growth_of_global`: the model-ball growth
  `μ(P_i) ≤ A R_i^k` from the growth hypotheses of `exists_root_approximants` (centres in
  `P(a,LR)`, so either `R_i ≤ 2LR` or `P_i ⊆ P(a_i,2LR)`) and of `approximant_canonical_limits`.
* `dp2_ae_multiplicity_lt_top`: the first moment (`p = 1`) and `Σ_i R_i^k ≤ K R^k < ∞` give
  `m < ∞` almost everywhere on the root.
* `dp2_relativeTail_of_exponentialTail`, `dp2_absoluteTail_of_exponentialTail`: the two tail
  conclusions of `exists_root_approximants` from the exponential tail bound
  (`dp2_ExponentialTailStatement`) at `s = (2^k + A²) K` and `s = (2^k + 1) K`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

variable {n k : ℕ} {K L : ℝ} {μ : Measure (Space n)} {a : Space n} {R : ℝ}

/-- The model balls are open, hence Borel. -/
theorem dp2_measurableSet_ball (𝒞 : RegularMixedCovering k K L μ a R) (i : 𝒞.index) :
    MeasurableSet (𝒞.ball i) :=
  Metric.isOpen_ball.measurableSet

/-- The multiplicity, as an extended real, is the countable sum of the indicators of the model
balls. -/
theorem dp2_multiplicity_eq_tsum (𝒞 : RegularMixedCovering k K L μ a R) (z : Space n) :
    (𝒞.multiplicity z : ℝ≥0∞) = ∑' i, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z := by
  rw [RegularMixedCovering.multiplicity, ← ENNReal.tsum_set_one,
    tsum_subtype {i : 𝒞.index | z ∈ 𝒞.ball i} (fun _ => (1 : ℝ≥0∞))]
  congr 1

/-- The multiplicity is Borel. -/
theorem dp2_measurable_multiplicity (𝒞 : RegularMixedCovering k K L μ a R) :
    Measurable fun z => (𝒞.multiplicity z : ℝ≥0∞) := by
  have h : (fun z => (𝒞.multiplicity z : ℝ≥0∞)) =
      fun z => ∑' i, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z :=
    funext (dp2_multiplicity_eq_tsum 𝒞)
  rw [h]
  exact Measurable.tsum fun i => measurable_const.indicator (dp2_measurableSet_ball 𝒞 i)

/-- The level sets `{m ≤ N}` are Borel. -/
theorem dp2_measurableSet_multiplicity_le (𝒞 : RegularMixedCovering k K L μ a R) (N : ℕ) :
    MeasurableSet {z | 𝒞.multiplicity z ≤ (N : ℕ∞)} := by
  have h : {z | 𝒞.multiplicity z ≤ (N : ℕ∞)} =
      {z | (𝒞.multiplicity z : ℝ≥0∞) ≤ (N : ℝ≥0∞)} := by
    ext z
    simp only [Set.mem_ofPred_eq, ENat.toENNReal_le_natCast]
  rw [h]
  exact measurableSet_le (dp2_measurable_multiplicity 𝒞) measurable_const

/-- The superlevel sets `{m > N}` are Borel. -/
theorem dp2_measurableSet_lt_multiplicity (𝒞 : RegularMixedCovering k K L μ a R) (N : ℕ) :
    MeasurableSet {z | (N : ℕ∞) < 𝒞.multiplicity z} := by
  have h : {z | (N : ℕ∞) < 𝒞.multiplicity z} =
      {z | (N : ℝ≥0∞) < (𝒞.multiplicity z : ℝ≥0∞)} := by
    ext z
    simp only [Set.mem_ofPred_eq, ENat.natCast_lt_toENNReal]
  rw [h]
  exact measurableSet_lt measurable_const (dp2_measurable_multiplicity 𝒞)

/-- Model-ball growth from the local growth hypothesis of `exists_root_approximants`: every model ball is
support-centred inside `P(a,LR)`; if `R_i ≤ 2LR` apply the growth at `(a_i, R_i)`, otherwise
`P_i ⊆ P(a,LR) ⊆ P(a_i, 2LR)` and `(2LR)^k ≤ R_i^k`. -/
theorem dp2_ball_growth_of_local (𝒞 : RegularMixedCovering k K L μ a R) {A : ℝ} (hA : 0 ≤ A)
    (hL : 1 ≤ L) (hR : 0 < R)
    (hgrowth : ∀ b ∈ μ.support ∩ Metric.ball a (2 * L * R), ∀ s : ℝ, 0 < s → s ≤ 2 * L * R →
      μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k)) (i : 𝒞.index) :
    μ (𝒞.ball i) ≤ ENNReal.ofReal (A * 𝒞.radius i ^ k) := by
  have hLR : 0 < L * R := mul_pos (by linarith) hR
  have h2 : L * R ≤ 2 * L * R := by linarith
  have hci : 𝒞.center i ∈ Metric.ball a (L * R) :=
    𝒞.ball_subset i (Metric.mem_ball_self (𝒞.radius_pos i))
  have hci2 : 𝒞.center i ∈ μ.support ∩ Metric.ball a (2 * L * R) :=
    ⟨𝒞.center_mem_support i, Metric.ball_subset_ball h2 hci⟩
  rcases le_or_gt (𝒞.radius i) (2 * L * R) with hr | hr
  · exact hgrowth _ hci2 _ (𝒞.radius_pos i) hr
  · have hsub : 𝒞.ball i ⊆ Metric.ball (𝒞.center i) (2 * L * R) := by
      intro z hz
      have h1 : z ∈ Metric.ball a (L * R) := 𝒞.ball_subset i hz
      rw [Metric.mem_ball] at h1 hci ⊢
      calc dist z (𝒞.center i) ≤ dist z a + dist a (𝒞.center i) := dist_triangle _ _ _
        _ = dist z a + dist (𝒞.center i) a := by rw [dist_comm a]
        _ < L * R + L * R := add_lt_add h1 hci
        _ = 2 * L * R := by ring
    calc μ (𝒞.ball i) ≤ μ (Metric.ball (𝒞.center i) (2 * L * R)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (A * (2 * L * R) ^ k) := hgrowth _ hci2 _ (by linarith) le_rfl
      _ ≤ ENNReal.ofReal (A * 𝒞.radius i ^ k) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) hr.le k) hA)

/-- Model-ball growth from the global support-centred growth hypothesis of
`approximant_canonical_limits`. -/
theorem dp2_ball_growth_of_global (𝒞 : RegularMixedCovering k K L μ a R) {A : ℝ}
    (hgrowth : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r →
      μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) (i : 𝒞.index) :
    μ (𝒞.ball i) ≤ ENNReal.ofReal (A * 𝒞.radius i ^ k) :=
  hgrowth _ (𝒞.center_mem_support i) _ (𝒞.radius_pos i)

/-- Finite multiplicity almost everywhere on the root from the first moment: the right side is finite because `Σ_i R_i^k ≤ K R^k` (`root_packing`). -/
theorem dp2_ae_multiplicity_lt_top (𝒞 : RegularMixedCovering k K L μ a R) {A : ℝ}
    (hmom : ∫⁻ z in Metric.ball a R, (𝒞.multiplicity z : ℝ≥0∞) ^ 1 ∂μ ≤
      (Nat.factorial 1 : ℝ≥0∞) * ENNReal.ofReal A * (2 ^ k * ENNReal.ofReal K) ^ (1 - 1) *
        ∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) :
    ∀ᵐ z ∂μ, z ∈ Metric.ball a R → 𝒞.multiplicity z < ⊤ := by
  have hS : ∑' i, ENNReal.ofReal (𝒞.radius i) ^ k ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top 𝒞.root_packing
  have hrhs : (Nat.factorial 1 : ℝ≥0∞) * ENNReal.ofReal A * (2 ^ k * ENNReal.ofReal K) ^ (1 - 1) *
      ∑' i, ENNReal.ofReal (𝒞.radius i) ^ k ≠ ⊤ := by
    simp only [Nat.factorial_one, Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_one]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS
  have hae := ae_lt_top ((dp2_measurable_multiplicity 𝒞).pow_const 1)
    (ne_top_of_le_ne_top hrhs hmom)
  rw [ae_restrict_iff' measurableSet_ball] at hae
  filter_upwards [hae] with z hz hzP
  have h1 := hz hzP
  rw [pow_one] at h1
  exact ENat.toENNReal_lt_top.1 h1

/-- The relative tail `C_tail = 2^k + A²` of `exists_root_approximants`, from the exponential
tail bound at `s = (2^k + A²) K`, the root packing `S ≤ K R^k` and the root lower bound
`A⁻¹ R^k ≤ μ(P₀)`: `A S / (A² K) ≤ A⁻¹ R^k ≤ μ(P₀)`. -/
theorem dp2_relativeTail_of_exponentialTail (𝒞 : RegularMixedCovering k K L μ a R) {A : ℝ}
    (hA : 1 ≤ A) (hK : 1 ≤ K)
    (htail : ∀ s : ℝ, 2 ^ k * K < s → ∀ N : ℕ,
      𝒞.residual N (Metric.ball a R) ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) / s)) *
          (μ (Metric.ball a R) +
            ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) /
              ENNReal.ofReal (s - 2 ^ k * K)))
    (hlow : ENNReal.ofReal (A⁻¹ * R ^ k) ≤ μ (Metric.ball a R)) :
    𝒞.RelativeTail ((2 : ℝ) ^ k + A ^ 2) := by
  intro N
  have hK0 : 0 < K := by linarith
  have hA0 : 0 < A := by linarith
  have hA2K : 0 < A ^ 2 * K := mul_pos (pow_pos hA0 2) hK0
  have hexp : ((2 : ℝ) ^ k + A ^ 2) * K = 2 ^ k * K + A ^ 2 * K := by ring
  have hs : (2 : ℝ) ^ k * K < ((2 : ℝ) ^ k + A ^ 2) * K := by rw [hexp]; linarith
  have h := htail _ hs N
  rw [show ((2 : ℝ) ^ k + A ^ 2) * K - 2 ^ k * K = A ^ 2 * K by ring] at h
  have hreal : A * (K * R ^ k) / (A ^ 2 * K) = A⁻¹ * R ^ k := by
    rw [inv_mul_eq_div, div_eq_div_iff hA2K.ne' hA0.ne']
    ring
  have hkey : ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) /
      ENNReal.ofReal (A ^ 2 * K) ≤ μ (Metric.ball a R) := by
    calc ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) / ENNReal.ofReal (A ^ 2 * K)
        ≤ ENNReal.ofReal A * ENNReal.ofReal (K * R ^ k) / ENNReal.ofReal (A ^ 2 * K) :=
          ENNReal.div_le_div_right (mul_le_mul_right 𝒞.root_packing _) _
      _ = ENNReal.ofReal (A⁻¹ * R ^ k) := by
          rw [← ENNReal.ofReal_mul hA0.le, ← ENNReal.ofReal_div_of_pos hA2K, hreal]
      _ ≤ μ (Metric.ball a R) := hlow
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  calc 𝒞.residual N (Metric.ball a R)
      ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / (((2 : ℝ) ^ k + A ^ 2) * K))) *
          (μ (Metric.ball a R) + μ (Metric.ball a R)) :=
        h.trans (mul_le_mul_right (add_le_add le_rfl hkey) _)
    _ = ENNReal.ofReal (2 * Real.exp (-(N : ℝ) / (((2 : ℝ) ^ k + A ^ 2) * K))) *
          μ (Metric.ball a R) := by
        rw [ENNReal.ofReal_mul zero_le_two, h2, ← two_mul]
        ring

/-- The absolute tail `C_abs = max(2A, 2^k + 1)` of `exists_root_approximants`, from the
exponential tail bound at `s = (2^k + 1) K`, the root packing `S ≤ K R^k` and the root upper
bound `μ(P₀) ≤ A R^k` (so that `∫_{P₀} e^{m/s} dμ ≤ 2 A R^k`). -/
theorem dp2_absoluteTail_of_exponentialTail (𝒞 : RegularMixedCovering k K L μ a R) {A : ℝ}
    (hA : 1 ≤ A) (hK : 1 ≤ K) (hR : 0 < R)
    (htail : ∀ s : ℝ, 2 ^ k * K < s → ∀ N : ℕ,
      𝒞.residual N (Metric.ball a R) ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) / s)) *
          (μ (Metric.ball a R) +
            ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) /
              ENNReal.ofReal (s - 2 ^ k * K)))
    (hroot : μ (Metric.ball a R) ≤ ENNReal.ofReal (A * R ^ k)) (N : ℕ) :
    𝒞.residual N (Metric.ball a R) ≤
      ENNReal.ofReal (max (2 * A) ((2 : ℝ) ^ k + 1) * R ^ k *
        Real.exp (-(N : ℝ) / (max (2 * A) ((2 : ℝ) ^ k + 1) * K))) := by
  have hK0 : 0 < K := by linarith
  have hA0 : 0 < A := by linarith
  have hexp : ((2 : ℝ) ^ k + 1) * K = 2 ^ k * K + K := by ring
  have hs : (2 : ℝ) ^ k * K < ((2 : ℝ) ^ k + 1) * K := by rw [hexp]; linarith
  have h := htail _ hs N
  rw [show ((2 : ℝ) ^ k + 1) * K - 2 ^ k * K = K by ring] at h
  have hRk : 0 ≤ R ^ k := pow_nonneg hR.le k
  have hreal : A * (K * R ^ k) / K = A * R ^ k := by
    rw [div_eq_iff hK0.ne']
    ring
  have hkey : ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) / ENNReal.ofReal K ≤
      ENNReal.ofReal (A * R ^ k) := by
    calc ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) / ENNReal.ofReal K
        ≤ ENNReal.ofReal A * ENNReal.ofReal (K * R ^ k) / ENNReal.ofReal K :=
          ENNReal.div_le_div_right (mul_le_mul_right 𝒞.root_packing _) _
      _ = ENNReal.ofReal (A * R ^ k) := by
          rw [← ENNReal.ofReal_mul hA0.le, ← ENNReal.ofReal_div_of_pos hK0, hreal]
  have hARk : 0 ≤ A * R ^ k := mul_nonneg hA0.le hRk
  have hsum : μ (Metric.ball a R) +
      ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) / ENNReal.ofReal K ≤
      ENNReal.ofReal (2 * A * R ^ k) := by
    calc μ (Metric.ball a R) +
          ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) / ENNReal.ofReal K
        ≤ ENNReal.ofReal (A * R ^ k) + ENNReal.ofReal (A * R ^ k) := add_le_add hroot hkey
      _ = ENNReal.ofReal (2 * A * R ^ k) := by
          rw [← ENNReal.ofReal_add hARk hARk]
          congr 1
          ring
  have hC1 : 2 * A ≤ max (2 * A) ((2 : ℝ) ^ k + 1) := le_max_left _ _
  have hC2 : (2 : ℝ) ^ k + 1 ≤ max (2 * A) ((2 : ℝ) ^ k + 1) := le_max_right _ _
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k + 1 := by positivity
  have hpos : 0 < ((2 : ℝ) ^ k + 1) * K := mul_pos h2k hK0
  have hexpb : Real.exp (-(N : ℝ) / (((2 : ℝ) ^ k + 1) * K)) ≤
      Real.exp (-(N : ℝ) / (max (2 * A) ((2 : ℝ) ^ k + 1) * K)) := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) hpos
      (mul_le_mul_of_nonneg_right hC2 hK0.le)
  calc 𝒞.residual N (Metric.ball a R)
      ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / (((2 : ℝ) ^ k + 1) * K))) *
          ENNReal.ofReal (2 * A * R ^ k) :=
        h.trans (mul_le_mul_right hsum _)
    _ = ENNReal.ofReal (Real.exp (-(N : ℝ) / (((2 : ℝ) ^ k + 1) * K)) * (2 * A * R ^ k)) :=
        (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    _ ≤ ENNReal.ofReal (max (2 * A) ((2 : ℝ) ^ k + 1) * R ^ k *
          Real.exp (-(N : ℝ) / (max (2 * A) ((2 : ℝ) ^ k + 1) * K))) := by
        apply ENNReal.ofReal_le_ofReal
        calc Real.exp (-(N : ℝ) / (((2 : ℝ) ^ k + 1) * K)) * (2 * A * R ^ k)
            ≤ Real.exp (-(N : ℝ) / (max (2 * A) ((2 : ℝ) ^ k + 1) * K)) *
                (max (2 * A) ((2 : ℝ) ^ k + 1) * R ^ k) :=
              mul_le_mul hexpb (mul_le_mul_of_nonneg_right hC1 hRk)
                (mul_nonneg (mul_nonneg zero_le_two hA0.le) hRk) (Real.exp_pos _).le
          _ = max (2 * A) ((2 : ℝ) ^ k + 1) * R ^ k *
                Real.exp (-(N : ℝ) / (max (2 * A) ((2 : ℝ) ^ k + 1) * K)) := by ring

end ParabolicRectifiability.QuantitativeCharacterization
