import ParabolicRectifiability.Metric.Hausdorff

/-! # Positive upper density of finite-Hausdorff restrictions

Proves `b4_hausdorff_restrict_ball_lower_bound_proof`: for a Borel set `F` of finite `H_P^k`
measure, `H_P^k`-almost every point of `F` has a positive lower bound `H_P^k(F ∩ B(z,r)) ≥ c r^k`
along arbitrarily small radii, with `c` depending only on `k`.

Throughout, `μH[k]` is Mathlib's *unnormalized* diameter-power Hausdorff measure, which is
`hausdorffP n k` on `Space n`; no normalizing constant `γ_k` enters.

## The domination bridge

`b4p2_outerMeasure_le_ofReal_mul_hausdorffMeasure`: let `μ` be an outer measure on a metric
space and `A` a set (no measurability). If `μ` has no mass at the points of `A` and
`μ (A ∩ B(z,r)) ≤ c' r^k` for all `z ∈ A` and `0 < r < r₀`, then `μ A ≤ c' 2^k μH[k] A`.
Route: the restricted outer measure `s ↦ μ (s ∩ A)` is at most
`c' 2^k (diam s)^k` on every set of diameter at most `r₀ / 4` (`OuterMeasure.le_mkMetric`),
and `OuterMeasure.mkMetric_smul` pulls the constant out of the Hausdorff construction.
A set of positive diameter `d ≤ r₀/4` meeting `A` at `z` lies in `B(z, 2d)` with `2d < r₀`;
a set of zero diameter meeting `A` at `z` is contained in `{z}`.

`b4p2_restrict_hausdorffMeasure_le` specializes to `μ = μH[k]⌊F` with `k ≥ 1`, where the
singleton masses vanish by singleton nullity of `μH[k]`.

## The statement

With `c' = 2^{-(k+2)}` and `c = 2^{-(k+3)}` (so `c' 2^k = 1/4`), the bad classes
`A_j = {z ∈ F : ν(B(z,r)) ≤ c' r^k for all 0 < r < 1/(j+1)}`, `ν = μH[k]⌊F`, satisfy
`H(A_j) = ν(A_j) ≤ ¼ H(A_j)` (`Measure.restrict_apply' hF`, `A_j ⊆ F`) and `H(A_j) ≤ H(F) < ∞`,
so they are null (`b4p2_badClass_null`). A point of `F` where the conclusion fails lies in some
`A_j`, and `ν(Fᶜ) = 0`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

section Bridge

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Small-ball-to-Hausdorff domination bridge** (outer-measure form).

Let `μ` be an outer measure and `A` an arbitrary set. If `μ {z} = 0` for `z ∈ A` and
`μ (A ∩ B(z,r)) ≤ c' r^k` for every `z ∈ A` and `0 < r < r₀`, then
`μ A ≤ c' 2^k μH[k] A`. Zero-diameter covering sets are handled by the singleton hypothesis;
sets of positive diameter `d ≤ r₀/4` are recentred in the ball of radius `2d < r₀`. -/
theorem b4p2_outerMeasure_le_ofReal_mul_hausdorffMeasure
    (μ : OuterMeasure X) (k : ℕ) (A : Set X) {c' r₀ : ℝ} (hc' : 0 < c') (hr₀ : 0 < r₀)
    (hsing : ∀ z ∈ A, μ {z} = 0)
    (hball : ∀ z ∈ A, ∀ r : ℝ, 0 < r → r < r₀ →
      μ (A ∩ Metric.ball z r) ≤ ENNReal.ofReal (c' * r ^ k)) :
    μ A ≤ ENNReal.ofReal (c' * 2 ^ k) * (Measure.hausdorffMeasure (k : ℝ) : Measure X) A := by
  have hCpos : 0 < c' * 2 ^ k := mul_pos hc' (pow_pos two_pos k)
  have hC0 : ENNReal.ofReal (c' * 2 ^ k) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hCpos
  have hCtop : ENNReal.ofReal (c' * 2 ^ k) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmesh : (0 : ℝ) < r₀ / 4 := div_pos hr₀ (by norm_num)
  -- The restricted outer measure `s ↦ μ (s ∩ A)` is dominated on sets of small diameter.
  have hle : OuterMeasure.restrict A μ ≤
      OuterMeasure.mkMetric (ENNReal.ofReal (c' * 2 ^ k) • fun d : ℝ≥0∞ => d ^ (k : ℝ)) := by
    refine OuterMeasure.le_mkMetric _ _ (ENNReal.ofReal (r₀ / 4))
      (ENNReal.ofReal_pos.2 hmesh) ?_
    intro s hs
    rw [OuterMeasure.restrict_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rcases (s ∩ A).eq_empty_or_nonempty with hsA | ⟨z, hzs, hzA⟩
    · rw [hsA, measure_empty]
      exact zero_le
    by_cases hd0 : Metric.ediam s = 0
    · -- Zero diameter: `s ∩ A ⊆ {z}`, which carries no mass.
      have hsub : s ∩ A ⊆ {z} := fun y hy =>
        (Metric.ediam_eq_zero_iff.1 hd0) hy.1 hzs
      rw [measure_mono_null hsub (hsing z hzA)]
      exact zero_le
    -- Positive diameter `d ≤ r₀ / 4`: recentre in the ball of radius `2 d < r₀`.
    have hdtop : Metric.ediam s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
    have hdpos : 0 < (Metric.ediam s).toReal := ENNReal.toReal_pos hd0 hdtop
    have hdle : (Metric.ediam s).toReal ≤ r₀ / 4 := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
      rwa [ENNReal.toReal_ofReal hmesh.le] at h
    have hsub : s ∩ A ⊆ A ∩ Metric.ball z (2 * (Metric.ediam s).toReal) := by
      intro y hy
      refine ⟨hy.2, ?_⟩
      rw [Metric.mem_ball, dist_edist]
      have h1 : (edist y z).toReal ≤ (Metric.ediam s).toReal :=
        ENNReal.toReal_mono hdtop (Metric.edist_le_ediam_of_mem hy.1 hzs)
      linarith
    calc μ (s ∩ A) ≤ μ (A ∩ Metric.ball z (2 * (Metric.ediam s).toReal)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (c' * (2 * (Metric.ediam s).toReal) ^ k) :=
          hball z hzA _ (mul_pos two_pos hdpos) (by linarith)
      _ = ENNReal.ofReal (c' * 2 ^ k) * ENNReal.ofReal (Metric.ediam s).toReal ^ k := by
          rw [← ENNReal.ofReal_pow hdpos.le, ← ENNReal.ofReal_mul (p := c' * 2 ^ k) hCpos.le]
          congr 1
          ring
      _ = ENNReal.ofReal (c' * 2 ^ k) * Metric.ediam s ^ (k : ℝ) := by
          rw [ENNReal.rpow_natCast, ENNReal.ofReal_toReal hdtop]
  have h := hle A
  rw [OuterMeasure.restrict_apply, Set.inter_self, OuterMeasure.mkMetric_smul _ hCtop hC0,
    smul_apply, smul_eq_mul, OuterMeasure.coe_mkMetric] at h
  exact h

/-- **The bridge for restrictions of Hausdorff measure** (`k ≥ 1`).

For any set `F` and any set `A`, if `(μH[k]⌊F)(B(z,r)) ≤ c' r^k` for every `z ∈ A` and
`0 < r < r₀`, then `(μH[k]⌊F)(A) ≤ c' 2^k μH[k](A)`. The zero-diameter covering sets are
handled by singleton nullity of `μH[k]` for `k ≥ 1`. -/
theorem b4p2_restrict_hausdorffMeasure_le
    (k : ℕ) (hk : 1 ≤ k) (F A : Set X) {c' r₀ : ℝ} (hc' : 0 < c') (hr₀ : 0 < r₀)
    (hball : ∀ z ∈ A, ∀ r : ℝ, 0 < r → r < r₀ →
      (Measure.hausdorffMeasure (k : ℝ) : Measure X).restrict F (Metric.ball z r) ≤
        ENNReal.ofReal (c' * r ^ k)) :
    (Measure.hausdorffMeasure (k : ℝ) : Measure X).restrict F A ≤
      ENNReal.ofReal (c' * 2 ^ k) * (Measure.hausdorffMeasure (k : ℝ) : Measure X) A := by
  have : NullSingletonClass (Measure.hausdorffMeasure (k : ℝ) : Measure X) :=
    Measure.nullSingletonClass_hausdorff X (Nat.cast_pos.2 hk)
  exact b4p2_outerMeasure_le_ofReal_mul_hausdorffMeasure
    ((Measure.hausdorffMeasure (k : ℝ) : Measure X).restrict F).toOuterMeasure k A hc' hr₀
    (fun z _ => measure_singleton (μ := (Measure.hausdorffMeasure (k : ℝ) : Measure X).restrict F) z)
    (fun z hz r hr hrr => le_trans
      (measure_mono (μ := (Measure.hausdorffMeasure (k : ℝ) : Measure X).restrict F)
        inter_subset_right)
      (hball z hz r hr hrr))

end Bridge

/-- `c' 2^k = 1/4` for `c' = 2^{-(k+2)}`. -/
theorem b4p2_const_mul_two_pow (k : ℕ) : ((2 : ℝ) ^ (k + 2))⁻¹ * 2 ^ k = 1 / 4 := by
  have h2 : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [pow_add, mul_inv, mul_right_comm, inv_mul_cancel₀ h2, one_mul]
  norm_num

/-- `x ≤ ¼ x` forces `x = 0` for finite `x`. -/
theorem b4p2_eq_zero_of_le_quarter {x : ℝ≥0∞} (hx : x ≠ ⊤)
    (h : x ≤ ENNReal.ofReal (1 / 4) * x) : x = 0 := by
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at h'
  have h0 : x.toReal = 0 := by
    have := ENNReal.toReal_nonneg (a := x)
    linarith
  rcases (ENNReal.toReal_eq_zero_iff x).1 h0 with h1 | h1
  · exact h1
  · exact absurd h1 hx

/-- **The bad classes are null.** For Borel `F` with `H_P^k(F) < ∞` and `k ≥ 1`, the set of
points of `F` at which `ν(B(z,r)) ≤ 2^{-(k+2)} r^k` for every `0 < r < 1/(j+1)`
(`ν = H_P^k⌊F`) has Hausdorff measure zero. No measurability of the bad class is used. -/
theorem b4p2_badClass_null {n k : ℕ} (hk : 1 ≤ k) {F : Set (Space n)} (hF : MeasurableSet F)
    (hFfin : hausdorffP n k F < ⊤) (j : ℕ) :
    hausdorffP n k {z | z ∈ F ∧ ∀ r : ℝ, 0 < r → r < 1 / (j + 1) →
        (hausdorffP n k).restrict F (Metric.ball z r) ≤
          ENNReal.ofReal ((2 ^ (k + 2))⁻¹ * r ^ k)} = 0 := by
  set A : Set (Space n) := {z | z ∈ F ∧ ∀ r : ℝ, 0 < r → r < 1 / (j + 1) →
      (hausdorffP n k).restrict F (Metric.ball z r) ≤
        ENNReal.ofReal ((2 ^ (k + 2))⁻¹ * r ^ k)} with hA
  have hAF : A ⊆ F := fun z hz => hz.1
  have hbridge : (hausdorffP n k).restrict F A ≤
      ENNReal.ofReal (((2 : ℝ) ^ (k + 2))⁻¹ * 2 ^ k) * hausdorffP n k A :=
    b4p2_restrict_hausdorffMeasure_le (X := Space n) k hk F A
      (c' := ((2 : ℝ) ^ (k + 2))⁻¹) (r₀ := 1 / ((j : ℝ) + 1))
      (inv_pos.2 (pow_pos two_pos _)) (by positivity) (fun z hz r hr hrr => hz.2 r hr hrr)
  rw [Measure.restrict_apply' hF, Set.inter_eq_left.2 hAF, b4p2_const_mul_two_pow] at hbridge
  exact b4p2_eq_zero_of_le_quarter
    (ne_top_of_le_ne_top hFfin.ne (measure_mono hAF)) hbridge

/-- **Lower density bound for restrictions of Hausdorff measure**: the statement of
`b4_hausdorff_restrict_ball_lower_bound`. The constant is
`c = 2^{-(k+3)}`, depending only on `k`, and chosen before `F`. -/
theorem b4_hausdorff_restrict_ball_lower_bound_proof :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∃ c : ℝ, 0 < c ∧ ∀ F : Set (Space n), MeasurableSet F → hausdorffP n k F < ⊤ →
        ∀ᵐ z ∂(hausdorffP n k).restrict F, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < δ ∧
          ENNReal.ofReal (c * r ^ k) ≤ (hausdorffP n k).restrict F (Metric.ball z r) := by
  intro n _ k hk _
  refine ⟨((2 : ℝ) ^ (k + 3))⁻¹, inv_pos.2 (pow_pos two_pos _), ?_⟩
  intro F hF hFfin
  have hnull : (hausdorffP n k).restrict F (⋃ j : ℕ, {z | z ∈ F ∧ ∀ r : ℝ, 0 < r →
      r < 1 / (j + 1) → (hausdorffP n k).restrict F (Metric.ball z r) ≤
        ENNReal.ofReal ((2 ^ (k + 2))⁻¹ * r ^ k)}) = 0 := by
    refine measure_iUnion_null fun j => ?_
    rw [Measure.restrict_apply' hF]
    exact measure_mono_null inter_subset_left (b4p2_badClass_null hk hF hFfin j)
  have hcc : ((2 : ℝ) ^ (k + 3))⁻¹ ≤ ((2 : ℝ) ^ (k + 2))⁻¹ := by
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ (k + 2))⁻¹ := inv_pos.2 (pow_pos two_pos _)
    have heq : ((2 : ℝ) ^ (k + 3))⁻¹ = ((2 : ℝ) ^ (k + 2))⁻¹ / 2 := by
      rw [show (2 : ℝ) ^ (k + 3) = 2 ^ (k + 2) * 2 from pow_succ 2 (k + 2), mul_inv,
        div_eq_mul_inv]
    rw [heq]
    linarith
  filter_upwards [ae_restrict_mem hF, measure_eq_zero_iff_ae_notMem.1 hnull] with z hzF hz
  intro δ hδ
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  apply hz
  refine Set.mem_iUnion.2 ⟨j, hzF, fun r hr hrj => ?_⟩
  refine (hcon r hr (hrj.trans hj)).le.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right hcc (pow_nonneg hr.le k)

end ParabolicRectifiability.Characterization
