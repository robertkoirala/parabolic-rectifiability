import ParabolicRectifiability.Analysis.SmoothCutoff.Profile
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Normalized weights, including the transition region

Let `ψ_b` (`b ∈ I`) be finitely many smooth functions on a real normed space with
values in `[0,1]`, and `Ψ = ∑_b ψ_b`. The normalized weights are

    θ_a = ψ_a * f(Ψ),     f(s) = χ(s)/s,

with the normalizer `f` (`normalizer` in `Profile`). Their sum is `Ψ f(Ψ) = χ(Ψ)` at every
point; in particular no lower bound for `Ψ` is assumed. Where `Ψ = 0` all weights
vanish, and in the transition region `1/4 < Ψ < 1/2` the sum lies strictly
between `0` and `1`.

The quantitative statement `sum_norm_iteratedFDeriv_normalizedWeight_le` is
pointwise and abstract. At a point `x`, suppose that all indices outside a
finset `A` of at most `N` indices are locally zero near `x`, and that the
active bumps satisfy `‖Dⁱψ_b(x)‖ ≤ B λⁱ` for `i = 1, 2`. Then, for `k ≤ 2`,

    ∑_a ‖Dᵏθ_a(x)‖ ≤ weightConstant N B F * λᵏ,

where `F` bounds `f, f', f''` on `[0, N]`. The proof uses mathlib's Leibniz bound
for products and Faà di Bruno bound for compositions. Explicitly, with
`G = N B + 1`, it gives `‖Dʲ(f ∘ Ψ)(x)‖ ≤ j! F (G λ)ʲ`, then a per-index bound
`8 max(B,1) F G² λᵏ`, summed over at most `N` active indices. This is a coarse
but explicit constant; sharper formulas are not needed.

-/

noncomputable section

open Set Filter
open scoped ContDiff Topology Nat

namespace ParabolicRectifiability.SmoothCutoff

variable {E : Type*} {ι : Type*}

/-- The normalized weight `θ_a = ψ_a f(∑_{b ∈ I} ψ_b)`. -/
def normalizedWeight (I : Finset ι) (ψ : ι → E → ℝ) (a : ι) (y : E) : ℝ :=
  ψ a y * normalizer (∑ b ∈ I, ψ b y)

/-- The sum of the weights is `χ(Ψ)`, at every point. -/
theorem sum_normalizedWeight (I : Finset ι) (ψ : ι → E → ℝ) (y : E) :
    ∑ a ∈ I, normalizedWeight I ψ a y = activation (∑ b ∈ I, ψ b y) := by
  simp only [normalizedWeight, ← Finset.sum_mul]
  exact mul_normalizer _

theorem sum_normalizedWeight_nonneg (I : Finset ι) (ψ : ι → E → ℝ) (y : E) :
    0 ≤ ∑ a ∈ I, normalizedWeight I ψ a y := by
  rw [sum_normalizedWeight]
  exact activation_nonneg _

theorem sum_normalizedWeight_le_one (I : Finset ι) (ψ : ι → E → ℝ) (y : E) :
    ∑ a ∈ I, normalizedWeight I ψ a y ≤ 1 := by
  rw [sum_normalizedWeight]
  exact activation_le_one _

/-- Where `Ψ ≥ 1/2`, the weights sum to one. -/
theorem sum_normalizedWeight_eq_one (I : Finset ι) (ψ : ι → E → ℝ) {y : E}
    (hy : 1 / 2 ≤ ∑ b ∈ I, ψ b y) : ∑ a ∈ I, normalizedWeight I ψ a y = 1 := by
  rw [sum_normalizedWeight, activation_eq_one hy]

theorem normalizedWeight_nonneg (I : Finset ι) (ψ : ι → E → ℝ) {a : ι} {y : E}
    (h : 0 ≤ ψ a y) : 0 ≤ normalizedWeight I ψ a y :=
  mul_nonneg h (normalizer_nonneg _)

/-- A weight whose bump is locally zero is locally zero. -/
theorem normalizedWeight_eventuallyEq_zero [TopologicalSpace E] (I : Finset ι)
    (ψ : ι → E → ℝ) {a : ι} {x : E}
    (h : ψ a =ᶠ[𝓝 x] fun _ => 0) : normalizedWeight I ψ a =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [h] with y hy
  rw [normalizedWeight, hy, zero_mul]

section Analytic

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_normalizedWeight (I : Finset ι) {ψ : ι → E → ℝ}
    (hψ : ∀ b ∈ I, ContDiff ℝ ∞ (ψ b)) {a : ι} (ha : ContDiff ℝ ∞ (ψ a)) :
    ContDiff ℝ ∞ (normalizedWeight I ψ a) :=
  ha.mul (contDiff_normalizer.comp (ContDiff.sum hψ))

/-- The explicit constant of the abstract normalization bound. -/
def weightConstant (N B F : ℝ) : ℝ := 8 * N * max B 1 * F * (N * B + 1) ^ 2

/-- A locally zero function has vanishing iterated derivatives. -/
theorem iteratedFDeriv_eq_zero_of_eventuallyEq_zero {f : E → ℝ} {x : E}
    (h : f =ᶠ[𝓝 x] fun _ => 0) (k : ℕ) : iteratedFDeriv ℝ k f x = 0 := by
  rw [(h.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_fun_zero]
  rfl

/-- The pointwise abstract bound for the derivatives of the normalized weights. -/
theorem sum_norm_iteratedFDeriv_normalizedWeight_le {I : Finset ι} {ψ : ι → E → ℝ}
    (hψ : ∀ b ∈ I, ContDiff ℝ ∞ (ψ b)) {x : E}
    (h0 : ∀ b ∈ I, 0 ≤ ψ b x) (h1 : ∀ b ∈ I, ψ b x ≤ 1)
    {A : Finset ι} (hA : A ⊆ I) (hout : ∀ b ∈ I, b ∉ A → ψ b =ᶠ[𝓝 x] fun _ => 0)
    {N B F lam : ℝ} (hN : (A.card : ℝ) ≤ N) (hB : 0 ≤ B) (hlam : 0 ≤ lam)
    (hψB : ∀ b ∈ A, ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i (ψ b) x‖ ≤ B * lam ^ i)
    (hF : ∀ i : ℕ, i ≤ 2 → ∀ s ∈ Icc 0 N, ‖iteratedFDeriv ℝ i normalizer s‖ ≤ F)
    {k : ℕ} (hk : k ≤ 2) :
    ∑ a ∈ I, ‖iteratedFDeriv ℝ k (normalizedWeight I ψ a) x‖ ≤
      weightConstant N B F * lam ^ k := by
  classical
  set Ψ : E → ℝ := fun y => ∑ b ∈ I, ψ b y with hΨdef
  have hN0 : 0 ≤ N := (Nat.cast_nonneg _).trans hN
  -- inactive indices contribute nothing
  have hzero : ∀ b ∈ I, b ∉ A → ∀ i : ℕ, iteratedFDeriv ℝ i (ψ b) x = 0 := fun b hb hbA i =>
    iteratedFDeriv_eq_zero_of_eventuallyEq_zero (hout b hb hbA) i
  have hval : ∀ b ∈ I, b ∉ A → ψ b x = 0 := fun b hb hbA => (hout b hb hbA).eq_of_nhds
  -- the value of `Ψ` lies in `[0, N]`
  have hΨx : Ψ x ∈ Icc 0 N := by
    refine ⟨Finset.sum_nonneg h0, ?_⟩
    have hsub : Ψ x = ∑ b ∈ A, ψ b x :=
      (Finset.sum_subset hA fun b hb hbA => hval b hb hbA).symm
    rw [hsub]
    refine (Finset.sum_le_sum fun b hb => h1 b (hA hb)).trans ?_
    simpa using hN
  have hF0 : 0 ≤ F := (norm_nonneg _).trans (hF 0 (by norm_num) (Ψ x) hΨx)
  -- derivatives of `Ψ`
  set G : ℝ := N * B + 1 with hGdef
  have hG1 : 1 ≤ G := by have := mul_nonneg hN0 hB; linarith
  have hG0 : 0 ≤ G := zero_le_one.trans hG1
  have hΨD : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i Ψ x‖ ≤ (G * lam) ^ i := by
    intro i hi1 hi2
    have hsum : iteratedFDeriv ℝ i Ψ x = ∑ b ∈ I, iteratedFDeriv ℝ i (ψ b) x :=
      iteratedFDeriv_fun_sum_apply fun b hb =>
        ((hψ b hb).of_le (mod_cast le_top)).contDiffAt
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    rw [← Finset.sum_subset hA fun b hb hbA => by rw [hzero b hb hbA i, norm_zero]]
    refine (Finset.sum_le_sum fun b hb => hψB b hb i hi1 hi2).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_pow, ← mul_assoc]
    have hlam : 0 ≤ lam ^ i := pow_nonneg hlam i
    refine mul_le_mul_of_nonneg_right ?_ hlam
    calc (A.card : ℝ) * B ≤ N * B := mul_le_mul_of_nonneg_right hN hB
      _ ≤ G := by linarith
      _ ≤ G ^ i := le_self_pow₀ hG1 (by omega)
  -- derivatives of `f ∘ Ψ`
  have hΨsmooth : ContDiff ℝ ∞ Ψ := ContDiff.sum hψ
  have hfΨ : ∀ j : ℕ, j ≤ 2 →
      ‖iteratedFDeriv ℝ j (normalizer ∘ Ψ) x‖ ≤ 2 * F * G ^ 2 * lam ^ j := by
    intro j hj
    have hcomp := norm_iteratedFDeriv_comp_le contDiff_normalizer hΨsmooth
      (mod_cast le_top) x (C := F) (D := G * lam)
      (fun i hi => hF i (hi.trans hj) (Ψ x) hΨx)
      (fun i hi1 hi2 => hΨD i hi1 (hi2.trans hj))
    refine hcomp.trans ?_
    have hfact : (j ! : ℝ) ≤ 2 := by
      have : j ! ≤ 2 ! := Nat.factorial_le hj
      exact_mod_cast this
    have hGj : G ^ j ≤ G ^ 2 := pow_le_pow_right₀ hG1 hj
    rw [mul_pow]
    have hl : 0 ≤ lam ^ j := pow_nonneg hlam j
    have hGj0 : 0 ≤ G ^ j := pow_nonneg hG0 j
    calc (j ! : ℝ) * F * (G ^ j * lam ^ j) ≤ 2 * F * (G ^ 2 * lam ^ j) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hfact hF0)
            (mul_le_mul_of_nonneg_right hGj hl) (by positivity) (by positivity)
      _ = 2 * F * G ^ 2 * lam ^ j := by ring
  -- bumps, including the zeroth derivative
  set B' : ℝ := max B 1 with hB'def
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hψB' : ∀ b ∈ A, ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i (ψ b) x‖ ≤ B' * lam ^ i := by
    intro b hb i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · rw [norm_iteratedFDeriv_zero, pow_zero, mul_one, Real.norm_of_nonneg (h0 b (hA hb))]
      exact (h1 b (hA hb)).trans hB'1
    · exact (hψB b hb i hi1 hi).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hlam i))
  -- the per-index bound
  have hper : ∀ a ∈ A, ‖iteratedFDeriv ℝ k (normalizedWeight I ψ a) x‖ ≤
      8 * B' * F * G ^ 2 * lam ^ k := by
    intro a ha
    have hθ : normalizedWeight I ψ a = fun y => ψ a y * (normalizer ∘ Ψ) y := rfl
    rw [hθ]
    refine (norm_iteratedFDeriv_mul_le (hψ a (hA ha)) (contDiff_normalizer.comp hΨsmooth) x
      (mod_cast le_top)).trans ?_
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψ a) x‖ *
            ‖iteratedFDeriv ℝ (k - i) (normalizer ∘ Ψ) x‖ ≤
          (k.choose i : ℝ) * (2 * B' * F * G ^ 2 * lam ^ k) := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hpow : lam ^ i * lam ^ (k - i) = lam ^ k := by
        rw [← pow_add, Nat.add_sub_cancel' hik]
      have e1 := hψB' a ha i (hik.trans hk)
      have e2 := hfΨ (k - i) ((Nat.sub_le k i).trans hk)
      have hc : (0 : ℝ) ≤ k.choose i := Nat.cast_nonneg _
      calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ψ a) x‖ *
              ‖iteratedFDeriv ℝ (k - i) (normalizer ∘ Ψ) x‖
            ≤ (k.choose i : ℝ) * (B' * lam ^ i) * (2 * F * G ^ 2 * lam ^ (k - i)) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left e1 hc) e2 (norm_nonneg _)
              exact mul_nonneg hc (mul_nonneg (zero_le_one.trans hB'1) (pow_nonneg hlam i))
          _ = (k.choose i : ℝ) * (2 * B' * F * G ^ 2 * (lam ^ i * lam ^ (k - i))) := by ring
          _ = (k.choose i : ℝ) * (2 * B' * F * G ^ 2 * lam ^ k) := by rw [hpow]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hchoose : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = 2 ^ k := by
      exact_mod_cast Nat.sum_range_choose k
    rw [hchoose]
    have h2k : (2 : ℝ) ^ k ≤ 4 := by
      calc (2 : ℝ) ^ k ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hk
        _ = 4 := by norm_num
    have hnn : 0 ≤ 2 * B' * F * G ^ 2 * lam ^ k := by
      have := zero_le_one.trans hB'1
      positivity
    calc (2 : ℝ) ^ k * (2 * B' * F * G ^ 2 * lam ^ k)
        ≤ 4 * (2 * B' * F * G ^ 2 * lam ^ k) := mul_le_mul_of_nonneg_right h2k hnn
      _ = 8 * B' * F * G ^ 2 * lam ^ k := by ring
  -- sum over the active indices
  have hsplit : ∑ a ∈ I, ‖iteratedFDeriv ℝ k (normalizedWeight I ψ a) x‖ =
      ∑ a ∈ A, ‖iteratedFDeriv ℝ k (normalizedWeight I ψ a) x‖ := by
    refine (Finset.sum_subset hA fun a ha haA => ?_).symm
    rw [iteratedFDeriv_eq_zero_of_eventuallyEq_zero
      (normalizedWeight_eventuallyEq_zero I ψ (hout a ha haA)) k, norm_zero]
  rw [hsplit]
  refine (Finset.sum_le_sum hper).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hnn : 0 ≤ 8 * B' * F * G ^ 2 * lam ^ k := by
    have := zero_le_one.trans hB'1
    positivity
  calc (A.card : ℝ) * (8 * B' * F * G ^ 2 * lam ^ k)
      ≤ N * (8 * B' * F * G ^ 2 * lam ^ k) := mul_le_mul_of_nonneg_right hN hnn
    _ = weightConstant N B F * lam ^ k := by
      rw [weightConstant]
      ring

theorem weightConstant_nonneg {N B F : ℝ} (hN : 0 ≤ N) (hB : 0 ≤ B) (hF : 0 ≤ F) :
    0 ≤ weightConstant N B F := by
  have : 0 ≤ max B 1 := hB.trans (le_max_left _ _)
  unfold weightConstant
  positivity

end Analytic

end ParabolicRectifiability.SmoothCutoff
