import ParabolicRectifiability.QuantitativeCharacterization.Coverings
import ParabolicRectifiability.QuantitativeCharacterization.Assembly.Monotonicity
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reverse.MainTerm

/-! # Helpers for the bounded-support forward covering

Auxiliary facts used to assemble `exists_bounded_forward_approximants`.

* `dp2_bdd_root_bound_of_carlesonEnergy`: `M_β < ∞` bounds every support-centred root integral by
  `M_β s^k`. This is a specialization of `ReverseTree.d2main_le_of_rootCarlesonSup` at
  `S = supp μ`, `σ = μ`, `f = S^R_μ` and `C = M_β`.
* `dp2_bdd_ForwardSupply`: the body of `exists_local_forward_covering` after its constants;
  `Forward.d1comp_exists_local_forward_covering` supplies it.
* `dp2_bdd_forward_at`: under the bounded-support hypotheses, the forward supply applies with
  `M = M_β` at every support-centred root `P(b, ρ)` with `B_loc ρ ≤ D_E` (the forward
  construction applies directly to small roots whose fixed buffers lie below `D_E`).
* `dp2_bdd_small_root`: the small-root covering (`B_loc R ≤ D_E`), raised to the common
  `(K, L₀)` by `RegularMixedCovering.mono`, with the radius-sum normalization
  `Σ_i R_i^k ≤ K R^k ≤ A K μ(P₀)` from the root lower bound.
* `dp2_bdd_relativeTail_of_radiusSum`: the relative tail `C_tail = 2^k + A²` from the exponential
  tail bound at `s = (2^k + A²) K` and the normalization `Σ_i R_i^k ≤ A K μ(P₀)`, after enlarging
  the covering constant once so that this normalization also holds.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- A finite Carleson energy bounds every support-centred root integral: the specialization of
`ReverseTree.d2main_le_of_rootCarlesonSup` at
`S = supp μ`, `σ = μ`, `f = S^R_μ`, `C = M_β` (`carlesonEnergy` is that root supremum), with `ofReal s ^ k · M_β = ofReal (M_β.toReal · s^k)` for `M_β < ∞`. -/
theorem dp2_bdd_root_bound_of_carlesonEnergy {n k : ℕ} {μ : Measure (Space n)}
    (hM : carlesonEnergy μ k ≠ ⊤) {b : Space n} (hb : b ∈ μ.support) {s : ℝ} (hs : 0 < s) :
    (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) ≤
      ENNReal.ofReal ((carlesonEnergy μ k).toReal * s ^ k) := by
  have h := ReverseTree.d2main_le_of_rootCarlesonSup
    (S := μ.support) (σ := μ) (k := k)
    (f := fun R z => squareEnergy μ k .mixed R z)
    (C := carlesonEnergy μ k) le_rfl hb hs
  refine h.trans_eq ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hM,
    ENNReal.ofReal_pow hs.le, mul_comm]

/-- The body of `exists_local_forward_covering`
for fixed `n, k, A` and constants `B_loc, L₀, C`. -/
def dp2_bdd_ForwardSupply (n k : ℕ) (A Bloc L₀ C : ℝ) : Prop :=
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ M : ℝ, 0 ≤ M →
      (∀ b ∈ μ.support ∩ Metric.ball a (Bloc * R), ∀ s : ℝ, 0 < s → s ≤ Bloc * R →
        ENNReal.ofReal (A⁻¹ * s ^ k) ≤ μ (Metric.ball b s) ∧
          μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k) ∧
          (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) ≤
            ENNReal.ofReal (M * s ^ k)) →
      Nonempty (RegularMixedCovering k (C * (1 + M)) L₀ μ a R)

/-- The forward supply at a support-centred root `P(b, ρ)` whose buffer `B_loc ρ` lies below
`D_E`, under the bounded-support hypotheses and a root Carleson bound `M`. -/
theorem dp2_bdd_forward_at {n k : ℕ} {A Bloc L₀ C : ℝ}
    (hfwd : dp2_bdd_ForwardSupply n k A Bloc L₀ C) {μ : Measure (Space n)}
    (hfin : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (hup : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r →
      μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k))
    (hlow : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → r ≤ Metric.diam μ.support →
      ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball z r))
    {M : ℝ} (hM0 : 0 ≤ M)
    (hMb : ∀ b ∈ μ.support, ∀ s : ℝ, 0 < s →
      (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) ≤ ENNReal.ofReal (M * s ^ k))
    {b : Space n} (hb : b ∈ μ.support) {ρ : ℝ} (hρ : 0 < ρ)
    (hρD : Bloc * ρ ≤ Metric.diam μ.support) :
    Nonempty (RegularMixedCovering k (C * (1 + M)) L₀ μ b ρ) :=
  hfwd μ hfin hreg b hb ρ hρ M hM0 fun b' hb' s hs hsle =>
    ⟨hlow b' hb'.1 s hs (hsle.trans hρD), hup b' hb'.1 s hs, hMb b' hb'.1 s hs⟩

/-- **Small roots**: for `B_loc R ≤ D_E` the local forward covering, raised to
`(K, L₀)` with `C₁ (1 + M) ≤ K` and `L₁ ≤ L₀`, has radius sum `≤ K R^k ≤ A K μ(P₀)` by the
lower bound at the root radius `R ≤ D_E`. -/
theorem dp2_bdd_small_root {n k : ℕ} {A Bloc L₁ C₁ L₀ K M : ℝ} (hA : 0 < A) (hB : 1 ≤ Bloc)
    (hL₁ : 1 ≤ L₁) (hLL : L₁ ≤ L₀) (hK0 : 0 ≤ K) (hKK : C₁ * (1 + M) ≤ K)
    (hfwd : dp2_bdd_ForwardSupply n k A Bloc L₁ C₁) {μ : Measure (Space n)}
    (hfin : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (hup : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r →
      μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k))
    (hlow : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → r ≤ Metric.diam μ.support →
      ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball z r))
    (hM0 : 0 ≤ M)
    (hMb : ∀ b ∈ μ.support, ∀ s : ℝ, 0 < s →
      (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) ≤ ENNReal.ofReal (M * s ^ k))
    {a : Space n} (ha : a ∈ μ.support) {R : ℝ} (hR : 0 < R)
    (hRB : Bloc * R ≤ Metric.diam μ.support) :
    ∃ 𝒞 : RegularMixedCovering k K L₀ μ a R,
      ∑' i, ENNReal.ofReal (𝒞.radius i) ^ k ≤
        ENNReal.ofReal (A * K) * μ (Metric.ball a R) := by
  obtain ⟨𝒞₀⟩ := dp2_bdd_forward_at hfwd hfin hreg hup hlow hM0 hMb ha hR hRB
  have hL0 : (0 : ℝ) < L₁ := by linarith
  refine ⟨𝒞₀.mono hR.le hL0 hKK hLL, ?_⟩
  have hRD : R ≤ Metric.diam μ.support := le_trans (le_mul_of_one_le_left hR.le hB) hRB
  have hreal : A * K * (A⁻¹ * R ^ k) = K * R ^ k := by
    rw [mul_mul_mul_comm, mul_inv_cancel₀ hA.ne', one_mul]
  calc ∑' i, ENNReal.ofReal ((𝒞₀.mono hR.le hL0 hKK hLL).radius i) ^ k
      ≤ ENNReal.ofReal (K * R ^ k) := (𝒞₀.mono hR.le hL0 hKK hLL).root_packing
    _ = ENNReal.ofReal (A * K) * ENNReal.ofReal (A⁻¹ * R ^ k) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hA.le hK0), hreal]
    _ ≤ ENNReal.ofReal (A * K) * μ (Metric.ball a R) :=
        mul_le_mul_right (hlow a ha R hR hRD) _

/-- **The relative tail of chosen coverings** (exponential tail bound and Markov, with the
radius-sum normalization): from the conclusion of the exponential tail statement at `s = (2^k + A²) K` and
`Σ_i R_i^k ≤ A K μ(P₀)`, `A S / (A² K) ≤ μ(P₀)`, so `e^N(P₀) ≤ 2 e^{-N/((2^k + A²)K)} μ(P₀)`. -/
theorem dp2_bdd_relativeTail_of_radiusSum {n k : ℕ} {K L : ℝ} {μ : Measure (Space n)}
    {a : Space n} {R : ℝ} (𝒞 : RegularMixedCovering k K L μ a R) {A : ℝ} (hA : 0 < A)
    (hK : 0 < K)
    (htail : ∀ s : ℝ, 2 ^ k * K < s → ∀ N : ℕ,
      𝒞.residual N (Metric.ball a R) ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) / s)) *
          (μ (Metric.ball a R) +
            ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) /
              ENNReal.ofReal (s - 2 ^ k * K)))
    (hS : ∑' i, ENNReal.ofReal (𝒞.radius i) ^ k ≤
      ENNReal.ofReal (A * K) * μ (Metric.ball a R)) :
    𝒞.RelativeTail ((2 : ℝ) ^ k + A ^ 2) := by
  intro N
  have hA2K : 0 < A ^ 2 * K := mul_pos (pow_pos hA 2) hK
  have hexp : ((2 : ℝ) ^ k + A ^ 2) * K = 2 ^ k * K + A ^ 2 * K := by ring
  have hs : (2 : ℝ) ^ k * K < ((2 : ℝ) ^ k + A ^ 2) * K := by rw [hexp]; linarith
  have h := htail _ hs N
  rw [show ((2 : ℝ) ^ k + A ^ 2) * K - 2 ^ k * K = A ^ 2 * K by ring] at h
  have hkey : ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k) /
      ENNReal.ofReal (A ^ 2 * K) ≤ μ (Metric.ball a R) := by
    refine ENNReal.div_le_of_le_mul ?_
    calc ENNReal.ofReal A * (∑' i, ENNReal.ofReal (𝒞.radius i) ^ k)
        ≤ ENNReal.ofReal A * (ENNReal.ofReal (A * K) * μ (Metric.ball a R)) :=
          mul_le_mul_right hS _
      _ = μ (Metric.ball a R) * ENNReal.ofReal (A ^ 2 * K) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hA.le, show A * (A * K) = A ^ 2 * K by ring]
          exact mul_comm _ _
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  calc 𝒞.residual N (Metric.ball a R)
      ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / (((2 : ℝ) ^ k + A ^ 2) * K))) *
          (μ (Metric.ball a R) + μ (Metric.ball a R)) :=
        h.trans (mul_le_mul_right (add_le_add le_rfl hkey) _)
    _ = ENNReal.ofReal (2 * Real.exp (-(N : ℝ) / (((2 : ℝ) ^ k + A ^ 2) * K))) *
          μ (Metric.ball a R) := by
        rw [ENNReal.ofReal_mul zero_le_two, h2, ← two_mul]
        ring

end ParabolicRectifiability.QuantitativeCharacterization
