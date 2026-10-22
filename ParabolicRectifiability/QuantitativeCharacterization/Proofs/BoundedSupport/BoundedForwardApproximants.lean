import ParabolicRectifiability.QuantitativeCharacterization.Proofs.BoundedSupport.ComponentTheorems
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.BoundedSupport.ForwardSupplyHelpers
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.ComponentTheorems
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.MultiplicityBasics
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Trace.ComponentTheorems
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.ForwardCovering

/-! # Bounded-support forward approximants

Assembly of the bounded-support forward covering from the separated root cover, the band-cost
bound and the bounded union of root certificates, together with the multiplicity, tail and
typed-split statements for coverings and the trace-carriage statement. The local forward covering
is `Forward.d1comp_exists_local_forward_covering`.

* `dp2_bdd_approximants_of_radiusSum`: a `(K,L)` covering (`L ≥ 1`, `K > 0`) of a root of a
  locally Radon `μ` with global upper growth and radius sum `Σ_i R_i^k ≤ A K μ(P₀)` has a typed
  trace split, the measure identity and the relative tail `2^k + A²` (model-ball growth,
  multiplicity, first moment, trace carriage, typed split, exponential tail,
  `dp2_bdd_relativeTail_of_radiusSum`).
* `dp2_bdd_large_root`: for `D_E ≤ B_loc R` the bounded union of the `r_*`-root certificates,
  `r_* = D_E / B_loc` (separated cover at `r_*`, the forward supply at each centre, band cost,
  bounded union), with the normalization `Σ_i R_i^k ≤ N K' r_*^k ≤ A K μ(P₀)`.
* `dp2_exists_bounded_forward_approximants`: the statement of `exists_bounded_forward_approximants`,
  with `L₀ = B_loc + L₁` and `C = A² (8 B_loc)^k C₁ + A 2^k B_loc^k` from the local forward
  covering's `(B_loc, L₁, C₁)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **Typed split, identity and relative tail of a chosen covering.**
Model-ball growth from the global upper growth, factorial moments, finite multiplicity from the
first moment, trace carriage, the typed split and identity, the exponential tail at
`s = (2^k + A²) K` and the radius-sum normalization `Σ_i R_i^k ≤ A K μ(P₀)`. -/
theorem dp2_bdd_approximants_of_radiusSum {n k : ℕ} {K L A : ℝ} (hL : 1 ≤ L) (hK : 0 < K)
    (hA : 0 < A) {μ : Measure (Space n)} (hfin : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular) {a : Space n} {R : ℝ} (𝒞 : RegularMixedCovering k K L μ a R)
    (hup : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r →
      μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k))
    (hS : ∑' i, ENNReal.ofReal (𝒞.radius i) ^ k ≤
      ENNReal.ofReal (A * K) * μ (Metric.ball a R)) :
    ∃ FH FV : Set (Space n), 𝒞.IsTypedTraceSplit FH FV ∧ 𝒞.MeasureIdentity FH FV ∧
      𝒞.RelativeTail ((2 : ℝ) ^ k + A ^ 2) := by
  have hball := dp2_ball_growth_of_global 𝒞 hup
  have hmom := dp2_factorial_moments n k K L A μ a R 𝒞 hball
  have hfm := dp2_ae_multiplicity_lt_top 𝒞 (hmom 1 le_rfl)
  have htr := dp2_trace_carriage n k K L hL μ hfin hreg a R 𝒞 hfm
  obtain ⟨FH, FV, hs, hid⟩ := dp2_typed_split n k K L hL μ a R 𝒞 htr
  have htail := dp2_exponential_tail n k K L A μ a R 𝒞 hK.le hmom
  exact ⟨FH, FV, hs, hid, dp2_bdd_relativeTail_of_radiusSum 𝒞 hA hK htail hS⟩

/-- **Large roots** (`D_E ≤ B_loc R`). With `r_* = D_E / B_loc`: the separated cover covers `E` by
`N ≤ A² (8 B_loc)^k` balls `P(b_j, r_*)` centred on `E`; the forward supply gives a
`(C₁(1+M), L₁)` covering of each `P(b_j, r_*)` (its buffer is `B_loc r_* = D_E`); the band cost bounds the
band `(P(a,R) ∩ E) × [r_*, R)` by `A 2^k B_loc^k R^k` (`μ(E) ≤ μ(P(a, 2D_E)) ≤ A (2D_E)^k`); the bounded union
combines them into a `(K, B_loc + L₁)` covering of `P(a,R)` (every `P(b_j, L₁ r_*)` lies in
`P(a, (B_loc + L₁) R)` since `dist(b_j, a) ≤ D_E ≤ B_loc R`) with
`Σ_i R_i^k ≤ N C₁(1+M) r_*^k ≤ K r_*^k ≤ A K μ(P(a, r_*)) ≤ A K μ(P₀)`, the lower bound
being used at the radius `r_* ≤ D_E`. -/
theorem dp2_bdd_large_root {n k : ℕ} (hk : 1 ≤ k) {A Bloc L₁ C₁ K M : ℝ} (hA : 0 < A)
    (hB : 1 ≤ Bloc) (hL₁ : 1 ≤ L₁) (hC₁ : 0 ≤ C₁) (hM0 : 0 ≤ M)
    (hKsum : A ^ 2 * (8 * Bloc) ^ k * (C₁ * (1 + M)) + A * 2 ^ k * Bloc ^ k ≤ K)
    (hfwd : dp2_bdd_ForwardSupply n k A Bloc L₁ C₁) {μ : Measure (Space n)}
    (hfin : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (hbd : Bornology.IsBounded μ.support) (hdiam : 0 < Metric.diam μ.support)
    (hup : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r →
      μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k))
    (hlow : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → r ≤ Metric.diam μ.support →
      ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball z r))
    (hMb : ∀ b ∈ μ.support, ∀ s : ℝ, 0 < s →
      (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) ≤ ENNReal.ofReal (M * s ^ k))
    {a : Space n} (ha : a ∈ μ.support) {R : ℝ} (hRB : Metric.diam μ.support ≤ Bloc * R) :
    ∃ 𝒞 : RegularMixedCovering k K (Bloc + L₁) μ a R,
      ∑' i, ENNReal.ofReal (𝒞.radius i) ^ k ≤
        ENNReal.ofReal (A * K) * μ (Metric.ball a R) := by
  have hB0 : (0 : ℝ) < Bloc := by linarith
  have hL0 : (0 : ℝ) < L₁ := by linarith
  -- the fixed small radius `r_* = D_E / B_loc`
  obtain ⟨rs, hrsdef⟩ : ∃ rs : ℝ, rs = Metric.diam μ.support / Bloc := ⟨_, rfl⟩
  have hrs : 0 < rs := by rw [hrsdef]; exact div_pos hdiam hB0
  have hBrs : Bloc * rs = Metric.diam μ.support := by
    rw [hrsdef]; exact mul_div_cancel₀ _ hB0.ne'
  have hrsD : rs ≤ Metric.diam μ.support := by rw [hrsdef]; exact div_le_self hdiam.le hB
  have hrsR : rs ≤ R := by
    rw [hrsdef, div_le_iff₀ hB0, mul_comm]; exact hRB
  -- separated cover: a bounded cover of `E` by `r_*`-roots
  obtain ⟨N, b, hbE, hcov, hN⟩ := dp2_separated_root_cover n k A μ hA hbd hup hlow rs hrs hrsD
  have h8 : 8 * Metric.diam μ.support / rs = 8 * Bloc := by
    rw [← hBrs, ← mul_assoc, mul_div_assoc, div_self hrs.ne', mul_one]
  have hNb : (N : ℝ) ≤ A ^ 2 * (8 * Bloc) ^ k := by rw [← h8]; exact hN
  -- the forward certificates at the centres
  have hfw : ∀ j, Nonempty (RegularMixedCovering k (C₁ * (1 + M)) L₁ μ (b j) rs) :=
    fun j => dp2_bdd_forward_at hfwd hfin hreg hup hlow hM0 hMb (hbE j) hrs hBrs.le
  -- band cost: the declared-bad band
  have hY : 0 ≤ A * 2 ^ k * Bloc ^ k :=
    mul_nonneg (mul_nonneg hA.le (pow_nonneg zero_le_two k)) (pow_nonneg hB0.le k)
  have hsupp : μ.support ⊆ Metric.ball a (2 * Metric.diam μ.support) := fun z hz => by
    rw [Metric.mem_ball]
    have h := Metric.dist_le_diam_of_mem hbd hz ha
    linarith
  have hmass : μ (Metric.ball a R ∩ μ.support) ≤
      ENNReal.ofReal (A * 2 ^ k * Bloc ^ k * rs ^ k) := by
    calc μ (Metric.ball a R ∩ μ.support) ≤ μ (Metric.ball a (2 * Metric.diam μ.support)) :=
          measure_mono (Set.inter_subset_right.trans hsupp)
      _ ≤ ENNReal.ofReal (A * (2 * Metric.diam μ.support) ^ k) := hup a ha _ (by linarith)
      _ = ENNReal.ofReal (A * 2 ^ k * Bloc ^ k * rs ^ k) := by
          rw [← hBrs]
          congr 1
          ring
  have hband := dp2_band_cost n k hk μ (Metric.ball a R ∩ μ.support) (A * 2 ^ k * Bloc ^ k)
    rs R hY hrs hrsR hmass
  -- bounded union
  have hK'0 : 0 ≤ C₁ * (1 + M) := mul_nonneg hC₁ (by linarith)
  have hKN : (N : ℝ) * (C₁ * (1 + M)) + A * 2 ^ k * Bloc ^ k ≤ K := by
    have h := mul_le_mul_of_nonneg_right hNb hK'0
    linarith
  have hdist : ∀ j, dist (b j) a + L₁ * rs ≤ (Bloc + L₁) * R := fun j => by
    have h1 : dist (b j) a ≤ Metric.diam μ.support := Metric.dist_le_diam_of_mem hbd (hbE j) ha
    have h2 : L₁ * rs ≤ L₁ * R := mul_le_mul_of_nonneg_left hrsR hL0.le
    linarith
  obtain ⟨𝒞, hS⟩ := dp2_bounded_union n k (C₁ * (1 + M)) L₁ K (Bloc + L₁)
    (A * 2 ^ k * Bloc ^ k) μ a R rs N b hfw hrs hrsR hK'0 hL0
    (by linarith) hY hcov hdist hband hKN
  -- the radius-sum normalization through the lower bound at `r_*`
  refine ⟨𝒞, hS.trans ?_⟩
  have hNK : (N : ℝ) * (C₁ * (1 + M)) ≤ K := by linarith
  have hK0 : 0 ≤ K := le_trans (mul_nonneg (Nat.cast_nonneg N) hK'0) hNK
  have hreal : A * K * (A⁻¹ * rs ^ k) = K * rs ^ k := by
    rw [mul_mul_mul_comm, mul_inv_cancel₀ hA.ne', one_mul]
  calc ENNReal.ofReal ((N : ℝ) * (C₁ * (1 + M)) * rs ^ k)
      ≤ ENNReal.ofReal (K * rs ^ k) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hNK (pow_nonneg hrs.le k))
    _ = ENNReal.ofReal (A * K) * ENNReal.ofReal (A⁻¹ * rs ^ k) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hA.le hK0), hreal]
    _ ≤ ENNReal.ofReal (A * K) * μ (Metric.ball a rs) :=
        mul_le_mul_right (hlow a ha rs hrs hrsD) _
    _ ≤ ENNReal.ofReal (A * K) * μ (Metric.ball a R) :=
        mul_le_mul_right (measure_mono (Metric.ball_subset_ball hrsR)) _

/-- **Bounded-support forward approximants** (`exists_bounded_forward_approximants`). The local
forward covering gives `(B_loc, L₁, C₁)`; take `L₀ = B_loc + L₁` and
`C = A² (8 B_loc)^k C₁ + A 2^k B_loc^k`, `M = M_β`. Small roots (`B_loc R ≤ D_E`):
`dp2_bdd_small_root`; large roots (`D_E < B_loc R`): `dp2_bdd_large_root`; in both cases
`Σ_i R_i^k ≤ A K μ(P₀)`, and `dp2_bdd_approximants_of_radiusSum` gives the typed split, the
measure identity and the relative tail `2^k + A²`. The hypothesis `μ ≠ 0` is not used (it follows
from `a ∈ supp μ`). -/
theorem dp2_exists_bounded_forward_approximants :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular → μ ≠ 0 →
      Bornology.IsBounded μ.support → 0 < Metric.diam μ.support →
      (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) →
      (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → r ≤ Metric.diam μ.support →
        ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball z r)) →
      carlesonEnergy μ k < ⊤ → ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R →
        ∃ 𝒞 : RegularMixedCovering k (C * (1 + (carlesonEnergy μ k).toReal)) L₀ μ a R,
          ∃ FH FV : Set (Space n), 𝒞.IsTypedTraceSplit FH FV ∧ 𝒞.MeasureIdentity FH FV ∧
            𝒞.RelativeTail ((2 : ℝ) ^ k + A ^ 2) := by
  intro n hn k hk hkn A hA
  obtain ⟨Bloc, hB, L₁, hL₁, C₁, hC₁, hfwd⟩ :=
    Forward.d1comp_exists_local_forward_covering n hn k hk hkn A hA
  have hA0 : (0 : ℝ) < A := by linarith
  have hB0 : (0 : ℝ) < Bloc := by linarith
  have hX : 1 ≤ A ^ 2 * (8 * Bloc) ^ k :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA) (one_le_pow₀ (by linarith))
  have hY : 0 ≤ A * 2 ^ k * Bloc ^ k :=
    mul_nonneg (mul_nonneg hA0.le (pow_nonneg zero_le_two k)) (pow_nonneg hB0.le k)
  have hXC : C₁ ≤ A ^ 2 * (8 * Bloc) ^ k * C₁ := by
    have h := mul_le_mul_of_nonneg_right hX (by linarith : (0 : ℝ) ≤ C₁)
    linarith
  refine ⟨Bloc + L₁, by linarith, A ^ 2 * (8 * Bloc) ^ k * C₁ + A * 2 ^ k * Bloc ^ k,
    by linarith, ?_⟩
  intro μ hfin hreg _hμ hbd hdiam hup hlow hM a ha R hR
  have hM0 : 0 ≤ (carlesonEnergy μ k).toReal := ENNReal.toReal_nonneg
  have hMb : ∀ b ∈ μ.support, ∀ s : ℝ, 0 < s →
      (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) ≤
        ENNReal.ofReal ((carlesonEnergy μ k).toReal * s ^ k) :=
    fun b hb s hs => dp2_bdd_root_bound_of_carlesonEnergy hM.ne hb hs
  have hC0 : 0 < A ^ 2 * (8 * Bloc) ^ k * C₁ + A * 2 ^ k * Bloc ^ k := by linarith
  have hK : 0 < (A ^ 2 * (8 * Bloc) ^ k * C₁ + A * 2 ^ k * Bloc ^ k) *
      (1 + (carlesonEnergy μ k).toReal) := mul_pos hC0 (by linarith)
  obtain ⟨𝒞, hS⟩ : ∃ 𝒞 : RegularMixedCovering k
      ((A ^ 2 * (8 * Bloc) ^ k * C₁ + A * 2 ^ k * Bloc ^ k) * (1 + (carlesonEnergy μ k).toReal))
      (Bloc + L₁) μ a R,
      ∑' i, ENNReal.ofReal (𝒞.radius i) ^ k ≤
        ENNReal.ofReal (A * ((A ^ 2 * (8 * Bloc) ^ k * C₁ + A * 2 ^ k * Bloc ^ k) *
          (1 + (carlesonEnergy μ k).toReal))) * μ (Metric.ball a R) := by
    rcases le_or_gt (Bloc * R) (Metric.diam μ.support) with hsmall | hlarge
    · have hCC : C₁ ≤ A ^ 2 * (8 * Bloc) ^ k * C₁ + A * 2 ^ k * Bloc ^ k := by linarith
      exact dp2_bdd_small_root hA0 hB hL₁ (by linarith) hK.le
        (mul_le_mul_of_nonneg_right hCC (by linarith)) hfwd hfin hreg hup hlow hM0
        hMb ha hR hsmall
    · have hKsum : A ^ 2 * (8 * Bloc) ^ k * (C₁ * (1 + (carlesonEnergy μ k).toReal)) +
          A * 2 ^ k * Bloc ^ k ≤
          (A ^ 2 * (8 * Bloc) ^ k * C₁ + A * 2 ^ k * Bloc ^ k) *
            (1 + (carlesonEnergy μ k).toReal) := by
        have h := mul_le_mul_of_nonneg_left
          (by linarith : (1 : ℝ) ≤ 1 + (carlesonEnergy μ k).toReal) hY
        linarith
      exact dp2_bdd_large_root hk hA0 hB hL₁ (by linarith) hM0 hKsum hfwd hfin hreg hbd hdiam
        hup hlow hMb ha hlarge.le
  obtain ⟨FH, FV, hs, hid, ht⟩ :=
    dp2_bdd_approximants_of_radiusSum (by linarith) hK hA0 hfin hreg 𝒞 hup hS
  exact ⟨𝒞, FH, FV, hs, hid, ht⟩

end ParabolicRectifiability.QuantitativeCharacterization
