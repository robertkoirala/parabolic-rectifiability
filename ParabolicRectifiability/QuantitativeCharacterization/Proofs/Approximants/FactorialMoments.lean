import ParabolicRectifiability.QuantitativeCharacterization.Statements.ApproximantComponents
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.MultiplicityBasics

/-! # Factorial moments of the multiplicity with the actual radius sum

Proof of `dp2_factorial_moments : dp2_FactorialMomentStatement`.

Write `P_i = P(a_i,R_i)` for the model balls, `w_i = R_i^k`, `S = Σ_i w_i`, `B = 2^k K` and
`1_i = 1_{P_i}`. The argument is a weak sorting and packing argument, written as an
induction on the moment order with weights depending on the point:

* **Weak sorting** (`dp2_mom_card_pow_le`, `dp2_mom_key`). For a finite index set `J` and the
  total preorder by radius, `|J|^q ≤ q Σ_{j ∈ J} #{l ∈ J : R_l ≤ R_j}^{q-1}`: remove a ball of
  largest radius and use `(x+1)^q ≤ x^q + q (x+1)^{q-1}`. Repeated indices and ties are counted;
  for infinite `J` both sides are `⊤`.
* **Localized multiplicity** `N_i(z) = #{j : z ∈ P_j, R_j ≤ R_i}` (`dp2_mom_localMult`). The
  sorting gives, at every point, `m^p ≤ p Σ_i 1_i N_i^{p-1}` (`dp2_mom_mult_pow_le`) and
  `N_i^{q+1} ≤ (q+1) Σ_{R_j ≤ R_i} 1_j N_j^q` (`dp2_mom_localMult_pow_le`).
* **Packing** (`dp2_mom_packing`): if `R_j ≤ R_i` and `P_j ∩ P_i ≠ ∅` then
  `d(a_j,a_i) < R_j + R_i ≤ 2R_i` and `R_j ≤ 2R_i`, so `local_packing` at `(a_i, 2R_i)` gives
  `Σ_{R_j ≤ R_i, P_j ∩ P_i ≠ ∅} w_j ≤ K (2R_i)^k = B w_i`.
* **Chains** (`dp2_mom_chain`): `∫ 1_i N_i^q dμ ≤ q! A B^q w_i`, by induction on `q`. The base is
  the model-ball growth of the smallest ball, `μ(P_i) ≤ A w_i`. In the step, each term keeps the
  consecutive intersection `1_i 1_j` (zero unless `P_j ∩ P_i ≠ ∅`), then drops `1_i ≤ 1` and
  applies the induction hypothesis and the packing bound.
* **Conclusion** (`dp2_factorial_moments_proof`): `∫_{P₀} m^p ≤ ∫ m^p ≤ p Σ_i ∫ 1_i N_i^{p-1}
  ≤ p (p-1)! A B^{p-1} S = p! A B^{p-1} S`.

Every real `A`, `K` is allowed: `ofReal` turns a negative constant into `0` on both sides. No
finiteness of the multiplicity is assumed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

/-! ### Weak sorting by radius -/

/-- `(x+1)^q ≤ x^q + q (x+1)^(q-1)` for `q ≥ 1`. -/
theorem dp2_mom_succ_pow_le (x q : ℕ) (hq : 1 ≤ q) :
    (x + 1) ^ q ≤ x ^ q + q * (x + 1) ^ (q - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
  clear hq
  rw [Nat.add_sub_cancel]
  induction t with
  | zero => simp
  | succ t ih =>
    have hx : x ^ (t + 1) ≤ (x + 1) ^ (t + 1) := Nat.pow_le_pow_left (Nat.le_succ x) _
    calc (x + 1) ^ (t + 1 + 1) = (x + 1) * (x + 1) ^ (t + 1) := by ring
      _ ≤ (x + 1) * (x ^ (t + 1) + (t + 1) * (x + 1) ^ t) := Nat.mul_le_mul_left _ ih
      _ = x ^ (t + 1 + 1) + x ^ (t + 1) + (t + 1) * (x + 1) ^ (t + 1) := by ring
      _ ≤ x ^ (t + 1 + 1) + (x + 1) ^ (t + 1) + (t + 1) * (x + 1) ^ (t + 1) :=
          Nat.add_le_add_right (Nat.add_le_add_left hx _) _
      _ = x ^ (t + 1 + 1) + (t + 1 + 1) * (x + 1) ^ (t + 1) := by ring

/-- Weak sorting on a finite set: with ties and repetitions allowed,
`|F|^q ≤ q Σ_{j ∈ F} #{l ∈ F : r l ≤ r j}^{q-1}` (remove an element of largest `r`). -/
theorem dp2_mom_card_pow_le {ι : Type*} (r : ι → ℝ) (F : Finset ι) (q : ℕ) (hq : 1 ≤ q) :
    F.card ^ q ≤ q * ∑ j ∈ F, (F.filter (fun l => r l ≤ r j)).card ^ (q - 1) := by
  classical
  induction F using Finset.induction_on_max_value r with
  | empty =>
    simp only [Finset.card_empty, Finset.sum_empty, mul_zero, zero_pow (show q ≠ 0 by omega),
      le_refl]
  | insert a s ha hmax ih =>
    have h1 : (insert a s).filter (fun l => r l ≤ r a) = insert a s := by
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_rfl
      · exact hmax x hx
    have h2 : ∑ j ∈ s, (s.filter (fun l => r l ≤ r j)).card ^ (q - 1) ≤
        ∑ j ∈ s, ((insert a s).filter (fun l => r l ≤ r j)).card ^ (q - 1) := by
      apply Finset.sum_le_sum
      intro j _
      exact Nat.pow_le_pow_left
        (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert a s))) _
    rw [Finset.sum_insert ha, h1, Finset.card_insert_of_notMem ha]
    calc (s.card + 1) ^ q ≤ s.card ^ q + q * (s.card + 1) ^ (q - 1) :=
          dp2_mom_succ_pow_le _ _ hq
      _ ≤ q * ∑ j ∈ s, (s.filter (fun l => r l ≤ r j)).card ^ (q - 1) +
            q * (s.card + 1) ^ (q - 1) := Nat.add_le_add_right ih _
      _ ≤ q * ∑ j ∈ s, ((insert a s).filter (fun l => r l ≤ r j)).card ^ (q - 1) +
            q * (s.card + 1) ^ (q - 1) := Nat.add_le_add_right (Nat.mul_le_mul_left _ h2) _
      _ = q * ((s.card + 1) ^ (q - 1) +
            ∑ j ∈ s, ((insert a s).filter (fun l => r l ≤ r j)).card ^ (q - 1)) := by ring

/-- Weak sorting for an arbitrary index set, in `ℝ≥0∞`: `|J|^q ≤ q Σ_{j ∈ J} N_J(j)^{q-1}` with
`N_J(j) = #{l ∈ J : r l ≤ r j}`. For infinite `J` the right side is `⊤`. -/
theorem dp2_mom_key {ι : Type*} (r : ι → ℝ) (J : Set ι) (q : ℕ) (hq : 1 ≤ q) :
    (∑' j, J.indicator (fun _ => (1 : ℝ≥0∞)) j) ^ q ≤
      (q : ℝ≥0∞) * ∑' j, J.indicator (fun j =>
        (∑' l, (J ∩ {l | r l ≤ r j}).indicator (fun _ => (1 : ℝ≥0∞)) l) ^ (q - 1)) j := by
  rcases J.finite_or_infinite with hfin | hinf
  · lift J to Finset ι using hfin
    have h1 : ∀ j, ((J : Set ι) ∩ {l | r l ≤ r j}) =
        ((J.filter (fun l => r l ≤ r j) : Finset ι) : Set ι) := by
      intro j
      ext l
      simp
    simp_rw [h1, ← sum_eq_tsum_indicator, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast dp2_mom_card_pow_le r J q hq
  · have hJ : ∑' j, J.indicator (fun _ => (1 : ℝ≥0∞)) j = ⊤ := by
      rw [← tsum_subtype J (fun _ => (1 : ℝ≥0∞)), ENNReal.tsum_set_one,
        Set.encard_eq_top_iff.2 hinf, ENat.toENNReal_top]
    have hle : ∑' j, J.indicator (fun _ => (1 : ℝ≥0∞)) j ≤ ∑' j, J.indicator (fun j =>
        (∑' l, (J ∩ {l | r l ≤ r j}).indicator (fun _ => (1 : ℝ≥0∞)) l) ^ (q - 1)) j := by
      refine ENNReal.tsum_le_tsum fun j => ?_
      by_cases hj : j ∈ J
      · rw [Set.indicator_of_mem hj, Set.indicator_of_mem hj]
        apply one_le_pow₀
        have hjj : j ∈ J ∩ {l | r l ≤ r j} := ⟨hj, le_refl (r j)⟩
        calc (1 : ℝ≥0∞) = (J ∩ {l | r l ≤ r j}).indicator (fun _ => (1 : ℝ≥0∞)) j := by
              rw [Set.indicator_of_mem hjj]
          _ ≤ ∑' l, (J ∩ {l | r l ≤ r j}).indicator (fun _ => (1 : ℝ≥0∞)) l :=
              ENNReal.le_tsum j
      · rw [Set.indicator_of_notMem hj, Set.indicator_of_notMem hj]
    rw [hJ, top_le_iff] at hle
    have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    rw [hle, ENNReal.mul_top hq0]
    exact le_top

/-! ### The covering: localized multiplicity, packing and the chain estimate -/

variable {n k : ℕ} {K L : ℝ} {μ : Measure (Space n)} {a : Space n} {R : ℝ}

/-- An indicator of a set with value `1` is at most `1`. -/
theorem dp2_mom_indicator_le_one (s : Set (Space n)) (z : Space n) :
    s.indicator (fun _ => (1 : ℝ≥0∞)) z ≤ 1 := by
  by_cases h : z ∈ s
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- The localized multiplicity `N_i(z) = #{j : z ∈ P_j, R_j ≤ R_i}`, as a countable sum. -/
def dp2_mom_localMult (𝒞 : RegularMixedCovering k K L μ a R) (i : 𝒞.index) (z : Space n) :
    ℝ≥0∞ :=
  ∑' j, if 𝒞.radius j ≤ 𝒞.radius i then (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z else 0

/-- The localized multiplicity is Borel. -/
theorem dp2_mom_measurable_localMult (𝒞 : RegularMixedCovering k K L μ a R) (i : 𝒞.index) :
    Measurable (dp2_mom_localMult 𝒞 i) := by
  show Measurable fun z => ∑' j,
    (if 𝒞.radius j ≤ 𝒞.radius i then (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z else 0)
  refine Measurable.tsum fun j => ?_
  by_cases h : 𝒞.radius j ≤ 𝒞.radius i
  · simp only [h, ↓reduceIte]
    exact measurable_const.indicator (dp2_measurableSet_ball 𝒞 j)
  · simp only [h, ↓reduceIte]
    exact measurable_const

/-- Pointwise weak sorting on the balls containing `z` and satisfying `φ`:
`(Σ_{φ j} 1_j(z))^q ≤ q Σ_{φ j} 1_j(z) N_j(z)^{q-1}`. -/
theorem dp2_mom_pointwise (𝒞 : RegularMixedCovering k K L μ a R) (φ : 𝒞.index → Prop)
    [DecidablePred φ] (z : Space n) (q : ℕ) (hq : 1 ≤ q) :
    (∑' j, if φ j then (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z else 0) ^ q ≤
      (q : ℝ≥0∞) * ∑' j, if φ j then
        (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 j z ^ (q - 1)
        else 0 := by
  have hL : (∑' j, if φ j then (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z else 0) =
      ∑' j, {j | z ∈ 𝒞.ball j ∧ φ j}.indicator (fun _ => (1 : ℝ≥0∞)) j := by
    congr 1
    funext j
    by_cases hφ : φ j <;> by_cases hz : z ∈ 𝒞.ball j <;> simp [hφ, hz]
  rw [hL]
  refine (dp2_mom_key 𝒞.radius {j | z ∈ 𝒞.ball j ∧ φ j} q hq).trans ?_
  refine mul_le_mul_right (ENNReal.tsum_le_tsum fun j => ?_) _
  by_cases hj : j ∈ {j | z ∈ 𝒞.ball j ∧ φ j}
  · have hzj : z ∈ 𝒞.ball j := hj.1
    have hφ : φ j := hj.2
    rw [Set.indicator_of_mem hj, ite_eq_left hφ, Set.indicator_of_mem hzj, one_mul]
    refine pow_le_pow_left' ?_ (q - 1)
    show _ ≤ ∑' l,
      (if 𝒞.radius l ≤ 𝒞.radius j then (𝒞.ball l).indicator (fun _ => (1 : ℝ≥0∞)) z else 0)
    refine ENNReal.tsum_le_tsum fun l => ?_
    by_cases hl : l ∈ {j | z ∈ 𝒞.ball j ∧ φ j} ∩ {l | 𝒞.radius l ≤ 𝒞.radius j}
    · have hzl : z ∈ 𝒞.ball l := hl.1.1
      have hlj : 𝒞.radius l ≤ 𝒞.radius j := hl.2
      rw [Set.indicator_of_mem hl, ite_eq_left hlj, Set.indicator_of_mem hzl]
    · rw [Set.indicator_of_notMem hl]
      exact zero_le
  · rw [Set.indicator_of_notMem hj]
    exact zero_le

/-- Weak sorting of all balls at `z`: `m(z)^q ≤ q Σ_i 1_i(z) N_i(z)^{q-1}`. -/
theorem dp2_mom_mult_pow_le (𝒞 : RegularMixedCovering k K L μ a R) (z : Space n) (q : ℕ)
    (hq : 1 ≤ q) :
    (𝒞.multiplicity z : ℝ≥0∞) ^ q ≤ (q : ℝ≥0∞) *
      ∑' i, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 i z ^ (q - 1) := by
  have h := dp2_mom_pointwise 𝒞 (fun _ => True) z q hq
  simp only [↓reduceIte] at h
  rw [dp2_multiplicity_eq_tsum 𝒞 z]
  exact h

/-- Weak sorting of the balls at `z` not larger than `P_i`:
`N_i(z)^q ≤ q Σ_{R_j ≤ R_i} 1_j(z) N_j(z)^{q-1}`. -/
theorem dp2_mom_localMult_pow_le (𝒞 : RegularMixedCovering k K L μ a R) (i : 𝒞.index)
    (z : Space n) (q : ℕ) (hq : 1 ≤ q) :
    dp2_mom_localMult 𝒞 i z ^ q ≤ (q : ℝ≥0∞) * ∑' j, if 𝒞.radius j ≤ 𝒞.radius i then
      (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 j z ^ (q - 1)
      else 0 :=
  dp2_mom_pointwise 𝒞 (fun j => 𝒞.radius j ≤ 𝒞.radius i) z q hq

open scoped Classical in
/-- **Packing**, the same-family local packing at `(a_i, 2R_i)`:
`Σ_{R_j ≤ R_i, P_j ∩ P_i ≠ ∅} R_j^k ≤ 2^k K R_i^k`. -/
theorem dp2_mom_packing (𝒞 : RegularMixedCovering k K L μ a R) (i : 𝒞.index) :
    (∑' j, if 𝒞.radius j ≤ 𝒞.radius i ∧ (𝒞.ball j ∩ 𝒞.ball i).Nonempty then
        ENNReal.ofReal (𝒞.radius j) ^ k else 0) ≤
      2 ^ k * ENNReal.ofReal K * ENNReal.ofReal (𝒞.radius i) ^ k := by
  have hri := 𝒞.radius_pos i
  have h2r : (0 : ℝ) ≤ 2 * 𝒞.radius i := by linarith
  refine le_trans ?_
    ((𝒞.local_packing (𝒞.center i) (2 * 𝒞.radius i) (by linarith)).trans (le_of_eq ?_))
  · refine ENNReal.tsum_le_tsum fun j => ?_
    by_cases h1 : 𝒞.radius j ≤ 𝒞.radius i ∧ (𝒞.ball j ∩ 𝒞.ball i).Nonempty
    · have hr : 𝒞.radius j ≤ 𝒞.radius i := h1.1
      obtain ⟨x, hxj, hxi⟩ := h1.2
      have hxj' : dist x (𝒞.center j) < 𝒞.radius j := hxj
      have hxi' : dist x (𝒞.center i) < 𝒞.radius i := hxi
      have hc : dist (𝒞.center j) (𝒞.center i) < 2 * 𝒞.radius i :=
        calc dist (𝒞.center j) (𝒞.center i) ≤ dist (𝒞.center j) x + dist x (𝒞.center i) :=
              dist_triangle _ _ _
          _ = dist x (𝒞.center j) + dist x (𝒞.center i) := by rw [dist_comm (𝒞.center j)]
          _ < 𝒞.radius j + 𝒞.radius i := add_lt_add hxj' hxi'
          _ ≤ 2 * 𝒞.radius i := by linarith
      have h2 : 𝒞.center j ∈ Metric.ball (𝒞.center i) (2 * 𝒞.radius i) ∧
          𝒞.radius j ≤ 2 * 𝒞.radius i := ⟨hc, by linarith⟩
      rw [ite_eq_left h1, ite_eq_left h2]
    · rw [ite_eq_right h1]
      exact zero_le
  · rw [ENNReal.ofReal_mul' (pow_nonneg h2r k), ENNReal.ofReal_pow h2r,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_pow]
    ring

open scoped Classical in
/-- **Chain estimate** (iterating the packing bound from the smallest ball):
`∫ 1_i N_i^q dμ ≤ q! A (2^k K)^q R_i^k` for every `q`, from the model-ball growth. -/
theorem dp2_mom_chain (𝒞 : RegularMixedCovering k K L μ a R) {A : ℝ}
    (hball : ∀ i, μ (𝒞.ball i) ≤ ENNReal.ofReal (A * 𝒞.radius i ^ k)) (q : ℕ) (i : 𝒞.index) :
    ∫⁻ z, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 i z ^ q ∂μ ≤
      (Nat.factorial q : ℝ≥0∞) * ENNReal.ofReal A * (2 ^ k * ENNReal.ofReal K) ^ q *
        ENNReal.ofReal (𝒞.radius i) ^ k := by
  induction q generalizing i with
  | zero =>
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, one_mul]
    rw [lintegral_indicator_const (dp2_measurableSet_ball 𝒞 i), one_mul]
    refine (hball i).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul' (pow_nonneg (𝒞.radius_pos i).le k),
      ENNReal.ofReal_pow (𝒞.radius_pos i).le]
  | succ q ih =>
    -- pointwise: weak sorting of the balls not larger than `P_i`
    have hK2 : ∀ z, dp2_mom_localMult 𝒞 i z ^ (q + 1) ≤ ((q + 1 : ℕ) : ℝ≥0∞) *
        ∑' j, (if 𝒞.radius j ≤ 𝒞.radius i then
          (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 j z ^ q
          else 0) := by
      intro z
      have h := dp2_mom_localMult_pow_le 𝒞 i z (q + 1) (by omega)
      rwa [Nat.add_sub_cancel] at h
    have hpt : ∀ z, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z *
        dp2_mom_localMult 𝒞 i z ^ (q + 1) ≤ ((q + 1 : ℕ) : ℝ≥0∞) *
          ∑' j, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z *
            (if 𝒞.radius j ≤ 𝒞.radius i then
              (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 j z ^ q
              else 0) := by
      intro z
      calc (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 i z ^ (q + 1)
          ≤ (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z * (((q + 1 : ℕ) : ℝ≥0∞) *
              ∑' j, (if 𝒞.radius j ≤ 𝒞.radius i then
                (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 j z ^ q
                else 0)) := mul_le_mul_right (hK2 z) _
        _ = _ := by rw [ENNReal.tsum_mul_left]; ring
    -- measurability of the terms
    have hT : ∀ j, Measurable fun z => (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z *
        (if 𝒞.radius j ≤ 𝒞.radius i then
          (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 j z ^ q
          else 0) := by
      intro j
      by_cases h1 : 𝒞.radius j ≤ 𝒞.radius i
      · simp only [h1, ↓reduceIte]
        exact (measurable_const.indicator (dp2_measurableSet_ball 𝒞 i)).mul
          ((measurable_const.indicator (dp2_measurableSet_ball 𝒞 j)).mul
            ((dp2_mom_measurable_localMult 𝒞 j).pow_const q))
      · simp only [h1, ↓reduceIte, mul_zero]
        exact measurable_const
    -- each term: consecutive intersection, then drop `1_i` and use the induction hypothesis
    have hTj : ∀ j, ∫⁻ z, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z *
        (if 𝒞.radius j ≤ 𝒞.radius i then
          (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 j z ^ q
          else 0) ∂μ ≤
        (if 𝒞.radius j ≤ 𝒞.radius i ∧ (𝒞.ball j ∩ 𝒞.ball i).Nonempty then
          (Nat.factorial q : ℝ≥0∞) * ENNReal.ofReal A * (2 ^ k * ENNReal.ofReal K) ^ q *
            ENNReal.ofReal (𝒞.radius j) ^ k else 0) := by
      intro j
      by_cases h1 : 𝒞.radius j ≤ 𝒞.radius i
      · by_cases h2 : (𝒞.ball j ∩ 𝒞.ball i).Nonempty
        · rw [ite_eq_left (And.intro h1 h2)]
          calc ∫⁻ z, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z *
                (if 𝒞.radius j ≤ 𝒞.radius i then
                  (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 j z ^ q
                  else 0) ∂μ
              ≤ ∫⁻ z, (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z *
                  dp2_mom_localMult 𝒞 j z ^ q ∂μ := by
                refine lintegral_mono fun z => ?_
                rw [ite_eq_left h1]
                exact mul_le_of_le_one_left' (dp2_mom_indicator_le_one _ _)
            _ ≤ _ := ih j
        · have hc : ¬(𝒞.radius j ≤ 𝒞.radius i ∧ (𝒞.ball j ∩ 𝒞.ball i).Nonempty) :=
            fun h => h2 h.2
          rw [ite_eq_right hc]
          have h0 : ∀ z, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z *
              (if 𝒞.radius j ≤ 𝒞.radius i then
                (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 j z ^ q
                else 0) = 0 := by
            intro z
            by_cases hzi : z ∈ 𝒞.ball i
            · by_cases hzj : z ∈ 𝒞.ball j
              · exact (h2 ⟨z, hzj, hzi⟩).elim
              · rw [ite_eq_left h1, Set.indicator_of_notMem hzj, zero_mul, mul_zero]
            · rw [Set.indicator_of_notMem hzi, zero_mul]
          exact le_of_eq ((lintegral_congr h0).trans lintegral_zero)
      · have hc : ¬(𝒞.radius j ≤ 𝒞.radius i ∧ (𝒞.ball j ∩ 𝒞.ball i).Nonempty) :=
          fun h => h1 h.1
        rw [ite_eq_right hc]
        have h0 : ∀ z, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z *
            (if 𝒞.radius j ≤ 𝒞.radius i then
              (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 j z ^ q
              else 0) = 0 := fun z => by rw [ite_eq_right h1, mul_zero]
        exact le_of_eq ((lintegral_congr h0).trans lintegral_zero)
    calc ∫⁻ z, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z *
          dp2_mom_localMult 𝒞 i z ^ (q + 1) ∂μ
        ≤ ∫⁻ z, ((q + 1 : ℕ) : ℝ≥0∞) *
            ∑' j, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z *
              (if 𝒞.radius j ≤ 𝒞.radius i then
                (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 j z ^ q
                else 0) ∂μ := lintegral_mono hpt
      _ = ((q + 1 : ℕ) : ℝ≥0∞) * ∑' j, ∫⁻ z, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z *
              (if 𝒞.radius j ≤ 𝒞.radius i then
                (𝒞.ball j).indicator (fun _ => (1 : ℝ≥0∞)) z * dp2_mom_localMult 𝒞 j z ^ q
                else 0) ∂μ := by
          rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
            lintegral_tsum fun j => (hT j).aemeasurable]
      _ ≤ ((q + 1 : ℕ) : ℝ≥0∞) * ∑' j,
            (if 𝒞.radius j ≤ 𝒞.radius i ∧ (𝒞.ball j ∩ 𝒞.ball i).Nonempty then
              (Nat.factorial q : ℝ≥0∞) * ENNReal.ofReal A * (2 ^ k * ENNReal.ofReal K) ^ q *
                ENNReal.ofReal (𝒞.radius j) ^ k else 0) :=
          mul_le_mul_right (ENNReal.tsum_le_tsum hTj) _
      _ = ((q + 1 : ℕ) : ℝ≥0∞) * ((Nat.factorial q : ℝ≥0∞) * ENNReal.ofReal A *
            (2 ^ k * ENNReal.ofReal K) ^ q *
            ∑' j, (if 𝒞.radius j ≤ 𝒞.radius i ∧ (𝒞.ball j ∩ 𝒞.ball i).Nonempty then
              ENNReal.ofReal (𝒞.radius j) ^ k else 0)) := by
          congr 1
          rw [← ENNReal.tsum_mul_left]
          congr 1
          funext j
          split_ifs <;> simp
      _ ≤ ((q + 1 : ℕ) : ℝ≥0∞) * ((Nat.factorial q : ℝ≥0∞) * ENNReal.ofReal A *
            (2 ^ k * ENNReal.ofReal K) ^ q *
            (2 ^ k * ENNReal.ofReal K * ENNReal.ofReal (𝒞.radius i) ^ k)) :=
          mul_le_mul_right (mul_le_mul_right (dp2_mom_packing 𝒞 i) _) _
      _ = (Nat.factorial (q + 1) : ℝ≥0∞) * ENNReal.ofReal A *
            (2 ^ k * ENNReal.ofReal K) ^ (q + 1) * ENNReal.ofReal (𝒞.radius i) ^ k := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          ring

/-! ### The statement -/

/-- **Factorial moments** with the actual radius sum
`S = Σ_i R_i^k`: `∫_{P₀} m^p dμ ≤ p! A (2^k K)^{p-1} S` for every `p ≥ 1`, from the model-ball
growth `μ(P_i) ≤ A R_i^k` and the same-family local packing. -/
theorem dp2_factorial_moments_proof : dp2_FactorialMomentStatement := by
  intro n k K L A μ a R 𝒞 hball p hp
  have hmeas : ∀ i, Measurable fun z => (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z *
      dp2_mom_localMult 𝒞 i z ^ (p - 1) := fun i =>
    (measurable_const.indicator (dp2_measurableSet_ball 𝒞 i)).mul
      ((dp2_mom_measurable_localMult 𝒞 i).pow_const _)
  calc ∫⁻ z in Metric.ball a R, (𝒞.multiplicity z : ℝ≥0∞) ^ p ∂μ
      ≤ ∫⁻ z, (𝒞.multiplicity z : ℝ≥0∞) ^ p ∂μ := setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ z, (p : ℝ≥0∞) * ∑' i, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z *
          dp2_mom_localMult 𝒞 i z ^ (p - 1) ∂μ :=
        lintegral_mono fun z => dp2_mom_mult_pow_le 𝒞 z p hp
    _ = (p : ℝ≥0∞) * ∑' i, ∫⁻ z, (𝒞.ball i).indicator (fun _ => (1 : ℝ≥0∞)) z *
          dp2_mom_localMult 𝒞 i z ^ (p - 1) ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top p),
          lintegral_tsum fun i => (hmeas i).aemeasurable]
    _ ≤ (p : ℝ≥0∞) * ∑' i, ((Nat.factorial (p - 1) : ℝ≥0∞) * ENNReal.ofReal A *
          (2 ^ k * ENNReal.ofReal K) ^ (p - 1) * ENNReal.ofReal (𝒞.radius i) ^ k) :=
        mul_le_mul_right (ENNReal.tsum_le_tsum fun i => dp2_mom_chain 𝒞 hball (p - 1) i) _
    _ = (Nat.factorial p : ℝ≥0∞) * ENNReal.ofReal A * (2 ^ k * ENNReal.ofReal K) ^ (p - 1) *
          ∑' i, ENNReal.ofReal (𝒞.radius i) ^ k := by
        rw [ENNReal.tsum_mul_left, ← Nat.mul_factorial_pred (show p ≠ 0 by omega),
          Nat.cast_mul]
        ring

end ParabolicRectifiability.QuantitativeCharacterization
