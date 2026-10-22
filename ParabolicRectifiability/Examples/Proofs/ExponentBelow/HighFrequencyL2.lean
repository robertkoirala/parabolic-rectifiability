import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements

/-! # A finite high-frequency cosine sum estimate

The assumed product-mean estimate bounds each off-diagonal entry of the Gram
matrix by the reciprocal of the larger frequency. Lacunarity makes each row
of this off-diagonal matrix summable, uniformly in the number of terms. -/

noncomputable section

open MeasureTheory

namespace ParabolicRectifiability.Examples

/-- Iterating the sixteen-fold frequency growth. -/
private theorem e2_bmo2_iterate_growth (N : ℕ → ℕ)
    (hN : ∀ j, 16 * N j ≤ N (j + 1)) (i d : ℕ) :
    16 ^ d * N i ≤ N (i + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        16 ^ (d + 1) * N i = 16 * (16 ^ d * N i) := by
          rw [pow_succ]
          ring
        _ ≤ 16 * N (i + d) := Nat.mul_le_mul_left 16 ih
        _ ≤ N (i + d + 1) := hN (i + d)

/-- Every natural power of sixteen is positive. -/
private theorem e2_bmo2_one_le_pow (d : ℕ) : 1 ≤ (16 : ℕ) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ]
      omega

/-- The frequency sequence is nondecreasing. -/
private theorem e2_bmo2_mono (N : ℕ → ℕ)
    (hN : ∀ j, 16 * N j ≤ N (j + 1)) {i j : ℕ} (hij : i ≤ j) :
    N i ≤ N j := by
  have hg := e2_bmo2_iterate_growth N hN i (j - i)
  have hsum : i + (j - i) = j := Nat.add_sub_of_le hij
  rw [hsum] at hg
  have hp : 1 ≤ 16 ^ (j - i) := e2_bmo2_one_le_pow _
  calc
    N i = 1 * N i := by simp
    _ ≤ 16 ^ (j - i) * N i := Nat.mul_le_mul_right (N i) hp
    _ ≤ N j := hg

/-- A positive index gap gives the sixteen-fold separation required by the product-mean estimate. -/
private theorem e2_bmo2_gap_growth (N : ℕ → ℕ)
    (hN : ∀ j, 16 * N j ≤ N (j + 1)) {i j : ℕ} (hij : i < j) :
    16 * N i ≤ N j := by
  exact (hN i).trans (e2_bmo2_mono N hN (Nat.succ_le_of_lt hij))

/-- The number of indices before a frequency is dominated by its growth. -/
private theorem e2_bmo2_mul16_le_pow (d : ℕ) : d * 16 ≤ 16 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      cases d with
      | zero => norm_num
      | succ d =>
          have hp : 16 ≤ 16 ^ (d + 1) := by
            rw [pow_succ]
            have hpos : 1 ≤ (16 : ℕ) ^ d := e2_bmo2_one_le_pow _
            nlinarith
          rw [Nat.succ_mul, pow_succ]
          nlinarith [ih, hp]

/-- The finite geometric sums are bounded by their infinite geometric sum. -/
private theorem e2_bmo2_geometric_sum (m : ℕ) :
    ∑ q ∈ Finset.range m, (1 / 16 : ℝ) ^ q ≤ 16 / 15 := by
  have hgeom := geom_sum_mul_of_le_one (by norm_num : (1 / 16 : ℝ) ≤ 1) m
  have hgeom' :
      (∑ q ∈ Finset.range m, (1 / 16 : ℝ) ^ q) * (15 / 16) =
        1 - (1 / 16 : ℝ) ^ m := by
    simpa only [show (1 - (1 / 16 : ℝ)) = 15 / 16 by norm_num] using hgeom
  have hpow : 0 ≤ (1 / 16 : ℝ) ^ m := pow_nonneg (by norm_num) _
  nlinarith [hgeom', hpow]

/-- A scaled version of the frequency growth, starting from any index whose
frequency already resolves the interval. -/
private theorem e2_bmo2_scaled_growth (N : ℕ → ℕ)
    (hN : ∀ j, 16 * N j ≤ N (j + 1)) {i : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hbase : 1 ≤ ℓ * (N i : ℝ)) (d : ℕ) :
    (16 : ℝ) ^ d ≤ ℓ * (N (i + d) : ℝ) := by
  have hiter := e2_bmo2_iterate_growth N hN i d
  have hiterR : (16 : ℝ) ^ d * (N i : ℝ) ≤ (N (i + d) : ℝ) := by
    exact_mod_cast hiter
  have hp : 0 ≤ (16 : ℝ) ^ d := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbase hp
  calc
    (16 : ℝ) ^ d = (16 : ℝ) ^ d * 1 := by ring
    _ ≤ (16 : ℝ) ^ d * (ℓ * (N i : ℝ)) := hmul
    _ = ℓ * ((16 : ℝ) ^ d * (N i : ℝ)) := by ring
    _ ≤ ℓ * (N (i + d) : ℝ) := by gcongr

/-- Convert the frequency lower bound to the reciprocal estimate used in a
row sum. -/
private theorem e2_bmo2_reciprocal_bound {N : ℕ → ℕ} {j d : ℕ} {ℓ : ℝ}
    (hNj : 0 < N j) (hfreq : (16 : ℝ) ^ d ≤ ℓ * (N j : ℝ)) :
    3 / (N j : ℝ) ≤ 3 * ℓ / (16 : ℝ) ^ d := by
  have hNjR : 0 < (N j : ℝ) := by exact_mod_cast hNj
  have hpow : 0 < (16 : ℝ) ^ d := by positivity
  rw [div_le_div_iff₀ hNjR hpow]
  nlinarith [hfreq]

/-- The integral of a pair of cosine modes on the interval. -/
private def e2_bmo2_pairIntegral (N : ℕ → ℕ) (α ℓ : ℝ) (i j : ℕ) : ℝ :=
  ∫ t in α..α + ℓ, Real.cos ((N i : ℝ) * t) * Real.cos ((N j : ℝ) * t)

/-- The reciprocal larger-frequency bound for a non-diagonal Gram entry. -/
private def e2_bmo2_weight (N : ℕ → ℕ) (i j : ℕ) : ℝ :=
  3 / max (N i : ℝ) (N j : ℝ)

private theorem e2_bmo2_weight_symm (N : ℕ → ℕ) (i j : ℕ) :
    e2_bmo2_weight N i j = e2_bmo2_weight N j i := by
  simp [e2_bmo2_weight, max_comm]

private theorem e2_bmo2_pairIntegral_symm (N : ℕ → ℕ) (α ℓ : ℝ) (i j : ℕ) :
    e2_bmo2_pairIntegral N α ℓ i j = e2_bmo2_pairIntegral N α ℓ j i := by
  simp [e2_bmo2_pairIntegral, mul_comm]

/-- The product-mean estimate controls every off-diagonal entry by the reciprocal of the larger
frequency. -/
private theorem e2_bmo2_pair_bound (hmean : E2CosProductMeanStatement)
    (N : ℕ → ℕ) (hN : ∀ j, 0 < N j)
    (hgrowth : ∀ j, 16 * N j ≤ N (j + 1)) (α ℓ : ℝ) {i j : ℕ}
    (hij : i ≠ j) :
    |e2_bmo2_pairIntegral N α ℓ i j| ≤ e2_bmo2_weight N i j := by
  by_cases hlt : i < j
  · have hfreq := e2_bmo2_gap_growth N hgrowth hlt
    have hmono := e2_bmo2_mono N hgrowth (Nat.le_of_lt hlt)
    have h := hmean (N i : ℝ) (N j : ℝ) (by positivity)
      (by exact_mod_cast hN j) (by exact_mod_cast hfreq) α ℓ
    have hmonoR : (N i : ℝ) ≤ (N j : ℝ) := by exact_mod_cast hmono
    simpa [e2_bmo2_pairIntegral, e2_bmo2_weight, max_eq_right hmonoR]
      using h
  · have hji : j < i := by omega
    have hfreq := e2_bmo2_gap_growth N hgrowth hji
    have hmono := e2_bmo2_mono N hgrowth (Nat.le_of_lt hji)
    have h := hmean (N j : ℝ) (N i : ℝ) (by positivity)
      (by exact_mod_cast hN i) (by exact_mod_cast hfreq) α ℓ
    rw [e2_bmo2_pairIntegral_symm]
    have hmonoR : (N j : ℝ) ≤ (N i : ℝ) := by exact_mod_cast hmono
    simpa [e2_bmo2_pairIntegral, e2_bmo2_weight, max_eq_left hmonoR]
      using h

/-- The off-diagonal weights in each row have a uniform summable bound. -/
private theorem e2_bmo2_row_bound (N : ℕ → ℕ)
    (hN : ∀ j, 0 < N j) (hgrowth : ∀ j, 16 * N j ≤ N (j + 1))
    {K M i : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hK : 1 ≤ ℓ * (N K : ℝ))
    (hi : i ∈ Finset.Ico K M) :
    ∑ j ∈ (Finset.Ico K M).erase i, e2_bmo2_weight N i j ≤ ℓ / 2 := by
  have hKi : K ≤ i := (Finset.mem_Ico.mp hi).1
  have hiM : i < M := (Finset.mem_Ico.mp hi).2
  have hmono : ∀ {a b : ℕ}, a ≤ b → N a ≤ N b := by
    intro a b hab
    exact e2_bmo2_mono N hgrowth hab
  have hbase_i : 1 ≤ ℓ * (N i : ℝ) := by
    calc
      1 ≤ ℓ * (N K : ℝ) := hK
      _ ≤ ℓ * (N i : ℝ) := mul_le_mul_of_nonneg_left
        (by exact_mod_cast hmono hKi) hℓ.le
  have hpartition : (Finset.Ico K M).erase i =
      Finset.Ico K i ∪ Finset.Ico (i + 1) M := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Ico, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Ico K i) (Finset.Ico (i + 1) M) := by
    apply Finset.disjoint_left.mpr
    intro j hj1 hj2
    simp only [Finset.mem_Ico] at hj1 hj2
    omega
  rw [hpartition, Finset.sum_union hdisj]
  have hpast :
      ∑ j ∈ Finset.Ico K i, e2_bmo2_weight N i j ≤ ℓ / 4 := by
    have hpast_eq :
        (∑ j ∈ Finset.Ico K i, e2_bmo2_weight N i j) =
          (i - K : ℝ) * (3 / (N i : ℝ)) := by
      rw [show (∑ j ∈ Finset.Ico K i, e2_bmo2_weight N i j) =
          ∑ j ∈ Finset.Ico K i, 3 / (N i : ℝ) by
          apply Finset.sum_congr rfl
          intro j hj
          have hjiNat : N j ≤ N i := hmono (a := j) (b := i) (by
            exact (Finset.mem_Ico.mp hj).2.le)
          have hji : (N j : ℝ) ≤ (N i : ℝ) := by exact_mod_cast hjiNat
          rw [e2_bmo2_weight, max_eq_left hji]]
      simp [Nat.card_Ico, Nat.cast_sub hKi]
    have hfreq := e2_bmo2_scaled_growth N hgrowth hℓ hK (i - K)
    have hfreqIndex : K + (i - K) = i := Nat.add_sub_of_le hKi
    rw [hfreqIndex] at hfreq
    have hrecip := e2_bmo2_reciprocal_bound (hN i) hfreq
    have hdist_nonneg : 0 ≤ (i - K : ℝ) := by exact_mod_cast Nat.zero_le (i - K)
    have hpow : 0 < (16 : ℝ) ^ (i - K) := by positivity
    have hcoef :
        (i - K : ℝ) * (3 * ℓ / (16 : ℝ) ^ (i - K)) ≤ ℓ / 4 := by
      have hmul16 : (i - K : ℝ) * 16 ≤ (16 : ℝ) ^ (i - K) := by
        exact_mod_cast e2_bmo2_mul16_le_pow (i - K)
      have hdiv : (i - K : ℝ) / (16 : ℝ) ^ (i - K) ≤ 1 / 16 := by
        rw [div_le_iff₀ hpow]
        nlinarith [hmul16]
      calc
        _ = 3 * ℓ * ((i - K : ℝ) / (16 : ℝ) ^ (i - K)) := by ring
        _ ≤ 3 * ℓ * (1 / 16) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ ≤ ℓ / 4 := by nlinarith [hℓ]
    calc
      _ = (i - K : ℝ) * (3 / (N i : ℝ)) := hpast_eq
      _ ≤ (i - K : ℝ) * (3 * ℓ / (16 : ℝ) ^ (i - K)) :=
        mul_le_mul_of_nonneg_left hrecip hdist_nonneg
      _ ≤ ℓ / 4 := hcoef
  have hfuture :
      ∑ j ∈ Finset.Ico (i + 1) M, e2_bmo2_weight N i j ≤ ℓ / 4 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hfuture_eq :
        (∑ q ∈ Finset.range (M - (i + 1)),
            e2_bmo2_weight N i (i + 1 + q)) =
          ∑ q ∈ Finset.range (M - (i + 1)),
            3 / (N (i + 1 + q) : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hmonoR : (N i : ℝ) ≤ (N (i + 1 + q) : ℝ) := by
        exact_mod_cast hmono (a := i) (b := i + 1 + q) (by omega)
      rw [e2_bmo2_weight, max_eq_right hmonoR]
    rw [hfuture_eq]
    calc
      _ ≤ ∑ q ∈ Finset.range (M - (i + 1)),
          3 * ℓ / (16 : ℝ) ^ (q + 1) := by
        apply Finset.sum_le_sum
        intro q hq
        have hfreq := e2_bmo2_scaled_growth N hgrowth hℓ hbase_i (q + 1)
        have hidx : i + (q + 1) = i + 1 + q := by omega
        rw [hidx] at hfreq
        exact e2_bmo2_reciprocal_bound (hN (i + 1 + q)) hfreq
      _ ≤ ℓ / 5 := by
        calc
          _ = (3 * ℓ * (1 / 16 : ℝ)) *
              ∑ q ∈ Finset.range (M - (i + 1)), (1 / 16 : ℝ) ^ q := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            rw [pow_succ, one_div_pow]
            field_simp [pow_ne_zero _ (by norm_num : (16 : ℝ) ≠ 0)]
          _ ≤ (3 * ℓ * (1 / 16 : ℝ)) * (16 / 15) := by
            exact mul_le_mul_of_nonneg_left (e2_bmo2_geometric_sum _)
              (by positivity)
          _ = ℓ / 5 := by ring
      _ ≤ ℓ / 4 := by linarith [hℓ]
  linarith

/-- A real product is bounded by the sum of its squared factors. -/
private theorem e2_bmo2_abs_mul_le_sq_add (a b : ℝ) :
    |a * b| ≤ a ^ 2 + b ^ 2 := by
  have ha : |a| ^ 2 = a ^ 2 := sq_abs a
  have hb : |b| ^ 2 = b ^ 2 := sq_abs b
  have hab : |a * b| = |a| * |b| := abs_mul a b
  nlinarith [sq_nonneg (|a| - |b|), ha, hb, hab]

/-- A finite sum of cosines with sixteen-fold lacunary frequencies has
uniformly bounded interval `L²` norm once the interval resolves its first
frequency. -/
theorem e2_highFrequency_L2_proof :
    E2CosProductMeanStatement → E2HighFrequencyL2Statement := by
  intro hmean c N hN hgrowth α ℓ hℓ K hK M
  let F := Finset.Ico K M
  let A := e2_bmo2_pairIntegral N α ℓ
  let w := e2_bmo2_weight N
  let f : ℕ → ℕ → ℝ := fun i j => c i * c j * A i j
  let energy : ℝ := ∑ i ∈ F, c i ^ 2
  have hpairInt (i j : ℕ) :
      IntervalIntegrable
        (fun t : ℝ => (c i * c j) *
          (Real.cos ((N i : ℝ) * t) * Real.cos ((N j : ℝ) * t)))
        volume α (α + ℓ) := by
    have hcont : Continuous (fun t : ℝ => (c i * c j) *
        (Real.cos ((N i : ℝ) * t) * Real.cos ((N j : ℝ) * t))) := by fun_prop
    exact hcont.intervalIntegrable _ _
  have hinnerInt (i : ℕ) :
      IntervalIntegrable
        (fun t : ℝ => ∑ j ∈ F, (c i * c j) *
          (Real.cos ((N i : ℝ) * t) * Real.cos ((N j : ℝ) * t)))
        volume α (α + ℓ) := by
    convert IntervalIntegrable.sum F (fun j hj => hpairInt i j) using 1
    ext t
    simp
  have hexpandPoint (t : ℝ) :
      (∑ j ∈ F, c j * Real.cos ((N j : ℝ) * t)) ^ 2 =
        ∑ i ∈ F, ∑ j ∈ F, (c i * c j) *
          (Real.cos ((N i : ℝ) * t) * Real.cos ((N j : ℝ) * t)) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hexpandIntegral :
      (∫ t in α..α + ℓ, (∑ j ∈ F, c j * Real.cos ((N j : ℝ) * t)) ^ 2) =
        ∑ i ∈ F, ∑ j ∈ F, f i j := by
    rw [show (fun t : ℝ => (∑ j ∈ F, c j * Real.cos ((N j : ℝ) * t)) ^ 2) =
        (fun t => ∑ i ∈ F, ∑ j ∈ F, (c i * c j) *
          (Real.cos ((N i : ℝ) * t) * Real.cos ((N j : ℝ) * t))) by
        funext t
        exact hexpandPoint t]
    rw [intervalIntegral.integral_finsetSum (fun i hi => hinnerInt i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum (fun j hj => hpairInt i j)]
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, A, e2_bmo2_pairIntegral, intervalIntegral.integral_const_mul]
  have hsplit :
      (∑ i ∈ F, ∑ j ∈ F, f i j) =
        (∑ i ∈ F, f i i) + ∑ i ∈ F, ∑ j ∈ F.erase i, f i j := by
    calc
      _ = ∑ i ∈ F, (f i i + ∑ j ∈ F.erase i, f i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_erase_add _ _ hi]
        ring
      _ = _ := by rw [Finset.sum_add_distrib]
  have hdiagA (i : ℕ) : A i i ≤ ℓ := by
    change e2_bmo2_pairIntegral N α ℓ i i ≤ ℓ
    have hcosInt : IntervalIntegrable
        (fun t : ℝ => Real.cos ((N i : ℝ) * t) ^ 2) volume α (α + ℓ) := by
      have hc : Continuous (fun t : ℝ => Real.cos ((N i : ℝ) * t) ^ 2) := by fun_prop
      exact hc.intervalIntegrable _ _
    have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume α (α + ℓ) :=
      intervalIntegrable_const
    have hmono :
        (∫ t in α..α + ℓ, Real.cos ((N i : ℝ) * t) ^ 2) ≤
          ∫ t in α..α + ℓ, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on (hab := by linarith)
        (hf := hcosInt) (hg := hconst)
      intro t ht
      have hs := Real.sin_sq_add_cos_sq ((N i : ℝ) * t)
      nlinarith [sq_nonneg (Real.sin ((N i : ℝ) * t))]
    have hconstInt : (∫ t in α..α + ℓ, (1 : ℝ)) = ℓ := by
      simp [intervalIntegral.integral_const]
    rw [e2_bmo2_pairIntegral, show
      (fun t : ℝ => Real.cos ((N i : ℝ) * t) * Real.cos ((N i : ℝ) * t)) =
        (fun t => Real.cos ((N i : ℝ) * t) ^ 2) by
          funext t
          ring]
    rw [hconstInt] at hmono
    exact hmono
  have hdiag : (∑ i ∈ F, f i i) ≤ ℓ * energy := by
    calc
      _ ≤ ∑ i ∈ F, c i ^ 2 * ℓ := by
        apply Finset.sum_le_sum
        intro i hi
        change c i * c i * e2_bmo2_pairIntegral N α ℓ i i ≤ c i ^ 2 * ℓ
        have hA : e2_bmo2_pairIntegral N α ℓ i i ≤ ℓ := hdiagA i
        have hsq : c i * c i = c i ^ 2 := by ring
        rw [hsq]
        exact mul_le_mul_of_nonneg_left hA (sq_nonneg (c i))
      _ = ℓ * energy := by
        dsimp [energy]
        calc
          _ = ∑ i ∈ F, ℓ * c i ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = ℓ * ∑ i ∈ F, c i ^ 2 := by rw [Finset.mul_sum]
  have hrow : ∀ i ∈ F, (∑ j ∈ F.erase i, w i j) ≤ ℓ / 2 := by
    intro i hi
    exact e2_bmo2_row_bound N hN hgrowth hℓ hK hi
  have hoffTerm : ∀ i j, i ≠ j → f i j ≤ (c i ^ 2 + c j ^ 2) * w i j := by
    intro i j hij
    have hA := e2_bmo2_pair_bound hmean N hN hgrowth α ℓ hij
    have hyoung := e2_bmo2_abs_mul_le_sq_add (c i) (c j)
    dsimp [f, A, w]
    calc
      c i * c j * e2_bmo2_pairIntegral N α ℓ i j ≤
          |c i * c j * e2_bmo2_pairIntegral N α ℓ i j| := le_abs_self _
      _ = |c i * c j| * |e2_bmo2_pairIntegral N α ℓ i j| := by rw [abs_mul]
      _ ≤ (c i ^ 2 + c j ^ 2) * e2_bmo2_weight N i j := by
        exact mul_le_mul hyoung hA (abs_nonneg _) (by positivity)
  have hoffDecomp :
      (∑ i ∈ F, ∑ j ∈ F.erase i, (c i ^ 2 + c j ^ 2) * w i j) =
        (∑ i ∈ F, c i ^ 2 * ∑ j ∈ F.erase i, w i j) +
          ∑ i ∈ F, ∑ j ∈ F.erase i, c j ^ 2 * w i j := by
    simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcomm :
      (∑ i ∈ F, ∑ j ∈ F.erase i, c j ^ 2 * w i j) =
        ∑ j ∈ F, ∑ i ∈ F.erase j, c j ^ 2 * w i j := by
    apply Finset.sum_comm'
    intro i j
    simp only [Finset.mem_erase]
    tauto
  have hsecond :
      (∑ i ∈ F, ∑ j ∈ F.erase i, c j ^ 2 * w i j) =
        ∑ i ∈ F, c i ^ 2 * ∑ j ∈ F.erase i, w i j := by
    rw [hcomm]
    calc
      _ = ∑ i ∈ F, ∑ j ∈ F.erase i, c i ^ 2 * w i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [show w j i = w i j by
          dsimp [w]
          exact e2_bmo2_weight_symm N j i]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum]
  have hfirst :
      (∑ i ∈ F, c i ^ 2 * ∑ j ∈ F.erase i, w i j) ≤ ℓ / 2 * energy := by
    calc
      _ ≤ ∑ i ∈ F, (ℓ / 2) * c i ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          c i ^ 2 * ∑ j ∈ F.erase i, w i j =
              (∑ j ∈ F.erase i, w i j) * c i ^ 2 := by ring
          _ ≤ (ℓ / 2) * c i ^ 2 :=
            mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg (c i))
      _ = ℓ / 2 * energy := by
        simp [energy, Finset.mul_sum]
  have hoff : (∑ i ∈ F, ∑ j ∈ F.erase i, f i j) ≤ ℓ * energy := by
    calc
      _ ≤ ∑ i ∈ F, ∑ j ∈ F.erase i, (c i ^ 2 + c j ^ 2) * w i j := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hoffTerm i j (Finset.ne_of_mem_erase hj).symm
      _ = (∑ i ∈ F, c i ^ 2 * ∑ j ∈ F.erase i, w i j) +
          ∑ i ∈ F, ∑ j ∈ F.erase i, c j ^ 2 * w i j := hoffDecomp
      _ = (∑ i ∈ F, c i ^ 2 * ∑ j ∈ F.erase i, w i j) * 2 := by
        rw [hsecond]
        ring
      _ ≤ (ℓ / 2 * energy) * 2 := by
        exact mul_le_mul_of_nonneg_right hfirst (by norm_num)
      _ = ℓ * energy := by ring
  calc
    (∫ t in α..α + ℓ, (∑ j ∈ F, c j * Real.cos ((N j : ℝ) * t)) ^ 2) =
        (∑ i ∈ F, f i i) + ∑ i ∈ F, ∑ j ∈ F.erase i, f i j := by
      rw [hexpandIntegral, hsplit]
    _ ≤ ℓ * energy + ℓ * energy := add_le_add hdiag hoff
    _ ≤ 5 * ℓ * energy := by
      have henergy : 0 ≤ energy := by
        dsimp [energy]
        exact Finset.sum_nonneg fun i hi => sq_nonneg (c i)
      nlinarith [mul_nonneg hℓ.le henergy]

end ParabolicRectifiability.Examples
