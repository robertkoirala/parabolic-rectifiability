import ParabolicRectifiability.BetaP.Proofs.Carrier.Separated

/-! # Variable-radius packing with its own transfer

Proves `ccar_variable_packing : CellsPackingStatement → CarrierVariablePackingStatement` as
`ccar_variable_packing_proof`, in implication form: the statement `CellsPackingStatement` is a
hypothesis.

The proof is the `p`-version of the quadratic `variable_radius_packing_of_discrete`, with the
quadratic transfer replaced by `CellsPackingStatement`. It is
**not** derived from the equal-radius nets (`ccar_separated`); it has its own transfer. For
disjoint balls
`P(z_i,r_i)` with `z_i ∈ K ∩ P(q,R)`, `0 < r_i ≤ R ≤ 1`:

* closed cells `P̄(z_i, r_i/100)` (inside the disjoint balls) of mass `≥ a (r_i/100)^k`;
  energy samples by `exists_mem_of_ae_of_measure_ne_zero`;
* barycenter cells with `radius = r_i`, `ε = 1/100`, cutoff `r_i/2`, synthetic weights
  `(r_i/2)^k`, `A = 50^k/a`;
* cutoff balls `P(c_i, r_i/2) ⊆ P(z_i, r_i)`, hence pairwise disjoint and inside `P(q,2R)`;
* `CellsPackingStatement` with `b = 1` gives
  `Σ (r_i/2)^k ≤ Ct (1 + 50^k 2^{k+p} L^{p/2}/a) (2R)^k`; multiply by `2^k`;
* arithmetic (`ccarn_variable_arith`): `50^k 2^k = 100^k`, `2^k 2^k 100^k = 400^k`,
  `400^k ≤ 400^(n+1)` (`k ≤ n+1`).

Constant (chosen after `n, p, Ct`, before `k, T, ν, L, a, K`): `C_v = Ct 2^p 400^(n+1)`.

Remark: `HasFiniteBallPacking` quantifies over finite
families only, which is all that `CarrierVariablePackingStatement` needs. Every disjoint family of positive-radius
open balls in this separable space is countable, so the finite-subfamily bound gives the same
bound for every disjoint family (supremum of the finite subsums); no Lean declaration is made
for this remark.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP.CarrierTree

open ParabolicRectifiability.Foundations

/-- The arithmetic of the variable-radius bound: with `P₂ ≥ 1` (later `P₂ = 2^p`,
`M = L^{p/2}`) and `k ≤ n + 1`,
`2^k · Ct (1 + 50^k/a · (2^k P₂) · M) (2R)^k ≤ Ct P₂ 400^(n+1) (1 + M/a) R^k`. -/
theorem ccarn_variable_arith {n k : ℕ} (hk : k ≤ n + 1) {Ct a M P2 R : ℝ} (hCt : 0 < Ct)
    (ha : 0 < a) (hM : 0 ≤ M) (hP2 : 1 ≤ P2) (hR : 0 < R) :
    2 ^ k * (Ct * (1 + 50 ^ k / a * (2 ^ k * P2) * M) * (2 * R) ^ k) ≤
      Ct * P2 * 400 ^ (n + 1) * (1 + M / a) * R ^ k := by
  have hP0 : 0 ≤ P2 := zero_le_one.trans hP2
  have hMa : 0 ≤ M / a := div_nonneg hM ha.le
  have hLa : 0 ≤ 1 + M / a := by linarith
  have hRk : 0 ≤ R ^ k := pow_nonneg hR.le k
  have hX : 1 + 50 ^ k / a * (2 ^ k * P2) * M ≤ 100 ^ k * P2 * (1 + M / a) := by
    have h100 : (1 : ℝ) ≤ 100 ^ k * P2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hP2
    have e100 : (100 : ℝ) ^ k = 50 ^ k * 2 ^ k := by
      rw [← mul_pow]
      norm_num
    have e : (50 : ℝ) ^ k / a * (2 ^ k * P2) * M = 100 ^ k * P2 * (M / a) := by
      rw [e100]
      ring
    rw [e, mul_add, mul_one]
    linarith
  have e400 : (2 : ℝ) ^ k * 2 ^ k * 100 ^ k = 400 ^ k := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  have h400 : (400 : ℝ) ^ k ≤ 400 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) hk
  calc 2 ^ k * (Ct * (1 + 50 ^ k / a * (2 ^ k * P2) * M) * (2 * R) ^ k)
      = Ct * (1 + 50 ^ k / a * (2 ^ k * P2) * M) * ((2 ^ k * 2 ^ k) * R ^ k) := by
        rw [mul_pow]; ring
    _ ≤ Ct * (100 ^ k * P2 * (1 + M / a)) * ((2 ^ k * 2 ^ k) * R ^ k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hCt.le) (by positivity)
    _ = Ct * P2 * ((2 : ℝ) ^ k * 2 ^ k * 100 ^ k) * (1 + M / a) * R ^ k := by ring
    _ = Ct * P2 * 400 ^ k * (1 + M / a) * R ^ k := by rw [e400]
    _ ≤ Ct * P2 * 400 ^ (n + 1) * (1 + M / a) * R ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h400 (mul_nonneg hCt.le hP0)) hLa) hRk

/-- The variable-radius bound for one lower-mass set and one finite disjoint family
(`p`-version of the body of `variable_radius_packing_of_discrete`, own transfer). -/
theorem ccarn_variable_packing_sum (hcp : CellsPackingStatement) {n : ℕ} {p Ct : ℝ}
    (hp : 2 ≤ p) (hCt : 0 < Ct) (htrunc : ActiveRadiusPackingTruncatedBound n p Ct)
    {k : ℕ} {T : FamilyKind} (hk : 1 ≤ k) (hkn : k < n + 2) (hT : Nonempty (Models n k T))
    (ν : Measure (Space n)) [IsFiniteMeasure ν] {L a : ℝ} (hL : 0 ≤ L) (ha : 0 < a)
    (hae : ∀ᵐ z ∂ν, allScaleEnergyP ν k T p z ≤ ENNReal.ofReal L)
    {K : Set (Space n)} (hlow : HasUniformLowerMass ν k a K)
    (q : Space n) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) {l : ℕ} (z : Fin l → Space n)
    (r : Fin l → ℝ) (hz : ∀ i, z i ∈ K ∩ Metric.ball q R) (hr : ∀ i, 0 < r i ∧ r i ≤ R)
    (hd : ∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) :
    (∑ i, ENNReal.ofReal (r i) ^ k) ≤
      ENNReal.ofReal (Ct * (2 : ℝ) ^ p * 400 ^ (n + 1) * (1 + L ^ (p / 2) / a) * R ^ k) := by
  -- Lower mass of each cell `P̄(z_i, r_i/100)`.
  have hcell_r : ∀ i, 0 < (1 / 100 : ℝ) * r i := fun i => by
    have := (hr i).1
    positivity
  have hcell_le : ∀ i, (1 / 100 : ℝ) * r i ≤ 1 := fun i => by
    have := (hr i).1
    have := (hr i).2
    linarith
  have hlow_i : ∀ i, ENNReal.ofReal (a * ((1 / 100 : ℝ) * r i) ^ k) ≤
      ν (Metric.closedBall (z i) ((1 / 100 : ℝ) * r i)) :=
    fun i => hlow (z i) (hz i).1 _ (hcell_r i) (hcell_le i)
  have hmass_pos : ∀ i, 0 < a * ((1 / 100 : ℝ) * r i) ^ k :=
    fun i => mul_pos ha (pow_pos (hcell_r i) k)
  have hmass_ne_zero : ∀ i, ν (Metric.closedBall (z i) ((1 / 100 : ℝ) * r i)) ≠ 0 :=
    fun i => (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (hmass_pos i)) (hlow_i i)).ne'
  -- Energy samples in each cell.
  have hgood : ∀ i, ∃ y ∈ Metric.closedBall (z i) ((1 / 100 : ℝ) * r i),
      allScaleEnergyP ν k T p y ≤ ENNReal.ofReal L :=
    fun i => exists_mem_of_ae_of_measure_ne_zero hae (hmass_ne_zero i)
  choose y hy hyL using hgood
  have hweight_le : ∀ i, (r i / 2) ^ k ≤ 50 ^ k / a *
      (ν (Metric.closedBall (z i) ((1 / 100 : ℝ) * r i))).toReal := by
    intro i
    have hm : a * ((1 / 100 : ℝ) * r i) ^ k ≤
        (ν (Metric.closedBall (z i) ((1 / 100 : ℝ) * r i))).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top ν _)).mp (hlow_i i)
    have heq : (r i / 2) ^ k = 50 ^ k / a * (a * ((1 / 100 : ℝ) * r i) ^ k) := by
      rw [← mul_assoc, div_mul_cancel₀ _ ha.ne', ← mul_pow]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hm (div_nonneg (pow_nonneg (by norm_num) k) ha.le)
  let D : FiniteBarycenterCells ν (Fin l) :=
    { cell := fun i => Metric.closedBall (z i) ((1 / 100 : ℝ) * r i)
      measurable_cell := fun i => Metric.isClosed_closedBall.measurableSet
      disjoint_cell := fun i j hij => (hd i j hij).mono
        (Metric.closedBall_subset_ball (by have := (hr i).1; linarith))
        (Metric.closedBall_subset_ball (by have := (hr j).1; linarith))
      mass_ne_zero := hmass_ne_zero
      mass_ne_top := fun i => measure_ne_top ν _
      center := z
      radius := r
      radius_pos := fun i => (hr i).1
      ε := 1 / 100
      ε_pos := by norm_num
      ε_le := by norm_num
      cell_subset := fun i => subset_rfl
      sample := y
      sample_mem := hy
      weight := fun i => (r i / 2) ^ k
      weight_pos := fun i => pow_pos (by have := (hr i).1; linarith) k
      A := 50 ^ k / a
      A_nonneg := div_nonneg (pow_nonneg (by norm_num) k) ha.le
      weight_le := hweight_le }
  -- Cutoff balls lie inside the original balls.
  have hsub : ∀ i, Metric.ball (D.barycenter i) (D.cutoff i) ⊆ Metric.ball (z i) (r i) := by
    intro i x hx
    have hc : dist (D.barycenter i) (z i) ≤ (1 / 100 : ℝ) * r i :=
      Metric.mem_closedBall.mp (D.barycenter_mem_closedBall i)
    have hx' : dist x (D.barycenter i) < r i / 2 := Metric.mem_ball.mp hx
    have := (hr i).1
    rw [Metric.mem_ball]
    linarith [dist_triangle x (D.barycenter i) (z i)]
  have hball : ∀ i, Metric.ball (D.barycenter i) (D.cutoff i) ⊆ Metric.ball q (2 * R) := by
    intro i
    refine (hsub i).trans fun x hx => ?_
    have h1 := Metric.mem_ball.mp hx
    have h2 := Metric.mem_ball.mp (hz i).2
    have := (hr i).2
    rw [Metric.mem_ball]
    linarith [dist_triangle x (z i) q]
  have hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (D.barycenter i) (D.cutoff i))
      (Metric.ball (D.barycenter j) (D.cutoff j)) :=
    fun i j hij => (hd i j hij).mono (hsub i) (hsub j)
  have hw : ∀ i, D.weight i ≤ 1 * D.cutoff i ^ k := fun i => by
    show (r i / 2) ^ k ≤ 1 * (r i / 2) ^ k
    rw [one_mul]
  have hsampleE : ∀ i, allScaleEnergyP ν k T p (D.sample i) ≤ ENNReal.ofReal L := hyL
  have key := hcp n p Ct hp htrunc k T hk hkn hT ν l D L hL hsampleE q (2 * R) 1
    (by positivity) one_pos hball hdisj hw
  -- Return to the original radii.
  have h20 : (0 : ℝ) ≤ 2 := by norm_num
  have h2k0 : (0 : ℝ) ≤ 2 ^ k := pow_nonneg h20 k
  have hterm : ∀ i, ENNReal.ofReal (r i) ^ k = 2 ^ k * ENNReal.ofReal (D.weight i) := by
    intro i
    have e : r i ^ k = 2 ^ k * (r i / 2) ^ k := by
      rw [← mul_pow]
      congr 1
      ring
    show ENNReal.ofReal (r i) ^ k = 2 ^ k * ENNReal.ofReal ((r i / 2) ^ k)
    rw [← ENNReal.ofReal_pow (hr i).1.le, e, ENNReal.ofReal_mul h2k0, ENNReal.ofReal_pow h20,
      ENNReal.ofReal_ofNat]
  have hA : D.A = 50 ^ k / a := rfl
  have hM : 0 ≤ L ^ (p / 2) := Real.rpow_nonneg hL _
  have hP2 : (1 : ℝ) ≤ (2 : ℝ) ^ p := Real.one_le_rpow (by norm_num) (by linarith)
  calc ∑ i, ENNReal.ofReal (r i) ^ k
      = ∑ i, 2 ^ k * ENNReal.ofReal (D.weight i) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = 2 ^ k * ∑ i, ENNReal.ofReal (D.weight i) := by rw [Finset.mul_sum]
    _ ≤ 2 ^ k * ENNReal.ofReal
          (Ct * (1 + D.A * (2 : ℝ) ^ ((k : ℝ) + p) * L ^ (p / 2)) * (2 * R) ^ k) :=
        mul_le_mul_of_nonneg_left key zero_le
    _ = ENNReal.ofReal
          (2 ^ k * (Ct * (1 + 50 ^ k / a * (2 ^ k * (2 : ℝ) ^ p) * L ^ (p / 2)) * (2 * R) ^ k)) := by
        rw [hA, ccarn_two_rpow_add, ENNReal.ofReal_mul h2k0, ENNReal.ofReal_pow h20,
          ENNReal.ofReal_ofNat]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (ccarn_variable_arith (by omega) hCt ha hM hP2 hR)

/-- **Variable-radius packing** (`ccar_variable_packing`), with its own transfer and the constant
`C_v = Ct 2^p 400^(n+1)`. -/
theorem ccar_variable_packing_proof :
    CellsPackingStatement → CarrierVariablePackingStatement := by
  intro hcp n _hn p hp Ct hCt htrunc
  refine ⟨Ct * (2 : ℝ) ^ p * 400 ^ (n + 1), by positivity, ?_⟩
  intro k hk hkn T hT ν hfin L a hL ha hae K hlow q R hR hR1 l z r hz hr hd
  exact ccarn_variable_packing_sum hcp hp hCt htrunc hk hkn hT ν hL ha hae hlow q hR hR1 z r
    hz hr hd

end ParabolicRectifiability.BetaP.CarrierTree
