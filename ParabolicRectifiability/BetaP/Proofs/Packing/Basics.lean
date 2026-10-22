import ParabolicRectifiability.BetaP.Proofs.Packing.PackingStatements
import ParabolicRectifiability.Measure.AtomicTruncation
import ParabolicRectifiability.Measure.Neck.Packing

/-! # Four auxiliary statements for the active-radius packing bound

Proofs of four of the statements used for `activeRadiusPacking_of_discretePacking`:

* `cpk_absorption_proof : CpkAbsorptionStatement` (bootstrap absorption);
* `cpk_massBound_proof : CpkMassBoundStatement` (mass bound);
* `cpk_activeSource_proof : CpkActiveSourceStatement` (active-source identity);
* `cpk_leastActiveBound_proof : CpkLeastActiveBoundStatement` (least active bound).

Both `truncatedAtomicSource` constants (the quadratic one and the `BetaP` one) are visible; every
occurrence here is qualified as `BetaP.truncatedAtomicSource`. Helpers carry the prefix `cpk1_`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## Bootstrap absorption -/

/-- **Bootstrap absorption.** Either `Λ ≤ 2Db`, or `Λ > 0` and
`Λ < 2D Λ^{1-2/p} B`, whence `Λ^{2/p} < 2DB` and `Λ < (2D)^{p/2} B^{p/2}`. -/
theorem cpk_absorption_proof : CpkAbsorptionStatement := by
  intro p D b B Λ hp hD hb hB hΛ hrec
  have hp0 : 0 < p := by linarith
  have hM1 : 2 * D ≤ max (2 * D) ((2 * D) ^ (p / 2)) := le_max_left _ _
  have hM2 : (2 * D) ^ (p / 2) ≤ max (2 * D) ((2 * D) ^ (p / 2)) := le_max_right _ _
  have hBp : 0 ≤ B ^ (p / 2) := Real.rpow_nonneg hB _
  have hsum : 0 ≤ b + B ^ (p / 2) := add_nonneg hb hBp
  by_cases hcase : Λ ≤ 2 * D * b
  · calc Λ ≤ 2 * D * b := hcase
      _ ≤ 2 * D * (b + B ^ (p / 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ ≤ max (2 * D) ((2 * D) ^ (p / 2)) * (b + B ^ (p / 2)) :=
          mul_le_mul_of_nonneg_right hM1 hsum
  · push Not at hcase
    have hDb : 0 ≤ 2 * D * b := by positivity
    have hΛpos : 0 < Λ := lt_of_le_of_lt hDb hcase
    have hapos : 0 < Λ ^ (1 - 2 / p) := Real.rpow_pos_of_pos hΛpos _
    have hsplit : Λ = Λ ^ (2 / p) * Λ ^ (1 - 2 / p) := by
      rw [← Real.rpow_add hΛpos]
      have h1 : 2 / p + (1 - 2 / p) = 1 := by ring
      rw [h1, Real.rpow_one]
    have hrec' : Λ ≤ D * b + D * (Λ ^ (1 - 2 / p) * B) := by
      rw [← mul_add]; exact hrec
    have hlt1 : Λ < 2 * D * B * Λ ^ (1 - 2 / p) := by
      have h2 : D * (Λ ^ (1 - 2 / p) * B) = D * B * Λ ^ (1 - 2 / p) := by ring
      have h3 : 2 * D * B * Λ ^ (1 - 2 / p) = 2 * (D * B * Λ ^ (1 - 2 / p)) := by ring
      rw [h2] at hrec'
      rw [h3]
      linarith
    have hlt2 : Λ ^ (2 / p) < 2 * D * B := by
      have h4 : Λ ^ (2 / p) * Λ ^ (1 - 2 / p) < 2 * D * B * Λ ^ (1 - 2 / p) := by
        rw [← hsplit]
        exact hlt1
      exact lt_of_mul_lt_mul_right h4 hapos.le
    have hlt3 : (Λ ^ (2 / p)) ^ (p / 2) < (2 * D * B) ^ (p / 2) :=
      Real.rpow_lt_rpow (Real.rpow_nonneg hΛ _) hlt2 (by positivity)
    have hL : (Λ ^ (2 / p)) ^ (p / 2) = Λ := by
      rw [← Real.rpow_mul hΛ]
      have h1 : 2 / p * (p / 2) = 1 := by field_simp
      rw [h1, Real.rpow_one]
    have hR : (2 * D * B) ^ (p / 2) = (2 * D) ^ (p / 2) * B ^ (p / 2) :=
      Real.mul_rpow (by positivity) hB
    rw [hL, hR] at hlt3
    have hMnn : 0 ≤ max (2 * D) ((2 * D) ^ (p / 2)) := le_trans (by linarith) hM1
    calc Λ ≤ (2 * D) ^ (p / 2) * B ^ (p / 2) := hlt3.le
      _ ≤ max (2 * D) ((2 * D) ^ (p / 2)) * B ^ (p / 2) :=
          mul_le_mul_of_nonneg_right hM2 hBp
      _ ≤ max (2 * D) ((2 * D) ^ (p / 2)) * (b + B ^ (p / 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hMnn

/-! ## Mass bound -/

/-- **Mass bound.** Every centre lies in `P(q,R)` and every radius is at most `R`,
so the active filter at `(q,R)` is everything; if `R ≤ 0` the family is empty. -/
theorem cpk_massBound_proof : CpkMassBoundStatement := by
  intro n N k q R z r w b Λ hP hΛ
  have hmem : ∀ i, dist (z i) q < R := fun i =>
    Metric.mem_ball.mp (hP.ball_subset i (Metric.mem_ball_self (hP.radius_pos i)))
  have hterm : ∀ i, 0 ≤ w i * r i ^ k := fun i =>
    mul_nonneg (hP.weight_pos i).le (pow_nonneg (hP.radius_pos i).le k)
  have hsrc : atomicSource k z r w univ = ENNReal.ofReal (∑ i, w i * r i ^ k) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hterm i)]
    simp only [atomicSource, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
  by_cases hR : 0 < R
  · have hfilt : Finset.univ.filter (fun i => r i ≤ R ∧ dist (z i) q < R) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      exact ⟨radius_le_of_ball_subset (hP.radius_pos i) (hP.ball_subset i), hmem i⟩
    have hmass : cpkActiveMass k z r w q R = ∑ i, w i * r i ^ k := by
      unfold cpkActiveMass
      rw [hfilt]
    rw [hsrc, ← hmass]
    exact ENNReal.ofReal_le_ofReal (hΛ q R hR)
  · have hN : ∀ i : Fin N, False := fun i => hR (lt_of_le_of_lt dist_nonneg (hmem i))
    have h0 : (∑ i : Fin N, w i * r i ^ k) = 0 := Finset.sum_eq_zero (fun i _ => (hN i).elim)
    rw [hsrc, h0, ENNReal.ofReal_zero]
    exact zero_le

/-! ## Active-source identity -/

/-- `fitPow` sees only the restriction of the source to the testing ball (the `p`-analogue of
`fit_eq_of_restrict_ball_eq`). -/
theorem cpk1_fitPow_eq_of_restrict_eq {n k : ℕ} {T : FamilyKind} {μ μ' : Measure (Space n)}
    (p : ℝ) (L : Models n k T) (x : Space n) (s : ℝ)
    (h : μ.restrict (Metric.ball x s) = μ'.restrict (Metric.ball x s)) :
    fitPow μ p L x s = fitPow μ' p L x s := by
  unfold fitPow
  rw [h]

/-- For pairwise disjoint open balls of positive radii and `s ≥ r_i`, BetaP's truncated testing
source and the full atomic source agree on `P(z_i, s)` (adapted from
`restrict_ball_finiteCutoffAtomicMeasure_eq_fullAtomicMeasure`). -/
theorem cpk1_restrict_ball_truncated_eq {n N : ℕ} (k : ℕ) (z : Fin N → Space n)
    (r w : Fin N → ℝ) (hr : ∀ i, 0 < r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j)))
    {i : Fin N} {s : ℝ} (hs : r i ≤ s) :
    (BetaP.truncatedAtomicSource k z r w s).restrict (Metric.ball (z i) s) =
      (atomicSource k z r w).restrict (Metric.ball (z i) s) := by
  ext t ht
  have hm : MeasurableSet (t ∩ Metric.ball (z i) s) := ht.inter measurableSet_ball
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
  simp only [BetaP.truncatedAtomicSource, atomicSource, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rfl
  · have hji : i ≠ j := fun h => hj (h ▸ hs)
    have hfar : z j ∉ t ∩ Metric.ball (z i) s := by
      intro hx
      have h1 := radius_le_dist_of_pairwise_disjoint_balls z r hr
        (fun a b hab => hdisj a b hab) hji
      have h2 : dist (z j) (z i) < s := hx.2
      rw [dist_comm] at h2
      linarith [not_le.mp hj]
    rw [Measure.dirac_apply' _ hm, Set.indicator_of_notMem hfar]
    simp

/-- **Active-source identity.** Above its own radius a centre sees the full source and the
truncated testing source alike, for every exponent, family and weights. -/
theorem cpk_activeSource_proof : CpkActiveSourceStatement := by
  intro n N k T p z r w hr hdisj i s hs
  have h := cpk1_restrict_ball_truncated_eq k z r w hr hdisj hs
  unfold betaPow
  split_ifs
  · congr 1
    exact iInf_congr fun L => cpk1_fitPow_eq_of_restrict_eq p L (z i) s h
  · rfl

/-! ## The least active bound -/

/-- The active mass is nonnegative for positive radii and weights. -/
theorem cpk1_activeMass_nonneg {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ)
    (hr : ∀ i, 0 < r i) (hw : ∀ i, 0 < w i) (x : Space n) (s : ℝ) :
    0 ≤ cpkActiveMass k z r w x s :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (pow_nonneg (hr i).le k)

/-- Each active term has `0 < r_i ≤ s`, so the active mass is at most `(Σ_i w_i) s^k`. -/
theorem cpk1_activeMass_le {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ)
    (hr : ∀ i, 0 < r i) (hw : ∀ i, 0 < w i) (x : Space n) {s : ℝ} (hs : 0 < s) :
    cpkActiveMass k z r w x s ≤ (∑ i, w i) * s ^ k := by
  unfold cpkActiveMass
  calc ∑ i ∈ Finset.univ.filter (fun i => r i ≤ s ∧ dist (z i) x < s), w i * r i ^ k
      ≤ ∑ i ∈ Finset.univ.filter (fun i => r i ≤ s ∧ dist (z i) x < s), w i * s ^ k := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hr i).le (Finset.mem_filter.mp hi).2.1 k) (hw i).le
    _ ≤ ∑ i, w i * s ^ k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => mul_nonneg (hw i).le (pow_nonneg hs.le k))
    _ = (∑ i, w i) * s ^ k := (Finset.sum_mul _ _ _).symm

/-- **The least active bound.** `Λ = sup {s^{-k} cpkActiveMass x s : x, s > 0}`: the set is
nonempty, nonnegative and bounded by `Σ_i w_i`, so its supremum is a nonnegative active bound
below every active bound. -/
theorem cpk_leastActiveBound_proof : CpkLeastActiveBoundStatement := by
  intro n N k z r w b hr hw _hb
  set S : Set ℝ :=
    {y | ∃ (x : Space n) (s : ℝ), 0 < s ∧ y = cpkActiveMass k z r w x s / s ^ k} with hS
  have hne : S.Nonempty :=
    ⟨cpkActiveMass k z r w (point 0 0) 1 / 1 ^ k, point 0 0, 1, one_pos, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨∑ i, w i, ?_⟩
    rintro y ⟨x, s, hs, rfl⟩
    exact (div_le_iff₀ (pow_pos hs k)).mpr (cpk1_activeMass_le k z r w hr hw x hs)
  refine ⟨sSup S, ?_, ?_, ?_⟩
  · apply Real.sSup_nonneg
    rintro y ⟨x, s, hs, rfl⟩
    exact div_nonneg (cpk1_activeMass_nonneg k z r w hr hw x s) (pow_nonneg hs.le k)
  · intro x s hs
    have hle : cpkActiveMass k z r w x s / s ^ k ≤ sSup S := le_csSup hbdd ⟨x, s, hs, rfl⟩
    exact (div_le_iff₀ (pow_pos hs k)).mp hle
  · intro Λ' hΛ'
    apply csSup_le hne
    rintro y ⟨x, s, hs, rfl⟩
    exact (div_le_iff₀ (pow_pos hs k)).mpr (hΛ' x s hs)

end ParabolicRectifiability.BetaP
