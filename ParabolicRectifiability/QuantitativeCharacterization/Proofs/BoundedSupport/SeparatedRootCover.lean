import ParabolicRectifiability.QuantitativeCharacterization.Statements.BoundedSupportComponents
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.NetExtension

/-! # The separated root cover

Proof of `dp2_separated_root_cover_proof : dp2_SeparatedRootCoverStatement`.

Proof idea: take an `r/2`-net `Z` of the closed support `E = supp μ` from
`Forward.PartitionEnergy.d1a_netExtension_proof` (`s = r/2`, `Z₀ = ∅`).
Every finite `P ⊆ Z` has pairwise disjoint balls `P(z, r/4)`, each of mass `≥ A⁻¹ (r/4)^k`
(lower growth, `r/4 ≤ D_E`), inside `P(z₀, 2 D_E)` of mass `≤ A (2 D_E)^k` (upper growth), so
`#P ≤ A² (8 D_E / r)^k` (`dp2sep_card_le`). Hence `Z` is finite (`dp2sep_finite`); enumerate it
with `Finset.equivFin`. Each point of `E` lies within `r/2 < r` of the net.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- The real counting bound: `c A⁻¹ ρ^k ≤ A (2D)^k` with `ρ > 0` gives `c ≤ A² (2D/ρ)^k`. -/
theorem dp2sep_real_bound {A c ρ D : ℝ} (k : ℕ) (hA : 0 < A) (hρ : 0 < ρ)
    (h : c * (A⁻¹ * ρ ^ k) ≤ A * (2 * D) ^ k) :
    c ≤ A ^ 2 * (2 * D / ρ) ^ k := by
  have hρk : 0 < ρ ^ k := pow_pos hρ k
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ hρk]
  calc c * ρ ^ k = A * (c * (A⁻¹ * ρ ^ k)) := by
        rw [mul_left_comm A c, ← mul_assoc A, mul_inv_cancel₀ hA.ne', one_mul]
    _ ≤ A * (A * (2 * D) ^ k) := by gcongr
    _ = A ^ 2 * (2 * D) ^ k := by ring

/-- **Packing count.** A finite `r/2`-separated family of support points has at most
`A² (8 D_E / r)^k` members. -/
theorem dp2sep_card_le {n k : ℕ} {A : ℝ} {μ : Measure (Space n)} (hA : 0 < A)
    (hbdd : Bornology.IsBounded μ.support)
    (hup : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k))
    (hlow : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → r ≤ Metric.diam μ.support →
      ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball z r))
    {r : ℝ} (hr : 0 < r) (hrD : r ≤ Metric.diam μ.support) {z₀ : Space n} (hz₀ : z₀ ∈ μ.support)
    (P : Finset (Space n)) (hPE : (P : Set (Space n)) ⊆ μ.support)
    (hsep : ∀ z ∈ P, ∀ z' ∈ P, z ≠ z' → r / 2 ≤ dist z z') :
    (P.card : ℝ) ≤ A ^ 2 * (8 * Metric.diam μ.support / r) ^ k := by
  set D := Metric.diam μ.support with hD
  have hD0 : 0 < D := hr.trans_le hrD
  have hr4 : 0 < r / 4 := by positivity
  have hdisj : (P : Set (Space n)).PairwiseDisjoint (fun z => Metric.ball z (r / 4)) := by
    intro z hz z' hz' hne
    exact Metric.ball_disjoint_ball (by linarith [hsep z hz z' hz' hne])
  have hsub : (⋃ z ∈ P, Metric.ball z (r / 4)) ⊆ Metric.ball z₀ (2 * D) := by
    refine iUnion₂_subset fun z hz y hy => ?_
    rw [Metric.mem_ball] at hy ⊢
    have h1 : dist z z₀ ≤ D := Metric.dist_le_diam_of_mem hbdd (hPE hz) hz₀
    linarith [dist_triangle y z z₀]
  have hmass : ((P.card : ℝ≥0∞)) * ENNReal.ofReal (A⁻¹ * (r / 4) ^ k) ≤
      ENNReal.ofReal (A * (2 * D) ^ k) := by
    calc ((P.card : ℝ≥0∞)) * ENNReal.ofReal (A⁻¹ * (r / 4) ^ k)
        = ∑ _z ∈ P, ENNReal.ofReal (A⁻¹ * (r / 4) ^ k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ P, μ (Metric.ball z (r / 4)) :=
          Finset.sum_le_sum fun z hz => hlow z (hPE hz) (r / 4) hr4 (by linarith)
      _ = μ (⋃ z ∈ P, Metric.ball z (r / 4)) :=
          (measure_biUnion_finset hdisj fun z _ => Metric.isOpen_ball.measurableSet).symm
      _ ≤ μ (Metric.ball z₀ (2 * D)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (A * (2 * D) ^ k) := hup z₀ hz₀ (2 * D) (by positivity)
  have hreal : (P.card : ℝ) * (A⁻¹ * (r / 4) ^ k) ≤ A * (2 * D) ^ k := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hmass
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmass
  have e : 8 * D / r = 2 * D / (r / 4) := by rw [div_div_eq_mul_div]; ring
  rw [e]
  exact dp2sep_real_bound k hA hr4 hreal

/-- **Finiteness.** An `r/2`-separated set of support points is finite. -/
theorem dp2sep_finite {n k : ℕ} {A : ℝ} {μ : Measure (Space n)} (hA : 0 < A)
    (hbdd : Bornology.IsBounded μ.support)
    (hup : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k))
    (hlow : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → r ≤ Metric.diam μ.support →
      ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball z r))
    {r : ℝ} (hr : 0 < r) (hrD : r ≤ Metric.diam μ.support) {z₀ : Space n} (hz₀ : z₀ ∈ μ.support)
    {Z : Set (Space n)} (hZE : Z ⊆ μ.support)
    (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → r / 2 ≤ dist z z') : Z.Finite := by
  by_contra hinf
  obtain ⟨P, hPZ, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf
    (⌈A ^ 2 * (8 * Metric.diam μ.support / r) ^ k⌉₊ + 1)
  have h := dp2sep_card_le hA hbdd hup hlow hr hrD hz₀ P (hPZ.trans hZE)
    (fun z hz z' hz' hne => hsep z (hPZ hz) z' (hPZ hz') hne)
  rw [hcard, Nat.cast_add, Nat.cast_one] at h
  linarith [Nat.le_ceil (A ^ 2 * (8 * Metric.diam μ.support / r) ^ k)]

/-- **Proof of the statement `dp2_separated_root_cover`** (type
`dp2_SeparatedRootCoverStatement`). -/
theorem dp2_separated_root_cover_proof : dp2_SeparatedRootCoverStatement := by
  intro n k A μ hA hbdd hup hlow r hr hrD
  obtain ⟨z₀, hz₀⟩ : μ.support.Nonempty := by
    rcases μ.support.eq_empty_or_nonempty with h | h
    · rw [h, Metric.diam_empty] at hrD
      linarith
    · exact h
  obtain ⟨Z, -, hZE, -, hsep, hcov⟩ :=
    Forward.PartitionEnergy.d1a_netExtension_proof n μ.support Measure.isClosed_support (r / 2)
      (by positivity) ∅ (empty_subset _) (fun z hz => absurd hz (notMem_empty z))
  have hZf := dp2sep_finite hA hbdd hup hlow hr hrD hz₀ hZE hsep
  set P := hZf.toFinset with hP
  have hPE : (P : Set (Space n)) ⊆ μ.support := by
    intro z hz
    exact hZE ((Set.Finite.mem_toFinset hZf).mp hz)
  have hPsep : ∀ z ∈ P, ∀ z' ∈ P, z ≠ z' → r / 2 ≤ dist z z' := fun z hz z' hz' hne =>
    hsep z ((Set.Finite.mem_toFinset hZf).mp hz) z' ((Set.Finite.mem_toFinset hZf).mp hz') hne
  refine ⟨P.card, fun j => (P.equivFin.symm j : Space n), fun j => hPE (P.equivFin.symm j).2,
    ?_, dp2sep_card_le hA hbdd hup hlow hr hrD hz₀ P hPE hPsep⟩
  intro x hx
  obtain ⟨z, hzZ, hxz⟩ := hcov x hx
  have hzP : z ∈ P := (Set.Finite.mem_toFinset hZf).mpr hzZ
  refine mem_iUnion.mpr ⟨P.equivFin ⟨z, hzP⟩, ?_⟩
  simp only [Equiv.symm_apply_apply, Metric.mem_ball]
  linarith

end ParabolicRectifiability.QuantitativeCharacterization
