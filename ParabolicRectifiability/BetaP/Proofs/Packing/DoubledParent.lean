import ParabolicRectifiability.BetaP.Proofs.Packing.PackingStatements

/-! # The doubled parent (`cpk_doubledParent`)

Proves the named statement `CpkDoubledParentStatement`, with the quadratic discrete packing bound
as the hypothesis `DiscretePackingBound n C₀`.

Proof: fix a centre `x` and a scale `s > 0`; enumerate the
retained index set `I = {i : r_i ≤ s, d(z_i, x) < s}` injectively by `I.equivFin.symm`; its
packing balls lie in the open doubled parent `P(x, 2s)` (triangle inequality); apply
`DiscretePackingBound n C₀` to the retained subfamily with parent `P(x, 2s)`, its tail hypothesis
being `CpkSubfamilyTailBound` at the enumeration; reindex the sum and use
`(2s)^k = 2^k s^k`. An empty retained family is covered by the same argument (`Fin 0`).

Only `ParabolicRectifiability.truncatedAtomicSource` occurs (through the two
hypotheses); this file never names either testing source.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- Reindexing a finset sum along its enumeration `I.equivFin`. -/
theorem cpk3_sum_finset_eq_sum_fin {N : ℕ} (I : Finset (Fin N)) (f : Fin N → ℝ) :
    ∑ i ∈ I, f i = ∑ m : Fin I.card, f (I.equivFin.symm m : Fin N) := by
  rw [← Finset.sum_coe_sort I]
  exact Fintype.sum_equiv I.equivFin _ _ (fun x => by rw [Equiv.symm_apply_apply])

/-- A retained ball lies in the open doubled parent: `r ≤ s` and `d(z, x) < s` give
`P(z, r) ⊆ P(x, 2s)`. -/
theorem cpk3_ball_subset_doubled {n : ℕ} {x z : Space n} {r s : ℝ} (hr : r ≤ s)
    (hz : dist z x < s) : Metric.ball z r ⊆ Metric.ball x (2 * s) := by
  intro y hy
  rw [Metric.mem_ball] at hy ⊢
  calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
    _ < r + s := add_lt_add hy hz
    _ ≤ 2 * s := by linarith

/-- The doubled-parent bound for any retained index set `I` (every index of `I` has
`r_i ≤ s` and `d(z_i, x) < s`): `Σ_{i ∈ I} w_i r_i^k ≤ 2^k C₀ (b + B') s^k`. -/
theorem cpk3_retained_sum_le {n : ℕ} {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hdisc : DiscretePackingBound n C₀) {k : ℕ} (hk : 1 ≤ k) (hkn : k < n + 2)
    {T : FamilyKind} (hT : Nonempty (Models n k T)) {N : ℕ} (z : Fin N → Space n)
    (r w : Fin N → ℝ) {b B' : ℝ} (hr : ∀ i, 0 < r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j)))
    (hw : ∀ i, 0 < w i) (hwb : ∀ i, w i ≤ b) (hb : 0 < b) (hB' : 0 ≤ B')
    (htail : CpkSubfamilyTailBound k T z r w B') (x : Space n) {s : ℝ} (hs : 0 < s)
    (I : Finset (Fin N)) (hI : ∀ i ∈ I, r i ≤ s ∧ dist (z i) x < s) :
    ∑ i ∈ I, w i * r i ^ k ≤ 2 ^ k * C₀ * (b + B') * s ^ k := by
  let e : Fin I.card → Fin N := fun m => (I.equivFin.symm m : Fin N)
  have he : Function.Injective e := fun a c hac =>
    I.equivFin.symm.injective (Subtype.ext hac)
  have hmem : ∀ m, r (e m) ≤ s ∧ dist (z (e m)) x < s := fun m =>
    hI _ (I.equivFin.symm m).2
  have key := hdisc k T hk hkn hT x (2 * s) b B' I.card (fun m => z (e m))
    (fun m => r (e m)) (fun m => w (e m)) (by linarith) hb hB'
    (fun m => ⟨hr (e m), cpk3_ball_subset_doubled (hmem m).1 (hmem m).2⟩)
    (fun a c hac => hdisj (e a) (e c) (fun h => hac (he h)))
    (fun m => ⟨hw (e m), hwb (e m)⟩)
    (fun j => htail I.card e he j)
  have hsum : ∑ i ∈ I, w i * r i ^ k = ∑ m : Fin I.card, w (e m) * r (e m) ^ k :=
    cpk3_sum_finset_eq_sum_fin I (fun i => w i * r i ^ k)
  have hnn : ∀ m, 0 ≤ w (e m) * r (e m) ^ k := fun m =>
    mul_nonneg (hw (e m)).le (pow_nonneg (hr (e m)).le k)
  have hrhs : 0 ≤ C₀ * (b + B') * (2 * s) ^ k :=
    mul_nonneg (mul_nonneg hC₀.le (by linarith)) (pow_nonneg (by linarith) k)
  have h2 : ENNReal.ofReal (∑ m : Fin I.card, w (e m) * r (e m) ^ k) ≤
      ENNReal.ofReal (C₀ * (b + B') * (2 * s) ^ k) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => hnn m)]
    exact key
  rw [hsum]
  calc ∑ m : Fin I.card, w (e m) * r (e m) ^ k ≤ C₀ * (b + B') * (2 * s) ^ k :=
        (ENNReal.ofReal_le_ofReal_iff hrhs).mp h2
    _ = 2 ^ k * C₀ * (b + B') * s ^ k := by rw [mul_pow]; ring

/-- **Doubled parent**: proof of the named statement `CpkDoubledParentStatement`. -/
theorem cpk_doubledParent_proof : CpkDoubledParentStatement := by
  intro n C₀ hC₀ hdisc k hk hkn T hT N z r w b B' hr hdisj hw hwb hb hB' htail x s hs
  unfold cpkActiveMass
  exact cpk3_retained_sum_le hC₀ hdisc hk hkn hT z r w hr hdisj hw hwb hb hB' htail x hs _
    (fun i hi => (Finset.mem_filter.mp hi).2)

end ParabolicRectifiability.BetaP
