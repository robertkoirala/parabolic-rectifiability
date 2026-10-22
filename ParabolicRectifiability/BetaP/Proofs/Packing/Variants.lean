import ParabolicRectifiability.BetaP.Proofs.Packing.VariantsLemmas
import ParabolicRectifiability.BetaP.Proofs.Support.Interfaces
import ParabolicRectifiability.BetaP.Proofs.Packing.HolderReduction
import ParabolicRectifiability.Measure.Neck.Packing

/-! # Variants of active-radius packing

`c2_activeRadiusPacking_variants` proves the statement of `activeRadiusPacking_variants`: the
unit-parent, exceptional and unit-parent exceptional packing bounds follow from the all-scale
bound with a single constant.

Proof (with the simplification described for `c2_CellPartitionStatement`), for fixed `n`,
`p ≥ 2` and the all-scale bound `ActiveRadiusPackingBound n p C`:
* **unit parent** (`c2_unitParent_of_main`): if `b ≤ 0` there is no index and `σ = 0`.
  Otherwise every packing ball of `P(q,1)` has `r_i ≤ 1` (`radius_le_of_ball_subset`); the
  centres split into `M(n)` cells of centre distance `< 1` (`c2_cellPartition`); each cell is a
  weighted packing of the same parent `P(q,1)` (`c2_subfamily`) whose all-scale tails are at most
  twice its endpoint-two tails (`c2_cellTail`), hence at most `2B` by monotonicity of `B_p` in
  the source (`cpk2_betaPow_mono_measure`). The all-scale bound with `R = 1` gives each cell mass
  `≤ C (b + (2B)^{p/2}) ≤ C 2^{p/2} (b + B^{p/2})`; the cell masses sum to `σ(X)`
  (`c2_subfamily`, `Finset.sum_fiberwise`), so `σ(X) ≤ (M+1) 2^{p/2} C (b + B^{p/2})`.
* **exceptional** (`c2_exceptional_of_main`, `c2_unitParentExceptional_of_unitParent`): the
  complementary subfamily of `E` is a weighted packing of the same parent (`c2_subfamily`) whose
  tails are below those of `σ`; its bound plus the exact weight `Σ_{i ∈ E} b_i r_i^k ≤ Γ` bounds
  `σ(X)` (coefficient one on `Γ`).
* **one constant**: `C' = (M+1) 2^{p/2} C ≥ C`; the all-scale bound is monotone in its constant
  (`c2_main_mono`).

No packing, content or density property of the family is assumed beyond the hypotheses of
the three variant bounds. `1 ≤ n` is not used (binder `_hn`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## Auxiliary lemmas -/

/-- A weighted packing with weight bound `b ≤ 0` has no index, so its atomic source is zero. -/
theorem c2_atomicSource_eq_zero_of_nonpos {n N : ℕ} (k : ℕ) {q : Space n} {R : ℝ}
    {z : Fin N → Space n} {r w : Fin N → ℝ} {b : ℝ} (hpack : IsWeightedPacking q R z r w b)
    (hb : b ≤ 0) : atomicSource k z r w = 0 := by
  have hnone : ∀ i : Fin N, False := fun i =>
    absurd ((hpack.weight_pos i).trans_le (hpack.weight_le i)) (not_lt.mpr hb)
  unfold atomicSource
  exact Finset.sum_eq_zero fun i _ => (hnone i).elim

/-- An index of the subfamily of `Eᶜ` lies outside `E`. -/
theorem c2_sub_compl_not_mem {N : ℕ} (E : Finset (Fin N)) (j : Fin Eᶜ.card) :
    (Eᶜ.equivFin.symm j).1 ∉ E :=
  Finset.mem_compl.mp (Eᶜ.equivFin.symm j).2

/-- Tails of a subfamily's source are below those of the full source over every scale set and
at every centre (monotonicity of `B_p` in the source, `cpk2_betaPow_mono_measure`). -/
theorem c2_sub_tail_le {n N : ℕ} (k : ℕ) (T : FamilyKind) {p : ℝ} (hp : 0 < p)
    (z : Fin N → Space n) (r w : Fin N → ℝ) (I : Finset (Fin N)) (A : Set ℝ) (x : Space n) :
    (∫⁻ s in A, betaPow (atomicSource k (c2_sub z I) (c2_sub r I) (c2_sub w I)) k T p x s ^
        (2 / p) ∂scaleMeasure) ≤
      ∫⁻ s in A, betaPow (atomicSource k z r w) k T p x s ^ (2 / p) ∂scaleMeasure :=
  lintegral_mono fun s => ENNReal.rpow_le_rpow
    (cpk2_betaPow_mono_measure (c2_subfamily k z r w I).1 k T p x s)
    (div_nonneg zero_le_two hp.le)

/-- Deleting an index set `E` of total weight `≤ Γ`: if the complementary subfamily has mass
`≤ X` with `X ≥ 0`, the family has mass `≤ X + Γ`. -/
theorem c2_mass_le_of_compl {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ)
    (hr : ∀ i, 0 < r i) (hw : ∀ i, 0 < w i) (E : Finset (Fin N)) {Γ X : ℝ} (hX : 0 ≤ X)
    (hE : (∑ i ∈ E, w i * r i ^ k) ≤ Γ)
    (hsub : atomicSource k (c2_sub z Eᶜ) (c2_sub r Eᶜ) (c2_sub w Eᶜ) univ ≤ ENNReal.ofReal X) :
    atomicSource k z r w univ ≤ ENNReal.ofReal (X + Γ) := by
  obtain ⟨-, hmassI, hmass, -⟩ := c2_subfamily k z r w Eᶜ
  have hnn : ∀ i ∈ E, 0 ≤ w i * r i ^ k := fun i _ =>
    mul_nonneg (hw i).le (pow_nonneg (hr i).le k)
  have hΓ : 0 ≤ Γ := (Finset.sum_nonneg hnn).trans hE
  rw [hmass, ← Finset.sum_compl_add_sum E (fun i => ENNReal.ofReal (w i * r i ^ k)), ← hmassI,
    ENNReal.ofReal_add hX hΓ]
  refine add_le_add hsub ?_
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  exact ENNReal.ofReal_le_ofReal hE

/-- The all-scale bound is monotone in its constant. -/
theorem c2_main_mono {n : ℕ} {p C C' : ℝ} (hCC' : C ≤ C')
    (hmain : ActiveRadiusPackingBound n p C) : ActiveRadiusPackingBound n p C' := by
  intro k hk hkn T hT q R hR N z r w b B hpack hB htail
  rcases le_or_gt b 0 with hb | hb
  · rw [c2_atomicSource_eq_zero_of_nonpos k hpack hb]
    simp
  refine (hmain k hk hkn T hT q R hR N z r w b B hpack hB htail).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCC' (add_nonneg hb.le (Real.rpow_nonneg hB _)))
    (pow_nonneg hR.le k)

/-! ## The unit-parent bound -/

/-- The unit-parent constant `(M+1) 2^{p/2} C`. -/
def c2_unitParentConstant (M : ℕ) (p C : ℝ) : ℝ := ((M : ℝ) + 1) * (2 : ℝ) ^ (p / 2) * C

theorem c2_one_le_unitParentFactor (M : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    1 ≤ ((M : ℝ) + 1) * (2 : ℝ) ^ (p / 2) :=
  one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)])
    (Real.one_le_rpow one_le_two (div_nonneg hp zero_le_two))

/-- **One cell**: a subfamily of a weighted packing of
`P(q,1)` whose centres are pairwise at distance `< 1` has mass `≤ C (b + (2B)^{p/2})`, by the
all-scale bound with parent `P(q,1)` and the cell tail (`c2_cellTail`) followed by monotonicity of
`B_p` in the source and the endpoint-two hypothesis. -/
theorem c2_cell_bound {n : ℕ} {p C : ℝ} (hmain : ActiveRadiusPackingBound n p C) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n + 2) {T : FamilyKind} (hT : Nonempty (Models n k T))
    {q : Space n} {N : ℕ} {z : Fin N → Space n} {r w : Fin N → ℝ} {b B : ℝ}
    (hpack : IsWeightedPacking q 1 z r w b) (hB : 0 ≤ B)
    (htail : ∀ i, (∫⁻ s in Ioo (r i) 2,
        betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure) ≤
      ENNReal.ofReal B)
    (hp0 : 0 < p) (hr1 : ∀ i, r i ≤ 1) (I : Finset (Fin N))
    (hI : ∀ i ∈ I, ∀ j ∈ I, dist (z i) (z j) < 1) :
    atomicSource k (c2_sub z I) (c2_sub r I) (c2_sub w I) univ ≤
      ENNReal.ofReal (C * (b + (2 * B) ^ (p / 2)) * 1 ^ k) := by
  obtain ⟨-, -, -, hpk⟩ := c2_subfamily k z r w I
  have hpkI := hpk q 1 b hpack
  refine hmain k hk hkn T hT q 1 one_pos I.card (c2_sub z I) (c2_sub r I) (c2_sub w I) b
    (2 * B) hpkI (mul_nonneg zero_le_two hB) fun j => ?_
  have hclose : ∀ j' j'', dist (c2_sub z I j') (c2_sub z I j'') < 1 := fun j' j'' =>
    hI _ (I.equivFin.symm j').2 _ (I.equivFin.symm j'').2
  calc (∫⁻ s in Ioi (c2_sub r I j), betaPow (atomicSource k (c2_sub z I) (c2_sub r I)
        (c2_sub w I)) k T p (c2_sub z I j) s ^ (2 / p) ∂scaleMeasure)
      ≤ 2 * ∫⁻ s in Ioo (c2_sub r I j) 2, betaPow (atomicSource k (c2_sub z I) (c2_sub r I)
        (c2_sub w I)) k T p (c2_sub z I j) s ^ (2 / p) ∂scaleMeasure :=
        c2_cellTail k T p hp0 (c2_sub z I) (c2_sub r I) (c2_sub w I) hpkI.radius_pos
          hpkI.weight_pos hclose j (hr1 (I.equivFin.symm j).1)
    _ ≤ 2 * ∫⁻ s in Ioo (c2_sub r I j) 2,
          betaPow (atomicSource k z r w) k T p (c2_sub z I j) s ^ (2 / p) ∂scaleMeasure :=
        mul_le_mul' le_rfl (c2_sub_tail_le k T hp0 z r w I _ _)
    _ ≤ 2 * ENNReal.ofReal B := mul_le_mul' le_rfl (htail (I.equivFin.symm j).1)
    _ = ENNReal.ofReal (2 * B) := by
        rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]

/-- **Unit parent with endpoint two** from the all-scale bound. -/
theorem c2_unitParent_of_main {n : ℕ} {p C : ℝ} (hp : 2 ≤ p) (hC : 0 < C)
    (hmain : ActiveRadiusPackingBound n p C) (M : ℕ) (hM : c2_CellLabelling n M) :
    ActiveRadiusPackingUnitParentBound n p (c2_unitParentConstant M p C) := by
  intro k hk hkn T hT q N z r w b B hpack hB htail
  rcases le_or_gt b 0 with hb | hb
  · rw [c2_atomicSource_eq_zero_of_nonpos k hpack hb]
    simp
  have hp0 : 0 < p := by linarith
  have hz : ∀ i, z i ∈ Metric.ball q 1 := fun i =>
    hpack.ball_subset i (Metric.mem_ball_self (hpack.radius_pos i))
  have hr1 : ∀ i, r i ≤ 1 := fun i =>
    _root_.ParabolicRectifiability.radius_le_of_ball_subset (hpack.radius_pos i)
      (hpack.ball_subset i)
  obtain ⟨κ, hκ⟩ := hM q z hz
  -- the cells `{i : κ i = m}`
  have hcell : ∀ m : Fin M,
      atomicSource k (c2_sub z (Finset.univ.filter (fun i => κ i = m)))
          (c2_sub r (Finset.univ.filter (fun i => κ i = m)))
          (c2_sub w (Finset.univ.filter (fun i => κ i = m))) univ ≤
        ENNReal.ofReal (C * (b + (2 * B) ^ (p / 2)) * 1 ^ k) := fun m =>
    c2_cell_bound hmain hk hkn hT hpack hB htail hp0 hr1 _ fun i hi j hj =>
      hκ i j ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  -- the cell masses sum to the total mass
  obtain ⟨-, -, hmass, -⟩ := c2_subfamily k z r w Finset.univ
  have hsum : atomicSource k z r w univ =
      ∑ m : Fin M, atomicSource k (c2_sub z (Finset.univ.filter (fun i => κ i = m)))
          (c2_sub r (Finset.univ.filter (fun i => κ i = m)))
          (c2_sub w (Finset.univ.filter (fun i => κ i = m))) univ := by
    rw [hmass, ← Finset.sum_fiberwise Finset.univ κ (fun i => ENNReal.ofReal (w i * r i ^ k))]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact ((c2_subfamily k z r w (Finset.univ.filter (fun i => κ i = m))).2.1).symm
  -- the constant
  have hreal : (M : ℝ) * (C * (b + (2 * B) ^ (p / 2)) * 1 ^ k) ≤
      c2_unitParentConstant M p C * (b + B ^ (p / 2)) := by
    have h2 : (1 : ℝ) ≤ 2 ^ (p / 2) := Real.one_le_rpow one_le_two (by linarith)
    have hstep : b + (2 * B) ^ (p / 2) ≤ 2 ^ (p / 2) * (b + B ^ (p / 2)) := by
      rw [Real.mul_rpow zero_le_two hB, mul_add]
      have hb2 : b ≤ 2 ^ (p / 2) * b := le_mul_of_one_le_left hb.le h2
      linarith
    have hX : 0 ≤ b + (2 * B) ^ (p / 2) :=
      add_nonneg hb.le (Real.rpow_nonneg (mul_nonneg zero_le_two hB) _)
    rw [one_pow, mul_one, c2_unitParentConstant]
    calc (M : ℝ) * (C * (b + (2 * B) ^ (p / 2)))
        ≤ ((M : ℝ) + 1) * (C * (2 ^ (p / 2) * (b + B ^ (p / 2)))) :=
          mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hstep hC.le)
            (mul_nonneg hC.le hX) (by positivity)
      _ = ((M : ℝ) + 1) * 2 ^ (p / 2) * C * (b + B ^ (p / 2)) := by ring
  calc atomicSource k z r w univ
      = ∑ m : Fin M, atomicSource k (c2_sub z (Finset.univ.filter (fun i => κ i = m)))
          (c2_sub r (Finset.univ.filter (fun i => κ i = m)))
          (c2_sub w (Finset.univ.filter (fun i => κ i = m))) univ := hsum
    _ ≤ ∑ _m : Fin M, ENNReal.ofReal (C * (b + (2 * B) ^ (p / 2)) * 1 ^ k) :=
        Finset.sum_le_sum fun m _ => hcell m
    _ = ENNReal.ofReal ((M : ℝ) * (C * (b + (2 * B) ^ (p / 2)) * 1 ^ k)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg M), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (c2_unitParentConstant M p C * (b + B ^ (p / 2))) :=
        ENNReal.ofReal_le_ofReal hreal

/-! ## The exceptional bounds -/

/-- **Exceptional indices** from the all-scale bound. -/
theorem c2_exceptional_of_main {n : ℕ} {p C : ℝ} (hp : 2 ≤ p) (hC : 0 < C)
    (hmain : ActiveRadiusPackingBound n p C) : ActiveRadiusPackingExceptionalBound n p C := by
  intro k hk hkn T hT q R hR N z r w b B hpack hB E Γ hE htail
  rcases le_or_gt b 0 with hb | hb
  · rw [c2_atomicSource_eq_zero_of_nonpos k hpack hb]
    simp
  have hp0 : 0 < p := by linarith
  obtain ⟨-, -, -, hpk⟩ := c2_subfamily k z r w Eᶜ
  have hsub := hmain k hk hkn T hT q R hR Eᶜ.card (c2_sub z Eᶜ) (c2_sub r Eᶜ) (c2_sub w Eᶜ) b B
    (hpk q R b hpack) hB fun j =>
      le_trans (c2_sub_tail_le k T hp0 z r w Eᶜ _ _)
        (htail (Eᶜ.equivFin.symm j).1 (c2_sub_compl_not_mem E j))
  exact c2_mass_le_of_compl k z r w hpack.radius_pos hpack.weight_pos E
    (mul_nonneg (mul_nonneg hC.le (add_nonneg hb.le (Real.rpow_nonneg hB _))) (pow_nonneg hR.le k))
    hE hsub

/-- **Exceptional indices for the unit-parent form.** -/
theorem c2_unitParentExceptional_of_unitParent {n : ℕ} {p C : ℝ} (hp : 2 ≤ p) (hC : 0 < C)
    (hU : ActiveRadiusPackingUnitParentBound n p C) :
    ActiveRadiusPackingUnitParentExceptionalBound n p C := by
  intro k hk hkn T hT q N z r w b B hpack hB E Γ hE htail
  rcases le_or_gt b 0 with hb | hb
  · rw [c2_atomicSource_eq_zero_of_nonpos k hpack hb]
    simp
  have hp0 : 0 < p := by linarith
  obtain ⟨-, -, -, hpk⟩ := c2_subfamily k z r w Eᶜ
  have hsub := hU k hk hkn T hT q Eᶜ.card (c2_sub z Eᶜ) (c2_sub r Eᶜ) (c2_sub w Eᶜ) b B
    (hpk q 1 b hpack) hB fun j =>
      le_trans (c2_sub_tail_le k T hp0 z r w Eᶜ _ _)
        (htail (Eᶜ.equivFin.symm j).1 (c2_sub_compl_not_mem E j))
  exact c2_mass_le_of_compl k z r w hpack.radius_pos hpack.weight_pos E
    (mul_nonneg hC.le (add_nonneg hb.le (Real.rpow_nonneg hB _))) hE hsub

/-! ## The three variants -/

/-- **Variants of active-radius packing**: the statement of `activeRadiusPacking_variants`. -/
theorem c2_activeRadiusPacking_variants (n : ℕ) (_hn : 1 ≤ n) (p : ℝ) (hp : 2 ≤ p) (C : ℝ)
    (hC : 0 < C) (hmain : ActiveRadiusPackingBound n p C) :
    ∃ C' : ℝ, 0 < C' ∧ ActiveRadiusPackingUnitParentBound n p C' ∧
      ActiveRadiusPackingExceptionalBound n p C' ∧
      ActiveRadiusPackingUnitParentExceptionalBound n p C' := by
  obtain ⟨M, hM⟩ := c2_cellPartition n
  have hfac := c2_one_le_unitParentFactor M (show (0 : ℝ) ≤ p by linarith)
  have hCle : C ≤ c2_unitParentConstant M p C := le_mul_of_one_le_left hC.le hfac
  have hpos : 0 < c2_unitParentConstant M p C := hC.trans_le hCle
  have hU := c2_unitParent_of_main hp hC hmain M hM
  exact ⟨_, hpos, hU, c2_exceptional_of_main hp hpos (c2_main_mono hCle hmain),
    c2_unitParentExceptional_of_unitParent hp hpos hU⟩

end ParabolicRectifiability.BetaP
