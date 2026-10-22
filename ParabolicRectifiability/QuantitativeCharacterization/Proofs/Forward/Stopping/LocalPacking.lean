import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Stopping

/-! # Same-family local packing with recentring

Proof of `d1b_localPacking_proof`, in implication form
`PartitionTreeStatement → RootContentStatement → RootPackingStatement → LocalPackingStatement`.
The latter two statements enter as hypotheses.

Route, for a test `P(w,s)`, `s > 0`, and the one family of roots of `F`:
* **`R ≤ s`**: drop the eligibility condition and apply root packing; `80^k R^k ≤ 192^k s^k`.
* **`s < R`**, part (a):
  - *generation choice* (`d1blocpack_generation`): some `j ≥ 0` has `s/4 ≤ ℓ_j < 10 s/4`
    (the largest generation with `s/4 ≤ ℓ_j`, found as the predecessor of the first generation
    with `ℓ_m < s/4`; `m ≠ 0` because `ℓ_0 = R > s/4`);
  - *ancestor grouping* (`d1blocpack_ancestor_mem_family`): an eligible root `S` has
    `ℓ_S ≤ s/4 ≤ ℓ_j`, hence level `≥ j` (`d1blocpack_le_of_scale_le`), and its level-`j`
    ancestor `T_S` (`d1blocpack_exists_ancestor`, a forest cell by `isBelow_of_common` with the
    top of `S`) is unique (`d1blocpack_ancestor_unique`); distinct level-`j` cells are disjoint
    (`d1blocpack_disjoint_of_ne`, `d1blocpack_family_pairwise_disjoint`);
  - *containment* (`d1blocpack_cell_subset_ball_aux`, `d1blocpack_cell_subset_ball`): for any
    eligible `S₀`, `T_S ⊆ P(z_{S₀}, 4 ℓ_j + 2 s) ⊆ P(z_{S₀}, 12 s)`.
  Part (b):
  - *mass estimate*: the grouping family (`d1blocpack_family`: level-`j` forest cells inside
    `P(z_{S₀}, 12 s)`) is disjoint and measurable, so its total mass is at most
    `μ(P(z_{S₀}, 12 s))` (`d1blocpack_tsum_measure_le`); recentring at the support point
    `z_{S₀} ∈ supp μ ∩ P(a, 5R)` with `12 s ≤ 12 R ≤ ρ`, `LocalADR` gives `≤ A (12 s)^k`
    (`d1blocpack_recentre`), the centre and the radius being checked separately;
  - *assembly*: bound each eligible term by the sum over the family of the terms below its
    cells, exchange the sums, apply `RootContentStatement` at each family cell and collect the
    constant `16^k · 12^k = 192^k`. With no eligible root the sum is `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

section LocalPacking

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}

/-! ## Scales and the generation choice -/

/-- The coherent scale `ℓ_j = ℓ₀ / 10^j`. -/
theorem d1blocpack_scale_eq (P : DirectPartition E ℓ₀) (j : ℕ) : P.scale j = ℓ₀ / 10 ^ j :=
  rfl

/-- The coherent scales are strictly decreasing. -/
theorem d1blocpack_scale_lt_of_lt (P : DirectPartition E ℓ₀) {i j : ℕ} (hij : i < j) :
    P.scale j < P.scale i := by
  rw [d1blocpack_scale_eq, d1blocpack_scale_eq]
  exact div_lt_div_of_pos_left P.scale_pos (pow_pos (by norm_num) i)
    (pow_lt_pow_right₀ (by norm_num) hij)

/-- A cell scale at most `ℓ_j` belongs to a generation at least `j`. -/
theorem d1blocpack_le_of_scale_le (P : DirectPartition E ℓ₀) {i j : ℕ}
    (h : P.scale i ≤ P.scale j) : j ≤ i :=
  not_lt.mp fun hij => absurd h (not_le.mpr (d1blocpack_scale_lt_of_lt P hij))

/-- **Generation choice** (with `D₁ = 4`, `h = 1/10`): for `0 < s < ℓ₀` some
generation `j ≥ 0` has `s/4 ≤ ℓ_j < 10 s / 4` (the largest generation with `s/4 ≤ ℓ_j`). -/
theorem d1blocpack_generation (P : DirectPartition E ℓ₀) {s : ℝ} (hs : 0 < s) (hsl : s < ℓ₀) :
    ∃ j : ℕ, s / 4 ≤ P.scale j ∧ P.scale j < 10 * s / 4 := by
  have hex : ∃ m : ℕ, P.scale m < s / 4 := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (4 * ℓ₀ / s) (by norm_num : (1 : ℝ) < 10)
    refine ⟨m, ?_⟩
    rw [d1blocpack_scale_eq, div_lt_iff₀ (pow_pos (by norm_num) m)]
    rw [div_lt_iff₀ hs] at hm
    have hrw : s / 4 * 10 ^ m = 10 ^ m * s / 4 := by ring
    rw [hrw]
    linarith
  classical
  obtain ⟨m, hm, hmin⟩ : ∃ m : ℕ, P.scale m < s / 4 ∧ ∀ i < m, ¬ P.scale i < s / 4 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  rcases m with _ | j
  · rw [d1blocpack_scale_eq, pow_zero, div_one] at hm
    linarith
  · refine ⟨j, not_lt.mp (hmin j (Nat.lt_succ_self j)), ?_⟩
    have h10 : P.scale (j + 1) = P.scale j / 10 := by
      rw [d1blocpack_scale_eq, d1blocpack_scale_eq, pow_succ, div_div]
    rw [h10] at hm
    linarith

/-! ## Ancestors, disjointness and containment -/

/-- The level-`j` ancestor of a forest cell `S` with `j ≤ S.1` exists and is a forest cell
(`exists_ancestor`; `isBelow_of_common` with the top cell of `S`). -/
theorem d1blocpack_exists_ancestor {P : DirectPartition E ℓ₀} (hP : PartitionTree P)
    {a : Space n} {R : ℝ} {S : ℕ × Space n} (hS : P.InForest a R S) {j : ℕ} (hj : j ≤ S.1) :
    ∃ T : ℕ × Space n, P.IsCell T ∧ T.1 = j ∧ P.IsBelow S T ∧ P.InForest a R T := by
  obtain ⟨z₀, hz₀, hmeet, hS0⟩ := hS
  obtain ⟨T, hTc, hTj, hST⟩ := hP.exists_ancestor S hS0.1 j hj
  exact ⟨T, hTc, hTj, hST, z₀, hz₀, hmeet,
    hP.isBelow_of_common S (0, z₀) T hz₀ hTc hS0 hST (Nat.zero_le _)⟩

/-- Two ancestors of one cell at the same level coincide. -/
theorem d1blocpack_ancestor_unique {P : DirectPartition E ℓ₀} (hP : PartitionTree P)
    {S T T' : ℕ × Space n} (hT : P.IsCell T) (hT' : P.IsCell T') (hST : P.IsBelow S T)
    (hST' : P.IsBelow S T') (hlev : T.1 = T'.1) : T = T' := by
  have h : P.IsBelow T' T := hP.isBelow_of_common S T T' hT hT' hST hST' hlev.le
  exact (hP.eq_of_isBelow T' T hT h hlev.symm).symm

/-- Distinct cells of one level are disjoint (`cell_disjoint`). -/
theorem d1blocpack_disjoint_of_ne (P : DirectPartition E ℓ₀) {T T' : ℕ × Space n}
    (hT : P.IsCell T) (hT' : P.IsCell T') (hlev : T.1 = T'.1) (hne : T ≠ T') :
    Disjoint (P.cellOf T) (P.cellOf T') := by
  obtain ⟨j, z⟩ := T
  obtain ⟨j', z'⟩ := T'
  have hj : j = j' := hlev
  subst hj
  have hz : z ≠ z' := fun h => hne (by rw [h])
  exact P.cell_disjoint j z hT z' hT' hz

/-- **Containment, sharp radius**: a cell `T` above a cell `S` with
`z_S ∈ P(w,s)` lies in `P(z_{S₀}, 4 ℓ_T + 2 s)` for every `z_{S₀} ∈ P(w,s)`. -/
theorem d1blocpack_cell_subset_ball_aux {P : DirectPartition E ℓ₀} (hP : PartitionTree P)
    {w : Space n} {s : ℝ} {S S₀ T : ℕ × Space n} (hTc : P.IsCell T) (hST : P.IsBelow S T)
    (hSw : S.2 ∈ Metric.ball w s) (hS₀w : S₀.2 ∈ Metric.ball w s) :
    P.cellOf T ⊆ Metric.ball S₀.2 (4 * P.scale T.1 + 2 * s) := by
  intro y hy
  have hyT : dist y T.2 < 2 * P.scale T.1 := P.cell_subset_ball T.1 T.2 hTc hy
  have hzS : S.2 ∈ P.cellOf T := hST.2.2 (hP.center_mem_cell S hST.1)
  have hzT : dist S.2 T.2 < 2 * P.scale T.1 := P.cell_subset_ball T.1 T.2 hTc hzS
  have hSw' : dist S.2 w < s := hSw
  have hS₀w' : dist S₀.2 w < s := hS₀w
  have t1 := dist_triangle y T.2 S.2
  have t2 := dist_triangle y S.2 w
  have t3 := dist_triangle y w S₀.2
  have c1 := dist_comm T.2 S.2
  have c2 := dist_comm w S₀.2
  show dist y S₀.2 < 4 * P.scale T.1 + 2 * s
  linarith

/-- **Containment** `T_S ⊆ P(z_{S₀}, 4 ℓ_j + 2 s) ⊆ P(z_{S₀}, 12 s)` when `ℓ_j < 10 s / 4`. -/
theorem d1blocpack_cell_subset_ball {P : DirectPartition E ℓ₀} (hP : PartitionTree P)
    {w : Space n} {s : ℝ} {S S₀ T : ℕ × Space n} (hTc : P.IsCell T) (hST : P.IsBelow S T)
    (hSw : S.2 ∈ Metric.ball w s) (hS₀w : S₀.2 ∈ Metric.ball w s)
    (hTs : P.scale T.1 < 10 * s / 4) :
    P.cellOf T ⊆ Metric.ball S₀.2 (12 * s) :=
  (d1blocpack_cell_subset_ball_aux hP hTc hST hSw hS₀w).trans
    (Metric.ball_subset_ball (by linarith))

/-- The grouping family: the level-`j` forest cells of `P(a,R)` inside `P(c, r)`. -/
def d1blocpack_family (P : DirectPartition E ℓ₀) (a : Space n) (R : ℝ) (j : ℕ) (c : Space n)
    (r : ℝ) : Set (ℕ × Space n) :=
  {T | P.IsCell T ∧ T.1 = j ∧ P.InForest a R T ∧ P.cellOf T ⊆ Metric.ball c r}

/-- **Ancestor grouping**: with `s/4 ≤ ℓ_j < 10 s / 4`, every eligible root
(`z_S ∈ P(w,s)`, `4 ℓ_S ≤ s`) has its level-`j` ancestor in the grouping family at
`P(z_{S₀}, 12 s)`, for any `z_{S₀} ∈ P(w,s)`. -/
theorem d1blocpack_ancestor_mem_family {P : DirectPartition E ℓ₀} (hP : PartitionTree P)
    {a : Space n} {R : ℝ} {w : Space n} {s : ℝ} {j : ℕ} (hj1 : s / 4 ≤ P.scale j)
    (hj2 : P.scale j < 10 * s / 4) {S S₀ : ℕ × Space n} (hS : P.InForest a R S)
    (hSw : S.2 ∈ Metric.ball w s) (hSs : 4 * P.scale S.1 ≤ s)
    (hS₀w : S₀.2 ∈ Metric.ball w s) :
    ∃ T ∈ d1blocpack_family P a R j S₀.2 (12 * s), P.IsBelow S T := by
  have hjS : j ≤ S.1 := d1blocpack_le_of_scale_le P (by linarith)
  obtain ⟨T, hTc, hTj, hST, hTF⟩ := d1blocpack_exists_ancestor hP hS hjS
  refine ⟨T, ⟨hTc, hTj, hTF, ?_⟩, hST⟩
  exact d1blocpack_cell_subset_ball hP hTc hST hSw hS₀w (by rw [hTj]; exact hj2)

/-- Distinct members of the grouping family are disjoint. -/
theorem d1blocpack_family_pairwise_disjoint (P : DirectPartition E ℓ₀) (a : Space n) (R : ℝ)
    (j : ℕ) (c : Space n) (r : ℝ) :
    Pairwise (Function.onFun Disjoint fun T : d1blocpack_family P a R j c r => P.cellOf T.1) := by
  intro T T' hne
  exact d1blocpack_disjoint_of_ne P T.2.1 T'.2.1 (T.2.2.1.trans T'.2.2.1.symm)
    (fun h => hne (Subtype.ext h))

/-! ## Mass estimate and recentring (part (b)) -/

/-- **Mass of the grouping family**: disjoint measurable cells inside `P(c, r)`. -/
theorem d1blocpack_tsum_measure_le (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (a : Space n) (R : ℝ) (j : ℕ) (c : Space n) (r : ℝ) :
    (∑' T : d1blocpack_family P a R j c r, μ (P.cellOf T.1)) ≤ μ (Metric.ball c r) :=
  (tsum_meas_le_meas_iUnion_of_disjoint μ
    (As := fun T : d1blocpack_family P a R j c r => P.cellOf T.1)
    (fun T => P.measurable_cell T.1.1 T.1.2)
    (d1blocpack_family_pairwise_disjoint P a R j c r)).trans
    (measure_mono (iUnion_subset fun T => T.2.2.2.2))

/-- A forest centre is a point of `E ∩ P(a, R + 4 ℓ₀)` (`center_subset`, `inForest_subset`). -/
theorem d1blocpack_forest_center_mem {P : DirectPartition E ℓ₀} (hP : PartitionTree P)
    {a : Space n} {R : ℝ} {S : ℕ × Space n} (hS : P.InForest a R S) :
    S.2 ∈ E ∩ Metric.ball a (R + 4 * ℓ₀) := by
  have hc : P.IsCell S := by
    obtain ⟨_, _, _, h⟩ := hS
    exact h.1
  exact ⟨P.center_subset S.1 hc, hP.inForest_subset a R S hS (hP.center_mem_cell S hc)⟩

/-- **Recentring**: at a forest centre `z_{S₀} ∈ supp μ ∩ P(a, 5R)` and radius
`0 < 12 s ≤ 12 R ≤ ρ`, `LocalADR` gives `μ(P(z_{S₀}, 12 s)) ≤ A (12 s)^k`; the centre and the
radius of the test are checked separately. -/
theorem d1blocpack_recentre {μ : Measure (Space n)} {k : ℕ} {A : ℝ} {a : Space n} {R ρ : ℝ}
    {P : DirectPartition μ.support R} (hP : PartitionTree P) (hρ : 12 * R ≤ ρ)
    (hADR : LocalADR μ k A a ρ) {S₀ : ℕ × Space n} (hS₀ : P.InForest a R S₀) {s : ℝ}
    (hs : 0 < s) (hsR : s < R) :
    μ (Metric.ball S₀.2 (12 * s)) ≤ ENNReal.ofReal (A * (12 * s) ^ k) := by
  have hz := d1blocpack_forest_center_mem hP hS₀
  have hz' : S₀.2 ∈ μ.support ∩ Metric.ball a ρ :=
    ⟨hz.1, Metric.ball_subset_ball (by linarith) hz.2⟩
  exact (hADR S₀.2 hz' (12 * s) (by linarith) (by linarith)).2

/-! ## Summation and constants -/

/-- Pointwise domination by a double sum, then exchange of the sums. -/
theorem d1blocpack_tsum_le_tsum_comm {ι κ : Type*} (g : ι → ℝ≥0∞) (h : ι → κ → ℝ≥0∞)
    (hgh : ∀ i, g i ≤ ∑' t, h i t) : (∑' i, g i) ≤ ∑' t, ∑' i, h i t :=
  (ENNReal.tsum_le_tsum hgh).trans_eq ENNReal.tsum_comm

/-- A sum over `s` restricted by `p` is the sum over the subtype `s ∩ p`. -/
theorem d1blocpack_tsum_ite_le {α : Type*} (s : Set α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ≥0∞) :
    (∑' x : s, if p x.1 then f x.1 else 0) ≤ ∑' x : {x // x ∈ s ∧ p x}, f x.1 := by
  classical
  calc (∑' x : s, if p x.1 then f x.1 else 0)
      = ∑' x, s.indicator (fun x => if p x then f x else 0) x :=
        tsum_subtype s (fun x => if p x then f x else 0)
    _ ≤ ∑' x, ({x | x ∈ s ∧ p x} : Set α).indicator f x := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hs : x ∈ s <;> by_cases hp : p x <;> simp [hs, hp]
    _ = ∑' x : {x // x ∈ s ∧ p x}, f x.1 := (tsum_subtype {x | x ∈ s ∧ p x} f).symm

/-- The large-scale constant: `80^k A² K R^k ≤ 192^k A² K s^k` for `0 < R ≤ s`, `K ≥ 0`. -/
theorem d1blocpack_large_const {k : ℕ} {A K R s : ℝ} (hK : 0 ≤ K) (hR : 0 < R) (hRs : R ≤ s) :
    80 ^ k * A ^ 2 * K * R ^ k ≤ 192 ^ k * A ^ 2 * K * s ^ k := by
  have h1 : (80 : ℝ) ^ k ≤ 192 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have h2 : R ^ k ≤ s ^ k := pow_le_pow_left₀ hR.le hRs k
  have h3 : 0 ≤ A ^ 2 * K := mul_nonneg (sq_nonneg A) hK
  have h4 : (80 : ℝ) ^ k * R ^ k ≤ 192 ^ k * s ^ k :=
    mul_le_mul h1 h2 (pow_nonneg hR.le k) (pow_nonneg (by norm_num) k)
  calc 80 ^ k * A ^ 2 * K * R ^ k = (A ^ 2 * K) * (80 ^ k * R ^ k) := by ring
    _ ≤ (A ^ 2 * K) * (192 ^ k * s ^ k) := mul_le_mul_of_nonneg_left h4 h3
    _ = 192 ^ k * A ^ 2 * K * s ^ k := by ring

/-- The small-scale constant: `16^k A K · A (12 s)^k = 192^k A² K s^k`. -/
theorem d1blocpack_small_const (k : ℕ) (A K s : ℝ) :
    16 ^ k * A * K * (A * (12 * s) ^ k) = 192 ^ k * A ^ 2 * K * s ^ k := by
  have h : (192 : ℝ) ^ k = 16 ^ k * 12 ^ k := by rw [← mul_pow]; norm_num
  rw [h, mul_pow]
  ring

end LocalPacking

/-! ## The statement -/

/-- **Same-family local packing with recentring** (`LocalPackingStatement`, in
implication form). For `R ≤ s` by root packing; for
`s < R` by the generation choice, the ancestor grouping in `P(z_{S₀}, 12 s)` at an eligible root
centre, root content at each grouping cell, disjointness and `LocalADR` at `z_{S₀}`. One family
of roots; no reselection per test. -/
theorem d1b_localPacking_proof :
    PartitionTreeStatement → RootContentStatement → RootPackingStatement →
      LocalPackingStatement := by
  intro hTree hContent hPack n k μ A a R ρ Λ b M hA ha hR hρ hb hM hADR P F hE w s hs
  have hP : PartitionTree P := hTree n μ.support R P
  have hA0 : 0 < A := by linarith
  have hK : 0 ≤ 1 + 4 * M / b := by positivity
  have h5 : 5 * R ≤ ρ := by linarith
  rcases le_or_gt R s with hRs | hsR
  · -- Large tests: root packing.
    have hroot := hPack n k μ A a R ρ Λ b M hA ha hR h5 hb hM hADR P F hE
    refine le_trans ?_ (le_trans hroot (ENNReal.ofReal_le_ofReal
      (d1blocpack_large_const hK hR hRs)))
    refine ENNReal.tsum_le_tsum fun S => ?_
    beta_reduce
    split_ifs
    · exact le_rfl
    · exact zero_le
  · -- Small tests: grouping at the generation `j` with `s/4 ≤ ℓ_j < 10 s / 4`.
    obtain ⟨j, hj1, hj2⟩ := d1blocpack_generation P hs hsR
    by_cases hex : ∃ S₀ ∈ F.roots, S₀.2 ∈ Metric.ball w s ∧ 4 * P.scale S₀.1 ≤ s
    · obtain ⟨S₀, hS₀r, hS₀w, -⟩ := hex
      have hS₀F : P.InForest a R S₀ := F.roots_forest S₀ hS₀r
      classical
      refine le_trans (d1blocpack_tsum_le_tsum_comm _
        (fun (S : F.roots) (T : d1blocpack_family P a R j S₀.2 (12 * s)) =>
          if P.IsBelow S.1 T.1 then ENNReal.ofReal (4 * P.scale S.1.1) ^ k else 0)
        (fun S => ?_)) ?_
      · -- Each eligible term is charged to its level-`j` ancestor.
        beta_reduce
        split_ifs with hel
        · obtain ⟨T, hT, hST⟩ := d1blocpack_ancestor_mem_family hP hj1 hj2
            (F.roots_forest S.1 S.2) hel.1 hel.2 hS₀w
          refine le_trans (le_of_eq ?_)
            (ENNReal.le_tsum (f := fun T : d1blocpack_family P a R j S₀.2 (12 * s) =>
              if P.IsBelow S.1 T.1 then ENNReal.ofReal (4 * P.scale S.1.1) ^ k else 0)
              ⟨T, hT⟩)
          exact (ite_eq_left hST).symm
        · exact zero_le
      · -- Root content at each grouping cell, disjointness, and recentring.
        have hcell : ∀ T : d1blocpack_family P a R j S₀.2 (12 * s),
            (∑' S : F.roots,
              if P.IsBelow S.1 T.1 then ENNReal.ofReal (4 * P.scale S.1.1) ^ k else 0) ≤
            ENNReal.ofReal (16 ^ k * A * (1 + 4 * M / b)) * μ (P.cellOf T.1) := fun T =>
          le_trans
            (d1blocpack_tsum_ite_le F.roots (fun S => P.IsBelow S T.1)
              (fun S => ENNReal.ofReal (4 * P.scale S.1) ^ k))
            (hContent n k μ A a R ρ Λ b M hA hR h5 hb hM hADR P F hE T.1 T.2.2.2.1)
        refine le_trans (ENNReal.tsum_le_tsum hcell) ?_
        rw [ENNReal.tsum_mul_left]
        refine le_trans (mul_le_mul_of_nonneg_left
          (d1blocpack_tsum_measure_le P μ a R j S₀.2 (12 * s)) zero_le) ?_
        refine le_trans (mul_le_mul_of_nonneg_left
          (d1blocpack_recentre hP hρ hADR hS₀F hs hsR) zero_le) ?_
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 16 ^ k * A * (1 + 4 * M / b) by positivity)]
        exact ENNReal.ofReal_le_ofReal (le_of_eq (d1blocpack_small_const k A _ s))
    · -- No eligible root: every term vanishes.
      refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun S => ?_)) zero_le
      exact ite_eq_right fun h => hex ⟨S.1, S.2, h.1, h.2⟩

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
