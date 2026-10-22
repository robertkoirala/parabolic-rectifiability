import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # Closed descendant cells of nested nets

Proof of `d1a_closedCellBasics_proof : ClosedCellBasicsStatement`: the basic properties of the
closed descendant cells and of the level cover.

Part (a): ancestry (`d1acells_ancestor_succ`, `d1acells_ancestor_mem`), the drift
`d_P(w, z) ≤ (10/9) ℓ_j` of descendants (`d1acells_drift`), `parent j z = z` for a persisting
centre (`d1acells_parent_self`), and finitely many children (`d1acells_children_finite`, from
the local finiteness of separated sets in the proper space, `d1acells_finite_inter_closedBall`).

Part (b): the descendant-set and closed-cell child unions, the inclusions in `E` and in
`P(z, 2 ℓ_j)`, and the level cover by a recurring level-`j` ancestor; then
`d1a_closedCellBasics_proof`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}

/-! ## Scales -/

theorem d1acells_scale_pos (N : NestedNets E ℓ₀) (j : ℕ) : 0 < coherentScale ℓ₀ j :=
  div_pos N.scale_pos (pow_pos (by norm_num) j)

theorem d1acells_scale_add (j d : ℕ) :
    coherentScale ℓ₀ (j + d) = coherentScale ℓ₀ j / 10 ^ d := by
  simp only [coherentScale, pow_add, div_div]

theorem d1acells_scale_succ (j : ℕ) :
    coherentScale ℓ₀ (j + 1) = coherentScale ℓ₀ j / 10 := by
  rw [d1acells_scale_add, pow_one]

theorem d1acells_scale_add_le (N : NestedNets E ℓ₀) (j d : ℕ) :
    coherentScale ℓ₀ (j + d) ≤ coherentScale ℓ₀ j := by
  rw [d1acells_scale_add]
  exact div_le_self (d1acells_scale_pos N j).le (one_le_pow₀ (by norm_num))

/-- Fine scales become arbitrarily small. -/
theorem d1acells_scale_eventually_lt (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d → coherentScale ℓ₀ (j + d) < ε := by
  obtain ⟨D₀, hD₀⟩ := pow_unbounded_of_one_lt (coherentScale ℓ₀ j / ε) (by norm_num : (1 : ℝ) < 10)
  refine ⟨D₀, fun d hd => ?_⟩
  have h10 : (10 : ℝ) ^ D₀ ≤ 10 ^ d := pow_le_pow_right₀ (by norm_num) hd
  have hp : (0 : ℝ) < 10 ^ d := pow_pos (by norm_num) d
  have h1 : coherentScale ℓ₀ j < 10 ^ d * ε := (div_lt_iff₀ hε).mp (hD₀.trans_le h10)
  rw [d1acells_scale_add, div_lt_iff₀ hp]
  calc coherentScale ℓ₀ j < 10 ^ d * ε := h1
    _ = ε * 10 ^ d := mul_comm _ _

/-! ## Local finiteness of separated sets -/

/-- An `s`-separated set (`s > 0`) meets every closed ball of the proper space `Space n` in a
finite set. -/
theorem d1acells_finite_inter_closedBall {S : Set (Space n)} {s : ℝ} (hs : 0 < s)
    (hsep : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → s ≤ dist z z') (x : Space n) (r : ℝ) :
    (S ∩ Metric.closedBall x r).Finite := by
  obtain ⟨t, htf, hcov⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall x r).totallyBounded (s / 2) (half_pos hs)
  have hsub : ∀ y : Space n, (S ∩ Metric.ball y (s / 2)).Subsingleton := by
    intro y a ha b hb
    by_contra hab
    have h1 := hsep a ha.1 b hb.1 hab
    have h2 : dist a b < s := by
      calc dist a b ≤ dist a y + dist b y := dist_triangle_right a b y
        _ < s / 2 + s / 2 := add_lt_add (Metric.mem_ball.mp ha.2) (Metric.mem_ball.mp hb.2)
        _ = s := add_halves s
    linarith
  refine (Set.Finite.biUnion (t := fun y => S ∩ Metric.ball y (s / 2)) htf
    fun y _ => (hsub y).finite).subset ?_
  rintro a ⟨haS, haK⟩
  obtain ⟨y, hy, hay⟩ := mem_iUnion₂.mp (hcov haK)
  exact mem_iUnion₂.mpr ⟨y, hy, haS, hay⟩

/-! ## Part (a): parents, ancestry, drift, finitely many children -/

/-- A persisting centre is its own parent: `parent j z = z` for `z ∈ 𝒵_j ⊆ 𝒵_{j+1}`. -/
theorem d1acells_parent_self (N : NestedNets E ℓ₀) {j : ℕ} {z : Space n}
    (hz : z ∈ N.center j) : N.parent j z = z := by
  have h1 := N.parent_nearest j z (N.center_mono j hz) z hz
  exact (dist_le_zero.mp (h1.trans_eq (dist_self z))).symm

/-- A parent step has length at most `ℓ_j` (cover and nearest parent). -/
theorem d1acells_parent_dist (N : NestedNets E ℓ₀) {j : ℕ} {w : Space n}
    (hw : w ∈ N.center (j + 1)) : dist w (N.parent j w) ≤ coherentScale ℓ₀ j := by
  obtain ⟨z, hz, hd⟩ := N.center_cover j w (N.center_subset (j + 1) hw)
  exact (N.parent_nearest j w hw z hz).trans hd

/-- Ancestry peeled at the top: `ancestor j (d+1) w = parent j (ancestor (j+1) d w)`. -/
theorem d1acells_ancestor_succ (N : NestedNets E ℓ₀) (j : ℕ) :
    ∀ (d : ℕ) (w : Space n), N.ancestor j (d + 1) w = N.parent j (N.ancestor (j + 1) d w)
  | 0, _ => rfl
  | d + 1, w => by
      have ih := d1acells_ancestor_succ N j d (N.parent (j + (d + 1)) w)
      show N.ancestor j (d + 1) (N.parent (j + (d + 1)) w) =
        N.parent j (N.ancestor (j + 1) d (N.parent (j + 1 + d) w))
      rw [ih, show j + 1 + d = j + (d + 1) by omega]

/-- Ancestors of centres are centres: `w ∈ 𝒵_{j+d} → ancestor j d w ∈ 𝒵_j`. -/
theorem d1acells_ancestor_mem (N : NestedNets E ℓ₀) {j : ℕ} :
    ∀ {d : ℕ} {w : Space n}, w ∈ N.center (j + d) → N.ancestor j d w ∈ N.center j
  | 0, _, hw => hw
  | d + 1, w, hw => d1acells_ancestor_mem N (d := d) (N.parent_mem (j + d) w hw)

/-- **Drift**: a level-`(j+d)` centre lies within `(10/9) ℓ_j` of its level-`j`
ancestor (`∑_{q ≥ j} ℓ_q = (10/9) ℓ_j`). -/
theorem d1acells_drift (N : NestedNets E ℓ₀) :
    ∀ (d j : ℕ) (w : Space n), w ∈ N.center (j + d) →
      dist w (N.ancestor j d w) ≤ 10 / 9 * coherentScale ℓ₀ j
  | 0, j, w, _ => by
      have := d1acells_scale_pos N j
      show dist w w ≤ 10 / 9 * coherentScale ℓ₀ j
      rw [dist_self]
      positivity
  | d + 1, j, w, hw => by
      have hw' : w ∈ N.center (j + 1 + d) := by
        rw [show j + 1 + d = j + (d + 1) by omega]
        exact hw
      have hu : N.ancestor (j + 1) d w ∈ N.center (j + 1) := d1acells_ancestor_mem N hw'
      have h1 := d1acells_drift N d (j + 1) w hw'
      have h2 := d1acells_parent_dist N (j := j) hu
      have h3 := dist_triangle w (N.ancestor (j + 1) d w) (N.parent j (N.ancestor (j + 1) d w))
      rw [d1acells_ancestor_succ]
      rw [d1acells_scale_succ] at h1
      linarith

/-- Descendants of `(j, z)` lie within `(10/9) ℓ_j` of `z`. -/
theorem d1acells_descendants_dist (N : NestedNets E ℓ₀) {j : ℕ} {z w : Space n}
    (hw : w ∈ N.descendants j z) : dist w z ≤ 10 / 9 * coherentScale ℓ₀ j := by
  obtain ⟨d, hwd, hanc⟩ := hw
  rw [← hanc]
  exact d1acells_drift N d j w hwd

/-- Children of `(j, z)` lie within `ℓ_j` of `z`. -/
theorem d1acells_children_dist (N : NestedNets E ℓ₀) {j : ℕ} {z w : Space n}
    (hw : w ∈ N.children j z) : dist w z ≤ coherentScale ℓ₀ j := by
  obtain ⟨hwc, hpw⟩ := hw
  rw [← hpw]
  exact d1acells_parent_dist N hwc

/-- **Finitely many children**: `{w ∈ 𝒵_{j+1} : parent j w = z}` is finite. -/
theorem d1acells_children_finite (N : NestedNets E ℓ₀) (j : ℕ) (z : Space n) :
    (N.children j z).Finite := by
  refine (d1acells_finite_inter_closedBall (d1acells_scale_pos N (j + 1))
    (N.center_separated (j + 1)) z (coherentScale ℓ₀ j)).subset ?_
  intro w hw
  exact ⟨hw.1, Metric.mem_closedBall.mpr (d1acells_children_dist N hw)⟩

/-! ## Part (b): child unions, inclusions and the level cover -/

/-- Descendant child union: `D_{j,z} = ⋃_{parent(w) = z} D_{j+1,w}` (the persisting centre `z`
is its own child). -/
theorem d1acells_descendants_eq_iUnion (N : NestedNets E ℓ₀) {j : ℕ} {z : Space n}
    (hz : z ∈ N.center j) :
    N.descendants j z = ⋃ w ∈ N.children j z, N.descendants (j + 1) w := by
  ext x
  constructor
  · rintro ⟨d, hx, hanc⟩
    cases d with
    | zero =>
        change x = z at hanc
        subst hanc
        exact mem_iUnion₂.mpr
          ⟨x, ⟨N.center_mono j hz, d1acells_parent_self N hz⟩, 0, N.center_mono j hz, rfl⟩
    | succ d =>
        have hx' : x ∈ N.center (j + 1 + d) := by
          rw [show j + 1 + d = j + (d + 1) by omega]
          exact hx
        rw [d1acells_ancestor_succ] at hanc
        exact mem_iUnion₂.mpr
          ⟨N.ancestor (j + 1) d x, ⟨d1acells_ancestor_mem N hx', hanc⟩, d, hx', rfl⟩
  · intro hx
    obtain ⟨w, ⟨_, hpw⟩, d, hxd, hanc⟩ := mem_iUnion₂.mp hx
    refine ⟨d + 1, ?_, ?_⟩
    · rw [show j + (d + 1) = j + 1 + d by omega]
      exact hxd
    · rw [d1acells_ancestor_succ, hanc, hpw]

/-- **Closed-cell child union**. -/
theorem d1acells_closedCell_children (N : NestedNets E ℓ₀) {j : ℕ} {z : Space n}
    (hz : z ∈ N.center j) :
    N.closedCell j z = ⋃ w ∈ N.children j z, N.closedCell (j + 1) w := by
  simp only [NestedNets.closedCell]
  rw [d1acells_descendants_eq_iUnion N hz, (d1acells_children_finite N j z).closure_biUnion]

/-- Closed cells lie in the closed set `E`. -/
theorem d1acells_closedCell_subset (N : NestedNets E ℓ₀) (hE : IsClosed E) (j : ℕ)
    (z : Space n) : N.closedCell j z ⊆ E := by
  refine closure_minimal ?_ hE
  rintro w ⟨d, hwd, _⟩
  exact N.center_subset (j + d) hwd

/-- Closed cells lie in `P(z, (10/9) ℓ_j)` closed, hence in `P(z, 2 ℓ_j)`. -/
theorem d1acells_closedCell_subset_ball (N : NestedNets E ℓ₀) (j : ℕ) (z : Space n) :
    N.closedCell j z ⊆ Metric.ball z (2 * coherentScale ℓ₀ j) := by
  have hpos := d1acells_scale_pos N j
  have h1 : N.closedCell j z ⊆ Metric.closedBall z (10 / 9 * coherentScale ℓ₀ j) := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro w hw
    exact Metric.mem_closedBall.mpr (d1acells_descendants_dist N hw)
  exact h1.trans (Metric.closedBall_subset_ball (by linarith))

/-- **Level cover**: every `x ∈ E` lies in a level-`j` closed cell, through a level-`j`
ancestor that recurs along fine-net approximants of `x`. -/
theorem d1acells_cover (N : NestedNets E ℓ₀) (j : ℕ) {x : Space n} (hx : x ∈ E) :
    ∃ z ∈ N.center j, x ∈ N.closedCell j z := by
  choose w hw hwx using fun d : ℕ => N.center_cover (j + d) x hx
  have hpos := d1acells_scale_pos N j
  have hSfin : (N.center j ∩ Metric.closedBall x (3 * coherentScale ℓ₀ j)).Finite :=
    d1acells_finite_inter_closedBall hpos (N.center_separated j) x _
  have hmem : ∀ d, N.ancestor j d (w d) ∈
      N.center j ∩ Metric.closedBall x (3 * coherentScale ℓ₀ j) := by
    intro d
    refine ⟨d1acells_ancestor_mem N (hw d), ?_⟩
    rw [Metric.mem_closedBall]
    have h1 := d1acells_drift N d j (w d) (hw d)
    have h2 := hwx d
    have h3 := d1acells_scale_add_le N j d
    have h4 := dist_triangle (N.ancestor j d (w d)) (w d) x
    rw [dist_comm (N.ancestor j d (w d)) (w d), dist_comm (w d) x] at h4
    linarith
  have := hSfin.to_subtype
  let f : ℕ → ↥(N.center j ∩ Metric.closedBall x (3 * coherentScale ℓ₀ j)) :=
    fun d => ⟨N.ancestor j d (w d), hmem d⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  have hinf : (f ⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
  refine ⟨y.1, y.2.1, Metric.mem_closure_iff.mpr fun ε hε => ?_⟩
  obtain ⟨D₀, hD₀⟩ := d1acells_scale_eventually_lt (ℓ₀ := ℓ₀) j hε
  obtain ⟨d, hd, hlt⟩ := hinf.exists_gt D₀
  have hfd : f d = y := hd
  refine ⟨w d, ⟨d, hw d, congrArg Subtype.val hfd⟩, ?_⟩
  exact (hwx d).trans_lt (hD₀ d hlt.le)

/-! ## The statement -/

/-- **Closed descendant cells** (`ClosedCellBasicsStatement`). -/
theorem d1a_closedCellBasics_proof : ClosedCellBasicsStatement := by
  intro n E ℓ₀ N hE
  exact
    { closedCell_subset := fun j z => d1acells_closedCell_subset N hE j z
      closedCell_subset_ball := fun j z _ => d1acells_closedCell_subset_ball N j z
      closedCell_children := fun j _ hz => d1acells_closedCell_children N hz
      closedCell_cover := fun j x hx => by
        obtain ⟨z, hz, hxz⟩ := d1acells_cover N j hx
        exact mem_iUnion₂.mpr ⟨z, hz, hxz⟩ }

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
