import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy
import ParabolicRectifiability.Metric.ProperSpace

/-! # Net extension

Proves `d1a_netExtension_proof : NetExtensionStatement`.

Route: a countable dense subset `range f` of `E` (second countability) and greedy retention
along `f`, starting from all of `Z₀` (`d1anet_stage`, by `Nat.rec`): `f k` is retained when it
lies at distance `≥ s` from `Z₀` and from the points retained before. The union is separated and
contained in `E`; it is countable because separated sets in a proper space are locally finite.
The covering bound is attained: if every retained point were at distance `> s` from `x ∈ E`,
local finiteness would give a margin `ε > 0`, and a dense point within `ε` of `x` would have been
retained.

**Exported helpers** (used by the construction of nested nets):
`d1anet_finite_inter_closedBall` (local finiteness of separated sets in a proper metric space)
and its consequence `d1anet_exists_nearest` (an attained nearest point).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

section Helpers

variable {X : Type*} [MetricSpace X]

/-- **Local finiteness** (exported for NEST): an `s`-separated set (`s > 0`) in a proper metric
space meets every closed ball in a finite set. -/
theorem d1anet_finite_inter_closedBall [ProperSpace X] {S : Set X} {s : ℝ} (hs : 0 < s)
    (hS : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → s ≤ dist z z') (x : X) (r : ℝ) :
    (S ∩ Metric.closedBall x r).Finite := by
  obtain ⟨t, -, htf, hcov⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall x r) (half_pos hs)
  have hmem : ∀ y ∈ S ∩ Metric.closedBall x r, ∃ c ∈ t, y ∈ Metric.ball c (s / 2) := by
    intro y hy
    have h := hcov hy.2
    simpa only [mem_iUnion, exists_prop] using h
  have : Nonempty X := ⟨x⟩
  choose! g hgt hgb using hmem
  refine Set.Finite.of_finite_image (f := g) (htf.subset ?_) ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact hgt y hy
  · intro y hy y' hy' hyy'
    by_contra hne
    have h1 := hS y hy.1 y' hy'.1 hne
    have a := hgb y hy
    have b := hgb y' hy'
    rw [hyy'] at a
    rw [Metric.mem_ball] at a b
    have h2 : dist y y' < s := by
      calc dist y y' ≤ dist y (g y') + dist y' (g y') := dist_triangle_right _ _ _
        _ < s / 2 + s / 2 := add_lt_add a b
        _ = s := add_halves s
    linarith

/-- **Attained nearest point** (exported for NEST): if an `s`-separated set in a proper space
meets `closedBall x r`, some point of it minimizes the distance to `x`, at distance `≤ r`. -/
theorem d1anet_exists_nearest [ProperSpace X] {S : Set X} {s : ℝ} (hs : 0 < s)
    (hS : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → s ≤ dist z z') (x : X) {r : ℝ}
    (hne : (S ∩ Metric.closedBall x r).Nonempty) :
    ∃ a ∈ S, dist x a ≤ r ∧ ∀ z ∈ S, dist x a ≤ dist x z := by
  obtain ⟨a, ha, hmin⟩ :=
    Set.exists_min_image _ (fun z => dist x z) (d1anet_finite_inter_closedBall hs hS x r) hne
  have har : dist x a ≤ r := by
    have h := ha.2
    rw [Metric.mem_closedBall, dist_comm] at h
    exact h
  refine ⟨a, ha.1, har, fun z hz => ?_⟩
  by_cases hzr : dist x z ≤ r
  · exact hmin z ⟨hz, by rw [Metric.mem_closedBall, dist_comm]; exact hzr⟩
  · push Not at hzr
    linarith

/-- Separated sets in a proper space are countable (a countable union of finite pieces). -/
theorem d1anet_countable_of_separated [ProperSpace X] {S : Set X} {s : ℝ} (hs : 0 < s)
    (hS : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → s ≤ dist z z') : S.Countable := by
  rcases S.eq_empty_or_nonempty with h | ⟨x, -⟩
  · rw [h]
    exact countable_empty
  · have hU : S = ⋃ m : ℕ, S ∩ Metric.closedBall x m := by
      rw [← inter_iUnion, Metric.iUnion_closedBall_nat, inter_univ]
    rw [hU]
    exact countable_iUnion fun m => (d1anet_finite_inter_closedBall hs hS x m).countable

/-- A margin beyond `s`: if every point of a separated set is at distance `> s` from `x`, then
all are at distance `≥ s + ε` for some `ε > 0`. -/
theorem d1anet_margin [ProperSpace X] {S : Set X} {s : ℝ} (hs : 0 < s)
    (hS : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → s ≤ dist z z') {x : X}
    (h : ∀ z ∈ S, s < dist x z) : ∃ ε > 0, ∀ z ∈ S, s + ε ≤ dist x z := by
  by_cases hne : (S ∩ Metric.closedBall x (2 * s)).Nonempty
  · obtain ⟨a, ha, -, hmin⟩ := d1anet_exists_nearest hs hS x hne
    have hxa := h a ha
    exact ⟨dist x a - s, by linarith, fun z hz => by linarith [hmin z hz]⟩
  · refine ⟨s, hs, fun z hz => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hne ⟨z, hz, by rw [Metric.mem_closedBall, dist_comm]; linarith⟩

/-- Inserting a point at distance `≥ s` from an `s`-separated set keeps it separated. -/
theorem d1anet_sep_insert {s : ℝ} {T : Set X} {p : X}
    (hT : ∀ z ∈ T, ∀ z' ∈ T, z ≠ z' → s ≤ dist z z') (hp : ∀ z ∈ T, s ≤ dist p z) :
    ∀ z ∈ insert p T, ∀ z' ∈ insert p T, z ≠ z' → s ≤ dist z z' := by
  intro z hz z' hz' hne
  rcases hz with rfl | hz <;> rcases hz' with rfl | hz'
  · exact absurd rfl hne
  · exact hp z' hz'
  · rw [dist_comm]
    exact hp z hz
  · exact hT z hz z' hz' hne

end Helpers

section Greedy

variable {X : Type*} [MetricSpace X]

open Classical in
/-- The greedy stages: `d1anet_stage Z₀ s f k` is the set of points `f i`, `i < k`, retained
along the enumeration `f`, starting with all of `Z₀` already retained. -/
def d1anet_stage (Z₀ : Set X) (s : ℝ) (f : ℕ → X) : ℕ → Set X
  | 0 => ∅
  | k + 1 =>
      if ∀ z ∈ Z₀ ∪ d1anet_stage Z₀ s f k, s ≤ dist (f k) z then
        insert (f k) (d1anet_stage Z₀ s f k)
      else d1anet_stage Z₀ s f k

variable (Z₀ : Set X) (s : ℝ) (f : ℕ → X)

theorem d1anet_stage_zero : d1anet_stage Z₀ s f 0 = ∅ := rfl

open Classical in
theorem d1anet_stage_succ (k : ℕ) :
    d1anet_stage Z₀ s f (k + 1) =
      if ∀ z ∈ Z₀ ∪ d1anet_stage Z₀ s f k, s ≤ dist (f k) z then
        insert (f k) (d1anet_stage Z₀ s f k)
      else d1anet_stage Z₀ s f k := rfl

theorem d1anet_stage_subset_succ (k : ℕ) :
    d1anet_stage Z₀ s f k ⊆ d1anet_stage Z₀ s f (k + 1) := by
  intro y hy
  rw [d1anet_stage_succ]
  split_ifs
  · exact mem_insert_of_mem _ hy
  · exact hy

theorem d1anet_stage_mono : Monotone (d1anet_stage Z₀ s f) :=
  monotone_nat_of_le_succ (d1anet_stage_subset_succ Z₀ s f)

theorem d1anet_stage_subset_range (k : ℕ) : d1anet_stage Z₀ s f k ⊆ range f := by
  induction k with
  | zero =>
    rw [d1anet_stage_zero]
    exact empty_subset _
  | succ k ih =>
    rw [d1anet_stage_succ]
    split_ifs
    · exact insert_subset (mem_range_self k) ih
    · exact ih

theorem d1anet_mem_stage_succ {k : ℕ}
    (h : ∀ z ∈ Z₀ ∪ d1anet_stage Z₀ s f k, s ≤ dist (f k) z) :
    f k ∈ d1anet_stage Z₀ s f (k + 1) := by
  rw [d1anet_stage_succ, ite_eq_left h]
  exact mem_insert _ _

theorem d1anet_stage_sep (hZ₀ : ∀ z ∈ Z₀, ∀ z' ∈ Z₀, z ≠ z' → s ≤ dist z z') (k : ℕ) :
    ∀ z ∈ Z₀ ∪ d1anet_stage Z₀ s f k, ∀ z' ∈ Z₀ ∪ d1anet_stage Z₀ s f k, z ≠ z' →
      s ≤ dist z z' := by
  induction k with
  | zero =>
    rw [d1anet_stage_zero, union_empty]
    exact hZ₀
  | succ k ih =>
    by_cases h : ∀ z ∈ Z₀ ∪ d1anet_stage Z₀ s f k, s ≤ dist (f k) z
    · rw [d1anet_stage_succ, ite_eq_left h, union_insert]
      exact d1anet_sep_insert ih h
    · rw [d1anet_stage_succ, ite_eq_right h]
      exact ih

/-- Every point of the greedy union lies in some stage union `Z₀ ∪ stage k`. -/
theorem d1anet_exists_stage {z : X} (hz : z ∈ Z₀ ∪ ⋃ k, d1anet_stage Z₀ s f k) :
    ∃ k, z ∈ Z₀ ∪ d1anet_stage Z₀ s f k := by
  rcases hz with h | h
  · exact ⟨0, Or.inl h⟩
  · obtain ⟨k, hk⟩ := mem_iUnion.mp h
    exact ⟨k, Or.inr hk⟩

theorem d1anet_union_sep (hZ₀ : ∀ z ∈ Z₀, ∀ z' ∈ Z₀, z ≠ z' → s ≤ dist z z') :
    ∀ z ∈ Z₀ ∪ ⋃ k, d1anet_stage Z₀ s f k, ∀ z' ∈ Z₀ ∪ ⋃ k, d1anet_stage Z₀ s f k,
      z ≠ z' → s ≤ dist z z' := by
  intro z hz z' hz' hne
  obtain ⟨k, hk⟩ := d1anet_exists_stage Z₀ s f hz
  obtain ⟨k', hk'⟩ := d1anet_exists_stage Z₀ s f hz'
  have hsub : ∀ i, i ≤ max k k' →
      Z₀ ∪ d1anet_stage Z₀ s f i ⊆ Z₀ ∪ d1anet_stage Z₀ s f (max k k') := fun i hi =>
    union_subset_union_right Z₀ (d1anet_stage_mono Z₀ s f hi)
  exact d1anet_stage_sep Z₀ s f hZ₀ (max k k') z (hsub k (le_max_left _ _) hk) z'
    (hsub k' (le_max_right _ _) hk') hne

/-- **Greedy extension along a dense sequence** in a proper metric space. -/
theorem d1anet_extend [ProperSpace X] {E : Set X} (hs : 0 < s) (hZ₀E : Z₀ ⊆ E)
    (hZ₀ : ∀ z ∈ Z₀, ∀ z' ∈ Z₀, z ≠ z' → s ≤ dist z z') (hfE : range f ⊆ E)
    (hEf : E ⊆ closure (range f)) :
    ∃ Z : Set X, Z₀ ⊆ Z ∧ Z ⊆ E ∧ Z.Countable ∧
      (∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → s ≤ dist z z') ∧ ∀ x ∈ E, ∃ z ∈ Z, dist x z ≤ s := by
  have hsep := d1anet_union_sep Z₀ s f hZ₀
  refine ⟨Z₀ ∪ ⋃ k, d1anet_stage Z₀ s f k, subset_union_left,
    union_subset hZ₀E (iUnion_subset fun k => (d1anet_stage_subset_range Z₀ s f k).trans hfE),
    d1anet_countable_of_separated hs hsep, hsep, ?_⟩
  intro x hx
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, hmar⟩ := d1anet_margin hs hsep hcon
  obtain ⟨b, hb, hxb⟩ := Metric.mem_closure_iff.mp (hEf hx) ε hε
  obtain ⟨k, rfl⟩ := hb
  have hret : ∀ z ∈ Z₀ ∪ d1anet_stage Z₀ s f k, s ≤ dist (f k) z := by
    intro z hz
    have hzZ : z ∈ Z₀ ∪ ⋃ k, d1anet_stage Z₀ s f k := by
      rcases hz with h | h
      · exact Or.inl h
      · exact Or.inr (mem_iUnion.mpr ⟨k, h⟩)
    have h1 := hmar z hzZ
    have h2 := dist_triangle x (f k) z
    linarith
  have hfk : f k ∈ Z₀ ∪ ⋃ k, d1anet_stage Z₀ s f k :=
    Or.inr (mem_iUnion.mpr ⟨k + 1, d1anet_mem_stage_succ Z₀ s f hret⟩)
  have h3 := hmar (f k) hfk
  linarith

end Greedy

/-- **Net extension** (`NetExtensionStatement`). -/
theorem d1a_netExtension_proof : NetExtensionStatement := by
  intro n E _hE s hs Z₀ hZ₀E hZ₀
  obtain ⟨c, hcE, hcc, hEc⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace E).exists_countable_dense_subset
  rcases c.eq_empty_or_nonempty with hc | hc
  · refine ⟨Z₀, subset_rfl, hZ₀E, d1anet_countable_of_separated hs hZ₀, hZ₀, ?_⟩
    intro x hx
    have h := hEc hx
    rw [hc, closure_empty] at h
    exact absurd h (notMem_empty x)
  · obtain ⟨f, rfl⟩ := hcc.exists_eq_range hc
    exact d1anet_extend Z₀ s f hs hZ₀E hZ₀ hcE hEc

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
