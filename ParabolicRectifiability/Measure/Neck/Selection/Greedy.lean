import Mathlib

/-!
# Greedy selections in a compact set

Two finite selections used at every stage of the source construction
(the construction of a neck from a source):

* `exists_terminal_selection`: from a set `E` inside a compact set, select centers
  `t 0, t 1, …` in decreasing order of a function `f` with only finitely many values
  `≥ r > 0` on `E`, each outside the earlier balls `P(t l, f(t l))`, until `f < r` on what
  remains;
* `exists_maximal_net`: a maximal `s`-separated finite subset of a set `A` inside a
  compact set; its `s`-balls cover `A`.

Both are obtained from a maximal admissible finite prefix: admissible prefixes are
`r`- (respectively `s`-) separated, so their lengths are bounded by the size of a finite
cover of the compact set by balls of half that radius; a longest prefix cannot be
extended, which is the stopping (respectively covering) property.
-/

namespace ParabolicRectifiability

namespace NeckSelection

open Set

variable {X : Type*} [PseudoMetricSpace X]

/-- Separated finite families in a compact set have uniformly bounded size. -/
theorem exists_separated_card_bound {B : Set X} (hB : IsCompact B) {s : ℝ} (hs : 0 < s) :
    ∃ N : ℕ, ∀ (m : ℕ) (t : ℕ → X), (∀ i < m, t i ∈ B) →
      (∀ i < m, ∀ l < m, i ≠ l → s ≤ dist (t i) (t l)) → m ≤ N := by
  obtain ⟨F, -, hF, hcover⟩ := finite_cover_balls_of_compact hB (half_pos hs)
  refine ⟨hF.toFinset.card, fun m t htB hsep => ?_⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm]
    exact Nat.zero_le _
  have : Nonempty X := ⟨t 0⟩
  have hc : ∀ i, i < m → ∃ x ∈ F, t i ∈ Metric.ball x (s / 2) := by
    intro i hi
    obtain ⟨x, hx, hxb⟩ := mem_iUnion₂.mp (hcover (htB i hi))
    exact ⟨x, hx, hxb⟩
  choose! g hgF hgb using hc
  have hmaps : Set.MapsTo g (Finset.range m : Set ℕ) (hF.toFinset : Set X) := by
    intro i hi
    rw [Finset.coe_range, Set.mem_Iio] at hi
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hgF i hi
  have hinj : Set.InjOn g (Finset.range m : Set ℕ) := by
    intro i hi l hl hgl
    rw [Finset.coe_range, Set.mem_Iio] at hi hl
    by_contra hne
    have h1 := hgb i hi
    have h2 := hgb l hl
    rw [Metric.mem_ball] at h1 h2
    rw [hgl] at h1
    have h3 := hsep i hi l hl hne
    have h4 := dist_triangle_right (t i) (t l) (g l)
    linarith
  have h := Finset.card_le_card_of_injOn g hmaps hinj
  simpa using h

/-- A predicate on prefixes `(m, a)` with bounded lengths and the empty prefix admits a
prefix of maximal length. -/
theorem exists_maximal_of_bounded {α : Type*} (V : ℕ → α → Prop) (N : ℕ)
    (hbound : ∀ m a, V m a → m ≤ N) (h0 : ∃ a, V 0 a) :
    ∃ m a, V m a ∧ ∀ m' a', V m' a' → m' ≤ m := by
  classical
  obtain ⟨a, ha⟩ := Nat.findGreatest_spec (P := fun m => ∃ a, V m a) (Nat.zero_le N) h0
  refine ⟨Nat.findGreatest (fun m => ∃ a, V m a) N, a, ha, fun m' a' h' => ?_⟩
  by_contra hlt
  push Not at hlt
  exact Nat.findGreatest_is_greatest hlt (hbound m' a' h') ⟨a', h'⟩

/-- An admissible prefix of the greedy terminal selection. -/
structure IsGreedyPrefix (E : Set X) (f : X → ℝ) (r : ℝ) (m : ℕ) (t : ℕ → X) : Prop where
  mem : ∀ i < m, t i ∈ E \ ⋃ (l : ℕ) (_ : l < i), Metric.ball (t l) (f (t l))
  large : ∀ i < m, r ≤ f (t i)
  max : ∀ i < m, ∀ z ∈ E \ ⋃ (l : ℕ) (_ : l < i), Metric.ball (t l) (f (t l)), f z ≤ f (t i)

/-- The greedy terminal selection terminates with `f < r` on the remainder. -/
theorem exists_terminal_selection [Nonempty X] {E B : Set X} (hB : IsCompact B) (hEB : E ⊆ B)
    (f : X → ℝ) {r : ℝ} (hr : 0 < r) (hfin : (f '' E ∩ Ici r).Finite) :
    ∃ (m : ℕ) (t : ℕ → X), IsGreedyPrefix E f r m t ∧
      ∀ z ∈ E \ ⋃ (i : ℕ) (_ : i < m), Metric.ball (t i) (f (t i)), f z < r := by
  classical
  obtain ⟨N, hN⟩ := exists_separated_card_bound hB hr
  have hbound : ∀ m t, IsGreedyPrefix E f r m t → m ≤ N := by
    intro m t ht
    refine hN m t (fun i hi => hEB (ht.mem i hi).1) ?_
    intro i hi l hl hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hnot : t l ∉ Metric.ball (t i) (f (t i)) := fun hb =>
        (ht.mem l hl).2 (mem_iUnion₂.mpr ⟨i, h, hb⟩)
      rw [Metric.mem_ball, not_lt] at hnot
      rw [dist_comm]
      exact (ht.large i hi).trans hnot
    · have hnot : t i ∉ Metric.ball (t l) (f (t l)) := fun hb =>
        (ht.mem i hi).2 (mem_iUnion₂.mpr ⟨l, h, hb⟩)
      rw [Metric.mem_ball, not_lt] at hnot
      exact (ht.large l hl).trans hnot
  have h0 : ∃ t, IsGreedyPrefix E f r 0 t :=
    ⟨fun _ => Classical.arbitrary X, ⟨fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => absurd hi (Nat.not_lt_zero i), fun i hi => absurd hi (Nat.not_lt_zero i)⟩⟩
  obtain ⟨m, t, ht, hmax⟩ := exists_maximal_of_bounded (IsGreedyPrefix E f r) N hbound h0
  refine ⟨m, t, ht, fun z hz => ?_⟩
  by_contra hge
  push Not at hge
  -- the largest value `≥ r` of `f` on the remainder
  have hVfin : (f '' (E \ ⋃ (i : ℕ) (_ : i < m), Metric.ball (t i) (f (t i))) ∩ Ici r).Finite :=
    hfin.subset (inter_subset_inter_left _ (image_mono Set.sdiff_subset))
  have hne : hVfin.toFinset.Nonempty :=
    ⟨f z, hVfin.mem_toFinset.mpr ⟨⟨z, hz, rfl⟩, hge⟩⟩
  have hv := hVfin.mem_toFinset.mp (Finset.max'_mem _ hne)
  have hvmax : ∀ w ∈ f '' (E \ ⋃ (i : ℕ) (_ : i < m), Metric.ball (t i) (f (t i))) ∩ Ici r,
      w ≤ hVfin.toFinset.max' hne :=
    fun w hw => Finset.le_max' _ w (hVfin.mem_toFinset.mpr hw)
  obtain ⟨⟨y, hyA, hyv⟩, hvr⟩ := hv
  obtain ⟨t', ht'lt, ht'm⟩ : ∃ t' : ℕ → X, (∀ i < m, t' i = t i) ∧ t' m = y :=
    ⟨fun i => if i < m then t i else y, fun i hi => ite_eq_left hi, ite_eq_right (lt_irrefl m)⟩
  have hU : ∀ i ≤ m, (⋃ (l : ℕ) (_ : l < i), Metric.ball (t' l) (f (t' l))) =
      ⋃ (l : ℕ) (_ : l < i), Metric.ball (t l) (f (t l)) := by
    intro i hi
    refine iUnion₂_congr fun l hl => ?_
    rw [ht'lt l (lt_of_lt_of_le hl hi)]
  have hext : IsGreedyPrefix E f r (m + 1) t' := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · have hi' := Nat.lt_add_one_iff.mp hi
      rw [hU i hi']
      rcases lt_or_eq_of_le hi' with h | h
      · rw [ht'lt i h]
        exact ht.mem i h
      · rw [h, ht'm]
        exact hyA
    · rcases lt_or_eq_of_le (Nat.lt_add_one_iff.mp hi) with h | h
      · rw [ht'lt i h]
        exact ht.large i h
      · rw [h, ht'm, hyv]
        exact hvr
    · intro w hw
      have hi' := Nat.lt_add_one_iff.mp hi
      rw [hU i hi'] at hw
      rcases lt_or_eq_of_le hi' with h | h
      · rw [ht'lt i h]
        exact ht.max i h w hw
      · rw [h, ht'm, hyv]
        rw [h] at hw
        by_cases hwr : r ≤ f w
        · exact hvmax (f w) ⟨⟨w, hw, rfl⟩, hwr⟩
        · push Not at hwr
          exact hwr.le.trans hvr
  have := hmax (m + 1) t' hext
  omega

/-- An admissible prefix of a separated net. -/
structure IsSeparatedPrefix (A : Set X) (s : ℝ) (c : ℕ) (g : ℕ → X) : Prop where
  mem : ∀ i < c, g i ∈ A
  sep : ∀ i < c, ∀ l < c, i ≠ l → s ≤ dist (g i) (g l)

/-- A maximal finite `s`-separated subset of `A` (inside a compact set) whose `s`-balls
cover `A`. -/
theorem exists_maximal_net [Nonempty X] {A B : Set X} (hB : IsCompact B) (hAB : A ⊆ B) {s : ℝ}
    (hs : 0 < s) :
    ∃ (c : ℕ) (g : ℕ → X), (∀ i < c, g i ∈ A) ∧
      (∀ i < c, ∀ l < c, i ≠ l → s ≤ dist (g i) (g l)) ∧
      A ⊆ ⋃ (i : ℕ) (_ : i < c), Metric.ball (g i) s := by
  classical
  obtain ⟨N, hN⟩ := exists_separated_card_bound hB hs
  have h0 : ∃ g, IsSeparatedPrefix A s 0 g :=
    ⟨fun _ => Classical.arbitrary X, ⟨fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩⟩
  obtain ⟨c, g, hg, hmax⟩ := exists_maximal_of_bounded (IsSeparatedPrefix A s) N
    (fun c g h => hN c g (fun i hi => hAB (h.mem i hi)) h.sep) h0
  refine ⟨c, g, hg.mem, hg.sep, fun z hz => ?_⟩
  by_contra hnot
  have hfar : ∀ i < c, s ≤ dist z (g i) := by
    intro i hi
    by_contra h
    push Not at h
    exact hnot (mem_iUnion₂.mpr ⟨i, hi, Metric.mem_ball.mpr h⟩)
  obtain ⟨g', hg'lt, hg'c⟩ : ∃ g' : ℕ → X, (∀ i < c, g' i = g i) ∧ g' c = z :=
    ⟨fun i => if i < c then g i else z, fun i hi => ite_eq_left hi, ite_eq_right (lt_irrefl c)⟩
  have hext : IsSeparatedPrefix A s (c + 1) g' := by
    refine ⟨fun i hi => ?_, fun i hi l hl hne => ?_⟩
    · rcases lt_or_eq_of_le (Nat.lt_add_one_iff.mp hi) with h | h
      · rw [hg'lt i h]
        exact hg.mem i h
      · rw [h, hg'c]
        exact hz
    · rcases lt_or_eq_of_le (Nat.lt_add_one_iff.mp hi) with h1 | h1 <;>
        rcases lt_or_eq_of_le (Nat.lt_add_one_iff.mp hl) with h2 | h2
      · rw [hg'lt i h1, hg'lt l h2]
        exact hg.sep i h1 l h2 hne
      · rw [hg'lt i h1, h2, hg'c, dist_comm]
        exact hfar i h1
      · rw [h1, hg'c, hg'lt l h2]
        exact hfar l h2
      · exact absurd (h1.trans h2.symm) hne
  have := hmax (c + 1) g' hext
  omega

end NeckSelection

end ParabolicRectifiability
