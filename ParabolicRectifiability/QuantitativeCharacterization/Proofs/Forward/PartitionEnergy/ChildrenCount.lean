import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy
import ParabolicRectifiability.Geometry.SmoothPartition

/-! # The child count

Proof of `d1a_childrenCount : ChildrenCountStatement`. Every child `w` of `(j, z)` lies within `ℓ_j` of `z`
(the level-`j` cover gives some centre within `ℓ_j` of `w`, and the parent `z` is nearest), and the
children are `ℓ_{j+1} = ℓ_j/10`-separated. The parabolic balls `P(w, ℓ_j/20)` are therefore pairwise
disjoint, with centres at distance `< 3 ℓ_j/2` from `z`, and the base volume count
`Geometry.SmoothPartition.card_filter_dist_lt_le` (with `ρ = ℓ_j/20`, `R = 3ℓ_j/2`) bounds every
finite family of children by `((R + ρ)/ρ)^{n+2} = 31^{n+2}` (homogeneous exponent `n + 2`). An
infinite child set would contain a finite subfamily of size `31^{n+2} + 1`; so the set is finite and
its `encard` is at most `31^{n+2}`.

(The radii differ from `ℓ_j/30` inside `(31/30) ℓ_j`, because the base lemma needs a
strict distance bound; the ratio, `31`, is the same.)
-/

set_option autoImplicit false

noncomputable section

open Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

/-- `ℓ_{j+1} = ℓ_j / 10`. -/
theorem d1acount_scale_succ (ℓ₀ : ℝ) (j : ℕ) :
    coherentScale ℓ₀ (j + 1) = coherentScale ℓ₀ j / 10 := by
  unfold coherentScale
  rw [pow_succ, div_div]

/-- `ℓ_j > 0` for `ℓ₀ > 0`. -/
theorem d1acount_scale_pos {ℓ₀ : ℝ} (h : 0 < ℓ₀) (j : ℕ) : 0 < coherentScale ℓ₀ j := by
  unfold coherentScale
  exact div_pos h (pow_pos (by norm_num) j)

/-- A child of `(j, z)` lies within `ℓ_j` of `z`. -/
theorem d1acount_dist_child_le {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} (N : NestedNets E ℓ₀)
    (j : ℕ) (z w : Space n) (hw : w ∈ N.center (j + 1)) (hwz : N.parent j w = z) :
    dist w z ≤ coherentScale ℓ₀ j := by
  obtain ⟨z₀, hz₀, hd⟩ := N.center_cover j w (N.center_subset (j + 1) hw)
  have hnear := N.parent_nearest j w hw z₀ hz₀
  rw [hwz] at hnear
  exact hnear.trans hd

/-- Every finite family of children of `(j, z)` has at most `31^{n+2}` members. -/
theorem d1acount_finset_card_le {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} (N : NestedNets E ℓ₀)
    (j : ℕ) (z : Space n) (I : Finset (Space n))
    (hI : (I : Set (Space n)) ⊆ {w | w ∈ N.center (j + 1) ∧ N.parent j w = z}) :
    I.card ≤ 31 ^ (n + 2) := by
  have hℓ := d1acount_scale_pos N.scale_pos j
  have hdisj : (I : Set (Space n)).PairwiseDisjoint
      fun a => Metric.ball a (coherentScale ℓ₀ j / 20) := by
    intro a ha b hb hab
    have hsep := N.center_separated (j + 1) a (hI ha).1 b (hI hb).1 hab
    rw [d1acount_scale_succ] at hsep
    have hsum : coherentScale ℓ₀ j / 20 + coherentScale ℓ₀ j / 20 ≤ dist a b := by linarith
    exact Metric.ball_disjoint_ball hsum
  have hcount : ((I.filter fun a => dist z a < 3 * coherentScale ℓ₀ j / 2).card : ℝ) ≤
      ((3 * coherentScale ℓ₀ j / 2 + coherentScale ℓ₀ j / 20) / (coherentScale ℓ₀ j / 20)) ^
        (n + 2) :=
    card_filter_dist_lt_le (ι := Space n) (I := I) (z := fun b : Space n => b)
      (ρ := coherentScale ℓ₀ j / 20) (R := 3 * coherentScale ℓ₀ j / 2) (by linarith)
      (by linarith) hdisj z
  have hfilter : (I.filter fun a => dist z a < 3 * coherentScale ℓ₀ j / 2) = I := by
    apply Finset.filter_true_of_mem
    intro a ha
    have h := d1acount_dist_child_le N j z a (hI ha).1 (hI ha).2
    rw [dist_comm] at h
    linarith
  rw [hfilter] at hcount
  have hratio : (3 * coherentScale ℓ₀ j / 2 + coherentScale ℓ₀ j / 20) / (coherentScale ℓ₀ j / 20)
      = 31 := by
    rw [div_eq_iff (div_pos hℓ (by norm_num : (0 : ℝ) < 20)).ne']
    ring
  rw [hratio] at hcount
  exact_mod_cast hcount

/-- **Child count** (`ChildrenCountStatement`). -/
theorem d1a_childrenCount_proof : ChildrenCountStatement := by
  intro n E ℓ₀ N j z _hz
  by_cases hfin : {w | w ∈ N.center (j + 1) ∧ N.parent j w = z}.Finite
  · rw [hfin.encard_eq_coe_toFinset_card]
    have h := d1acount_finset_card_le N j z hfin.toFinset (by rw [Set.Finite.coe_toFinset])
    exact_mod_cast h
  · exfalso
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hfin (31 ^ (n + 2) + 1)
    have h := d1acount_finset_card_le N j z t ht
    rw [htc] at h
    exact Nat.not_succ_le_self _ h

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
