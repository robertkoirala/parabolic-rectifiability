import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.NetExtension

/-! # Nested nets with nearest parents

Proves `d1a_nestedNets_proof : NetExtensionStatement → NestedNetsStatement`, in implication
form: `NetExtensionStatement` enters only as the hypothesis.

The import of `NetExtension` is used only for the exported local-finiteness helper
`d1anet_exists_nearest` (a consequence of `d1anet_finite_inter_closedBall`);
`d1a_netExtension_proof` is not used.

Route: `𝒵₀` = the extension of `∅` at `ℓ₀ = coherentScale ℓ₀ 0`; `𝒵_{j+1}` = the extension of
`𝒵_j` at `ℓ_{j+1}` (`𝒵_j` is `ℓ_j`-, hence `ℓ_{j+1}`-separated), by recursion on `j` with
`Classical.choose` (`d1anest_level`). The parent of `w` is a nearest point of `𝒵_j`
(`d1anest_parent`), which exists for `w ∈ E` because `𝒵_j ∩ closedBall w ℓ_j` is nonempty (cover)
and finite (local finiteness).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

section Nest

variable {n : ℕ}

theorem d1anest_scale_pos {ℓ₀ : ℝ} (h : 0 < ℓ₀) (j : ℕ) : 0 < coherentScale ℓ₀ j :=
  div_pos h (pow_pos (by norm_num) j)

theorem d1anest_scale_succ_le {ℓ₀ : ℝ} (h : 0 < ℓ₀) (j : ℕ) :
    coherentScale ℓ₀ (j + 1) ≤ coherentScale ℓ₀ j :=
  div_le_div_of_nonneg_left h.le (pow_pos (by norm_num) j)
    (pow_le_pow_right₀ (by norm_num) (Nat.le_succ j))

/-- A level of the construction: an `s`-separated countable subset of `E` covering `E` at
distance `≤ s`. -/
structure d1anest_Good (E : Set (Space n)) (s : ℝ) (Z : Set (Space n)) : Prop where
  subset : Z ⊆ E
  countable : Z.Countable
  sep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → s ≤ dist z z'
  cover : ∀ x ∈ E, ∃ z ∈ Z, dist x z ≤ s

theorem d1anest_sep_mono {Z : Set (Space n)} {s t : ℝ} (hst : t ≤ s)
    (hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → s ≤ dist z z') :
    ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → t ≤ dist z z' :=
  fun z hz z' hz' hne => hst.trans (hZ z hz z' hz' hne)

/-- The nested levels `𝒵_j`, by recursion on `j` from the extension hypothesis. -/
def d1anest_level (hext : NetExtensionStatement) (E : Set (Space n)) (hE : IsClosed E)
    (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀) : (j : ℕ) → {Z : Set (Space n) // d1anest_Good E (coherentScale ℓ₀ j) Z}
  | 0 =>
    have h := hext n E hE (coherentScale ℓ₀ 0) (d1anest_scale_pos hℓ₀ 0) ∅ (empty_subset _)
      (fun z hz => absurd hz (notMem_empty z))
    ⟨Classical.choose h, ⟨(Classical.choose_spec h).2.1, (Classical.choose_spec h).2.2.1,
      (Classical.choose_spec h).2.2.2.1, (Classical.choose_spec h).2.2.2.2⟩⟩
  | j + 1 =>
    have h := hext n E hE (coherentScale ℓ₀ (j + 1)) (d1anest_scale_pos hℓ₀ (j + 1))
      (d1anest_level hext E hE ℓ₀ hℓ₀ j).1 (d1anest_level hext E hE ℓ₀ hℓ₀ j).2.subset
      (d1anest_sep_mono (d1anest_scale_succ_le hℓ₀ j) (d1anest_level hext E hE ℓ₀ hℓ₀ j).2.sep)
    ⟨Classical.choose h, ⟨(Classical.choose_spec h).2.1, (Classical.choose_spec h).2.2.1,
      (Classical.choose_spec h).2.2.2.1, (Classical.choose_spec h).2.2.2.2⟩⟩

/-- The levels are nested: the extension keeps the previous level. -/
theorem d1anest_level_mono (hext : NetExtensionStatement) (E : Set (Space n)) (hE : IsClosed E)
    (ℓ₀ : ℝ) (hℓ₀ : 0 < ℓ₀) (j : ℕ) :
    (d1anest_level hext E hE ℓ₀ hℓ₀ j).1 ⊆ (d1anest_level hext E hE ℓ₀ hℓ₀ (j + 1)).1 :=
  (Classical.choose_spec (hext n E hE (coherentScale ℓ₀ (j + 1)) (d1anest_scale_pos hℓ₀ (j + 1))
      (d1anest_level hext E hE ℓ₀ hℓ₀ j).1 (d1anest_level hext E hE ℓ₀ hℓ₀ j).2.subset
      (d1anest_sep_mono (d1anest_scale_succ_le hℓ₀ j)
        (d1anest_level hext E hE ℓ₀ hℓ₀ j).2.sep))).1

open Classical in
/-- The nearest parent: a point of `C j` nearest to `w` when one exists (otherwise `w`). -/
def d1anest_parent (C : ℕ → Set (Space n)) (j : ℕ) (w : Space n) : Space n :=
  if h : ∃ a ∈ C j, ∀ z ∈ C j, dist w a ≤ dist w z then Classical.choose h else w

theorem d1anest_parent_spec (C : ℕ → Set (Space n)) (j : ℕ) (w : Space n)
    (h : ∃ a ∈ C j, ∀ z ∈ C j, dist w a ≤ dist w z) :
    d1anest_parent C j w ∈ C j ∧ ∀ z ∈ C j, dist w (d1anest_parent C j w) ≤ dist w z := by
  rw [d1anest_parent, dite_eq_left h]
  exact Classical.choose_spec h

/-- A nearest point of a level exists for every `w ∈ E` (cover plus local finiteness, through
the exported NET helper `d1anet_exists_nearest`). -/
theorem d1anest_exists_parent {E : Set (Space n)} {s : ℝ} (hs : 0 < s) {Z : Set (Space n)}
    (hZ : d1anest_Good E s Z) {w : Space n} (hw : w ∈ E) :
    ∃ a ∈ Z, ∀ z ∈ Z, dist w a ≤ dist w z := by
  obtain ⟨z, hz, hwz⟩ := hZ.cover w hw
  obtain ⟨a, ha, -, hmin⟩ := d1anet_exists_nearest hs hZ.sep w (r := s)
    ⟨z, hz, by rw [Metric.mem_closedBall, dist_comm]; exact hwz⟩
  exact ⟨a, ha, hmin⟩

end Nest

/-- **Nested nets with nearest parents** (`NetExtensionStatement → NestedNetsStatement`). -/
theorem d1a_nestedNets_proof : NetExtensionStatement → NestedNetsStatement := by
  intro hext n E hE ℓ₀ hℓ₀
  let C : ℕ → Set (Space n) := fun j => (d1anest_level hext E hE ℓ₀ hℓ₀ j).1
  have hgood : ∀ j, d1anest_Good E (coherentScale ℓ₀ j) (C j) := fun j =>
    (d1anest_level hext E hE ℓ₀ hℓ₀ j).2
  have hnear : ∀ j, ∀ w ∈ C (j + 1), d1anest_parent C j w ∈ C j ∧
      ∀ z ∈ C j, dist w (d1anest_parent C j w) ≤ dist w z := fun j w hw =>
    d1anest_parent_spec C j w
      (d1anest_exists_parent (d1anest_scale_pos hℓ₀ j) (hgood j) ((hgood (j + 1)).subset hw))
  exact ⟨{ scale_pos := hℓ₀
           center := C
           parent := d1anest_parent C
           center_subset := fun j => (hgood j).subset
           center_countable := fun j => (hgood j).countable
           center_mono := fun j => d1anest_level_mono hext E hE ℓ₀ hℓ₀ j
           center_separated := fun j => (hgood j).sep
           center_cover := fun j => (hgood j).cover
           parent_mem := fun j w hw => (hnear j w hw).1
           parent_nearest := fun j w hw => (hnear j w hw).2 }⟩

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
