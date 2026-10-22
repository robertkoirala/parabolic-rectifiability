import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Nearest cell midpoint

In the decorated segment construction, a parent interval of length `L` is cut into `N_j`
cells; every point of the half-open parent interval has a nearest cell midpoint.
The right endpoint is excluded so the floor index remains below `N_j`. -/

noncomputable section
namespace ParabolicRectifiability.Examples

/-- Every point in the half-open parent interval has a nearest cell midpoint. -/
theorem e2_sap_cell_proof : E2sapCell := by
  intro a L x j hL hax hxl
  have hN : (0 : ℝ) < (e2_sapN j : ℝ) := by
    have : 0 < e2_sapN j := by unfold e2_sapN; positivity
    exact_mod_cast this
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (e2_sapN j : ℝ) := ⟨_, rfl⟩
  rw [← hNdef] at hN
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = L / N := ⟨_, rfl⟩
  have hhpos : 0 < h := by rw [hh]; exact div_pos hL hN
  have hNh : N * h = L := by rw [hh]; field_simp
  have ht0 : 0 ≤ (x - a) / h := div_nonneg (by linarith) hhpos.le
  have htN : (x - a) / h < N := by
    rw [div_lt_iff₀ hhpos]; linarith
  have hthh : (x - a) / h * h = x - a := div_mul_cancel₀ _ hhpos.ne'
  refine ⟨⌊(x - a) / h⌋₊, ?_, ?_⟩
  · have := (Nat.floor_lt ht0).2 (by rw [hNdef] at htN; exact htN)
    exact this
  · have h1 := Nat.floor_le ht0
    have h2 := Nat.lt_floor_add_one ((x - a) / h)
    rw [← hNdef, ← hh]
    have h3 : (⌊(x - a) / h⌋₊ : ℝ) * h ≤ (x - a) / h * h := mul_le_mul_of_nonneg_right h1 hhpos.le
    have h4 : (x - a) / h * h < ((⌊(x - a) / h⌋₊ : ℝ) + 1) * h :=
      mul_lt_mul_of_pos_right h2 hhpos
    rw [abs_le]
    constructor <;> nlinarith

end ParabolicRectifiability.Examples
