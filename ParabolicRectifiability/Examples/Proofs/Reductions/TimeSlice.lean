import ParabolicRectifiability.Examples.Proofs.Reductions.TimeSliceLemmas

/-! # Assembly of the shared time-slice identity

* `e2_timeSlice_betaPow : E2TimeSliceBetaPowStatement`: the shared identity, composed from the
  affine enlargement `E2AffineEnlargementStatement` and the slice-identity statement.
* `e2_timeSlice_energies`: both scale energies agree at **every real** endpoint (pointwise
  congruence of the integrands; no measurability or integrability is used). For `a ≤ 0` both
  sides integrate over the empty interval.
* `e2_timeSlice_statement : TimeSliceStatement`: the assembly, which ignores the locally Radon
  premises and reorders the family disjunction.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- **The shared slice identity** `e2_timeSlice_betaPow`. -/
theorem e2_timeSlice_betaPow : E2TimeSliceBetaPowStatement :=
  e2_timeSlice_betaPow_of_enlarge e2_affinePlane_enlarge

/-- Both slice energies equal their Euclidean counterparts at every real endpoint `a`. -/
theorem e2_timeSlice_energies (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (ν : Measure (Spatial n))
    (p : ℝ) (hp : 0 < p) (t₀ : ℝ) (T : FamilyKind) (hT : T = .horizontal ∨ T = .mixed)
    (x : Spatial n) (a : ℝ) :
    energyS (ν.map (fun y : Spatial n => point y t₀)) k T p a (point x t₀) =
        euclideanEnergyS ν k p a x ∧
      energyT (ν.map (fun y : Spatial n => point y t₀)) k T p a (point x t₀) =
        euclideanEnergyT ν k p a x := by
  have hβ := e2_timeSlice_betaPow n k hk hkn ν p hp t₀ T hT x
  refine ⟨?_, ?_⟩ <;> simp only [energyS, euclideanEnergyS, energyT, euclideanEnergyT, hβ]

/-- **E's time-slice conjunct** `TimeSliceStatement`, assembled from the shared identity. -/
theorem e2_timeSlice_statement : TimeSliceStatement := by
  intro n _ k hk hkn p hp ν _ _ t₀ T hT
  have hT' : T = .horizontal ∨ T = .mixed := hT.symm
  refine ⟨fun x r _ => e2_timeSlice_betaPow n k hk hkn ν p hp t₀ T hT' x r,
    fun a _ x => e2_timeSlice_energies n k hk hkn ν p hp t₀ T hT' x a, fun x => ⟨?_, ?_⟩⟩
  · exact iSup_congr fun a => (e2_timeSlice_energies n k hk hkn ν p hp t₀ T hT' x a).1
  · exact iSup_congr fun a => (e2_timeSlice_energies n k hk hkn ν p hp t₀ T hT' x a).2

end ParabolicRectifiability.Examples
