import ParabolicRectifiability.Examples.Proofs.Reductions.ReductionLemmas
import ParabolicRectifiability.Examples.Proofs.Reductions.TimeSlice

/-! # Assembly of the stationary reductions

* `e2_stationaryProduct : StationaryProductStatement`, from the four stationary-product
  statements (`E2StationaryLengthStatement`, `E2StationaryVerticalStatement`,
  `E2StationaryHorizontalStatement`, `E2StationaryAssemblyStatement`).
* `e2_stationaryGraphExtension : StationaryGraphExtensionStatement`: the extension
  (`E2OrthogonalExtensionStatement`), its parabolic Lipschitz bound
  (`LipschitzWith.prod_fst`: `‖u - v‖ ≤ d_P((u,t),(v,s))`), the zero derivative data
  (`E2TimeIndependentHalfTimeStatement`), the general regular predicate with
  `L' = √(n-m) L`, `B = 0`, and the full graph with direction `W`, offset `0`, function
  `(u,t) ↦ g'(u)`, whose image is the stated range.
* `e2_reductions` has exactly the type of `reductions_bundle`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- **The stationary product** -/
theorem e2_stationaryProduct : StationaryProductStatement :=
  e2_stationary_assembly e2_stationary_length e2_stationary_vertical e2_stationary_horizontal

/-- **The stationary graph extension** -/
theorem e2_stationaryGraphExtension : StationaryGraphExtensionStatement := by
  intro n _ W _ E g L hg
  obtain ⟨g', hext, hlip⟩ := e2_orthogonalExtension n W E g L hg
  have hlipP : LipschitzWith (NNReal.sqrt ((n - Module.finrank ℝ W : ℕ) : ℝ≥0) * L)
      (fun q : SubspaceSpace W => g' q.1) := by
    have h := hlip.comp
      (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : SubspaceSpace W → W))
    rwa [mul_one] at h
  obtain ⟨hrep, hbmo⟩ := e2_timeIndependent_halfTime n W g' _ hlip
  have hreg : IsGeneralRegularVerticalFunction W (fun q : SubspaceSpace W => g' q.1)
      ((NNReal.sqrt ((n - Module.finrank ℝ W : ℕ) : ℝ≥0) * L : ℝ≥0) : ℝ) :=
    ⟨fun _ => 0, NNReal.sqrt ((n - Module.finrank ℝ W : ℕ) : ℝ≥0) * L, 0, hlipP,
      by simpa using hbmo, hrep, by simp⟩
  refine ⟨g', hext, hlip, hlipP, hrep, hbmo, hreg, ?_⟩
  refine ⟨{ vertical_dimension := Nat.le_add_left 2 _
            direction := W
            rank_eq := rfl
            offset := 0
            function := fun q => g' q.1
            regular := hreg }, ?_⟩
  show Set.range (fun p : SubspaceSpace W =>
      ((0 : Spatial n) + (p.1 : Spatial n) + (g' p.1 : Spatial n), p.2)) = _
  simp only [zero_add]

/-- **The reductions bundle**: exactly the type of `reductions_bundle`. -/
theorem e2_reductions : ReductionsStatement :=
  ⟨e2_timeSlice_statement, e2_timeSlice_tube, e2_stationaryProduct, e2_stationaryGraphExtension⟩

end ParabolicRectifiability.Examples
