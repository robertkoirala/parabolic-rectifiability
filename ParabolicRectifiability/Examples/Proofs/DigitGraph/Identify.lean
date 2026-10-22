import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements

/-! # The digit graph source is restricted Hausdorff measure

The graph source satisfies `μ = H¹⌊E` and `H¹(E) = 1` (`e2_sb_identify_proof`): the first
coordinate projection is `1`-Lipschitz and inverts `T`, so `μ ≤ H¹⌊E`, and both measures have
total mass at most one while `μ` is a probability. Projection images are
used as arbitrary sets; their measurability is not needed for outer measure bounds. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Examples
open ParabolicRectifiability.BetaP (Plane)

private theorem horizontal_projection_lipschitz :
    LipschitzWith 1 (fun z : Plane => z 0) := by
  intro x y
  simpa using (PiLp.edist_apply_le x y (0 : Fin 2))

/-- Exact identification from Borel measurability and the cylinder upper bound. -/
theorem e2_sb_identify_proof (hM : E2sbMeasurable) (hC : E2sbCover) :
    E2sbIdentify := by
  have htotal : e2_sbSource univ = 1 := by
    rw [e2_sbSource, Measure.map_apply hM.2.2 MeasurableSet.univ]
    simp [Real.volume_Ico]
  have hle : e2_sbSource ≤ μH[1].restrict e2_sbSet := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [e2_sbSource, Measure.map_apply hM.2.2 hA,
      Measure.restrict_apply (hM.2.2 hA), Measure.restrict_apply hA]
    calc
      volume (e2_sbGraph ⁻¹' A ∩ Ico 0 1) ≤
          volume ((fun z : Plane => z 0) '' (A ∩ e2_sbSet)) := by
        apply measure_mono
        intro x hx
        refine ⟨e2_sbGraph x, ⟨hx.1, ?_⟩, ?_⟩
        · exact subset_closure ⟨x, hx.2, rfl⟩
        · simp [e2_sbGraph]
      _ = μH[1] ((fun z : Plane => z 0) '' (A ∩ e2_sbSet)) := by
        rw [hausdorffMeasure_real]
      _ ≤ μH[1] (A ∩ e2_sbSet) := by
        simpa using horizontal_projection_lipschitz.hausdorffMeasure_image_le
          (d := 1) (by norm_num) (A ∩ e2_sbSet)
  have hmass : μH[1] e2_sbSet = 1 := by
    apply le_antisymm hC.2
    simpa [htotal] using hle univ
  have : IsFiniteMeasure e2_sbSource := ⟨by rw [htotal]; exact ENNReal.one_lt_top⟩
  have heq : e2_sbSource = μH[1].restrict e2_sbSet :=
    Measure.eq_of_le_of_measure_univ_eq hle (by simp [htotal, hmass])
  exact ⟨heq.symm, hmass⟩

end ParabolicRectifiability.Examples
