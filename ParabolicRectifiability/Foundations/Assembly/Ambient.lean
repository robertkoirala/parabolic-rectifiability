import ParabolicRectifiability.Foundations.Assembly.ProvedStatements

/-! # The ambient case `k = n + 2`

The ambient clauses are independent; each is the corresponding theorem
(`ambient_zero_graph_cover_all`, `ambient_rectifiable_iff_ac_iff_density`, and so on), except the
first clause `AmbientEnergyZeroStatement`, which
is the arbitrary-source statement with the two locally Radon hypotheses discarded.
-/

namespace ParabolicRectifiability.Foundations

/-- First clause, for a locally Radon source: the arbitrary-source statement applied to it. -/
theorem ambient_energy_zero_skeleton : AmbientEnergyZeroStatement :=
  fun n hn μ _ _ T hT => ambient_betaSq_squareEnergy_eq_zero n hn μ T hT

/-- Generalization of the first clause to an arbitrary measure. -/
theorem ambient_energy_zero_arbitrary_source_skeleton :
    AmbientEnergyZeroArbitrarySourceStatement :=
  ambient_betaSq_squareEnergy_eq_zero

/-- Second clause: the zero-graph cover. -/
theorem ambient_zero_graph_cover_skeleton : AmbientZeroGraphCoverStatement :=
  ambient_zero_graph_cover_all

/-- Third clause: the ambient characterization. -/
theorem ambient_characterization_skeleton : AmbientCharacterizationStatement :=
  ambient_rectifiable_iff_ac_iff_density

/-- Fourth clause: differentiation with respect to volume. -/
theorem ambient_absolutely_continuous_density_skeleton :
    AmbientAbsolutelyContinuousDensityStatement :=
  ambient_densities_pos_finite_of_ac_volume

/-- Fifth clause: the ambient core with zero remainder. -/
theorem ambient_local_core_skeleton : AmbientLocalCoreStatement :=
  ambient_local_core_bounds

end ParabolicRectifiability.Foundations
