import ParabolicRectifiability.Characterization.Statements.Branches
import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.Criterion
import ParabolicRectifiability.Characterization.Proofs.GraphSource.SquareFiniteness
import ParabolicRectifiability.Characterization.Assembly.Branches

/-! # Reusable branches of the qualitative characterization

The theorems here prove the branch statements of the characterization
(`FiniteHausdorffCriterionStatement` and its companions): the finite-Hausdorff criterion, intrinsic-source sufficiency, arbitrary-source finiteness
on a graph, necessity, and typed refinements. The finite-Hausdorff criterion tests
`H_P^k⌊E`; the intrinsic and graph-source results test the original ambient source.
The latter conclusion is Hausdorff-almost everywhere on the graph, even when source mass
is concentrated on a Hausdorff-null subset.

`exists_typed_refinement_set` and `exists_typed_refinement_measure` choose their Borel typed
pieces before the tolerance; these refinements do not assert canonical uniqueness.
The proofs are `intrinsic_sufficiency_skeleton`, `necessity_skeleton`, the typed refinements
`typed_refinement_set_skeleton` and `typed_refinement_measure_skeleton`, and the
finite-Hausdorff and graph-source results `b4_finite_hausdorff_criterion` and
`b2_graph_source_square_finite`.
-/

namespace ParabolicRectifiability.Characterization

/-- For Borel `E` of finite `H_P^k` measure, square finiteness for the restricted source
`η = H_P^k⌊E` at one positive endpoint implies typed set rectifiability at every positive
tolerance. The ambient clause supplies one zero-norm full vertical graph containing every
set when `k = n + 2`. -/
theorem isRegularlyRectifiableSet_of_finite_hausdorff : FiniteHausdorffCriterionStatement := by
  exact ParabolicRectifiability.Characterization.b4_finite_hausdorff_criterion

/-- **Intrinsic sufficiency.** A locally Radon `μ ≪ H_P^k` with a Borel sigma-finite
`H_P^k` carrier and finite square energy `μ`-a.e. at one positive endpoint is carried, at
every positive tolerance, by countably many typed graphs. -/
theorem hasTypedMeasureCover_of_intrinsic : IntrinsicSufficiencyStatement := by
  exact ParabolicRectifiability.Characterization.intrinsic_sufficiency_skeleton

/-- An arbitrary locally Radon ambient source has finite own-type square energy
`H_P^k`-almost everywhere on each individual finite-norm graph, for every positive
endpoint. Horizontal
domains may be arbitrary subsets; vertical graphs are full general regular graphs.
The exceptional set is Hausdorff-null, with no assertion that it has zero source mass. -/
theorem hausdorffP_graph_squareEnergy_eq_top_eq_zero : GraphSourceStatement := by
  exact ParabolicRectifiability.Characterization.b2_graph_source_square_finite

/-- A locally Radon regularly rectifiable measure has a Borel sigma-finite Hausdorff
carrier, positive finite lower and upper densities, and finite full-source mixed and
own-family energies. On one common full-measure set this holds at every positive
endpoint. -/
theorem regularlyRectifiableMeasure_necessity : NecessityStatement := by
  exact ParabolicRectifiability.Characterization.necessity_skeleton

/-- **Typed refinement, set version.** A Borel set of finite `H_P^k` measure with finite
mixed square energy splits once into disjoint Borel horizontal and vertical pieces, each
covered by graphs of its own type at every positive tolerance and with finite own-type
square energy. -/
theorem exists_typed_refinement_set : TypedRefinementSetStatement := by
  exact ParabolicRectifiability.Characterization.typed_refinement_set_skeleton

/-- **Typed refinement, measure version.** A locally Radon regularly rectifiable measure
splits once into disjoint Borel horizontal and vertical source pieces whose restrictions are
carried by graphs of their own type at every positive tolerance, with finite own-type square
energy of the original measure. -/
theorem exists_typed_refinement_measure : TypedRefinementMeasureStatement := by
  exact ParabolicRectifiability.Characterization.typed_refinement_measure_skeleton

end ParabolicRectifiability.Characterization
