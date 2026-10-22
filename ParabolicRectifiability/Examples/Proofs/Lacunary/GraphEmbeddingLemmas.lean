import ParabolicRectifiability.Examples.Proofs.Lacunary.GraphEmbedding
import ParabolicRectifiability.Examples.Proofs.Lacunary.GraphEmbeddingStatements

/-! # The lacunary graph map is a measurable embedding

The theorem delegates to its corresponding proof
`e2_lacunaryGraphMap_measurableEmbedding_proof : E2LacunaryGraphEmbeddingStatement`
(prefix `e2_`).
-/

namespace ParabolicRectifiability.Examples

/-- **The lacunary graph map is a measurable embedding.**
Route: `lacunaryFunction ε a N` is `ε` times a `tsum` of continuous, hence measurable, functions;
`Measurable.tsum` (no summability
premise) and `Measurable.const_mul` make it measurable; `measurable_point`
composed with `EuclideanSpace.single 0` makes `F` measurable. The time
coordinate `g z = z.2.val` is measurable (`measurable_time`) and
`g (F t) = t`, so `F` is injective. Its range is `{z | F (g z) = z}`, measurable because the
diagonal of the second-countable Borel space `Space 1` is measurable (`measurableSet_eq_fun`).
Conclude with `MeasurableEmbedding.of_measurable_inverse`. -/
theorem e2_lacunaryGraphMap_measurableEmbedding : E2LacunaryGraphEmbeddingStatement := by
  exact e2_lacunaryGraphMap_measurableEmbedding_proof

end ParabolicRectifiability.Examples
