import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Boxes.Grid
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Boxes.Geometry
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Boxes.Maximal
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Boxes.Overlap

/-! # Parabolic dyadic grid and Whitney boxes

Three geometric statements about the Whitney boxes of the regular trace extension:

* `parabolicDyadicBox_geometry_proof`: partition, nesting, parent, volume,
  measurability, inner and outer balls, child–parent center bound
  (`WhitneyBoxes.Grid`, `WhitneyBoxes.Geometry`);
* `exists_whitneyBoxes_data_proof`: the maximal eligible boxes of a compact
  nonempty `F₀` form Whitney data, with the upper distance bounds and center separation
  (`WhitneyBoxes.Maximal`);
* `whitneyBoxes_enlarged_overlap_proof`: comparable scales, bounded overlap,
  local finiteness and avoidance of `F₀` for the `3/2`-enlargements
  (`WhitneyBoxes.Overlap`).
-/
