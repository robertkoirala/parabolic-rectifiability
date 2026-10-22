import ParabolicRectifiability.Analysis.TraceExtension.Reservoirs.Sets
import ParabolicRectifiability.Analysis.TraceExtension.Reservoirs.Allocation

/-! # Reservoirs and the Whitney source allocation

Collects the two results that produce the source data of the regular trace extension:

* `exists_reservoir_sets_proof`: robust reservoir sets inside a ball of large source
  mass, from the geometry in `Reservoirs.frame_lower_bound` and its companions (robust
  frames, matrix perturbation, slab volume, heavy grid cells, tube-avoiding selection,
  barycenter bounds);
* `exists_whitney_source_allocation_proof`: simultaneous allocation of the source to all
  Whitney holes, with finite real-capacity transport and weak compactness of bounded
  densities as leading hypotheses.
-/
