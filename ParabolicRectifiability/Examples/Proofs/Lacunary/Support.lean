import ParabolicRectifiability.Examples.Lacunary

/-! # Lacunary graph: two auxiliary facts

Two elementary facts about the lacunary graph used by several proofs of the lacunary estimates:

* `e2_isometry_time_of_dist`: a map `G : ℝ → Y` with `dist (G t) (G s) = √|t-s|` for all
  `t, s` is an isometry when read on snowflaked time, `fun τ : Time => G τ.val`. It is applied to
  `G = lacunaryGraphMap ε a N` for the exact Hausdorff identity; continuity of `G` follows by
  composing with the snowflake homeomorphism:
  `(e2_isometry_time_of_dist h).continuous.comp Metric.Snowflaking.continuous_toSnowflaking :
  Continuous G`, then `.measurable`.
* `e2_lacunarySource_univ`: the total mass of a restricted source, `ν_E(X) = |E|`, for a
  measurable graph map (the same statement as `Examples.lacunarySource_univ`). It gives the mass
  clause `ν_E univ = ν_{E₀}(G)` of the restriction carried by a regular graph.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Examples

/-- **The snowflake isometry adapter.** If `dist (G t) (G s) = √|t - s|` for
all real `t, s`, then `τ ↦ G τ.val` is an isometry from `Time = (ℝ, √|t-s|)`. -/
theorem e2_isometry_time_of_dist {Y : Type*} [PseudoMetricSpace Y] {G : ℝ → Y}
    (h : ∀ t s : ℝ, dist (G t) (G s) = Real.sqrt |t - s|) :
    Isometry (fun τ : Time => G τ.val) := by
  refine Isometry.of_dist_eq fun τ σ => ?_
  obtain ⟨t⟩ := τ
  obtain ⟨s⟩ := σ
  show dist (G t) (G s) =
    dist (Metric.Snowflaking.toSnowflaking t : Time) (Metric.Snowflaking.toSnowflaking s)
  rw [h, Metric.Snowflaking.dist_toSnowflaking_toSnowflaking, Real.dist_eq, Real.sqrt_eq_rpow]

/-- **Total mass of a restricted source.** For a measurable graph map, `ν_E(X) = |E|`
(the same statement as `Examples.lacunarySource_univ`). -/
theorem e2_lacunarySource_univ {ε : ℝ} {a : ℕ → ℝ} {N : ℕ → ℕ}
    (hF : Measurable (lacunaryGraphMap ε a N)) (E : Set ℝ) :
    lacunarySource ε a N E univ = volume E := by
  rw [lacunarySource, Measure.map_apply hF MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ]

end ParabolicRectifiability.Examples
