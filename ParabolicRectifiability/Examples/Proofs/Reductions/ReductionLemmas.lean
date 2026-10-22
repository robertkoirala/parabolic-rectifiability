import ParabolicRectifiability.Examples.Proofs.Reductions.ReductionStatements
import ParabolicRectifiability.Examples.Proofs.StationaryGraphs.OrthogonalExtension
import ParabolicRectifiability.Examples.Proofs.StationaryGraphs.Assembly
import ParabolicRectifiability.Examples.Proofs.StationaryGraphs.Horizontal
import ParabolicRectifiability.Examples.Proofs.StationaryGraphs.Length
import ParabolicRectifiability.Examples.Proofs.StationaryGraphs.Vertical
import ParabolicRectifiability.Examples.Proofs.StationaryGraphs.TimeIndependentHalfTime

/-! # Statements of the stationary reductions

Each statement is proved by the corresponding module.
-/

namespace ParabolicRectifiability.Examples

/-- **Interval length.** Route: `Real.volume_Ioo`,
`Ioo ∩ Icc` is an interval with endpoints `max (t - r²) (-1)`, `min (t + r²) 1`; lower bound by
cases `r² ≤ 2` (length `≥ r²`, attained at `t = ±1`) and `2 ≤ r² ≤ 4` (length `≥ 2 ≥ r²/2`);
upper bound `≤ |Ioo| = 2r²`. -/
theorem e2_stationary_length : E2StationaryLengthStatement := by
  exact e2_stationary_length_proof

/-- **Vertical identity.** Route: for a vertical
model `V × ℝ` (spatial rank `m`, `VerticalModel.rank_eq`), `modelCost` at `point y s` is
`dist(y,V)²` (`VerticalModel.modelCost_point`); push the
product through `lintegral_map` and Tonelli (`lintegral_prod`, `SFinite ν` from
`IsFiniteMeasureOnCompacts` on the σ-compact `Spatial n`), the ball preimage is
`B(x,r) × (t-r², t+r²)` (`mem_ball_point`), so `fit = ℓ ∫_{B(x,r)} dist(y,V)² dν`. Reindex
`VerticalModel n (m+2)` by `AffineSpatialPlane n m` (`spatialRank = m` from `rank_eq`) and pull the
finite nonzero `ℓ` out of the infimum (`ENNReal.mul_iInf_of_ne`); normalizations:
`r^{-(m+4)} ℓ = (ℓ/r²) r^{-(m+2)}` (`ENNReal.rpow_natCast`, `ofReal r ≠ 0, ⊤`). -/
theorem e2_stationary_vertical : E2StationaryVerticalStatement := by
  exact e2_stationary_vertical_proof

/-- **Horizontal lower bound.** Implication form
over the interval length. Route: horizontal `modelCost (point y s) ≥ |s - τ|` (`HorizontalModel.modelCost_point`); Tonelli as in `E2StationaryVerticalStatement`; `∫_J |s - τ| ds ≥ ℓ²/4` for an interval
`J` of length `ℓ` (minimized at the midpoint); `ℓ ≥ r²/2` (`E2StationaryLengthStatement`), so
`β²_H ≥ r^{-(m+4)} ν(B) ℓ²/4 ≥ r^{-m} ν(B)/16`; and `b^E ≤ r^{-m} ν(B)` by an `m`-plane through
`x` (`AffineSpatialPlane.exists_mem_of_nonempty`, `m ≤ n`; `infEDist ≤ edist < r`). An empty
horizontal family (`m + 2 > n`) gives `β²_H = ⊤`. -/
theorem e2_stationary_horizontal : E2StationaryHorizontalStatement := by
  exact e2_stationary_horizontal_proof

/-- **Assembly of the stationary comparisons.**
Implication form over the interval length, the vertical identity and the horizontal lower bound. Route: clause 1 is `E2StationaryVerticalStatement`; the mixed square is
`min(β²_H, β²_V)` (`betaSq_of_pos`, `iInf_sum` over `HorizontalModel ⊕ VerticalModel`, monotone
multiplication); lower: `(1/16) b^E ≤ β²_H` (`E2StationaryHorizontalStatement`) and `(1/16) b^E ≤ (1/2) b^E ≤ (ℓ/r²) b^E = β²_V`
(`E2StationaryLengthStatement`, `E2StationaryVerticalStatement`); upper: `β²_mixed ≤ β²_V = (ℓ/r²) b^E ≤ 2 b^E` (`betaSq_mixed_le_vertical`; interval length). -/
theorem e2_stationary_assembly : E2StationaryAssemblyStatement := by
  exact e2_stationary_assembly_proof

/-- **Orthogonal Lipschitz extension.** Route:
an orthonormal basis of `W^⊥` (`stdOrthonormalBasis`, `finrank W^⊥ = n - dim W` by
`Submodule.finrank_add_finrank_orthogonal`, `finrank_euclideanSpace_fin`); each coordinate of
`g` is `L`-Lipschitz on `E ⊆ W`; extend each by McShane (`LipschitzOnWith.extend_real`), assemble
with the basis; the Euclidean norm gives `√(n - dim W) L`. `E = ∅`: the zero map. -/
theorem e2_orthogonalExtension : E2OrthogonalExtensionStatement := by
  exact e2_orthogonalExtension_proof

/-- **Zero half-time derivative of time-independent functions.**
Route, per orthonormal normal component `G_i(u,t) = h_i(u)` (`normalFourierComponent`), through an internal **weighted-cancellation helper**: for a
continuous `a : ℝ^m → ℂ` and a compactly supported Schwartz test `ψ`,
`a(u) K_ψ(u,t) ∈ L¹` and `∫ a(u) K_ψ(u,t) du dt = 0`, where `K_ψ = testKernel ψ`.
Total mean zero of `K_ψ` alone does **not** imply this weighted cancellation. Proof of the helper:
`K = spatialTestSupport ψ` is compact (`isCompact_spatialTestSupport`) and `K_ψ` vanishes off `K × ℝ`
(`testKernel_eq_zero_of_notMem_spatialTestSupport`), so `a` may be replaced by `1_K a`,
bounded and invariant under time translation; integrability by
`integrable_bounded_mul_testKernel`; cancellation by multiplying the integrable
difference-kernel integrand (`fcond_integrable_testKernelIntegrand_prod`) by this factor, then Fubini and time-translation
invariance. No smoothness of `a ψ` is needed. With `a = h_i` (Lipschitz, hence continuous) and
`ψ` the real compact test, transfer to `|D_t|^{1/2}φ` (`testKernel_ae_halfTimeDeriv`) and apply ordered Fubini (`fcond_ordered_of_integrable`) for the three ordered clauses with limit `0 = ∫ 0 · φ`. The affine-only
`b2aff_affine_ordered` is a model
argument, not a theorem for arbitrary Lipschitz `h`. BMO: the zero function, `0 ≤ 0`,
average `0`. -/
theorem e2_timeIndependent_halfTime : E2TimeIndependentHalfTimeStatement := by
  exact e2_timeIndependent_halfTime_proof

end ParabolicRectifiability.Examples
