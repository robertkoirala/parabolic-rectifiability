import ParabolicRectifiability.BetaP.Proofs.Laws.Annulus
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.Rows.RescaledCarrier
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.Rows.UniformTails
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.Rows.ZeroBase
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.Rows.SqueezeLimit
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.RowStatements

/-! # Auxiliary results for the `S_p` and `T_p` examples

This module proves four of the statements `C2…Statement`: `c2_zeroBase_carried`,
`c2_squeeze_limit`, `c2_uniform_tails` and `c2_rescaled_carrier_null`, and records
`c2_input_betaPowAnnulus`, the finite-annulus law `BetaPowAnnulusStatement`, proved by
`c2_betaPowAnnulus_proof`. The other statements are proved in `c2_timeSlice_measure`,
`c2_tpAbove_endpoint` and `c2_rescaled_mass`. The arguments are assembled in
`c2_spBelowTwo_notSufficient_of_witness` and the theorems built on `c2_tpAboveTwo_notSufficient_of`.

Each result depends only on named statements and previously proved declarations, not on another
result of this module.
-/

namespace ParabolicRectifiability.BetaP

/-! ## Input statement -/

/-- **Finite-annulus law for `B_p`**: `BetaPowAnnulusStatement`, proved by
`c2_betaPowAnnulus_proof`. It is used by `c2_tpAbove_endpoint`, hence by
`c2_tpAboveTwo_notSufficient_of_witness`. -/
theorem c2_input_betaPowAnnulus : BetaPowAnnulusStatement := by
  exact c2_betaPowAnnulus_proof

/-! ## The auxiliary statements -/

/-- **One rank-zero regular graph carries the source** (`C2ZeroBaseCarriedStatement`).

Proof: build `G : GeneralRegularVerticalGraph 1 2 η` with `vertical_dimension := le_rfl`,
`direction := Examples.zeroDirection` (`⊥`), `rank_eq` from `finrank_bot`, `offset := 0`,
`function := Examples.zeroBaseLift g`, `regular :=` the hypothesis. For `p : SubspaceSpace ⊥ =
⊥ × Time`, `(p.1 : Spatial 1) = 0` (`Submodule.mem_bot`), so `G.map p = point (single 0 (g p.2.val))
p.2.val` (`point`; `Examples.zeroBaseLift`); every `t` is hit by
`(0, toSnowflaking t)`. Hence `G.image = range (fun t => point (single 0 (g t)) t)`. Carrier: `I = ∅`
(empty horizontal family, `HorizontalGraph` index elimination by `Set.mem_empty_iff_false`),
`J = {0}` (or `univ`) with the constant family `G`; `⋃` over the empty index is `∅`, over a
nonempty constant family is `G.image`. -/
theorem c2_zeroBase_carried : C2ZeroBaseCarriedStatement := by
  exact c2_zeroBase_carried_proof

/-- **Squeezed limit of a vanishing remainder function** (`C2SqueezeLimitStatement`), used for
both remainder failures of `T_p`.

Proof: `C ε^p → 0` as `ε → 0⁺` (`Real.continuousAt_rpow_const`/`tendsto_rpow_atTop`-type facts, or
`Real.rpow_le_rpow_left_iff`; `p > 0`), so `g → 0` along `𝓝[>] 0` by squeezing
(`tendsto_of_tendsto_of_tendsto_of_le_of_le'` on `𝓝[>] 0` restricted to `(0, ε₀]`), and in fact
`Tendsto g (𝓝[>] 0) (𝓝[>] 0)` (`tendsto_nhdsWithin_iff`, `g > 0` eventually). Compose with `Φ`:
`Φ (g ε) → 0`, so eventually `Φ (g ε) < c` (`gt_mem_nhds`); intersect with `ε ∈ (0, ε₀]`
(`Ioc_mem_nhdsGT`) and take a point (`Filter.Eventually.exists`, `𝓝[>] 0` is `NeBot`). -/
theorem c2_squeeze_limit : C2SqueezeLimitStatement := by
  exact c2_squeeze_limit_proof

/-- **Egorov with compact inner approximation** (`C2UniformTailsStatement`).

Proof: put `f_m(y) = energyS ω k T p (1/(m+1)) y`. Measurability: `ω` is finite, hence finite on
compacts and inner regular (instances), and the measurability law
`cfit_betaPowMeasurability_proof` makes each `f_m` measurable. Pointwise: for `y ∈ A`,
`f_m(y) ↓ 0` because `S_p^1(y) < ∞` and `⋂_m Ioo 0 (1/(m+1)) =
∅` (`tendsto_measure_iInter_atTop` for the finite measure `B_p^{2/p} dr/r` restricted to `Ioo 0 1`,
or `MeasureTheory.tendsto_setLIntegral_of_antitone`). Work with the real parts `(f_m y).toReal`
(finite on `A`). Egorov `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto'` (finite measure) with
`δ = ω(A)/2` gives a measurable `S`, `ω(S) ≤ δ`, with uniform convergence off `S`; then
`ω(A' \ S) > 0` for a measurable `A' ⊆ A` of full measure (`toMeasurable` of `Aᶜ`), and inner
regularity (`MeasurableSet.exists_isCompact_lt_add` or `InnerRegular`) gives compact
`K ⊆ A' \ S` with `ω(K) > 0`. For `M > 0` take `m₀` from uniform convergence and
`h = 1/(m₀+1)`. -/
theorem c2_uniform_tails : C2UniformTailsStatement := by
  exact c2_uniform_tails_proof

/-- **Rescaled carrier nullity** (`C2RescaledCarrierNullStatement`).

Proof: with `S = similarity q R hR` (a homeomorphism), `rescaledSource (H⌊A) 1 q R hR K =
R⁻¹ · H((S⁻¹' K) ∩ A)` (`Measure.smul_apply`, `Measure.map_apply` with `K` closed,
`Measure.restrict_apply`). Write `N = K \ ⋃ G_i.image`; `S⁻¹' K ⊆ ⋃_i S⁻¹'(G_i.image) ∪ S⁻¹' N`.
Each `S⁻¹'(G_i.image) = S.symm '' G_i.image` is the image of the horizontal graph
`Foundations.fsimb5_horizontalGraph q R hR (G i)` of the same slope
(`fsimb5_horizontalGraph_image`), so `H(S⁻¹'(G_i.image) ∩ A) = 0` by hypothesis;
`H(S⁻¹' N) = R · H(N) = 0` (`Foundations.fsim_hausdorffP_preimage_similarity_proof`). Countable
subadditivity (`measure_iUnion_null`, `measure_union_null`). -/
theorem c2_rescaled_carrier_null : C2RescaledCarrierNullStatement := by
  exact c2_rescaled_carrier_null_proof

end ParabolicRectifiability.BetaP
