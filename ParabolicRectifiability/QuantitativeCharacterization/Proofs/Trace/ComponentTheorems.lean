import ParabolicRectifiability.QuantitativeCharacterization.Statements.TraceComponents
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Trace.InfiniteMultiplicityNull
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Trace.TraceCarriage
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Trace.RestrictCarrierRectifiable

/-! # Trace statements for quantitative mixed rectifiability: proofs

Each declaration below delegates to the corresponding proof module, imported above. Their types
are the `dp2_…Statement` propositions.

* `dp2_infinite_multiplicity_null`: the set of points of infinite multiplicity is `H_P^k`-null;
* `dp2_trace_carriage`: almost every point of the root lies on a trace `P_i ∩ Γ_i`;
* `dp2_restrict_carrier_rectifiable`: reference-null transfer.

The three statements are independent of each other; they are combined in
`dp2_qmr_rectifiable_of_reference_covers`.
-/

set_option autoImplicit false

noncomputable section

namespace ParabolicRectifiability.QuantitativeCharacterization

/-- **Infinite multiplicity is null** (`dp2_InfiniteMultiplicityNullStatement`). Root packing gives
`Σ_i R_i^k < ∞`, hence `H_P^k(limsup_i P_i) = 0`. The argument uses Hausdorff tail covers, not an
estimate for `Σ_i μ(P_i)`.

Proof sketch. Put `S = {z | 𝒞.multiplicity z = ⊤}` (`multiplicity` is the `encard` of
`{i | z ∈ P_i}`; it is `⊤` exactly when that set is infinite).
1. `𝒞.root_packing` gives `Σ' i, ofReal (R_i) ^ k ≤ ofReal (K R^k) < ⊤`, so the tails
   `Σ_{i ∉ F} ofReal (R_i)^k → 0` along finite `F` (`ENNReal.tendsto_tsum_compl_atTop_zero`) and,
   since `k ≥ 1`, all but finitely many `R_i` are below any `δ > 0`.
2. For every finite `F ⊆ index`, `S ⊆ ⋃_{i ∉ F} P_i`.
3. `hausdorffP n k = μH[(k : ℝ)]`; apply
   `MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum` along finite sets `F` with the covers
   `{P_i : i ∉ F}`, `diam P_i ≤ 2 R_i` (`EMetric.diam_ball`-type bound), so
   `μH[k] S ≤ 2^k liminf_F Σ_{i ∉ F} R_i^k = 0` (rpow to pow: `ENNReal.rpow_natCast`).
If `index` is finite, `S = ∅`.

It is used in `dp2_root_rectifiable`, with `μ ≪ H_P^k` from the `(K,L)` property. -/
theorem dp2_infinite_multiplicity_null : dp2_InfiniteMultiplicityNullStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.dp2_infinite_multiplicity_null_proof

/-- **Trace carriage** (`dp2_TraceCarriageStatement`): where the multiplicity is finite, almost
every point of the root lies on a trace `P_i ∩ Γ_i`. It uses the fields `bad_bound`, `cover_null`,
`scaleSet_cover`, `ball_meets_carrier`, `measurable_badSet` of `RegularMixedCovering`.

Proof sketch.
1. Fubini on the bad set: `pointScaleMeasure μ 𝓑 = ∫⁻ z, scaleMeasure (𝓑_z) dμ`
   (`Measure.prod_apply`, `𝓑` Borel, `scaleMeasure` s-finite) is at most `ofReal (K R^k) < ⊤`,
   so `scaleMeasure (𝓑_z) < ⊤` for `μ`-a.e. `z` (`ae_lt_top`).
2. Fubini on `cover_null` (`Measure.measure_prod_null`; the set is Borel since `index ⊆ ℕ` is
   countable and `damb_measurableSet_rootPairs`): for
   `μ`-a.e. `z ∈ P(a,R) ∩ supp μ`, `scaleMeasure`-a.e. `r ∈ (0,R)` has `(z,r) ∈ 𝓑 ∪ ⋃_i 𝓤_i`.
   Points of `P(a,R) \ supp μ` are `μ`-null (`Measure.measure_compl_support_of_innerRegular`).
3. Fix such a `z` with finite multiplicity (hypothesis) off every trace `P_i ∩ Γ_i`. Each
   carrier is closed (horizontal: a support, `Measure.isClosed_support`; vertical:
   `ba1_vertical_basic_proof`, needs `1 ≤ L`;
   ambient: `univ`) and nonempty (`ball_meets_carrier`), so for the finitely many `i` with
   `z ∈ P_i`, `infDist z Γ_i > 0`. Let `δ` be `L⁻¹` times their minimum (`δ = R` if there are
   none). For `0 < r < min δ R`, `(z,r) ∉ 𝓤_i` for every `i` (`scaleSet_cover`: `z ∈ P_i` and
   `L⁻¹ dist(z,Γ_i) ≤ r`), so `(0, min δ R) ⊆ 𝓑_z` up to a `scaleMeasure`-null set.
4. `scaleMeasure (Ioo 0 c) = ⊤` for `c > 0` (dyadic shells of mass `log 2`,
   `scaleMeasure_Ioo_two_mul`, or
   `bf1m45_scaleMeasure_Ioo`), contradicting 1.

It is used in `dp2_root_rectifiable` and in the typed split of the approximants. -/
theorem dp2_trace_carriage : dp2_TraceCarriageStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.dp2_trace_carriage_proof

/-- **Reference-null transfer** (`dp2_RestrictCarrierRectifiableStatement`). Covering the carrier
modulo the reference measure is equivalent, by Ahlfors-David regularity, to covering it modulo
`H_P^k`; absolute continuity of `μ` transfers these exceptional sets.

Proof sketch.
1. `Characterization.b2_reference_adr_square n hn k hk hkn L hL` gives `c, C` with
   `IsADRCarrier k c C ρ.carrier ρ.measure` for every `L`-reference `ρ`.
2. `Characterization.b2_adr_hausdorff_comparison_proof k c C` gives `b` with
   `H_P^k(S ∩ Γ) ≤ b σ(S)` for every set `S`.
3. Split on `ρ` (horizontal, vertical, ambient; `ρ.kind` is `.horizontal` or `.vertical`), take
   the cover `⟨I, G, hG⟩` with `σ(Uᶜ) = 0`, `U` the union of the graph images. Then
   `H_P^k(Uᶜ ∩ Γ) = 0`, so `μ(Uᶜ ∩ Γ) = 0`, and `(μ⌊Γ)(Uᶜ) = μ(Uᶜ ∩ Γ)`
   (`Measure.restrict_apply'`, `Γ` closed by `IsADRCarrier.isClosed`). Carrier with the constant
   norm `fun _ => 1`.
4. `μ⌊Γ ≪ μ ≪ H_P^k` (`Measure.absolutelyContinuous_of_le Measure.restrict_le_self`).

It is used in `dp2_root_rectifiable`, and it also gives the typed rectifiability of the
approximants. -/
theorem dp2_restrict_carrier_rectifiable : dp2_RestrictCarrierRectifiableStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.dp2_restrict_carrier_rectifiable_proof

end ParabolicRectifiability.QuantitativeCharacterization
