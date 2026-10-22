import ParabolicRectifiability.QuantitativeCharacterization.Statements.PiecesComponents
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Pieces.SharpChart
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Pieces.HorizontalReferenceCover
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Pieces.VerticalReference
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Pieces.DisjointRestrictions
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Pieces.OneReferenceCertificate
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Pieces.PiecesAssembly

/-! # Countable quantitative pieces: proofs of the auxiliary statements

Each declaration below delegates to the corresponding proof module, imported above. Their types
are the `dp2_…Statement` propositions.

Statements that need another one take it as a hypothesis (implication form), so that no proof
imports another's file: the horizontal references take the sharp chart; the pieces assembly takes
the horizontal references, vertical references, disjoint restrictions and one-reference
certificate. They are combined in `dp2_countable_pieces_of_typed_covers`.
-/

set_option autoImplicit false

noncomputable section

namespace ParabolicRectifiability.QuantitativeCharacterization

/-- **The sharp horizontal chart** (`dp2_SharpChartStatement`). A sharper companion to
`b2chart_bilip` is enough.

Proof sketch: copy the construction of `Characterization.b2chart_explicit_constant` at `ε = 1`:
`e = b2chart_coords G`, the normal extension `g'` from `b2chart_exists_normal_extension` with
`K = Real.toNNReal |1| = 1` and `Foundations.bf1genv1_normal_lipschitz G`, so
`‖g' x - g' y‖ ≤ √n ‖x - y‖`; `F v = offset + e⁻¹ v + g'(e⁻¹ v)`, `D = e '' G.domain`,
`τ = time ∘ e⁻¹` on `D`. Replace `b2chart_bilip` by its Pythagorean companion: `x - y ∈ U`
and `g' x - g' y ∈ Uᗮ` are orthogonal (`Submodule.inner_right_of_mem_orthogonal`), so
`‖(x - y) + (g' x - g' y)‖² = ‖x - y‖² + ‖g' x - g' y‖² ≤ (1 + n) ‖x - y‖²`
(`norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`), and `≥ ‖x - y‖²`; distances transfer by
`b2chart_norm_symm_sub`. Trace: `Foundations.bf1genv1_time_bound` at `ε = 1`. -/
theorem dp2_sharp_chart : dp2_SharpChartStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.dp2_sharp_chart_proof

/-- **Horizontal references.** Implication form over the sharp chart:
`dp2_SharpChartStatement → dp2_HorizontalReferenceCoverStatement`.

Proof sketch (template: `Characterization.b2_horizontal_graph_reference`):
1. `Characterization.b2_horizontal_compact_cover_proof n k 1 G`: `J`, graphs `Gc j` of
   slope `1` with nonempty compact domains, `H_P^k(G.image \ ⋃ j, (Gc j).image) = 0`.
2. `k ≤ n` from `G.rank_eq` and `Submodule.finrank_le` (as in the template).
3. For each `j`, the sharp chart gives `F, D, τ`; with `L_* = max 2 √(1+n) ≥ 2 ≥ 1` and
   `√(1+n) ≤ L_*`, weaken to `dist u v ≤ L_* dist (F u) (F v)`, `dist (F u) (F v) ≤ L_* dist u v`,
   `|τ u - τ v| ≤ L_*² dist u v²`.
4. `b2_whitney_plateau_completion_proof n k hk hkn L_* F _ D _ _ τ _`
   gives `H j` with
   `spatialMap = F`, `domain = D`, `height = τ` on `D`.
5. `Characterization.b2_horizontalReference_map_mem_carrier_proof`
   : every
   `(F u, τ u) = (H j).map u`, `u ∈ D`, lies in `(H j).carrier`; hence
   `(Gc j).image ⊆ (H j).carrier` and the remainder is contained in that of step 1. -/
theorem dp2_horizontal_reference_cover :
    dp2_SharpChartStatement → dp2_HorizontalReferenceCoverStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.dp2_horizontal_reference_cover_proof

/-- **Vertical references** (`dp2_VerticalReferenceStatement`). The existing adapter suffices,
including `k = 2` (rank zero).

Proof sketch: `Characterization.b2_vertical_graph_reference n k hk 1 G` gives `V : VerticalReference n k (1 + 1)`
with `V.carrier = G.image`; `VerticalReference.mono` with `1 + 1 ≤ max 2 √(1+n)` keeps the
same data, so the carrier is unchanged (definitionally). -/
theorem dp2_vertical_reference : dp2_VerticalReferenceStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.dp2_vertical_reference_proof

/-- **Disjoint Borel restrictions** (`dp2_DisjointRestrictionStatement`), with
`E_j = B_j \ ⋃_{i<j} B_i`.

Proof sketch: `E = disjointed B` (mathlib `disjointed`, `disjoint_disjointed`, `disjointed_subset`,
`iUnion_disjointed`, `MeasurableSet.disjointed`). Since `μ (⋃ j, B j)ᶜ = 0`,
`μ = μ⌊⋃ j, E j` (`Measure.restrict_eq_self_of_ae_mem` or `Measure.restrict_congr_set` with
`Measure.restrict_univ`), and `Measure.restrict_iUnion` (pairwise disjoint, measurable) gives `Σ_j μ⌊E_j`. -/
theorem dp2_disjoint_restrictions : dp2_DisjointRestrictionStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.dp2_disjoint_restrictions_proof

/-- **One-reference certificate** (`dp2_OneReferenceCertificateStatement`), supplied by
`dp2_one_reference_certificate_proof`.

Proof sketch: generalize the single-ball covering `damb_covering` from the ambient
reference at `(2^{n+2}, 2)` to an arbitrary `ρ : Reference n k L`, `L ≥ 2`, at `(2^k, L)`: for a
support point `a` of `ν` and `R > 0`, index `{0}`, reference `ρ`, centre `a`, radius `2R`, bad set
`∅`, scale set `rootPairs ν a R`. Fields: `ball_subset` from `2R ≤ L R`; `ball_meets_carrier`
at `a ∈ supp ν ⊆ Γ`; `root_packing` `(2R)^k = 2^k R^k`; `local_packing` (zero, or
`(2R)^k ≤ s^k ≤ 2^k s^k` when `2R ≤ s`); `scaleSet_cover` since `z ∈ supp ν ⊆ Γ` gives
`infDist z Γ = 0` (`Metric.infDist_zero_of_mem`), `z ∈ P(a,2R)` and `r < R < 2R`; every
exceptional set is empty. Reuse `damb_measurableSet_rootPairs` and `damb_tsum_singleton`. The first conjunct of
`IsQuantitativelyMixedRectifiable` is the hypothesis. -/
theorem dp2_one_reference_certificate : dp2_OneReferenceCertificateStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.dp2_one_reference_certificate_proof

/-- **Countable-pieces assembly**, supplied by `dp2_pieces_assembly_proof`. Implication form over
the four preceding statements: `dp2_HorizontalReferenceCoverStatement → dp2_VerticalReferenceStatement →
dp2_DisjointRestrictionStatement → dp2_OneReferenceCertificateStatement →
dp2_CountablePiecesStatement`.

Proof sketch. Fix `n, k, μ, EH, EV` and the two covers at tolerance `1`.
* **Ambient, `k = n + 2`**: ignore the split. Put `B 0 = univ`,
  `B (j+1) = ∅`; the disjoint restrictions give `E`; each nonzero `μ⌊E_j` has `μ⌊E_j ≪ μ ≪ H_P^k` and support in
  `univ`, the carrier of `Reference.ambient`; the one-reference certificate at
  `L_* ≥ 2` concludes. (`damb_covering` with `RegularMixedCovering.mono` is an equivalent route.)
* **Nonambient, `k < n + 2`.** Horizontal cover `⟨I, H, hH⟩` of `μ⌊EH`: for each `i`, the horizontal references give
  references `Γ_{i,ℓ}` covering `(H i).image` modulo `H_P^k`, hence modulo `μ`. Vertical cover
  `⟨J, V, hV⟩` of `μ⌊EV`: the vertical references give references with `Γ_j = (V j).image`. Carriers are closed
  (`ba1_horizontal_basic_proof`, `ba1_vertical_basic_proof`). Enumerate the
  Borel sets `EH ∩ Γ_{i,ℓ}`, `EV ∩ Γ_j` as `B : ℕ → Set` with empty padding
  (`Characterization.exists_nat_family`, or a direct `Encodable` enumeration); `μ (⋃ B)ᶜ = 0` from `μ (EH ∪ EV)ᶜ = 0`,
  `(μ⌊EH)(⋃ H)ᶜ = μ((⋃ H)ᶜ ∩ EH) = 0` (`Measure.restrict_apply'`), the `H_P^k`-null horizontal
  remainders and `μ ≪ H_P^k`, and likewise vertically. The restrictions satisfy `E_j ⊆ B_j`. A nonzero
  `μ⌊E_j` has `B_j` nonempty, so `B_j ⊆ Γ` for one reference `ρ_j` (wrapped as
  `Reference.horizontal`/`Reference.vertical`); `(μ⌊E_j)(Γᶜ) = 0` and
  `Measure.support_subset_of_isClosed` give
  `supp (μ⌊E_j) ⊆ Γ`; the one-reference certificate at `L_*` concludes. -/
theorem dp2_pieces_assembly :
    dp2_HorizontalReferenceCoverStatement → dp2_VerticalReferenceStatement →
      dp2_DisjointRestrictionStatement → dp2_OneReferenceCertificateStatement →
        dp2_CountablePiecesStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.dp2_pieces_assembly_proof

end ParabolicRectifiability.QuantitativeCharacterization
