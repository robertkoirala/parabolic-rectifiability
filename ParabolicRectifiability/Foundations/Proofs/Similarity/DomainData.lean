import ParabolicRectifiability.Foundations.GraphDomainCover
import ParabolicRectifiability.Decomposition.Carrier.Definitions
import ParabolicRectifiability.Metric.Similarity
import ParabolicRectifiability.Foundations.Proofs.Similarity.DomainDataTransport
import ParabolicRectifiability.Foundations.Proofs.Similarity.DomainDataTransportVertical

/-! # Graph-domain data transported by a parabolic similarity

The declarations delegate to the imported graph-domain transport proofs. They are
the graph-domain-data halves of the transport of graph covers; the cover halves
are `fsim_hasHorizontalGraphCover_preimage_similarity` and
`fsim_hasGeneralRegularVerticalGraphCover_preimage_similarity`.

Notation, as for those statements: `S = similarity a R hR`,
`S z = δ_{1/R}(z - a)`, is the inverse of `F(y) = a + δ_R y`; pulled-back sets are
`S⁻¹' A = F(A) = S.symm '' A`.

The trace-base volume and the domain estimates scale by `R^k`, and the mesh `δ/R` is used in
the unit construction. The three identities below are exact for arbitrary testing
sets and every real `s`; for `s ≤ 0` both local index sets are empty, and a nonpositive mesh
forces empty patch families.

Conventions. The statements take the scaling laws they use as hypotheses with exactly the types
of the corresponding results: `hH` is the type of `fsim_hausdorffP_preimage_similarity`, and
`hreg` (vertical only) is the type of the regular-class covariance
`fsim_isGeneralRegularVerticalFunction_baseSimilarity` at `t₀ = a_t`. The given domain data are
the input of covariance; no carrier, packing, content or graphicality assumption is added.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Foundations

/-- **Horizontal graph-domain data transported by the similarity.**

Hypothesis: the Hausdorff law `hH` of `S` (exactly the type of
`fsim_hausdorffP_preimage_similarity`). For every
set `K`, tolerance `ε` and real `δ`, horizontal domain data of `K` with mesh `δ/R` give
horizontal domain data of `S⁻¹' K` with mesh `δ` and the exact identities
* trace volumes: `traceVolume' U = R^k · traceVolume (S '' U)` for **every** set `U`;
* total charge: `totalCharge' = R^k · totalCharge`;
* local charges: `localCharge' q s = R^k · localCharge (S q) (s/R)` for every `q` and real `s`
  (the local index sets correspond, `I'(q,s) = I(S q, s/R)`, both conditions kept).

Proof route. Same index sets. Graphs: `fsimb5_horizontalGraph a R hR`: direction `U`, domain `R • D`, offset
`R a_G + a_x`, normal map `u ↦ R g(u/R)`, time map `u ↦ R² h(u/R) + a_t`, same slope bound
`min ε 1`; its graph map satisfies `Φ'(R u) = S.symm (Φ u)` (the computation of
`fsimb5_horizontalGraph_image`). Traces `S⁻¹' F_j`; then
`horizontalPreimage G'_j (S⁻¹' F_j) = R • horizontalPreimage G_j F_j` and
`horizontalPreimage G'_j U = R • horizontalPreimage G_j (S '' U)` (`S.symm ⁻¹' U = S '' U`).
Patch centres `R p_α`, radii `R ρ_α ∈ (0, δ]`; `B(R p, R ρ) = R • B(p, ρ)`, so the new patch is
`S⁻¹'` of the old one. Base volume `λ_U(R • A) = R^k λ_U(A)` for every `A`
(`Measure.addHaar_smul`, `finrank U = k`, `rank_eq`); charges
`c'_α = (Rρ)^k + R^k λ(B_α) + R^k H_P^k(P_α) = R^k c_α` (`hH` for the patch). Centre points
`z'_α = S.symm z_α`, so `z'_α ∈ P(q,s) ↔ z_α ∈ P(S q, s/R)` (`image_similarity_ball`) and
`R ρ_α ≤ s ↔ ρ_α ≤ s/R`; the `tsum`s correspond through this index equivalence
(`ENNReal.tsum_mul_left`). Measurability and coverage modulo `H_P^k` transfer by the
homeomorphism, the linear equivalence `u ↦ R u` of `U`, and `hH`
(`S⁻¹' K \ ⋃ S⁻¹' F_j = S⁻¹'(K \ ⋃ F_j)`). -/
theorem fsim_horizontalDomainData_preimage_similarity {n k : ℕ} (a : Space n) (R : ℝ)
    (hR : 0 < R)
    (hH : ∀ A : Set (Space n),
      hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
    (K : Set (Space n)) (ε δ : ℝ) (D : HorizontalDomainData n k ε (δ / R) K) :
    ∃ D' : HorizontalDomainData n k ε δ (similarity a R hR ⁻¹' K),
      (∀ U : Set (Space n),
        D'.traceVolume U = ENNReal.ofReal R ^ k * D.traceVolume (similarity a R hR '' U)) ∧
      D'.totalCharge = ENNReal.ofReal R ^ k * D.totalCharge ∧
      ∀ (q : Space n) (s : ℝ),
        D'.localCharge q s =
          ENNReal.ofReal R ^ k * D.localCharge (similarity a R hR q) (s / R) := by
  exact fsim_horizontalDomainData_preimage_similarity_proof a R hR hH K ε δ D

/-- **General regular vertical graph-domain data transported by the similarity.**
Under `G_R(u,t) = R G(u/R, t/R²)` the parabolic Lipschitz seminorm is unchanged and every
prescribed graph tolerance is retained.

Hypotheses: the Hausdorff law `hH` of `S` (exactly the type of
`fsim_hausdorffP_preimage_similarity`) and the regular-class covariance `hreg` for the base
similarity with centre `(0, a_t)` (exactly the hypothesis of
`fsim_hasGeneralRegularVerticalGraphCover_preimage_similarity`). This is the vertical analogue
of `fsim_horizontalDomainData_preimage_similarity`:
vertical domain data of `K` with mesh `δ/R` give vertical domain data of `S⁻¹' K` with mesh `δ`
and the same three exact identities.

Proof route. Same index sets. Graphs: `fsimb5_verticalGraph a R hreg`: same direction `W` and rank, offset
`R a_G + a_x`, function `R • G ∘ σ`, `σ = baseSimilarity W (0, a_t) R`, regular with bound
`min ε 1` by `hreg`. With the base map `β = σ⁻¹`, `β(u,t) = (R u, R² t + a_t)`
(`baseSimilarityHomeomorph`), the graph maps satisfy
`Φ' (β p) = S.symm (Φ p)` (pointwise form of `range_similarity_symm_graph`). Traces
`S⁻¹' F_j`; `Φ'⁻¹(S⁻¹' F) = β '' Φ⁻¹(F)` and `Φ'⁻¹(U) = β '' Φ⁻¹(S '' U)`. Patch centres
`β p_α`, radii `R ρ_α ∈ (0, δ]`; `β '' B(p, ρ) = B(β p, R ρ)` in the max parabolic metric
(`dist_baseSimilarity`), so the whole-ball patch is `S⁻¹'` of the old one. Intrinsic volume
`intrinsicParabolicVolume W (β '' A) = R^{dim W + 2} · intrinsicParabolicVolume W A = R^k · …`
for every `A` (`map_baseSimilarityHomeomorph`, `rank_eq`); charges `c'_α = R^k c_α`
(radius, base ball, `hH`); local index sets correspond as in the horizontal case. Rank zero
(`k = 2`, base `ℝ` with `dt`) and full rank need no separate argument. -/
theorem fsim_verticalDomainData_preimage_similarity {n k : ℕ} (a : Space n) (R : ℝ)
    (hR : 0 < R)
    (hH : ∀ A : Set (Space n),
      hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
    (hreg : ∀ (W : Submodule ℝ (Spatial n)) (F : SubspaceSpace W → W.orthogonal) (ε : ℝ),
      IsGeneralRegularVerticalFunction W F ε →
        IsGeneralRegularVerticalFunction W
          (fun p => R • F (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking a.2.val) R p))
          ε)
    (K : Set (Space n)) (ε δ : ℝ) (D : VerticalDomainData n k ε (δ / R) K) :
    ∃ D' : VerticalDomainData n k ε δ (similarity a R hR ⁻¹' K),
      (∀ U : Set (Space n),
        D'.traceVolume U = ENNReal.ofReal R ^ k * D.traceVolume (similarity a R hR '' U)) ∧
      D'.totalCharge = ENNReal.ofReal R ^ k * D.totalCharge ∧
      ∀ (q : Space n) (s : ℝ),
        D'.localCharge q s =
          ENNReal.ofReal R ^ k * D.localCharge (similarity a R hR q) (s / R) := by
  exact fsim_verticalDomainData_preimage_similarity_proof a R hR hH hreg K ε δ D

end ParabolicRectifiability.Foundations
