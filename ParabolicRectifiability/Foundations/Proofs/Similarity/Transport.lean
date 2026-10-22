import ParabolicRectifiability.Foundations.SupportBounds
import ParabolicRectifiability.Measure.BetaLaws
import ParabolicRectifiability.Decomposition.Carrier.Definitions
import ParabolicRectifiability.Foundations.Proofs.Similarity.MeasureTransport
import ParabolicRectifiability.Foundations.Proofs.Similarity.SupportBoundsTransport
import ParabolicRectifiability.Foundations.Proofs.Similarity.CoverTransport

/-! # Transport by a parabolic similarity

Measure-theoretic and graph-cover statements under a parabolic similarity: Hausdorff measure
(`fsim_hausdorffP_preimage_similarity`), supports of pulled-back restrictions
(`fsim_support_restrict_preimage_homeomorph`), tubular neighbourhoods
(`fsim_parabolicVolume_thickening_preimage_similarity`), the support bundle
(`fsim_hasRegularSupportBounds_preimage_similarity`) and horizontal and vertical graph covers
(`fsim_hasHorizontalGraphCover_preimage_similarity`,
`fsim_hasGeneralRegularVerticalGraphCover_preimage_similarity`). They are stated for arbitrary
sets, measures, centres and scales.

Notation: `S = similarity a R hR`, `S z = δ_{1/R}(z - a)`, is the inverse of
`F(y) = a + δ_R y`. Pulled-back sets are `S⁻¹' A = F(A)`. `S` is a homeomorphism with
`d(S z, S w) = R⁻¹ d(z, w)` (`dist_similarity`), `S⁻¹' P(S q, s) = P(q, R s)`
(`preimage_similarity_ball`) and `S_# L^{n+1} = R^{n+2} L^{n+1}`
(`map_similarity_parabolicVolume`).

A similarity multiplies `H_P^k` by `R^k`, packing radii by `R` and ambient volume by `R^{n+2}`;
the tubular estimate thus has the scaled factor `R^k r^{n+2-k}`; a homeomorphism carries the
actual support onto the actual support; graph covers at every prescribed tolerance are
retained.

The transport statements take the scaling laws they use (`hH`, the Hausdorff law; `hT`, the
tube law; for vertical graphs `hreg`, the covariance of the regular class) as hypotheses with
exactly those types. Unit-scale bounds and covers are inputs to covariance; nothing else is
assumed.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Foundations

/-- **Hausdorff measure under the similarity.**

`H_P^k(S⁻¹' A) = R^k H_P^k(A)` for every `k` and every set `A` (outer
measure; no measurability; `k = 0` included).

Proof route: `S⁻¹' A = S.symm '' A`; `edist (S.symm x) (S.symm y) = R · edist x y`
(`edist_similarity` applied to `S`); a map multiplying all extended distances by `R`
multiplies the unnormalized diameter-power Hausdorff measure by `R^k` (mathlib's
`LipschitzWith.hausdorffMeasure_image_le` for `S.symm` with constant `R` and for `S` with
constant `R⁻¹`, or `Isometry`-style `hausdorffMeasure_image` after scaling), with
`hausdorffP` unfolded. The proof is `fsim_hausdorffP_preimage_similarity_proof`. -/
theorem fsim_hausdorffP_preimage_similarity (n k : ℕ) (a : Space n) (R : ℝ) (hR : 0 < R)
    (A : Set (Space n)) :
    hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A := by
  exact fsim_hausdorffP_preimage_similarity_proof n k a R hR A

/-- **Actual supports of pulled-back restrictions.**

In the general form: for Borel spaces `X`, `Y`, any measure `μ` on `X`, any
homeomorphism `e : X ≃ₜ Y`, any constant `c ∈ (0, ∞)` and any set `A ⊆ Y` (not necessarily
measurable), the actual support of `μ⌊e⁻¹(A)` is the preimage under `e` of the actual support
of `(c · e_# μ)⌊A`. No regularity of `μ` is used. The similarity case
(`ν = rescaledSource μ k a R hR = R^{-k} S_# μ`) is the corollary
`fsim_support_restrict_preimage_similarity`.

Proof route: `Measure.mem_support_iff_forall`; for open `V`,
`(c · e_# μ)⌊A (V) = c · μ(e⁻¹' V ∩ e⁻¹' A)` (`Measure.restrict_apply` on the open, hence
measurable, `V`; `MeasurableEquiv.map_apply` for `e.toMeasurableEquiv`, valid for every set);
`c ≠ 0, ⊤`; the open neighbourhoods of `x` are exactly the `e⁻¹' V` with `V` an open
neighbourhood of `e x`. The proof is `fsim_support_restrict_preimage_homeomorph_proof`. -/
theorem fsim_support_restrict_preimage_homeomorph {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (e : X ≃ₜ Y) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤) (A : Set Y) :
    (μ.restrict (e ⁻¹' A)).support = e ⁻¹' ((c • μ.map e).restrict A).support := by
  exact fsim_support_restrict_preimage_homeomorph_proof μ e c hc0 hct A

/-- **Tubular neighbourhoods under the similarity.**

For every set `K` and every real `r`,
`|{z : dist(z, S⁻¹' K) < r}| = R^{n+2} |{w : dist(w, K) < r/R}|` (extended distance; the empty
set has an empty neighbourhood; `r ≤ 0` gives empty sets on both sides).

Proof route: `infEDist z (S⁻¹' K) = R · infEDist (S z) K` (`S⁻¹' K = S.symm '' K` and
`edist_similarity`); so the left set is `S⁻¹'` of the right one
(`ofReal R * x < ofReal r ↔ x < ofReal (r / R)` for `R > 0`, including `x = ⊤` and
`r ≤ 0`); then `map_similarity_parabolicVolume` on this open (hence Borel) set. The proof is
`fsim_parabolicVolume_thickening_preimage_similarity_proof`. -/
theorem fsim_parabolicVolume_thickening_preimage_similarity {n : ℕ} (a : Space n) (R : ℝ)
    (hR : 0 < R) (K : Set (Space n)) (r : ℝ) :
    parabolicVolume n {z | Metric.infEDist z (similarity a R hR ⁻¹' K) < ENNReal.ofReal r} =
      ENNReal.ofReal R ^ (n + 2) *
        parabolicVolume n {w | Metric.infEDist w K < ENNReal.ofReal (r / R)} := by
  exact fsim_parabolicVolume_thickening_preimage_similarity_proof a R hR K r

/-- **The support bundle transported by the similarity, with the same constant.**

Hypotheses: `k ≤ n + 2`; the Hausdorff law `hH` of `S` (exactly the type of
`fsim_hausdorffP_preimage_similarity`); the tube law `hT` (exactly the type of
`fsim_parabolicVolume_thickening_preimage_similarity`); the bundle
`HasRegularSupportBounds k C b ρ` of `(K_H, K_V)` at any centre `b` and scale `ρ`; and the
typed covers of the pulled-back supports at every positive tolerance (supplied by
`fsim_hasHorizontalGraphCover_preimage_similarity` and
`fsim_hasGeneralRegularVerticalGraphCover_preimage_similarity`). Conclusion: the bundle
`HasRegularSupportBounds k C (S.symm b) (R ρ)` of `(S⁻¹' K_H, S⁻¹' K_V)` with the **same**
constant `C`. The case `b = 0`, `ρ = 1` gives `S.symm 0 = a`.

Proof route, field by field. Compactness: `S⁻¹' K = S.symm '' K`. Inclusion:
`S⁻¹' P̄(b, ρ) = P̄(S.symm b, R ρ)`. Unavailable types: `S⁻¹' ∅ = ∅`. Covers: given.
Global Hausdorff: `hH` and `R^k ρ^k = (R ρ)^k`. Local Hausdorff at `0 < s ≤ R ρ`:
`(S⁻¹' K) ∩ P(q, s) = S⁻¹'(K ∩ P(S q, s/R))` (`preimage_similarity_ball`), `s/R ≤ ρ`, `hH`.
Separated sets: `S` maps an `r`-separated `F ⊆ S⁻¹' K ∩ P(q,s)` injectively onto an
`r/R`-separated subset of `K ∩ P(S q, s/R)`, and `(s/R)/(r/R) = s/r`. Finite and countable
packings: `S` maps the disjoint `P(z_i, r_i)` onto the disjoint `P(S z_i, r_i/R)`
(`image_similarity_ball`), `S z_i ∈ K ∩ P(S q, s/R)`, `0 < r_i/R ≤ s/R`, and
`Σ r_i^k = R^k Σ (r_i/R)^k` (`ENNReal.tsum_mul_left`). Tube (checkpoint, from `hT`):
`R^{n+2} C ρ^k (r/R)^{n+2-k} = C (R ρ)^k r^{n+2-k}` for `0 < r ≤ R ρ`, using `k ≤ n + 2`.
The local and packing fields use the unit bundle's packing and Hausdorff inputs at the
transformed scale. The proof is `fsim_hasRegularSupportBounds_preimage_similarity_proof`. -/
theorem fsim_hasRegularSupportBounds_preimage_similarity {n k : ℕ} (hkn : k ≤ n + 2) (C : ℝ)
    (a : Space n) (R : ℝ) (hR : 0 < R)
    (hH : ∀ A : Set (Space n),
      hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
    (hT : ∀ (K : Set (Space n)) (r : ℝ),
      parabolicVolume n {z | Metric.infEDist z (similarity a R hR ⁻¹' K) < ENNReal.ofReal r} =
        ENNReal.ofReal R ^ (n + 2) *
          parabolicVolume n {w | Metric.infEDist w K < ENNReal.ofReal (r / R)})
    (b : Space n) (ρ : ℝ) (KH KV : Set (Space n)) (h : HasRegularSupportBounds k C b ρ KH KV)
    (hHcov : ∀ ε : ℝ, 0 < ε → HasHorizontalGraphCover k (similarity a R hR ⁻¹' KH) ε)
    (hVcov : ∀ ε : ℝ, 0 < ε →
      HasGeneralRegularVerticalGraphCover k (similarity a R hR ⁻¹' KV) ε) :
    HasRegularSupportBounds k C ((similarity a R hR).symm b) (R * ρ)
      (similarity a R hR ⁻¹' KH) (similarity a R hR ⁻¹' KV) := by
  exact fsim_hasRegularSupportBounds_preimage_similarity_proof hkn C a R hR hH hT b ρ KH KV h hHcov hVcov

/-- **Horizontal graph covers transported by the similarity.**

Hypothesis: the Hausdorff law `hH` of `S` (exactly the type of
`fsim_hausdorffP_preimage_similarity`). For every set `K` and every tolerance `ε`, a horizontal `ε`-cover of `K` modulo `H_P^k` gives one
of `S⁻¹' K` at the same `ε`. No graph-domain data.

Proof route: transport each graph by `F = S.symm`: same direction `U`, domain `R • D ⊆ U`,
offset `R a_G + a_x`, normal map `u ↦ R n(u/R)`, time map `u ↦ R² τ(u/R) + a_t`; the slope
bound is unchanged (`max(‖R Δn‖, √(R² |Δτ|)) = R max(‖Δn‖, √|Δτ|) ≤ ε ‖Δu‖`), and the new
image is `S.symm ''` (old image) `= S⁻¹'` (old image). The exception
`S⁻¹' K \ ⋃ S⁻¹' Γ_i = S⁻¹'(K \ ⋃ Γ_i)` is `H_P^k`-null by `hH`. The proof is
`fsim_hasHorizontalGraphCover_preimage_similarity_proof`. -/
theorem fsim_hasHorizontalGraphCover_preimage_similarity {n k : ℕ} (a : Space n) (R : ℝ)
    (hR : 0 < R)
    (hH : ∀ A : Set (Space n),
      hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
    (K : Set (Space n)) (ε : ℝ) (h : HasHorizontalGraphCover k K ε) :
    HasHorizontalGraphCover k (similarity a R hR ⁻¹' K) ε := by
  exact fsim_hasHorizontalGraphCover_preimage_similarity_proof a R hR hH K ε h

/-- **General regular vertical graph covers transported by the similarity.**

Under `G_R(u,t) = R G(u/R, t/R²)` the parabolic Lipschitz seminorm is unchanged, and
translation has the same invariance; hence every prescribed graph tolerance is retained.

Hypotheses: the Hausdorff law `hH` of `S`, and the regular-class covariance `hreg` for the
base similarity with centre `(0, a_t)` (exactly the type of
`fsim_isGeneralRegularVerticalFunction_baseSimilarity` with `t₀ = a_t`).
For every set `K` and tolerance `ε`, a general regular vertical `ε`-cover of
`K` modulo `H_P^k` gives one of `S⁻¹' K` at the same `ε`. No graph-domain data.

Proof route: transport each full graph by `F = S.symm`: same direction `W` and rank, offset
`R • a_G + a_x`, function `G' = R • G ∘ σ`, `σ = baseSimilarity W (0, a_t) R`, regular with the
same `ε` by `hreg`. Since `σ` is a bijection of `W × ℝ` with inverse
`β(u,t) = (R u, R² t + a_t)`, the new graph map satisfies `Φ'(β p) = S.symm (Φ p)`, so the new
image is `S⁻¹'` of the old one. The exception is `H_P^k`-null by `hH`. The proof is
`fsim_hasGeneralRegularVerticalGraphCover_preimage_similarity_proof`. -/
theorem fsim_hasGeneralRegularVerticalGraphCover_preimage_similarity {n k : ℕ} (a : Space n)
    (R : ℝ) (hR : 0 < R)
    (hH : ∀ A : Set (Space n),
      hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
    (hreg : ∀ (W : Submodule ℝ (Spatial n)) (F : SubspaceSpace W → W.orthogonal) (ε : ℝ),
      IsGeneralRegularVerticalFunction W F ε →
        IsGeneralRegularVerticalFunction W
          (fun p => R • F (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking a.2.val) R p))
          ε)
    (K : Set (Space n)) (ε : ℝ) (h : HasGeneralRegularVerticalGraphCover k K ε) :
    HasGeneralRegularVerticalGraphCover k (similarity a R hR ⁻¹' K) ε := by
  exact fsim_hasGeneralRegularVerticalGraphCover_preimage_similarity_proof a R hR hH hreg K ε h

end ParabolicRectifiability.Foundations
