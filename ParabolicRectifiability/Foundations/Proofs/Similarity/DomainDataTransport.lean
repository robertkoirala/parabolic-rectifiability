import ParabolicRectifiability.Foundations.GraphDomainCover
import ParabolicRectifiability.Foundations.Proofs.Similarity.CoverTransport
import ParabolicRectifiability.Metric.Similarity

/-! # Horizontal graph-domain data transported by a parabolic similarity

Proof of `fsim_horizontalDomainData_preimage_similarity`.
`fsim_horizontalDomainData_preimage_similarity_proof` has exactly the type of the statement.

Notation: `S = similarity a R hR`, `S.symm (x, t) = (R x + a_x, R² t + a_t)`; for a horizontal
graph `G`, `G' = fsimb5_horizontalGraph a R hR G` is the proved transported graph (domain
`R • D`, same direction and slope bound), `Φ`, `Φ'` the graph maps.

* **Bookkeeping (reused for the vertical case).** Borel preimages, trace containment, coverage
  modulo `H_P^k` through `hH`, the radius bound `ρ ≤ δ/R ⇒ R ρ ≤ δ`, the charge identity
  `(Rρ)^k + R^k b + R^k h = R^k (ρ^k + b + h)`, the local index correspondence
  `{α : S.symm z_α ∈ P(q,s), R ρ_α ≤ s} = {α : z_α ∈ P(S q, s/R), ρ_α ≤ s/R}` for every real `s`,
  and the `tsum` identities. They are stated for arbitrary index types and families.
* **Checkpoint 1.** `Φ'(R u) = S.symm (Φ u)` and the trace preimages
  `Φ'⁻¹(T) = (R⁻¹ • ·)⁻¹' Φ⁻¹(S.symm⁻¹' T)`, so `Φ'⁻¹(S⁻¹' F) = R • Φ⁻¹(F)` and
  `Φ'⁻¹(U) = R • Φ⁻¹(S '' U)` for every set `U`.
* **Checkpoint 2.** `λ(R • A) = R^k λ(A)` for every `A` (`Measure.addHaar_smul_of_nonneg`,
  `rank_eq`), the patch identity `Φ'(R•D ∩ B(R p, R ρ)) = S⁻¹' Φ(D ∩ B(p, ρ))`, the charges
  `c'_α = R^k c_α`, and the local index sets `I'(q,s) = I(S q, s/R)`.

No measurability of the testing set `U` is used. For `s ≤ 0` both local index sets are empty;
this needs no case split, since the index identity holds for every real `s`. A nonpositive
mesh gives empty patch families automatically: the patch indices are the given ones.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise

namespace ParabolicRectifiability.Foundations

/-! ## Shared bookkeeping, independent of the similarity (reused for the vertical case) -/

section Generic

/-- The mesh `δ/R` becomes the mesh `δ`: `ρ ≤ δ/R ⇒ R ρ ≤ δ`. -/
theorem fsimb5d_mul_le_of_le_div {R ρ δ : ℝ} (hR : 0 < R) (hρ : ρ ≤ δ / R) : R * ρ ≤ δ :=
  (le_div_iff₀' hR).mp hρ

/-- The charge identity `(R ρ)^k + R^k b + R^k h = R^k (ρ^k + b + h)`. -/
theorem fsimb5d_charge_scale {k : ℕ} {R : ℝ} (hR : 0 < R) (ρ : ℝ) {b b' h h' : ℝ≥0∞}
    (hb : b' = ENNReal.ofReal R ^ k * b) (hh : h' = ENNReal.ofReal R ^ k * h) :
    ENNReal.ofReal (R * ρ) ^ k + b' + h' =
      ENNReal.ofReal R ^ k * (ENNReal.ofReal ρ ^ k + b + h) := by
  rw [ENNReal.ofReal_mul hR.le, mul_pow, hb, hh, mul_add, mul_add]

/-- A `tsum` over equal index sets of termwise rescaled terms. -/
theorem fsimb5d_tsum_subtype_eq_mul {ι : Type*} {s t : Set ι} (hst : s = t)
    (c c' : ι → ℝ≥0∞) (r : ℝ≥0∞) (hc : ∀ α, c' α = r * c α) :
    ∑' α : s, c' α = r * ∑' α : t, c α := by
  subst hst
  simp only [hc, ENNReal.tsum_mul_left]

/-- A `tsum` of termwise rescaled terms. -/
theorem fsimb5d_tsum_eq_mul {ι : Type*} (c c' : ι → ℝ≥0∞) (r : ℝ≥0∞)
    (hc : ∀ α, c' α = r * c α) :
    ∑' α, c' α = r * ∑' α, c α := by
  simp only [hc, ENNReal.tsum_mul_left]

/-- `x ∈ B(R p, R ρ) ↔ R⁻¹ x ∈ B(p, ρ)` in a real normed space. -/
theorem fsimb5d_mem_ball_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {R : ℝ}
    (hR : 0 < R) (x p : E) (ρ : ℝ) :
    x ∈ Metric.ball (R • p) (R * ρ) ↔ R⁻¹ • x ∈ Metric.ball p ρ := by
  rw [← mem_smul_set_iff_inv_smul_mem₀ hR.ne', smul_ball hR.ne', Real.norm_eq_abs, abs_of_pos hR]

end Generic

/-! ## Shared bookkeeping for `S = similarity a R hR` (reused for the vertical case) -/

section Bookkeeping

variable {n k : ℕ} (a : Space n) (R : ℝ) (hR : 0 < R)

/-- Borel sets pull back to Borel sets under the similarity. -/
theorem fsimb5d_measurableSet_preimage {A : Set (Space n)} (hA : MeasurableSet A) :
    MeasurableSet (similarity a R hR ⁻¹' A) :=
  hA.preimage (similarity a R hR).continuous.measurable

/-- `S.symm z ∈ S⁻¹' K ↔ z ∈ K`. -/
theorem fsimb5d_symm_mem_preimage_iff (K : Set (Space n)) (z : Space n) :
    (similarity a R hR).symm z ∈ similarity a R hR ⁻¹' K ↔ z ∈ K := by
  rw [mem_preimage, Homeomorph.apply_symm_apply]

/-- Trace containment transfers: `F ⊆ K ∩ Γ` and `Γ' = S.symm '' Γ` give
`S⁻¹' F ⊆ S⁻¹' K ∩ Γ'`. -/
theorem fsimb5d_preimage_subset_inter {F K Γ Γ' : Set (Space n)}
    (hΓ : Γ' = (similarity a R hR).symm '' Γ) (h : F ⊆ K ∩ Γ) :
    similarity a R hR ⁻¹' F ⊆ similarity a R hR ⁻¹' K ∩ Γ' := by
  rw [hΓ, Homeomorph.image_symm, ← preimage_inter]
  exact preimage_mono h

/-- Pairwise disjoint traces stay pairwise disjoint. -/
theorem fsimb5d_pairwise_disjoint_preimage {ι : Type*} {F : ι → Set (Space n)}
    (h : Pairwise fun i j => Disjoint (F i) (F j)) :
    Pairwise fun i j => Disjoint (similarity a R hR ⁻¹' F i) (similarity a R hR ⁻¹' F j) := by
  intro i j hij
  exact (h hij).preimage _

/-- Coverage modulo `H_P^k` transfers through the Hausdorff law `hH`: if `F' i = S⁻¹' F i`
and `H_P^k(K \ ⋃ F i) = 0`, then `H_P^k(S⁻¹' K \ ⋃ F' i) = 0`. -/
theorem fsimb5d_hausdorffP_diff_iUnion {ι : Sort*}
    (hH : ∀ A : Set (Space n),
      hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
    (K : Set (Space n)) (F F' : ι → Set (Space n))
    (hF : ∀ i, F' i = similarity a R hR ⁻¹' F i) (h0 : hausdorffP n k (K \ ⋃ i, F i) = 0) :
    hausdorffP n k (similarity a R hR ⁻¹' K \ ⋃ i, F' i) = 0 := by
  simp only [hF]
  rw [← preimage_iUnion, ← preimage_sdiff, hH, h0, mul_zero]

/-- The Hausdorff law for a set given as a preimage. -/
theorem fsimb5d_hausdorffP_of_eq_preimage
    (hH : ∀ A : Set (Space n),
      hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
    {P P' : Set (Space n)} (hP : P' = similarity a R hR ⁻¹' P) :
    hausdorffP n k P' = ENNReal.ofReal R ^ k * hausdorffP n k P := by
  rw [hP, hH]

/-- The local index correspondence, for every real `s` (both sets are empty when `s ≤ 0`):
with centre points `z'_α = S.symm z_α` and radii `ρ'_α = R ρ_α`,
`{α : z'_α ∈ P(q,s), ρ'_α ≤ s} = {α : z_α ∈ P(S q, s/R), ρ_α ≤ s/R}`. -/
theorem fsimb5d_localIndex_eq {ι : Type*} (z z' : ι → Space n) (ρ ρ' : ι → ℝ)
    (hz : ∀ α, z' α = (similarity a R hR).symm (z α)) (hρ : ∀ α, ρ' α = R * ρ α)
    (q : Space n) (s : ℝ) :
    {α | z' α ∈ Metric.ball q s ∧ ρ' α ≤ s} =
      {α | z α ∈ Metric.ball (similarity a R hR q) (s / R) ∧ ρ α ≤ s / R} := by
  ext α
  rw [mem_ofPred_eq, mem_ofPred_eq, hz, hρ, ← image_similarity_ball, ← Homeomorph.preimage_symm,
    mem_preimage, le_div_iff₀' hR]

/-- The local charge identity: with `z'_α = S.symm z_α`, `ρ'_α = R ρ_α` and `c'_α = R^k c_α`,
`Σ_{α ∈ I'(q,s)} c'_α = R^k Σ_{α ∈ I(S q, s/R)} c_α` for every `q` and real `s`. -/
theorem fsimb5d_localCharge_eq {ι : Type*} (z z' : ι → Space n) (ρ ρ' : ι → ℝ)
    (c c' : ι → ℝ≥0∞) (hz : ∀ α, z' α = (similarity a R hR).symm (z α))
    (hρ : ∀ α, ρ' α = R * ρ α) (hc : ∀ α, c' α = ENNReal.ofReal R ^ k * c α)
    (q : Space n) (s : ℝ) :
    ∑' α : {α | z' α ∈ Metric.ball q s ∧ ρ' α ≤ s}, c' α =
      ENNReal.ofReal R ^ k *
        ∑' α : {α | z α ∈ Metric.ball (similarity a R hR q) (s / R) ∧ ρ α ≤ s / R}, c α :=
  fsimb5d_tsum_subtype_eq_mul (fsimb5d_localIndex_eq a R hR z z' ρ ρ' hz hρ q s) c c' _ hc

end Bookkeeping

/-! ## Checkpoint 1: the graph-map identity and the trace preimages -/

section HorizontalGraph

variable {n k : ℕ} {ε : ℝ} (a : Space n) (R : ℝ) (hR : 0 < R) (G : HorizontalGraph n k ε)

/-- `u ↦ R u` from the domain of `G` onto the domain of the transported graph, with that
domain as its declared codomain. -/
def fsimb5d_push (u : G.domain) : (fsimb5_horizontalGraph a R hR G).domain :=
  fsimb5_hPush R hR G u

theorem fsimb5d_pull_push (u : G.domain) : fsimb5_hPull R G (fsimb5d_push a R hR G u) = u :=
  fsimb5_hPull_hPush R hR G u

theorem fsimb5d_push_pull (u : (fsimb5_horizontalGraph a R hR G).domain) :
    fsimb5d_push a R hR G (fsimb5_hPull R G u) = u :=
  Subtype.ext (smul_inv_smul₀ hR.ne' u.1)

/-- The pointwise graph-map identity `Φ'(u) = S.symm (Φ (R⁻¹ u))`. -/
theorem fsimb5d_horizontalGraphMap (u : (fsimb5_horizontalGraph a R hR G).domain) :
    horizontalGraphMap (fsimb5_horizontalGraph a R hR G) u =
      (similarity a R hR).symm (horizontalGraphMap G (fsimb5_hPull R G u)) := by
  rw [similarity_symm_apply]
  change point (R • G.offset + a.1 + ((u.val : G.direction) : Spatial n) +
      R • ((G.normal (fsimb5_hPull R G u) : G.direction.orthogonal) : Spatial n))
      (R ^ 2 * G.time (fsimb5_hPull R G u) + a.2.val) =
    point (R • (G.offset + R⁻¹ • ((u.val : G.direction) : Spatial n) +
      (G.normal (fsimb5_hPull R G u) : Spatial n)) + a.1)
      (R ^ 2 * G.time (fsimb5_hPull R G u) + a.2.val)
  congr 1
  rw [smul_add, smul_add, smul_inv_smul₀ hR.ne']
  abel

/-- **Checkpoint 1, graph maps.** `Φ'(R u) = S.symm (Φ u)`. -/
theorem fsimb5d_horizontalGraphMap_push (u : G.domain) :
    horizontalGraphMap (fsimb5_horizontalGraph a R hR G) (fsimb5d_push a R hR G u) =
      (similarity a R hR).symm (horizontalGraphMap G u) := by
  rw [fsimb5d_horizontalGraphMap, fsimb5d_pull_push]

/-- The graph-map identity on centres: `Φ u ∈ K ⇒ Φ'(R u) ∈ S⁻¹' K`. -/
theorem fsimb5d_horizontalGraphMap_push_mem {K : Set (Space n)} {u : G.domain}
    (hu : horizontalGraphMap G u ∈ K) :
    horizontalGraphMap (fsimb5_horizontalGraph a R hR G) (fsimb5d_push a R hR G u) ∈
      similarity a R hR ⁻¹' K := by
  rw [fsimb5d_horizontalGraphMap_push]
  exact (fsimb5d_symm_mem_preimage_iff a R hR K _).mpr hu

/-- The preimage identity `Φ'⁻¹(T) = (R⁻¹ • ·)⁻¹' Φ⁻¹(S.symm⁻¹' T)` for every set `T`. -/
theorem fsimb5d_horizontalPreimage (T : Set (Space n)) :
    horizontalPreimage (fsimb5_horizontalGraph a R hR G) T =
      (fun u : (fsimb5_horizontalGraph a R hR G).direction => R⁻¹ • u) ⁻¹'
        horizontalPreimage G ((similarity a R hR).symm ⁻¹' T) := by
  ext u
  constructor
  · rintro ⟨hu, hT⟩
    refine ⟨hu, ?_⟩
    rw [fsimb5d_horizontalGraphMap a R hR G ⟨u, hu⟩] at hT
    exact hT
  · rintro ⟨hu, hT⟩
    refine ⟨hu, ?_⟩
    rw [fsimb5d_horizontalGraphMap a R hR G ⟨u, hu⟩]
    exact hT

/-- **Checkpoint 1, trace preimages.** `Φ'⁻¹(S⁻¹' F) = R • Φ⁻¹(F)`, as the preimage under
`R⁻¹ • ·`. -/
theorem fsimb5d_horizontalPreimage_preimage (F : Set (Space n)) :
    horizontalPreimage (fsimb5_horizontalGraph a R hR G) (similarity a R hR ⁻¹' F) =
      (fun u : (fsimb5_horizontalGraph a R hR G).direction => R⁻¹ • u) ⁻¹'
        horizontalPreimage G F := by
  rw [fsimb5d_horizontalPreimage, Homeomorph.preimage_symm, Homeomorph.image_preimage]

/-- **Checkpoint 1, testing sets.** `Φ'⁻¹(U) = R • Φ⁻¹(S '' U)` for **every** set `U`. -/
theorem fsimb5d_horizontalPreimage_image (U : Set (Space n)) :
    horizontalPreimage (fsimb5_horizontalGraph a R hR G) U =
      (fun u : (fsimb5_horizontalGraph a R hR G).direction => R⁻¹ • u) ⁻¹'
        horizontalPreimage G (similarity a R hR '' U) := by
  rw [fsimb5d_horizontalPreimage, Homeomorph.preimage_symm]

/-- `u ↦ R⁻¹ u` is measurable on the transported direction. -/
theorem fsimb5d_measurable_inv_smul :
    Measurable (fun u : (fsimb5_horizontalGraph a R hR G).direction => R⁻¹ • u) :=
  (continuous_const_smul R⁻¹).measurable

/-- Borel trace preimages transfer. -/
theorem fsimb5d_measurableSet_horizontalPreimage {F : Set (Space n)}
    (hF : MeasurableSet (horizontalPreimage G F)) :
    MeasurableSet
      (horizontalPreimage (fsimb5_horizontalGraph a R hR G) (similarity a R hR ⁻¹' F)) := by
  -- View `hF` with the measurable structure of the transported direction (same submodule).
  have hF' : MeasurableSet
      (horizontalPreimage G F : Set (fsimb5_horizontalGraph a R hR G).direction) := hF
  rw [fsimb5d_horizontalPreimage_preimage]
  exact hF'.preimage (fsimb5d_measurable_inv_smul a R hR G)

/-- Patch centres transfer: `p ∈ Φ⁻¹(F) ⇒ R p ∈ Φ'⁻¹(S⁻¹' F)`. -/
theorem fsimb5d_push_mem_horizontalPreimage {F : Set (Space n)} {u : G.domain}
    (hu : (u : G.direction) ∈ horizontalPreimage G F) :
    ((fsimb5d_push a R hR G u : (fsimb5_horizontalGraph a R hR G).domain) :
        (fsimb5_horizontalGraph a R hR G).direction) ∈
      horizontalPreimage (fsimb5_horizontalGraph a R hR G) (similarity a R hR ⁻¹' F) := by
  rw [fsimb5d_horizontalPreimage_preimage]
  show R⁻¹ • R • (u : G.direction) ∈ horizontalPreimage G F
  rw [inv_smul_smul₀ hR.ne']
  exact hu

end HorizontalGraph

/-! ## Checkpoint 2: base volumes, patches, charges and local indices -/

section Volume

/-- `λ((R⁻¹ • ·)⁻¹' A) = λ(R • A) = R^{dim E} λ(A)` for **every** set `A` of a
finite-dimensional inner-product space with its inner-product volume. -/
theorem fsimb5d_volume_preimage_inv_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {R : ℝ} (hR : 0 < R) (A : Set E) :
    volume ((fun u : E => R⁻¹ • u) ⁻¹' A) =
      ENNReal.ofReal R ^ Module.finrank ℝ E * volume A := by
  rw [preimage_smul_inv₀ hR.ne', Measure.addHaar_smul_of_nonneg volume hR.le,
    ENNReal.ofReal_pow hR.le]

/-- `λ(B(R p, R ρ)) = R^{dim E} λ(B(p, ρ))`. -/
theorem fsimb5d_volume_ball_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {R : ℝ} (hR : 0 < R) (p : E) (ρ : ℝ) :
    volume (Metric.ball (R • p) (R * ρ)) =
      ENNReal.ofReal R ^ Module.finrank ℝ E * volume (Metric.ball p ρ) := by
  have hball : Metric.ball (R • p) (R * ρ) = R • Metric.ball p ρ := by
    rw [smul_ball hR.ne', Real.norm_eq_abs, abs_of_pos hR]
  rw [hball, Measure.addHaar_smul_of_nonneg volume hR.le, ENNReal.ofReal_pow hR.le]

/-- **Checkpoint 2, base balls.** In the `k`-dimensional direction of a horizontal graph,
`λ(B(R p, R ρ)) = R^k λ(B(p, ρ))`. -/
theorem fsimb5d_volume_ball_graph {n k : ℕ} {ε R : ℝ} (hR : 0 < R) (G : HorizontalGraph n k ε)
    (p : G.direction) (ρ : ℝ) :
    volume (Metric.ball (R • p) (R * ρ)) = ENNReal.ofReal R ^ k * volume (Metric.ball p ρ) := by
  rw [fsimb5d_volume_ball_smul hR, G.rank_eq]

end Volume

section HorizontalPatch

variable {n k : ℕ} {ε : ℝ} (a : Space n) (R : ℝ) (hR : 0 < R) (G : HorizontalGraph n k ε)

/-- The base volume in the transported direction (`finrank = k`):
`λ((R⁻¹ • ·)⁻¹' A) = R^k λ(A)` for every `A`. -/
theorem fsimb5d_volume_preimage_inv_smul_graph
    (A : Set (fsimb5_horizontalGraph a R hR G).direction) :
    volume ((fun u : (fsimb5_horizontalGraph a R hR G).direction => R⁻¹ • u) ⁻¹' A) =
      ENNReal.ofReal R ^ k * volume A := by
  rw [fsimb5d_volume_preimage_inv_smul hR, (fsimb5_horizontalGraph a R hR G).rank_eq]

/-- **Checkpoint 2, trace volumes.** For **every** pair of sets `F`, `U`:
`λ(Φ'⁻¹(S⁻¹' F) ∩ Φ'⁻¹(U)) = R^k λ(Φ⁻¹(F) ∩ Φ⁻¹(S '' U))`. -/
theorem fsimb5d_volume_horizontalPreimage_inter (F U : Set (Space n)) :
    volume (horizontalPreimage (fsimb5_horizontalGraph a R hR G) (similarity a R hR ⁻¹' F) ∩
        horizontalPreimage (fsimb5_horizontalGraph a R hR G) U) =
      ENNReal.ofReal R ^ k *
        volume (horizontalPreimage G F ∩ horizontalPreimage G (similarity a R hR '' U)) := by
  -- Term-mode steps: the two directions are the same submodule only up to unfolding
  -- `fsimb5_horizontalGraph`, so the type-crossing equalities are checked by `isDefEq`.
  have hset : horizontalPreimage (fsimb5_horizontalGraph a R hR G) (similarity a R hR ⁻¹' F) ∩
        horizontalPreimage (fsimb5_horizontalGraph a R hR G) U =
      (fun u : (fsimb5_horizontalGraph a R hR G).direction => R⁻¹ • u) ⁻¹'
        (horizontalPreimage G F ∩ horizontalPreimage G (similarity a R hR '' U)) :=
    (congrArg₂ (· ∩ ·) (fsimb5d_horizontalPreimage_preimage a R hR G F)
      (fsimb5d_horizontalPreimage_image a R hR G U)).trans preimage_inter.symm
  exact (congrArg (fun A => volume A) hset).trans
    (fsimb5d_volume_preimage_inv_smul_graph a R hR G _)

/-- **Checkpoint 2, patches.** `Φ'(R•D ∩ B(R p, R ρ)) = S⁻¹' Φ(D ∩ B(p, ρ))`, with
`D = Φ⁻¹(F)` and `R•D = Φ'⁻¹(S⁻¹' F)`, for every centre `p` and real radius `ρ`. -/
theorem fsimb5d_horizontalPatch (F : Set (Space n)) (p : G.direction) (ρ : ℝ) :
    horizontalPatch (fsimb5_horizontalGraph a R hR G) (similarity a R hR ⁻¹' F) (R • p)
        (R * ρ) =
      similarity a R hR ⁻¹' horizontalPatch G F p ρ := by
  have hset : {u : (fsimb5_horizontalGraph a R hR G).domain |
        (u : (fsimb5_horizontalGraph a R hR G).direction) ∈
          horizontalPreimage (fsimb5_horizontalGraph a R hR G) (similarity a R hR ⁻¹' F) ∩
            Metric.ball (R • p) (R * ρ)} =
      fsimb5d_push a R hR G ''
        {u : G.domain | (u : G.direction) ∈ horizontalPreimage G F ∩ Metric.ball p ρ} := by
    rw [image_eq_preimage_of_inverse (fsimb5d_pull_push a R hR G) (fsimb5d_push_pull a R hR G)]
    ext u
    exact and_congr (Set.ext_iff.mp (fsimb5d_horizontalPreimage_preimage a R hR G F) _)
      (fsimb5d_mem_ball_smul hR _ _ _)
  calc horizontalPatch (fsimb5_horizontalGraph a R hR G) (similarity a R hR ⁻¹' F) (R • p)
        (R * ρ)
      = horizontalGraphMap (fsimb5_horizontalGraph a R hR G) '' (fsimb5d_push a R hR G ''
          {u : G.domain | (u : G.direction) ∈ horizontalPreimage G F ∩ Metric.ball p ρ}) :=
        congrArg (horizontalGraphMap (fsimb5_horizontalGraph a R hR G) '' ·) hset
    _ = (similarity a R hR).symm '' (horizontalGraphMap G ''
          {u : G.domain | (u : G.direction) ∈ horizontalPreimage G F ∩ Metric.ball p ρ}) := by
        rw [image_image, image_image]
        exact image_congr fun u _ => fsimb5d_horizontalGraphMap_push a R hR G u
    _ = similarity a R hR ⁻¹' horizontalPatch G F p ρ :=
        congrFun (Homeomorph.image_symm (similarity a R hR)) _

/-- The patch identity at a transported centre `R p`, `p` in the domain. -/
theorem fsimb5d_horizontalPatch_push (F : Set (Space n)) (u : G.domain) (ρ : ℝ) :
    horizontalPatch (fsimb5_horizontalGraph a R hR G) (similarity a R hR ⁻¹' F)
        (fsimb5d_push a R hR G u : (fsimb5_horizontalGraph a R hR G).domain) (R * ρ) =
      similarity a R hR ⁻¹' horizontalPatch G F u ρ :=
  fsimb5d_horizontalPatch a R hR G F u ρ

/-- Borel patches transfer. -/
theorem fsimb5d_measurableSet_horizontalPatch {F : Set (Space n)} {u : G.domain} {ρ : ℝ}
    (h : MeasurableSet (horizontalPatch G F u ρ)) :
    MeasurableSet (horizontalPatch (fsimb5_horizontalGraph a R hR G) (similarity a R hR ⁻¹' F)
      (fsimb5d_push a R hR G u : (fsimb5_horizontalGraph a R hR G).domain) (R * ρ)) := by
  rw [fsimb5d_horizontalPatch_push]
  exact fsimb5d_measurableSet_preimage a R hR h

end HorizontalPatch

/-! ## The transported horizontal domain data and the three identities -/

section HorizontalData

variable {n k : ℕ} (a : Space n) (R : ℝ) (hR : 0 < R)
  (hH : ∀ A : Set (Space n),
    hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
  {K : Set (Space n)} {ε δ : ℝ} (D : HorizontalDomainData n k ε (δ / R) K)

/-- The transported horizontal domain data of `S⁻¹' K`, with mesh `δ`: the same graph and
patch indices, graphs `fsimb5_horizontalGraph`, traces `S⁻¹' F_j`, centres `R p_α` and radii
`R ρ_α`. -/
def fsimb5d_horizontalData : HorizontalDomainData n k ε δ (similarity a R hR ⁻¹' K) where
  graphIndex := D.graphIndex
  graph j := fsimb5_horizontalGraph a R hR (D.graph j)
  trace j := similarity a R hR ⁻¹' D.trace j
  measurableSet_trace j := fsimb5d_measurableSet_preimage a R hR (D.measurableSet_trace j)
  trace_subset j := fsimb5d_preimage_subset_inter a R hR
    (fsimb5_horizontalGraph_image a R hR (D.graph j)) (D.trace_subset j)
  pairwise_disjoint_trace := fsimb5d_pairwise_disjoint_preimage a R hR D.pairwise_disjoint_trace
  trace_cover :=
    fsimb5d_hausdorffP_diff_iUnion a R hR hH K D.trace _ (fun _ => rfl) D.trace_cover
  measurableSet_tracePreimage j :=
    fsimb5d_measurableSet_horizontalPreimage a R hR (D.graph j) (D.measurableSet_tracePreimage j)
  patchIndex := D.patchIndex
  patchGraph := D.patchGraph
  center α := fsimb5d_push a R hR (D.graph (D.patchGraph α)) (D.center α)
  center_mem_tracePreimage α :=
    fsimb5d_push_mem_horizontalPreimage a R hR (D.graph (D.patchGraph α))
      (D.center_mem_tracePreimage α)
  centerPoint_mem α :=
    fsimb5d_horizontalGraphMap_push_mem a R hR (D.graph (D.patchGraph α)) (D.centerPoint_mem α)
  radius α := R * D.radius α
  radius_pos α := mul_pos hR (D.radius_pos α)
  radius_le α := fsimb5d_mul_le_of_le_div hR (D.radius_le α)
  measurableSet_patch α :=
    fsimb5d_measurableSet_horizontalPatch a R hR (D.graph (D.patchGraph α))
      (D.measurableSet_patch α)
  patch_cover := fsimb5d_hausdorffP_diff_iUnion a R hR hH K
    (fun α => horizontalPatch (D.graph (D.patchGraph α)) (D.trace (D.patchGraph α))
      (D.center α) (D.radius α)) _
    (fun α => fsimb5d_horizontalPatch_push a R hR (D.graph (D.patchGraph α))
      (D.trace (D.patchGraph α)) (D.center α) (D.radius α))
    D.patch_cover

/-- **Identity 1.** `traceVolume' U = R^k traceVolume (S '' U)` for **every** set `U`. -/
theorem fsimb5d_horizontalData_traceVolume (U : Set (Space n)) :
    (fsimb5d_horizontalData a R hR hH D).traceVolume U =
      ENNReal.ofReal R ^ k * D.traceVolume (similarity a R hR '' U) := by
  unfold HorizontalDomainData.traceVolume
  refine fsimb5d_tsum_eq_mul _ _ _ fun j => ?_
  exact fsimb5d_volume_horizontalPreimage_inter a R hR (D.graph j) (D.trace j) U

/-- **Checkpoint 2, charges.** `c'_α = R^k c_α`. -/
theorem fsimb5d_horizontalData_charge (α : D.patchIndex) :
    (fsimb5d_horizontalData a R hR hH D).charge α = ENNReal.ofReal R ^ k * D.charge α := by
  unfold HorizontalDomainData.charge
  refine fsimb5d_charge_scale hR (D.radius α) ?_ ?_
  · exact fsimb5d_volume_ball_graph hR (D.graph (D.patchGraph α)) (D.center α) (D.radius α)
  · exact fsimb5d_hausdorffP_of_eq_preimage a R hR hH
      (fsimb5d_horizontalPatch_push a R hR (D.graph (D.patchGraph α))
        (D.trace (D.patchGraph α)) (D.center α) (D.radius α))

/-- **Identity 2.** `totalCharge' = R^k totalCharge`. -/
theorem fsimb5d_horizontalData_totalCharge :
    (fsimb5d_horizontalData a R hR hH D).totalCharge = ENNReal.ofReal R ^ k * D.totalCharge := by
  unfold HorizontalDomainData.totalCharge
  exact fsimb5d_tsum_eq_mul _ _ _ (fsimb5d_horizontalData_charge a R hR hH D)

/-- Centre points: `z'_α = S.symm z_α`. -/
theorem fsimb5d_horizontalData_centerPoint (α : D.patchIndex) :
    (fsimb5d_horizontalData a R hR hH D).centerPoint α =
      (similarity a R hR).symm (D.centerPoint α) :=
  fsimb5d_horizontalGraphMap_push a R hR (D.graph (D.patchGraph α)) (D.center α)

/-- **Checkpoint 2, local indices.** `I'(q,s) = I(S q, s/R)` for every `q` and real `s`
(same index set, both conditions kept). -/
theorem fsimb5d_horizontalData_localIndex (q : Space n) (s : ℝ) :
    (fsimb5d_horizontalData a R hR hH D).localIndex q s =
      D.localIndex (similarity a R hR q) (s / R) :=
  fsimb5d_localIndex_eq a R hR D.centerPoint (fsimb5d_horizontalData a R hR hH D).centerPoint
    D.radius (fsimb5d_horizontalData a R hR hH D).radius
    (fsimb5d_horizontalData_centerPoint a R hR hH D) (fun _ => rfl) q s

/-- **Identity 3.** `localCharge' q s = R^k localCharge (S q) (s/R)` for every `q` and real
`s`. -/
theorem fsimb5d_horizontalData_localCharge (q : Space n) (s : ℝ) :
    (fsimb5d_horizontalData a R hR hH D).localCharge q s =
      ENNReal.ofReal R ^ k * D.localCharge (similarity a R hR q) (s / R) :=
  fsimb5d_localCharge_eq a R hR D.centerPoint (fsimb5d_horizontalData a R hR hH D).centerPoint
    D.radius (fsimb5d_horizontalData a R hR hH D).radius D.charge
    (fsimb5d_horizontalData a R hR hH D).charge (fsimb5d_horizontalData_centerPoint a R hR hH D)
    (fun _ => rfl) (fsimb5d_horizontalData_charge a R hR hH D) q s

end HorizontalData

/-! ## The statement -/

/-- **Horizontal graph-domain data transported by the similarity**
(`fsim_horizontalDomainData_preimage_similarity`), proved with its exact type: horizontal domain data of `K` with mesh `δ/R` give horizontal domain data of
`S⁻¹' K` with mesh `δ`, with exact trace-volume (every `U`), total-charge and local-charge
(every `q`, every real `s`) identities. -/
theorem fsim_horizontalDomainData_preimage_similarity_proof {n k : ℕ} (a : Space n) (R : ℝ)
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
          ENNReal.ofReal R ^ k * D.localCharge (similarity a R hR q) (s / R) :=
  ⟨fsimb5d_horizontalData a R hR hH D, fsimb5d_horizontalData_traceVolume a R hR hH D,
    fsimb5d_horizontalData_totalCharge a R hR hH D,
    fsimb5d_horizontalData_localCharge a R hR hH D⟩

end ParabolicRectifiability.Foundations
