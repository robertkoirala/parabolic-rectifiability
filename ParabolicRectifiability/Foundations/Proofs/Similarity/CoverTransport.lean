import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Decomposition.Carrier.Transport

/-! # Graph covers transported by a parabolic similarity

Proofs of `fsim_hasHorizontalGraphCover_preimage_similarity` and
`fsim_hasGeneralRegularVerticalGraphCover_preimage_similarity`. Each `<name>_proof` has exactly
the type of the statement.

Notation: `S = similarity a R hR`, so `S.symm (x, t) = (R x + a_x, R² t + a_t)`.

* Horizontal. A graph `G` over `D ⊆ U` is transported to the graph over
  `D' = {u : R⁻¹ u ∈ D} = R • D`, with offset `R a_G + a_x`, normal map `u ↦ R n(R⁻¹ u)` and
  time map `u ↦ R² τ(R⁻¹ u) + a_t`. The slope bound is exact for every real `ε`:
  `max(‖R Δn‖, √(R² |Δτ|)) = R max(‖Δn‖, √|Δτ|) ≤ R ε ‖R⁻¹ Δu‖ = ε ‖Δu‖`. The map
  `u ↦ R u` from `D` onto `D'` gives `image' = S.symm '' image`.
* Vertical. Same direction and rank, offset `R a_G + a_x`, function
  `p ↦ R G(σ p)` with `σ = baseSimilarity W (0, a_t) R`, regular by the hypothesis `hreg`;
  the image identity is `range_similarity_symm_graph`.
* In both cases `S.symm '' Γ = S⁻¹' Γ`, so the new exception is
  `S⁻¹'(K \ ⋃ Γ_i)`, which is `H_P^k`-null by the hypothesis `hH`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Foundations

variable {n k : ℕ} {ε : ℝ}

/-! ## Horizontal graphs -/

/-- The transported domain `{u : R⁻¹ u ∈ D} = R • D`. -/
def fsimb5_hDomain (R : ℝ) (G : HorizontalGraph n k ε) : Set G.direction :=
  {u | R⁻¹ • u ∈ G.domain}

/-- Pull a point of the transported domain back to the original domain: `u ↦ R⁻¹ u`. -/
def fsimb5_hPull (R : ℝ) (G : HorizontalGraph n k ε) (u : fsimb5_hDomain R G) : G.domain :=
  ⟨R⁻¹ • u.1, u.2⟩

/-- Push a point of the original domain to the transported domain: `u ↦ R u`. -/
def fsimb5_hPush (R : ℝ) (hR : 0 < R) (G : HorizontalGraph n k ε) (u : G.domain) :
    fsimb5_hDomain R G :=
  ⟨R • u.1, show R⁻¹ • R • u.1 ∈ G.domain by rw [inv_smul_smul₀ hR.ne']; exact u.2⟩

theorem fsimb5_hPull_hPush (R : ℝ) (hR : 0 < R) (G : HorizontalGraph n k ε) (u : G.domain) :
    fsimb5_hPull R G (fsimb5_hPush R hR G u) = u :=
  Subtype.ext (inv_smul_smul₀ hR.ne' u.1)

theorem fsimb5_hPush_surjective (R : ℝ) (hR : 0 < R) (G : HorizontalGraph n k ε) :
    Function.Surjective (fsimb5_hPush R hR G) := fun w =>
  ⟨fsimb5_hPull R G w, Subtype.ext (smul_inv_smul₀ hR.ne' w.1)⟩

theorem fsimb5_hPull_coe (R : ℝ) (G : HorizontalGraph n k ε) (u : fsimb5_hDomain R G) :
    (((fsimb5_hPull R G u).val : G.direction) : Spatial n) =
      R⁻¹ • ((u.val : G.direction) : Spatial n) :=
  Submodule.coe_smul _ _

/-- The slope bound of the transported graph, exact for every real `ε`. -/
theorem fsimb5_hSlope (R : ℝ) (hR : 0 < R) (G : HorizontalGraph n k ε) (c : ℝ)
    (u v : fsimb5_hDomain R G) :
    max ‖R • G.normal (fsimb5_hPull R G u) - R • G.normal (fsimb5_hPull R G v)‖
        (Real.sqrt |(R ^ 2 * G.time (fsimb5_hPull R G u) + c) -
          (R ^ 2 * G.time (fsimb5_hPull R G v) + c)|) ≤
      ε * ‖((u.val : G.direction) : Spatial n) - ((v.val : G.direction) : Spatial n)‖ := by
  have hs := G.small_slope (fsimb5_hPull R G u) (fsimb5_hPull R G v)
  rw [fsimb5_hPull_coe, fsimb5_hPull_coe, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hR] at hs
  have h1 : ‖R • G.normal (fsimb5_hPull R G u) - R • G.normal (fsimb5_hPull R G v)‖ =
      R * ‖G.normal (fsimb5_hPull R G u) - G.normal (fsimb5_hPull R G v)‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  have h2 : Real.sqrt |(R ^ 2 * G.time (fsimb5_hPull R G u) + c) -
        (R ^ 2 * G.time (fsimb5_hPull R G v) + c)| =
      R * Real.sqrt |G.time (fsimb5_hPull R G u) - G.time (fsimb5_hPull R G v)| := by
    rw [add_sub_add_right_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg R),
      Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR.le]
  rw [h1, h2, ← mul_max_of_nonneg _ _ hR.le]
  calc R * max ‖G.normal (fsimb5_hPull R G u) - G.normal (fsimb5_hPull R G v)‖
          (Real.sqrt |G.time (fsimb5_hPull R G u) - G.time (fsimb5_hPull R G v)|)
      ≤ R * (ε * (R⁻¹ *
          ‖((u.val : G.direction) : Spatial n) - ((v.val : G.direction) : Spatial n)‖)) :=
        mul_le_mul_of_nonneg_left hs hR.le
    _ = ε * ‖((u.val : G.direction) : Spatial n) - ((v.val : G.direction) : Spatial n)‖ := by
        rw [mul_left_comm R ε, ← mul_assoc R R⁻¹, mul_inv_cancel₀ hR.ne', one_mul]

/-- The horizontal graph transported by `S.symm`, `S = similarity a R hR`. -/
def fsimb5_horizontalGraph (a : Space n) (R : ℝ) (hR : 0 < R) (G : HorizontalGraph n k ε) :
    HorizontalGraph n k ε where
  direction := G.direction
  rank_eq := G.rank_eq
  domain := fsimb5_hDomain R G
  offset := R • G.offset + a.1
  normal u := R • G.normal (fsimb5_hPull R G u)
  time u := R ^ 2 * G.time (fsimb5_hPull R G u) + a.2.val
  small_slope u v := fsimb5_hSlope R hR G a.2.val u v

theorem fsimb5_horizontalGraph_image (a : Space n) (R : ℝ) (hR : 0 < R)
    (G : HorizontalGraph n k ε) :
    (fsimb5_horizontalGraph a R hR G).image = (similarity a R hR).symm '' G.image := by
  have hfun : (fun u : fsimb5_hDomain R G =>
        point (R • G.offset + a.1 + ((u.val : G.direction) : Spatial n) +
          ((R • G.normal (fsimb5_hPull R G u) : G.direction.orthogonal) : Spatial n))
          (R ^ 2 * G.time (fsimb5_hPull R G u) + a.2.val)) ∘ fsimb5_hPush R hR G =
      (similarity a R hR).symm ∘ (fun u : G.domain =>
        point (G.offset + ((u.val : G.direction) : Spatial n) + (G.normal u : Spatial n))
          (G.time u)) := by
    funext u
    simp only [Function.comp_apply]
    rw [fsimb5_hPull_hPush, similarity_symm_apply]
    change point (R • G.offset + a.1 + ((R • u.1 : G.direction) : Spatial n) +
        ((R • G.normal u : G.direction.orthogonal) : Spatial n))
        (R ^ 2 * G.time u + a.2.val) =
      point (R • (G.offset + ((u.val : G.direction) : Spatial n) + (G.normal u : Spatial n)) +
        a.1) (R ^ 2 * G.time u + a.2.val)
    congr 1
    rw [Submodule.coe_smul, Submodule.coe_smul, smul_add, smul_add]
    abel
  change Set.range (fun u : fsimb5_hDomain R G =>
        point (R • G.offset + a.1 + ((u.val : G.direction) : Spatial n) +
          ((R • G.normal (fsimb5_hPull R G u) : G.direction.orthogonal) : Spatial n))
          (R ^ 2 * G.time (fsimb5_hPull R G u) + a.2.val)) =
    (similarity a R hR).symm '' Set.range (fun u : G.domain =>
        point (G.offset + ((u.val : G.direction) : Spatial n) + (G.normal u : Spatial n))
          (G.time u))
  rw [← (fsimb5_hPush_surjective R hR G).range_comp, hfun, range_comp]

/-- Horizontal graph covers are transported by the similarity at the same
tolerance. -/
theorem fsim_hasHorizontalGraphCover_preimage_similarity_proof {n k : ℕ} (a : Space n) (R : ℝ)
    (hR : 0 < R)
    (hH : ∀ A : Set (Space n),
      hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
    (K : Set (Space n)) (ε : ℝ) (h : HasHorizontalGraphCover k K ε) :
    HasHorizontalGraphCover k (similarity a R hR ⁻¹' K) ε := by
  obtain ⟨I, G, hnull⟩ := h
  refine ⟨I, fun i => fsimb5_horizontalGraph a R hR (G i), ?_⟩
  have hset : similarity a R hR ⁻¹' K \ ⋃ i, (fsimb5_horizontalGraph a R hR (G i)).image =
      similarity a R hR ⁻¹' (K \ ⋃ i, (G i).image) := by
    simp only [fsimb5_horizontalGraph_image, Homeomorph.image_symm, preimage_sdiff,
      preimage_iUnion]
  rw [hset, hH, hnull, mul_zero]

/-! ## General regular vertical graphs -/

/-- The general regular vertical graph transported by `S.symm`: offset `R a_G + a_x`,
function `p ↦ R G(σ p)`, `σ = baseSimilarity W (0, a_t) R`, regular by `hreg`. -/
def fsimb5_verticalGraph (a : Space n) (R : ℝ)
    (hreg : ∀ (W : Submodule ℝ (Spatial n)) (F : SubspaceSpace W → W.orthogonal) (ε : ℝ),
      IsGeneralRegularVerticalFunction W F ε →
        IsGeneralRegularVerticalFunction W
          (fun p => R • F (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking a.2.val) R p))
          ε)
    (G : GeneralRegularVerticalGraph n k ε) : GeneralRegularVerticalGraph n k ε where
  vertical_dimension := G.vertical_dimension
  direction := G.direction
  rank_eq := G.rank_eq
  offset := R • G.offset + a.1
  function p := R • G.function
    (baseSimilarity G.direction ((0 : G.direction), Metric.Snowflaking.toSnowflaking a.2.val) R p)
  regular := hreg G.direction G.function ε G.regular

theorem fsimb5_verticalGraph_image (a : Space n) (R : ℝ) (hR : 0 < R)
    (hreg : ∀ (W : Submodule ℝ (Spatial n)) (F : SubspaceSpace W → W.orthogonal) (ε : ℝ),
      IsGeneralRegularVerticalFunction W F ε →
        IsGeneralRegularVerticalFunction W
          (fun p => R • F (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking a.2.val) R p))
          ε)
    (G : GeneralRegularVerticalGraph n k ε) :
    (fsimb5_verticalGraph a R hreg G).image = (similarity a R hR).symm '' G.image :=
  range_similarity_symm_graph G.direction G.offset G.function a R hR

/-- General regular vertical graph covers are transported by the similarity at the
same tolerance. -/
theorem fsim_hasGeneralRegularVerticalGraphCover_preimage_similarity_proof {n k : ℕ}
    (a : Space n) (R : ℝ) (hR : 0 < R)
    (hH : ∀ A : Set (Space n),
      hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
    (hreg : ∀ (W : Submodule ℝ (Spatial n)) (F : SubspaceSpace W → W.orthogonal) (ε : ℝ),
      IsGeneralRegularVerticalFunction W F ε →
        IsGeneralRegularVerticalFunction W
          (fun p => R • F (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking a.2.val) R p))
          ε)
    (K : Set (Space n)) (ε : ℝ) (h : HasGeneralRegularVerticalGraphCover k K ε) :
    HasGeneralRegularVerticalGraphCover k (similarity a R hR ⁻¹' K) ε := by
  obtain ⟨I, G, hnull⟩ := h
  refine ⟨I, fun i => fsimb5_verticalGraph a R hreg (G i), ?_⟩
  have hset : similarity a R hR ⁻¹' K \ ⋃ i, (fsimb5_verticalGraph a R hreg (G i)).image =
      similarity a R hR ⁻¹' (K \ ⋃ i, (G i).image) := by
    simp only [fsimb5_verticalGraph_image a R hR hreg, Homeomorph.image_symm, preimage_sdiff,
      preimage_iUnion]
  rw [hset, hH, hnull, mul_zero]

end ParabolicRectifiability.Foundations
