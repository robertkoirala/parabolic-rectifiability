import ParabolicRectifiability.Foundations.GraphDomainCover
import ParabolicRectifiability.Foundations.Proofs.Similarity.CoverTransport
import ParabolicRectifiability.Foundations.Proofs.Similarity.DomainDataTransport
import ParabolicRectifiability.Decomposition.Carrier.Transport
import ParabolicRectifiability.Metric.Similarity

/-! # Vertical graph-domain data transported by a parabolic similarity

Proof of `fsim_verticalDomainData_preimage_similarity`.
`fsim_verticalDomainData_preimage_similarity_proof` has exactly the type of the statement.

Notation: `S = similarity a R hR`, `S.symm (x, t) = (R x + a_x, R² t + a_t)`; for a general
regular vertical graph `G`, `G' = fsimb5_verticalGraph a R hreg G` is the proved transported
graph (same direction `W` and rank, offset `R a_G + a_x`, function `R • G ∘ σ`); `Φ = G.map`,
`Φ' = G'.map` are the graph maps on the whole bases `W × ℝ`.

* **The base maps.** `σ = baseSimilarityHomeomorph W (0, a_t) R`, `σ(u,t) = (u/R, (t-a_t)/R²)`
  (centre `(0, a_t)`, exactly the centre of `hreg` and of `fsimb5_verticalGraph`), viewed as a
  homeomorphism from the transported base onto the original base, and `β = σ.symm`,
  `β(u,t) = (R u, R² t + a_t)`.
* **Checkpoint 1.** `Φ'(p) = S.symm (Φ (σ p))`, hence `Φ'(β p) = S.symm (Φ p)`, and the
  preimages `Φ'⁻¹(T) = σ⁻¹' Φ⁻¹(S.symm⁻¹' T)`, so `Φ'⁻¹(S⁻¹' F) = σ⁻¹' Φ⁻¹(F) = β '' Φ⁻¹(F)`
  and `Φ'⁻¹(U) = σ⁻¹' Φ⁻¹(S '' U)` for **every** set `U`.
* **Checkpoint 2.** The intrinsic volume: `λ'(σ⁻¹' A) = (σ_* λ)(A) = R^{dim W + 2} λ(A) = R^k λ(A)`
  for **every** set `A` (`map_baseSimilarityHomeomorph`, `MeasurableEmbedding.map_apply`,
  `rank_eq`; this includes `dim W = 0`, `k = 2`). Balls: `σ⁻¹' B(p, ρ) = B(β p, R ρ)`
  (`dist_baseSimilarity`), so the **whole-ball** patch is
  `Φ'(B(β p, R ρ)) = S.symm '' Φ(B(p, ρ)) = S⁻¹' Φ(B(p, ρ))`. Charges `c'_α = R^k c_α`, local
  index sets `I'(q,s) = I(S q, s/R)` (the horizontal bookkeeping `fsimb5d_localCharge_eq`).

No measurability of the testing set `U` is used. For `s ≤ 0` both local index sets are empty
(the index identity holds for every real `s`). A nonpositive mesh gives empty patch families
automatically: the patch indices are the given ones.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Foundations

/-! ## Checkpoint 1: the base maps, the graph-map identity and the preimage identities -/

section VerticalGraph

variable {n k : ℕ} {ε : ℝ} (a : Space n) (R : ℝ) (hR : 0 < R)
  (hreg : ∀ (W : Submodule ℝ (Spatial n)) (F : SubspaceSpace W → W.orthogonal) (ε : ℝ),
    IsGeneralRegularVerticalFunction W F ε →
      IsGeneralRegularVerticalFunction W
        (fun p => R • F (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking a.2.val) R p))
        ε)
  (G : GeneralRegularVerticalGraph n k ε)

/-- The base similarity `σ = baseSimilarity W (0, a_t) R`, `σ(u,t) = (u/R, (t-a_t)/R²)`, as a
homeomorphism from the base of the transported graph onto the base of `G` (the same space
`W × ℝ`). Its inverse is `β(u,t) = (R u, R² t + a_t)`. -/
def fsimb6d_sigma :
    SubspaceSpace (fsimb5_verticalGraph a R hreg G).direction ≃ₜ SubspaceSpace G.direction :=
  baseSimilarityHomeomorph G.direction ((0 : G.direction), Metric.Snowflaking.toSnowflaking a.2.val)
    R hR

theorem fsimb6d_sigma_apply (p : SubspaceSpace (fsimb5_verticalGraph a R hreg G).direction) :
    fsimb6d_sigma a R hR hreg G p =
      baseSimilarity G.direction ((0 : G.direction), Metric.Snowflaking.toSnowflaking a.2.val) R p :=
  baseSimilarityHomeomorph_apply G.direction _ R hR p

/-- `σ` multiplies distances by `R⁻¹` (`dist_baseSimilarity`). -/
theorem fsimb6d_dist_sigma (x y : SubspaceSpace (fsimb5_verticalGraph a R hreg G).direction) :
    dist (fsimb6d_sigma a R hR hreg G x) (fsimb6d_sigma a R hR hreg G y) = R⁻¹ * dist x y := by
  rw [fsimb6d_sigma_apply, fsimb6d_sigma_apply]
  exact dist_baseSimilarity G.direction _ R hR x y

/-- The graph-map computation on the original base (stated without transported types): the
unfolded transported graph map at `p` is `S.symm (Φ (σ p))`. The time coordinate is
`R² ((t - a_t)/R²) + a_t = t` (translation sign of `S.symm` and of the centre `(0, a_t)`). -/
theorem fsimb6d_map_aux (p : SubspaceSpace G.direction) :
    ((R • G.offset + a.1 + (p.1 : Spatial n) +
        ((R • G.function (baseSimilarity G.direction
          ((0 : G.direction), Metric.Snowflaking.toSnowflaking a.2.val) R p) :
            G.direction.orthogonal) : Spatial n), p.2) : Space n) =
      (similarity a R hR).symm (G.map (baseSimilarity G.direction
        ((0 : G.direction), Metric.Snowflaking.toSnowflaking a.2.val) R p)) := by
  rw [similarity_symm_apply]
  rcases p with ⟨u, ⟨t⟩⟩
  refine Prod.ext ?_ ?_
  · show R • G.offset + a.1 + (u : Spatial n) +
        ((R • G.function (baseSimilarity G.direction
          ((0 : G.direction), Metric.Snowflaking.toSnowflaking a.2.val) R
            (u, Metric.Snowflaking.toSnowflaking t)) :
              G.direction.orthogonal) : Spatial n) =
      R • (G.offset + ((R⁻¹ • (u - 0) : G.direction) : Spatial n) +
        (G.function (baseSimilarity G.direction
          ((0 : G.direction), Metric.Snowflaking.toSnowflaking a.2.val) R
            (u, Metric.Snowflaking.toSnowflaking t)) : Spatial n)) + a.1
    simp only [sub_zero, Submodule.coe_smul, smul_add, smul_smul, mul_inv_cancel₀ hR.ne',
      one_smul]
    abel
  · show (Metric.Snowflaking.toSnowflaking t : Time) =
      Metric.Snowflaking.toSnowflaking (R ^ 2 * (R⁻¹ ^ 2 * (t - a.2.val)) + a.2.val)
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hR.ne', one_pow, one_mul, sub_add_cancel]

/-- **Checkpoint 1, graph maps.** `Φ'(p) = S.symm (Φ (σ p))` on the whole base. -/
theorem fsimb6d_map (p : SubspaceSpace (fsimb5_verticalGraph a R hreg G).direction) :
    (fsimb5_verticalGraph a R hreg G).map p =
      (similarity a R hR).symm (G.map (fsimb6d_sigma a R hR hreg G p)) := by
  rw [fsimb6d_sigma_apply]
  -- The transported graph map unfolds to the left side of `fsimb6d_map_aux` (same submodule).
  exact fsimb6d_map_aux a R hR G p

/-- **Checkpoint 1, graph maps at transported centres.** `Φ'(β p) = S.symm (Φ p)`. -/
theorem fsimb6d_map_symm (p : SubspaceSpace G.direction) :
    (fsimb5_verticalGraph a R hreg G).map ((fsimb6d_sigma a R hR hreg G).symm p) =
      (similarity a R hR).symm (G.map p) := by
  rw [fsimb6d_map a R hR hreg G, Homeomorph.apply_symm_apply]

/-- The graph-map identity on centres: `Φ p ∈ K ⇒ Φ'(β p) ∈ S⁻¹' K`. -/
theorem fsimb6d_map_symm_mem {K : Set (Space n)} {p : SubspaceSpace G.direction}
    (hp : G.map p ∈ K) :
    (fsimb5_verticalGraph a R hreg G).map ((fsimb6d_sigma a R hR hreg G).symm p) ∈
      similarity a R hR ⁻¹' K := by
  rw [fsimb6d_map_symm]
  exact (fsimb5d_symm_mem_preimage_iff a R hR K _).mpr hp

/-- The preimage identity `Φ'⁻¹(T) = σ⁻¹' Φ⁻¹(S.symm⁻¹' T)` for every set `T`. -/
theorem fsimb6d_map_preimage (T : Set (Space n)) :
    (fsimb5_verticalGraph a R hreg G).map ⁻¹' T =
      fsimb6d_sigma a R hR hreg G ⁻¹' (G.map ⁻¹' ((similarity a R hR).symm ⁻¹' T)) := by
  ext p
  rw [mem_preimage, fsimb6d_map a R hR hreg G p]
  rfl

/-- **Checkpoint 1, trace preimages.** `Φ'⁻¹(S⁻¹' F) = σ⁻¹' Φ⁻¹(F)` `(= β '' Φ⁻¹(F))`. -/
theorem fsimb6d_map_preimage_preimage (F : Set (Space n)) :
    (fsimb5_verticalGraph a R hreg G).map ⁻¹' (similarity a R hR ⁻¹' F) =
      fsimb6d_sigma a R hR hreg G ⁻¹' (G.map ⁻¹' F) := by
  rw [fsimb6d_map_preimage a R hR hreg G, Homeomorph.preimage_symm, Homeomorph.image_preimage]

/-- **Checkpoint 1, testing sets.** `Φ'⁻¹(U) = σ⁻¹' Φ⁻¹(S '' U)` for **every** set `U`. -/
theorem fsimb6d_map_preimage_image (U : Set (Space n)) :
    (fsimb5_verticalGraph a R hreg G).map ⁻¹' U =
      fsimb6d_sigma a R hR hreg G ⁻¹' (G.map ⁻¹' (similarity a R hR '' U)) := by
  rw [fsimb6d_map_preimage a R hR hreg G, Homeomorph.preimage_symm]

/-- Borel trace preimages transfer: `Φ⁻¹(F)` Borel `⇒ Φ'⁻¹(S⁻¹' F) = σ⁻¹' Φ⁻¹(F)` Borel. -/
theorem fsimb6d_measurableSet_map_preimage {F : Set (Space n)}
    (hF : MeasurableSet (G.map ⁻¹' F)) :
    MeasurableSet ((fsimb5_verticalGraph a R hreg G).map ⁻¹' (similarity a R hR ⁻¹' F)) := by
  rw [fsimb6d_map_preimage_preimage a R hR hreg G]
  exact hF.preimage (fsimb6d_sigma a R hR hreg G).measurable

/-- Patch centres transfer: `p ∈ Φ⁻¹(F) ⇒ β p ∈ Φ'⁻¹(S⁻¹' F)`. -/
theorem fsimb6d_symm_mem_map_preimage {F : Set (Space n)} {p : SubspaceSpace G.direction}
    (hp : p ∈ G.map ⁻¹' F) :
    (fsimb6d_sigma a R hR hreg G).symm p ∈
      (fsimb5_verticalGraph a R hreg G).map ⁻¹' (similarity a R hR ⁻¹' F) := by
  rw [mem_preimage, fsimb6d_map_symm]
  exact (fsimb5d_symm_mem_preimage_iff a R hR F _).mpr hp

end VerticalGraph

/-! ## Checkpoint 2: intrinsic volumes, whole-ball patches -/

section VerticalPatch

variable {n k : ℕ} {ε : ℝ} (a : Space n) (R : ℝ) (hR : 0 < R)
  (hreg : ∀ (W : Submodule ℝ (Spatial n)) (F : SubspaceSpace W → W.orthogonal) (ε : ℝ),
    IsGeneralRegularVerticalFunction W F ε →
      IsGeneralRegularVerticalFunction W
        (fun p => R • F (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking a.2.val) R p))
        ε)
  (G : GeneralRegularVerticalGraph n k ε)

/-- **Checkpoint 2, base volume.** `λ'(σ⁻¹' A) = R^k λ(A)` for **every** set `A`: the
pushforward `σ_* λ = R^{dim W + 2} λ` (`map_baseSimilarityHomeomorph`) evaluated through the
measurable embedding `σ`, and `dim W + 2 = k` (`rank_eq`, including `dim W = 0`). -/
theorem fsimb6d_volume_preimage_sigma (A : Set (SubspaceSpace G.direction)) :
    intrinsicParabolicVolume (fsimb5_verticalGraph a R hreg G).direction
        (fsimb6d_sigma a R hR hreg G ⁻¹' A) =
      ENNReal.ofReal R ^ k * intrinsicParabolicVolume G.direction A := by
  have h1 : intrinsicParabolicVolume (fsimb5_verticalGraph a R hreg G).direction
        (fsimb6d_sigma a R hR hreg G ⁻¹' A) =
      Measure.map (baseSimilarityHomeomorph G.direction
          ((0 : G.direction), Metric.Snowflaking.toSnowflaking a.2.val) R hR)
        (intrinsicParabolicVolume G.direction) A :=
    ((baseSimilarityHomeomorph G.direction
      ((0 : G.direction), Metric.Snowflaking.toSnowflaking a.2.val) R hR).measurableEmbedding.map_apply
        _ A).symm
  rw [h1, map_baseSimilarityHomeomorph, Measure.smul_apply, smul_eq_mul, G.rank_eq]

/-- `σ⁻¹' B(p, ρ) = B(β p, R ρ)` in the max parabolic metric, for every real `ρ`. -/
theorem fsimb6d_preimage_ball (p : SubspaceSpace G.direction) (ρ : ℝ) :
    fsimb6d_sigma a R hR hreg G ⁻¹' Metric.ball p ρ =
      Metric.ball ((fsimb6d_sigma a R hR hreg G).symm p) (R * ρ) := by
  ext x
  have h := fsimb6d_dist_sigma a R hR hreg G x ((fsimb6d_sigma a R hR hreg G).symm p)
  rw [Homeomorph.apply_symm_apply] at h
  rw [mem_preimage, Metric.mem_ball, Metric.mem_ball, h, inv_mul_lt_iff₀ hR]

/-- `β '' B(p, ρ) = B(β p, R ρ)`. -/
theorem fsimb6d_image_ball (p : SubspaceSpace G.direction) (ρ : ℝ) :
    (fsimb6d_sigma a R hR hreg G).symm '' Metric.ball p ρ =
      Metric.ball ((fsimb6d_sigma a R hR hreg G).symm p) (R * ρ) := by
  rw [Homeomorph.image_symm, fsimb6d_preimage_ball]

/-- **Checkpoint 2, base balls.** `λ'(B(β p, R ρ)) = R^k λ(B(p, ρ))`. -/
theorem fsimb6d_volume_ball (p : SubspaceSpace G.direction) (ρ : ℝ) :
    intrinsicParabolicVolume (fsimb5_verticalGraph a R hreg G).direction
        (Metric.ball ((fsimb6d_sigma a R hR hreg G).symm p) (R * ρ)) =
      ENNReal.ofReal R ^ k * intrinsicParabolicVolume G.direction (Metric.ball p ρ) := by
  rw [← fsimb6d_preimage_ball, fsimb6d_volume_preimage_sigma]

/-- **Checkpoint 2, trace volumes.** For **every** pair of sets `F`, `U`:
`λ'(Φ'⁻¹(S⁻¹' F) ∩ Φ'⁻¹(U)) = R^k λ(Φ⁻¹(F) ∩ Φ⁻¹(S '' U))`. -/
theorem fsimb6d_volume_map_preimage_inter (F U : Set (Space n)) :
    intrinsicParabolicVolume (fsimb5_verticalGraph a R hreg G).direction
        ((fsimb5_verticalGraph a R hreg G).map ⁻¹' (similarity a R hR ⁻¹' F) ∩
          (fsimb5_verticalGraph a R hreg G).map ⁻¹' U) =
      ENNReal.ofReal R ^ k * intrinsicParabolicVolume G.direction
        (G.map ⁻¹' F ∩ G.map ⁻¹' (similarity a R hR '' U)) := by
  rw [fsimb6d_map_preimage_preimage a R hR hreg G, fsimb6d_map_preimage_image a R hR hreg G,
    ← preimage_inter, fsimb6d_volume_preimage_sigma]

/-- **Checkpoint 2, whole-ball patches.** `Φ'(B(β p, R ρ)) = S⁻¹' Φ(B(p, ρ))` for every centre
`p` and real radius `ρ`. -/
theorem fsimb6d_verticalPatch (p : SubspaceSpace G.direction) (ρ : ℝ) :
    verticalPatch (fsimb5_verticalGraph a R hreg G) ((fsimb6d_sigma a R hR hreg G).symm p)
        (R * ρ) =
      similarity a R hR ⁻¹' verticalPatch G p ρ := by
  unfold verticalPatch
  rw [← fsimb6d_image_ball a R hR hreg G, image_image,
    ← Homeomorph.image_symm (similarity a R hR), image_image]
  exact image_congr fun x _ => fsimb6d_map_symm a R hR hreg G x

/-- Borel patches transfer. -/
theorem fsimb6d_measurableSet_verticalPatch {p : SubspaceSpace G.direction} {ρ : ℝ}
    (h : MeasurableSet (verticalPatch G p ρ)) :
    MeasurableSet (verticalPatch (fsimb5_verticalGraph a R hreg G)
      ((fsimb6d_sigma a R hR hreg G).symm p) (R * ρ)) := by
  rw [fsimb6d_verticalPatch]
  exact fsimb5d_measurableSet_preimage a R hR h

end VerticalPatch

/-! ## The transported vertical domain data and the three identities -/

section VerticalData

variable {n k : ℕ} (a : Space n) (R : ℝ) (hR : 0 < R)
  (hH : ∀ A : Set (Space n),
    hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
  (hreg : ∀ (W : Submodule ℝ (Spatial n)) (F : SubspaceSpace W → W.orthogonal) (ε : ℝ),
    IsGeneralRegularVerticalFunction W F ε →
      IsGeneralRegularVerticalFunction W
        (fun p => R • F (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking a.2.val) R p))
        ε)
  {K : Set (Space n)} {ε δ : ℝ} (D : VerticalDomainData n k ε (δ / R) K)

/-- The transported vertical domain data of `S⁻¹' K`, with mesh `δ`: the same graph and patch
indices, graphs `fsimb5_verticalGraph`, traces `S⁻¹' F_j`, centres `β p_α` and radii `R ρ_α`;
the patches are whole base balls. -/
def fsimb6d_verticalData : VerticalDomainData n k ε δ (similarity a R hR ⁻¹' K) where
  graphIndex := D.graphIndex
  graph j := fsimb5_verticalGraph a R hreg (D.graph j)
  trace j := similarity a R hR ⁻¹' D.trace j
  measurableSet_trace j := fsimb5d_measurableSet_preimage a R hR (D.measurableSet_trace j)
  trace_subset j := fsimb5d_preimage_subset_inter a R hR
    (fsimb5_verticalGraph_image a R hR hreg (D.graph j)) (D.trace_subset j)
  pairwise_disjoint_trace := fsimb5d_pairwise_disjoint_preimage a R hR D.pairwise_disjoint_trace
  trace_cover :=
    fsimb5d_hausdorffP_diff_iUnion a R hR hH K D.trace _ (fun _ => rfl) D.trace_cover
  measurableSet_tracePreimage j :=
    fsimb6d_measurableSet_map_preimage a R hR hreg (D.graph j) (D.measurableSet_tracePreimage j)
  patchIndex := D.patchIndex
  patchGraph := D.patchGraph
  center α := (fsimb6d_sigma a R hR hreg (D.graph (D.patchGraph α))).symm (D.center α)
  center_mem_tracePreimage α :=
    fsimb6d_symm_mem_map_preimage a R hR hreg (D.graph (D.patchGraph α))
      (D.center_mem_tracePreimage α)
  centerPoint_mem α :=
    fsimb6d_map_symm_mem a R hR hreg (D.graph (D.patchGraph α)) (D.centerPoint_mem α)
  radius α := R * D.radius α
  radius_pos α := mul_pos hR (D.radius_pos α)
  radius_le α := fsimb5d_mul_le_of_le_div hR (D.radius_le α)
  measurableSet_patch α :=
    fsimb6d_measurableSet_verticalPatch a R hR hreg (D.graph (D.patchGraph α))
      (D.measurableSet_patch α)
  patch_cover := fsimb5d_hausdorffP_diff_iUnion a R hR hH K
    (fun α => verticalPatch (D.graph (D.patchGraph α)) (D.center α) (D.radius α)) _
    (fun α => fsimb6d_verticalPatch a R hR hreg (D.graph (D.patchGraph α)) (D.center α)
      (D.radius α))
    D.patch_cover

/-- **Identity 1.** `traceVolume' U = R^k traceVolume (S '' U)` for **every** set `U`. -/
theorem fsimb6d_verticalData_traceVolume (U : Set (Space n)) :
    (fsimb6d_verticalData a R hR hH hreg D).traceVolume U =
      ENNReal.ofReal R ^ k * D.traceVolume (similarity a R hR '' U) := by
  unfold VerticalDomainData.traceVolume
  refine fsimb5d_tsum_eq_mul _ _ _ fun j => ?_
  exact fsimb6d_volume_map_preimage_inter a R hR hreg (D.graph j) (D.trace j) U

/-- **Checkpoint 2, charges.** `c'_α = R^k c_α`. -/
theorem fsimb6d_verticalData_charge (α : D.patchIndex) :
    (fsimb6d_verticalData a R hR hH hreg D).charge α = ENNReal.ofReal R ^ k * D.charge α := by
  unfold VerticalDomainData.charge
  refine fsimb5d_charge_scale hR (D.radius α) ?_ ?_
  · exact fsimb6d_volume_ball a R hR hreg (D.graph (D.patchGraph α)) (D.center α) (D.radius α)
  · exact fsimb5d_hausdorffP_of_eq_preimage a R hR hH
      (fsimb6d_verticalPatch a R hR hreg (D.graph (D.patchGraph α)) (D.center α) (D.radius α))

/-- **Identity 2.** `totalCharge' = R^k totalCharge`. -/
theorem fsimb6d_verticalData_totalCharge :
    (fsimb6d_verticalData a R hR hH hreg D).totalCharge =
      ENNReal.ofReal R ^ k * D.totalCharge := by
  unfold VerticalDomainData.totalCharge
  exact fsimb5d_tsum_eq_mul _ _ _ (fsimb6d_verticalData_charge a R hR hH hreg D)

/-- Centre points: `z'_α = Φ'(β p_α) = S.symm z_α`. -/
theorem fsimb6d_verticalData_centerPoint (α : D.patchIndex) :
    (fsimb6d_verticalData a R hR hH hreg D).centerPoint α =
      (similarity a R hR).symm (D.centerPoint α) :=
  fsimb6d_map_symm a R hR hreg (D.graph (D.patchGraph α)) (D.center α)

/-- **Local indices.** `I'(q,s) = I(S q, s/R)` for every `q` and real `s` (same index set,
both conditions kept). -/
theorem fsimb6d_verticalData_localIndex (q : Space n) (s : ℝ) :
    (fsimb6d_verticalData a R hR hH hreg D).localIndex q s =
      D.localIndex (similarity a R hR q) (s / R) :=
  fsimb5d_localIndex_eq a R hR D.centerPoint (fsimb6d_verticalData a R hR hH hreg D).centerPoint
    D.radius (fsimb6d_verticalData a R hR hH hreg D).radius
    (fsimb6d_verticalData_centerPoint a R hR hH hreg D) (fun _ => rfl) q s

/-- **Identity 3.** `localCharge' q s = R^k localCharge (S q) (s/R)` for every `q` and real
`s`. -/
theorem fsimb6d_verticalData_localCharge (q : Space n) (s : ℝ) :
    (fsimb6d_verticalData a R hR hH hreg D).localCharge q s =
      ENNReal.ofReal R ^ k * D.localCharge (similarity a R hR q) (s / R) :=
  fsimb5d_localCharge_eq a R hR D.centerPoint (fsimb6d_verticalData a R hR hH hreg D).centerPoint
    D.radius (fsimb6d_verticalData a R hR hH hreg D).radius D.charge
    (fsimb6d_verticalData a R hR hH hreg D).charge
    (fsimb6d_verticalData_centerPoint a R hR hH hreg D)
    (fun _ => rfl) (fsimb6d_verticalData_charge a R hR hH hreg D) q s

end VerticalData

/-! ## The statement -/

/-- **Vertical graph-domain data transported by the similarity**
(`fsim_verticalDomainData_preimage_similarity`), proved with its exact type: general regular vertical domain data of `K` with mesh `δ/R` give vertical domain
data of `S⁻¹' K` with mesh `δ`, with exact trace-volume (every `U`), total-charge and
local-charge (every `q`, every real `s`) identities. -/
theorem fsim_verticalDomainData_preimage_similarity_proof {n k : ℕ} (a : Space n) (R : ℝ)
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
          ENNReal.ofReal R ^ k * D.localCharge (similarity a R hR q) (s / R) :=
  ⟨fsimb6d_verticalData a R hR hH hreg D, fsimb6d_verticalData_traceVolume a R hR hH hreg D,
    fsimb6d_verticalData_totalCharge a R hR hH hreg D,
    fsimb6d_verticalData_localCharge a R hR hH hreg D⟩

end ParabolicRectifiability.Foundations
