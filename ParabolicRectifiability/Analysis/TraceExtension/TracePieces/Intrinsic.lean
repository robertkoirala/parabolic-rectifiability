import ParabolicRectifiability.Analysis.TraceExtension.TracePieces.Transport

/-! # Trace pieces on the intrinsic base

The coordinate statements `exists_affine_trace_pieces_coord` (uniform constants) and
`exists_affine_trace_pieces_coord_of_finite_square` (finite square function)
are transported to the intrinsic vertical base `W × Time` with values in `Wᗮ` through the
parabolic isometry `Φ = subspaceParabolicIsometry W`: the trace set `K` becomes `Φ K`, the
trace `f ∘ Φ⁻¹`, the square function and the base-null remainder are preserved
(`traceErrorSq_subspaceParabolicIsometry_proof` and the measure-preserving equivalence), and
the pieces `Φ⁻¹ P_j`, the functions `H_j ∘ Φ` keep compactness, agreement, compact support,
Lipschitz constants and (by `hasAffineCarlesonBound_comp_subspaceParabolicIsometry_proof`)
the affine Carleson constants.

The coordinate statements enter as hypotheses (at the universe of `Wᗮ`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

variable {n : ℕ}

/-- Almost-everywhere statements on `K` transport to `Φ K`. -/
theorem ae_restrict_image_subspaceParabolicIsometry (W : Submodule ℝ (Spatial n))
    (K : Set (SubspaceSpace W)) {P : Space (Module.finrank ℝ W) → Prop}
    (h : ∀ᵐ x ∂(intrinsicParabolicVolume W).restrict K, P (subspaceParabolicIsometry W x)) :
    ∀ᵐ y ∂(parabolicVolume (Module.finrank ℝ W)).restrict (subspaceParabolicIsometry W '' K),
      P y := by
  rw [← map_restrict_subspaceParabolicIsometry W K]
  exact (subspaceParabolicMeasurableEquiv W).measurableEmbedding.ae_map_iff.2 h

/-- Scale integrals of the trace error transport along `Φ`. -/
theorem setLIntegral_traceErrorSq_subspaceParabolicIsometry (W : Submodule ℝ (Spatial n))
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (K : Set (SubspaceSpace W))
    (f : SubspaceSpace W → Y) (x : SubspaceSpace W) (A : Set ℝ) :
    ∫⁻ r in A, traceErrorSq (parabolicVolume (Module.finrank ℝ W))
        (subspaceParabolicIsometry W '' K) (f ∘ (subspaceParabolicIsometry W).symm)
        (subspaceParabolicIsometry W x) r ∂scaleMeasure =
      ∫⁻ r in A, traceErrorSq (intrinsicParabolicVolume W) K f x r ∂scaleMeasure :=
  lintegral_congr fun r => (traceErrorSq_subspaceParabolicIsometry_proof W K f x r).symm

/-- The transported trace data on `Φ K`: compactness, the unit ball and the Lipschitz bound. -/
theorem trace_data_image_subspaceParabolicIsometry (W : Submodule ℝ (Spatial n))
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (K : Set (SubspaceSpace W))
    (f : SubspaceSpace W → Y) (L : ℝ≥0) (hK : IsCompact K)
    (hK₁ : K ⊆ Metric.closedBall
      (((0 : W), Metric.Snowflaking.toSnowflaking (0 : ℝ)) : SubspaceSpace W) 1)
    (hf : LipschitzOnWith L f K) :
    IsCompact (subspaceParabolicIsometry W '' K) ∧
      subspaceParabolicIsometry W '' K ⊆ Metric.closedBall (point 0 0) 1 ∧
      LipschitzOnWith L (f ∘ (subspaceParabolicIsometry W).symm)
        (subspaceParabolicIsometry W '' K) := by
  set Φ := subspaceParabolicIsometry W with hΦ
  refine ⟨hK.image Φ.continuous, ?_, ?_⟩
  · have h0 : Φ ((0 : W), Metric.Snowflaking.toSnowflaking (0 : ℝ)) = point 0 0 := by
      rw [hΦ, subspaceParabolicIsometry_apply, map_zero]
      rfl
    rw [← h0, ← Φ.image_closedBall]
    exact image_mono hK₁
  · refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    simp only [Function.comp_apply, IsometryEquiv.symm_apply_apply, Φ.dist_eq]
    exact hf.dist_le_mul x hx y hy

/-- Coordinate pieces of `Φ K` pull back to intrinsic pieces of `K`. -/
theorem trace_pieces_preimage_subspaceParabolicIsometry (W : Submodule ℝ (Spatial n))
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (K : Set (SubspaceSpace W))
    (f : SubspaceSpace W → Y) {I : Set ℕ} (P : I → Set (Space (Module.finrank ℝ W)))
    (c : I → Y) (H : I → Space (Module.finrank ℝ W) → Y)
    (hP : ∀ j, IsCompact (P j) ∧ P j ⊆ subspaceParabolicIsometry W '' K)
    (hnull : parabolicVolume (Module.finrank ℝ W) (subspaceParabolicIsometry W '' K \ ⋃ j, P j) = 0)
    (hagree : ∀ j, ∀ p ∈ P j, c j + H j p = (f ∘ (subspaceParabolicIsometry W).symm) p) :
    (∀ j, IsCompact (subspaceParabolicIsometry W ⁻¹' P j) ∧
        subspaceParabolicIsometry W ⁻¹' P j ⊆ K) ∧
      intrinsicParabolicVolume W (K \ ⋃ j, subspaceParabolicIsometry W ⁻¹' P j) = 0 ∧
      (∀ j, ∀ p ∈ subspaceParabolicIsometry W ⁻¹' P j,
        c j + (H j ∘ subspaceParabolicIsometry W) p = f p) := by
  set Φ := subspaceParabolicIsometry W with hΦ
  refine ⟨fun j => ⟨Φ.toHomeomorph.isCompact_preimage.2 (hP j).1, fun x hx => ?_⟩, ?_,
    fun j p hp => ?_⟩
  · obtain ⟨y, hy, hyx⟩ := (hP j).2 hx
    rw [← Φ.injective hyx]
    exact hy
  · have hset : K \ ⋃ j, Φ ⁻¹' P j =
        subspaceParabolicMeasurableEquiv W ⁻¹' (Φ '' K \ ⋃ j, P j) := by
      ext x
      change x ∈ K \ ⋃ j, Φ ⁻¹' P j ↔ Φ x ∈ Φ '' K \ ⋃ j, P j
      simp only [Set.mem_sdiff, mem_iUnion, mem_preimage, Φ.injective.mem_set_image]
    rw [hset, (subspaceParabolic_measurePreserving W).measure_preimage_equiv]
    exact hnull
  · have h := hagree j (Φ p) hp
    simp only [Function.comp_apply, IsometryEquiv.symm_apply_apply] at h ⊢
    exact h

/-- A compact support pulls back along `Φ`. -/
theorem hasCompactSupport_comp_subspaceParabolicIsometry (W : Submodule ℝ (Spatial n))
    {Y : Type*} [NormedAddCommGroup Y] {H : Space (Module.finrank ℝ W) → Y}
    (h : HasCompactSupport H) : HasCompactSupport (H ∘ subspaceParabolicIsometry W) :=
  h.comp_homeomorph (subspaceParabolicIsometry W).toHomeomorph

/-- Lipschitz constants of `c + H` pull back along `Φ`. -/
theorem lipschitzWith_add_comp_subspaceParabolicIsometry (W : Submodule ℝ (Spatial n))
    {Y : Type*} [NormedAddCommGroup Y] {c : Y} {H : Space (Module.finrank ℝ W) → Y} {L : ℝ≥0}
    (h : LipschitzWith L (fun p => c + H p)) :
    LipschitzWith L (fun p => c + (H ∘ subspaceParabolicIsometry W) p) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h' := h.dist_le_mul (subspaceParabolicIsometry W x) (subspaceParabolicIsometry W y)
  rw [(subspaceParabolicIsometry W).dist_eq] at h'
  exact h'

/-- **Affine trace pieces on the intrinsic base**, with the conclusion of
`exists_affine_trace_pieces`, from the coordinate statement `hcoord` (the statement of
`exists_affine_trace_pieces_coord`). -/
theorem exists_affine_trace_pieces_proof
    (hcoord : ∀ m d : ℕ, ∃ C : ℝ≥0, 0 < C ∧ ∀ {Y : Type} [NormedAddCommGroup Y]
      [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y], Module.finrank ℝ Y = d →
      ∀ (K : Set (Space m)) (f : Space m → Y) (L : ℝ≥0) (B₀ : ℝ),
        IsCompact K → K ⊆ Metric.closedBall (point 0 0) 1 → LipschitzOnWith L f K → 0 ≤ B₀ →
        (∀ᵐ p ∂(parabolicVolume m).restrict K,
          ∫⁻ r in Ioo 0 2, traceErrorSq (parabolicVolume m) K f p r ∂scaleMeasure ≤
            ENNReal.ofReal B₀) →
        ∃ (I : Set ℕ) (P : I → Set (Space m)) (c : I → Y) (H : I → Space m → Y),
          (∀ j, IsCompact (P j) ∧ P j ⊆ K) ∧ parabolicVolume m (K \ ⋃ j, P j) = 0 ∧
          (∀ j, ∀ p ∈ P j, c j + H j p = f p) ∧ (∀ j, HasCompactSupport (H j)) ∧
          (∀ j, LipschitzWith (C * L) (fun p => c j + H j p)) ∧
          ∀ j, HasAffineCarlesonBound (parabolicVolume m) (H j)
            (((C : ℝ) * ((L : ℝ) + Real.sqrt B₀)) ^ 2))
    (m d : ℕ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ {n : ℕ} (W : Submodule ℝ (Spatial n)),
      Module.finrank ℝ W = m → Module.finrank ℝ W.orthogonal = d →
      ∀ (K : Set (SubspaceSpace W)) (f : SubspaceSpace W → W.orthogonal)
        (L : ℝ≥0) (B₀ : ℝ),
        IsCompact K →
        K ⊆ Metric.closedBall
          (((0 : W), Metric.Snowflaking.toSnowflaking (0 : ℝ)) : SubspaceSpace W) 1 →
        LipschitzOnWith L f K → 0 ≤ B₀ →
        (∀ᵐ p ∂(intrinsicParabolicVolume W).restrict K,
          ∫⁻ r in Ioo 0 2, traceErrorSq (intrinsicParabolicVolume W) K f p r
            ∂scaleMeasure ≤ ENNReal.ofReal B₀) →
        ∃ (I : Set ℕ) (P : I → Set (SubspaceSpace W)) (c : I → W.orthogonal)
          (H : I → SubspaceSpace W → W.orthogonal),
          (∀ j, IsCompact (P j) ∧ P j ⊆ K) ∧
          intrinsicParabolicVolume W (K \ ⋃ j, P j) = 0 ∧
          (∀ j, ∀ p ∈ P j, c j + H j p = f p) ∧
          (∀ j, HasCompactSupport (H j)) ∧
          (∀ j, LipschitzWith (C * L) (fun p => c j + H j p)) ∧
          ∀ j, HasAffineCarlesonBound (intrinsicParabolicVolume W) (H j)
            (((C : ℝ) * ((L : ℝ) + Real.sqrt B₀)) ^ 2) := by
  obtain ⟨C, hC, hT⟩ := hcoord m d
  refine ⟨C, hC, ?_⟩
  intro n W hm hd K f L B₀ hK hK₁ hf hB₀ hS
  subst hm
  obtain ⟨hK', hK'₁, hf'⟩ := trace_data_image_subspaceParabolicIsometry W K f L hK hK₁ hf
  have hS' := ae_restrict_image_subspaceParabolicIsometry W K
    (P := fun y => ∫⁻ r in Ioo 0 2, traceErrorSq (parabolicVolume (Module.finrank ℝ W))
      (subspaceParabolicIsometry W '' K) (f ∘ (subspaceParabolicIsometry W).symm) y r
        ∂scaleMeasure ≤ ENNReal.ofReal B₀)
    (hS.mono fun x hx =>
      (setLIntegral_traceErrorSq_subspaceParabolicIsometry W K f x _).trans_le hx)
  obtain ⟨I, P, c, H, hP, hnull, hagree, hsupp, hlip, hcarl⟩ :=
    hT hd _ _ L B₀ hK' hK'₁ hf' hB₀ hS'
  obtain ⟨hP', hnull', hagree'⟩ :=
    trace_pieces_preimage_subspaceParabolicIsometry W K f P c H hP hnull hagree
  exact ⟨I, fun j => subspaceParabolicIsometry W ⁻¹' P j, c,
    fun j => H j ∘ subspaceParabolicIsometry W, hP', hnull', hagree',
    fun j => hasCompactSupport_comp_subspaceParabolicIsometry W (hsupp j),
    fun j => lipschitzWith_add_comp_subspaceParabolicIsometry W (hlip j),
    fun j => (hasAffineCarlesonBound_comp_subspaceParabolicIsometry_proof W (H j) _).1
      (hcarl j)⟩

/-- **Finite-square form of the affine trace pieces on the intrinsic base**, with the
conclusion of `exists_affine_trace_pieces_of_finite_square`, from the coordinate statement
`hfin` (the statement of `exists_affine_trace_pieces_coord_of_finite_square`). -/
theorem exists_affine_trace_pieces_of_finite_square_proof
    (hfin : ∀ {m : ℕ} {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [FiniteDimensional ℝ Y] (K : Set (Space m)) (f : Space m → Y) (L : ℝ≥0), IsCompact K →
      K ⊆ Metric.closedBall (point 0 0) 1 → LipschitzOnWith L f K →
      (∀ᵐ p ∂(parabolicVolume m).restrict K,
        ∫⁻ r in Ioo 0 2, traceErrorSq (parabolicVolume m) K f p r ∂scaleMeasure < ⊤) →
      ∃ (I : Set ℕ) (P : I → Set (Space m)) (c : I → Y) (H : I → Space m → Y),
        (∀ j, IsCompact (P j) ∧ P j ⊆ K) ∧ parabolicVolume m (K \ ⋃ j, P j) = 0 ∧
        (∀ j, ∀ p ∈ P j, c j + H j p = f p) ∧ (∀ j, HasCompactSupport (H j)) ∧
        ∀ j, ∃ (L' : ℝ≥0) (B : ℝ), LipschitzWith L' (fun p => c j + H j p) ∧
          HasAffineCarlesonBound (parabolicVolume m) (H j) B)
    {n : ℕ} (W : Submodule ℝ (Spatial n)) (K : Set (SubspaceSpace W))
    (f : SubspaceSpace W → W.orthogonal) (L : ℝ≥0) (hK : IsCompact K)
    (hK₁ : K ⊆ Metric.closedBall
          (((0 : W), Metric.Snowflaking.toSnowflaking (0 : ℝ)) : SubspaceSpace W) 1)
    (hf : LipschitzOnWith L f K)
    (hS : ∀ᵐ p ∂(intrinsicParabolicVolume W).restrict K,
      ∫⁻ r in Ioo 0 2, traceErrorSq (intrinsicParabolicVolume W) K f p r
        ∂scaleMeasure < ⊤) :
    ∃ (I : Set ℕ) (P : I → Set (SubspaceSpace W)) (c : I → W.orthogonal)
      (H : I → SubspaceSpace W → W.orthogonal),
      (∀ j, IsCompact (P j) ∧ P j ⊆ K) ∧
      intrinsicParabolicVolume W (K \ ⋃ j, P j) = 0 ∧
      (∀ j, ∀ p ∈ P j, c j + H j p = f p) ∧
      (∀ j, HasCompactSupport (H j)) ∧
      ∀ j, ∃ (L' : ℝ≥0) (B : ℝ), LipschitzWith L' (fun p => c j + H j p) ∧
        HasAffineCarlesonBound (intrinsicParabolicVolume W) (H j) B := by
  obtain ⟨hK', hK'₁, hf'⟩ := trace_data_image_subspaceParabolicIsometry W K f L hK hK₁ hf
  have hS' := ae_restrict_image_subspaceParabolicIsometry W K
    (P := fun y => ∫⁻ r in Ioo 0 2, traceErrorSq (parabolicVolume (Module.finrank ℝ W))
      (subspaceParabolicIsometry W '' K) (f ∘ (subspaceParabolicIsometry W).symm) y r
        ∂scaleMeasure < ⊤)
    (hS.mono fun x hx =>
      (setLIntegral_traceErrorSq_subspaceParabolicIsometry W K f x _).trans_lt hx)
  obtain ⟨I, P, c, H, hP, hnull, hagree, hsupp, hreg⟩ := hfin _ _ L hK' hK'₁ hf' hS'
  obtain ⟨hP', hnull', hagree'⟩ :=
    trace_pieces_preimage_subspaceParabolicIsometry W K f P c H hP hnull hagree
  refine ⟨I, fun j => subspaceParabolicIsometry W ⁻¹' P j, c,
    fun j => H j ∘ subspaceParabolicIsometry W, hP', hnull', hagree',
    fun j => hasCompactSupport_comp_subspaceParabolicIsometry W (hsupp j), fun j => ?_⟩
  obtain ⟨L', B, hlip, hcarl⟩ := hreg j
  exact ⟨L', B, lipschitzWith_add_comp_subspaceParabolicIsometry W hlip,
    (hasAffineCarlesonBound_comp_subspaceParabolicIsometry_proof W (H j) B).1 hcarl⟩

end ParabolicRectifiability
