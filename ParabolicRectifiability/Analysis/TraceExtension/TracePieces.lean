import ParabolicRectifiability.Analysis.TraceExtension.TracePieces.Piece
import ParabolicRectifiability.Analysis.TraceExtension.TracePieces.Measurability
import ParabolicRectifiability.Analysis.TraceExtension.TracePieces.Intrinsic
import ParabolicRectifiability.Analysis.TraceExtension.DensityTracePieces

/-! # Affine trace pieces

The decomposition of a trace set into compact pieces carrying affine perturbations, in
ordinary coordinates.

* `exists_affine_trace_pieces_coord_proof`: the density localization of `DensityTracePieces`, applied
  with the good set `{S_K ≤ B₀}` of the trace square function, gives compact pieces
  `P_j ⊆ K ∩ {S_K ≤ B₀} ∩ P̄(x_j,ρ_j)` covering `K` up to a null set. An empty piece gets the
  zero perturbation; a nonempty piece is extended by `exists_trace_piece_extension`. The
  index set of the localization already is a countable subset of `ℕ`.
* `exists_affine_trace_pieces_coord_of_finite_square_proof`: the square function `S_K` is
  measurable (`measurable_traceErrorSq_of_isCompact_proof`), so the levels
  `K ∩ {S_K ≤ N}` are measurable; inner regularity gives compact `Q_{N,i}` inside them
  exhausting them up to null sets. Restriction monotonicity gives `S_{Q_{N,i}} ≤ S_K ≤ N`
  on `Q_{N,i}`, so the first statement applies with `B₀ = N`; the countable triple index `(N,i,j)` is
  reindexed through a bijection with a subset of `ℕ` (`exists_setNat_equiv_of_countable`).
  Points with `S_K = ∞` form a null set.

The compact cutoff and the source extension (for the first statement), and the first
statement itself (for the second), enter as hypotheses.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

universe u

/-- **Affine trace pieces in ordinary coordinates**, with the conclusion of
`exists_affine_trace_pieces_coord`, from the compact cutoff `hcut` (the statement of
`exists_compact_cutoff_affineCarleson`) and the source extension `hext` (the statement of
`exists_affine_extension_of_source`). -/
theorem exists_affine_trace_pieces_coord_proof
    (hcut : ∀ m : ℕ, ∃ C : ℝ≥0, 0 < C ∧ ∀ {Y : Type u} [NormedAddCommGroup Y]
      [InnerProductSpace ℝ Y] (F : Space m → Y) (L : ℝ≥0) (B : ℝ), LipschitzWith L F →
      HasAffineCarlesonBound (parabolicVolume m) F B →
      ∀ (z₀ : Space m) (R₀ : ℝ), 0 < R₀ →
        ∃ (c : Y) (H : Space m → Y), (∀ p ∈ Metric.ball z₀ R₀, c + H p = F p) ∧
          HasCompactSupport H ∧ LipschitzWith (C * L) (fun p => c + H p) ∧
          HasAffineCarlesonBound (parabolicVolume m) H (C * (B + (L : ℝ) ^ 2)))
    (hext : ∀ (m : ℕ) (c : ℝ), 0 < c →
      ∃ C : ℝ≥0, 0 < C ∧ ∀ {Y : Type u} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [FiniteDimensional ℝ Y] (F₀ : Set (Space m)), IsCompact F₀ → F₀.Nonempty →
      ∀ σ : Measure (Space m), σ ≤ parabolicVolume m →
      ∀ T : Set (Space m), MeasurableSet T → F₀ ⊆ T → σ Tᶜ = 0 →
      ∀ (f : Space m → Y) (L : ℝ≥0), LipschitzOnWith L f T →
      (∀ x ∈ F₀, ∀ r : ℝ, 0 < r → ENNReal.ofReal (c * r ^ (m + 2)) ≤ σ (Metric.ball x r)) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ x ∈ F₀, ∫⁻ r in Ioi 0, affineErrorSq σ f x r ∂scaleMeasure ≤ ENNReal.ofReal B) →
      ∃ F : Space m → Y, (∀ x ∈ F₀, F x = f x) ∧ LipschitzWith (C * L) F ∧
        HasAffineCarlesonBound (parabolicVolume m) F (C * ((L : ℝ) ^ 2 + B)))
    (m d : ℕ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ {Y : Type u} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [FiniteDimensional ℝ Y], Module.finrank ℝ Y = d →
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
            (((C : ℝ) * ((L : ℝ) + Real.sqrt B₀)) ^ 2) := by
  obtain ⟨C, hC, hpiece⟩ := exists_trace_piece_extension hcut hext m
  refine ⟨C, hC, ?_⟩
  intro Y _ _ _ _ K f L B₀ hK _ hf hB₀ hS
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  -- the good set of the trace square function
  set G : Set (Space m) := {p | ∫⁻ r in Ioo 0 2, traceErrorSq (parabolicVolume m) K f p r
    ∂scaleMeasure ≤ ENNReal.ofReal B₀} with hGdef
  have hG : parabolicVolume m (K \ G) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 ((ae_restrict_iff' hKm).1 hS))
    intro p hp h'
    exact hp.2 (h' hp.1)
  obtain ⟨I, P, x₀, ρ, hP, hnull⟩ := exists_density_trace_pieces_proof m K G hK hG
  have hj : ∀ j : I, ∃ (c : Y) (H : Space m → Y), (∀ p ∈ P j, c + H p = f p) ∧
      HasCompactSupport H ∧ LipschitzWith (C * L) (fun p => c + H p) ∧
      HasAffineCarlesonBound (parabolicVolume m) H
        (((C : ℝ) * ((L : ℝ) + Real.sqrt B₀)) ^ 2) := by
    intro j
    obtain ⟨hPc, hPKG, hPx, hρ, hρ1, hd⟩ := hP j
    rcases (P j).eq_empty_or_nonempty with he | hne
    · refine ⟨0, fun _ => 0, fun p hp => by simp [he] at hp, HasCompactSupport.zero, ?_, ?_⟩
      · exact (LipschitzWith.const (0 + 0 : Y)).weaken zero_le
      · exact (hasAffineCarlesonBound_const _ (0 : Y)).mono_const (sq_nonneg _)
    · exact hpiece K (P j) f L B₀ (x₀ j) (ρ j) hK hPc hne (fun p hp => (hPKG hp).1) hPx hρ hρ1
        hf hB₀ (fun p hp r hr hr' => hd p hp r hr (by linarith)) (fun p hp => (hPKG hp).2)
  choose c H hcH using hj
  exact ⟨I, P, c, H, fun j => ⟨(hP j).1, fun p hp => ((hP j).2.1 hp).1⟩, hnull,
    fun j => (hcH j).1, fun j => (hcH j).2.1, fun j => (hcH j).2.2.1, fun j => (hcH j).2.2.2⟩

/-- **Countable reindexing**: every countable type is in bijection with a subset of `ℕ`. -/
theorem exists_setNat_equiv_of_countable (S : Type*) [Countable S] :
    ∃ I : Set ℕ, Nonempty (I ≃ S) := by
  obtain ⟨ι, hι⟩ := Countable.exists_injective_nat S
  exact ⟨Set.range ι, ⟨(Equiv.ofInjective ι hι).symm⟩⟩

/-- **Compact levels** of a measurable function that is finite almost everywhere on a compact
set: compact `Q_{N,i} ⊆ K ∩ {S ≤ N}` exhaust `K` up to a null set (inner regularity). -/
theorem exists_compact_level_pieces {m : ℕ} (K : Set (Space m)) (hK : IsCompact K)
    {S : Space m → ℝ≥0∞} (hSm : Measurable S)
    (hS : ∀ᵐ p ∂(parabolicVolume m).restrict K, S p < ⊤) :
    ∃ Q : ℕ → ℕ → Set (Space m),
      (∀ N i, IsCompact (Q N i) ∧ Q N i ⊆ K ∧ ∀ p ∈ Q N i, S p ≤ N) ∧
        parabolicVolume m (K \ ⋃ N, ⋃ i, Q N i) = 0 := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hAm : ∀ N : ℕ, MeasurableSet (K ∩ {p | S p ≤ N}) := fun N =>
    hKm.inter (measurableSet_le hSm measurable_const)
  have hAfin : ∀ N : ℕ, parabolicVolume m (K ∩ {p | S p ≤ N}) ≠ ⊤ := fun N =>
    ((measure_mono inter_subset_left).trans_lt hK.measure_lt_top).ne
  have hcpt : ∀ N i : ℕ, ∃ Q ⊆ K ∩ {p | S p ≤ N}, IsCompact Q ∧
      parabolicVolume m ((K ∩ {p | S p ≤ N}) \ Q) < (i : ℝ≥0∞)⁻¹ := fun N i =>
    (hAm N).exists_isCompact_sdiff_lt (hAfin N)
      (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top i))
  choose Q hQA hQc hQε using hcpt
  refine ⟨Q, fun N i => ⟨hQc N i, fun p hp => (hQA N i hp).1, fun p hp => (hQA N i hp).2⟩, ?_⟩
  have hinf : parabolicVolume m {p | p ∈ K ∧ ¬ S p < ⊤} = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 ((ae_restrict_iff' hKm).1 hS))
    intro p hp h'
    exact hp.2 (h' hp.1)
  have hres : ∀ N : ℕ, parabolicVolume m ((K ∩ {p | S p ≤ N}) \ ⋃ i, Q N i) = 0 := by
    intro N
    refine le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun i => ?_) zero_le
    exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion _ i))).trans (hQε N i).le
  refine measure_mono_null ?_ (measure_union_null hinf (measure_iUnion_null hres))
  rintro p ⟨hpK, hpQ⟩
  by_cases hpS : S p < ⊤
  swap
  · exact Or.inl ⟨hpK, hpS⟩
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hpS.ne
  refine Or.inr (mem_iUnion.2 ⟨N, ⟨hpK, hN.le⟩, fun h => hpQ (mem_iUnion.2 ⟨N, h⟩)⟩)

/-- **Affine trace pieces for a finite square function, in ordinary coordinates**, with the
conclusion of `exists_affine_trace_pieces_coord_of_finite_square`, from the uniform-constant
statement `hcoord` (the statement of `exists_affine_trace_pieces_coord`). -/
theorem exists_affine_trace_pieces_coord_of_finite_square_proof
    (hcoord : ∀ m d : ℕ, ∃ C : ℝ≥0, 0 < C ∧ ∀ {Y : Type u} [NormedAddCommGroup Y]
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
    {m : ℕ} {Y : Type u}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set (Space m)) (f : Space m → Y) (L : ℝ≥0) (hK : IsCompact K)
    (hK₁ : K ⊆ Metric.closedBall (point 0 0) 1) (hf : LipschitzOnWith L f K)
    (hS : ∀ᵐ p ∂(parabolicVolume m).restrict K,
      ∫⁻ r in Ioo 0 2, traceErrorSq (parabolicVolume m) K f p r ∂scaleMeasure < ⊤) :
    ∃ (I : Set ℕ) (P : I → Set (Space m)) (c : I → Y) (H : I → Space m → Y),
      (∀ j, IsCompact (P j) ∧ P j ⊆ K) ∧ parabolicVolume m (K \ ⋃ j, P j) = 0 ∧
      (∀ j, ∀ p ∈ P j, c j + H j p = f p) ∧ (∀ j, HasCompactSupport (H j)) ∧
      ∀ j, ∃ (L' : ℝ≥0) (B : ℝ), LipschitzWith L' (fun p => c j + H j p) ∧
        HasAffineCarlesonBound (parabolicVolume m) (H j) B := by
  obtain ⟨C, -, hT⟩ := hcoord m (Module.finrank ℝ Y)
  -- compact levels of the measurable trace square function
  obtain ⟨Q, hQ, hQnull⟩ := exists_compact_level_pieces K hK
    ((measurable_traceErrorSq_of_isCompact_proof K hK f L hf).2 2) hS
  -- uniform-constant statement on each compact level piece, with `B₀ = N`; restriction monotonicity
  have hpieces : ∀ N i : ℕ, ∃ (J : Set ℕ) (P : J → Set (Space m)) (c : J → Y)
      (H : J → Space m → Y),
      (∀ j, IsCompact (P j) ∧ P j ⊆ Q N i) ∧ parabolicVolume m (Q N i \ ⋃ j, P j) = 0 ∧
      (∀ j, ∀ p ∈ P j, c j + H j p = f p) ∧ (∀ j, HasCompactSupport (H j)) ∧
      (∀ j, LipschitzWith (C * L) (fun p => c j + H j p)) ∧
      ∀ j, HasAffineCarlesonBound (parabolicVolume m) (H j)
        (((C : ℝ) * ((L : ℝ) + Real.sqrt N)) ^ 2) := by
    intro N i
    obtain ⟨hQc, hQK, hQS⟩ := hQ N i
    refine hT rfl (Q N i) f L (N : ℝ) hQc (hQK.trans hK₁) (hf.mono hQK) (Nat.cast_nonneg N)
      ((ae_restrict_iff' hQc.isClosed.measurableSet).2 (Eventually.of_forall fun p hp => ?_))
    calc ∫⁻ r in Ioo 0 2, traceErrorSq (parabolicVolume m) (Q N i) f p r ∂scaleMeasure
        ≤ ∫⁻ r in Ioo 0 2, traceErrorSq (parabolicVolume m) K f p r ∂scaleMeasure :=
          lintegral_mono fun r => traceErrorSq_mono_set _ hQK _ _ _
      _ ≤ (N : ℝ≥0∞) := hQS p hp
      _ = ENNReal.ofReal N := (ENNReal.ofReal_natCast N).symm
  choose J P c H hP hnull hagree hsupp hlip hcarl using hpieces
  -- countable reindexing of the triples `(N, i, j)`
  obtain ⟨I, ⟨e⟩⟩ := exists_setNat_equiv_of_countable (Σ (N : ℕ) (i : ℕ), J N i)
  refine ⟨I, fun q => P (e q).1 (e q).2.1 (e q).2.2, fun q => c (e q).1 (e q).2.1 (e q).2.2,
    fun q => H (e q).1 (e q).2.1 (e q).2.2,
    fun q => ⟨(hP _ _ _).1, (hP _ _ _).2.trans (hQ _ _).2.1⟩, ?_, fun q => hagree _ _ _,
    fun q => hsupp _ _ _, fun q => ⟨_, _, hlip _ _ _, hcarl _ _ _⟩⟩
  refine measure_mono_null ?_ (measure_union_null hQnull
    (measure_iUnion_null fun N => measure_iUnion_null fun i => hnull N i))
  rintro p ⟨hpK, hpP⟩
  by_cases hpQ : p ∈ ⋃ N, ⋃ i, Q N i
  swap
  · exact Or.inl ⟨hpK, hpQ⟩
  obtain ⟨N, hN⟩ := mem_iUnion.1 hpQ
  obtain ⟨i, hi⟩ := mem_iUnion.1 hN
  refine Or.inr (mem_iUnion.2 ⟨N, mem_iUnion.2 ⟨i, hi, fun h => hpP ?_⟩⟩)
  obtain ⟨j, hj⟩ := mem_iUnion.1 h
  refine mem_iUnion.2 ⟨e.symm ⟨N, i, j⟩, ?_⟩
  have he : e (e.symm ⟨N, i, j⟩) = ⟨N, i, j⟩ := e.apply_symm_apply _
  show p ∈ P (e (e.symm ⟨N, i, j⟩)).1 (e (e.symm ⟨N, i, j⟩)).2.1 (e (e.symm ⟨N, i, j⟩)).2.2
  rw [he]
  exact hj

end ParabolicRectifiability
