import ParabolicRectifiability.Analysis.RegularExtension.AffineCarlesonBMO
import ParabolicRectifiability.Analysis.RegularExtension.TraceScales.DensityPieces
import ParabolicRectifiability.Analysis.RegularExtension.TraceScales.ScaleTail
import ParabolicRectifiability.Analysis.RegularExtension.TraceScales.ScaleBridge
import ParabolicRectifiability.Analysis.TraceExtension.TracePieces
import ParabolicRectifiability.Analysis.TraceExtension.SourceExtension
import ParabolicRectifiability.Analysis.TraceExtension.CutoffCarleson
import ParabolicRectifiability.Analysis.TraceExtension.Reservoirs
import ParabolicRectifiability.Analysis.TraceExtension.Hall.Transport
import ParabolicRectifiability.Metric.BaseVolume

/-! # Regular trace pieces and regular graphs from a vertical square function

This file proves `exists_regular_trace_pieces_proof` (existence of regular trace pieces) and
`exists_regular_graphs_of_vertical_square_proof` (a set with finite vertical square function is
covered, up to a null set, by countably many Lipschitz graphs with regular vertical functions).
They are assembled from:

* the compact cutoff with affine Carleson bound `exists_compact_cutoff_affineCarleson_proof`
  (`TraceExtension/CutoffCarleson`);
* the Whitney source allocation `exists_whitney_source_allocation_proof`
  (`TraceExtension/Reservoirs/Allocation`), applied to the Hall-type transport
  `exists_transport_of_hall_condition_proof` and the weakly convergent density subsequence
  `exists_weakly_convergent_density_subseq_proof` (`TraceExtension/HallTransport`);
* the half-time BMO estimate `halfTimeBMO_of_affineCarleson_proof` (`AffineBMOProof`);
* the density pieces `exists_density_pieces_intrinsic_proof` and the two scale estimates
  `lintegral_Ioi_traceErrorSq_le_of_subset_closedBall_proof` and
  `lintegral_Ioc_traceErrorSq_le_betaSq_proof` (`RegularExtension/RX1/*`);
* the affine trace pieces `exists_affine_trace_pieces_proof`,
  `exists_affine_trace_pieces_coord_proof` and the source extension
  `exists_affine_extension_of_source_proof`.

Helper lemmas on regular vertical functions and lifts live in the namespace `RegularHubProofs`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability

namespace RegularHubProofs

variable {n : ℕ}

/-- Regular vertical functions are monotone in their tolerance. -/
theorem regular_mono {W : Submodule ℝ (Spatial n)} {G : SubspaceSpace W → W.orthogonal}
    {ε ε' : ℝ} (h : IsRegularVerticalFunction W G ε) (hε : ε ≤ ε') :
    IsRegularVerticalFunction W G ε' := by
  obtain ⟨c, H, g, L, B, hG, hH, hL, hB, hrep, hsum⟩ := h
  exact ⟨c, H, g, L, B, hG, hH, hL, hB, hrep, hsum.trans hε⟩

/-- The lift `q ↦ (q.1 + f q, q.2)` is `(1 + L)`-Lipschitz on `K` when `f` is `L`-Lipschitz on `K`. -/
theorem lipschitzOnWith_lift (W : Submodule ℝ (Spatial n)) (K : Set (SubspaceSpace W))
    (f : SubspaceSpace W → W.orthogonal) (L : ℝ≥0) (hf : LipschitzOnWith L f K) :
    LipschitzOnWith (1 + L)
      (fun q : SubspaceSpace W => (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n))
      K := by
  refine LipschitzOnWith.of_dist_le_mul fun q hq p hp => ?_
  have hd : dist q p = max (dist q.1 p.1) (dist q.2 p.2) := Prod.dist_eq
  have h1 : dist q.1 p.1 ≤ dist q p := hd ▸ le_max_left _ _
  have h2 : dist q.2 p.2 ≤ dist q p := hd ▸ le_max_right _ _
  have hfq : dist (f q) (f p) ≤ L * dist q p := hf.dist_le_mul q hq p hp
  have h0 : 0 ≤ dist q p := dist_nonneg
  have hLd : 0 ≤ (L : ℝ) * dist q p := mul_nonneg L.coe_nonneg h0
  have hsp : dist ((q.1 : Spatial n) + (f q : Spatial n)) ((p.1 : Spatial n) + (f p : Spatial n))
      ≤ dist q.1 p.1 + dist (f q) (f p) := by
    rw [Subtype.dist_eq q.1 p.1, Subtype.dist_eq (f q) (f p)]
    exact dist_add_add_le _ _ _ _
  refine (Prod.dist_eq).trans_le (max_le ?_ ?_)
  · calc dist ((q.1 : Spatial n) + (f q : Spatial n)) ((p.1 : Spatial n) + (f p : Spatial n))
        ≤ dist q.1 p.1 + dist (f q) (f p) := hsp
      _ ≤ dist q p + (L : ℝ) * dist q p := add_le_add h1 hfq
      _ = ((1 + L : ℝ≥0) : ℝ) * dist q p := by push_cast; ring
  · calc dist q.2 p.2 ≤ dist q p := h2
      _ ≤ ((1 + L : ℝ≥0) : ℝ) * dist q p := by push_cast; linarith

/-- The lift of an `L`-Lipschitz function on `K` sends base-null subsets of `K` to
`H^{m+2}_P`-null sets. -/
theorem hausdorffP_image_lift_null (W : Submodule ℝ (Spatial n)) {m : ℕ}
    (hW : Module.finrank ℝ W = m) (K : Set (SubspaceSpace W))
    (f : SubspaceSpace W → W.orthogonal) (L : ℝ≥0) (hf : LipschitzOnWith L f K)
    (A : Set (SubspaceSpace W)) (hA : A ⊆ K) (hA0 : intrinsicParabolicVolume W A = 0) :
    hausdorffP n (m + 2)
      ((fun q : SubspaceSpace W => (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n)) ''
        A) = 0 := by
  subst hW
  have hb := (vertical_base_hausdorff_comparison W A).2
  rw [hA0, mul_zero, nonpos_iff_eq_zero] at hb
  have hl := ((lipschitzOnWith_lift W K f L hf).mono hA).hausdorffMeasure_image_le
    (d := ((Module.finrank ℝ W + 2 : ℕ) : ℝ)) (Nat.cast_nonneg _)
  rw [hb, mul_zero, nonpos_iff_eq_zero] at hl
  rw [hausdorffP_eq]
  exact hl

end RegularHubProofs

open RegularHubProofs

/-- Regular extension on countably many compact trace pieces. For a compact
subset `K` of the intrinsic unit ball, an `L`-Lipschitz trace and an a.e.
trace-error square bound `B₀ ≥ 0` on scales `(0,2)`, the pieces cover `K`
up to intrinsic-volume zero and agree with full compact perturbations of
constants of regular norm at most `C * (L + sqrt B₀)`. The constant depends
only on the spatial base rank `m` and normal rank `d`. Both ranks may be zero.
Whitney source allocation gives affine extensions, and the affine-Carleson
estimate supplies the half-time BMO bound. -/
theorem exists_regular_trace_pieces_proof (m d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (W : Submodule ℝ (Spatial n)),
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
          ∀ j, IsRegularVerticalFunction W (fun p => c j + H j p)
            (C * ((L : ℝ) + Real.sqrt B₀)) := by
  obtain ⟨CT, hCT, hT⟩ := exists_affine_trace_pieces_proof
    (exists_affine_trace_pieces_coord_proof.{0} exists_compact_cutoff_affineCarleson_proof
      (fun m c hc => exists_affine_extension_of_source_proof
        (fun m c D a b hc => exists_whitney_source_allocation_proof.{0}
          exists_transport_of_hall_condition_proof
          exists_weakly_convergent_density_subseq_proof m c D a b hc) m c hc)) m d
  obtain ⟨CA, hCA, hA⟩ := halfTimeBMO_of_affineCarleson_proof m d
  have hCTr : (0 : ℝ) < CT := by exact_mod_cast hCT
  refine ⟨(CT : ℝ) + 2 * CA * CT,
    add_pos_of_pos_of_nonneg hCTr (mul_nonneg (mul_nonneg zero_le_two hCA.le) hCTr.le), ?_⟩
  intro n W hm hd K f L B₀ hK hK₁ hf hB₀ hS
  obtain ⟨I, P, c, H, hP, hnull, hagree, hsupp, hlip, hcarl⟩ :=
    hT W hm hd K f L B₀ hK hK₁ hf hB₀ hS
  refine ⟨I, P, c, H, hP, hnull, hagree, hsupp, fun j => ?_⟩
  have hHlip : LipschitzWith (CT * L) (H j) := LipschitzWith.of_dist_le_mul fun x y => by
    have h := (hlip j).dist_le_mul x y
    simp only [dist_add_left] at h
    exact h
  obtain ⟨g, hrep, hbmo⟩ := hA W hm hd (H j) (CT * L)
    (((CT : ℝ) * ((L : ℝ) + Real.sqrt B₀)) ^ 2) (hsupp j) hHlip (hcarl j)
  have hsq : Real.sqrt (((CT : ℝ) * ((L : ℝ) + Real.sqrt B₀)) ^ 2) =
      (CT : ℝ) * ((L : ℝ) + Real.sqrt B₀) :=
    Real.sqrt_sq (mul_nonneg CT.coe_nonneg (add_nonneg L.coe_nonneg (Real.sqrt_nonneg _)))
  rw [hsq, NNReal.coe_mul] at hbmo
  have hx : 0 ≤ CA * ((CT : ℝ) * L + CT * ((L : ℝ) + Real.sqrt B₀)) :=
    mul_nonneg hCA.le (add_nonneg (mul_nonneg CT.coe_nonneg L.coe_nonneg)
      (mul_nonneg CT.coe_nonneg (add_nonneg L.coe_nonneg (Real.sqrt_nonneg _))))
  refine ⟨c j, H j, g, CT * L,
    Real.toNNReal (CA * ((CT : ℝ) * L + CT * ((L : ℝ) + Real.sqrt B₀))),
    rfl, hsupp j, hlip j, ?_, hrep, ?_⟩
  · rw [Real.coe_toNNReal _ hx]
    exact hbmo
  · rw [Real.coe_toNNReal _ hx, NNReal.coe_mul]
    have h1 : 0 ≤ ((CT : ℝ) + CA * CT) * Real.sqrt B₀ :=
      mul_nonneg (add_nonneg CT.coe_nonneg (mul_nonneg hCA.le CT.coe_nonneg))
        (Real.sqrt_nonneg _)
    nlinarith [h1]

/-- Cover a compact small-slope vertical graph by full regular graphs up
to parabolic Hausdorff measure zero. The slope threshold `L₀` depends on
base rank `m`; the regularity constant also depends on normal rank `d`.
The beta hypothesis uses `H_P^(m+2)` restricted to the original partial
graph and scales `(0,2)`, with a.e. quantification on the base. The output
bound is `C * (L + sqrt B₀)`. Density pieces and the beta-to-trace estimate
reduce this to `exists_regular_trace_pieces_proof`. -/
theorem exists_regular_graphs_of_vertical_square_proof (m : ℕ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ L₀ ≤ 1 ∧ ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (W : Submodule ℝ (Spatial n)),
      Module.finrank ℝ W = m → Module.finrank ℝ W.orthogonal = d →
      ∀ (K : Set (SubspaceSpace W)) (f : SubspaceSpace W → W.orthogonal)
        (L : ℝ≥0) (B₀ : ℝ),
        IsCompact K →
        K ⊆ Metric.closedBall
          (((0 : W), Metric.Snowflaking.toSnowflaking (0 : ℝ)) : SubspaceSpace W) 1 →
        LipschitzOnWith L f K → (L : ℝ) ≤ L₀ → 0 ≤ B₀ →
        (∀ᵐ p ∂(intrinsicParabolicVolume W).restrict K,
          ∫⁻ r in Ioo 0 2,
            betaSq ((hausdorffP n (m + 2)).restrict
                ((fun q : SubspaceSpace W =>
                  (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n)) '' K))
              (m + 2) .vertical
              (((p.1 : Spatial n) + (f p : Spatial n), p.2) : Space n) r
            ∂scaleMeasure ≤ ENNReal.ofReal B₀) →
        ∃ (I : Set ℕ) (G : I → SubspaceSpace W → W.orthogonal),
          (∀ j, IsRegularVerticalFunction W (G j) (C * ((L : ℝ) + Real.sqrt B₀))) ∧
          hausdorffP n (m + 2)
            ((fun q : SubspaceSpace W =>
                (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n)) '' K \
              ⋃ j, Set.range (fun q : SubspaceSpace W =>
                (((q.1 : Spatial n) + (G j q : Spatial n), q.2) : Space n))) = 0 := by
  obtain ⟨L₀, hL₀, hL₀1, hbr⟩ := lintegral_Ioc_traceErrorSq_le_betaSq_proof m
  refine ⟨L₀, hL₀, hL₀1, fun d => ?_⟩
  obtain ⟨C₄, hC₄, hbr'⟩ := hbr d
  obtain ⟨C₃, hC₃, hzero⟩ := lintegral_Ioi_traceErrorSq_le_of_subset_closedBall_proof m
  obtain ⟨C₁, hC₁, htrace⟩ := exists_regular_trace_pieces_proof m d
  refine ⟨C₁ * (1 + Real.sqrt C₄ + Real.sqrt C₃), mul_pos hC₁ (by positivity), ?_⟩
  intro n W hm hd K f L B₀ hK hK₁ hf hL hB₀ hS
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  -- the good set of the vertical square function contains almost every point of `K`
  have hG : intrinsicParabolicVolume W (K \ {p | ∫⁻ r in Ioo 0 2,
      betaSq ((hausdorffP n (m + 2)).restrict
          ((fun q : SubspaceSpace W =>
            (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n)) '' K))
        (m + 2) .vertical (((p.1 : Spatial n) + (f p : Spatial n), p.2) : Space n) r
      ∂scaleMeasure ≤ ENNReal.ofReal B₀}) = 0 := by
    have h := (ae_restrict_iff' hKm).1 hS
    rw [ae_iff] at h
    refine measure_mono_null (fun p hp => ?_) h
    simp only [Set.mem_ofPred_eq, not_imp]
    exact ⟨hp.1, hp.2⟩
  obtain ⟨I, P, x₀, ρ, hP, hcov⟩ := exists_density_pieces_intrinsic_proof W K _ hK hG
  -- regular trace pieces on each piece
  have hpiece : ∀ j : I, ∃ (I' : Set ℕ) (Q : I' → Set (SubspaceSpace W))
      (c : I' → W.orthogonal) (H : I' → SubspaceSpace W → W.orthogonal),
      (∀ i, IsCompact (Q i) ∧ Q i ⊆ P j) ∧
      intrinsicParabolicVolume W (P j \ ⋃ i, Q i) = 0 ∧
      (∀ i, ∀ p ∈ Q i, c i + H i p = f p) ∧
      (∀ i, HasCompactSupport (H i)) ∧
      ∀ i, IsRegularVerticalFunction W (fun p => c i + H i p)
        (C₁ * ((L : ℝ) + Real.sqrt ((Real.sqrt C₄ * Real.sqrt B₀ + Real.sqrt C₃ * L) ^ 2))) := by
    intro j
    obtain ⟨hPc, hPKG, hPball, hρ, hρ64, hdens⟩ := hP j
    have hPK : P j ⊆ K := fun p hp => (hPKG hp).1
    refine htrace W hm hd (P j) f L ((Real.sqrt C₄ * Real.sqrt B₀ + Real.sqrt C₃ * L) ^ 2) hPc
      (hPK.trans hK₁) (hf.mono hPK) (sq_nonneg _) ?_
    refine ae_restrict_of_forall_mem hPc.isClosed.measurableSet fun p hp => ?_
    have hpG : ∫⁻ r in Ioo 0 2,
        betaSq ((hausdorffP n (m + 2)).restrict
            ((fun q : SubspaceSpace W =>
              (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n)) '' K))
          (m + 2) .vertical (((p.1 : Spatial n) + (f p : Spatial n), p.2) : Space n) r
        ∂scaleMeasure ≤ ENNReal.ofReal B₀ := (hPKG hp).2
    have hsplit : Ioo (0 : ℝ) 2 ⊆ Ioc 0 (ρ j) ∪ Ioi (ρ j) := by
      intro r hr
      rcases le_or_gt r (ρ j) with h | h
      · exact Or.inl ⟨hr.1, h⟩
      · exact Or.inr h
    have hlow := hbr' W hm hd K (P j) f L hK hf hL hPK p hp (ρ j) hρ (by linarith)
      (fun r hr hrρ => hdens p hp r hr (by linarith))
    have hhigh := hzero W hm (P j) f L (x₀ j) (ρ j) hPc hρ hPball (hf.mono hPK) p hp
    have hsq : C₄ * B₀ + C₃ * (L : ℝ) ^ 2 ≤
        (Real.sqrt C₄ * Real.sqrt B₀ + Real.sqrt C₃ * L) ^ 2 := by
      have e1 : (Real.sqrt C₄ * Real.sqrt B₀) ^ 2 = C₄ * B₀ := by
        rw [mul_pow, Real.sq_sqrt hC₄.le, Real.sq_sqrt hB₀]
      have e2 : (Real.sqrt C₃ * (L : ℝ)) ^ 2 = C₃ * (L : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hC₃]
      have h0 : 0 ≤ Real.sqrt C₄ * Real.sqrt B₀ * (Real.sqrt C₃ * L) := by positivity
      nlinarith [e1, e2, h0]
    calc ∫⁻ r in Ioo 0 2, traceErrorSq (intrinsicParabolicVolume W) (P j) f p r ∂scaleMeasure
        ≤ ∫⁻ r in Ioc 0 (ρ j) ∪ Ioi (ρ j),
            traceErrorSq (intrinsicParabolicVolume W) (P j) f p r ∂scaleMeasure :=
          lintegral_mono_set hsplit
      _ ≤ (∫⁻ r in Ioc 0 (ρ j),
            traceErrorSq (intrinsicParabolicVolume W) (P j) f p r ∂scaleMeasure) +
          ∫⁻ r in Ioi (ρ j), traceErrorSq (intrinsicParabolicVolume W) (P j) f p r
            ∂scaleMeasure := lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal C₄ * ENNReal.ofReal B₀ + ENNReal.ofReal (C₃ * (L : ℝ) ^ 2) :=
          add_le_add (hlow.trans (mul_le_mul_right hpG _)) hhigh
      _ = ENNReal.ofReal (C₄ * B₀ + C₃ * (L : ℝ) ^ 2) := by
          rw [← ENNReal.ofReal_mul hC₄.le,
            ← ENNReal.ofReal_add (mul_nonneg hC₄.le hB₀) (mul_nonneg hC₃ (sq_nonneg _))]
      _ ≤ ENNReal.ofReal ((Real.sqrt C₄ * Real.sqrt B₀ + Real.sqrt C₃ * L) ^ 2) :=
          ENNReal.ofReal_le_ofReal hsq
  choose I' Q c H _hQ hQnull hagree _hsupp hreg using hpiece
  have hbound : C₁ * ((L : ℝ) +
      Real.sqrt ((Real.sqrt C₄ * Real.sqrt B₀ + Real.sqrt C₃ * L) ^ 2)) ≤
      C₁ * (1 + Real.sqrt C₄ + Real.sqrt C₃) * ((L : ℝ) + Real.sqrt B₀) := by
    have h1 : 0 ≤ Real.sqrt C₄ := Real.sqrt_nonneg _
    have h2 : 0 ≤ Real.sqrt C₃ := Real.sqrt_nonneg _
    have h3 : 0 ≤ Real.sqrt B₀ := Real.sqrt_nonneg _
    have h4 : (0 : ℝ) ≤ L := L.coe_nonneg
    rw [Real.sqrt_sq (by positivity)]
    have key : (L : ℝ) + (Real.sqrt C₄ * Real.sqrt B₀ + Real.sqrt C₃ * L) ≤
        (1 + Real.sqrt C₄ + Real.sqrt C₃) * ((L : ℝ) + Real.sqrt B₀) := by
      nlinarith [mul_nonneg h1 h4, mul_nonneg h2 h3]
    calc C₁ * ((L : ℝ) + (Real.sqrt C₄ * Real.sqrt B₀ + Real.sqrt C₃ * L))
        ≤ C₁ * ((1 + Real.sqrt C₄ + Real.sqrt C₃) * ((L : ℝ) + Real.sqrt B₀)) :=
          mul_le_mul_of_nonneg_left key hC₁.le
      _ = C₁ * (1 + Real.sqrt C₄ + Real.sqrt C₃) * ((L : ℝ) + Real.sqrt B₀) := by ring
  obtain ⟨J, ⟨e⟩⟩ := exists_setNat_equiv_of_countable (Σ j : I, I' j)
  set G : (Σ j : I, I' j) → SubspaceSpace W → W.orthogonal :=
    fun x p => c x.1 x.2 + H x.1 x.2 p with hGdef
  refine ⟨J, fun k => G (e k), fun k => regular_mono (hreg (e k).1 (e k).2) hbound, ?_⟩
  -- the base remainder is null
  have hN : intrinsicParabolicVolume W (K \ ⋃ x : (Σ j : I, I' j), Q x.1 x.2) = 0 := by
    refine measure_mono_null ?_
      (measure_union_null hcov (measure_iUnion_null fun j => hQnull j))
    intro p hp
    by_cases hpP : p ∈ ⋃ j, P j
    · obtain ⟨j, hpj⟩ := Set.mem_iUnion.1 hpP
      refine Or.inr (Set.mem_iUnion.2 ⟨j, hpj, fun hq => hp.2 ?_⟩)
      obtain ⟨i, hpi⟩ := Set.mem_iUnion.1 hq
      exact Set.mem_iUnion.2 ⟨⟨j, i⟩, hpi⟩
    · exact Or.inl ⟨hp.1, hpP⟩
  refine measure_mono_null ?_ (hausdorffP_image_lift_null W hm K f L hf _ Set.sdiff_subset hN)
  rintro z ⟨⟨p, hpK, rfl⟩, hz⟩
  refine ⟨p, ⟨hpK, fun hp => hz ?_⟩, rfl⟩
  obtain ⟨x, hpx⟩ := Set.mem_iUnion.1 hp
  have hGx : G (e (e.symm x)) p = f p := by
    rw [Equiv.apply_symm_apply, hGdef]
    exact hagree x.1 x.2 p hpx
  refine Set.mem_iUnion.2 ⟨e.symm x, p, ?_⟩
  simp only [hGx]

end ParabolicRectifiability
