import ParabolicRectifiability.Foundations.HalfTimeDerivative

/-! # The vertical chart: bi-Lipschitz bounds and coordinate BMO

Proves the statements of `b2_vertical_chart_bilipschitz` and `b2_vertical_coordinate_bmo`.

* `b2_vertical_chart_bilipschitz_proof`: the vertical chart
  `Φ(p) = (a + ι(p)₁ + G(ι p), p₂)`, `ι = (subspaceParabolicIsometry W).symm`, satisfies
  `d(p,q) ≤ d(Φ p, Φ q) ≤ (1 + K) d(p,q)` for a `K`-Lipschitz `G : W × ℝ → W^⊥`. Route:
  orthogonal Pythagoras for the lower bound, the triangle inequality for the upper bound.
* `b2_vertical_coordinate_bmo_proof`: every ambient coordinate of `g ∘ ι` has real parabolic
  BMO bound `B` when `g` has vector parabolic BMO bound `B`. Route: `ι` is a
  measure-preserving isometry, and `v ↦ (v : ℝ^n)_α` is a continuous linear functional of
  norm at most one.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-! ## The vertical chart is bi-Lipschitz -/

/-- The vertical chart in intrinsic base coordinates: for `P, Q` in the intrinsic base,
`d(P,Q) ≤ d(Φ P, Φ Q) ≤ (1 + K) d(P,Q)` with `Φ P = (a + P₁ + G P, P₂)`. -/
theorem b2vch_chart_bounds {n : ℕ} (W : Submodule ℝ (Spatial n)) (a : Spatial n)
    (Gf : SubspaceSpace W → W.orthogonal) (K : ℝ≥0) (hG : LipschitzWith K Gf)
    (P Q : SubspaceSpace W) :
    dist P Q ≤ dist ((a + (P.1 : Spatial n) + (Gf P : Spatial n), P.2) : Space n)
        (a + (Q.1 : Spatial n) + (Gf Q : Spatial n), Q.2) ∧
      dist ((a + (P.1 : Spatial n) + (Gf P : Spatial n), P.2) : Space n)
          (a + (Q.1 : Spatial n) + (Gf Q : Spatial n), Q.2) ≤
        (1 + (K : ℝ)) * dist P Q := by
  set A : Spatial n := ((P.1 - Q.1 : W) : Spatial n) with hA
  set C : Spatial n := ((Gf P - Gf Q : W.orthogonal) : Spatial n) with hC
  have hd : dist P Q = max ‖A‖ (dist P.2 Q.2) := by
    rw [Prod.dist_eq, dist_eq_norm]
    rfl
  have hΦ : dist ((a + (P.1 : Spatial n) + (Gf P : Spatial n), P.2) : Space n)
      (a + (Q.1 : Spatial n) + (Gf Q : Spatial n), Q.2) = max ‖A + C‖ (dist P.2 Q.2) := by
    rw [Prod.dist_eq, dist_eq_norm]
    congr 2
    rw [hA, hC, Submodule.coe_sub, Submodule.coe_sub, add_assoc a, add_assoc a,
      add_sub_add_left_eq_sub, add_sub_add_comm]
  have hinner : inner ℝ A C = 0 :=
    Submodule.inner_right_of_mem_orthogonal (P.1 - Q.1).2 (Gf P - Gf Q).2
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero A C hinner
  have hlow : ‖A‖ ≤ ‖A + C‖ :=
    (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2
      (by rw [hpy]; exact le_add_of_nonneg_right (mul_self_nonneg _))
  have hClip : ‖C‖ ≤ (K : ℝ) * dist P Q := by
    have h := hG.dist_le_mul P Q
    rw [dist_eq_norm] at h
    exact h
  have hAd : ‖A‖ ≤ dist P Q := hd ▸ le_max_left _ _
  have htd : dist P.2 Q.2 ≤ dist P Q := hd ▸ le_max_right _ _
  have hKd : 0 ≤ (K : ℝ) * dist P Q := mul_nonneg K.2 dist_nonneg
  refine ⟨?_, ?_⟩
  · rw [hΦ, hd]
    exact max_le_max hlow le_rfl
  · rw [hΦ]
    have hexp : (1 + (K : ℝ)) * dist P Q = dist P Q + (K : ℝ) * dist P Q := by ring
    rw [hexp]
    refine max_le ?_ ?_
    · calc ‖A + C‖ ≤ ‖A‖ + ‖C‖ := norm_add_le _ _
        _ ≤ dist P Q + (K : ℝ) * dist P Q := add_le_add hAd hClip
    · linarith

/-- **The vertical chart is bi-Lipschitz**: `d(p,q) ≤ d(Φ p, Φ q) ≤ (1 + K) d(p,q)` for a
`K`-Lipschitz `G` (the statement of `b2_vertical_chart_bilipschitz`). -/
theorem b2_vertical_chart_bilipschitz_proof :
    ∀ (n : ℕ) (W : Submodule ℝ (Spatial n)) (a : Spatial n)
      (Gf : SubspaceSpace W → W.orthogonal) (K : ℝ≥0), LipschitzWith K Gf →
      ∀ p q : Space (Module.finrank ℝ W),
        dist p q ≤ dist ((a + (((subspaceParabolicIsometry W).symm p).1 : Spatial n) +
              (Gf ((subspaceParabolicIsometry W).symm p) : Spatial n), p.2) : Space n)
            (a + (((subspaceParabolicIsometry W).symm q).1 : Spatial n) +
              (Gf ((subspaceParabolicIsometry W).symm q) : Spatial n), q.2) ∧
        dist ((a + (((subspaceParabolicIsometry W).symm p).1 : Spatial n) +
              (Gf ((subspaceParabolicIsometry W).symm p) : Spatial n), p.2) : Space n)
            (a + (((subspaceParabolicIsometry W).symm q).1 : Spatial n) +
              (Gf ((subspaceParabolicIsometry W).symm q) : Spatial n), q.2) ≤
          (1 + (K : ℝ)) * dist p q := by
  intro n W a Gf K hG p q
  have h := b2vch_chart_bounds W a Gf K hG ((subspaceParabolicIsometry W).symm p)
    ((subspaceParabolicIsometry W).symm q)
  rw [IsometryEquiv.dist_eq] at h
  exact h

/-! ## Coordinate BMO of a vector BMO function -/

/-- The ambient coordinate functional `v ↦ (v : ℝ^n)_α` on the normal space. -/
def b2vch_coord {n : ℕ} (W : Submodule ℝ (Spatial n)) (α : Fin n) :
    W.orthogonal →L[ℝ] ℝ :=
  (EuclideanSpace.proj α).comp W.orthogonal.subtypeL

theorem b2vch_coord_apply {n : ℕ} (W : Submodule ℝ (Spatial n)) (α : Fin n)
    (v : W.orthogonal) : b2vch_coord W α v = (v : Spatial n) α := rfl

theorem b2vch_norm_coord_le {n : ℕ} (W : Submodule ℝ (Spatial n)) (α : Fin n)
    (v : W.orthogonal) : ‖b2vch_coord W α v‖ ≤ ‖v‖ := by
  rw [b2vch_coord_apply]
  exact PiLp.norm_apply_le (v : Spatial n) α

/-- **Coordinate BMO**: every ambient coordinate of `g ∘ ι` has parabolic BMO bound `B` when `g`
has vector parabolic BMO bound `B` (the statement of `b2_vertical_coordinate_bmo`). -/
theorem b2_vertical_coordinate_bmo_proof :
    ∀ (n : ℕ) (W : Submodule ℝ (Spatial n)) (g : SubspaceSpace W → W.orthogonal) (B : ℝ),
      HasParabolicBMOBound W g B → ∀ α : Fin n,
        HasStandardParabolicBMOBound (Module.finrank ℝ W)
          (fun p => ((g ((subspaceParabolicIsometry W).symm p) : W.orthogonal) : Spatial n) α)
          B := by
  intro n W g B hg α
  set ιI := (subspaceParabolicIsometry W).symm with hιI
  have hmp : MeasurePreserving ιI (parabolicVolume (Module.finrank ℝ W))
      (intrinsicParabolicVolume W) := subspaceParabolic_symm_measurePreserving W
  have hemb : MeasurableEmbedding ιI :=
    (subspaceParabolicMeasurableEquiv W).symm.measurableEmbedding
  -- local integrability of `g ∘ ι`
  have hmap : Measure.map ιI.toHomeomorph (parabolicVolume (Module.finrank ℝ W)) =
      intrinsicParabolicVolume W := hmp.map_eq
  have hloc : LocallyIntegrable (fun q => g (ιI q)) (parabolicVolume (Module.finrank ℝ W)) := by
    have h := (locallyIntegrable_map_homeomorph ιI.toHomeomorph (f := g)
      (μ := parabolicVolume (Module.finrank ℝ W))).1 (by rw [hmap]; exact hg.2.1)
    exact h
  have hcomp : ∀ q, ((g (ιI q) : W.orthogonal) : Spatial n) α = b2vch_coord W α (g (ιI q)) :=
    fun q => rfl
  refine ⟨hg.1, ?_, fun p r hr => ?_⟩
  · refine hloc.mono ?_ (Eventually.of_forall fun q => ?_)
    · exact (b2vch_coord W α).continuous.comp_aestronglyMeasurable hloc.aestronglyMeasurable
    · rw [hcomp]
      exact b2vch_norm_coord_le W α _
  · set P := ιI p with hP
    have hball : ιI ⁻¹' Metric.ball P r = Metric.ball p r := by
      rw [IsometryEquiv.preimage_ball, hP, IsometryEquiv.symm_apply_apply]
    have hvol : parabolicVolume (Module.finrank ℝ W) (Metric.ball p r) =
        intrinsicParabolicVolume W (Metric.ball P r) := by
      rw [← hball]
      exact hmp.measure_preimage Metric.isOpen_ball.measurableSet.nullMeasurableSet
    have hint : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
        (F : SubspaceSpace W → E),
        ∫ q in Metric.ball p r, F (ιI q) ∂parabolicVolume (Module.finrank ℝ W) =
          ∫ y in Metric.ball P r, F y ∂intrinsicParabolicVolume W := by
      intro E _ _ F
      rw [← hball]
      exact hmp.setIntegral_preimage_emb hemb F _
    have hIh : IntegrableOn (fun q => g (ιI q)) (Metric.ball p r)
        (parabolicVolume (Module.finrank ℝ W)) :=
      (hloc.integrableOn_isCompact (isCompact_closedBall p r)).mono_set
        Metric.ball_subset_closedBall
    set c := parabolicBallAverage W g P r with hc
    have havg : standardBallAverage (Module.finrank ℝ W)
        (fun p => ((g ((subspaceParabolicIsometry W).symm p) : W.orthogonal) : Spatial n) α)
        p r = b2vch_coord W α c := by
      rw [hc, parabolicBallAverage, map_smul, ← hint g,
        ← (b2vch_coord W α).integral_comp_comm hIh, ← hvol]
      rfl
    have hfin : parabolicVolume (Module.finrank ℝ W) (Metric.ball p r) ≠ ∞ :=
      measure_ball_lt_top.ne
    have hle : ∫ q in Metric.ball p r,
          ‖((g ((subspaceParabolicIsometry W).symm q) : W.orthogonal) : Spatial n) α -
            b2vch_coord W α c‖ ∂parabolicVolume (Module.finrank ℝ W) ≤
        ∫ y in Metric.ball P r, ‖g y - c‖ ∂intrinsicParabolicVolume W := by
      rw [← hint (fun y => ‖g y - c‖)]
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (hIh.sub (integrableOn_const hfin)).norm (Eventually.of_forall fun q => ?_)
      change ‖b2vch_coord W α (g (ιI q)) - b2vch_coord W α c‖ ≤ ‖g (ιI q) - c‖
      rw [← map_sub]
      exact b2vch_norm_coord_le W α _
    rw [havg, hvol]
    calc (∫ q in Metric.ball p r,
          ‖((g ((subspaceParabolicIsometry W).symm q) : W.orthogonal) : Spatial n) α -
            b2vch_coord W α c‖ ∂parabolicVolume (Module.finrank ℝ W)) /
          (intrinsicParabolicVolume W (Metric.ball P r)).toReal
        ≤ (∫ y in Metric.ball P r, ‖g y - c‖ ∂intrinsicParabolicVolume W) /
          (intrinsicParabolicVolume W (Metric.ball P r)).toReal := by
          gcongr
      _ ≤ B := hg.2.2 P r hr

end ParabolicRectifiability.Characterization
