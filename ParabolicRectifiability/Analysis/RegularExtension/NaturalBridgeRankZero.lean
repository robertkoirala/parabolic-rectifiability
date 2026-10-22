import ParabolicRectifiability.Analysis.RegularExtension.NaturalBridge

/-! # Three auxiliary statements for the natural bridge at rank zero (`m = 0`)

Proofs of `affineFit_le_modelCost_rank_zero`, `lintegral_comp_lift_le_of_mapsTo` and
`lift_mem_ball_of_lipschitz`, each under the name `<statement>_proof`.

* `affineFit_le_modelCost_rank_zero_proof`: at rank zero every vertical model is a
  line `{x₀} × ℝ`; compete with the constant `x₀ ∈ Wᗮ = ℝ^n` and `B = 0`.
* `lintegral_comp_lift_le_of_mapsTo_proof`: the
  `NaturalBridge.lintegral_comp_lift_le` with `hmaps` replacing `NaturalBridge.lift_mem_ball`.
* `lift_mem_ball_of_lipschitz_proof`: Pythagoras in `W ⊕ Wᗮ`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace ParabolicRectifiability

/-- Exact squared distance to a vertical model, for an arbitrary point of `Space n`. -/
theorem rx2_modelCost_vertical_eq {n k : ℕ} (M : Models n k .vertical) (z : Space n) :
    modelCost M z =
      ENNReal.ofReal (‖z.1 - (VerticalModel.spatial (n := n) (k := k) M).direction.starProjection z.1
        - (VerticalModel.spatial (n := n) (k := k) M).anchor‖ ^ 2) := by
  rcases z with ⟨x, ⟨t⟩⟩
  exact VerticalModel.modelCost_point (n := n) (k := k) M x t

/-- **`affineFit_le_modelCost_rank_zero`**: the affine fit at rank zero. -/
theorem affineFit_le_modelCost_rank_zero_proof {n : ℕ} (W : Submodule ℝ (Spatial n))
    (hW : Module.finrank ℝ W = 0) (K : Set (SubspaceSpace W))
    (f : SubspaceSpace W → W.orthogonal) (p : SubspaceSpace W) (r : ℝ)
    (M : Models n 2 .vertical) :
    ⨅ (a : W.orthogonal) (B : W →L[ℝ] W.orthogonal),
        ∫⁻ q in Metric.ball p r ∩ K, ‖f q - (a + B q.1)‖ₑ ^ 2 ∂intrinsicParabolicVolume W ≤
      ∫⁻ q in Metric.ball p r ∩ K,
        modelCost M (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n)
        ∂intrinsicParabolicVolume W := by
  have hW0 : W = ⊥ := Submodule.finrank_eq_zero.mp hW
  have hrk : VerticalModel.spatialRank (n := n) (k := 2) M = 0 := by
    have := VerticalModel.rank_eq (n := n) (k := 2) M
    omega
  have hdir : (VerticalModel.spatial (n := n) (k := 2) M).direction = ⊥ :=
    Submodule.finrank_eq_zero.mp ((VerticalModel.spatial (n := n) (k := 2) M).rank_eq.trans hrk)
  have hP : ∀ x : Spatial n,
      (VerticalModel.spatial (n := n) (k := 2) M).direction.starProjection x = 0 := fun x =>
    (Submodule.eq_bot_iff _).mp hdir _
      ((VerticalModel.spatial (n := n) (k := 2) M).direction.orthogonalProjectionOnto x).2
  have ha : (VerticalModel.spatial (n := n) (k := 2) M).anchor ∈ W.orthogonal := by
    rw [hW0, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  refine iInf_le_of_le ⟨_, ha⟩ (iInf_le_of_le 0 ?_)
  refine lintegral_mono fun q => ?_
  have hq : (q.1 : Spatial n) = 0 := (Submodule.eq_bot_iff W).mp hW0 _ q.1.2
  rw [rx2_modelCost_vertical_eq]
  dsimp only
  rw [hP, hq, zero_add, sub_zero, zero_apply, add_zero, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), ← Submodule.norm_coe, Submodule.coe_sub]

open NaturalBridge Metric in
/-- **`lintegral_comp_lift_le_of_mapsTo`**: the lift comparison under a mapping hypothesis. -/
theorem lintegral_comp_lift_le_of_mapsTo_proof {n : ℕ} (W : Submodule ℝ (Spatial n)) {m : ℕ}
    (hW : Module.finrank ℝ W = m) (K : Set (SubspaceSpace W)) (hK : IsCompact K)
    (f : SubspaceSpace W → W.orthogonal) (L : ℝ≥0) (hf : LipschitzOnWith L f K)
    (p : SubspaceSpace W) (r ρ : ℝ)
    (hmaps : ∀ q ∈ K, dist q p < r →
      (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n) ∈
        Metric.ball (((p.1 : Spatial n) + (f p : Spatial n), p.2) : Space n) ρ)
    (g : Space n → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ q in Metric.ball p r ∩ K, g (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n)
        ∂intrinsicParabolicVolume W ≤
      (2 * omega m) *
        ∫⁻ z in Metric.ball (((p.1 : Spatial n) + (f p : Spatial n), p.2) : Space n) ρ, g z
          ∂((hausdorffP n (m + 2)).restrict
            ((fun q : SubspaceSpace W =>
              (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n)) '' K)) := by
  change ∫⁻ q in ball p r ∩ K, g (lift W f q) ∂intrinsicParabolicVolume W ≤
      (2 * omega m) * ∫⁻ z in ball (lift W f p) ρ, g z
        ∂((hausdorffP n (m + 2)).restrict (lift W f '' K))
  subst hW
  have hs : MeasurableSet (ball p r ∩ K) := measurableSet_ball.inter hK.isClosed.measurableSet
  have hcont : ContinuousOn (lift W f) K := by
    unfold lift
    exact ((continuous_subtype_val.comp continuous_fst).continuousOn.add
      (continuous_subtype_val.comp_continuousOn hf.continuousOn)).prodMk
        continuous_snd.continuousOn
  have hΦ : AEMeasurable (lift W f) ((intrinsicParabolicVolume W).restrict (ball p r ∩ K)) :=
    (hcont.mono inter_subset_right).aemeasurable hs
  rw [← lintegral_map' hg.aemeasurable hΦ]
  have hω0 : (2 * omega (Module.finrank ℝ W)) ≠ 0 :=
    (ENNReal.mul_pos (by norm_num) (omega_pos _).ne').ne'
  have hωt : (2 * omega (Module.finrank ℝ W)) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (omega_lt_top _).ne
  have hle : Measure.map (lift W f) ((intrinsicParabolicVolume W).restrict (ball p r ∩ K)) ≤
      (2 * omega (Module.finrank ℝ W)) •
        ((hausdorffP n (Module.finrank ℝ W + 2)).restrict (lift W f '' K)).restrict
          (ball (lift W f p) ρ) := by
    rw [Measure.le_iff]
    intro S hS
    rw [Measure.map_apply_of_aemeasurable hΦ hS, Measure.restrict_apply' hs, Measure.smul_apply,
      smul_eq_mul, Measure.restrict_apply hS, Measure.restrict_apply (hS.inter measurableSet_ball)]
    set A := lift W f ⁻¹' S ∩ (ball p r ∩ K) with hA
    have h1 : intrinsicParabolicVolume W A ≤ 2 * omega (Module.finrank ℝ W) *
        Measure.hausdorffMeasure ((Module.finrank ℝ W + 2 : ℕ) : ℝ) A :=
      (ENNReal.inv_mul_le_iff hω0 hωt).mp (vertical_base_hausdorff_comparison W A).1
    have h2 : Measure.hausdorffMeasure ((Module.finrank ℝ W + 2 : ℕ) : ℝ) A ≤
        hausdorffP n (Module.finrank ℝ W + 2) (lift W f '' A) := by
      have himg : baseProj W '' (lift W f '' A) = A := by
        rw [image_image]
        simp only [baseProj_lift, image_id']
      have := (lipschitzWith_baseProj W).hausdorffMeasure_image_le
        (Nat.cast_nonneg (Module.finrank ℝ W + 2)) (lift W f '' A)
      rw [himg, ENNReal.coe_one, ENNReal.one_rpow, one_mul] at this
      exact this
    have h3 : lift W f '' A ⊆ S ∩ ball (lift W f p) ρ ∩ lift W f '' K := by
      rintro _ ⟨q, ⟨hqS, hqB, hqK⟩, rfl⟩
      exact ⟨⟨hqS, hmaps q hqK hqB⟩, mem_image_of_mem _ hqK⟩
    calc intrinsicParabolicVolume W A
        ≤ 2 * omega (Module.finrank ℝ W) *
            Measure.hausdorffMeasure ((Module.finrank ℝ W + 2 : ℕ) : ℝ) A := h1
      _ ≤ 2 * omega (Module.finrank ℝ W) *
            hausdorffP n (Module.finrank ℝ W + 2) (lift W f '' A) := mul_le_mul_right h2 _
      _ ≤ _ := mul_le_mul_right (measure_mono h3) _
  calc ∫⁻ z, g z ∂Measure.map (lift W f) ((intrinsicParabolicVolume W).restrict (ball p r ∩ K))
      ≤ ∫⁻ z, g z ∂((2 * omega (Module.finrank ℝ W)) •
          ((hausdorffP n (Module.finrank ℝ W + 2)).restrict (lift W f '' K)).restrict
            (ball (lift W f p) ρ)) := lintegral_mono' hle le_rfl
    _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]

/-- **`lift_mem_ball_of_lipschitz`**: the lift of a Lipschitz graph lies in the ball. -/
theorem lift_mem_ball_of_lipschitz_proof {n : ℕ} (W : Submodule ℝ (Spatial n))
    (K : Set (SubspaceSpace W)) (f : SubspaceSpace W → W.orthogonal) (L : ℝ≥0)
    (hf : LipschitzOnWith L f K) {p q : SubspaceSpace W} (hp : p ∈ K) (hq : q ∈ K) {r : ℝ}
    (hqp : dist q p < r) :
    (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n) ∈
      Metric.ball (((p.1 : Spatial n) + (f p : Spatial n), p.2) : Space n)
        (max 2 (Real.sqrt (1 + (L : ℝ) ^ 2)) * r) := by
  have hd : dist q p = max (dist q.1 p.1) (dist q.2 p.2) := Prod.dist_eq
  have h1 : dist q.1 p.1 ≤ dist q p := hd ▸ le_max_left _ _
  have h2 : dist q.2 p.2 ≤ dist q p := hd ▸ le_max_right _ _
  have hfq : dist (f q) (f p) ≤ L * dist q p := hf.dist_le_mul q hq p hp
  have hd0 : 0 ≤ dist q p := dist_nonneg
  have hr : 0 < r := lt_of_le_of_lt hd0 hqp
  have hs0 : 0 < Real.sqrt (1 + (L : ℝ) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hmax2 : (2 : ℝ) ≤ max 2 (Real.sqrt (1 + (L : ℝ) ^ 2)) := le_max_left _ _
  have hmaxs : Real.sqrt (1 + (L : ℝ) ^ 2) ≤ max 2 (Real.sqrt (1 + (L : ℝ) ^ 2)) :=
    le_max_right _ _
  -- spatial Pythagoras
  have hsp : ‖((q.1 : Spatial n) + (f q : Spatial n)) - ((p.1 : Spatial n) + (f p : Spatial n))‖
      ≤ Real.sqrt (1 + (L : ℝ) ^ 2) * dist q p := by
    have huv : ⟪(q.1 : Spatial n) - p.1, (f q : Spatial n) - f p⟫_ℝ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K := W) (W.sub_mem q.1.2 p.1.2)
        (W.orthogonal.sub_mem (f q).2 (f p).2)
    have heq : ((q.1 : Spatial n) + (f q : Spatial n)) - ((p.1 : Spatial n) + (f p : Spatial n))
        = ((q.1 : Spatial n) - p.1) + ((f q : Spatial n) - f p) := by abel
    have hu : ‖(q.1 : Spatial n) - p.1‖ ≤ dist q p := by
      rw [← dist_eq_norm, ← Subtype.dist_eq]; exact h1
    have hv : ‖(f q : Spatial n) - f p‖ ≤ L * dist q p := by
      rw [← dist_eq_norm, ← Subtype.dist_eq]; exact hfq
    have hu2 := mul_self_le_mul_self (norm_nonneg _) hu
    have hv2 := mul_self_le_mul_self (norm_nonneg _) hv
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_real huv
    rw [heq, ← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt (by positivity)]
    nlinarith [hpy, hu2, hv2]
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  constructor
  · change dist ((q.1 : Spatial n) + (f q : Spatial n)) ((p.1 : Spatial n) + (f p : Spatial n)) < _
    rw [dist_eq_norm]
    calc _ ≤ Real.sqrt (1 + (L : ℝ) ^ 2) * dist q p := hsp
      _ < Real.sqrt (1 + (L : ℝ) ^ 2) * r := mul_lt_mul_of_pos_left hqp hs0
      _ ≤ max 2 (Real.sqrt (1 + (L : ℝ) ^ 2)) * r := mul_le_mul_of_nonneg_right hmaxs hr.le
  · change dist q.2 p.2 < _
    nlinarith

end ParabolicRectifiability
