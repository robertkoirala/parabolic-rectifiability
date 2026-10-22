import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Metric.Measure

/-! # Measurability of compact trace errors

For a compact trace set `K`, a trace `f` that is Lipschitz on `K` and finite-dimensional
values, the squared trace error `γ_K(p,r)^2` is jointly measurable in `(p,r)`, and so is
its scale integral in `p`.

Route. Only `f` on `K` enters, so `f` is replaced by its zero extension `g` off `K`, which
is Borel since `f` is continuous on the closed set `K`. For a fixed affine competitor
`(a,B)` the fit integral `∫_{P(p,r)} |g - a - B u|^2 d(vol⌞K)` is jointly measurable in
`(p,r)` (Tonelli for the finite measure `vol⌞K` and the open incidence set
`{dist(q,p) < r}`). For fixed `(p,r)` it is continuous in `(a,B)`: its square root is an
`L^2` norm, which moves by at most `(1 + D) |(a,B) - (a',B')| vol(K)^{1/2}` on the bounded
set `K ⊆ {|u| ≤ D}`. Hence the infimum over all competitors equals the infimum over a
dense sequence, a countable infimum of measurable functions.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

section CongrAE

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The unrestricted affine error only sees the values almost everywhere. -/
theorem affineErrorSq_congr_ae {μ : Measure (E × Time)} {f g : E × Time → Y}
    (h : f =ᵐ[μ] g) (y : E × Time) (s : ℝ) :
    affineErrorSq μ f y s = affineErrorSq μ g y s := by
  unfold affineErrorSq affineFitIntegral
  split_ifs with hs
  · congr 1
    refine iInf_congr fun a => iInf_congr fun B => lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae h] with q hq
    rw [hq]
  · rfl

end CongrAE

section FitContinuity

variable {α E Y : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- For a finite measure and an a.e. bound `‖u‖ ≤ D`, the squared `L²` distance from `g` to the
affine competitor `a + B ∘ u` depends continuously on `(a, B)`: its square root moves by at
most `(1 + D) μ(α)^{1/2}` times the distance of the competitors. -/
theorem continuous_lintegral_enorm_sub_affine_sq (μ : Measure α) [IsFiniteMeasure μ]
    {g : α → Y} {u : α → E} (hg : AEStronglyMeasurable g μ) (hu : AEStronglyMeasurable u μ)
    {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ᵐ q ∂μ, ‖u q‖ ≤ D) :
    Continuous fun x : Y × (E →L[ℝ] Y) => ∫⁻ q, ‖g q - (x.1 + x.2 (u q))‖ₑ ^ 2 ∂μ := by
  have hA : ∀ x : Y × (E →L[ℝ] Y), AEStronglyMeasurable (fun q => x.1 + x.2 (u q)) μ :=
    fun x => (x.2.continuous.comp_aestronglyMeasurable hu).const_add x.1
  have hsq : ∀ x : Y × (E →L[ℝ] Y), ∫⁻ q, ‖g q - (x.1 + x.2 (u q))‖ₑ ^ 2 ∂μ =
      eLpNorm (fun q => g q - (x.1 + x.2 (u q))) 2 μ ^ 2 := by
    intro x
    have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := 2) two_ne_zero (hg.sub (hA x))
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] at h
    exact h.symm
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0∞, C = μ univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (1 + D) :=
    ⟨_, rfl⟩
  have hCtop : C ≠ ⊤ := by
    rw [hC]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)) ENNReal.ofReal_ne_top
  have hbd : ∀ x y : Y × (E →L[ℝ] Y),
      ∀ᵐ q ∂μ, ‖(y.1 + y.2 (u q)) - (x.1 + x.2 (u q))‖ ≤ (1 + D) * dist x y := by
    intro x y
    filter_upwards [hD] with q hq
    have h1 : ‖y.1 - x.1‖ ≤ dist x y := by
      rw [dist_comm, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
      exact le_max_left _ _
    have h2 : ‖y.2 - x.2‖ ≤ dist x y := by
      rw [dist_comm, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
      exact le_max_right _ _
    have h3 : (y.2 - x.2) (u q) = y.2 (u q) - x.2 (u q) := by simp
    calc ‖(y.1 + y.2 (u q)) - (x.1 + x.2 (u q))‖ = ‖(y.1 - x.1) + (y.2 - x.2) (u q)‖ := by
          rw [h3]
          congr 1
          abel
      _ ≤ ‖y.1 - x.1‖ + ‖y.2 - x.2‖ * ‖u q‖ :=
          (norm_add_le _ _).trans (add_le_add le_rfl ((y.2 - x.2).le_opNorm _))
      _ ≤ dist x y + dist x y * D :=
          add_le_add h1 (mul_le_mul h2 hq (norm_nonneg _) dist_nonneg)
      _ = (1 + D) * dist x y := by ring
  have hN : ∀ x y : Y × (E →L[ℝ] Y),
      eLpNorm (fun q => g q - (x.1 + x.2 (u q))) 2 μ ≤
        eLpNorm (fun q => g q - (y.1 + y.2 (u q))) 2 μ + C * edist x y := by
    intro x y
    have hsplit : (fun q => g q - (x.1 + x.2 (u q))) =
        (fun q => g q - (y.1 + y.2 (u q))) + (fun q => (y.1 + y.2 (u q)) - (x.1 + x.2 (u q))) := by
      funext q
      simp only [Pi.add_apply]
      abel
    rw [hsplit]
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add le_rfl ?_)
    refine (eLpNorm_le_of_ae_bound ((hA y).sub (hA x)) (hbd x y)).trans (le_of_eq ?_)
    rw [hC, edist_dist, mul_assoc, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 + D by linarith)]
  exact ((ENNReal.continuous_pow 2).comp (continuous_of_le_add_edist C hCtop hN)).congr
    fun x => (hsq x).symm

end FitContinuity

/-- The infimum of a continuous function equals its infimum over a dense sequence. -/
theorem iInf_eq_iInf_denseRange {X : Type*} [TopologicalSpace X] {d : ℕ → X}
    (hd : DenseRange d) {φ : X → ℝ≥0∞} (hφ : Continuous φ) : ⨅ x, φ x = ⨅ i, φ (d i) := by
  refine le_antisymm (le_iInf fun i => iInf_le _ (d i)) (le_iInf fun x => ?_)
  exact hd.induction_on (p := fun x => (⨅ i, φ (d i)) ≤ φ x) x
    (isClosed_le continuous_const hφ) (fun i => iInf_le _ i)

/-- Ball integrals of a fixed measurable integrand are jointly measurable in the center and
the radius. -/
theorem measurable_setLIntegral_ball {m : ℕ} (ν : Measure (Space m)) [SFinite ν]
    {F : Space m → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun z : Space m × ℝ => ∫⁻ q in Metric.ball z.1 z.2, F q ∂ν := by
  have hset : MeasurableSet {w : (Space m × ℝ) × Space m | dist w.2 w.1.1 < w.1.2} :=
    measurableSet_lt (measurable_snd.dist (measurable_fst.comp measurable_fst))
      (measurable_snd.comp measurable_fst)
  have hint : Measurable fun w : (Space m × ℝ) × Space m =>
      {w : (Space m × ℝ) × Space m | dist w.2 w.1.1 < w.1.2}.indicator (fun w => F w.2) w :=
    (hF.comp measurable_snd).indicator hset
  have hrw : (fun z : Space m × ℝ => ∫⁻ q in Metric.ball z.1 z.2, F q ∂ν) = fun z =>
      ∫⁻ q, {w : (Space m × ℝ) × Space m | dist w.2 w.1.1 < w.1.2}.indicator
        (fun w => F w.2) (z, q) ∂ν := by
    funext z
    rw [← lintegral_indicator measurableSet_ball]
    congr 1
  rw [hrw]
  exact hint.lintegral_prod_right'

/-- **Measurability of the trace error** for a compact trace set; the statement of
`measurable_traceErrorSq_of_isCompact`. -/
theorem measurable_traceErrorSq_of_isCompact_proof {m : ℕ} {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] (K : Set (Space m)) (hK : IsCompact K)
    (f : Space m → Y) (L : ℝ≥0) (hf : LipschitzOnWith L f K) :
    Measurable (fun p : Space m × ℝ => traceErrorSq (parabolicVolume m) K f p.1 p.2) ∧
      ∀ R : ℝ, Measurable (fun p : Space m =>
        ∫⁻ r in Ioo 0 R, traceErrorSq (parabolicVolume m) K f p r ∂scaleMeasure) := by
  classical
  let _ : MeasurableSpace Y := borel Y
  have _ : BorelSpace Y := ⟨rfl⟩
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have _ : IsFiniteMeasure ((parabolicVolume m).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  -- the zero extension of the trace is Borel and equals `f` on `K`
  obtain ⟨g, hgm, hfg⟩ : ∃ g : Space m → Y, Measurable g ∧
      f =ᵐ[(parabolicVolume m).restrict K] g := by
    refine ⟨K.piecewise f 0, hf.continuousOn.measurable_piecewise continuous_zero.continuousOn hKm,
      ?_⟩
    filter_upwards [ae_restrict_mem hKm] with q hq
    rw [Set.piecewise_eq_of_mem _ _ _ hq]
  -- the trace set is spatially bounded
  obtain ⟨D₀, hD₀⟩ := hK.exists_bound_of_continuousOn
    (continuous_fst.continuousOn : ContinuousOn (fun q : Space m => q.1) K)
  obtain ⟨D, hD0, hDK⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ q ∈ K, ‖q.1‖ ≤ D :=
    ⟨max D₀ 0, le_max_right _ _, fun q hq => (hD₀ q hq).trans (le_max_left _ _)⟩
  -- the fit integrals of fixed competitors
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Y × (Spatial m →L[ℝ] Y) → Space m × ℝ → ℝ≥0∞, Φ = fun x z =>
      ∫⁻ q in Metric.ball z.1 z.2, ‖g q - (x.1 + x.2 q.1)‖ₑ ^ 2 ∂(parabolicVolume m).restrict K :=
    ⟨_, rfl⟩
  have hΦm : ∀ x, Measurable (Φ x) := fun x => by
    rw [hΦ]
    exact measurable_setLIntegral_ball _ ((hgm.sub (measurable_const.add
      (x.2.continuous.measurable.comp measurable_fst))).enorm.pow_const 2)
  have hΦc : ∀ z : Space m × ℝ, Continuous fun x => Φ x z := fun z => by
    rw [hΦ]
    exact continuous_lintegral_enorm_sub_affine_sq
      (((parabolicVolume m).restrict K).restrict (Metric.ball z.1 z.2)) hgm.aestronglyMeasurable
      measurable_fst.aestronglyMeasurable hD0
      (ae_restrict_of_ae ((ae_restrict_mem hKm).mono fun q hq => hDK q hq))
  -- reduction of the infimum to a dense sequence
  have hd := TopologicalSpace.denseRange_denseSeq (Y × (Spatial m →L[ℝ] Y))
  have hinf : ∀ z, (⨅ (a : Y) (B : Spatial m →L[ℝ] Y), Φ (a, B) z) =
      ⨅ i, Φ (TopologicalSpace.denseSeq (Y × (Spatial m →L[ℝ] Y)) i) z := by
    intro z
    exact (iInf_prod (f := fun x => Φ x z)).symm.trans (iInf_eq_iInf_denseRange hd (hΦc z))
  have heq : (fun p : Space m × ℝ => traceErrorSq (parabolicVolume m) K f p.1 p.2) =
      fun z => if 0 < z.2 then (ENNReal.ofReal z.2)⁻¹ ^ (baseDimension (Spatial m) + 2) *
        ⨅ i, Φ (TopologicalSpace.denseSeq (Y × (Spatial m →L[ℝ] Y)) i) z else 0 := by
    funext z
    change affineErrorSq ((parabolicVolume m).restrict K) f z.1 z.2 = _
    rw [affineErrorSq_congr_ae hfg, ← hinf z, hΦ]
    rfl
  have h1 : Measurable (fun p : Space m × ℝ => traceErrorSq (parabolicVolume m) K f p.1 p.2) := by
    rw [heq]
    refine Measurable.ite (measurableSet_lt measurable_const measurable_snd) ?_ measurable_const
    exact ((ENNReal.measurable_ofReal.comp measurable_snd).inv.pow_const _).mul
      (Measurable.iInf fun i => hΦm _)
  exact ⟨h1, fun R => h1.lintegral_prod_right'⟩

end ParabolicRectifiability
