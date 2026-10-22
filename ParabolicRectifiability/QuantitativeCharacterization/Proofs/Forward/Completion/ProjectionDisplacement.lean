import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion
import ParabolicRectifiability.Geometry.Chart.InductionEstimates
import ParabolicRectifiability.Geometry.Chart.LimitChart

/-! # Compact displacement of the projection limit (`d1e_projection_displacement`)

Proves `d1e_projection_displacement_proof : d1e_ProjectionDisplacementStatement`.

Route (no square bound, no neck container).
* **Uniform convergence.** Below `δ₀ = deltaThreshold n σ` the smallness `DeltaSmall` holds
  (`smallness_of_le`), and the third clause of `induction_estimates_proof` gives
  `|F_{j+1} - F_j| ≤ ε r_j`, hence `|F_l - F_k| ≤ ε r_k / (1 - h)` (`norm_sub_le_geometric`).
  The stages are Cauchy, so they converge to their `limUnder` (convergence is proved before the
  value of `limUnder` is used), uniformly with error
  `ε r_N / (1 - h)`. Each stage is continuous (`contDiff_stage`), so `F⁰` is continuous.
* **Compact support.** By `parent_mem` and `parent_dist`, every centre `z_{j,a}` lies within
  `M₀ + (10/9) r₀` of a fixed point `O`, where `M₀ = ∑_{b ∈ I₀} d(z_{0,b}, O)` (finite root
  set). A level-`j` weight vanishes off the open parabolic ball `P(z_{j,a}, 3 r_j)`
  (`tsupport_parabolicWeight_subset`), so a stage map fixes every point at distance at least
  `B = M₀ + (10/9) r₀ + 3 r₀` from `O`. If `(F₀(u,t), t)` is such a point, induction gives
  `F_j(u,t) = F₀(u,t)` for all `j`, hence `F⁰(u,t) = F₀(u,t)`. Otherwise `|u| < B + |x_*|`
  (`U_*` is an isometry) and `|t| < B²`, a compact parameter set.

Helpers carry the prefix `d1edisp_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

open ParabolicRectifiability.Foundations
open CoherentChart

section Helpers

variable {n m : ℕ} {ι : Type*}

/-- Uniform convergence of the actual stages to the projection limit: under `DeltaSmall` and
coherence, `|F_N - F⁰| ≤ ε r_N / (1 - h)` at every parameter. -/
theorem d1edisp_stage_sub_limit_le {F : CoherentFamily n m ι} {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) (hF : F.IsCoherent σ δ) (P : InitialChart F)
    (N : ℕ) (u : Spatial m) (t : ℝ) :
    ‖stage F P N u t - d1e_projectionLimit F P u t‖ ≤
      chartEps n σ δ * F.scale N / (1 - ratio) := by
  have hε : 0 ≤ chartEps n σ δ := chartEps_nonneg hσ hδ
  have hstep : ∀ (i : ℕ), ‖stage F P (i + 1) u t - stage F P i u t‖ ≤
      chartEps n σ δ * F.scale i :=
    fun i => (induction_estimates_proof hσ hδ hsmall (hF i) P).2.2 i le_rfl u t
  have hdisp : ∀ k l : ℕ, k ≤ l →
      ‖stage F P l u t - stage F P k u t‖ ≤ chartEps n σ δ * F.scale k / (1 - ratio) :=
    fun k l hkl => norm_sub_le_geometric F (fun j => stage F P j u t) (chartEps n σ δ) hε
      hkl (fun i _ _ => hstep i)
  have hb : Tendsto (fun N => 2 * (chartEps n σ δ * F.scale N / (1 - ratio))) atTop (𝓝 0) := by
    have h := (((CoherentChart.tendsto_scale_zero F).const_mul (chartEps n σ δ)).div_const
      (1 - ratio)).const_mul 2
    rw [mul_zero, zero_div, mul_zero] at h
    exact h
  have hG : Tendsto (fun N => stage F P N u t) atTop (𝓝 (d1e_projectionLimit F P u t)) := by
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    refine cauchySeq_of_le_tendsto_0 _ (fun a b K ha hb' => ?_) hb
    calc dist (stage F P a u t) (stage F P b u t)
        ≤ dist (stage F P a u t) (stage F P K u t) + dist (stage F P b u t) (stage F P K u t) :=
          dist_triangle_right _ _ _
      _ ≤ chartEps n σ δ * F.scale K / (1 - ratio) + chartEps n σ δ * F.scale K / (1 - ratio) := by
          rw [dist_eq_norm, dist_eq_norm]
          exact add_le_add (hdisp K a ha) (hdisp K b hb')
      _ = 2 * (chartEps n σ δ * F.scale K / (1 - ratio)) := by ring
  have hlim : Tendsto (fun l => ‖stage F P N u t - stage F P l u t‖) atTop
      (𝓝 ‖stage F P N u t - d1e_projectionLimit F P u t‖) :=
    (tendsto_const_nhds.sub hG).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop N] with l hl
  rw [norm_sub_rev]
  exact hdisp N l hl

/-- Every centre lies within `M₀ + (10/9)(r₀ - r_j)` of `O`, where `M₀` sums the distances
of the finitely many root centres to `O` (`parent_mem`, `parent_dist`). -/
theorem d1edisp_center_dist_le {F : CoherentFamily n m ι} {σ δ : ℝ} (hF : F.IsCoherent σ δ)
    (O : Space n) (j : ℕ) :
    ∀ a ∈ F.index j, dist (F.center j a) O ≤
      (∑ b ∈ F.index 0, dist (F.center 0 b) O) + 10 / 9 * F.scale 0 - 10 / 9 * F.scale j := by
  induction j with
  | zero =>
    intro a ha
    have h := Finset.single_le_sum (f := fun b => dist (F.center 0 b) O)
      (fun b _ => dist_nonneg) ha
    linarith
  | succ j ih =>
    intro a ha
    have hp := (hF (j + 1)).parent_mem j le_rfl a ha
    have hd := (hF (j + 1)).parent_dist j le_rfl a ha
    have h1 := ih _ hp
    have hs := scale_succ F j
    have htri := dist_triangle (F.center (j + 1) a) (F.center j (F.parent (j + 1) a)) O
    rw [hs]
    unfold ratio
    linarith

/-- A uniform bound `B₀` for all centres. -/
theorem d1edisp_center_dist_le' {F : CoherentFamily n m ι} {σ δ : ℝ} (hF : F.IsCoherent σ δ)
    (O : Space n) (j : ℕ) (a : ι) (ha : a ∈ F.index j) :
    dist (F.center j a) O ≤ (∑ b ∈ F.index 0, dist (F.center 0 b) O) + 10 / 9 * F.scale 0 := by
  have h := d1edisp_center_dist_le hF O j a ha
  have := (scale_pos F j).le
  linarith

/-- `r_j ≤ r₀`. -/
theorem d1edisp_scale_le_zero (F : CoherentFamily n m ι) (j : ℕ) : F.scale j ≤ F.scale 0 := by
  unfold CoherentFamily.scale coherentScale
  rw [pow_zero, div_one]
  exact div_le_self F.initialRadius_pos.le (one_le_pow₀ (by norm_num))

/-- A stage map fixes every point far from all centres. -/
theorem d1edisp_stageMap_eq_self {F : CoherentFamily n m ι} {σ δ : ℝ}
    (hF : F.IsCoherent σ δ) (O : Space n) (j : ℕ) (x : Spatial n) (t : ℝ)
    (hfar : (∑ b ∈ F.index 0, dist (F.center 0 b) O) + 10 / 9 * F.scale 0 + 3 * F.scale 0 ≤
      dist (point x t) O) :
    stageMap F j x t = x := by
  have hw : ∀ a ∈ F.index j, weight F j a x t = 0 := by
    intro a ha
    by_contra hne
    have hmem : (x, t) ∈ tsupport (parabolicWeight (F.scale j) (F.index j) (F.center j) a) :=
      subset_tsupport _ (Function.mem_support.2 hne)
    have hball := tsupport_parabolicWeight_subset (scale_pos F j) (F.index j) (F.center j) a hmem
    rw [Metric.mem_ball] at hball
    have hc := d1edisp_center_dist_le' hF O j a ha
    have hsj := d1edisp_scale_le_zero F j
    have htri := dist_triangle (point x t) (F.center j a) O
    have : dist (point (x, t).1 (x, t).2) (F.center j a) = dist (point x t) (F.center j a) := rfl
    linarith
  have hsum : ∑ a ∈ F.index j, weight F j a x t • ((F.plane j a).projection x - x) = 0 :=
    Finset.sum_eq_zero fun a ha => by rw [hw a ha, zero_smul]
  unfold stageMap CoherentProjection.sigma
  rw [hsum, add_zero]

/-- Far from all centres the stages never move, and the projection limit equals `F₀`. -/
theorem d1edisp_limit_eq_initial {F : CoherentFamily n m ι} {σ δ : ℝ}
    (hF : F.IsCoherent σ δ) (P : InitialChart F) (O : Space n) (u : Spatial m) (t : ℝ)
    (hfar : (∑ b ∈ F.index 0, dist (F.center 0 b) O) + 10 / 9 * F.scale 0 + 3 * F.scale 0 ≤
      dist (point (P.origin + P.isometry u) t) O) :
    d1e_projectionLimit F P u t = P.origin + P.isometry u := by
  have hconst : ∀ j, stage F P j u t = P.origin + P.isometry u := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      show stageMap F j (stage F P j u t) t = _
      rw [ih]
      exact d1edisp_stageMap_eq_self hF O j _ t hfar
  have hfun : (fun j => stage F P j u t) = fun _ => P.origin + P.isometry u := funext hconst
  unfold d1e_projectionLimit
  rw [hfun]
  exact tendsto_const_nhds.limUnder_eq

end Helpers

/-- **Compact displacement of the projection limit**: the type
`d1e_ProjectionDisplacementStatement`. -/
theorem d1e_projection_displacement_proof : d1e_ProjectionDisplacementStatement := by
  intro n σ hσ _hσ₁
  refine ⟨deltaThreshold n σ, deltaThreshold_pos hσ, ?_⟩
  intro m ι F δ hδ hδ₀ hF P
  obtain ⟨hsmall, -, -, -⟩ := smallness_of_le (E := 0) (κ := 0) hσ hδ hδ₀
    (energyThreshold_pos hσ).le (by norm_num [heightThreshold])
  -- continuity: uniform limit of continuous stages
  have hval : Continuous (fun p : Space m => p.2.val) :=
    Metric.Snowflaking.continuous_ofSnowflaking.comp continuous_snd
  have hstage : ∀ N : ℕ, Continuous (fun p : Space m => stage F P N p.1 p.2.val) := fun N =>
    (contDiff_stage F P N).continuous.comp (continuous_fst.prodMk hval)
  have hunif : TendstoUniformly (fun (N : ℕ) (p : Space m) => stage F P N p.1 p.2.val)
      (fun p : Space m => d1e_projectionLimit F P p.1 p.2.val) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hb : Tendsto (fun N => chartEps n σ δ * F.scale N / (1 - ratio)) atTop (𝓝 0) := by
      have h := ((CoherentChart.tendsto_scale_zero F).const_mul (chartEps n σ δ)).div_const
        (1 - ratio)
      rw [mul_zero, zero_div] at h
      exact h
    filter_upwards [(tendsto_order.1 hb).2 ε hε] with N hN p
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (d1edisp_stage_sub_limit_le hσ hδ hsmall hF P N p.1 p.2.val) hN
  have hcont0 : Continuous (fun p : Space m => d1e_projectionLimit F P p.1 p.2.val) :=
    hunif.continuous (Frequently.of_forall hstage)
  have hcont : Continuous (fun p : Space m =>
      d1e_projectionLimit F P p.1 p.2.val - (P.origin + P.isometry p.1)) :=
    hcont0.sub (continuous_const.add (P.isometry.continuous.comp continuous_fst))
  refine ⟨hcont, ?_⟩
  -- compact support
  set O : Space n := point 0 0 with hO
  set B : ℝ := (∑ b ∈ F.index 0, dist (F.center 0 b) O) + 10 / 9 * F.scale 0 + 3 * F.scale 0
    with hB
  have hBpos : 0 < B := by
    have h0 : 0 ≤ ∑ b ∈ F.index 0, dist (F.center 0 b) O :=
      Finset.sum_nonneg fun b _ => dist_nonneg
    have := scale_pos F 0
    rw [hB]
    linarith
  have hKc : IsCompact ((fun q : Spatial m × ℝ => point q.1 q.2) ''
      (Metric.closedBall (0 : Spatial m) (B + ‖P.origin‖) ×ˢ Icc (-B ^ 2) (B ^ 2))) := by
    refine ((isCompact_closedBall _ _).prod isCompact_Icc).image ?_
    exact continuous_fst.prodMk (Metric.Snowflaking.continuous_toSnowflaking.comp continuous_snd)
  refine HasCompactSupport.intro hKc fun p hp => ?_
  by_cases hfar : B ≤ dist (point (P.origin + P.isometry p.1) p.2.val) O
  · rw [d1edisp_limit_eq_initial hF P O p.1 p.2.val hfar, sub_self]
  · exfalso
    apply hp
    rw [not_le] at hfar
    rw [hO, dist_point, sub_zero, sub_zero, max_lt_iff] at hfar
    obtain ⟨hx, ht⟩ := hfar
    refine ⟨(p.1, p.2.val), ⟨?_, ?_⟩, rfl⟩
    · show dist p.1 0 ≤ B + ‖P.origin‖
      rw [dist_zero_right]
      have h1 : ‖P.isometry p.1‖ = ‖p.1‖ := P.isometry.norm_map p.1
      have h2 := norm_sub_le (P.origin + P.isometry p.1) P.origin
      rw [add_sub_cancel_left] at h2
      linarith
    · show -B ^ 2 ≤ p.2.val ∧ p.2.val ≤ B ^ 2
      rw [Real.sqrt_lt' hBpos] at ht
      have h := abs_lt.1 ht
      exact ⟨h.1.le, h.2.le⟩

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
