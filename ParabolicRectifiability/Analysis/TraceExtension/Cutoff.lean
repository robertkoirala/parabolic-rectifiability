import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Data
import ParabolicRectifiability.Analysis.SmoothCutoff.ParabolicBump

/-! # Parabolic cutoffs and the buffered exterior source

Three auxiliary statements of the trace localization: parabolic cutoffs, their
Lipschitz behaviour, and the buffered exterior source. They live in the namespace
`TraceExtension`.

* `exists_parabolic_cutoff`: the parabolic bump
  `ψ(x,t) = a(|x - x₀|²/R₀²) b((t - t₀)/R₀²)` of `SmoothCutoff` at radius `R₀` is one
  on `P(z₀, 2R₀)`,
  supported in the closed set `{|x - x₀|² ≤ 8R₀², |t - t₀| ≤ 8R₀²} ⊆ P(z₀, 3R₀)`, and
  has the bounds `B/R₀`, `B/R₀²`, `B/R₀²` with `B = bumpBound m`.
* `cutoff_lipschitz`: a cutoff with these bounds is
  `max(2K,1)/R₀`-Lipschitz for the parabolic metric (mean value theorem in space and
  time; `|t - s| ≤ d²`; the values lie in `[0,1]` for `d > R₀`). The product rule
  `H(p) - H(q) = χ(p)(F(p) - F(q)) + (χ(p) - χ(q))(F(q) - F(z₀))`, applied with `q` in
  the support where `|F(q) - F(z₀)| ≤ 4 L R₀`, gives `Lip H ≤ (1 + 4 max(2K,1)) L`.
  The closed support lies in the compact closed ball `P̄(z₀, 4R₀)`.
* `buffered_exterior_source`: the gap `32 - 4 = 28 ≥ 8`
  keeps `f*` `L`-Lipschitz; the density holds with `c = v/(2·128^k)`, `v = 2ω_m`,
  in the three ranges `r ≤ 1`, `1 < r < 128`, `r ≥ 128`; on scales `r ≤ 31` the
  exterior piece does not meet `P(x,r)`, so the energy is the given trace energy
  (`31 < 2/ρ`), and for `r > 31` the zero comparison gives
  `κ² ≤ r^{-2} (8L)² |P̄(0,4)|`, whose `dr/r` integral is at most `1/2` of that mass.
  `C = 32 v 4^k`. The accompanying `buffered_exterior_source_support` records the
  Borel support and the source domination `σ ≤ dp` used by the extension theorem.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

namespace TraceExtension

/-- A parabolic cutoff at scale `R₀`: values in `[0,1]`, parabolic derivative bounds `K`
at scale `R₀` with `K` depending only on `m`, equal to one on `P(z₀, R₀)` and with closed
support in `P(z₀, 4R₀)`. -/
theorem exists_parabolic_cutoff (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z₀ : Space m) (R₀ : ℝ), 0 < R₀ →
      ∃ χ : Space m → ℝ, HasParabolicDerivBounds χ K R₀ ∧ (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) ∧
        (∀ p ∈ Metric.ball z₀ R₀, χ p = 1) ∧ tsupport χ ⊆ Metric.ball z₀ (4 * R₀) := by
  refine ⟨SmoothCutoff.bumpBound m, SmoothCutoff.bumpBound_nonneg m, fun z₀ R₀ hR => ?_⟩
  refine ⟨fun p => SmoothCutoff.parabolicBump R₀ z₀ (p.1, p.2.val), ?_, ?_, ?_, ?_⟩
  · exact
      { contDiff := (SmoothCutoff.contDiff_parabolicBump R₀ z₀).of_le
          ENat.LEInfty.out
        spatial_le := fun u t => SmoothCutoff.norm_fderiv_parabolicBump_spatial_le hR z₀ t u
        spatial₂_le := fun u t =>
          SmoothCutoff.norm_fderiv_fderiv_parabolicBump_spatial_le hR z₀ t u
        time_le := fun u t => SmoothCutoff.abs_deriv_parabolicBump_time_le hR z₀ u t }
  · exact fun p => ⟨SmoothCutoff.parabolicBump_nonneg _ _ _,
      SmoothCutoff.parabolicBump_le_one _ _ _⟩
  · intro p hp
    exact SmoothCutoff.parabolicBump_eq_one hR
      (Metric.ball_subset_ball (by linarith) hp : p ∈ Metric.ball z₀ (2 * R₀))
  · have hcl : IsClosed {p : Space m | (p.1, p.2.val) ∈ SmoothCutoff.bumpSupportSet R₀ z₀} :=
      (SmoothCutoff.isClosed_bumpSupportSet R₀ z₀).preimage
        (continuous_fst.prodMk continuous_time)
    refine (closure_minimal (fun p hp => ?_) hcl).trans fun p hp => ?_
    · by_contra h
      exact hp (SmoothCutoff.parabolicBump_eq_zero hR h)
    · have h3 := SmoothCutoff.point_mem_ball_of_mem_bumpSupportSet hR
        (hp : (p.1, p.2.val) ∈ SmoothCutoff.bumpSupportSet R₀ z₀)
      exact Metric.ball_subset_ball (by linarith) h3

/-- A cutoff with parabolic derivative bounds `K` at scale `R₀` and values in `[0,1]`
is `max(2K,1)/R₀`-Lipschitz for the parabolic metric. -/
theorem abs_sub_le_of_hasParabolicDerivBounds {m : ℕ} {χ : Space m → ℝ} {K R₀ : ℝ}
    (hR : 0 < R₀) (hχ : HasParabolicDerivBounds χ K R₀) (h01 : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1)
    (p q : Space m) : |χ p - χ q| ≤ max (2 * K) 1 / R₀ * dist p q := by
  have hK : 0 ≤ K := by
    have h := (norm_nonneg _).trans (hχ.spatial_le 0 0)
    rwa [le_div_iff₀ hR, zero_mul] at h
  have hds : ∀ t : ℝ, Differentiable ℝ (fun v : Spatial m => χ (point v t)) := fun t =>
    (hχ.contDiff.comp (contDiff_id.prodMk contDiff_const)).differentiable two_ne_zero
  have hdt : ∀ u : Spatial m, Differentiable ℝ (fun s : ℝ => χ (point u s)) := fun u =>
    (hχ.contDiff.comp (contDiff_const.prodMk contDiff_id)).differentiable two_ne_zero
  set d := dist p q with hd_def
  have hd0 : 0 ≤ d := dist_nonneg
  have hpq : d = max ‖p.1 - q.1‖ (Real.sqrt |p.2.val - q.2.val|) :=
    dist_point p.1 q.1 p.2.val q.2.val
  have hx : ‖p.1 - q.1‖ ≤ d := by rw [hpq]; exact le_max_left _ _
  have ht : |p.2.val - q.2.val| ≤ d ^ 2 :=
    (Real.sqrt_le_left hd0).1 (by rw [hpq]; exact le_max_right _ _)
  -- spatial and time steps
  have hspace : |χ (point p.1 p.2.val) - χ (point q.1 p.2.val)| ≤ K / R₀ * ‖p.1 - q.1‖ := by
    have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun v _ => (hds p.2.val) v) (fun v _ => hχ.spatial_le v p.2.val)
      (mem_univ q.1) (mem_univ p.1)
    rwa [Real.norm_eq_abs] at h
  have htime : |χ (point q.1 p.2.val) - χ (point q.1 q.2.val)| ≤
      K / R₀ ^ 2 * |p.2.val - q.2.val| := by
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun s _ => (hdt q.1) s) (fun s _ => by
        rw [Real.norm_eq_abs]; exact hχ.time_le q.1 s) (mem_univ q.2.val) (mem_univ p.2.val)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hsum : |χ p - χ q| ≤ K / R₀ * d + K / R₀ ^ 2 * d ^ 2 := by
    have e1 : χ p = χ (point p.1 p.2.val) := rfl
    have e2 : χ q = χ (point q.1 q.2.val) := rfl
    calc |χ p - χ q| ≤ |χ (point p.1 p.2.val) - χ (point q.1 p.2.val)| +
          |χ (point q.1 p.2.val) - χ (point q.1 q.2.val)| := by
          rw [e1, e2]; exact abs_sub_le _ _ _
      _ ≤ K / R₀ * d + K / R₀ ^ 2 * d ^ 2 := by
          refine add_le_add (hspace.trans ?_) (htime.trans ?_)
          · exact mul_le_mul_of_nonneg_left hx (div_nonneg hK hR.le)
          · exact mul_le_mul_of_nonneg_left ht (div_nonneg hK (by positivity))
  have hM1 : 1 ≤ max (2 * K) 1 := le_max_right _ _
  rcases le_or_gt d R₀ with hdR | hdR
  · have e : K / R₀ ^ 2 * d ^ 2 = (K / R₀ * d) * (d / R₀) := by
      field_simp
    have h1 : K / R₀ ^ 2 * d ^ 2 ≤ K / R₀ * d := by
      rw [e]
      exact mul_le_of_le_one_right (mul_nonneg (div_nonneg hK hR.le) hd0)
        ((div_le_one hR).2 hdR)
    calc |χ p - χ q| ≤ K / R₀ * d + K / R₀ * d := hsum.trans (by linarith)
      _ = 2 * K / R₀ * d := by ring
      _ ≤ max (2 * K) 1 / R₀ * d :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _) hR.le) hd0
  · have h1 : |χ p - χ q| ≤ 1 :=
      abs_sub_le_iff.2 ⟨by linarith [h01 p, h01 q], by linarith [h01 p, h01 q]⟩
    have h2 : 1 < d / R₀ := (one_lt_div hR).2 hdR
    calc |χ p - χ q| ≤ 1 := h1
      _ ≤ max (2 * K) 1 * (d / R₀) := one_le_mul_of_one_le_of_one_le hM1 h2.le
      _ = max (2 * K) 1 / R₀ * d := by ring

/-- Lipschitz part of the cutoff lemma: for a cutoff `χ` as in `exists_parabolic_cutoff`
and an `L`-Lipschitz `F`, the function `χ (F - F(z₀))` is `C L`-Lipschitz and compactly
supported, with `C` depending only on `K`. -/
theorem cutoff_lipschitz (m : ℕ) (K : ℝ) :
    ∃ C : ℝ≥0, ∀ (z₀ : Space m) (R₀ : ℝ), 0 < R₀ → ∀ χ : Space m → ℝ,
      HasParabolicDerivBounds χ K R₀ → (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) →
      tsupport χ ⊆ Metric.ball z₀ (4 * R₀) →
      ∀ {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (F : Space m → Y)
        (L : ℝ≥0), LipschitzWith L F →
        LipschitzWith (C * L) (fun p => χ p • (F p - F z₀)) ∧
          HasCompactSupport (fun p => χ p • (F p - F z₀)) := by
  have hC0 : (0 : ℝ) ≤ 1 + 4 * max (2 * K) 1 :=
    add_nonneg zero_le_one (mul_nonneg (by norm_num) (le_max_of_le_right zero_le_one))
  refine ⟨Real.toNNReal (1 + 4 * max (2 * K) 1), ?_⟩
  intro z₀ R₀ hR χ hχ h01 hsupp Y _ _ F L hF
  have hlipχ := abs_sub_le_of_hasParabolicDerivBounds hR hχ h01
  have hM : (0 : ℝ) ≤ max (2 * K) 1 := le_max_of_le_right zero_le_one
  have hsup : ∀ q, χ q ≠ 0 → dist q z₀ < 4 * R₀ := fun q hq =>
    Metric.mem_ball.1 (hsupp (subset_tsupport _ hq))
  have key : ∀ p q, χ q ≠ 0 → ‖χ p • (F p - F z₀) - χ q • (F q - F z₀)‖ ≤
      (1 + 4 * max (2 * K) 1) * L * dist p q := by
    intro p q hq
    have hdecomp : χ p • (F p - F z₀) - χ q • (F q - F z₀) =
        χ p • (F p - F q) + (χ p - χ q) • (F q - F z₀) := by
      simp only [smul_sub, sub_smul]
      abel
    rw [hdecomp]
    have h1 : ‖χ p • (F p - F q)‖ ≤ L * dist p q := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (h01 p).1, ← dist_eq_norm]
      exact (mul_le_of_le_one_left dist_nonneg (h01 p).2).trans (hF.dist_le_mul p q)
    have hFq : dist (F q) (F z₀) ≤ L * (4 * R₀) :=
      (hF.dist_le_mul q z₀).trans (mul_le_mul_of_nonneg_left (hsup q hq).le L.coe_nonneg)
    have h2 : ‖(χ p - χ q) • (F q - F z₀)‖ ≤ 4 * max (2 * K) 1 * L * dist p q := by
      rw [norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
      calc |χ p - χ q| * dist (F q) (F z₀)
          ≤ (max (2 * K) 1 / R₀ * dist p q) * (L * (4 * R₀)) :=
            mul_le_mul (hlipχ p q) hFq dist_nonneg
              (mul_nonneg (div_nonneg hM hR.le) dist_nonneg)
        _ = 4 * max (2 * K) 1 * L * dist p q := by
            field_simp
    calc ‖χ p • (F p - F q) + (χ p - χ q) • (F q - F z₀)‖
        ≤ ‖χ p • (F p - F q)‖ + ‖(χ p - χ q) • (F q - F z₀)‖ := norm_add_le _ _
      _ ≤ L * dist p q + 4 * max (2 * K) 1 * L * dist p q := add_le_add h1 h2
      _ = (1 + 4 * max (2 * K) 1) * L * dist p q := by ring
  refine ⟨LipschitzWith.of_dist_le_mul fun p q => ?_, ?_⟩
  · rw [dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _ hC0]
    by_cases hq : χ q = 0
    · by_cases hp : χ p = 0
      · simp only [hp, hq, zero_smul, sub_self, norm_zero]
        exact mul_nonneg (mul_nonneg hC0 L.coe_nonneg) dist_nonneg
      · rw [← norm_neg, neg_sub, dist_comm]
        exact key q p hp
    · exact key p q hq
  · refine HasCompactSupport.intro (isCompact_closedBall z₀ (4 * R₀)) fun p hp => ?_
    have h0 : χ p = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      hp (Metric.ball_subset_closedBall (hsupp h))
    simp only [h0, zero_smul]

/-! ## The buffered exterior source -/

theorem two_mul_omega_ne_top (m : ℕ) : 2 * omega m ≠ ⊤ :=
  ENNReal.mul_ne_top (by simp) (omega_lt_top m).ne

theorem parabolicVolume_ball_eq_ofReal {m : ℕ} (z : Space m) {r : ℝ} (hr : 0 < r) :
    parabolicVolume m (Metric.ball z r) =
      ENNReal.ofReal ((2 * omega m).toReal * r ^ (m + 2)) := by
  rw [parabolicVolume_ball z r hr, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (two_mul_omega_ne_top m), ENNReal.ofReal_pow hr.le]

theorem parabolicVolume_closedBall_eq_ofReal {m : ℕ} (z : Space m) {r : ℝ} (hr : 0 ≤ r) :
    parabolicVolume m (Metric.closedBall z r) =
      ENNReal.ofReal ((2 * omega m).toReal * r ^ (m + 2)) := by
  rw [parabolicVolume_closedBall z r hr, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (two_mul_omega_ne_top m), ENNReal.ofReal_pow hr]

/-- The `dr/r` tail `∫_{(31,∞)} r^{-2} dr/r = 31^{-2}/2 ≤ 1/2`. -/
theorem lintegral_Ioi_inv_sq_scaleMeasure_le :
    ∫⁻ r in Ioi (31 : ℝ), (ENNReal.ofReal r)⁻¹ ^ 2 ∂scaleMeasure ≤ ENNReal.ofReal (1 / 2) := by
  have hg : Measurable fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ 2 := by fun_prop
  rw [scaleMeasure, restrict_withDensity measurableSet_Ioi,
    lintegral_withDensity_eq_lintegral_mul _ measurable_scaleDensity hg,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.2 (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 31))]
  have hpt : EqOn (fun r : ℝ => ((fun r : ℝ => ENNReal.ofReal (1 / r)) *
      fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ 2) r) (fun r : ℝ => ENNReal.ofReal (r ^ (-3 : ℝ)))
      (Ioi 31) := by
    intro r hr
    have hr0 : 0 < r := lt_trans (by norm_num) hr
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_inv_of_pos hr0, ← ENNReal.ofReal_pow (inv_nonneg.2 hr0.le),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.rpow_neg hr0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hI : IntegrableOn (fun r : ℝ => r ^ (-3 : ℝ)) (Ioi 31) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (31 : ℝ))] fun r : ℝ => r ^ (-3 : ℝ) :=
    (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun r hr => (Real.rpow_pos_of_pos (lt_trans (by norm_num) hr) _).le)
  have h1 : (31 : ℝ) ^ (-2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  calc ∫⁻ r in Ioi 31, ((fun r : ℝ => ENNReal.ofReal (1 / r)) *
          fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ 2) r ∂volume
      = ∫⁻ r in Ioi 31, ENNReal.ofReal (r ^ (-3 : ℝ)) ∂volume :=
        setLIntegral_congr_fun measurableSet_Ioi hpt
    _ = ENNReal.ofReal (∫ r in Ioi 31, r ^ (-3 : ℝ)) :=
        (ofReal_integral_eq_lintegral_ofReal hI hnn).symm
    _ ≤ ENNReal.ofReal (1 / 2) := by
        rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num),
          show (-3 : ℝ) + 1 = -2 by norm_num]
        apply ENNReal.ofReal_le_ofReal
        linarith

/-- The Borel support and source domination accompanying `buffered_exterior_source`
(the inputs `σ ≤ dp`, `T` Borel, `F₀ ⊆ T`, `σ Tᶜ = 0` of the source extension
`exists_affine_extension_of_source_proof`, for `σ = dp⌞E*` and `T = E*`). -/
theorem buffered_exterior_source_support {m : ℕ} {E F : Set (Space m)} (hE : MeasurableSet E)
    (hFE : F ⊆ E) :
    MeasurableSet (E ∪ (Metric.ball (point 0 0) 32)ᶜ) ∧
      F ⊆ E ∪ (Metric.ball (point 0 0) 32)ᶜ ∧
      (parabolicVolume m).restrict (E ∪ (Metric.ball (point 0 0) 32)ᶜ) ≤ parabolicVolume m ∧
      (parabolicVolume m).restrict (E ∪ (Metric.ball (point 0 0) 32)ᶜ)
        (E ∪ (Metric.ball (point 0 0) 32)ᶜ)ᶜ = 0 := by
  have hT : MeasurableSet (E ∪ (Metric.ball (point (0 : Spatial m) 0) 32)ᶜ) :=
    hE.union measurableSet_ball.compl
  refine ⟨hT, fun x hx => Or.inl (hFE hx), Measure.restrict_le_self, ?_⟩
  rw [Measure.restrict_apply hT.compl, compl_inter_self, measure_empty]

open Classical in
/-- The buffered exterior source: appending the exterior `P(0,32)ᶜ` (extending the trace
by zero there) to a normalized source `E ⊆ P̄(0,4)` keeps the trace `L`-Lipschitz, gives
lower density `c r^(m+2)` at every scale around points of `F`, and raises the source
energy by at most `C L²`. -/
theorem buffered_exterior_source (m : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      (E F : Set (Space m)) (f : Space m → Y) (L : ℝ≥0) (B₀ ρ : ℝ),
      MeasurableSet E → F ⊆ E → F ⊆ Metric.closedBall (point 0 0) 1 →
      E ⊆ Metric.closedBall (point 0 0) 4 → 0 < ρ → ρ ≤ 1 / 64 → 0 ≤ B₀ →
      LipschitzOnWith L f E → (∀ q ∈ E, ‖f q‖ ≤ 8 * L) →
      (∀ p ∈ F, ∀ r : ℝ, 0 < r → r ≤ 1 →
        parabolicVolume m (Metric.ball p r) ≤ 2 * parabolicVolume m (E ∩ Metric.ball p r)) →
      (∀ p ∈ F, ∫⁻ r in Ioo 0 (2 / ρ), traceErrorSq (parabolicVolume m) E f p r ∂scaleMeasure ≤
        ENNReal.ofReal B₀) →
      LipschitzOnWith L (fun q => if q ∈ E then f q else 0) (E ∪ (Metric.ball (point 0 0) 32)ᶜ) ∧
      (∀ x ∈ F, ∀ r : ℝ, 0 < r → ENNReal.ofReal (c * r ^ (m + 2)) ≤
        (parabolicVolume m).restrict (E ∪ (Metric.ball (point 0 0) 32)ᶜ) (Metric.ball x r)) ∧
      ∀ x ∈ F, ∫⁻ r in Ioi 0,
          affineErrorSq ((parabolicVolume m).restrict (E ∪ (Metric.ball (point 0 0) 32)ᶜ))
            (fun q => if q ∈ E then f q else 0) x r ∂scaleMeasure ≤
        ENNReal.ofReal (B₀ + C * (L : ℝ) ^ 2) := by
  obtain ⟨v, hv_def⟩ : ∃ v : ℝ, v = (2 * omega m).toReal := ⟨_, rfl⟩
  have hv : 0 < v := by
    rw [hv_def]
    exact ENNReal.toReal_pos (mul_ne_zero two_ne_zero (omega_pos m).ne')
      (two_mul_omega_ne_top m)
  have hvol : ∀ (z : Space m) (r : ℝ), 0 < r →
      parabolicVolume m (Metric.ball z r) = ENNReal.ofReal (v * r ^ (m + 2)) := by
    intro z r hr
    rw [hv_def]
    exact parabolicVolume_ball_eq_ofReal z hr
  have h128 : (1 : ℝ) ≤ 128 ^ (m + 2) := one_le_pow₀ (by norm_num)
  have hc_le : v / (2 * 128 ^ (m + 2)) ≤ v / 2 :=
    div_le_div_of_nonneg_left hv.le two_pos (by linarith)
  refine ⟨v / (2 * 128 ^ (m + 2)), 32 * v * 4 ^ (m + 2), div_pos hv (by positivity),
    mul_nonneg (mul_nonneg (by norm_num) hv.le) (by positivity), ?_⟩
  intro Y _ _ E F f L B₀ ρ hE hFE hF1 hE4 hρ hρ1 hB₀ hL hf8 hdens henergy
  set o : Space m := point 0 0 with ho
  set Es := E ∪ (Metric.ball o 32)ᶜ with hEs
  set fs : Space m → Y := fun q => if q ∈ E then f q else 0 with hfs
  have hfs_E : ∀ q ∈ E, fs q = f q := fun q hq => by simp [hfs, hq]
  have hfs_nE : ∀ q ∉ E, fs q = 0 := fun q hq => by simp [hfs, hq]
  have hE_o : ∀ q ∈ E, dist q o ≤ 4 := fun q hq => Metric.mem_closedBall.1 (hE4 hq)
  have hF_o : ∀ x ∈ F, dist x o ≤ 1 := fun x hx => Metric.mem_closedBall.1 (hF1 hx)
  have hfar : ∀ q ∈ Es, q ∉ E → 32 ≤ dist q o := by
    intro q hq hqE
    rcases hq with hq | hq
    · exact absurd hq hqE
    · exact not_lt.1 fun h => hq (Metric.mem_ball.2 h)
  refine ⟨LipschitzOnWith.of_dist_le_mul fun q hq q' hq' => ?_, ?_, ?_⟩
  · -- the gap `28` dominates the amplitude `8L`
    have hgap : ∀ a b : Space m, a ∈ E → b ∈ Es → b ∉ E →
        dist (fs a) (fs b) ≤ L * dist a b := by
      intro a b ha hb hbE
      rw [hfs_E a ha, hfs_nE b hbE, dist_zero_right]
      have h28 : 28 ≤ dist a b := by
        linarith [dist_triangle b a o, dist_comm a b, hE_o a ha, hfar b hb hbE]
      calc ‖f a‖ ≤ 8 * L := hf8 a ha
        _ ≤ L * dist a b := by nlinarith [L.coe_nonneg]
    by_cases h : q ∈ E <;> by_cases h' : q' ∈ E
    · rw [hfs_E q h, hfs_E q' h']
      exact hL.dist_le_mul q h q' h'
    · exact hgap q q' h hq' h'
    · rw [dist_comm, dist_comm q]
      exact hgap q' q h' hq h
    · rw [hfs_nE q h, hfs_nE q' h', dist_self]
      exact mul_nonneg L.coe_nonneg dist_nonneg
  · -- density at every scale
    intro x hx r hr
    rw [Measure.restrict_apply measurableSet_ball]
    have hhalf : ∀ s : ℝ, 0 < s → s ≤ 1 →
        ENNReal.ofReal (v * s ^ (m + 2) / 2) ≤ parabolicVolume m (Metric.ball x s ∩ Es) := by
      intro s hs hs1
      have h := hdens x hx s hs hs1
      rw [hvol x s hs] at h
      calc ENNReal.ofReal (v * s ^ (m + 2) / 2)
          = ENNReal.ofReal (v * s ^ (m + 2)) / 2 := by
            rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
        _ ≤ parabolicVolume m (E ∩ Metric.ball x s) :=
            ENNReal.div_le_of_le_mul (h.trans_eq (mul_comm _ _))
        _ ≤ parabolicVolume m (Metric.ball x s ∩ Es) :=
            measure_mono fun q hq => ⟨hq.2, Or.inl hq.1⟩
    rcases le_or_gt r 1 with hr1 | hr1
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hhalf r hr hr1)
      calc v / (2 * 128 ^ (m + 2)) * r ^ (m + 2) ≤ v / 2 * r ^ (m + 2) :=
            mul_le_mul_of_nonneg_right hc_le (by positivity)
        _ = v * r ^ (m + 2) / 2 := by ring
    rcases lt_or_ge r 128 with hr128 | hr128
    · have h1 := hhalf 1 one_pos le_rfl
      rw [one_pow, mul_one] at h1
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (h1.trans
        (measure_mono fun q hq => ⟨Metric.ball_subset_ball hr1.le hq.1, hq.2⟩))
      calc v / (2 * 128 ^ (m + 2)) * r ^ (m + 2)
          ≤ v / (2 * 128 ^ (m + 2)) * 128 ^ (m + 2) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hr128.le _)
              (div_nonneg hv.le (by positivity))
        _ = v / 2 := by field_simp
    · -- subtract the missing radius-`32` ball
      have h4 : 4 * 32 ^ (m + 2) ≤ r ^ (m + 2) := by
        have ha : (128 : ℝ) ^ (m + 2) ≤ r ^ (m + 2) := pow_le_pow_left₀ (by norm_num) hr128 _
        have hb : (128 : ℝ) ^ (m + 2) = 4 ^ (m + 2) * 32 ^ (m + 2) := by
          rw [← mul_pow]; norm_num
        have hc : (4 : ℝ) ≤ 4 ^ (m + 2) := le_self_pow₀ (by norm_num) (by omega)
        have hd : (4 : ℝ) * 32 ^ (m + 2) ≤ 4 ^ (m + 2) * 32 ^ (m + 2) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        linarith
      have hineq : v / (2 * 128 ^ (m + 2)) * r ^ (m + 2) ≤
          v * r ^ (m + 2) - v * 32 ^ (m + 2) := by
        have e1 := mul_le_mul_of_nonneg_right hc_le (by positivity : (0 : ℝ) ≤ r ^ (m + 2))
        have e2 := mul_le_mul_of_nonneg_left h4 hv.le
        have e3 : 0 ≤ v * r ^ (m + 2) := mul_nonneg hv.le (by positivity)
        nlinarith
      calc ENNReal.ofReal (v / (2 * 128 ^ (m + 2)) * r ^ (m + 2))
          ≤ ENNReal.ofReal (v * r ^ (m + 2) - v * 32 ^ (m + 2)) :=
            ENNReal.ofReal_le_ofReal hineq
        _ = ENNReal.ofReal (v * r ^ (m + 2)) - ENNReal.ofReal (v * 32 ^ (m + 2)) :=
            ENNReal.ofReal_sub _ (mul_nonneg hv.le (by positivity))
        _ = parabolicVolume m (Metric.ball x r) - parabolicVolume m (Metric.ball o 32) := by
            rw [hvol x r hr, hvol o 32 (by norm_num)]
        _ ≤ parabolicVolume m (Metric.ball x r \ Metric.ball o 32) := le_measure_sdiff
        _ ≤ parabolicVolume m (Metric.ball x r ∩ Es) :=
            measure_mono fun q hq => ⟨hq.1, Or.inr hq.2⟩
  · -- the source energy
    intro x hx
    have hxo := hF_o x hx
    -- scales `r ≤ 31`: the exterior piece is absent and `f* = f`
    have hlow : ∀ r ∈ Ioc (0 : ℝ) 31,
        affineErrorSq ((parabolicVolume m).restrict Es) fs x r =
          traceErrorSq (parabolicVolume m) E f x r := by
      intro r hr
      have hball : Metric.ball x r ∩ Es = Metric.ball x r ∩ E := by
        ext q
        constructor
        · rintro ⟨hq1, hq2 | hq2⟩
          · exact ⟨hq1, hq2⟩
          · exfalso
            apply hq2
            rw [Metric.mem_ball] at hq1 ⊢
            linarith [dist_triangle q x o, hr.2]
        · rintro ⟨hq1, hq2⟩
          exact ⟨hq1, Or.inl hq2⟩
      rw [traceErrorSq, affineErrorSq_of_pos _ _ _ hr.1, affineErrorSq_of_pos _ _ _ hr.1]
      congr 1
      refine iInf_congr fun a => iInf_congr fun B => ?_
      simp only [affineFitIntegral]
      rw [Measure.restrict_restrict measurableSet_ball,
        Measure.restrict_restrict measurableSet_ball, hball]
      exact setLIntegral_congr_fun (measurableSet_ball.inter hE) fun q hq => by
        simp only [hfs_E q hq.2]
    have hlowint : ∫⁻ r in Ioc 0 31, affineErrorSq ((parabolicVolume m).restrict Es) fs x r
        ∂scaleMeasure ≤ ENNReal.ofReal B₀ := by
      have h31 : (31 : ℝ) < 2 / ρ := by
        rw [lt_div_iff₀ hρ]
        linarith
      rw [setLIntegral_congr_fun measurableSet_Ioc hlow]
      exact le_trans (lintegral_mono_set (show Ioc (0 : ℝ) 31 ⊆ Ioo 0 (2 / ρ) from
        fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 h31⟩)) (henergy x hx)
    -- scales `r > 31`: the zero comparison
    have hpt : ∀ q, ‖fs q - (0 + (0 : Spatial m →L[ℝ] Y) q.1)‖ₑ ^ 2 ≤
        E.indicator (fun _ => ENNReal.ofReal (8 * L) ^ 2) q := by
      intro q
      by_cases hq : q ∈ E
      · rw [hfs_E q hq, Set.indicator_of_mem hq]
        rw [show (0 : Spatial m →L[ℝ] Y) q.1 = 0 from rfl, add_zero, sub_zero]
        refine pow_le_pow_left₀ zero_le ?_ 2
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hf8 q hq)
      · rw [hfs_nE q hq, Set.indicator_of_notMem hq]
        simp
    have hMt : ENNReal.ofReal (8 * L) ^ 2 * parabolicVolume m (Metric.closedBall o 4) =
        ENNReal.ofReal (64 * (L : ℝ) ^ 2 * (v * 4 ^ (m + 2))) := by
      rw [hv_def, parabolicVolume_closedBall_eq_ofReal o (by norm_num : (0 : ℝ) ≤ 4),
        ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    have hfitInt : ∀ r, affineFitIntegral ((parabolicVolume m).restrict Es) fs 0 0 x r ≤
        ENNReal.ofReal (64 * (L : ℝ) ^ 2 * (v * 4 ^ (m + 2))) := by
      intro r
      calc affineFitIntegral ((parabolicVolume m).restrict Es) fs 0 0 x r
          ≤ ∫⁻ q, ‖fs q - (0 + (0 : Spatial m →L[ℝ] Y) q.1)‖ₑ ^ 2
              ∂(parabolicVolume m).restrict Es := setLIntegral_le_lintegral _ _
        _ ≤ ∫⁻ q, E.indicator (fun _ => ENNReal.ofReal (8 * L) ^ 2) q ∂parabolicVolume m :=
            lintegral_mono' Measure.restrict_le_self fun q => hpt q
        _ = ENNReal.ofReal (8 * L) ^ 2 * parabolicVolume m E := lintegral_indicator_const hE _
        _ ≤ ENNReal.ofReal (8 * L) ^ 2 * parabolicVolume m (Metric.closedBall o 4) :=
            mul_le_mul_right (measure_mono hE4) _
        _ = _ := hMt
    have hfit : ∀ r ∈ Ioi (31 : ℝ), affineErrorSq ((parabolicVolume m).restrict Es) fs x r ≤
        (ENNReal.ofReal r)⁻¹ ^ 2 * ENNReal.ofReal (64 * (L : ℝ) ^ 2 * (v * 4 ^ (m + 2))) := by
      intro r hr
      have hr0 : 0 < r := lt_trans (by norm_num) hr
      refine (affineErrorSq_le_fitIntegral _ _ _ hr0 0 0).trans (mul_le_mul' ?_ (hfitInt r))
      exact pow_le_pow_of_le_one zero_le
        (ENNReal.inv_le_one.2 (ENNReal.one_le_ofReal.2 (by linarith [mem_Ioi.1 hr])))
        (Nat.le_add_left 2 _)
    have hg : Measurable fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ 2 := by fun_prop
    have htail : ∫⁻ r in Ioi 31, affineErrorSq ((parabolicVolume m).restrict Es) fs x r
        ∂scaleMeasure ≤ ENNReal.ofReal (32 * v * 4 ^ (m + 2) * (L : ℝ) ^ 2) := by
      calc ∫⁻ r in Ioi 31, affineErrorSq ((parabolicVolume m).restrict Es) fs x r ∂scaleMeasure
          ≤ ∫⁻ r in Ioi 31, (ENNReal.ofReal r)⁻¹ ^ 2 *
              ENNReal.ofReal (64 * (L : ℝ) ^ 2 * (v * 4 ^ (m + 2))) ∂scaleMeasure :=
            setLIntegral_mono' measurableSet_Ioi hfit
        _ = (∫⁻ r in Ioi 31, (ENNReal.ofReal r)⁻¹ ^ 2 ∂scaleMeasure) *
              ENNReal.ofReal (64 * (L : ℝ) ^ 2 * (v * 4 ^ (m + 2))) :=
            lintegral_mul_const _ hg
        _ ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal (64 * (L : ℝ) ^ 2 * (v * 4 ^ (m + 2))) :=
            mul_le_mul_left lintegral_Ioi_inv_sq_scaleMeasure_le _
        _ = ENNReal.ofReal (32 * v * 4 ^ (m + 2) * (L : ℝ) ^ 2) := by
            rw [← ENNReal.ofReal_mul (by norm_num)]
            congr 1
            ring
    calc ∫⁻ r in Ioi 0, affineErrorSq ((parabolicVolume m).restrict Es) fs x r ∂scaleMeasure
        ≤ ∫⁻ r in Ioc 0 31 ∪ Ioi 31,
            affineErrorSq ((parabolicVolume m).restrict Es) fs x r ∂scaleMeasure := by
          refine lintegral_mono_set fun r hr => ?_
          rcases le_or_gt r 31 with h | h
          · exact Or.inl ⟨hr, h⟩
          · exact Or.inr h
      _ ≤ ∫⁻ r in Ioc 0 31, affineErrorSq ((parabolicVolume m).restrict Es) fs x r
            ∂scaleMeasure +
          ∫⁻ r in Ioi 31, affineErrorSq ((parabolicVolume m).restrict Es) fs x r
            ∂scaleMeasure := lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal B₀ + ENNReal.ofReal (32 * v * 4 ^ (m + 2) * (L : ℝ) ^ 2) :=
          add_le_add hlowint htail
      _ = ENNReal.ofReal (B₀ + 32 * v * 4 ^ (m + 2) * (L : ℝ) ^ 2) :=
          (ENNReal.ofReal_add hB₀ (by positivity)).symm

end TraceExtension

end ParabolicRectifiability
