import ParabolicRectifiability.Analysis.TraceExtension.SourceAllocation

/-! # Source estimates for the regular trace extension

Four auxiliary estimates for the trace extension: the slab bound for a source measure
(`reservoir_slab_bound_proof`), the least-squares source fit with bounded slope
(`exists_source_fit_slope_le_proof`), the moment coefficients
(`exists_moment_coefficients_proof`) and the continuous domination of the volume by the
source (`volume_restrict_le_of_source_density_proof`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-! ## The slab bound -/

/-- Volume of a spatial ball. -/
theorem volume_spatial_ball_eq {m : ℕ} (x : Spatial m) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Spatial m)) (Metric.ball x r) = ENNReal.ofReal r ^ m * omega m := by
  rw [Measure.addHaar_ball_of_pos (volume : Measure (Spatial m)) x hr, finrank_euclideanSpace_fin,
    ENNReal.ofReal_pow hr.le]
  rfl

/-- Packing bound for a spatial slab of half-width `R/(2N)` in a ball of radius `R`: `N`
disjoint translates in the direction `e` fit in the ball of radius `2R`. -/
theorem volume_spatial_slab_mul_le {m : ℕ} (x e : Spatial m) (he : ‖e‖ = 1) (β : ℝ)
    {R : ℝ} (hR : 0 < R) (N : ℕ) (hN : 0 < N) :
    (N : ℝ≥0∞) * (volume : Measure (Spatial m))
        (Metric.ball x R ∩ {u | |inner ℝ e u - β| < R / N / 2}) ≤
      ENNReal.ofReal (2 * R) ^ m * omega m := by
  classical
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set q : ℝ := R / N with hq
  have hq0 : 0 < q := div_pos hR hNr
  set S₀ : Set (Spatial m) := Metric.ball x R ∩ {u | |inner ℝ e u - β| < q / 2} with hS₀
  have hS₀m : MeasurableSet S₀ :=
    measurableSet_ball.inter (measurableSet_lt
      (((continuous_const.inner continuous_id).sub continuous_const).abs.measurable)
      measurable_const)
  let T : ℕ → Set (Spatial m) := fun j => (fun u => -(((j : ℝ) * q) • e) + u) ⁻¹' S₀
  have hTm : ∀ j, MeasurableSet (T j) := fun j => (measurable_const_add _) hS₀m
  have hTvol : ∀ j, (volume : Measure (Spatial m)) (T j) = volume S₀ := fun j =>
    measure_preimage_add _ _ _
  have hin : ∀ (j : ℕ) (u : Spatial m),
      inner ℝ e (-(((j : ℝ) * q) • e) + u) = inner ℝ e u - (j : ℝ) * q := by
    intro j u
    rw [inner_add_right, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
    ring
  have hTsub : ∀ j ∈ Finset.range N, T j ⊆ Metric.ball x (2 * R) := by
    intro j hj u hu
    have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hj
    simp only [T, hS₀, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Metric.mem_ball, dist_eq_norm] at hu
    have hu1 : ‖-(((j : ℝ) * q) • e) + u - x‖ < R := hu.1
    have hv : ‖((j : ℝ) * q) • e‖ ≤ R := by
      rw [norm_smul, he, mul_one, Real.norm_of_nonneg (by positivity)]
      calc (j : ℝ) * q ≤ (N : ℝ) * q := by
            exact mul_le_mul_of_nonneg_right (by linarith) hq0.le
        _ = R := by
            have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
            rw [hq]; field_simp
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖u - x‖ = ‖(-(((j : ℝ) * q) • e) + u - x) + ((j : ℝ) * q) • e‖ := by
          congr 1; abel
      _ ≤ ‖-(((j : ℝ) * q) • e) + u - x‖ + ‖((j : ℝ) * q) • e‖ := norm_add_le _ _
      _ < R + R := by linarith
      _ = 2 * R := by ring
  have hTdisj : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint T := by
    intro j _ k _ hjk
    refine Set.disjoint_left.2 fun u hu hu' => hjk ?_
    simp only [T, hS₀, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, hin] at hu hu'
    have h1 := hu.2
    have h2 := hu'.2
    rw [abs_lt] at h1 h2
    have hlt : ((j : ℝ) - k) * q < 1 * q := by linarith [h1.1, h1.2, h2.1, h2.2]
    have hgt : ((k : ℝ) - j) * q < 1 * q := by linarith [h1.1, h1.2, h2.1, h2.2]
    have hlt' := lt_of_mul_lt_mul_right hlt hq0.le
    have hgt' := lt_of_mul_lt_mul_right hgt hq0.le
    rcases lt_trichotomy j k with h | h | h
    · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
      linarith
    · exact h
    · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith
  calc (N : ℝ≥0∞) * volume S₀ = ∑ j ∈ Finset.range N, volume (T j) := by
        rw [Finset.sum_congr rfl (fun j _ => hTvol j), Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
    _ = volume (⋃ j ∈ Finset.range N, T j) :=
        (measure_biUnion_finset hTdisj fun j _ => hTm j).symm
    _ ≤ volume (Metric.ball x (2 * R)) := measure_mono (Set.iUnion₂_subset hTsub)
    _ = ENNReal.ofReal (2 * R) ^ m * omega m := volume_spatial_ball_eq x (by positivity)

/-- The parabolic slab `P(x,R) ∩ {|e·u - β| < R/(2N)}` has volume at most
`(2R)^m ω_m · 2R² / N`. -/
theorem parabolicVolume_slab_mul_le {m : ℕ} (x : Space m) (e : Spatial m) (he : ‖e‖ = 1)
    (β : ℝ) {R : ℝ} (hR : 0 < R) (N : ℕ) (hN : 0 < N) :
    (N : ℝ≥0∞) * parabolicVolume m
        (Metric.ball x R ∩ {z : Space m | |inner ℝ e z.1 - β| < R / N / 2}) ≤
      ENNReal.ofReal (2 * R) ^ m * omega m * ENNReal.ofReal (2 * R ^ 2) := by
  have hsub : (coordinatesMeasurableEquiv m).symm ⁻¹'
      (Metric.ball x R ∩ {z : Space m | |inner ℝ e z.1 - β| < R / N / 2}) ⊆
      (Metric.ball x.1 R ∩ {u : Spatial m | |inner ℝ e u - β| < R / N / 2}) ×ˢ
        Ioo (x.2.val - R ^ 2) (x.2.val + R ^ 2) := by
    rw [Set.preimage_inter, coordinates_symm_preimage_ball x R hR]
    rintro ⟨u, s⟩ ⟨⟨hu, hs⟩, hslab⟩
    exact ⟨⟨hu, hslab⟩, hs⟩
  rw [parabolicVolume_apply]
  calc (N : ℝ≥0∞) * coordinateVolume m ((coordinatesMeasurableEquiv m).symm ⁻¹'
        (Metric.ball x R ∩ {z : Space m | |inner ℝ e z.1 - β| < R / N / 2}))
      ≤ (N : ℝ≥0∞) * coordinateVolume m
          ((Metric.ball x.1 R ∩ {u : Spatial m | |inner ℝ e u - β| < R / N / 2}) ×ˢ
            Ioo (x.2.val - R ^ 2) (x.2.val + R ^ 2)) :=
        mul_le_mul_right (measure_mono hsub) _
    _ = ((N : ℝ≥0∞) * (volume : Measure (Spatial m))
          (Metric.ball x.1 R ∩ {u : Spatial m | |inner ℝ e u - β| < R / N / 2})) *
          (volume : Measure ℝ) (Ioo (x.2.val - R ^ 2) (x.2.val + R ^ 2)) := by
        rw [coordinateVolume, Measure.prod_prod, mul_assoc]
    _ ≤ (ENNReal.ofReal (2 * R) ^ m * omega m) * ENNReal.ofReal (2 * R ^ 2) :=
        mul_le_mul' (volume_spatial_slab_mul_le x.1 e he β hR N hN)
          (le_of_eq (by
            rw [Real.volume_Ioo, show x.2.val + R ^ 2 - (x.2.val - R ^ 2) = 2 * R ^ 2 by ring]))

/-- **Slab bound.** With
`N = ⌈2^(m+2) ω_m / c⌉ + 1`, the slab `|e·u - β| < R/(2N)` carries source mass at most
`(c/2) R^(m+2)`, so at least `(c/2) R^(m+2)` of the mass of `P(x,R)` sees the integrand
`≥ R²/(4N²)`; hence `c₃ = c/(8N²)`. At `m = 0` there is no unit vector. -/
theorem reservoir_slab_bound_proof (m : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∀ (x : Space m) (R : ℝ) (σ : Measure (Space m)),
      0 < R → σ ≤ parabolicVolume m →
      ENNReal.ofReal (c * R ^ (m + 2)) ≤ σ (Metric.ball x R) →
      ∀ e : Spatial m, ‖e‖ = 1 → ∀ β : ℝ,
        ENNReal.ofReal (c₃ * R ^ (m + 4)) ≤
          ∫⁻ z in Metric.ball x R, ENNReal.ofReal ((inner ℝ e z.1 - β) ^ 2) ∂σ := by
  set ω : ℝ := (omega m).toReal with hω
  have hωeq : omega m = ENNReal.ofReal ω := (ENNReal.ofReal_toReal (omega_lt_top m).ne).symm
  have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
  set N : ℕ := ⌈2 ^ (m + 2) * ω / c⌉₊ + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos _
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hNbig : 2 ^ (m + 2) * ω / c ≤ N := by
    rw [hNdef]; push_cast; linarith [Nat.le_ceil (2 ^ (m + 2) * ω / c)]
  refine ⟨c / (8 * (N : ℝ) ^ 2), by positivity, ?_⟩
  intro x R σ hR hσ hmass e he β
  set P : Set (Space m) := Metric.ball x R with hP
  set Sl : Set (Space m) := Metric.ball x R ∩ {z : Space m | |inner ℝ e z.1 - β| < R / N / 2}
    with hSl
  have hSlm : MeasurableSet Sl :=
    measurableSet_ball.inter (measurableSet_lt
      (((continuous_const.inner continuous_fst).sub continuous_const).abs.measurable)
      measurable_const)
  -- The slab carries at most half of the guaranteed mass.
  have hslab : σ Sl ≤ ENNReal.ofReal (c / 2 * R ^ (m + 2)) := by
    have h1 := parabolicVolume_slab_mul_le x e he β hR N hN
    have h3 : ENNReal.ofReal (2 * R) ^ m * omega m * ENNReal.ofReal (2 * R ^ 2) =
        ENNReal.ofReal (2 ^ (m + 1) * ω * R ^ (m + 2)) := by
      rw [hωeq, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [h3] at h1
    have h4 : parabolicVolume m Sl ≤ ENNReal.ofReal (2 ^ (m + 1) * ω * R ^ (m + 2) / N) := by
      rw [ENNReal.ofReal_div_of_pos hNr, ENNReal.ofReal_natCast,
        ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.2 hN.ne'))
          (Or.inl (ENNReal.natCast_ne_top N)), mul_comm]
      exact h1
    refine (Measure.le_iff'.1 hσ Sl).trans (h4.trans (ENNReal.ofReal_le_ofReal ?_))
    rw [div_le_iff₀ hNr]
    have h5 : 2 ^ (m + 2) * ω ≤ c * N := by
      rw [div_le_iff₀ hc] at hNbig; linarith
    have h6 : 2 ^ (m + 1) * ω ≤ c / 2 * N := by
      have : (2 : ℝ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
      rw [this] at h5
      linarith
    have hRp : 0 < R ^ (m + 2) := by positivity
    calc 2 ^ (m + 1) * ω * R ^ (m + 2) ≤ (c / 2 * N) * R ^ (m + 2) :=
          mul_le_mul_of_nonneg_right h6 hRp.le
      _ = c / 2 * R ^ (m + 2) * N := by ring
  -- Off the slab, the integrand is at least `(R/(2N))²`.
  have hlow : ∀ z ∈ P, (Slᶜ).indicator (fun _ => ENNReal.ofReal ((R / N / 2) ^ 2)) z ≤
      ENNReal.ofReal ((inner ℝ e z.1 - β) ^ 2) := by
    intro z hz
    by_cases hzs : z ∈ Sl
    · rw [Set.indicator_of_notMem (show z ∉ Slᶜ from fun h => h hzs)]
      exact zero_le
    · rw [Set.indicator_of_mem (Set.mem_compl hzs)]
      apply ENNReal.ofReal_le_ofReal
      have hge : R / N / 2 ≤ |inner ℝ e z.1 - β| := by
        by_contra h
        exact hzs ⟨hz, not_le.1 h⟩
      have h0 : 0 ≤ R / N / 2 := by positivity
      calc (R / N / 2) ^ 2 ≤ |inner ℝ e z.1 - β| ^ 2 := pow_le_pow_left₀ h0 hge 2
        _ = (inner ℝ e z.1 - β) ^ 2 := sq_abs _
  calc ENNReal.ofReal (c / (8 * (N : ℝ) ^ 2) * R ^ (m + 4))
      = ENNReal.ofReal ((R / N / 2) ^ 2) * ENNReal.ofReal (c / 2 * R ^ (m + 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
        field_simp
        ring
    _ ≤ ENNReal.ofReal ((R / N / 2) ^ 2) * σ (P \ Sl) := by
        refine mul_le_mul_right ?_ _
        calc ENNReal.ofReal (c / 2 * R ^ (m + 2))
            = ENNReal.ofReal (c * R ^ (m + 2)) - ENNReal.ofReal (c / 2 * R ^ (m + 2)) := by
              rw [← ENNReal.ofReal_sub _ (by positivity)]
              congr 1
              ring
          _ ≤ σ P - σ Sl := tsub_le_tsub hmass hslab
          _ ≤ σ (P \ Sl) := le_measure_sdiff
    _ = ∫⁻ z in P, (Slᶜ).indicator (fun _ => ENNReal.ofReal ((R / N / 2) ^ 2)) z ∂σ := by
        rw [lintegral_indicator_const hSlm.compl, Measure.restrict_apply hSlm.compl,
          Set.sdiff_eq, Set.inter_comm]
    _ ≤ ∫⁻ z in P, ENNReal.ofReal ((inner ℝ e z.1 - β) ^ 2) ∂σ :=
        setLIntegral_mono' measurableSet_ball hlow

/-! ## Least-squares source fit with bounded slope -/

/-- In `L²`, `ofReal ‖h‖²` is the integral of `‖g‖ₑ²` for every representative `g` of `h`. -/
theorem ofReal_norm_sq_eq_lintegral {α Y : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup Y] (h : Lp Y 2 μ) {g : α → Y} (hg : h =ᵐ[μ] g) :
    ENNReal.ofReal (‖h‖ ^ 2) = ∫⁻ q, ‖g q‖ₑ ^ 2 ∂μ := by
  have hgm : AEStronglyMeasurable g μ := (Lp.aestronglyMeasurable h).congr hg
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top h), eLpNorm_congr_ae hg]
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := 2) two_ne_zero hgm
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h2
  exact h2

/-- An operator bound from the unit vectors. -/
theorem opNorm_le_of_forall_unit {m : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (B : Spatial m →L[ℝ] Y) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ e : Spatial m, ‖e‖ = 1 → ‖B e‖ ≤ M) : ‖B‖ ≤ M := by
  refine B.opNorm_le_bound hM fun u => ?_
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
  have he : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hu'.le), inv_mul_cancel₀ hu'.ne']
  have h1 := h _ he
  rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hu'.le), inv_mul_le_iff₀ hu'] at h1
  calc ‖B u‖ ≤ ‖u‖ * M := h1
    _ = M * ‖u‖ := mul_comm _ _

/-- From the slab bound to affine maps with values in an inner-product space: for a unit
`e`, take `w = B e / ‖B e‖` and the Riesz vector `g` of `u ↦ ⟪w, B u⟫`; then
`‖a + B u‖² ≥ ⟪w, a + B u⟫² = ‖g‖² (⟪g/‖g‖, u⟫ - β)²` and `‖g‖ ≥ ‖B e‖`. -/
theorem ofReal_mul_norm_apply_sq_le_lintegral {m : ℕ} {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] (ν : Measure (Space m)) {K : ℝ} (hK : 0 ≤ K)
    (hslab : ∀ e : Spatial m, ‖e‖ = 1 → ∀ β : ℝ,
      ENNReal.ofReal K ≤ ∫⁻ z, ENNReal.ofReal ((inner ℝ e z.1 - β) ^ 2) ∂ν)
    (a : Y) (B : Spatial m →L[ℝ] Y) (e : Spatial m) (he : ‖e‖ = 1) :
    ENNReal.ofReal (K * ‖B e‖ ^ 2) ≤ ∫⁻ z, ‖a + B z.1‖ₑ ^ 2 ∂ν := by
  by_cases hBe : B e = 0
  · rw [hBe, norm_zero]
    simp
  have hBe' : 0 < ‖B e‖ := norm_pos_iff.2 hBe
  set w : Y := ‖B e‖⁻¹ • B e with hw
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hBe'.le), inv_mul_cancel₀ hBe'.ne']
  set ℓ : Spatial m →L[ℝ] ℝ := (innerSL ℝ w).comp B with hℓ
  set g : Spatial m := (InnerProductSpace.toDual ℝ (Spatial m)).symm ℓ with hg
  have hgu : ∀ u, inner ℝ g u = inner ℝ w (B u) := fun u => by
    rw [hg, InnerProductSpace.toDual_symm_apply, hℓ, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply]
  have hgn : ‖B e‖ ≤ ‖g‖ := by
    have h1 : ℓ e = ‖B e‖ := by
      rw [hℓ, ContinuousLinearMap.comp_apply, innerSL_apply_apply, hw, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      field_simp
    have h2 : ‖ℓ e‖ ≤ ‖ℓ‖ * ‖e‖ := ℓ.le_opNorm e
    rw [he, mul_one, h1, Real.norm_of_nonneg hBe'.le] at h2
    rw [hg, LinearIsometryEquiv.norm_map]
    exact h2
  have hg0 : 0 < ‖g‖ := lt_of_lt_of_le hBe' hgn
  set ĝ : Spatial m := ‖g‖⁻¹ • g with hĝ
  have hĝn : ‖ĝ‖ = 1 := by
    rw [hĝ, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hg0.le), inv_mul_cancel₀ hg0.ne']
  set β : ℝ := -inner ℝ w a / ‖g‖ with hβ
  have hpt : ∀ z : Space m,
      ENNReal.ofReal (‖g‖ ^ 2 * (inner ℝ ĝ z.1 - β) ^ 2) ≤ ‖a + B z.1‖ₑ ^ 2 := by
    intro z
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hid : ‖g‖ ^ 2 * (inner ℝ ĝ z.1 - β) ^ 2 = (inner ℝ w (a + B z.1)) ^ 2 := by
      rw [inner_add_right, ← hgu, hĝ, real_inner_smul_left, hβ]
      field_simp
      ring
    rw [hid]
    have h1 := abs_real_inner_le_norm w (a + B z.1)
    rw [hwn, one_mul] at h1
    calc inner ℝ w (a + B z.1) ^ 2 = |inner ℝ w (a + B z.1)| ^ 2 := (sq_abs _).symm
      _ ≤ ‖a + B z.1‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc ENNReal.ofReal (K * ‖B e‖ ^ 2) ≤ ENNReal.ofReal (‖g‖ ^ 2) * ENNReal.ofReal K := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hBe'.le hgn 2) hK
    _ ≤ ENNReal.ofReal (‖g‖ ^ 2) * ∫⁻ z, ENNReal.ofReal ((inner ℝ ĝ z.1 - β) ^ 2) ∂ν :=
        mul_le_mul_right (hslab ĝ hĝn β) _
    _ = ∫⁻ z, ENNReal.ofReal (‖g‖ ^ 2) * ENNReal.ofReal ((inner ℝ ĝ z.1 - β) ^ 2) ∂ν :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ z, ENNReal.ofReal (‖g‖ ^ 2 * (inner ℝ ĝ z.1 - β) ^ 2) ∂ν := by
        congr 1
        funext z
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ∫⁻ z, ‖a + B z.1‖ₑ ^ 2 ∂ν := lintegral_mono hpt

/-- **Bounded slope of the source fit.** The fit integral is
`‖F - Λ(a,B)‖²` in `L²(σ⌞P(x,R); Y)` for a Lipschitz extension `F` of `f` and the
linear map `Λ(a,B) = a + B u`; the orthogonal projection onto the finite-dimensional
range of `Λ` gives the minimizer, Pythagoras gives minimality and uniqueness (`Λ` is
injective by the slab bound and `σ(P(x,R)) > 0`), and comparison with the constant fit
`f(z₀)`, `z₀ ∈ T ∩ P(x,R)`, gives `c₃ R^(m+4) ‖B₀ e‖² ≤ 32 ω_m L² R^(m+4)`, so
`‖B₀‖ ≤ (32 ω_m / c₃)^(1/2) L` with `c₃` from `reservoir_slab_bound_proof`. -/
theorem exists_source_fit_slope_le_proof (m : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Space m) (R : ℝ) (σ : Measure (Space m)),
      0 < R → σ ≤ parabolicVolume m →
      ENNReal.ofReal (c * R ^ (m + 2)) ≤ σ (Metric.ball x R) →
      ∀ {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
        (f : Space m → Y) (L : ℝ≥0) (T : Set (Space m)),
        σ (Metric.ball x R \ T) = 0 → LipschitzOnWith L f T →
        ∃ (a₀ : Y) (B₀ : Spatial m →L[ℝ] Y), ‖B₀‖ ≤ C * L ∧
          (∀ (a' : Y) (B' : Spatial m →L[ℝ] Y),
            affineFitIntegral σ f a₀ B₀ x R ≤ affineFitIntegral σ f a' B' x R) ∧
          (0 < m → ∀ (a' : Y) (B' : Spatial m →L[ℝ] Y),
            affineFitIntegral σ f a' B' x R = affineFitIntegral σ f a₀ B₀ x R →
              a' = a₀ ∧ B' = B₀) := by
  obtain ⟨c₃, hc₃, hslab⟩ := reservoir_slab_bound_proof m c hc
  set ω : ℝ := (omega m).toReal with hω
  have hωeq : omega m = ENNReal.ofReal ω := (ENNReal.ofReal_toReal (omega_lt_top m).ne).symm
  have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
  refine ⟨Real.sqrt (32 * ω / c₃), Real.sqrt_nonneg _, ?_⟩
  intro x R σ hR hσ hmass Y _ _ _ f L T hT hfL
  have hPfin : σ (Metric.ball x R) < ∞ :=
    (Measure.le_iff'.1 hσ _).trans_lt (measure_ball_lt_top (parabolicVolume m) x R)
  have : IsFiniteMeasure (σ.restrict (Metric.ball x R)) := isFiniteMeasure_restrict.2 hPfin.ne
  have hPpos : 0 < σ (Metric.ball x R) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) hmass
  have hPae : ∀ᵐ q ∂σ.restrict (Metric.ball x R), q ∈ Metric.ball x R :=
    ae_restrict_mem measurableSet_ball
  have hTae : ∀ᵐ q ∂σ.restrict (Metric.ball x R), q ∈ T := by
    rw [ae_iff, Measure.restrict_apply' measurableSet_ball]
    have hset : {q | ¬q ∈ T} ∩ Metric.ball x R = Metric.ball x R \ T := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff]
      tauto
    rw [hset]
    exact hT
  have hK : (0 : ℝ) ≤ c₃ * R ^ (m + 4) := by positivity
  have hslab' : ∀ e : Spatial m, ‖e‖ = 1 → ∀ β : ℝ,
      ENNReal.ofReal (c₃ * R ^ (m + 4)) ≤
        ∫⁻ z, ENNReal.ofReal ((inner ℝ e z.1 - β) ^ 2) ∂σ.restrict (Metric.ball x R) :=
    hslab x R σ hR hσ hmass
  have hq1 : ∀ q ∈ Metric.ball x R, ‖q.1‖ ≤ ‖x.1‖ + R := by
    intro q hq
    have h1 : dist q.1 x.1 ≤ dist q x := by rw [Prod.dist_eq]; exact le_max_left _ _
    have h2 : dist q x < R := hq
    have h3 := norm_sub_norm_le q.1 x.1
    rw [← dist_eq_norm] at h3
    linarith
  -- Lipschitz extension of `f`, equal to `f` almost everywhere.
  obtain ⟨F, hFlip, hFeq⟩ := hfL.extend_finite_dimension
  have hfF : f =ᵐ[σ.restrict (Metric.ball x R)] F := hTae.mono fun q hq => hFeq hq
  have hFb : ∀ q ∈ Metric.ball x R,
      ‖F q‖ ≤ ‖F x‖ + (lipschitzExtensionConstant Y * L : ℝ≥0) * R := by
    intro q hq
    have h1 := hFlip.dist_le_mul q x
    have h2 : dist q x < R := hq
    have h3 := norm_sub_norm_le (F q) (F x)
    rw [← dist_eq_norm] at h3
    have h4 : ((lipschitzExtensionConstant Y * L : ℝ≥0) : ℝ) * dist q x ≤
        (lipschitzExtensionConstant Y * L : ℝ≥0) * R :=
      mul_le_mul_of_nonneg_left h2.le (NNReal.coe_nonneg _)
    linarith
  have hmemF : MemLp F 2 (σ.restrict (Metric.ball x R)) :=
    MemLp.of_bound hFlip.continuous.aestronglyMeasurable
      (‖F x‖ + (lipschitzExtensionConstant Y * L : ℝ≥0) * R) (hPae.mono fun q hq => hFb q hq)
  have hmemA : ∀ p : Y × (Spatial m →L[ℝ] Y),
      MemLp (fun q : Space m => p.1 + p.2 q.1) 2 (σ.restrict (Metric.ball x R)) := by
    intro p
    refine MemLp.of_bound
      ((continuous_const.add (p.2.continuous.comp continuous_fst)).aestronglyMeasurable)
      (‖p.1‖ + ‖p.2‖ * (‖x.1‖ + R)) (hPae.mono fun q hq => ?_)
    calc ‖p.1 + p.2 q.1‖ ≤ ‖p.1‖ + ‖p.2 q.1‖ := norm_add_le _ _
      _ ≤ ‖p.1‖ + ‖p.2‖ * ‖q.1‖ := add_le_add le_rfl (p.2.le_opNorm _)
      _ ≤ ‖p.1‖ + ‖p.2‖ * (‖x.1‖ + R) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (hq1 q hq) (norm_nonneg _))
  -- The affine maps as a linear map into `L²`.
  let Λ : (Y × (Spatial m →L[ℝ] Y)) →ₗ[ℝ] Lp Y 2 (σ.restrict (Metric.ball x R)) :=
    { toFun := fun p => (hmemA p).toLp _
      map_add' := fun p p' => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (ae_of_all _ fun q => ?_)
        simp only [Prod.fst_add, Prod.snd_add, add_apply, Pi.add_apply]
        abel
      map_smul' := fun t p => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (ae_of_all _ fun q => ?_)
        simp only [Prod.smul_fst, Prod.smul_snd, smul_apply, Pi.smul_apply,
          smul_add] }
  have hΛae : ∀ p : Y × (Spatial m →L[ℝ] Y),
      ⇑(Λ p) =ᵐ[σ.restrict (Metric.ball x R)] fun q => p.1 + p.2 q.1 :=
    fun p => MemLp.coeFn_toLp (hmemA p)
  set Fl : Lp Y 2 (σ.restrict (Metric.ball x R)) := hmemF.toLp F with hFl
  have hFlae : ⇑Fl =ᵐ[σ.restrict (Metric.ball x R)] F := MemLp.coeFn_toLp hmemF
  have : CompleteSpace (LinearMap.range Λ) := FiniteDimensional.complete ℝ _
  obtain ⟨⟨a₀, B₀⟩, hp₀⟩ :=
    LinearMap.mem_range.1 ((LinearMap.range Λ).starProjection_apply_mem Fl)
  have hperp : Fl - Λ (a₀, B₀) ∈ (LinearMap.range Λ)ᗮ := by
    rw [hp₀]
    exact (LinearMap.range Λ).sub_starProjection_mem_orthogonal Fl
  have hpyth : ∀ v ∈ LinearMap.range Λ,
      ‖Fl - v‖ ^ 2 = ‖Fl - Λ (a₀, B₀)‖ ^ 2 + ‖Λ (a₀, B₀) - v‖ ^ 2 := by
    intro v hv
    have h0 : inner ℝ (Fl - Λ (a₀, B₀)) (Λ (a₀, B₀) - v) = 0 :=
      Submodule.inner_left_of_mem_orthogonal
        ((LinearMap.range Λ).sub_mem (LinearMap.mem_range_self Λ _) hv) hperp
    have h1 := norm_add_sq_eq_norm_sq_add_norm_sq_real h0
    rw [show Fl - Λ (a₀, B₀) + (Λ (a₀, B₀) - v) = Fl - v by abel] at h1
    rw [sq, sq, sq, h1]
  -- The fit integral as a squared `L²` distance.
  have hΦ : ∀ (a' : Y) (B' : Spatial m →L[ℝ] Y),
      affineFitIntegral σ f a' B' x R = ENNReal.ofReal (‖Fl - Λ (a', B')‖ ^ 2) := by
    intro a' B'
    rw [ofReal_norm_sq_eq_lintegral (Fl - Λ (a', B')) (g := fun q => F q - (a' + B' q.1))]
    · show ∫⁻ q in Metric.ball x R, ‖f q - (a' + B' q.1)‖ₑ ^ 2 ∂σ = _
      exact lintegral_congr_ae (hfF.mono fun q hq => by simp only [hq])
    · filter_upwards [Lp.coeFn_sub Fl (Λ (a', B')), hFlae, hΛae (a', B')] with q h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
  -- The `L²` norm of an affine map.
  have hΛnorm : ∀ p : Y × (Spatial m →L[ℝ] Y),
      ENNReal.ofReal (‖Λ p‖ ^ 2) =
        ∫⁻ q, ‖p.1 + p.2 q.1‖ₑ ^ 2 ∂σ.restrict (Metric.ball x R) :=
    fun p => ofReal_norm_sq_eq_lintegral (Λ p) (hΛae p)
  have hmin : ∀ v ∈ LinearMap.range Λ, ‖Fl - Λ (a₀, B₀)‖ ≤ ‖Fl - v‖ := by
    intro v hv
    have h := hpyth v hv
    have h' : ‖Fl - Λ (a₀, B₀)‖ ^ 2 ≤ ‖Fl - v‖ ^ 2 := by
      rw [h]; nlinarith [sq_nonneg ‖Λ (a₀, B₀) - v‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h'
  have hdpP : parabolicVolume m (Metric.ball x R) = ENNReal.ofReal (2 * ω * R ^ (m + 2)) := by
    rw [parabolicVolume_ball x R hR, hωeq, ← ENNReal.ofReal_pow hR.le,
      ENNReal.ofReal_mul (mul_nonneg (by norm_num) hω0),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  refine ⟨a₀, B₀, ?_, ?_, ?_⟩
  · -- slope bound
    obtain ⟨z₀, hz₀P, hz₀T⟩ : (Metric.ball x R ∩ T).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have hPT : Metric.ball x R \ T = Metric.ball x R := by
        ext q
        constructor
        · exact fun h => h.1
        · intro hq
          refine ⟨hq, fun hqT => ?_⟩
          have hmem : q ∈ Metric.ball x R ∩ T := ⟨hq, hqT⟩
          rw [hne] at hmem
          exact hmem
      rw [hPT] at hT
      exact hPpos.ne' hT
    -- the constant fit `f(z₀)`
    have hconst : ‖Fl - Λ (F z₀, 0)‖ ^ 2 ≤ 8 * ω * L ^ 2 * R ^ (m + 4) := by
      have hbd : ∀ᵐ q ∂σ.restrict (Metric.ball x R),
          ‖f q - (F z₀ + (0 : Spatial m →L[ℝ] Y) q.1)‖ₑ ^ 2 ≤
            ENNReal.ofReal ((2 * L * R) ^ 2) := by
        filter_upwards [hPae, hTae] with q hqP hqT
        rw [zero_apply, add_zero, ← hFeq hz₀T, ← ofReal_norm,
          ← ENNReal.ofReal_pow (norm_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : dist (f q) (f z₀) ≤ L * dist q z₀ := hfL.dist_le_mul q hqT z₀ hz₀T
        have h2 : dist q z₀ < 2 * R := by
          have := dist_triangle_right q z₀ x
          have hq' : dist q x < R := hqP
          have hz' : dist z₀ x < R := hz₀P
          linarith
        have h3 : ‖f q - f z₀‖ ≤ 2 * L * R := by
          rw [← dist_eq_norm]
          calc dist (f q) (f z₀) ≤ L * dist q z₀ := h1
            _ ≤ L * (2 * R) := mul_le_mul_of_nonneg_left h2.le L.coe_nonneg
            _ = 2 * L * R := by ring
        exact pow_le_pow_left₀ (norm_nonneg _) h3 2
      have hle : ENNReal.ofReal (‖Fl - Λ (F z₀, 0)‖ ^ 2) ≤
          ENNReal.ofReal ((2 * L * R) ^ 2 * (2 * ω * R ^ (m + 2))) := by
        rw [← hΦ]
        calc affineFitIntegral σ f (F z₀) 0 x R
            = ∫⁻ q, ‖f q - (F z₀ + (0 : Spatial m →L[ℝ] Y) q.1)‖ₑ ^ 2
                ∂σ.restrict (Metric.ball x R) := rfl
          _ ≤ ∫⁻ _q, ENNReal.ofReal ((2 * L * R) ^ 2) ∂σ.restrict (Metric.ball x R) :=
              lintegral_mono_ae hbd
          _ = ENNReal.ofReal ((2 * L * R) ^ 2) * σ (Metric.ball x R) := by
              rw [lintegral_const, Measure.restrict_apply_univ]
          _ ≤ ENNReal.ofReal ((2 * L * R) ^ 2) * parabolicVolume m (Metric.ball x R) :=
              mul_le_mul_right (Measure.le_iff'.1 hσ _) _
          _ = ENNReal.ofReal ((2 * L * R) ^ 2 * (2 * ω * R ^ (m + 2))) := by
              rw [hdpP, ← ENNReal.ofReal_mul (sq_nonneg _)]
      have h := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num) hω0) (pow_nonneg hR.le _)))).1 hle
      calc ‖Fl - Λ (F z₀, 0)‖ ^ 2 ≤ (2 * L * R) ^ 2 * (2 * ω * R ^ (m + 2)) := h
        _ = 8 * ω * L ^ 2 * R ^ (m + 4) := by ring
    -- the fitted affine map is close to the constant fit
    have hdiff : ‖Λ (a₀ - F z₀, B₀)‖ ^ 2 ≤ 32 * ω * L ^ 2 * R ^ (m + 4) := by
      have hsub : Λ (a₀ - F z₀, B₀) = Λ (a₀, B₀) - Λ (F z₀, 0) := by
        rw [← map_sub, Prod.mk_sub_mk, sub_zero]
      have h1 : ‖Λ (a₀, B₀) - Λ (F z₀, 0)‖ ≤ 2 * ‖Fl - Λ (F z₀, 0)‖ := by
        have h2 := hmin (Λ (F z₀, 0)) (LinearMap.mem_range_self Λ _)
        calc ‖Λ (a₀, B₀) - Λ (F z₀, 0)‖ = ‖(Fl - Λ (F z₀, 0)) - (Fl - Λ (a₀, B₀))‖ := by
              congr 1; abel
          _ ≤ ‖Fl - Λ (F z₀, 0)‖ + ‖Fl - Λ (a₀, B₀)‖ := norm_sub_le _ _
          _ ≤ 2 * ‖Fl - Λ (F z₀, 0)‖ := by linarith
      rw [hsub]
      have h3 : ‖Λ (a₀, B₀) - Λ (F z₀, 0)‖ ^ 2 ≤ (2 * ‖Fl - Λ (F z₀, 0)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [hconst]
    -- lower bound by the slab estimate, direction by direction
    have hdir : ∀ e : Spatial m, ‖e‖ = 1 → ‖B₀ e‖ ≤ Real.sqrt (32 * ω / c₃) * L := by
      intro e he
      have hQ := ofReal_mul_norm_apply_sq_le_lintegral (σ.restrict (Metric.ball x R)) hK
        hslab' (a₀ - F z₀) B₀ e he
      rw [← hΛnorm (a₀ - F z₀, B₀)] at hQ
      have hQ' : c₃ * R ^ (m + 4) * ‖B₀ e‖ ^ 2 ≤ ‖Λ (a₀ - F z₀, B₀)‖ ^ 2 :=
        (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 hQ
      have hRp : 0 < R ^ (m + 4) := by positivity
      have h4 : ‖B₀ e‖ ^ 2 ≤ 32 * ω / c₃ * (L : ℝ) ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc₃]
        have h5 : (c₃ * ‖B₀ e‖ ^ 2) * R ^ (m + 4) ≤ (32 * ω * L ^ 2) * R ^ (m + 4) := by
          nlinarith [hQ', hdiff]
        have h6 := le_of_mul_le_mul_right h5 hRp
        linarith
      calc ‖B₀ e‖ = Real.sqrt (‖B₀ e‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (32 * ω / c₃ * (L : ℝ) ^ 2) := Real.sqrt_le_sqrt h4
        _ = Real.sqrt (32 * ω / c₃) * L := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq L.coe_nonneg]
    exact opNorm_le_of_forall_unit B₀ (by positivity) hdir
  · -- minimality
    intro a' B'
    rw [hΦ, hΦ]
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (norm_nonneg _) (hmin _ (LinearMap.mem_range_self Λ _)) 2
  · -- uniqueness
    intro _ a' B' heq
    rw [hΦ, hΦ, ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)] at heq
    have h1 := hpyth _ (LinearMap.mem_range_self Λ (a', B'))
    rw [heq] at h1
    have h2 : ‖Λ (a₀, B₀) - Λ (a', B')‖ = 0 := by
      have : ‖Λ (a₀, B₀) - Λ (a', B')‖ ^ 2 = 0 := by linarith
      exact (pow_eq_zero_iff two_ne_zero).1 this
    have h3 : Λ (a₀ - a', B₀ - B') = 0 := by
      rw [← Prod.mk_sub_mk, map_sub]
      exact norm_eq_zero.1 h2
    have h4 : ∫⁻ q, ‖(a₀ - a') + (B₀ - B') q.1‖ₑ ^ 2 ∂σ.restrict (Metric.ball x R) = 0 := by
      rw [← hΛnorm (a₀ - a', B₀ - B'), h3, norm_zero]
      simp
    have hB : B₀ - B' = 0 := by
      have hn : ‖B₀ - B'‖ ≤ 0 := by
        refine opNorm_le_of_forall_unit _ le_rfl fun e he => ?_
        have hQ := ofReal_mul_norm_apply_sq_le_lintegral (σ.restrict (Metric.ball x R)) hK
          hslab' (a₀ - a') (B₀ - B') e he
        rw [h4, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hQ
        have hK' : 0 < c₃ * R ^ (m + 4) := by positivity
        have h5 : ‖(B₀ - B') e‖ ^ 2 ≤ 0 := by
          by_contra h
          have := mul_pos hK' (not_le.1 h)
          linarith
        have h6 : ‖(B₀ - B') e‖ = 0 :=
          (pow_eq_zero_iff two_ne_zero).1 (le_antisymm h5 (sq_nonneg _))
        rw [h6]
      exact norm_le_zero_iff.1 hn
    have ha : a₀ - a' = 0 := by
      rw [hB] at h4
      simp only [zero_apply, add_zero] at h4
      rw [lintegral_const, Measure.restrict_apply_univ] at h4
      rcases mul_eq_zero.1 h4 with h | h
      · exact enorm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)
      · exact absurd h hPpos.ne'
    exact ⟨(sub_eq_zero.1 ha).symm, (sub_eq_zero.1 hB).symm⟩

/-! ## Moment coefficients -/

/-- An allocated barycenter lies within `|C_B| r_i` of the anchor: it is the average of the
spatial coordinate against the probability density `h_{i,l}/|Q_i|`, carried by the
reservoir `S_{i,l} ⊆ P(a_i, C_B r_i)`. -/
theorem WhitneySourceAllocation.norm_barycenter_sub_anchor_le {m : ℕ} {ι : Type*}
    {F₀ : Set (Space m)} {D a : ℝ} {W : WhitneyData m ι F₀ D a} {σ : Measure (Space m)}
    {A C_B c₂ : ℝ} (S : WhitneySourceAllocation W σ A C_B c₂) (i : ι) (l : Fin (m + 1)) :
    ‖S.barycenter i l - (S.anchor i).1‖ ≤ |C_B| * W.radius i := by
  have hr : 0 < W.radius i := W.radius_pos i
  set V : ℝ := W.radius i ^ (m + 2) with hVdef
  have hV : 0 < V := by positivity
  set h : Space m → ℝ≥0∞ := S.density i l with hhdef
  have hm : Measurable h := S.measurable_density i l
  have hlin : ∫⁻ x, h x ∂σ = ENNReal.ofReal V := S.lintegral_density i l
  have hfin : ∫⁻ x, h x ∂σ ≠ ∞ := by rw [hlin]; exact ENNReal.ofReal_ne_top
  have hint : Integrable (fun x => (h x).toReal) σ :=
    integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin
  have hintV : ∫ x, (h x).toReal ∂σ = V := by
    rw [integral_toReal hm.aemeasurable (ae_lt_top hm hfin), hlin, ENNReal.toReal_ofReal hV.le]
  set p : Spatial m := (S.anchor i).1 with hpdef
  have hbound : ∀ x : Space m, ‖(h x).toReal • (x.1 - p)‖ ≤ (h x).toReal * (|C_B| * W.radius i) := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    by_cases hx : x ∈ S.reservoir i l
    · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      have hd := S.reservoir_subset i l hx
      rw [Metric.mem_ball] at hd
      have h1 : dist x.1 p ≤ dist x (S.anchor i) := by
        rw [Prod.dist_eq]; exact le_max_left _ _
      rw [← dist_eq_norm]
      calc dist x.1 p ≤ dist x (S.anchor i) := h1
        _ ≤ C_B * W.radius i := hd.le
        _ ≤ |C_B| * W.radius i := mul_le_mul_of_nonneg_right (le_abs_self C_B) hr.le
    · have h0 : h x = 0 := S.density_eq_zero i l x hx
      rw [h0, ENNReal.toReal_zero, zero_mul, zero_mul]
  have hf₁ : Integrable (fun x : Space m => (h x).toReal • (x.1 - p)) σ :=
    Integrable.mono' (hint.mul_const (|C_B| * W.radius i))
      ((hm.ennreal_toReal.smul (measurable_fst.sub_const p)).aestronglyMeasurable)
      (ae_of_all _ hbound)
  have hg : Integrable (fun x : Space m => (h x).toReal • p) σ := hint.smul_const p
  have hsplit : (fun x : Space m => (h x).toReal • x.1) =
      fun x => (h x).toReal • (x.1 - p) + (h x).toReal • p := by
    funext x
    rw [← smul_add, sub_add_cancel]
  have hb : S.barycenter i l = V⁻¹ • ∫ x, (h x).toReal • x.1 ∂σ := rfl
  have hb' : S.barycenter i l - p = V⁻¹ • ∫ x, (h x).toReal • (x.1 - p) ∂σ := by
    rw [hb, hsplit, integral_add hf₁ hg, integral_smul_const, hintV, smul_add, smul_smul,
      inv_mul_cancel₀ hV.ne', one_smul, add_sub_cancel_right]
  rw [hb', norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hV.le)]
  calc V⁻¹ * ‖∫ x, (h x).toReal • (x.1 - p) ∂σ‖
      ≤ V⁻¹ * ∫ x, (h x).toReal * (|C_B| * W.radius i) ∂σ :=
        mul_le_mul_of_nonneg_left
          (norm_integral_le_of_norm_le (hint.mul_const _) (ae_of_all _ hbound))
          (inv_nonneg.2 hV.le)
    _ = |C_B| * W.radius i := by
        rw [integral_mul_const, hintV, ← mul_assoc, inv_mul_cancel₀ hV.ne', one_mul]

/-- **Moment coefficients.** The simplex bound makes
`v ↦ Σ_k v_k (b_{i,k+1} - b_{i,0})` injective, hence surjective on `ℝ^m`; solve it for
`u_i - b_{i,0}`, whose norm is at most `(|b| + |C_B|) r_i`, and put
`c_{i,0} = 1 - Σ_k v_k`, `c_{i,k+1} = v_k`. Then `Σ_l |c_{i,l}| ≤ 1 + 2m (|b|+|C_B|)/c₂`.
For `m = 0` this gives `c_{i,0} = 1`. -/
theorem exists_moment_coefficients_proof (m : ℕ) (D a b A C_B c₂ : ℝ) (hc₂ : 0 < c₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), (∀ j, Metric.infDist (W.center j) F₀ ≤ b * W.radius j) →
      ∀ (σ : Measure (Space m)), σ ≤ parabolicVolume m →
      ∀ S : WhitneySourceAllocation W σ A C_B c₂,
        ∃ coef : ι → Fin (m + 1) → ℝ, S.IsMomentCoefficients coef C := by
  refine ⟨1 + 2 * m * ((|b| + |C_B|) / c₂), by positivity, ?_⟩
  intro ι _ F₀ W hb σ _ S
  have key : ∀ i, ∃ v : Fin m → ℝ,
      ∑ k : Fin m, v k • (S.barycenter i k.succ - S.barycenter i 0) =
        (W.center i).1 - S.barycenter i 0 ∧
      ‖WithLp.toLp 2 v‖ ≤ (|b| + |C_B|) / c₂ := by
    intro i
    have hr : 0 < W.radius i := W.radius_pos i
    let M : (Fin m → ℝ) →ₗ[ℝ] Spatial m :=
      { toFun := fun v => ∑ k : Fin m, v k • (S.barycenter i k.succ - S.barycenter i 0)
        map_add' := fun v w => by
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun t v => by
          simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
    have hlow : ∀ v, c₂ * W.radius i * ‖WithLp.toLp 2 v‖ ≤ ‖M v‖ := fun v => S.simplex i v
    have hinj : Function.Injective M := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have h := hlow v
      rw [hv, norm_zero] at h
      have h0 : ‖WithLp.toLp 2 v‖ = 0 := by
        refine le_antisymm ?_ (norm_nonneg _)
        by_contra hpos
        replace hpos := not_le.1 hpos
        have := mul_pos (mul_pos hc₂ hr) hpos
        linarith
      have h1 : WithLp.toLp 2 v = 0 := norm_eq_zero.1 h0
      have h2 := congrArg (WithLp.ofLp (p := 2)) h1
      simpa using h2
    have hsurj : Function.Surjective M :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [Module.finrank_fin_fun, finrank_euclideanSpace_fin])).1 hinj
    obtain ⟨v, hv⟩ := hsurj ((W.center i).1 - S.barycenter i 0)
    refine ⟨v, hv, ?_⟩
    -- the right-hand side is at most `(|b| + |C_B|) r_i`
    have hu : ‖(W.center i).1 - (S.anchor i).1‖ ≤ |b| * W.radius i := by
      rw [← dist_eq_norm]
      calc dist (W.center i).1 (S.anchor i).1 ≤ dist (W.center i) (S.anchor i) := by
            rw [Prod.dist_eq]; exact le_max_left _ _
        _ = Metric.infDist (W.center i) F₀ := S.dist_anchor i
        _ ≤ b * W.radius i := hb i
        _ ≤ |b| * W.radius i := mul_le_mul_of_nonneg_right (le_abs_self b) hr.le
    have hb0 := S.norm_barycenter_sub_anchor_le i 0
    have hrhs : ‖(W.center i).1 - S.barycenter i 0‖ ≤ (|b| + |C_B|) * W.radius i := by
      calc ‖(W.center i).1 - S.barycenter i 0‖
          = ‖((W.center i).1 - (S.anchor i).1) + -(S.barycenter i 0 - (S.anchor i).1)‖ := by
            congr 1; abel
        _ ≤ ‖(W.center i).1 - (S.anchor i).1‖ + ‖-(S.barycenter i 0 - (S.anchor i).1)‖ :=
            norm_add_le _ _
        _ ≤ |b| * W.radius i + |C_B| * W.radius i := by rw [norm_neg]; linarith
        _ = (|b| + |C_B|) * W.radius i := by ring
    have hMv : M v = (W.center i).1 - S.barycenter i 0 := hv
    have h1 := hlow v
    rw [hMv] at h1
    have h2 : (‖WithLp.toLp 2 v‖ * c₂) * W.radius i ≤ (|b| + |C_B|) * W.radius i := by
      linarith
    rw [le_div_iff₀ hc₂]
    exact le_of_mul_le_mul_right h2 hr
  choose v hv hvn using key
  refine ⟨fun i => Fin.cons (1 - ∑ k, v i k) (v i), ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩⟩
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have h := hv i
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul] at h
    rw [sub_smul, one_smul]
    calc S.barycenter i 0 - (∑ k, v i k) • S.barycenter i 0 +
          ∑ k, v i k • S.barycenter i k.succ
        = S.barycenter i 0 +
          (∑ k, v i k • S.barycenter i k.succ - (∑ k, v i k) • S.barycenter i 0) := by abel
      _ = S.barycenter i 0 + ((W.center i).1 - S.barycenter i 0) := by rw [h]
      _ = (W.center i).1 := by abel
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hcoord : ∀ k, |v i k| ≤ ‖WithLp.toLp 2 (v i)‖ := by
      intro k
      have := PiLp.norm_apply_le (WithLp.toLp 2 (v i)) k
      simpa [Real.norm_eq_abs] using this
    have hsum : ∑ k, |v i k| ≤ m * ((|b| + |C_B|) / c₂) := by
      calc ∑ k, |v i k| ≤ ∑ _k : Fin m, (|b| + |C_B|) / c₂ :=
            Finset.sum_le_sum fun k _ => (hcoord k).trans (hvn i)
        _ = m * ((|b| + |C_B|) / c₂) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have habs : |1 - ∑ k, v i k| ≤ 1 + ∑ k, |v i k| := by
      calc |1 - ∑ k, v i k| ≤ |(1 : ℝ)| + |∑ k, v i k| := abs_sub _ _
        _ ≤ 1 + ∑ k, |v i k| := by
            rw [abs_one]; exact add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
    linarith

/-! ## Continuous domination -/

/-- The parabolic volume is uniformly locally doubling, with constant `2^(m+2)`. -/
theorem parabolicVolume_isUnifLocDoublingMeasure (m : ℕ) :
    IsUnifLocDoublingMeasure (parabolicVolume m) := by
  refine ⟨⟨2 ^ (m + 2), eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) x => ?_⟩⟩
  rw [parabolicVolume_closedBall x (2 * ε) (by positivity), parabolicVolume_closedBall x ε hε.le,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow, ENNReal.ofReal_ofNat]
  push_cast
  apply le_of_eq
  ring

/-- **Continuous domination.** Lebesgue
differentiation for the doubling parabolic volume: at almost every point of `F₀` the
ratios `σ(P̄(x,r)) / |P̄(x,r)| ≥ c / (2 ω_m)` converge to `dσ/dp`, so `dσ/dp ≥ c/(2ω_m)`
almost everywhere on `F₀`, and `|E ∩ F₀| ≤ (2ω_m/c) ∫_{E ∩ F₀} dσ/dp ≤ (2ω_m/c) σ(E ∩ F₀)`. -/
theorem volume_restrict_le_of_source_density_proof {m : ℕ} (c : ℝ) (hc : 0 < c)
    (σ : Measure (Space m)) (hσ : σ ≤ parabolicVolume m) (F₀ : Set (Space m))
    (hF₀ : MeasurableSet F₀)
    (hden : ∀ x ∈ F₀, ∀ r : ℝ, 0 < r → ENNReal.ofReal (c * r ^ (m + 2)) ≤ σ (Metric.ball x r)) :
    (parabolicVolume m).restrict F₀ ≤ (2 * omega m / ENNReal.ofReal c) • σ.restrict F₀ := by
  have := parabolicVolume_isUnifLocDoublingMeasure m
  have : IsLocallyFiniteMeasure σ := Measure.isLocallyFiniteMeasure_of_le hσ
  have hω0 : omega m ≠ 0 := (omega_pos m).ne'
  have hωt : omega m ≠ ∞ := (omega_lt_top m).ne
  have h2ω0 : 2 * omega m ≠ 0 := mul_ne_zero two_ne_zero hω0
  have h2ωt : 2 * omega m ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hωt
  have hc0 : ENNReal.ofReal c ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hc
  have hct : ENNReal.ofReal c ≠ ∞ := ENNReal.ofReal_ne_top
  -- The density is at least `c / (2 ω_m)` almost everywhere on `F₀`.
  have hrn : ∀ᵐ x ∂parabolicVolume m, x ∈ F₀ →
      ENNReal.ofReal c / (2 * omega m) ≤ σ.rnDeriv (parabolicVolume m) x := by
    filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily (parabolicVolume m) 1).ae_tendsto_rnDeriv
      σ] with x hx hxF
    have hlim : Tendsto (fun r => σ (Metric.closedBall x r) /
        parabolicVolume m (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 (σ.rnDeriv (parabolicVolume m) x)) :=
      hx.comp (IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt (parabolicVolume m) (K := 1)
        (fun _ => x) id tendsto_id
        (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) =>
          Metric.mem_closedBall_self (by simpa using hr.le)))
    refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => ?_)
    have hball : ENNReal.ofReal (c * r ^ (m + 2)) ≤ σ (Metric.closedBall x r) :=
      (hden x hxF r hr).trans (measure_mono Metric.ball_subset_closedBall)
    rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_pow hr.le] at hball
    have hr0 : ENNReal.ofReal r ^ (m + 2) ≠ 0 :=
      pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.2 hr)
    have hrt : ENNReal.ofReal r ^ (m + 2) ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    show ENNReal.ofReal c / (2 * omega m) ≤
      σ (Metric.closedBall x r) / parabolicVolume m (Metric.closedBall x r)
    rw [parabolicVolume_closedBall x r hr.le]
    calc ENNReal.ofReal c / (2 * omega m)
        = ENNReal.ofReal c * ENNReal.ofReal r ^ (m + 2) /
            (2 * omega m * ENNReal.ofReal r ^ (m + 2)) :=
          (ENNReal.mul_div_mul_right _ _ hr0 hrt).symm
      _ ≤ σ (Metric.closedBall x r) / (2 * omega m * ENNReal.ofReal r ^ (m + 2)) :=
          ENNReal.div_le_div_right hball _
  have key : ∀ a b : ℝ≥0∞, a ≠ 0 → a ≠ ∞ → b ≠ 0 → b ≠ ∞ → a / b * (b / a) = 1 := by
    intro a b ha ha' hb hb'
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc b⁻¹ b,
      ENNReal.inv_mul_cancel hb hb', one_mul, ENNReal.mul_inv_cancel ha ha']
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
  have hsF : MeasurableSet (s ∩ F₀) := hs.inter hF₀
  have hae : ∀ᵐ x ∂(parabolicVolume m).restrict (s ∩ F₀),
      (1 : ℝ≥0∞) ≤ (2 * omega m / ENNReal.ofReal c) * σ.rnDeriv (parabolicVolume m) x := by
    refine (ae_restrict_iff' hsF).2 (hrn.mono fun x hx hxs => ?_)
    calc (1 : ℝ≥0∞) = (2 * omega m / ENNReal.ofReal c) * (ENNReal.ofReal c / (2 * omega m)) :=
          (key _ _ h2ω0 h2ωt hc0 hct).symm
      _ ≤ _ := mul_le_mul_right (hx hxs.2) _
  calc parabolicVolume m (s ∩ F₀) = ∫⁻ _ in s ∩ F₀, 1 ∂parabolicVolume m :=
        (setLIntegral_one _).symm
    _ ≤ ∫⁻ x in s ∩ F₀, (2 * omega m / ENNReal.ofReal c) *
          σ.rnDeriv (parabolicVolume m) x ∂parabolicVolume m := lintegral_mono_ae hae
    _ = (2 * omega m / ENNReal.ofReal c) *
          ∫⁻ x in s ∩ F₀, σ.rnDeriv (parabolicVolume m) x ∂parabolicVolume m :=
        lintegral_const_mul _ (Measure.measurable_rnDeriv _ _)
    _ ≤ (2 * omega m / ENNReal.ofReal c) * σ (s ∩ F₀) :=
        mul_le_mul_right (Measure.setLIntegral_rnDeriv_le _) _

end ParabolicRectifiability
