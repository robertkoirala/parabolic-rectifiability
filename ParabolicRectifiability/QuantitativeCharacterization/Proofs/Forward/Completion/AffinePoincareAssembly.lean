import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion

/-! # Second-order affine Poincaré on parabolic base balls

`d1e_affinePoincare_assembly_proof` has the type (implication form)
`d1e_TimePoincareStatement → d1e_SpatialSecondPoincareStatement →
d1e_AffinePoincareStatement`. The time and spatial second-order Poincaré statements enter only
as hypotheses.

Statement. For every rank `m` there is `C ≥ 0` (here `C = max 8 (2 C₂)`, `C₂` the constant of
the spatial child at rank `m`, chosen before `d`) such that every `C²` map
`H : ℝ^m × ℝ → ℝ^d` has on every base ball `P_b(p, r)`, `r > 0`,
`affineErrorSq ≤ C r^{-m} ∫_{P_b(p,r)} (‖D_u²H‖² + |∂_t H|²)`.

Route (transport and good slice; competitor estimate and normalization).
* **Product-measure transport** (`d1eassemblyp_ball_lintegral_eq_prod`): under the inverse
  coordinate map (`coordinates_symm_measurePreserving`, `coordinates_symm_preimage_ball`) the
  ball is `B × I`, `B = B(u_p, r)`, `I = (t_p - r², t_p + r²)`, with product Lebesgue measure.
* **Good time slice** (`d1eassemblyp_good_time`): a time `t₁ ∈ I` with
  `∫_B g(·, t₁) ≤ (2r²)⁻¹ ∫_{B × I} g` (`MeasureTheory.exists_le_setLAverage`, Tonelli
  `setLIntegral_prod_symm`), applied to `g = ‖D_u²H‖²`.
* **Competitor estimate** (`d1eassemblyp_fit_le`): `(a, B)` the spatial competitor of
  `H(·, t₁)`; `|x - z|² ≤ 2|x - y|² + 2|y - z|²` through `y = H(u, t₁)`; the time child at each
  `u` with `s₀ = t₁` gives `∫_I |H(u,·) - H(u,t₁)|² ≤ 4 r⁴ ∫_I |∂_t H(u,·)|²`; the spatial term
  is `2r² ∫_B |H(·,t₁) - a - B·|² ≤ 2r² C₂ r⁴ ∫_B ‖D_u²H(·,t₁)‖² ≤ C₂ r⁴ ∫_{B×I} ‖D_u²H‖²`;
  total `≤ max(8, 2C₂) r⁴ ∫_{B×I} (‖D_u²H‖² + |∂_tH|²)`.
* **Normalization** (`d1eassemblyp_normalize`): `baseDimension (Spatial m) + 2 = m + 4`, and
  `r^{-(m+4)} · C r⁴ = C r^{-m}`.

Measurability of every integrand comes from continuity: `H` is `C²`, so its partial derivatives
`∂_t H` and `D_u² H` are continuous (`ContDiff.fderiv`). Rank `m = 0` needs no separate case.

Helpers carry the prefix `d1eassemblyp_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-! ## Part (a): product-measure transport and the good time slice -/

/-- The time interval `I = (t₀ - r², t₀ + r²)` has Lebesgue measure `2 r²`. -/
theorem d1eassemblyp_volume_Ioo (t₀ r : ℝ) :
    volume (Ioo (t₀ - r ^ 2) (t₀ + r ^ 2)) = ENNReal.ofReal (2 * r ^ 2) := by
  rw [Real.volume_Ioo]
  congr 1
  ring

/-- **Product-measure transport.** A lower integral over the parabolic base ball `P_b(p, r)`
against `parabolicVolume m`, of an integrand written in coordinates, equals the lower integral
over the product `B(u_p, r) × (t_p - r², t_p + r²)` against product Lebesgue measure. No
measurability is needed (the inverse coordinate map is a measurable embedding). -/
theorem d1eassemblyp_ball_lintegral_eq_prod {m : ℕ} (g : Spatial m × ℝ → ℝ≥0∞)
    (p : Space m) (r : ℝ) (hr : 0 < r) :
    ∫⁻ z in Metric.ball p r, g (z.1, z.2.val) ∂parabolicVolume m =
      ∫⁻ x in Metric.ball p.1 r ×ˢ Ioo (p.2.val - r ^ 2) (p.2.val + r ^ 2), g x := by
  have h := (coordinates_symm_measurePreserving m).setLIntegral_comp_preimage_emb
    (coordinatesMeasurableEquiv m).symm.measurableEmbedding
    (fun z : Space m => g (z.1, z.2.val)) (Metric.ball p r)
  rw [coordinates_symm_preimage_ball p r hr] at h
  exact h.symm

/-- **Product-measure transport, iterated** (space outside, time inside), for a measurable
integrand: Tonelli (`setLIntegral_prod`) after `d1eassemblyp_ball_lintegral_eq_prod`. -/
theorem d1eassemblyp_ball_lintegral_eq_iterated {m : ℕ} (g : Spatial m × ℝ → ℝ≥0∞)
    (hg : Measurable g) (p : Space m) (r : ℝ) (hr : 0 < r) :
    ∫⁻ z in Metric.ball p r, g (z.1, z.2.val) ∂parabolicVolume m =
      ∫⁻ u in Metric.ball p.1 r, ∫⁻ t in Ioo (p.2.val - r ^ 2) (p.2.val + r ^ 2), g (u, t) := by
  rw [d1eassemblyp_ball_lintegral_eq_prod g p r hr]
  exact setLIntegral_prod g hg.aemeasurable

/-- **Good time slice.** For a measurable `g ≥ 0` on `ℝ^m × ℝ`, a ball `B = B(u₀, r)` and the
interval `I = (t₀ - r², t₀ + r²)`, there is `t₁ ∈ I` with
`∫_B g(·, t₁) ≤ (2r²)⁻¹ ∫_{B × I} g` (`MeasureTheory.exists_le_setLAverage`: a point where the
nonnegative measurable slice integral is at most its average over `I`). -/
theorem d1eassemblyp_good_time {m : ℕ} (g : Spatial m × ℝ → ℝ≥0∞) (hg : Measurable g)
    (u₀ : Spatial m) (t₀ r : ℝ) (hr : 0 < r) :
    ∃ t₁ ∈ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
      ∫⁻ u in Metric.ball u₀ r, g (u, t₁) ≤
        (ENNReal.ofReal (2 * r ^ 2))⁻¹ *
          ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2), g x := by
  have hvol : volume (Ioo (t₀ - r ^ 2) (t₀ + r ^ 2)) = ENNReal.ofReal (2 * r ^ 2) :=
    d1eassemblyp_volume_Ioo t₀ r
  have hpos : (0 : ℝ) < 2 * r ^ 2 := by positivity
  have hφ : Measurable (fun t : ℝ => ∫⁻ u in Metric.ball u₀ r, g (u, t)) :=
    hg.lintegral_prod_left'
  have h0 : volume (Ioo (t₀ - r ^ 2) (t₀ + r ^ 2)) ≠ 0 := by
    rw [hvol]; exact (ENNReal.ofReal_pos.2 hpos).ne'
  have htop : volume (Ioo (t₀ - r ^ 2) (t₀ + r ^ 2)) ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  obtain ⟨t₁, ht₁, hle⟩ := exists_le_setLAverage (μ := (volume : Measure ℝ))
    (s := Ioo (t₀ - r ^ 2) (t₀ + r ^ 2))
    (f := fun t : ℝ => ∫⁻ u in Metric.ball u₀ r, g (u, t)) h0 htop hφ.aemeasurable
  have hprod : ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2), g x =
      ∫⁻ t in Ioo (t₀ - r ^ 2) (t₀ + r ^ 2), ∫⁻ u in Metric.ball u₀ r, g (u, t) :=
    setLIntegral_prod_symm g hg.aemeasurable
  refine ⟨t₁, ht₁, hle.trans (le_of_eq ?_)⟩
  rw [setLAverage_eq, hvol, ENNReal.div_eq_inv_mul, hprod]

/-! ## Regularity of the slices and partial derivatives -/

/-- A spatial slice `u ↦ H(u, t₁)` of a jointly `C²` map is `C²`. -/
theorem d1eassemblyp_contDiff_slice {m d : ℕ} {H : Spatial m → ℝ → Spatial d}
    (hH : ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2)) (t₁ : ℝ) :
    ContDiff ℝ 2 (fun u : Spatial m => H u t₁) := by
  have hc : ContDiff ℝ 2 (fun u : Spatial m => ((u, t₁) : Spatial m × ℝ)) := by fun_prop
  exact hH.comp hc

/-- `(u, t) ↦ H(u, t₁)` is continuous. -/
theorem d1eassemblyp_continuous_slice {m d : ℕ} {H : Spatial m → ℝ → Spatial d}
    (hH : ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2)) (t₁ : ℝ) :
    Continuous (fun x : Spatial m × ℝ => H x.1 t₁) := by
  have hc : Continuous (fun x : Spatial m × ℝ => ((x.1, t₁) : Spatial m × ℝ)) := by fun_prop
  exact hH.continuous.comp hc

/-- The time derivative `(u, t) ↦ ∂_t H(u, t)` of a jointly `C²` map is continuous. -/
theorem d1eassemblyp_continuous_timeDeriv {m d : ℕ} {H : Spatial m → ℝ → Spatial d}
    (hH : ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2)) :
    Continuous (fun x : Spatial m × ℝ => deriv (fun s => H x.1 s) x.2) := by
  have hc : ContDiff ℝ 2 (fun q : (Spatial m × ℝ) × ℝ => ((q.1.1, q.2) : Spatial m × ℝ)) := by
    fun_prop
  have h1 : ContDiff ℝ 1 (fun x : Spatial m × ℝ => fderiv ℝ (fun s => H x.1 s) x.2) :=
    ContDiff.fderiv (f := fun (x : Spatial m × ℝ) (s : ℝ) => H x.1 s) (g := fun x => x.2)
      (hH.comp hc) contDiff_snd one_add_one_eq_two.le
  exact h1.continuous.clm_apply (continuous_const : Continuous fun _ : Spatial m × ℝ => (1 : ℝ))

/-- The second spatial derivative `(u, t) ↦ D_u² H(u, t)` of a jointly `C²` map is
continuous. -/
theorem d1eassemblyp_continuous_spaceDeriv2 {m d : ℕ} {H : Spatial m → ℝ → Spatial d}
    (hH : ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2)) :
    Continuous (fun x : Spatial m × ℝ =>
      fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1) := by
  have hc : ContDiff ℝ 2 (fun q : ((Spatial m × ℝ) × Spatial m) × Spatial m =>
      ((q.2, q.1.1.2) : Spatial m × ℝ)) := by fun_prop
  have h1 : ContDiff ℝ 1 (fun q : (Spatial m × ℝ) × Spatial m =>
      fderiv ℝ (fun w => H w q.1.2) q.2) :=
    ContDiff.fderiv (f := fun (q : (Spatial m × ℝ) × Spatial m) (w : Spatial m) => H w q.1.2)
      (g := fun q => q.2) (hH.comp hc) contDiff_snd one_add_one_eq_two.le
  have h2 : ContDiff ℝ 0 (fun x : Spatial m × ℝ =>
      fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1) :=
    ContDiff.fderiv
      (f := fun (x : Spatial m × ℝ) (v : Spatial m) => fderiv ℝ (fun w => H w x.2) v)
      (g := fun x => x.1) h1 contDiff_fst (zero_add (1 : WithTop ℕ∞)).le
  exact h2.continuous

/-- `x ↦ ‖f x‖ₑ²` is measurable for continuous `f`. -/
theorem d1eassemblyp_measurable_enorm_sq {α E : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [SeminormedAddCommGroup E] {f : α → E} (hf : Continuous f) :
    Measurable (fun x => ‖f x‖ₑ ^ 2) :=
  hf.enorm.measurable.pow_const 2

/-! ## Elementary inequalities -/

/-- `|x - z|² ≤ 2|x - y|² + 2|y - z|²` for extended norms. -/
theorem d1eassemblyp_enorm_sub_sq_le {E : Type*} [SeminormedAddCommGroup E] (x y z : E) :
    ‖x - z‖ₑ ^ 2 ≤ 2 * ‖x - y‖ₑ ^ 2 + 2 * ‖y - z‖ₑ ^ 2 := by
  have hr : ‖x - z‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖y - z‖ ^ 2 := by
    have h1 : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := norm_sub_le_norm_sub_add_norm_sub x y z
    have h2 : ‖x - z‖ ^ 2 ≤ (‖x - y‖ + ‖y - z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖x - y‖ - ‖y - z‖)]
  have hxy : (0 : ℝ) ≤ 2 * ‖x - y‖ ^ 2 := by positivity
  have hyz : (0 : ℝ) ≤ 2 * ‖y - z‖ ^ 2 := by positivity
  calc ‖x - z‖ₑ ^ 2 = ENNReal.ofReal (‖x - z‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ ≤ ENNReal.ofReal (2 * ‖x - y‖ ^ 2 + 2 * ‖y - z‖ ^ 2) := ENNReal.ofReal_le_ofReal hr
    _ = 2 * ‖x - y‖ₑ ^ 2 + 2 * ‖y - z‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_add hxy hyz, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_pow (norm_nonneg _),
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ofReal_norm, ENNReal.ofReal_ofNat]

/-- `ofReal (‖x‖² + ‖y‖²) = ‖x‖ₑ² + ‖y‖ₑ²`. -/
theorem d1eassemblyp_ofReal_sq_add {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (x : E) (y : F) :
    ENNReal.ofReal (‖x‖ ^ 2 + ‖y‖ ^ 2) = ‖x‖ₑ ^ 2 + ‖y‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ofReal_norm]

/-- Integrated two-term splitting: `F ≤ 2 T₁ + 2 T₂` pointwise gives
`∫ F ≤ 2 ∫ T₁ + 2 ∫ T₂` (measurable `T₁`, `T₂`). -/
theorem d1eassemblyp_lintegral_split {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {F T₁ T₂ : α → ℝ≥0∞} (hT₁ : Measurable T₁) (hT₂ : Measurable T₂)
    (h : ∀ x, F x ≤ 2 * T₁ x + 2 * T₂ x) :
    ∫⁻ x, F x ∂μ ≤ 2 * ∫⁻ x, T₁ x ∂μ + 2 * ∫⁻ x, T₂ x ∂μ := by
  calc ∫⁻ x, F x ∂μ ≤ ∫⁻ x, (2 * T₁ x + 2 * T₂ x) ∂μ := lintegral_mono h
    _ = ∫⁻ x, 2 * T₁ x ∂μ + ∫⁻ x, 2 * T₂ x ∂μ := lintegral_add_left (hT₁.const_mul 2) _
    _ = 2 * ∫⁻ x, T₁ x ∂μ + 2 * ∫⁻ x, T₂ x ∂μ := by
        rw [lintegral_const_mul 2 hT₁, lintegral_const_mul 2 hT₂]

/-- Constant bookkeeping: `2 A ≤ K`, `2 B ≤ K` give `2 (A Jt) + 2 (B J₂) ≤ K (J₂ + Jt)`. -/
theorem d1eassemblyp_combine {A Bc K Jt J₂ : ℝ≥0∞} (hA : 2 * A ≤ K) (hB : 2 * Bc ≤ K) :
    2 * (A * Jt) + 2 * (Bc * J₂) ≤ K * (J₂ + Jt) := by
  calc 2 * (A * Jt) + 2 * (Bc * J₂) = 2 * A * Jt + 2 * Bc * J₂ := by ring
    _ ≤ K * Jt + K * J₂ := by gcongr
    _ = K * (J₂ + Jt) := by ring

/-- **Normalization.** With `n = m + 4` (`baseDimension (Spatial m) + 2`),
`X ≤ C r⁴ J` gives `r^{-n} X ≤ C r^{-m} J`. -/
theorem d1eassemblyp_normalize {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r) {m n : ℕ}
    (hn : n = m + 4) {X J : ℝ≥0∞} (hX : X ≤ ENNReal.ofReal (C * r ^ 4) * J) :
    (ENNReal.ofReal r)⁻¹ ^ n * X ≤ ENNReal.ofReal C * (ENNReal.ofReal r)⁻¹ ^ m * J := by
  subst hn
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  have h4 : (ENNReal.ofReal r)⁻¹ ^ 4 * ENNReal.ofReal r ^ 4 = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel hr0 ENNReal.ofReal_ne_top, one_pow]
  calc (ENNReal.ofReal r)⁻¹ ^ (m + 4) * X
      ≤ (ENNReal.ofReal r)⁻¹ ^ (m + 4) * (ENNReal.ofReal (C * r ^ 4) * J) := by gcongr
    _ = ENNReal.ofReal C * (ENNReal.ofReal r)⁻¹ ^ m * J *
          ((ENNReal.ofReal r)⁻¹ ^ 4 * ENNReal.ofReal r ^ 4) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow hr.le, pow_add]
        ring
    _ = ENNReal.ofReal C * (ENNReal.ofReal r)⁻¹ ^ m * J := by rw [h4, mul_one]

/-! ## Part (b): the competitor estimate -/

/-- **Time term.** By the time child at each `u` with base time `s₀ = t₁ ∈ I`:
`∫_{B × I} |H(u,t) - H(u,t₁)|² ≤ 4 r⁴ ∫_{B × I} |∂_t H|²`. -/
theorem d1eassemblyp_time_term (hT : d1e_TimePoincareStatement) {m d : ℕ}
    {H : Spatial m → ℝ → Spatial d} (hH : ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2))
    (u₀ : Spatial m) (t₀ r : ℝ) (hr : 0 < r) (t₁ : ℝ)
    (ht₁ : t₁ ∈ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2)) :
    ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2), ‖H x.1 x.2 - H x.1 t₁‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * r ^ 4) *
        ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
          ‖deriv (fun s => H x.1 s) x.2‖ₑ ^ 2 := by
  have hm1 : Measurable (fun x : Spatial m × ℝ => ‖H x.1 x.2 - H x.1 t₁‖ₑ ^ 2) :=
    d1eassemblyp_measurable_enorm_sq (hH.continuous.sub (d1eassemblyp_continuous_slice hH t₁))
  have hm2 : Measurable (fun x : Spatial m × ℝ => ‖deriv (fun s => H x.1 s) x.2‖ₑ ^ 2) :=
    d1eassemblyp_measurable_enorm_sq (d1eassemblyp_continuous_timeDeriv hH)
  have e1 : ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
        ‖H x.1 x.2 - H x.1 t₁‖ₑ ^ 2 =
      ∫⁻ u in Metric.ball u₀ r, ∫⁻ t in Ioo (t₀ - r ^ 2) (t₀ + r ^ 2), ‖H u t - H u t₁‖ₑ ^ 2 :=
    setLIntegral_prod _ hm1.aemeasurable
  have e2 : ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
        ‖deriv (fun s => H x.1 s) x.2‖ₑ ^ 2 =
      ∫⁻ u in Metric.ball u₀ r, ∫⁻ t in Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
        ‖deriv (fun s => H u s) t‖ₑ ^ 2 :=
    setLIntegral_prod _ hm2.aemeasurable
  have hu : ∀ u : Spatial m,
      ∫⁻ t in Ioo (t₀ - r ^ 2) (t₀ + r ^ 2), ‖H u t - H u t₁‖ₑ ^ 2 ≤
        ENNReal.ofReal (4 * r ^ 4) *
          ∫⁻ t in Ioo (t₀ - r ^ 2) (t₀ + r ^ 2), ‖deriv (fun s => H u s) t‖ₑ ^ 2 := by
    intro u
    have hpath : ContDiff ℝ 2 (fun s : ℝ => ((u, s) : Spatial m × ℝ)) := by fun_prop
    have hcd : ContDiff ℝ 1 (fun s : ℝ => H u s) := (hH.comp hpath).of_le one_le_two
    have hab : t₀ - r ^ 2 < t₀ + r ^ 2 := by
      have := pow_pos hr 2
      linarith
    have h := hT d (fun s : ℝ => H u s) (t₀ - r ^ 2) (t₀ + r ^ 2) hab hcd t₁
      (Ioo_subset_Icc_self ht₁)
    have hlen : (t₀ + r ^ 2 - (t₀ - r ^ 2)) ^ 2 = 4 * r ^ 4 := by ring
    rw [hlen] at h
    exact h
  rw [e1, e2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun u => hu u

/-- **Spatial term, time integration.** The integrand `|H(u,t₁) - a - B u|²` does not depend on
`t`, so its integral over `B × I` is `2 r²` times its integral over `B`. -/
theorem d1eassemblyp_space_term {m d : ℕ} {H : Spatial m → ℝ → Spatial d}
    (hH : ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2)) (u₀ : Spatial m) (t₀ r t₁ : ℝ)
    (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d) :
    ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2), ‖H x.1 t₁ - (a + B x.1)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * r ^ 2) * ∫⁻ u in Metric.ball u₀ r, ‖H u t₁ - (a + B u)‖ₑ ^ 2 := by
  have hc : Continuous (fun x : Spatial m × ℝ => H x.1 t₁ - (a + B x.1)) :=
    (d1eassemblyp_continuous_slice hH t₁).sub (by fun_prop)
  have hmeas : Measurable (fun x : Spatial m × ℝ => ‖H x.1 t₁ - (a + B x.1)‖ₑ ^ 2) :=
    d1eassemblyp_measurable_enorm_sq hc
  have e : ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
        ‖H x.1 t₁ - (a + B x.1)‖ₑ ^ 2 =
      ∫⁻ u in Metric.ball u₀ r, ∫⁻ _t in Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
        ‖H u t₁ - (a + B u)‖ₑ ^ 2 :=
    setLIntegral_prod _ hmeas.aemeasurable
  have hconst : ∀ u : Spatial m,
      ∫⁻ _t in Ioo (t₀ - r ^ 2) (t₀ + r ^ 2), ‖H u t₁ - (a + B u)‖ₑ ^ 2 =
        ‖H u t₁ - (a + B u)‖ₑ ^ 2 * ENNReal.ofReal (2 * r ^ 2) := by
    intro u
    rw [setLIntegral_const, d1eassemblyp_volume_Ioo]
  rw [e, lintegral_congr hconst, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  exact mul_comm _ _

/-- **Splitting through the good slice.** On `B × I`:
`∫ |H - a - B u|² ≤ 2 ∫ |H(u,t) - H(u,t₁)|² + 2 ∫ |H(u,t₁) - a - B u|²`. -/
theorem d1eassemblyp_split_le {m d : ℕ} {H : Spatial m → ℝ → Spatial d}
    (hH : ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2)) (u₀ : Spatial m) (t₀ r t₁ : ℝ)
    (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d) :
    ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2), ‖H x.1 x.2 - (a + B x.1)‖ₑ ^ 2 ≤
      2 * (∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
          ‖H x.1 x.2 - H x.1 t₁‖ₑ ^ 2) +
        2 * ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
          ‖H x.1 t₁ - (a + B x.1)‖ₑ ^ 2 := by
  have hm1 : Measurable (fun x : Spatial m × ℝ => ‖H x.1 x.2 - H x.1 t₁‖ₑ ^ 2) :=
    d1eassemblyp_measurable_enorm_sq (hH.continuous.sub (d1eassemblyp_continuous_slice hH t₁))
  have hm2 : Measurable (fun x : Spatial m × ℝ => ‖H x.1 t₁ - (a + B x.1)‖ₑ ^ 2) :=
    d1eassemblyp_measurable_enorm_sq ((d1eassemblyp_continuous_slice hH t₁).sub (by fun_prop))
  exact d1eassemblyp_lintegral_split
    (F := fun x : Spatial m × ℝ => ‖H x.1 x.2 - (a + B x.1)‖ₑ ^ 2)
    ((volume : Measure (Spatial m × ℝ)).restrict
      (Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2))) hm1 hm2
    fun x => d1eassemblyp_enorm_sub_sq_le (H x.1 x.2) (H x.1 t₁) (a + B x.1)

/-- **Spatial term.** From the spatial child at the good time `t₁` and the good-slice bound:
`∫_{B × I} |H(u,t₁) - a - B u|² ≤ C₂ r⁴ ∫_{B × I} ‖D_u²H‖²`. -/
theorem d1eassemblyp_space_bound {m d : ℕ} {C₂ : ℝ}
    {H : Spatial m → ℝ → Spatial d} (hH : ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2))
    (u₀ : Spatial m) (t₀ r : ℝ) (hr : 0 < r) (t₁ : ℝ) (a : Spatial d)
    (B : Spatial m →L[ℝ] Spatial d)
    (hspace : ∫⁻ u in Metric.ball u₀ r, ‖H u t₁ - (a + B u)‖ₑ ^ 2 ≤
      ENNReal.ofReal (C₂ * r ^ 4) *
        ∫⁻ u in Metric.ball u₀ r, ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w t₁) v) u‖ₑ ^ 2)
    (hgood : ∫⁻ u in Metric.ball u₀ r,
        ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w t₁) v) u‖ₑ ^ 2 ≤
      (ENNReal.ofReal (2 * r ^ 2))⁻¹ *
        ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
          ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ₑ ^ 2) :
    ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
        ‖H x.1 t₁ - (a + B x.1)‖ₑ ^ 2 ≤
      ENNReal.ofReal (C₂ * r ^ 4) *
        ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
          ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ₑ ^ 2 := by
  have h2r : ENNReal.ofReal (2 * r ^ 2) * (ENNReal.ofReal (2 * r ^ 2))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top
  have hgood' : ENNReal.ofReal (2 * r ^ 2) *
        ∫⁻ u in Metric.ball u₀ r, ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w t₁) v) u‖ₑ ^ 2 ≤
      ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
        ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ₑ ^ 2 := by
    calc _ ≤ ENNReal.ofReal (2 * r ^ 2) * ((ENNReal.ofReal (2 * r ^ 2))⁻¹ *
          ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
            ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ₑ ^ 2) := by gcongr
      _ = _ := by rw [← mul_assoc, h2r, one_mul]
  rw [d1eassemblyp_space_term hH u₀ t₀ r t₁ a B]
  calc ENNReal.ofReal (2 * r ^ 2) * ∫⁻ u in Metric.ball u₀ r, ‖H u t₁ - (a + B u)‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 * r ^ 2) * (ENNReal.ofReal (C₂ * r ^ 4) *
          ∫⁻ u in Metric.ball u₀ r,
            ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w t₁) v) u‖ₑ ^ 2) := by gcongr
    _ = ENNReal.ofReal (C₂ * r ^ 4) * (ENNReal.ofReal (2 * r ^ 2) *
          ∫⁻ u in Metric.ball u₀ r,
            ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w t₁) v) u‖ₑ ^ 2) := mul_left_comm _ _ _
    _ ≤ _ := by gcongr

/-- The derivative integrand: `ofReal (‖D_u²H‖² + |∂_tH|²) = ‖D_u²H‖ₑ² + ‖∂_tH‖ₑ²`. -/
theorem d1eassemblyp_integrand_eq {m d : ℕ} (H : Spatial m → ℝ → Spatial d)
    (x : Spatial m × ℝ) :
    ENNReal.ofReal (‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ ^ 2 +
        ‖deriv (fun s => H x.1 s) x.2‖ ^ 2) =
      ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ₑ ^ 2 +
        ‖deriv (fun s => H x.1 s) x.2‖ₑ ^ 2 :=
  d1eassemblyp_ofReal_sq_add (fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1)
    (deriv (fun s => H x.1 s) x.2)

/-- **Energy splitting.** The derivative energy on `B × I` is the sum of the second-order
spatial energy and the time energy. -/
theorem d1eassemblyp_energy_split {m d : ℕ} {H : Spatial m → ℝ → Spatial d}
    (hH : ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2)) (u₀ : Spatial m) (t₀ r : ℝ) :
    ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
        ENNReal.ofReal (‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ ^ 2 +
          ‖deriv (fun s => H x.1 s) x.2‖ ^ 2) =
      (∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
          ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ₑ ^ 2) +
        ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
          ‖deriv (fun s => H x.1 s) x.2‖ₑ ^ 2 := by
  have hmD : Measurable (fun x : Spatial m × ℝ =>
      ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ₑ ^ 2) :=
    d1eassemblyp_measurable_enorm_sq (d1eassemblyp_continuous_spaceDeriv2 hH)
  rw [← lintegral_add_left hmD]
  exact lintegral_congr (d1eassemblyp_integrand_eq H)

/-- Constant bookkeeping: `2 a ≤ b` gives `2 · ofReal (a r⁴) ≤ ofReal (b r⁴)`. -/
theorem d1eassemblyp_two_ofReal_le {a b r : ℝ} (hr : 0 < r) (hab : 2 * a ≤ b) :
    2 * ENNReal.ofReal (a * r ^ 4) ≤ ENNReal.ofReal (b * r ^ 4) := by
  have h : (2 : ℝ) * (a * r ^ 4) ≤ b * r ^ 4 :=
    calc (2 : ℝ) * (a * r ^ 4) = 2 * a * r ^ 4 := by ring
      _ ≤ b * r ^ 4 := mul_le_mul_of_nonneg_right hab (pow_pos hr 4).le
  calc 2 * ENNReal.ofReal (a * r ^ 4) = ENNReal.ofReal (2 * (a * r ^ 4)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h

/-- **Competitor estimate on the product.** With `t₁ ∈ I` a good time for `‖D_u²H‖²` and
`(a, B)` a spatial second-order competitor of `H(·, t₁)` on `B(u₀, r)` with constant `C₂`:
`∫_{B × I} |H - a - B u|² ≤ max(8, 2C₂) r⁴ ∫_{B × I} (‖D_u²H‖² + |∂_t H|²)`. -/
theorem d1eassemblyp_fit_le (hT : d1e_TimePoincareStatement) {m d : ℕ} {C₂ : ℝ}
    {H : Spatial m → ℝ → Spatial d} (hH : ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2))
    (u₀ : Spatial m) (t₀ r : ℝ) (hr : 0 < r) (t₁ : ℝ)
    (ht₁ : t₁ ∈ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2)) (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d)
    (hspace : ∫⁻ u in Metric.ball u₀ r, ‖H u t₁ - (a + B u)‖ₑ ^ 2 ≤
      ENNReal.ofReal (C₂ * r ^ 4) *
        ∫⁻ u in Metric.ball u₀ r, ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w t₁) v) u‖ₑ ^ 2)
    (hgood : ∫⁻ u in Metric.ball u₀ r,
        ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w t₁) v) u‖ₑ ^ 2 ≤
      (ENNReal.ofReal (2 * r ^ 2))⁻¹ *
        ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
          ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ₑ ^ 2) :
    ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2), ‖H x.1 x.2 - (a + B x.1)‖ₑ ^ 2 ≤
      ENNReal.ofReal (max 8 (2 * C₂) * r ^ 4) *
        ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
          ENNReal.ofReal (‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ ^ 2 +
            ‖deriv (fun s => H x.1 s) x.2‖ ^ 2) := by
  have hsplit := d1eassemblyp_split_le hH u₀ t₀ r t₁ a B
  have htime := d1eassemblyp_time_term hT hH u₀ t₀ r hr t₁ ht₁
  have hsp := d1eassemblyp_space_bound hH u₀ t₀ r hr t₁ a B hspace hgood
  have hA : 2 * ENNReal.ofReal (4 * r ^ 4) ≤ ENNReal.ofReal (max 8 (2 * C₂) * r ^ 4) :=
    d1eassemblyp_two_ofReal_le hr
      ((le_of_eq (by norm_num : (2 : ℝ) * 4 = 8)).trans (le_max_left 8 (2 * C₂)))
  have hB : 2 * ENNReal.ofReal (C₂ * r ^ 4) ≤ ENNReal.ofReal (max 8 (2 * C₂) * r ^ 4) :=
    d1eassemblyp_two_ofReal_le hr (le_max_right 8 (2 * C₂))
  rw [d1eassemblyp_energy_split hH u₀ t₀ r]
  calc _ ≤ _ := hsplit
    _ ≤ 2 * (ENNReal.ofReal (4 * r ^ 4) *
            ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
              ‖deriv (fun s => H x.1 s) x.2‖ₑ ^ 2) +
          2 * (ENNReal.ofReal (C₂ * r ^ 4) *
            ∫⁻ x in Metric.ball u₀ r ×ˢ Ioo (t₀ - r ^ 2) (t₀ + r ^ 2),
              ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ₑ ^ 2) := by
        gcongr
    _ ≤ _ := d1eassemblyp_combine hA hB

/-! ## Identification with the base `affineErrorSq` -/

/-- The base fit integral `affineFitIntegral` of `(u, t) ↦ H(u, t)` on `P_b(p, r)` is the lower
integral over the product `B(u_p, r) × (t_p - r², t_p + r²)` (product-measure transport). -/
theorem d1eassemblyp_fitIntegral_eq {m d : ℕ} (H : Spatial m → ℝ → Spatial d) (a : Spatial d)
    (B : Spatial m →L[ℝ] Spatial d) (p : Space m) (r : ℝ) (hr : 0 < r) :
    affineFitIntegral (parabolicVolume m) (fun z : Space m => H z.1 z.2.val) a B p r =
      ∫⁻ x in Metric.ball p.1 r ×ˢ Ioo (p.2.val - r ^ 2) (p.2.val + r ^ 2),
        ‖H x.1 x.2 - (a + B x.1)‖ₑ ^ 2 :=
  d1eassemblyp_ball_lintegral_eq_prod
    (fun x : Spatial m × ℝ => ‖H x.1 x.2 - (a + B x.1)‖ₑ ^ 2) p r hr

/-- One competitor bounds the infimum (generic base `E × Time`, so that the slope type of the
competitor is syntactically the index type of the infimum). -/
theorem d1eassemblyp_affineErrorSq_le_of_fit {E Y : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (μ : Measure (E × Time)) (f : E × Time → Y) (y : E × Time) {s : ℝ} (hs : 0 < s)
    (a : Y) (B : E →L[ℝ] Y) {X : ℝ≥0∞} (h : affineFitIntegral μ f a B y s ≤ X) :
    affineErrorSq μ f y s ≤ (ENNReal.ofReal s)⁻¹ ^ (baseDimension E + 2) * X := by
  have hinf : ⨅ (a' : Y) (B' : E →L[ℝ] Y), affineFitIntegral μ f a' B' y s ≤ X :=
    iInf_le_of_le a (iInf_le_of_le B h)
  rw [affineErrorSq, ite_eq_left hs]
  gcongr

/-- One competitor `(a, B)` with `fit ≤ C r⁴ J` bounds the normalized base error:
`affineErrorSq ≤ C r^{-m} J` (`baseDimension (Spatial m) + 2 = m + 4`). -/
theorem d1eassemblyp_affineErrorSq_le {m d : ℕ} (H : Spatial m → ℝ → Spatial d) (p : Space m)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d)
    {J : ℝ≥0∞}
    (h : affineFitIntegral (parabolicVolume m) (fun z : Space m => H z.1 z.2.val) a B p r ≤
      ENNReal.ofReal (C * r ^ 4) * J) :
    affineErrorSq (parabolicVolume m) (fun z : Space m => H z.1 z.2.val) p r ≤
      ENNReal.ofReal C * (ENNReal.ofReal r)⁻¹ ^ m * J := by
  have hbd : baseDimension (Spatial m) + 2 = m + 4 := by
    have h : Module.finrank ℝ (Spatial m) = m := finrank_euclideanSpace_fin
    unfold baseDimension
    omega
  exact (d1eassemblyp_affineErrorSq_le_of_fit (parabolicVolume m)
    (fun z : Space m => H z.1 z.2.val) p hr a B h).trans (d1eassemblyp_normalize hC hr hbd le_rfl)

/-- Transport of the competitor estimate back to `P_b(p, r)` and normalization. -/
theorem d1eassemblyp_conclude {m d : ℕ} (H : Spatial m → ℝ → Spatial d) (p : Space m)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d)
    (h : ∫⁻ x in Metric.ball p.1 r ×ˢ Ioo (p.2.val - r ^ 2) (p.2.val + r ^ 2),
        ‖H x.1 x.2 - (a + B x.1)‖ₑ ^ 2 ≤
      ENNReal.ofReal (C * r ^ 4) *
        ∫⁻ x in Metric.ball p.1 r ×ˢ Ioo (p.2.val - r ^ 2) (p.2.val + r ^ 2),
          ENNReal.ofReal (‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ ^ 2 +
            ‖deriv (fun s => H x.1 s) x.2‖ ^ 2)) :
    affineErrorSq (parabolicVolume m) (fun z : Space m => H z.1 z.2.val) p r ≤
      ENNReal.ofReal C * (ENNReal.ofReal r)⁻¹ ^ m *
        ∫⁻ z in Metric.ball p r,
          ENNReal.ofReal (‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w z.2.val) v) z.1‖ ^ 2 +
            ‖deriv (fun s => H z.1 s) z.2.val‖ ^ 2) ∂parabolicVolume m := by
  apply d1eassemblyp_affineErrorSq_le H p hr hC a B
  rw [d1eassemblyp_fitIntegral_eq H a B p r hr,
    d1eassemblyp_ball_lintegral_eq_prod
      (fun x : Spatial m × ℝ =>
        ENNReal.ofReal (‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ ^ 2 +
          ‖deriv (fun s => H x.1 s) x.2‖ ^ 2)) p r hr]
  exact h

/-! ## The assembly -/

/-- **Second-order affine Poincaré on parabolic base balls**
(implication form of `d1e_affinePoincare_assembly_proof`).
From the time child (constant `1`) and the spatial second-order child
(constant `C₂` at rank `m`), the constant `max 8 (2 C₂)` works at rank `m`, for every target
dimension `d`. -/
theorem d1e_affinePoincare_assembly_proof :
    d1e_TimePoincareStatement → d1e_SpatialSecondPoincareStatement →
      d1e_AffinePoincareStatement := by
  intro hT hS m
  obtain ⟨C₂, -, hS'⟩ := hS m
  have hC : (0 : ℝ) ≤ max 8 (2 * C₂) := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨max 8 (2 * C₂), hC, ?_⟩
  intro d H hH p r hr
  obtain ⟨t₁, ht₁, hgood⟩ := d1eassemblyp_good_time
    (fun x : Spatial m × ℝ => ‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w x.2) v) x.1‖ₑ ^ 2)
    (d1eassemblyp_measurable_enorm_sq (d1eassemblyp_continuous_spaceDeriv2 hH)) p.1 p.2.val r hr
  obtain ⟨a, B, hspace⟩ := hS' d (fun u => H u t₁) (d1eassemblyp_contDiff_slice hH t₁) p.1 r hr
  exact d1eassemblyp_conclude H p hr hC a B
    (d1eassemblyp_fit_le hT hH p.1 p.2.val r hr t₁ ht₁ a B hspace hgood)

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
