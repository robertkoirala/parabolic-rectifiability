import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion
import ParabolicRectifiability.Analysis.TraceExtension.CutoffCarleson

/-! # Affine energy of the smooth attachment

Proof of `d1e_attachment_energy` (implication form of `d1e_AttachmentEnergyStatement`). The
Poincaré statement `d1e_AffinePoincareStatement` is a hypothesis.

Part (a): the support-weighted estimate. We work with an abstract separated family:
an index type `I`, radii `s i > 0`, centres `p i` in the base `Space m`, vectors `v i` with
`‖v i‖ ≤ 2 a s i`, and pairwise separation `s i + s j ≤ d(p i, p j)` (so the open balls
`P(p i, s i)` are disjoint; the closed ones may touch). The bumps are the base
`SmoothCutoff.parabolicBump` of radius `s i / 3`, whose closed support lies in the open ball
`P(p i, s i)`, and `G = ∑' i, ψ_i v_i`. For a testing radius `r` such that only finitely many
bumps are large (`r ≤ s i`), put `H_r = ∑_{r ≤ s i} ψ_i v_i` (a finite sum, smooth) and
`J_r = G - H_r` (the small bumps). Poincaré is applied once to `H_r`; at every point at most one
bump is active, so the derivative energy of `H_r` is that of a single bump and `|J_r|` is that
of a single small bump. Two-term subadditivity of the affine error (only the first summand needs
to be measurable) gives

`a_G(y,r)² ≤ C a² r^{-(m+2)} ∫_{P(y,r)} ∑_i 1_{P(p_i,s_i)} min(r/s_i, s_i/r)²`,

with `C = 1296 C_P B² + 8` (`B = bumpBound m`, `C_P` the Poincaré constant). The weight
`min(r/s, s/r)²` is `(r/s)²` for `r ≤ s` and `(s/r)²` for `s < r`.

Part (b): the integration. Each bracket's scale integral over `(0, R)` is at most `2`
for every `R` (`∫_0^s (r/s) dr/r = 1`, `∫_s^∞ (s/r)² dr/r = 1/2`), so a bump much larger than
the testing root is never charged with its whole volume. Tonelli (three swaps of `y`, `r`, `x`,
with the explicit measurable kernel `r^{-(m+2)} 1_{P(y,r)}(x) W_r(x)`) and
`r^{-(m+2)} |P(x,r)| = 2 ω_m` reduce the Carleson integral over `P(z,R)` to
`2 ω_m ∫_{P(z,2R)} ∫_0^R W_r(x) dr/r dx ≤ 4 ω_m |P(z,2R)|`; at most one support meets each point.

Infinite families. The neck has finitely many stops above each positive level (compact centre
set and `bpn:stop-separation`, `d1eaenergy_stopping_finite`), so at every testing radius the
large-bump sum `H_r` is already a finite sum and `J_r = G - H_r` is handled pointwise (at most
one nonzero term of the `tsum`). This replaces the uniform finite approximation and the Fatou
passage of the route by an exact identity; countability of the stops (needed for
the measurability of `W`) follows from the same finiteness. No chart metric bound is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

section SupportWeighted

variable {m n : ℕ} {I : Type*}

/-! ### The scale weight and the support-weighted sum -/

/-- The scale weight `min(r/s, s/r)²`: `(r/s)²` for `r ≤ s`, `(s/r)²` for `s < r`. -/
def d1eaenergy_weight (s r : ℝ) : ℝ := min (r / s) (s / r) ^ 2

theorem d1eaenergy_weight_nonneg (s r : ℝ) : 0 ≤ d1eaenergy_weight s r := sq_nonneg _

theorem d1eaenergy_weight_of_le {s r : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    d1eaenergy_weight s r = (r / s) ^ 2 := by
  have hs : 0 < s := hr.trans_le hrs
  unfold d1eaenergy_weight
  rw [min_eq_left]
  rw [div_le_div_iff₀ hs hr]
  nlinarith

theorem d1eaenergy_weight_of_lt {s r : ℝ} (hs : 0 < s) (hsr : s < r) :
    d1eaenergy_weight s r = (s / r) ^ 2 := by
  have hr : 0 < r := hs.trans hsr
  unfold d1eaenergy_weight
  rw [min_eq_right]
  rw [div_le_div_iff₀ hr hs]
  nlinarith

/-- The support-weighted sum `W_r(x) = ∑_i 1_{P(p_i,s_i)}(x) min(r/s_i, s_i/r)²`. -/
def d1eaenergy_weightSum (s : I → ℝ) (p : I → Space m) (r : ℝ) (x : Space m) : ℝ≥0∞ :=
  ∑' i, (Metric.ball (p i) (s i)).indicator
    (fun _ => ENNReal.ofReal (d1eaenergy_weight (s i) r)) x

theorem d1eaenergy_le_weightSum (s : I → ℝ) (p : I → Space m) (r : ℝ) {x : Space m} {j : I}
    (hj : x ∈ Metric.ball (p j) (s j)) :
    ENNReal.ofReal (d1eaenergy_weight (s j) r) ≤ d1eaenergy_weightSum s p r x :=
  calc ENNReal.ofReal (d1eaenergy_weight (s j) r)
      = (Metric.ball (p j) (s j)).indicator
          (fun _ => ENNReal.ofReal (d1eaenergy_weight (s j) r)) x :=
        (Set.indicator_of_mem hj (fun _ => ENNReal.ofReal (d1eaenergy_weight (s j) r))).symm
    _ ≤ d1eaenergy_weightSum s p r x :=
        ENNReal.le_tsum (f := fun i => (Metric.ball (p i) (s i)).indicator
          (fun _ => ENNReal.ofReal (d1eaenergy_weight (s i) r)) x) j

/-! ### Disjoint supports -/

/-- At most one open ball of a separated family contains a given point. -/
theorem d1eaenergy_eq_of_mem_ball {s : I → ℝ} {p : I → Space m}
    (hdisj : ∀ i j, i ≠ j → s i + s j ≤ dist (p i) (p j)) {x : Space m} {i j : I}
    (hi : x ∈ Metric.ball (p i) (s i)) (hj : x ∈ Metric.ball (p j) (s j)) : i = j := by
  by_contra hij
  have h1 := hdisj i j hij
  have h2 : dist (p i) (p j) ≤ dist x (p i) + dist x (p j) := dist_triangle_left _ _ _
  rw [Metric.mem_ball] at hi hj
  linarith

/-- Outside the open ball `P(p,s)` the bump of radius `s/3` vanishes near the point. -/
theorem d1eaenergy_bump_eventually_zero {s : ℝ} (hs : 0 < s) (p : Space m) {x : Space m}
    (hx : x ∉ Metric.ball p s) :
    SmoothCutoff.parabolicBump (s / 3) p =ᶠ[𝓝 (x.1, x.2.val)] fun _ => 0 := by
  refine SmoothCutoff.parabolicBump_eventuallyEq_zero (by positivity) fun hmem => hx ?_
  have h := SmoothCutoff.point_mem_ball_of_mem_bumpSupportSet (by positivity : 0 < s / 3) hmem
  rw [show 3 * (s / 3) = s by ring] at h
  exact h

theorem d1eaenergy_bump_eq_zero {s : ℝ} (hs : 0 < s) (p : Space m) {x : Space m}
    (hx : x ∉ Metric.ball p s) : SmoothCutoff.parabolicBump (s / 3) p (x.1, x.2.val) = 0 :=
  (d1eaenergy_bump_eventually_zero hs p hx).eq_of_nhds

/-! ### Bounds for one bump (base bump bounds, direct) -/

theorem d1eaenergy_bump_smul_eq (s : ℝ) (p : Space m) (v : Spatial n) (t : ℝ) :
    (fun w => SmoothCutoff.parabolicBump (s / 3) p (w, t) • v) =
      (ContinuousLinearMap.toSpanSingleton ℝ v) ∘
        fun w => SmoothCutoff.parabolicBump (s / 3) p (w, t) := by
  funext w
  simp [ContinuousLinearMap.toSpanSingleton_apply]

theorem d1eaenergy_bump_contDiff_spatial (s : ℝ) (p : Space m) (t : ℝ) :
    ContDiff ℝ 2 fun w : Spatial m => SmoothCutoff.parabolicBump (s / 3) p (w, t) :=
  (contDiff_infty.1 (SmoothCutoff.contDiff_parabolicBump (s / 3) p) 2).comp
    (contDiff_id.prodMk contDiff_const)

/-- Second spatial derivative of one bump term: `‖D_u² (ψ v)‖ ≤ ‖v‖ B (s/3)^{-2}`. -/
theorem d1eaenergy_bump_spatial_le {s : ℝ} (hs : 0 < s) (p : Space m) (v : Spatial n)
    (u : Spatial m) (t : ℝ) :
    ‖fderiv ℝ (fderiv ℝ fun w => SmoothCutoff.parabolicBump (s / 3) p (w, t) • v) u‖ ≤
      ‖v‖ * (SmoothCutoff.bumpBound m * (s / 3)⁻¹ ^ 2) := by
  have hρ : 0 < s / 3 := by positivity
  rw [d1eaenergy_bump_smul_eq s p v t, ← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  refine ((ContinuousLinearMap.toSpanSingleton ℝ v).norm_iteratedFDeriv_comp_left
    (d1eaenergy_bump_contDiff_spatial s p t).contDiffAt (by norm_num)).trans ?_
  rw [ContinuousLinearMap.norm_toSpanSingleton]
  exact mul_le_mul_of_nonneg_left
    (SmoothCutoff.norm_iteratedFDeriv_parabolicBump_spatial_le hρ p t u (by norm_num))
    (norm_nonneg v)

/-- Time derivative of one bump term: `|∂_t (ψ v)| ≤ B (s/3)^{-2} ‖v‖`. -/
theorem d1eaenergy_bump_time_le {s : ℝ} (hs : 0 < s) (p : Space m) (v : Spatial n)
    (u : Spatial m) (t : ℝ) :
    ‖deriv (fun τ => SmoothCutoff.parabolicBump (s / 3) p (u, τ) • v) t‖ ≤
      SmoothCutoff.bumpBound m / (s / 3) ^ 2 * ‖v‖ := by
  have hρ : 0 < s / 3 := by positivity
  have hdiff : DifferentiableAt ℝ (fun τ => SmoothCutoff.parabolicBump (s / 3) p (u, τ)) t :=
    (((SmoothCutoff.contDiff_parabolicBump (s / 3) p).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) t
  rw [deriv_smul_const hdiff, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (SmoothCutoff.abs_deriv_parabolicBump_time_le hρ p u t)
    (norm_nonneg v)

/-- The arithmetic of the bump bounds: `X ≤ ‖v‖ B (s/3)^{-2}`, `Y ≤ B (s/3)^{-2} ‖v‖` and
`‖v‖ ≤ 2 a s` give `X² + Y² ≤ 648 B² a² / s²`. -/
theorem d1eaenergy_sq_arith {X Y B nv s a : ℝ} (hs : 0 < s) (hB : 0 ≤ B) (hX0 : 0 ≤ X)
    (hY0 : 0 ≤ Y) (hv : nv ≤ 2 * a * s) (hX : X ≤ nv * (B * (s / 3)⁻¹ ^ 2))
    (hY : Y ≤ B / (s / 3) ^ 2 * nv) :
    X ^ 2 + Y ^ 2 ≤ 648 * B ^ 2 * a ^ 2 / s ^ 2 := by
  have e1 : nv * (B * (s / 3)⁻¹ ^ 2) = 9 * B * nv / s ^ 2 := by
    rw [inv_div, div_pow]
    ring
  have e2 : B / (s / 3) ^ 2 * nv = 9 * B * nv / s ^ 2 := by
    rw [div_pow, div_div_eq_mul_div]
    ring
  have hK : 9 * B * nv / s ^ 2 ≤ 18 * B * a / s := by
    rw [div_le_div_iff₀ (by positivity) hs]
    have := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 9 * B * s)
    nlinarith
  have hX' : X ≤ 18 * B * a / s := hX.trans (e1.trans_le hK)
  have hY' : Y ≤ 18 * B * a / s := hY.trans (e2.trans_le hK)
  calc X ^ 2 + Y ^ 2 ≤ (18 * B * a / s) ^ 2 + (18 * B * a / s) ^ 2 :=
        add_le_add (pow_le_pow_left₀ hX0 hX' 2) (pow_le_pow_left₀ hY0 hY' 2)
    _ = 648 * B ^ 2 * a ^ 2 / s ^ 2 := by
        rw [div_pow]
        ring

/-- One bump term `g = ψ v` with `‖v‖ ≤ 2 a s`: `‖D_u² g‖² + |∂_t g|² ≤ 648 B² a² / s²`
(`‖D_u² g‖, |∂_t g| ≤ 18 B a / s`). -/
theorem d1eaenergy_bump_deriv_sq_le {s a : ℝ} (hs : 0 < s) (p : Space m) {v : Spatial n}
    (hv : ‖v‖ ≤ 2 * a * s) (u : Spatial m) (t : ℝ) :
    ‖fderiv ℝ (fderiv ℝ fun w => SmoothCutoff.parabolicBump (s / 3) p (w, t) • v) u‖ ^ 2 +
        ‖deriv (fun τ => SmoothCutoff.parabolicBump (s / 3) p (u, τ) • v) t‖ ^ 2 ≤
      648 * SmoothCutoff.bumpBound m ^ 2 * a ^ 2 / s ^ 2 :=
  d1eaenergy_sq_arith hs (SmoothCutoff.bumpBound_nonneg m) (ContinuousLinearMap.opNorm_nonneg _)
    (norm_nonneg _) hv
    (d1eaenergy_bump_spatial_le hs p v u t) (d1eaenergy_bump_time_le hs p v u t)

/-- **Localization of the derivative energy**: if `H` agrees near `(u,t)` with one bump term
`ψ v₀` (radius `s/3`, `‖v₀‖ ≤ 2 a s`), its energy at `(u,t)` is at most `648 B² a² / s²`. -/
theorem d1eaenergy_energy_of_eventuallyEq {H : Spatial m → ℝ → Spatial n} {s a : ℝ}
    (hs : 0 < s) {p₀ : Space m} {v₀ : Spatial n} (hv : ‖v₀‖ ≤ 2 * a * s) {u : Spatial m}
    {t : ℝ}
    (hev : (fun q : Coordinates m => H q.1 q.2) =ᶠ[𝓝 (u, t)]
      fun q => SmoothCutoff.parabolicBump (s / 3) p₀ q • v₀) :
    ‖fderiv ℝ (fun w' => fderiv ℝ (fun w => H w t) w') u‖ ^ 2 +
        ‖deriv (fun τ => H u τ) t‖ ^ 2 ≤
      648 * SmoothCutoff.bumpBound m ^ 2 * a ^ 2 / s ^ 2 := by
  have hsp : (fun w => H w t) =ᶠ[𝓝 u]
      fun w => SmoothCutoff.parabolicBump (s / 3) p₀ (w, t) • v₀ :=
    hev.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto u)
  have htm : (fun τ => H u τ) =ᶠ[𝓝 t]
      fun τ => SmoothCutoff.parabolicBump (s / 3) p₀ (u, τ) • v₀ :=
    hev.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto t)
  have h1 : fderiv ℝ (fun w' => fderiv ℝ (fun w => H w t) w') u =
      fderiv ℝ (fderiv ℝ fun w => SmoothCutoff.parabolicBump (s / 3) p₀ (w, t) • v₀) u :=
    (hsp.fderiv (𝕜 := ℝ)).fderiv_eq
  rw [h1, htm.deriv_eq]
  exact d1eaenergy_bump_deriv_sq_le hs p₀ hv u t

/-! ### The large-bump sum `H_r` and its localization -/

/-- The finite sum `H(u,t) = ∑_{i ∈ T} ψ_i(u,t) v_i` (ordinary coordinates). -/
def d1eaenergy_finSum (s : I → ℝ) (p : I → Space m) (v : I → Spatial n) (T : Finset I)
    (u : Spatial m) (t : ℝ) : Spatial n :=
  ∑ i ∈ T, SmoothCutoff.parabolicBump (s i / 3) (p i) (u, t) • v i

theorem d1eaenergy_finSum_contDiff (s : I → ℝ) (p : I → Space m) (v : I → Spatial n)
    (T : Finset I) :
    ContDiff ℝ 2 (fun x : Spatial m × ℝ => d1eaenergy_finSum s p v T x.1 x.2) := by
  unfold d1eaenergy_finSum
  refine ContDiff.sum fun i _ => ?_
  exact (contDiff_infty.1 (SmoothCutoff.contDiff_parabolicBump (s i / 3) (p i)) 2).smul
    contDiff_const

theorem d1eaenergy_finSum_continuous (s : I → ℝ) (p : I → Space m) (v : I → Spatial n)
    (T : Finset I) :
    Continuous (fun z : Space m => d1eaenergy_finSum s p v T z.1 z.2.val) := by
  have hcomp : (fun z : Space m => d1eaenergy_finSum s p v T z.1 z.2.val) =
      (fun x : Spatial m × ℝ => d1eaenergy_finSum s p v T x.1 x.2) ∘
        (fun z : Space m => ((z.1, z.2.val) : Spatial m × ℝ)) := rfl
  have hc : Continuous fun z : Space m => ((z.1, z.2.val) : Spatial m × ℝ) :=
    continuous_fst.prodMk continuous_time
  have hH : Continuous (fun x : Spatial m × ℝ => d1eaenergy_finSum s p v T x.1 x.2) :=
    (d1eaenergy_finSum_contDiff s p v T).continuous
  rw [hcomp]
  exact hH.comp hc

/-- Near a point of the ball of `j ∈ T`, only the term `j` of `H` survives. -/
theorem d1eaenergy_finSum_eventuallyEq_single {s : I → ℝ} (hs : ∀ i, 0 < s i)
    (p : I → Space m) (v : I → Spatial n) {T : Finset I} {x : Space m} {j : I} (hjT : j ∈ T)
    (hj : ∀ i ∈ T, i ≠ j → x ∉ Metric.ball (p i) (s i)) :
    (fun q : Coordinates m => d1eaenergy_finSum s p v T q.1 q.2) =ᶠ[𝓝 (x.1, x.2.val)]
      fun q => SmoothCutoff.parabolicBump (s j / 3) (p j) q • v j := by
  classical
  have hev : ∀ᶠ q in 𝓝 (x.1, x.2.val), ∀ i ∈ T.erase j,
      SmoothCutoff.parabolicBump (s i / 3) (p i) q = 0 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact d1eaenergy_bump_eventually_zero (hs i) (p i)
      (hj i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
  filter_upwards [hev] with q hq
  simp only [d1eaenergy_finSum, Prod.mk.eta]
  rw [Finset.sum_eq_single j
    (fun i hi hij => by rw [hq i (Finset.mem_erase.2 ⟨hij, hi⟩), zero_smul])
    (fun h => absurd hjT h)]

/-- Near a point outside every ball of `T`, `H` vanishes. -/
theorem d1eaenergy_finSum_eventuallyEq_zero {s : I → ℝ} (hs : ∀ i, 0 < s i)
    (p : I → Space m) (v : I → Spatial n) {T : Finset I} {x : Space m}
    (hx : ∀ i ∈ T, x ∉ Metric.ball (p i) (s i)) :
    (fun q : Coordinates m => d1eaenergy_finSum s p v T q.1 q.2) =ᶠ[𝓝 (x.1, x.2.val)]
      fun _ => 0 := by
  have hev : ∀ᶠ q in 𝓝 (x.1, x.2.val), ∀ i ∈ T,
      SmoothCutoff.parabolicBump (s i / 3) (p i) q = 0 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact d1eaenergy_bump_eventually_zero (hs i) (p i) (hx i hi)
  filter_upwards [hev] with q hq
  simp only [d1eaenergy_finSum, Prod.mk.eta]
  exact Finset.sum_eq_zero fun i hi => by rw [hq i hi, zero_smul]

/-- **Disjoint supports separate the derivative energy of `H_r`**: pointwise,
`‖D_u² H‖² + |∂_t H|² ≤ 648 B² a² r^{-2} W_r` when `T` is the set of large bumps `r ≤ s i`. -/
theorem d1eaenergy_finSum_energy_le {s : I → ℝ} {p : I → Space m} {v : I → Spatial n} {a : ℝ}
    (hs : ∀ i, 0 < s i) (hv : ∀ i, ‖v i‖ ≤ 2 * a * s i)
    (hdisj : ∀ i j, i ≠ j → s i + s j ≤ dist (p i) (p j)) {r : ℝ} (hr : 0 < r) {T : Finset I}
    (hT : ∀ i, i ∈ T ↔ r ≤ s i) (z : Space m) :
    ENNReal.ofReal
        (‖fderiv ℝ (fun w' => fderiv ℝ (fun w => d1eaenergy_finSum s p v T w z.2.val) w') z.1‖ ^ 2 +
          ‖deriv (fun τ => d1eaenergy_finSum s p v T z.1 τ) z.2.val‖ ^ 2) ≤
      ENNReal.ofReal (648 * SmoothCutoff.bumpBound m ^ 2 * a ^ 2) * (ENNReal.ofReal r)⁻¹ ^ 2 *
        d1eaenergy_weightSum s p r z := by
  by_cases hex : ∃ j ∈ T, z ∈ Metric.ball (p j) (s j)
  · obtain ⟨j, hjT, hzj⟩ := hex
    have hothers : ∀ i ∈ T, i ≠ j → z ∉ Metric.ball (p i) (s i) :=
      fun i _ hij hzi => hij (d1eaenergy_eq_of_mem_ball hdisj hzi hzj)
    have hev := d1eaenergy_finSum_eventuallyEq_single hs p v hjT hothers
    have hrs : r ≤ s j := (hT j).1 hjT
    have hr0 : r ≠ 0 := hr.ne'
    have hs0 : s j ≠ 0 := (hs j).ne'
    calc _ ≤ ENNReal.ofReal (648 * SmoothCutoff.bumpBound m ^ 2 * a ^ 2 / s j ^ 2) :=
          ENNReal.ofReal_le_ofReal (d1eaenergy_energy_of_eventuallyEq (hs j) (hv j) hev)
      _ = ENNReal.ofReal (648 * SmoothCutoff.bumpBound m ^ 2 * a ^ 2) *
            (ENNReal.ofReal r)⁻¹ ^ 2 * ENNReal.ofReal (d1eaenergy_weight (s j) r) := by
          rw [← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_pow (inv_nonneg.2 hr.le),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            d1eaenergy_weight_of_le hr hrs]
          congr 1
          field_simp
      _ ≤ _ := mul_le_mul_right (d1eaenergy_le_weightSum s p r hzj) _
  · simp only [not_exists, not_and] at hex
    have hev0 := d1eaenergy_finSum_eventuallyEq_zero hs p v hex
    have hev : (fun q : Coordinates m => d1eaenergy_finSum s p v T q.1 q.2) =ᶠ[𝓝 (z.1, z.2.val)]
        fun q => SmoothCutoff.parabolicBump ((3 : ℝ) / 3) z q • (0 : Spatial n) :=
      hev0.trans (Filter.Eventually.of_forall fun q => (smul_zero _).symm)
    have h := d1eaenergy_energy_of_eventuallyEq (a := 0) (by norm_num) (by simp) hev
    have h0 : ‖fderiv ℝ (fun w' => fderiv ℝ (fun w => d1eaenergy_finSum s p v T w z.2.val) w')
          z.1‖ ^ 2 + ‖deriv (fun τ => d1eaenergy_finSum s p v T z.1 τ) z.2.val‖ ^ 2 ≤ 0 := by
      simpa using h
    rw [ENNReal.ofReal_eq_zero.2 h0]
    exact zero_le

/-- **The small-bump remainder `J_r = G - H_r`**: pointwise
`|J_r|² ≤ 4 a² r² W_r` (zero fit, one small bump per point). -/
theorem d1eaenergy_rest_le {s : I → ℝ} {p : I → Space m} {v : I → Spatial n} {a : ℝ}
    (hs : ∀ i, 0 < s i) (hv : ∀ i, ‖v i‖ ≤ 2 * a * s i)
    (hdisj : ∀ i j, i ≠ j → s i + s j ≤ dist (p i) (p j)) {r : ℝ} (hr : 0 < r) {T : Finset I}
    (hT : ∀ i, i ∈ T ↔ r ≤ s i) (z : Space m) :
    ‖(∑' i, SmoothCutoff.parabolicBump (s i / 3) (p i) (z.1, z.2.val) • v i) -
        d1eaenergy_finSum s p v T z.1 z.2.val‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * a ^ 2) * ENNReal.ofReal r ^ 2 * d1eaenergy_weightSum s p r z := by
  by_cases hex : ∃ j, z ∈ Metric.ball (p j) (s j)
  · obtain ⟨j, hzj⟩ := hex
    have hzero : ∀ i, i ≠ j → SmoothCutoff.parabolicBump (s i / 3) (p i) (z.1, z.2.val) = 0 :=
      fun i hij => d1eaenergy_bump_eq_zero (hs i) (p i)
        fun hzi => hij (d1eaenergy_eq_of_mem_ball hdisj hzi hzj)
    have hG : (∑' i, SmoothCutoff.parabolicBump (s i / 3) (p i) (z.1, z.2.val) • v i) =
        SmoothCutoff.parabolicBump (s j / 3) (p j) (z.1, z.2.val) • v j :=
      tsum_eq_single j fun i hij => by rw [hzero i hij, zero_smul]
    by_cases hjT : j ∈ T
    · have hH : d1eaenergy_finSum s p v T z.1 z.2.val =
          SmoothCutoff.parabolicBump (s j / 3) (p j) (z.1, z.2.val) • v j :=
        Finset.sum_eq_single j (fun i _ hij => by rw [hzero i hij, zero_smul])
          (fun h => absurd hjT h)
      rw [hG, hH, sub_self]
      simp
    · have hH : d1eaenergy_finSum s p v T z.1 z.2.val = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [hzero i (fun h => hjT (h ▸ hi)), zero_smul]
      rw [hG, hH, sub_zero]
      have hsr : s j < r := lt_of_not_ge fun h => hjT ((hT j).2 h)
      have hnorm : ‖SmoothCutoff.parabolicBump (s j / 3) (p j) (z.1, z.2.val) • v j‖ ≤
          2 * a * s j := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (SmoothCutoff.parabolicBump_nonneg _ _ _)]
        calc _ ≤ 1 * ‖v j‖ := mul_le_mul_of_nonneg_right
              (SmoothCutoff.parabolicBump_le_one _ _ _) (norm_nonneg _)
          _ ≤ 2 * a * s j := by rw [one_mul]; exact hv j
      calc ‖SmoothCutoff.parabolicBump (s j / 3) (p j) (z.1, z.2.val) • v j‖ₑ ^ 2
          = ENNReal.ofReal (‖SmoothCutoff.parabolicBump (s j / 3) (p j) (z.1, z.2.val) • v j‖ ^ 2) := by
            rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        _ ≤ ENNReal.ofReal ((2 * a * s j) ^ 2) :=
            ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
        _ = ENNReal.ofReal (4 * a ^ 2) * ENNReal.ofReal r ^ 2 *
              ENNReal.ofReal (d1eaenergy_weight (s j) r) := by
            rw [← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity), d1eaenergy_weight_of_lt (hs j) hsr]
            congr 1
            field_simp
            ring
        _ ≤ _ := mul_le_mul_right (d1eaenergy_le_weightSum s p r hzj) _
  · simp only [not_exists] at hex
    have hG : (∑' i, SmoothCutoff.parabolicBump (s i / 3) (p i) (z.1, z.2.val) • v i) = 0 := by
      refine (tsum_congr fun i => ?_).trans tsum_zero
      rw [d1eaenergy_bump_eq_zero (hs i) (p i) (hex i), zero_smul]
    have hH : d1eaenergy_finSum s p v T z.1 z.2.val = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [d1eaenergy_bump_eq_zero (hs i) (p i) (hex i), zero_smul]
    rw [hG, hH, sub_zero]
    simp

/-! ### Two-term subadditivity and the zero fit -/

theorem d1eaenergy_enorm_add_sq_le (x y : Spatial n) :
    ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  calc ‖x + y‖ₑ ^ 2 = ENNReal.ofReal (‖x + y‖ ^ 2) := by
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (‖x‖ - ‖y‖)])
    _ = 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (norm_nonneg _),
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ofReal_norm, ENNReal.ofReal_ofNat]

/-- **Two-term subadditivity of the affine error**: `a_{f+g}² ≤ 2 a_f² + 2 a_g²`. Only `f` needs
to be continuous (it makes the first integrand measurable); `g` is arbitrary. -/
theorem d1eaenergy_affineErrorSq_add_le {f g : Space m → Spatial n} (hf : Continuous f)
    (y : Space m) (r : ℝ) :
    affineErrorSq (parabolicVolume m) (f + g) y r ≤
      2 * affineErrorSq (parabolicVolume m) f y r + 2 * affineErrorSq (parabolicVolume m) g y r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [affineErrorSq_of_nonpos _ _ _ hr]
  rw [affineErrorSq_of_pos _ _ _ hr, affineErrorSq_of_pos _ _ _ hr, affineErrorSq_of_pos _ _ _ hr]
  have key : (⨅ (a : Spatial n) (B : Spatial m →L[ℝ] Spatial n),
        affineFitIntegral (parabolicVolume m) (f + g) a B y r) ≤
      (⨅ (a : Spatial n) (B : Spatial m →L[ℝ] Spatial n),
          2 * affineFitIntegral (parabolicVolume m) f a B y r) +
        ⨅ (a : Spatial n) (B : Spatial m →L[ℝ] Spatial n),
          2 * affineFitIntegral (parabolicVolume m) g a B y r := by
    refine ENNReal.le_iInf₂_add_iInf₂ fun a₁ B₁ a₂ B₂ => ?_
    refine (iInf₂_le (a₁ + a₂) (B₁ + B₂)).trans ?_
    unfold affineFitIntegral
    have hmeas : AEMeasurable (fun q : Space m => 2 * ‖f q - (a₁ + B₁ q.1)‖ₑ ^ 2)
        ((parabolicVolume m).restrict (Metric.ball y r)) :=
      (((hf.sub (continuous_const.add (B₁.continuous.comp continuous_fst))).enorm.measurable.pow_const
        2).const_mul 2).aemeasurable
    calc ∫⁻ q in Metric.ball y r, ‖(f + g) q - (a₁ + a₂ + (B₁ + B₂) q.1)‖ₑ ^ 2 ∂parabolicVolume m
        ≤ ∫⁻ q in Metric.ball y r, (2 * ‖f q - (a₁ + B₁ q.1)‖ₑ ^ 2 +
            2 * ‖g q - (a₂ + B₂ q.1)‖ₑ ^ 2) ∂parabolicVolume m := by
          refine lintegral_mono fun q => ?_
          have hsplit : (f + g) q - (a₁ + a₂ + (B₁ + B₂) q.1) =
              (f q - (a₁ + B₁ q.1)) + (g q - (a₂ + B₂ q.1)) := by
            simp only [Pi.add_apply, add_apply]
            abel
          rw [hsplit]
          exact d1eaenergy_enorm_add_sq_le _ _
      _ = 2 * ∫⁻ q in Metric.ball y r, ‖f q - (a₁ + B₁ q.1)‖ₑ ^ 2 ∂parabolicVolume m +
            2 * ∫⁻ q in Metric.ball y r, ‖g q - (a₂ + B₂ q.1)‖ₑ ^ 2 ∂parabolicVolume m := by
          rw [lintegral_add_left' hmeas, lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ (by norm_num)]
  have h2 : ∀ F : Space m → Spatial n,
      (⨅ (a : Spatial n) (B : Spatial m →L[ℝ] Spatial n),
          2 * affineFitIntegral (parabolicVolume m) F a B y r) =
        2 * ⨅ (a : Spatial n) (B : Spatial m →L[ℝ] Spatial n),
          affineFitIntegral (parabolicVolume m) F a B y r := by
    intro F
    rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
    refine iInf_congr fun a => ?_
    rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  rw [h2, h2] at key
  calc _ ≤ (ENNReal.ofReal r)⁻¹ ^ (baseDimension (Spatial m) + 2) *
        (2 * (⨅ (a : Spatial n) (B : Spatial m →L[ℝ] Spatial n),
            affineFitIntegral (parabolicVolume m) f a B y r) +
          2 * ⨅ (a : Spatial n) (B : Spatial m →L[ℝ] Spatial n),
            affineFitIntegral (parabolicVolume m) g a B y r) := mul_le_mul_right key _
    _ = _ := by ring

/-- **The zero fit**: `a_g(y,r)² ≤ r^{-(m+4)} ∫_{P(y,r)} |g|²`. -/
theorem d1eaenergy_affineErrorSq_le_zero_fit (g : Space m → Spatial n) (y : Space m) {r : ℝ}
    (hr : 0 < r) :
    affineErrorSq (parabolicVolume m) g y r ≤
      (ENNReal.ofReal r)⁻¹ ^ (m + 4) *
        ∫⁻ q in Metric.ball y r, ‖g q‖ₑ ^ 2 ∂parabolicVolume m := by
  refine (affineErrorSq_le_fitIntegral _ g y hr 0 0).trans (le_of_eq ?_)
  rw [CutoffCarleson.baseDimension_spatial_eq]
  simp [affineFitIntegral]

/-- The ENNReal bookkeeping of the support-weighted estimate. -/
theorem d1eaenergy_combine {C : ℝ} (hC : 0 ≤ C) (B a : ℝ) {r : ℝ} (hr : 0 < r) (m : ℕ)
    (X : ℝ≥0∞) :
    2 * (ENNReal.ofReal C * (ENNReal.ofReal r)⁻¹ ^ m *
        (ENNReal.ofReal (648 * B ^ 2 * a ^ 2) * (ENNReal.ofReal r)⁻¹ ^ 2 * X)) +
      2 * ((ENNReal.ofReal r)⁻¹ ^ (m + 4) *
        (ENNReal.ofReal (4 * a ^ 2) * ENNReal.ofReal r ^ 2 * X)) =
      ENNReal.ofReal ((1296 * C * B ^ 2 + 8) * a ^ 2) * (ENNReal.ofReal r)⁻¹ ^ (m + 2) * X := by
  have hne : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  have h1 : (ENNReal.ofReal r)⁻¹ ^ m * (ENNReal.ofReal r)⁻¹ ^ 2 =
      (ENNReal.ofReal r)⁻¹ ^ (m + 2) := (pow_add _ _ _).symm
  have h2 : (ENNReal.ofReal r)⁻¹ ^ (m + 4) * ENNReal.ofReal r ^ 2 =
      (ENNReal.ofReal r)⁻¹ ^ (m + 2) := by
    rw [show m + 4 = (m + 2) + 2 by ring, pow_add, mul_assoc, ← mul_pow,
      ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_pow, mul_one]
  have h3 : 2 * (ENNReal.ofReal C * ENNReal.ofReal (648 * B ^ 2 * a ^ 2)) +
      2 * ENNReal.ofReal (4 * a ^ 2) = ENNReal.ofReal ((1296 * C * B ^ 2 + 8) * a ^ 2) := by
    rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (mul_nonneg hC (by positivity)))
        (by positivity)]
    congr 1
    ring
  calc _ = (2 * (ENNReal.ofReal C * ENNReal.ofReal (648 * B ^ 2 * a ^ 2)) *
          ((ENNReal.ofReal r)⁻¹ ^ m * (ENNReal.ofReal r)⁻¹ ^ 2) +
        2 * ENNReal.ofReal (4 * a ^ 2) *
          ((ENNReal.ofReal r)⁻¹ ^ (m + 4) * ENNReal.ofReal r ^ 2)) * X := by ring
    _ = _ := by rw [h1, h2, ← h3]; ring

/-! ### The support-weighted estimate -/

/-- **Part (a): the support-weighted estimate.** For a separated family
of bumps and a testing radius `r > 0` with finitely many large bumps (`r ≤ s i`), given the
Poincaré inequality with constant `C_P` on the base `Space m`,

`a_G(y,r)² ≤ (1296 C_P B² + 8) a² r^{-(m+2)} ∫_{P(y,r)} W_r`,

`W_r = ∑_i 1_{P(p_i,s_i)} min(r/s_i, s_i/r)²`, `B = bumpBound m`. Poincaré is applied once to the
finite sum `H_r` of the large bumps; the small bumps `J_r = G - H_r` take the zero fit. -/
theorem d1eaenergy_supportWeighted {C_P : ℝ} (hCP : 0 ≤ C_P)
    (hP : ∀ (d : ℕ) (H : Spatial m → ℝ → Spatial d),
      ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2) →
      ∀ (p : Space m) (r : ℝ), 0 < r →
        affineErrorSq (parabolicVolume m) (fun z : Space m => H z.1 z.2.val) p r ≤
          ENNReal.ofReal C_P * (ENNReal.ofReal r)⁻¹ ^ m *
            ∫⁻ z in Metric.ball p r,
              ENNReal.ofReal (‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w z.2.val) v) z.1‖ ^ 2 +
                ‖deriv (fun s => H z.1 s) z.2.val‖ ^ 2) ∂parabolicVolume m)
    {s : I → ℝ} {p : I → Space m} {v : I → Spatial n} {a : ℝ}
    (hs : ∀ i, 0 < s i) (hv : ∀ i, ‖v i‖ ≤ 2 * a * s i)
    (hdisj : ∀ i j, i ≠ j → s i + s j ≤ dist (p i) (p j))
    (y : Space m) {r : ℝ} (hr : 0 < r) (hfin : {i | r ≤ s i}.Finite) :
    affineErrorSq (parabolicVolume m)
        (fun x : Space m => ∑' i, SmoothCutoff.parabolicBump (s i / 3) (p i) (x.1, x.2.val) • v i)
        y r ≤
      ENNReal.ofReal ((1296 * C_P * SmoothCutoff.bumpBound m ^ 2 + 8) * a ^ 2) *
        (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
          ∫⁻ x in Metric.ball y r, d1eaenergy_weightSum s p r x ∂parabolicVolume m := by
  set T := hfin.toFinset with hTdef
  have hT : ∀ i, i ∈ T ↔ r ≤ s i := fun i => by
    rw [hTdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  set G : Space m → Spatial n :=
    fun x => ∑' i, SmoothCutoff.parabolicBump (s i / 3) (p i) (x.1, x.2.val) • v i with hGdef
  set Hb : Space m → Spatial n := fun z => d1eaenergy_finSum s p v T z.1 z.2.val with hHbdef
  have hsplit : G = Hb + (G - Hb) := by
    funext z
    simp only [Pi.add_apply, Pi.sub_apply, add_sub_cancel]
  have hHbound : affineErrorSq (parabolicVolume m) Hb y r ≤
      ENNReal.ofReal C_P * (ENNReal.ofReal r)⁻¹ ^ m *
        (ENNReal.ofReal (648 * SmoothCutoff.bumpBound m ^ 2 * a ^ 2) * (ENNReal.ofReal r)⁻¹ ^ 2 *
          ∫⁻ x in Metric.ball y r, d1eaenergy_weightSum s p r x ∂parabolicVolume m) := by
    refine (hP n (d1eaenergy_finSum s p v T) (d1eaenergy_finSum_contDiff s p v T) y r hr).trans ?_
    refine mul_le_mul_right ?_ _
    rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hr).ne')))]
    exact lintegral_mono fun z => d1eaenergy_finSum_energy_le hs hv hdisj hr hT z
  have hJbound : affineErrorSq (parabolicVolume m) (G - Hb) y r ≤
      (ENNReal.ofReal r)⁻¹ ^ (m + 4) *
        (ENNReal.ofReal (4 * a ^ 2) * ENNReal.ofReal r ^ 2 *
          ∫⁻ x in Metric.ball y r, d1eaenergy_weightSum s p r x ∂parabolicVolume m) := by
    refine (d1eaenergy_affineErrorSq_le_zero_fit (G - Hb) y hr).trans ?_
    refine mul_le_mul_right ?_ _
    rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
    exact lintegral_mono fun z => d1eaenergy_rest_le hs hv hdisj hr hT z
  calc affineErrorSq (parabolicVolume m) G y r
      = affineErrorSq (parabolicVolume m) (Hb + (G - Hb)) y r := by rw [← hsplit]
    _ ≤ 2 * affineErrorSq (parabolicVolume m) Hb y r +
          2 * affineErrorSq (parabolicVolume m) (G - Hb) y r :=
        d1eaenergy_affineErrorSq_add_le (d1eaenergy_finSum_continuous s p v T) y r
    _ ≤ _ := add_le_add (mul_le_mul_right hHbound 2) (mul_le_mul_right hJbound 2)
    _ = _ := d1eaenergy_combine hCP _ a hr m _

end SupportWeighted

/-! ## Part (b): integration of the support-weighted estimate -/

section Integration

variable {m n : ℕ} {I : Type*}

theorem d1eaenergy_measurable_weight (s : ℝ) :
    Measurable fun r : ℝ => ENNReal.ofReal (d1eaenergy_weight s r) := by
  unfold d1eaenergy_weight
  exact (((measurable_id.div_const s).min (measurable_const.div measurable_id)).pow_const
    2).ennreal_ofReal

/-- The support-weighted sum is jointly measurable in `(r, x)` for a countable family. -/
theorem d1eaenergy_measurable_weightSum [Countable I] (s : I → ℝ) (p : I → Space m) :
    Measurable (fun q : ℝ × Space m => d1eaenergy_weightSum s p q.1 q.2) := by
  unfold d1eaenergy_weightSum
  refine Measurable.tsum fun i => ?_
  have h : (fun q : ℝ × Space m => (Metric.ball (p i) (s i)).indicator
        (fun _ => ENNReal.ofReal (d1eaenergy_weight (s i) q.1)) q.2) =
      (Prod.snd ⁻¹' Metric.ball (p i) (s i)).indicator
        (fun q : ℝ × Space m => ENNReal.ofReal (d1eaenergy_weight (s i) q.1)) := by
    funext q
    by_cases hq : q.2 ∈ Metric.ball (p i) (s i)
    · rw [Set.indicator_of_mem hq,
        Set.indicator_of_mem (show q ∈ Prod.snd ⁻¹' Metric.ball (p i) (s i) from hq)]
    · rw [Set.indicator_of_notMem hq,
        Set.indicator_of_notMem (show q ∉ Prod.snd ⁻¹' Metric.ball (p i) (s i) from hq)]
  rw [h]
  exact ((d1eaenergy_measurable_weight (s i)).comp measurable_fst).indicator
    (Metric.isOpen_ball.measurableSet.preimage measurable_snd)

/-- At a point of the ball of `j` the weighted sum is the single weight of `j`. -/
theorem d1eaenergy_weightSum_eq_single {s : I → ℝ} {p : I → Space m}
    (hdisj : ∀ i j, i ≠ j → s i + s j ≤ dist (p i) (p j)) {x : Space m} {j : I}
    (hj : x ∈ Metric.ball (p j) (s j)) (r : ℝ) :
    d1eaenergy_weightSum s p r x = ENNReal.ofReal (d1eaenergy_weight (s j) r) := by
  unfold d1eaenergy_weightSum
  rw [tsum_eq_single j fun i hij => Set.indicator_of_notMem
    (fun hi => hij (d1eaenergy_eq_of_mem_ball hdisj hi hj)) _]
  exact Set.indicator_of_mem hj _

theorem d1eaenergy_weightSum_eq_zero {s : I → ℝ} {p : I → Space m} {x : Space m}
    (hx : ∀ i, x ∉ Metric.ball (p i) (s i)) (r : ℝ) : d1eaenergy_weightSum s p r x = 0 := by
  unfold d1eaenergy_weightSum
  exact (tsum_congr fun i => Set.indicator_of_notMem (hx i) _).trans tsum_zero

/-- **The scale integral of one bracket**:
`∫_{(0,R)} min(r/s, s/r)² dr/r ≤ ∫_0^s (r/s) dr/r + ∫_s^∞ (s/r)² dr/r ≤ 2`, for every `R`
(this covers `s ≫ R` without charging the whole bump to a small root). -/
theorem d1eaenergy_lintegral_weight_le {s : ℝ} (hs : 0 < s) (R : ℝ) :
    ∫⁻ r in Ioo 0 R, ENNReal.ofReal (d1eaenergy_weight s r) ∂scaleMeasure ≤ 2 := by
  have h1 : ∫⁻ r in Ioc 0 s, ENNReal.ofReal (d1eaenergy_weight s r) ∂scaleMeasure ≤ 1 := by
    refine (setLIntegral_mono' measurableSet_Ioc fun r hr => ?_).trans_eq
      (CutoffCarleson.lintegral_Ioc_div_scaleMeasure hs)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [d1eaenergy_weight_of_le hr.1 hr.2]
    have hx0 : 0 ≤ r / s := div_nonneg hr.1.le hs.le
    have hx1 : r / s ≤ 1 := (div_le_one hs).2 hr.2
    nlinarith
  have h2 : ∫⁻ r in Ioi s, ENNReal.ofReal (d1eaenergy_weight s r) ∂scaleMeasure ≤ 1 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi
      (g := fun r => ENNReal.ofReal (s ^ 2) * (ENNReal.ofReal r)⁻¹ ^ 2) fun r hr => by
        have hr0 : 0 < r := hs.trans hr
        show ENNReal.ofReal (d1eaenergy_weight s r) =
          ENNReal.ofReal (s ^ 2) * (ENNReal.ofReal r)⁻¹ ^ 2
        rw [d1eaenergy_weight_of_lt hs hr, ← ENNReal.ofReal_inv_of_pos hr0,
          ← ENNReal.ofReal_pow (inv_nonneg.2 hr0.le), ← ENNReal.ofReal_mul (sq_nonneg s)]
        congr 1
        ring]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_inv_pow_Ioi_scaleMeasure 2 two_pos hs, ← ENNReal.ofReal_mul (sq_nonneg s)]
    refine ENNReal.ofReal_le_one.2 ?_
    have hs2 : s ^ 2 ≠ 0 := by positivity
    push_cast
    rw [mul_div_assoc', mul_inv_cancel₀ hs2]
    norm_num
  calc ∫⁻ r in Ioo 0 R, ENNReal.ofReal (d1eaenergy_weight s r) ∂scaleMeasure
      ≤ ∫⁻ r in Ioc 0 s ∪ Ioi s, ENNReal.ofReal (d1eaenergy_weight s r) ∂scaleMeasure := by
        refine lintegral_mono_set ?_
        rw [Set.Ioc_union_Ioi_eq_Ioi hs.le]
        exact Ioo_subset_Ioi_self
    _ ≤ ∫⁻ r in Ioc 0 s, ENNReal.ofReal (d1eaenergy_weight s r) ∂scaleMeasure +
          ∫⁻ r in Ioi s, ENNReal.ofReal (d1eaenergy_weight s r) ∂scaleMeasure :=
        lintegral_union_le _ _ _
    _ ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

/-- At most one support meets each point, so the scale integral of `W_r(x)` is at most `2`. -/
theorem d1eaenergy_lintegral_weightSum_le {s : I → ℝ} {p : I → Space m} (hs : ∀ i, 0 < s i)
    (hdisj : ∀ i j, i ≠ j → s i + s j ≤ dist (p i) (p j)) (x : Space m) (R : ℝ) :
    ∫⁻ r in Ioo 0 R, d1eaenergy_weightSum s p r x ∂scaleMeasure ≤ 2 := by
  by_cases hex : ∃ j, x ∈ Metric.ball (p j) (s j)
  · obtain ⟨j, hj⟩ := hex
    rw [lintegral_congr fun r => d1eaenergy_weightSum_eq_single hdisj hj r]
    exact d1eaenergy_lintegral_weight_le (hs j) R
  · simp only [not_exists] at hex
    rw [lintegral_congr fun r => d1eaenergy_weightSum_eq_zero hex r, lintegral_zero]
    exact zero_le

/-- Joint measurability of the Tonelli kernel
`(y, r, x) ↦ r^{-(m+2)} 1_{P(y,r)}(x) Φ(r,x)`. -/
theorem d1eaenergy_measurable_kernel {Φ : ℝ × Space m → ℝ≥0∞} (hΦ : Measurable Φ)
    {β : Type*} [MeasurableSpace β] {Y X : β → Space m} {Q : β → ℝ} (hY : Measurable Y)
    (hQ : Measurable Q) (hX : Measurable X) :
    Measurable fun b => (ENNReal.ofReal (Q b))⁻¹ ^ (m + 2) *
      (Metric.ball (Y b) (Q b)).indicator (fun x => Φ (Q b, x)) (X b) := by
  have hset : MeasurableSet {b | dist (X b) (Y b) < Q b} := measurableSet_lt (hX.dist hY) hQ
  have heq : (fun b => (Metric.ball (Y b) (Q b)).indicator (fun x => Φ (Q b, x)) (X b)) =
      {b | dist (X b) (Y b) < Q b}.indicator (fun b => Φ (Q b, X b)) := by
    funext b
    by_cases hb : dist (X b) (Y b) < Q b
    · rw [Set.indicator_of_mem (show X b ∈ Metric.ball (Y b) (Q b) from hb),
        Set.indicator_of_mem (show b ∈ {b | dist (X b) (Y b) < Q b} from hb)]
    · rw [Set.indicator_of_notMem (show X b ∉ Metric.ball (Y b) (Q b) from hb),
        Set.indicator_of_notMem (show b ∉ {b | dist (X b) (Y b) < Q b} from hb)]
  have h2 : Measurable fun b =>
      (Metric.ball (Y b) (Q b)).indicator (fun x => Φ (Q b, x)) (X b) := by
    rw [heq]
    exact (hΦ.comp (hQ.prodMk hX)).indicator hset
  exact ((measurable_inv_pow_ofReal (m + 2)).comp hQ).mul h2

/-- The inner Tonelli bound: for `0 < r < R`, integrating the kernel over `y ∈ P(z,R)` gives at
most `2 ω_m 1_{P(z,2R)}(x) Φ(r,x)` (`r^{-(m+2)} |P(x,r)| = 2 ω_m`). -/
theorem d1eaenergy_kernel_y_le (Φ : ℝ × Space m → ℝ≥0∞) (z x : Space m) {R r : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    ∫⁻ y in Metric.ball z R, (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
        (Metric.ball y r).indicator (fun x => Φ (r, x)) x ∂parabolicVolume m ≤
      (Metric.ball z (2 * R)).indicator (fun x => 2 * omega m * Φ (r, x)) x := by
  have hpt : ∀ y, (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
      (Metric.ball y r).indicator (fun x => Φ (r, x)) x =
      (Metric.ball x r).indicator (fun _ => (ENNReal.ofReal r)⁻¹ ^ (m + 2) * Φ (r, x)) y := by
    intro y
    by_cases hxy : dist x y < r
    · rw [Set.indicator_of_mem (show x ∈ Metric.ball y r from hxy),
        Set.indicator_of_mem (show y ∈ Metric.ball x r by rw [Metric.mem_ball, dist_comm]; exact hxy)]
    · rw [Set.indicator_of_notMem (show x ∉ Metric.ball y r from hxy),
        Set.indicator_of_notMem (show y ∉ Metric.ball x r by
          rw [Metric.mem_ball, dist_comm]; exact hxy), mul_zero]
  by_cases hx : x ∈ Metric.ball z (2 * R)
  · rw [Set.indicator_of_mem hx]
    calc ∫⁻ y in Metric.ball z R, (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
          (Metric.ball y r).indicator (fun x => Φ (r, x)) x ∂parabolicVolume m
        ≤ ∫⁻ y, (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
          (Metric.ball y r).indicator (fun x => Φ (r, x)) x ∂parabolicVolume m :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ y, (Metric.ball x r).indicator
            (fun _ => (ENNReal.ofReal r)⁻¹ ^ (m + 2) * Φ (r, x)) y ∂parabolicVolume m :=
          lintegral_congr hpt
      _ = (ENNReal.ofReal r)⁻¹ ^ (m + 2) * Φ (r, x) * parabolicVolume m (Metric.ball x r) := by
          rw [lintegral_indicator Metric.isOpen_ball.measurableSet, setLIntegral_const]
      _ = 2 * omega m * Φ (r, x) := by
          have hne : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
          rw [parabolicVolume_ball x r hr]
          calc (ENNReal.ofReal r)⁻¹ ^ (m + 2) * Φ (r, x) *
                (2 * omega m * ENNReal.ofReal r ^ (m + 2))
              = 2 * omega m * Φ (r, x) *
                  ((ENNReal.ofReal r)⁻¹ ^ (m + 2) * ENNReal.ofReal r ^ (m + 2)) := by ring
            _ = 2 * omega m * Φ (r, x) := by
                rw [← mul_pow, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_pow,
                  mul_one]
  · rw [Set.indicator_of_notMem hx]
    have h0 : ∀ y ∈ Metric.ball z R, (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
        (Metric.ball y r).indicator (fun x => Φ (r, x)) x = 0 := by
      intro y hy
      rw [Set.indicator_of_notMem, mul_zero]
      intro hxy
      apply hx
      rw [Metric.mem_ball] at hxy hy ⊢
      have := dist_triangle x y z
      linarith
    rw [setLIntegral_congr_fun Metric.isOpen_ball.measurableSet h0]
    exact (lintegral_zero).le

/-- **Tonelli for the support-weighted bound**:
`∫_{P(z,R)} ∫_0^R r^{-(m+2)} ∫_{P(y,r)} Φ(r,x) dx dr/r dy ≤ 2 ω_m ∫_{P(z,2R)} ∫_0^R Φ(r,x) dr/r dx`
for a measurable `Φ ≥ 0`. -/
theorem d1eaenergy_tonelli (Φ : ℝ × Space m → ℝ≥0∞) (hΦ : Measurable Φ) (z : Space m) (R : ℝ) :
    ∫⁻ y in Metric.ball z R, ∫⁻ r in Ioo 0 R, (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
        ∫⁻ x in Metric.ball y r, Φ (r, x) ∂parabolicVolume m ∂scaleMeasure ∂parabolicVolume m ≤
      2 * omega m * ∫⁻ x in Metric.ball z (2 * R), ∫⁻ r in Ioo 0 R, Φ (r, x) ∂scaleMeasure
        ∂parabolicVolume m := by
  have e1 : ∀ (y : Space m) (r : ℝ), (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
      ∫⁻ x in Metric.ball y r, Φ (r, x) ∂parabolicVolume m =
      ∫⁻ x, (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
        (Metric.ball y r).indicator (fun x => Φ (r, x)) x ∂parabolicVolume m := by
    intro y r
    have hm : Measurable fun x => (Metric.ball y r).indicator (fun x => Φ (r, x)) x :=
      (hΦ.comp measurable_prodMk_left).indicator Metric.isOpen_ball.measurableSet
    rw [← lintegral_indicator Metric.isOpen_ball.measurableSet, ← lintegral_const_mul _ hm]
  calc ∫⁻ y in Metric.ball z R, ∫⁻ r in Ioo 0 R, (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
          ∫⁻ x in Metric.ball y r, Φ (r, x) ∂parabolicVolume m ∂scaleMeasure ∂parabolicVolume m
      = ∫⁻ y in Metric.ball z R, ∫⁻ r in Ioo 0 R, ∫⁻ x, (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
          (Metric.ball y r).indicator (fun x => Φ (r, x)) x
            ∂parabolicVolume m ∂scaleMeasure ∂parabolicVolume m := by
        refine lintegral_congr fun y => lintegral_congr fun r => e1 y r
    _ = ∫⁻ y in Metric.ball z R, ∫⁻ x, ∫⁻ r in Ioo 0 R, (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
          (Metric.ball y r).indicator (fun x => Φ (r, x)) x
            ∂scaleMeasure ∂parabolicVolume m ∂parabolicVolume m := by
        refine lintegral_congr fun y => lintegral_lintegral_swap ?_
        exact (d1eaenergy_measurable_kernel hΦ (Y := fun _ : ℝ × Space m => y) (Q := Prod.fst)
          (X := Prod.snd) measurable_const measurable_fst measurable_snd).aemeasurable
    _ = ∫⁻ x, ∫⁻ y in Metric.ball z R, ∫⁻ r in Ioo 0 R, (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
          (Metric.ball y r).indicator (fun x => Φ (r, x)) x
            ∂scaleMeasure ∂parabolicVolume m ∂parabolicVolume m := by
        refine lintegral_lintegral_swap ?_
        exact (Measurable.lintegral_prod_right' (d1eaenergy_measurable_kernel hΦ
          (Y := fun b : (Space m × Space m) × ℝ => b.1.1) (Q := fun b => b.2)
          (X := fun b => b.1.2) (measurable_fst.comp measurable_fst) measurable_snd
          (measurable_snd.comp measurable_fst))).aemeasurable
    _ = ∫⁻ x, ∫⁻ r in Ioo 0 R, ∫⁻ y in Metric.ball z R, (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
          (Metric.ball y r).indicator (fun x => Φ (r, x)) x
            ∂parabolicVolume m ∂scaleMeasure ∂parabolicVolume m := by
        refine lintegral_congr fun x => lintegral_lintegral_swap ?_
        exact (d1eaenergy_measurable_kernel hΦ (Y := fun b : Space m × ℝ => b.1)
          (Q := Prod.snd) (X := fun _ => x) measurable_fst measurable_snd
          measurable_const).aemeasurable
    _ ≤ ∫⁻ x, (Metric.ball z (2 * R)).indicator
          (fun x => 2 * omega m * ∫⁻ r in Ioo 0 R, Φ (r, x) ∂scaleMeasure) x
            ∂parabolicVolume m := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Metric.ball z (2 * R)
        · rw [Set.indicator_of_mem hx, ← lintegral_const_mul' _ _
            (TraceExtension.two_mul_omega_ne_top m)]
          refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
          exact (d1eaenergy_kernel_y_le Φ z x hr.1 hr.2).trans_eq (Set.indicator_of_mem hx _)
        · rw [Set.indicator_of_notMem hx]
          calc _ ≤ ∫⁻ r in Ioo 0 R, (0 : ℝ≥0∞) ∂scaleMeasure :=
                setLIntegral_mono' measurableSet_Ioo fun r hr =>
                  (d1eaenergy_kernel_y_le Φ z x hr.1 hr.2).trans_eq
                    (Set.indicator_of_notMem hx _)
            _ = 0 := lintegral_zero
    _ = 2 * omega m * ∫⁻ x in Metric.ball z (2 * R), ∫⁻ r in Ioo 0 R, Φ (r, x) ∂scaleMeasure
          ∂parabolicVolume m := by
        rw [lintegral_indicator Metric.isOpen_ball.measurableSet,
          lintegral_const_mul' _ _ (TraceExtension.two_mul_omega_ne_top m)]

/-- The constant of the attachment energy: `C(m, C_P) = (1296 C_P B² + 8) · 2 (2ω_m)² 2^{m+2}`. -/
def d1eaenergy_const (m : ℕ) (C_P : ℝ) : ℝ :=
  (1296 * C_P * SmoothCutoff.bumpBound m ^ 2 + 8) *
    (2 * (2 * omega m).toReal ^ 2 * 2 ^ (m + 2))

theorem d1eaenergy_const_nonneg (m : ℕ) {C_P : ℝ} (hCP : 0 ≤ C_P) :
    0 ≤ d1eaenergy_const m C_P := by
  unfold d1eaenergy_const
  have := SmoothCutoff.bumpBound_nonneg m
  have h1 : 0 ≤ 1296 * C_P * SmoothCutoff.bumpBound m ^ 2 + 8 := by positivity
  exact mul_nonneg h1 (by positivity)

/-- **The abstract attachment energy**: a separated family of bumps with
`‖v_i‖ ≤ 2 a s_i` and finitely many radii above each positive level has affine Carleson
constant `C(m, C_P) a²` on `Space m`, for every centre and radius (no restriction on the size of
the bumps relative to the testing root). -/
theorem d1eaenergy_carleson {C_P : ℝ} (hCP : 0 ≤ C_P)
    (hP : ∀ (d : ℕ) (H : Spatial m → ℝ → Spatial d),
      ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2) →
      ∀ (p : Space m) (r : ℝ), 0 < r →
        affineErrorSq (parabolicVolume m) (fun z : Space m => H z.1 z.2.val) p r ≤
          ENNReal.ofReal C_P * (ENNReal.ofReal r)⁻¹ ^ m *
            ∫⁻ z in Metric.ball p r,
              ENNReal.ofReal (‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w z.2.val) v) z.1‖ ^ 2 +
                ‖deriv (fun s => H z.1 s) z.2.val‖ ^ 2) ∂parabolicVolume m)
    {s : I → ℝ} {p : I → Space m} {v : I → Spatial n} {a : ℝ}
    (hs : ∀ i, 0 < s i) (hv : ∀ i, ‖v i‖ ≤ 2 * a * s i)
    (hdisj : ∀ i j, i ≠ j → s i + s j ≤ dist (p i) (p j))
    (hfin : ∀ r : ℝ, 0 < r → {i | r ≤ s i}.Finite) :
    HasAffineCarlesonBound (parabolicVolume m)
      (fun x : Space m => ∑' i, SmoothCutoff.parabolicBump (s i / 3) (p i) (x.1, x.2.val) • v i)
      (d1eaenergy_const m C_P * a ^ 2) := by
  have hcount : Countable I := by
    have hcov : (Set.univ : Set I) ⊆ ⋃ k : ℕ, {i | 1 / ((k : ℝ) + 1) ≤ s i} := fun i _ => by
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (hs i)
      exact Set.mem_iUnion.2 ⟨k, hk.le⟩
    exact Set.countable_univ_iff.1
      ((Set.countable_iUnion fun k => (hfin _ (by positivity)).countable).mono hcov)
  set K : ℝ := (1296 * C_P * SmoothCutoff.bumpBound m ^ 2 + 8) * a ^ 2 with hKdef
  have hK0 : 0 ≤ K := by
    have := SmoothCutoff.bumpBound_nonneg m
    have h1 : 0 ≤ 1296 * C_P * SmoothCutoff.bumpBound m ^ 2 + 8 := by positivity
    exact mul_nonneg h1 (sq_nonneg a)
  refine ⟨mul_nonneg (d1eaenergy_const_nonneg m hCP) (sq_nonneg a), fun z R hR => ?_⟩
  set w : ℝ := (2 * omega m).toReal with hw
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  have hω : 2 * omega m = ENNReal.ofReal w :=
    (ENNReal.ofReal_toReal (TraceExtension.two_mul_omega_ne_top m)).symm
  calc affineCarlesonIntegral (parabolicVolume m)
        (fun x : Space m => ∑' i, SmoothCutoff.parabolicBump (s i / 3) (p i) (x.1, x.2.val) • v i)
        z R
      = ∫⁻ y in Metric.ball z R, ∫⁻ r in Ioo 0 R, affineErrorSq (parabolicVolume m)
          (fun x : Space m =>
            ∑' i, SmoothCutoff.parabolicBump (s i / 3) (p i) (x.1, x.2.val) • v i) y r
            ∂scaleMeasure ∂parabolicVolume m := rfl
    _ ≤ ∫⁻ y in Metric.ball z R, ∫⁻ r in Ioo 0 R, ENNReal.ofReal K *
          ((ENNReal.ofReal r)⁻¹ ^ (m + 2) *
            ∫⁻ x in Metric.ball y r, d1eaenergy_weightSum s p r x ∂parabolicVolume m)
            ∂scaleMeasure ∂parabolicVolume m :=
        lintegral_mono fun y => setLIntegral_mono' measurableSet_Ioo fun r hr =>
          (d1eaenergy_supportWeighted hCP hP hs hv hdisj y hr.1 (hfin r hr.1)).trans_eq
            (mul_assoc _ _ _)
    _ = ENNReal.ofReal K * ∫⁻ y in Metric.ball z R, ∫⁻ r in Ioo 0 R,
          (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
            ∫⁻ x in Metric.ball y r, d1eaenergy_weightSum s p r x ∂parabolicVolume m
            ∂scaleMeasure ∂parabolicVolume m := by
        refine (lintegral_congr fun y =>
          lintegral_const_mul' (ENNReal.ofReal K) _ ENNReal.ofReal_ne_top).trans ?_
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * (2 * omega m * ∫⁻ x in Metric.ball z (2 * R),
          ∫⁻ r in Ioo 0 R, d1eaenergy_weightSum s p r x ∂scaleMeasure ∂parabolicVolume m) :=
        mul_le_mul_right (d1eaenergy_tonelli (fun q : ℝ × Space m => d1eaenergy_weightSum s p q.1 q.2)
          (d1eaenergy_measurable_weightSum s p) z R) _
    _ ≤ ENNReal.ofReal K * (2 * omega m * ∫⁻ x in Metric.ball z (2 * R), 2 ∂parabolicVolume m) :=
        mul_le_mul_right (mul_le_mul_right
          (lintegral_mono fun x => d1eaenergy_lintegral_weightSum_le hs hdisj x R) _) _
    _ = ENNReal.ofReal (K * (w * (2 * (w * (2 * R) ^ (m + 2))))) := by
        rw [setLIntegral_const,
          TraceExtension.parabolicVolume_ball_eq_ofReal z (r := 2 * R) (by positivity), ← hw, hω,
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_mul hK0]
    _ = ENNReal.ofReal (d1eaenergy_const m C_P * a ^ 2 * R ^ baseDimension (Spatial m)) := by
        rw [CutoffCarleson.baseDimension_spatial_eq]
        congr 1
        rw [hKdef, d1eaenergy_const, ← hw, mul_pow]
        ring

end Integration

/-! ## The neck: finitely many stops above each positive level -/

section Neck

/-- A uniformly separated subset of a compact set is finite. -/
theorem d1eaenergy_finite_of_separated {X : Type*} [PseudoMetricSpace X] {K S : Set X}
    (hK : IsCompact K) (hS : S ⊆ K) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) : S.Finite := by
  obtain ⟨t, -, htf, hcover⟩ := finite_cover_balls_of_compact hK (half_pos hδ)
  refine (htf.biUnion (t := fun c => S ∩ Metric.ball c (δ / 2)) fun c _ => ?_).subset ?_
  · refine Set.Subsingleton.finite fun a ha b hb => ?_
    by_contra hab
    have h1 := hsep a ha.1 b hb.1 hab
    have h2 := dist_triangle_right a b c
    have ha2 : dist a c < δ / 2 := ha.2
    have hb2 : dist b c < δ / 2 := hb.2
    linarith
  · intro a ha
    obtain ⟨c, hc, hac⟩ := Set.mem_iUnion₂.1 (hcover (hS ha))
    exact Set.mem_iUnion₂.2 ⟨c, hc, ha, hac⟩

/-- **Finitely many stops above each positive level** (compact centre set and
`bpn:stop-separation`): `{c ∈ 𝒞₊ : r ≤ χ d_c}` is finite for `r > 0`. -/
theorem d1eaenergy_stopping_finite {n k : ℕ} {ι : Type} {q : Space n}
    {R c₀ Cd Cs σ δ E κ θ γ : ℝ} (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ)
    {χ : ℝ} (hχ : 0 < χ) {r : ℝ} (hr : 0 < r) :
    {c : N.stopping | r ≤ χ * N.radius c}.Finite := by
  have hc₀ : 0 < c₀ := N.parameters.c₀_pos
  have hS : {x : Space n | x ∈ N.stopping ∧ r ≤ χ * N.radius x}.Finite := by
    refine d1eaenergy_finite_of_separated N.isCompact_centers (fun x hx => hx.1.1)
      (mul_pos hc₀ (div_pos hr hχ)) fun x hx y hy hxy => ?_
    have hsep := N.stop_separation x hx.1.1 y hy.1.1 hx.1.2 hy.1.2 hxy
    have hxr : r / χ ≤ N.radius x := by
      rw [div_le_iff₀ hχ]
      linarith [hx.2]
    calc c₀ * (r / χ) ≤ c₀ * max (N.radius x) (N.radius y) :=
          mul_le_mul_of_nonneg_left (hxr.trans (le_max_left _ _)) hc₀.le
      _ ≤ dist x y := hsep
  exact (hS.preimage Subtype.val_injective.injOn).subset fun c hc => ⟨c.2, hc⟩

end Neck

/-! ## The attachment energy of the datum -/

/-- **`d1e_attachment_energy`** (implication form of `d1e_AttachmentEnergyStatement`).
The bound is for `K.attachment` itself, the `tsum` of the
datum's bump terms `g_c = ψ_c v_c` (radius `χ d_c / 3`, `v_c = x_c - F⁰(p_c)`). The constant
`C = d1eaenergy_const (k - 2) C_P` is chosen after `n, k` and before the neck (`C_P` is the
Poincaré constant at rank `k - 2`, `B = bumpBound (k - 2)`). -/
theorem d1e_attachment_energy_proof :
    d1e_AffinePoincareStatement → d1e_AttachmentEnergyStatement := by
  intro hPoinc n k
  obtain ⟨C_P, hCP, hP⟩ := hPoinc (NeckType.vertical.rank k)
  refine ⟨d1eaenergy_const (NeckType.vertical.rank k) C_P,
    d1eaenergy_const_nonneg _ hCP, ?_⟩
  intro ι q R c₀ Cd Cs σ δ E κ θ γ N χ ζ a hχ ha hζ K
  have hrad : ∀ c : N.stopping, 0 < N.radius c := fun c => c.2.2
  exact d1eaenergy_carleson (n := n) hCP hP (s := fun c : N.stopping => χ * N.radius c)
    (p := fun c : N.stopping => K.pre c)
    (v := fun c : N.stopping => (c : Space n).1 - K.limitMap (K.pre c))
    (fun c => mul_pos hχ (hrad c))
    (fun c => by
      show ‖(c : Space n).1 - K.limitMap (K.pre c)‖ ≤ 2 * a * (χ * N.radius c)
      rw [norm_sub_rev]
      calc ‖K.limitMap (K.pre c) - (c : Space n).1‖ ≤ 2 * ζ * N.radius c := K.stop_error c c.2
        _ ≤ 2 * (a * χ) * N.radius c :=
            mul_le_mul_of_nonneg_right (by linarith) (hrad c).le
        _ = 2 * a * (χ * N.radius c) := by ring)
    (fun c c' hcc' => K.ball_disjoint c c.2 c' c'.2 fun h => hcc' (Subtype.ext h))
    (fun r hr => d1eaenergy_stopping_finite N hχ hr)

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
