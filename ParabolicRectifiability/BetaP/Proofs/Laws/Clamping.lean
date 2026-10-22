import ParabolicRectifiability.BetaP.Statements.Laws
import ParabolicRectifiability.Geometry.ModelDistance

/-! # The density-free clamping comparisons of beta-`p`

We prove `cclamp_betaPowClamping_proof : BetaPowClampingStatement` (the statement of
`betaPowClamping_law`).

Proof.
1. **Model clamping** (`cclamp_exists_clamped_model`). For `r > 0`, every model `L` and centre `z`
   there is a model `L'` of the same family with `d_P(w,L') ≤ d_P(w,L)` and `d_P(w,L') ≤ 2r` for
   every `w ∈ P(z,r)`. The affine spatial plane keeps its direction, and its normal offset is moved
   radially to the nearest point of the radius-`r` ball around the normal component of the centre
   (`cclamp_plane_clamp`); a horizontal time level is clamped into `[t - r^2, t + r^2]`
   (`cclamp_time_clamp`).
2. **Power comparison** (`cclamp_rpow_add_le`): `d^(a+b) ≤ D^a d^b` for `d ≤ D`, `a, b ≥ 0`.
3. **Integration and normalization** (`cclamp_fitPow_le`, `cclamp_betaPow_le`):
   `B_{a+b} ≤ 2^a B_b` for all `a, b ≥ 0`, which gives both clamping inequalities
   (`a = 2-p, b = p` and `a = p-2, b = 2`). Everything is in `ℝ≥0∞`; no regularity of `μ`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## Model clamping -/

/-- Clamping an affine spatial plane: the same direction with the normal offset moved into the
radius-`r` ball around the normal component of `c`. Residuals of points of the open `r`-ball around
`c` do not increase and are at most `2r`. -/
theorem cclamp_plane_clamp {n m : ℕ} (A : AffineSpatialPlane n m) (c : Spatial n) {r : ℝ}
    (hr : 0 < r) :
    ∃ A' : AffineSpatialPlane n m, ∀ x : Spatial n, ‖x - c‖ < r →
      ‖x - A'.projection x‖ ≤ ‖x - A.projection x‖ ∧ ‖x - A'.projection x‖ ≤ 2 * r := by
  obtain ⟨qc, hqc⟩ : ∃ q : Spatial n, q = c - A.direction.starProjection c := ⟨_, rfl⟩
  have hqcmem : qc ∈ A.directionᗮ := hqc ▸ A.direction.sub_starProjection_mem_orthogonal c
  -- the normal component of a ball point is within `r` of the normal component of `c`
  have hy : ∀ x : Spatial n, ‖x - A.direction.starProjection x - qc‖ ≤ ‖x - c‖ := by
    intro x
    have h1 : x - A.direction.starProjection x - qc =
        (x - c) - A.direction.starProjection (x - c) := by
      rw [hqc, map_sub]; abel
    rw [h1, ← Submodule.starProjection_orthogonal_val]
    exact A.directionᗮ.norm_starProjection_apply_le _
  -- residual of a plane with direction `A.direction` and anchor `b`
  have hres : ∀ b x : Spatial n, x - (b + A.direction.starProjection x) =
      (x - A.direction.starProjection x - qc) - (b - qc) := by
    intro b x; abel
  by_cases hu : ‖A.anchor - qc‖ ≤ r
  · refine ⟨A, fun x hx => ⟨le_rfl, ?_⟩⟩
    have e : x - A.projection x =
        (x - A.direction.starProjection x - qc) - (A.anchor - qc) := hres A.anchor x
    rw [e]
    calc ‖(x - A.direction.starProjection x - qc) - (A.anchor - qc)‖
        ≤ ‖x - A.direction.starProjection x - qc‖ + ‖A.anchor - qc‖ := norm_sub_le _ _
      _ ≤ r + r := add_le_add ((hy x).trans hx.le) hu
      _ = 2 * r := by ring
  · replace hu := not_le.mp hu
    obtain ⟨u, hu_def⟩ : ∃ u : Spatial n, u = A.anchor - qc := ⟨_, rfl⟩
    rw [← hu_def] at hu
    have hN : 0 < ‖u‖ := hr.trans hu
    obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = r / ‖u‖ := ⟨_, rfl⟩
    have hs0 : 0 ≤ s := hs_def ▸ div_nonneg hr.le hN.le
    have hs1 : s ≤ 1 := hs_def ▸ (div_le_one₀ hN).2 hu.le
    have hsN : s * ‖u‖ = r := by rw [hs_def]; exact div_mul_cancel₀ r hN.ne'
    have humem : u ∈ A.directionᗮ := hu_def ▸ A.directionᗮ.sub_mem A.anchor_orthogonal hqcmem
    have hmem : qc + s • u ∈ A.directionᗮ :=
      A.directionᗮ.add_mem hqcmem (A.directionᗮ.smul_mem s humem)
    refine ⟨⟨A.direction, A.rank_eq, qc + s • u, hmem⟩, fun x hx => ?_⟩
    have e' : x - (⟨A.direction, A.rank_eq, qc + s • u, hmem⟩ : AffineSpatialPlane n m).projection x
        = (x - A.direction.starProjection x - qc) - s • u := by
      rw [show (x - A.direction.starProjection x - qc) - s • u =
        (x - A.direction.starProjection x - qc) - ((qc + s • u) - qc) by abel]
      exact hres (qc + s • u) x
    have e : x - A.projection x = (x - A.direction.starProjection x - qc) - u := by
      rw [hu_def]; exact hres A.anchor x
    rw [e', e]
    obtain ⟨y, hy_def⟩ : ∃ y : Spatial n, y = x - A.direction.starProjection x - qc := ⟨_, rfl⟩
    rw [← hy_def]
    have hyr : ‖y‖ ≤ r := hy_def ▸ (hy x).trans hx.le
    constructor
    · have hi : inner ℝ y u ≤ ‖y‖ * ‖u‖ := real_inner_le_norm y u
      have h2 : ‖y‖ * ‖u‖ ≤ s * ‖u‖ * ‖u‖ := by
        rw [hsN]; exact mul_le_mul_of_nonneg_right hyr hN.le
      have hF : (1 - s) * inner ℝ y u ≤ (1 - s) * (s * ‖u‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (hi.trans h2) (by linarith)
      have key : ‖y - s • u‖ ^ 2 ≤ ‖y - u‖ ^ 2 := by
        rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right, norm_smul,
          Real.norm_of_nonneg hs0]
        nlinarith [hF, sq_nonneg ((1 - s) * ‖u‖)]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 key
    · calc ‖y - s • u‖ ≤ ‖y‖ + ‖s • u‖ := norm_sub_le _ _
        _ = ‖y‖ + s * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hs0]
        _ ≤ r + r := by rw [hsN]; linarith
        _ = 2 * r := by ring

/-- Clamping a time level into `[t - ρ, t + ρ]`: for `|s - t| ≤ ρ` the distance to the level does
not increase and is at most `2ρ`. -/
theorem cclamp_time_clamp (t τ s ρ : ℝ) (hs : |s - t| ≤ ρ) :
    |s - max (t - ρ) (min (t + ρ) τ)| ≤ |s - τ| ∧
      |s - max (t - ρ) (min (t + ρ) τ)| ≤ 2 * ρ := by
  obtain ⟨h1, h2⟩ := abs_le.mp hs
  have a1 := le_abs_self (s - τ)
  have a3 := neg_le_abs (s - τ)
  have a4 := abs_nonneg (s - τ)
  rcases le_total τ (t + ρ) with h | h
  · rw [min_eq_right h]
    rcases le_total (t - ρ) τ with h' | h'
    · rw [max_eq_right h']
      exact ⟨le_rfl, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    · rw [max_eq_left h']
      exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  · rw [min_eq_left h, max_eq_right (by linarith : t - ρ ≤ t + ρ)]
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem cclamp_horizontal_infEDist {n k : ℕ} (L : HorizontalModel n k) (x : Spatial n) (s : ℝ) :
    Metric.infEDist (point x s) L.toSet =
      ENNReal.ofReal (max ‖x - L.spatial.projection x‖ (Real.sqrt |s - L.time|)) := by
  rw [L.infEDist_eq_projection, edist_dist]
  change ENNReal.ofReal (dist (point x s) (point (L.spatial.projection x) L.time)) = _
  rw [dist_point]

theorem cclamp_vertical_infEDist {n k : ℕ} (L : VerticalModel n k) (x : Spatial n) (s : ℝ) :
    Metric.infEDist (point x s) L.toSet = ENNReal.ofReal ‖x - L.spatial.projection x‖ := by
  rw [L.infEDist_eq_projection, edist_dist]
  change ENNReal.ofReal (dist (point x s) (point (L.spatial.projection x) s)) = _
  rw [dist_point, sub_self, abs_zero, Real.sqrt_zero, max_eq_left (norm_nonneg _)]

theorem cclamp_ofReal_two_mul (r : ℝ) : ENNReal.ofReal (2 * r) = 2 * ENNReal.ofReal r := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

theorem cclamp_horizontal_clamp {n k : ℕ} (L : HorizontalModel n k) (z : Space n) {r : ℝ}
    (hr : 0 < r) :
    ∃ L' : HorizontalModel n k, ∀ w ∈ Metric.ball z r,
      Metric.infEDist w L'.toSet ≤ Metric.infEDist w L.toSet ∧
        Metric.infEDist w L'.toSet ≤ 2 * ENNReal.ofReal r := by
  rcases z with ⟨c, ⟨t⟩⟩
  obtain ⟨A', hA'⟩ := cclamp_plane_clamp L.spatial c hr
  refine ⟨⟨L.positive, A', max (t - r ^ 2) (min (t + r ^ 2) L.time)⟩, ?_⟩
  rintro ⟨x, ⟨s⟩⟩ hw
  have hw' : ‖x - c‖ < r ∧ |s - t| < r ^ 2 := (mem_ball_point c x t s r hr).1 hw
  obtain ⟨hx1, hx2⟩ := hA' x hw'.1
  obtain ⟨ht1, ht2⟩ := cclamp_time_clamp t L.time s (r ^ 2) hw'.2.le
  have e1 := cclamp_horizontal_infEDist L x s
  have e2 := cclamp_horizontal_infEDist
    ⟨L.positive, A', max (t - r ^ 2) (min (t + r ^ 2) L.time)⟩ x s
  change Metric.infEDist (point x s) _ ≤ Metric.infEDist (point x s) _ ∧
    Metric.infEDist (point x s) _ ≤ _
  rw [e1, e2]
  dsimp only
  refine ⟨ENNReal.ofReal_le_ofReal (max_le_max hx1 (Real.sqrt_le_sqrt ht1)), ?_⟩
  rw [← cclamp_ofReal_two_mul]
  refine ENNReal.ofReal_le_ofReal (max_le hx2 ?_)
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith [sq_nonneg r]

theorem cclamp_vertical_clamp {n k : ℕ} (L : VerticalModel n k) (z : Space n) {r : ℝ}
    (hr : 0 < r) :
    ∃ L' : VerticalModel n k, ∀ w ∈ Metric.ball z r,
      Metric.infEDist w L'.toSet ≤ Metric.infEDist w L.toSet ∧
        Metric.infEDist w L'.toSet ≤ 2 * ENNReal.ofReal r := by
  rcases z with ⟨c, ⟨t⟩⟩
  obtain ⟨A', hA'⟩ := cclamp_plane_clamp L.spatial c hr
  refine ⟨⟨L.spatialRank, L.two_le, L.rank_eq, A'⟩, ?_⟩
  rintro ⟨x, ⟨s⟩⟩ hw
  have hw' : ‖x - c‖ < r ∧ |s - t| < r ^ 2 := (mem_ball_point c x t s r hr).1 hw
  obtain ⟨hx1, hx2⟩ := hA' x hw'.1
  have e1 := cclamp_vertical_infEDist L x s
  have e2 := cclamp_vertical_infEDist ⟨L.spatialRank, L.two_le, L.rank_eq, A'⟩ x s
  change Metric.infEDist (point x s) _ ≤ Metric.infEDist (point x s) _ ∧
    Metric.infEDist (point x s) _ ≤ _
  rw [e1, e2]
  dsimp only
  refine ⟨ENNReal.ofReal_le_ofReal hx1, ?_⟩
  rw [← cclamp_ofReal_two_mul]
  exact ENNReal.ofReal_le_ofReal hx2

/-- **Model clamping lemma.** For `r > 0`, every model and every centre there is a model of the
same family whose distance to every point of `P(z,r)` is no larger and at most `2r`. -/
theorem cclamp_exists_clamped_model {n k : ℕ} {T : FamilyKind} (L : Models n k T) (z : Space n)
    {r : ℝ} (hr : 0 < r) :
    ∃ L' : Models n k T, ∀ w ∈ Metric.ball z r,
      Metric.infEDist w (modelSet L') ≤ Metric.infEDist w (modelSet L) ∧
        Metric.infEDist w (modelSet L') ≤ 2 * ENNReal.ofReal r := by
  cases T with
  | horizontal => exact cclamp_horizontal_clamp L z hr
  | vertical => exact cclamp_vertical_clamp L z hr
  | mixed =>
    cases L with
    | inl L =>
      obtain ⟨L', h⟩ := cclamp_horizontal_clamp L z hr
      exact ⟨Sum.inl L', h⟩
    | inr L =>
      obtain ⟨L', h⟩ := cclamp_vertical_clamp L z hr
      exact ⟨Sum.inr L', h⟩

/-! ## Power comparison, integration and normalization -/

theorem cclamp_rpow_add_le {d D : ℝ≥0∞} (hd : d ≤ D) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    d ^ (a + b) ≤ D ^ a * d ^ b := by
  rw [ENNReal.rpow_add_of_nonneg _ _ ha hb]
  exact mul_le_mul' (ENNReal.rpow_le_rpow hd ha) le_rfl

theorem cclamp_fitPow_le {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n)) (L : Models n k T)
    (z : Space n) {r : ℝ} (hr : 0 < r) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ L' : Models n k T,
      fitPow μ (a + b) L' z r ≤ (2 * ENNReal.ofReal r) ^ a * fitPow μ b L z r := by
  obtain ⟨L', hL'⟩ := cclamp_exists_clamped_model L z hr
  refine ⟨L', ?_⟩
  have hne : (2 * ENNReal.ofReal r) ^ a ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ha (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)
  unfold fitPow
  calc ∫⁻ w in Metric.ball z r, Metric.infEDist w (modelSet L') ^ (a + b) ∂μ
      ≤ ∫⁻ w in Metric.ball z r,
          (2 * ENNReal.ofReal r) ^ a * Metric.infEDist w (modelSet L) ^ b ∂μ := by
        refine setLIntegral_mono' Metric.isOpen_ball.measurableSet fun w hw => ?_
        obtain ⟨h1, h2⟩ := hL' w hw
        exact (cclamp_rpow_add_le h2 ha hb).trans
          (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow h1 hb))
    _ = (2 * ENNReal.ofReal r) ^ a *
          ∫⁻ w in Metric.ball z r, Metric.infEDist w (modelSet L) ^ b ∂μ :=
        lintegral_const_mul' _ _ hne

theorem cclamp_scale_identity (R : ℝ≥0∞) (h0 : R ≠ 0) (ht : R ≠ ⊤) (c : ℝ) {a : ℝ}
    (ha : 0 ≤ a) : R⁻¹ ^ (c + a) * (2 * R) ^ a = 2 ^ a * R⁻¹ ^ c := by
  have h1 : R⁻¹ ^ a * R ^ a = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ ha, ENNReal.inv_mul_cancel h0 ht, ENNReal.one_rpow]
  rw [ENNReal.rpow_add _ _ (ENNReal.inv_ne_zero.2 ht) (ENNReal.inv_ne_top.2 h0),
    ENNReal.mul_rpow_of_nonneg _ _ ha]
  calc R⁻¹ ^ c * R⁻¹ ^ a * (2 ^ a * R ^ a) = 2 ^ a * R⁻¹ ^ c * (R⁻¹ ^ a * R ^ a) := by ring
    _ = 2 ^ a * R⁻¹ ^ c := by rw [h1, mul_one]

/-- `B_{a+b} ≤ 2^a B_b` for all `a, b ≥ 0`, every family, source, centre and radius. -/
theorem cclamp_betaPow_le {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (z : Space n)
    (r : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    betaPow μ k T (a + b) z r ≤ (2 : ℝ≥0∞) ^ a * betaPow μ k T b z r := by
  unfold betaPow
  split_ifs with hr
  · have hR0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
    have hRt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
    have h2t : 2 * ENNReal.ofReal r ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hRt
    have hC0 : (2 * ENNReal.ofReal r) ^ a ≠ 0 :=
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 (mul_ne_zero two_ne_zero hR0)) h2t).ne'
    have hCt : (2 * ENNReal.ofReal r) ^ a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ha h2t
    have hinf : ⨅ L : Models n k T, fitPow μ (a + b) L z r ≤
        (2 * ENNReal.ofReal r) ^ a * ⨅ L : Models n k T, fitPow μ b L z r := by
      rw [ENNReal.mul_iInf_of_ne hC0 hCt]
      refine le_iInf fun L => ?_
      obtain ⟨L', hL'⟩ := cclamp_fitPow_le μ L z hr ha hb
      exact (iInf_le _ L').trans hL'
    have hexp : (k : ℝ) + (a + b) = ((k : ℝ) + b) + a := by ring
    calc (ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + (a + b)) * ⨅ L : Models n k T, fitPow μ (a + b) L z r
        ≤ (ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + (a + b)) *
            ((2 * ENNReal.ofReal r) ^ a * ⨅ L : Models n k T, fitPow μ b L z r) :=
          mul_le_mul' le_rfl hinf
      _ = 2 ^ a * ((ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + b) *
            ⨅ L : Models n k T, fitPow μ b L z r) := by
          rw [← mul_assoc, hexp, cclamp_scale_identity _ hR0 hRt _ ha, mul_assoc]
  · exact zero_le

/-- The density-free clamping comparisons `B_2 ≤ 2^{2-p} B_p` (`0 < p ≤ 2`) and
`B_p ≤ 2^{p-2} B_2` (`2 ≤ p`): `BetaPowClampingStatement`. -/
theorem cclamp_betaPowClamping_proof : BetaPowClampingStatement := by
  intro n _ k _ _ T μ z r
  refine ⟨fun p hp _ => ?_, fun p hp => ?_⟩
  · have h := cclamp_betaPow_le μ k T z r (a := 2 - p) (b := p) (by linarith) hp.le
    rwa [sub_add_cancel] at h
  · have h := cclamp_betaPow_le μ k T z r (a := p - 2) (b := 2) (by linarith) (by norm_num)
    rwa [sub_add_cancel] at h

end ParabolicRectifiability.BetaP
