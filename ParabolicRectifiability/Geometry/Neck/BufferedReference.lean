import ParabolicRectifiability.Geometry.Neck.Conclusions
import ParabolicRectifiability.Metric.BaseVolume

/-!
# Buffered reference measures from a supplied chart

The two buffer constructions for necks:
`verticalBufferedReference_of_chart_proof` and `horizontalBufferedReference_of_chart_proof`,
with the types of `NeckHubTree.verticalBufferedReference_of_chart` and
`NeckHubTree.horizontalBufferedReference_of_chart`.

The supplied chart is the existential chart witness. The base ball is centred at
`p₀ = (0, t_q)` (vertical) or `u₀ = 0` (horizontal) with radius `4 C_* R`. Every occurrence
`(j,a)` is reached by a parameter `p = (u, t_{j,a})` with `|u| ≤ 13/4 C_* R`, so the buffer
ball `P_b(p, r_j/8)` lies in the base ball, and its image lies in `P(z_{j,a}, r_j)` because
`11/10 · 1/8 + 1/4 < 1`. The constants are
`c_b = min_{d ≤ n} 2 ω_d 8^{-(d+2)}`, `C_m = Σ_{d ≤ n} 2 ω_d (4 C_*)^{d+2}` (vertical) and
`c_b = min_{d ≤ n} ω_d 8^{-d}`, `C_m = Σ_{d ≤ n} ω_d (4 C_*)^d` (horizontal); the linear
isometry `U` forces `m ≤ n`. The case `m = 0` is included.
-/

noncomputable section

namespace ParabolicRectifiability

namespace NeckHubTree

open MeasureTheory Set
open scoped ENNReal

universe u

/-! ## Constants and elementary facts -/

/-- Vertical `c_b = min_{d ≤ n} 2 ω_d / 8^{d+2}`. -/
def nk1VerticalCb (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).inf' (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero n))
    (fun d => 2 * (omega d).toReal / 8 ^ (d + 2))

/-- Vertical `C_m = Σ_{d ≤ n} 2 ω_d (4 C_*)^{d+2}`. -/
def nk1VerticalCm (n : ℕ) (Cs : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (n + 1), 2 * (omega d).toReal * (4 * Cs) ^ (d + 2)

/-- Horizontal `c_b = min_{d ≤ n} ω_d / 8^d`. -/
def nk1HorizontalCb (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).inf' (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero n))
    (fun d => (omega d).toReal / 8 ^ d)

/-- Horizontal `C_m = Σ_{d ≤ n} ω_d (4 C_*)^d`. -/
def nk1HorizontalCm (n : ℕ) (Cs : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (n + 1), (omega d).toReal * (4 * Cs) ^ d

theorem nk1_omega_toReal_pos (d : ℕ) : 0 < (omega d).toReal :=
  ENNReal.toReal_pos (omega_pos d).ne' (omega_lt_top d).ne

theorem nk1_verticalCb_pos (n : ℕ) : 0 < nk1VerticalCb n := by
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_eq_inf'
    (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero n))
    (fun d => 2 * (omega d).toReal / 8 ^ (d + 2))
  have := nk1_omega_toReal_pos d
  rw [nk1VerticalCb, hd]
  show 0 < 2 * (omega d).toReal / 8 ^ (d + 2)
  positivity

theorem nk1_verticalCb_le {n d : ℕ} (hd : d ≤ n) :
    nk1VerticalCb n ≤ 2 * (omega d).toReal / 8 ^ (d + 2) :=
  Finset.inf'_le (fun d => 2 * (omega d).toReal / 8 ^ (d + 2))
    (Finset.mem_range.2 (Nat.lt_succ_of_le hd))

theorem nk1_verticalCm_pos (n : ℕ) {Cs : ℝ} (hCs : 0 < Cs) : 0 < nk1VerticalCm n Cs := by
  unfold nk1VerticalCm
  refine Finset.sum_pos (fun d _ => ?_) ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
  have := nk1_omega_toReal_pos d
  positivity

theorem nk1_verticalCm_le {n d : ℕ} (hd : d ≤ n) {Cs : ℝ} (hCs : 0 < Cs) :
    2 * (omega d).toReal * (4 * Cs) ^ (d + 2) ≤ nk1VerticalCm n Cs := by
  unfold nk1VerticalCm
  refine Finset.single_le_sum (f := fun d => 2 * (omega d).toReal * (4 * Cs) ^ (d + 2))
    (fun i _ => ?_) (Finset.mem_range.2 (Nat.lt_succ_of_le hd))
  have := nk1_omega_toReal_pos i
  positivity

theorem nk1_horizontalCb_pos (n : ℕ) : 0 < nk1HorizontalCb n := by
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_eq_inf'
    (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero n))
    (fun d => (omega d).toReal / 8 ^ d)
  have := nk1_omega_toReal_pos d
  rw [nk1HorizontalCb, hd]
  show 0 < (omega d).toReal / 8 ^ d
  positivity

theorem nk1_horizontalCb_le {n d : ℕ} (hd : d ≤ n) :
    nk1HorizontalCb n ≤ (omega d).toReal / 8 ^ d :=
  Finset.inf'_le (fun d => (omega d).toReal / 8 ^ d)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hd))

theorem nk1_horizontalCm_pos (n : ℕ) {Cs : ℝ} (hCs : 0 < Cs) : 0 < nk1HorizontalCm n Cs := by
  unfold nk1HorizontalCm
  refine Finset.sum_pos (fun d _ => ?_) ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
  have := nk1_omega_toReal_pos d
  positivity

theorem nk1_horizontalCm_le {n d : ℕ} (hd : d ≤ n) {Cs : ℝ} (hCs : 0 < Cs) :
    (omega d).toReal * (4 * Cs) ^ d ≤ nk1HorizontalCm n Cs := by
  unfold nk1HorizontalCm
  refine Finset.single_le_sum (f := fun d => (omega d).toReal * (4 * Cs) ^ d)
    (fun i _ => ?_) (Finset.mem_range.2 (Nat.lt_succ_of_le hd))
  have := nk1_omega_toReal_pos i
  positivity

theorem nk1_ofReal_two_omega_mul (d k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (2 * (omega d).toReal * r ^ k) = 2 * omega d * ENNReal.ofReal r ^ k := by
  have h := nk1_omega_toReal_pos d
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_toReal (omega_lt_top d).ne, ENNReal.ofReal_pow hr, ENNReal.ofReal_ofNat]

theorem nk1_ofReal_omega_mul (d k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal ((omega d).toReal * r ^ k) = omega d * ENNReal.ofReal r ^ k := by
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (omega_lt_top d).ne, ENNReal.ofReal_pow hr]

theorem nk1_scale_pos {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι) (j : ℕ) :
    0 < F.scale j :=
  div_pos F.initialRadius_pos (pow_pos (by norm_num) j)

theorem nk1_scale_le {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι) (j : ℕ) :
    F.scale j ≤ F.initialRadius :=
  div_le_self F.initialRadius_pos.le (one_le_pow₀ (by norm_num))

/-- A linear isometry `ℝ^m → ℝ^n` forces `m ≤ n`. -/
theorem nk1_le_of_linearIsometry {m n : ℕ} (U : Spatial m →ₗᵢ[ℝ] Spatial n) : m ≤ n := by
  have h := LinearMap.finrank_le_finrank_of_injective (f := U.toLinearMap) U.injective
  simpa only [finrank_euclideanSpace_fin] using h

theorem nk1_continuous_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {K : ℝ} (hK : 0 ≤ K) (h : ∀ x y, dist (f x) (f y) ≤ K * dist x y) :
    Continuous f :=
  (LipschitzWith.of_dist_le_mul (K := ⟨K, hK⟩) h).continuous

/-- `‖U u‖ ≤ 13/4 C_* R` from the four triangle-inequality pieces. -/
theorem nk1_norm_le_of_pieces {n : ℕ} (Uu Gu c y x : Spatial n) {r Cs R : ℝ}
    (h1 : ‖Gu - (x + Uu)‖ ≤ Cs * R) (h2 : ‖Gu - c‖ ≤ r / 4) (hr : r ≤ Cs * R)
    (h3 : ‖c - y‖ < Cs * R) (h4 : ‖x - y‖ ≤ Cs * R) :
    ‖Uu‖ ≤ 13 / 4 * (Cs * R) := by
  have e : Uu = -(Gu - (x + Uu)) + (Gu - c) + (c - y) + (y - x) := by abel
  have a1 := norm_add_le (-(Gu - (x + Uu)) + (Gu - c) + (c - y)) (y - x)
  have a2 := norm_add_le (-(Gu - (x + Uu)) + (Gu - c)) (c - y)
  have a3 := norm_add_le (-(Gu - (x + Uu))) (Gu - c)
  rw [norm_neg] at a3
  rw [norm_sub_rev] at h4
  rw [e]
  linarith

/-! ## Vertical form -/

theorem nk1_vertical_core {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι) (N : ℕ)
    (q : Space n) (R Cs : ℝ) (G : Spatial m → ℝ → Spatial n) (x : Spatial n)
    (U : Spatial m →ₗᵢ[ℝ] Spatial n) (hCs : 0 < Cs) (hR : 0 < R)
    (hG : ∀ p p' : Space m,
      4 / 5 * dist p p' ≤ dist (timePreservingMap G p) (timePreservingMap G p') ∧
        dist (timePreservingMap G p) (timePreservingMap G p') ≤ 11 / 10 * dist p p')
    (hGx : ∀ (u : Spatial m) (t : ℝ), ‖G u t - (x + U u)‖ ≤ Cs * R)
    (hx : ‖x - q.1‖ ≤ Cs * R) (hr0 : F.initialRadius ≤ Cs * R)
    (hcen : ∀ j ≤ N, ∀ a ∈ F.index j, F.center j a ∈ Metric.ball q (Cs * R))
    (hreach : ∀ j ≤ N, ∀ a ∈ F.index j, ∃ u : Spatial m,
      ‖G u (F.center j a).2.val - (F.center j a).1‖ ≤ F.scale j / 4) :
    F.HasVerticalBufferedReference R (4 * Cs) (nk1VerticalCm n Cs) (nk1VerticalCb n) N := by
  have hmn : m ≤ n := nk1_le_of_linearIsometry U
  have hCsR : 0 < Cs * R := mul_pos hCs hR
  have hD : 0 < 4 * Cs * R := by positivity
  have hmeas : Measurable (timePreservingMap G) :=
    (nk1_continuous_of_dist_le (by norm_num : (0 : ℝ) ≤ 11 / 10) (fun p p' => (hG p p').2)).measurable
  have key : ∀ j ≤ N, ∀ a ∈ F.index j, ∃ p ∈ Metric.ball (point (0 : Spatial m) q.2.val) (4 * Cs * R),
      p.2.val = (F.center j a).2.val ∧
        dist (timePreservingMap G p) (F.center j a) ≤ F.scale j / 4 ∧
        Metric.ball p (F.scale j / 8) ⊆ Metric.ball (point (0 : Spatial m) q.2.val) (4 * Cs * R) := by
    intro j hj a ha
    obtain ⟨u, hu⟩ := hreach j hj a ha
    have hr := nk1_scale_pos F j
    have hrle : F.scale j ≤ Cs * R := (nk1_scale_le F j).trans hr0
    have hc := hcen j hj a ha
    change point (F.center j a).1 (F.center j a).2.val ∈
      Metric.ball (point q.1 q.2.val) (Cs * R) at hc
    rw [mem_ball_point _ _ _ _ _ hCsR] at hc
    have hu' : ‖U u‖ ≤ 13 / 4 * (Cs * R) :=
      nk1_norm_le_of_pieces (U u) _ _ _ x (hGx u _) hu hrle hc.1 hx
    rw [U.norm_map] at hu'
    have hdist : dist (point u (F.center j a).2.val) (point (0 : Spatial m) q.2.val) ≤
        13 / 4 * (Cs * R) := by
      rw [dist_point, sub_zero]
      refine max_le hu' ?_
      have := ((Real.sqrt_lt' hCsR).2 hc.2).le
      linarith
    refine ⟨point u (F.center j a).2.val, ?_, rfl, ?_, ?_⟩
    · rw [Metric.mem_ball]
      linarith
    · change dist (point (G u (F.center j a).2.val) (F.center j a).2.val)
        (point (F.center j a).1 (F.center j a).2.val) ≤ F.scale j / 4
      rw [dist_point, sub_self, abs_zero, Real.sqrt_zero]
      exact max_le hu (by positivity)
    · apply Metric.ball_subset_ball'
      linarith
  refine ⟨G, point (0 : Spatial m) q.2.val, hG, key, ?_, ?_⟩
  · rw [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ, parabolicVolume_ball _ _ hD,
      ← nk1_ofReal_two_omega_mul _ _ hD.le]
    apply ENNReal.ofReal_le_ofReal
    calc 2 * (omega m).toReal * (4 * Cs * R) ^ (m + 2)
        = (2 * (omega m).toReal * (4 * Cs) ^ (m + 2)) * R ^ (m + 2) := by
          rw [mul_pow]; ring
      _ ≤ nk1VerticalCm n Cs * R ^ (m + 2) :=
          mul_le_mul_of_nonneg_right (nk1_verticalCm_le hmn hCs) (by positivity)
  · intro j hj a ha
    obtain ⟨p, -, -, hpz, hsub⟩ := key j hj a ha
    have hr := nk1_scale_pos F j
    have hr8 : 0 < F.scale j / 8 := by positivity
    have hreal : nk1VerticalCb n * F.scale j ^ (m + 2) ≤
        2 * (omega m).toReal * (F.scale j / 8) ^ (m + 2) := by
      calc nk1VerticalCb n * F.scale j ^ (m + 2)
          ≤ 2 * (omega m).toReal / 8 ^ (m + 2) * F.scale j ^ (m + 2) :=
            mul_le_mul_of_nonneg_right (nk1_verticalCb_le hmn) (by positivity)
        _ = 2 * (omega m).toReal * (F.scale j / 8) ^ (m + 2) := by
            rw [div_pow]; ring
    calc ENNReal.ofReal (nk1VerticalCb n * F.scale j ^ (m + 2))
        ≤ ENNReal.ofReal (2 * (omega m).toReal * (F.scale j / 8) ^ (m + 2)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = parabolicVolume m (Metric.ball p (F.scale j / 8)) := by
          rw [nk1_ofReal_two_omega_mul _ _ hr8.le, parabolicVolume_ball _ _ hr8]
      _ ≤ ((parabolicVolume m).restrict (Metric.ball (point (0 : Spatial m) q.2.val) (4 * Cs * R)))
            (timePreservingMap G ⁻¹' Metric.ball (F.center j a) (F.scale j)) := by
          rw [Measure.restrict_apply' Metric.isOpen_ball.measurableSet]
          apply measure_mono
          intro p' hp'
          refine ⟨?_, hsub hp'⟩
          rw [Set.mem_preimage, Metric.mem_ball]
          have h1 := (hG p' p).2
          have h2 : dist p' p < F.scale j / 8 := hp'
          have h3 := dist_triangle (timePreservingMap G p') (timePreservingMap G p) (F.center j a)
          linarith
      _ ≤ _ := Measure.le_map_apply hmeas.aemeasurable _

/-- Buffered reference, vertical form: the supplied chart is the witness,
`p₀ = (0, t_q)`, `C_r = 4 C_*`. The type is that of
`NeckHubTree.verticalBufferedReference_of_chart`. -/
theorem verticalBufferedReference_of_chart_proof (n : ℕ) :
    ∃ cb : ℝ, 0 < cb ∧ ∀ Cs : ℝ, 0 < Cs → ∃ Cr Cm : ℝ, 0 < Cr ∧ 0 < Cm ∧
      ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (N : ℕ) (q : Space n) (R : ℝ)
        (G : Spatial m → ℝ → Spatial n) (x : Spatial n) (U : Spatial m →ₗᵢ[ℝ] Spatial n),
        0 < R →
        (∀ p p' : Space m,
          4 / 5 * dist p p' ≤ dist (timePreservingMap G p) (timePreservingMap G p') ∧
            dist (timePreservingMap G p) (timePreservingMap G p') ≤ 11 / 10 * dist p p') →
        (∀ (u : Spatial m) (t : ℝ), ‖G u t - (x + U u)‖ ≤ Cs * R) →
        ‖x - q.1‖ ≤ Cs * R →
        F.initialRadius ≤ Cs * R →
        (∀ j ≤ N, ∀ a ∈ F.index j, F.center j a ∈ Metric.ball q (Cs * R)) →
        (∀ j ≤ N, ∀ a ∈ F.index j, ∃ u : Spatial m,
          ‖G u (F.center j a).2.val - (F.center j a).1‖ ≤ F.scale j / 4) →
        F.HasVerticalBufferedReference R Cr Cm cb N := by
  refine ⟨nk1VerticalCb n, nk1_verticalCb_pos n, fun Cs hCs =>
    ⟨4 * Cs, nk1VerticalCm n Cs, by positivity, nk1_verticalCm_pos n hCs, ?_⟩⟩
  intro m ι F N q R G x U hR hG hGx hx hr0 hcen hreach
  exact nk1_vertical_core F N q R Cs G x U hCs hR hG hGx hx hr0 hcen hreach

/-! ## Horizontal form -/

theorem nk1_horizontal_core {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι) (N : ℕ)
    (y : Spatial n) (R Cs : ℝ) (G : Spatial m → Spatial n) (x : Spatial n)
    (U : Spatial m →ₗᵢ[ℝ] Spatial n) (hCs : 0 < Cs) (hR : 0 < R)
    (hG : ∀ u v : Spatial m,
      4 / 5 * ‖u - v‖ ≤ ‖G u - G v‖ ∧ ‖G u - G v‖ ≤ 11 / 10 * ‖u - v‖)
    (hGx : ∀ u : Spatial m, ‖G u - (x + U u)‖ ≤ Cs * R)
    (hx : ‖x - y‖ ≤ Cs * R) (hr0 : F.initialRadius ≤ Cs * R)
    (hcen : ∀ j ≤ N, ∀ a ∈ F.index j, (F.center j a).1 ∈ Metric.ball y (Cs * R))
    (hreach : ∀ j ≤ N, ∀ a ∈ F.index j, ∃ u : Spatial m,
      ‖G u - (F.center j a).1‖ ≤ F.scale j / 4) :
    F.HasHorizontalBufferedReference R (4 * Cs) (nk1HorizontalCm n Cs) (nk1HorizontalCb n) N := by
  have hmn : m ≤ n := nk1_le_of_linearIsometry U
  have hCsR : 0 < Cs * R := mul_pos hCs hR
  have hD : 0 < 4 * Cs * R := by positivity
  have hGd : ∀ u v : Spatial m, dist (G u) (G v) ≤ 11 / 10 * dist u v := by
    intro u v
    rw [dist_eq_norm, dist_eq_norm]
    exact (hG u v).2
  have hmeas : Measurable G :=
    (nk1_continuous_of_dist_le (by norm_num : (0 : ℝ) ≤ 11 / 10) hGd).measurable
  have key : ∀ j ≤ N, ∀ a ∈ F.index j, ∃ u ∈ Metric.ball (0 : Spatial m) (4 * Cs * R),
      ‖G u - (F.center j a).1‖ ≤ F.scale j / 4 ∧
        Metric.ball u (F.scale j / 8) ⊆ Metric.ball (0 : Spatial m) (4 * Cs * R) := by
    intro j hj a ha
    obtain ⟨u, hu⟩ := hreach j hj a ha
    have hrle : F.scale j ≤ Cs * R := (nk1_scale_le F j).trans hr0
    have hc := hcen j hj a ha
    rw [Metric.mem_ball, dist_eq_norm] at hc
    have hu' : ‖U u‖ ≤ 13 / 4 * (Cs * R) :=
      nk1_norm_le_of_pieces (U u) _ _ _ x (hGx u) hu hrle hc hx
    rw [U.norm_map] at hu'
    have hdist : dist u 0 ≤ 13 / 4 * (Cs * R) := by
      rw [dist_zero_right]; exact hu'
    refine ⟨u, ?_, hu, ?_⟩
    · rw [Metric.mem_ball]
      linarith
    · apply Metric.ball_subset_ball'
      linarith
  refine ⟨G, 0, hG, key, ?_, ?_⟩
  · rw [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ, volume_spatial_ball _ hD,
      ← nk1_ofReal_omega_mul _ _ hD.le]
    apply ENNReal.ofReal_le_ofReal
    calc (omega m).toReal * (4 * Cs * R) ^ m
        = ((omega m).toReal * (4 * Cs) ^ m) * R ^ m := by
          rw [mul_pow]; ring
      _ ≤ nk1HorizontalCm n Cs * R ^ m :=
          mul_le_mul_of_nonneg_right (nk1_horizontalCm_le hmn hCs) (by positivity)
  · intro j hj a ha
    obtain ⟨u, -, hu, hsub⟩ := key j hj a ha
    have hr := nk1_scale_pos F j
    have hr8 : 0 < F.scale j / 8 := by positivity
    have hreal : nk1HorizontalCb n * F.scale j ^ m ≤
        (omega m).toReal * (F.scale j / 8) ^ m := by
      calc nk1HorizontalCb n * F.scale j ^ m
          ≤ (omega m).toReal / 8 ^ m * F.scale j ^ m :=
            mul_le_mul_of_nonneg_right (nk1_horizontalCb_le hmn) (by positivity)
        _ = (omega m).toReal * (F.scale j / 8) ^ m := by
            rw [div_pow]; ring
    calc ENNReal.ofReal (nk1HorizontalCb n * F.scale j ^ m)
        ≤ ENNReal.ofReal ((omega m).toReal * (F.scale j / 8) ^ m) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = volume (Metric.ball u (F.scale j / 8)) := by
          rw [nk1_ofReal_omega_mul _ _ hr8.le, volume_spatial_ball _ hr8]
      _ ≤ ((volume : Measure (Spatial m)).restrict (Metric.ball (0 : Spatial m) (4 * Cs * R)))
            (G ⁻¹' Metric.ball (F.center j a).1 (F.scale j)) := by
          rw [Measure.restrict_apply' Metric.isOpen_ball.measurableSet]
          apply measure_mono
          intro v hv
          refine ⟨?_, hsub hv⟩
          rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
          have h1 := hGd v u
          have h2 : dist v u < F.scale j / 8 := hv
          have h3 := norm_sub_le_norm_sub_add_norm_sub (G v) (G u) (F.center j a).1
          rw [← dist_eq_norm (G v) (G u)] at h3
          linarith
      _ ≤ _ := Measure.le_map_apply hmeas.aemeasurable _

/-- Buffered reference, horizontal form: the supplied chart is the witness, `u₀ = 0`,
`C_r = 4 C_*`. The type is that of `NeckHubTree.horizontalBufferedReference_of_chart`. -/
theorem horizontalBufferedReference_of_chart_proof (n : ℕ) :
    ∃ cb : ℝ, 0 < cb ∧ ∀ Cs : ℝ, 0 < Cs → ∃ Cr Cm : ℝ, 0 < Cr ∧ 0 < Cm ∧
      ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (N : ℕ) (y : Spatial n) (R : ℝ)
        (G : Spatial m → Spatial n) (x : Spatial n) (U : Spatial m →ₗᵢ[ℝ] Spatial n),
        0 < R →
        (∀ u v : Spatial m,
          4 / 5 * ‖u - v‖ ≤ ‖G u - G v‖ ∧ ‖G u - G v‖ ≤ 11 / 10 * ‖u - v‖) →
        (∀ u : Spatial m, ‖G u - (x + U u)‖ ≤ Cs * R) →
        ‖x - y‖ ≤ Cs * R →
        F.initialRadius ≤ Cs * R →
        (∀ j ≤ N, ∀ a ∈ F.index j, (F.center j a).1 ∈ Metric.ball y (Cs * R)) →
        (∀ j ≤ N, ∀ a ∈ F.index j, ∃ u : Spatial m,
          ‖G u - (F.center j a).1‖ ≤ F.scale j / 4) →
        F.HasHorizontalBufferedReference R Cr Cm cb N := by
  refine ⟨nk1HorizontalCb n, nk1_horizontalCb_pos n, fun Cs hCs =>
    ⟨4 * Cs, nk1HorizontalCm n Cs, by positivity, nk1_horizontalCm_pos n hCs, ?_⟩⟩
  intro m ι F N y R G x U hR hG hGx hx hr0 hcen hreach
  exact nk1_horizontal_core F N y R Cs G x U hCs hR hG hGx hx hr0 hcen hreach

end NeckHubTree

end ParabolicRectifiability
