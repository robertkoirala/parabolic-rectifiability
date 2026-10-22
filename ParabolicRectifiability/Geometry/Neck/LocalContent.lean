import ParabolicRectifiability.Geometry.Neck.ContentBound
import ParabolicRectifiability.Geometry.Neck.Conclusions
import ParabolicRectifiability.Metric.BaseVolume

/-!
# Local content for vertical and horizontal neck regions

The local content bounds for necks:
`vertical_localContent_of_parametrization` and `horizontal_localContent_of_parametrization`.
Both are derived from the general content lemma
`nk4_localContent_of_distortion` with distortion `L = 2`, Hausdorff ball constant `D = 10^k`
and packing radius factor `a = c₀/8`:

* vertical: parameter space `ℝ^{k-2} × ℝ` with `parabolicVolume (k-2)`, whose balls have volume
  `2 ω_{k-2} r^k`; the map is the full time-preserving map restricted to the compact `A`;
* horizontal: parameter space `ℝ^k` with Lebesgue volume, balls of volume `ω_k r^k`; the map
  `u ↦ (F u, τ u)` is defined only on `A`.

The resulting constant `80^k + (1 + 32/c₀)^k` is bounded uniformly over the available
dimensions `k ≤ n + 2` by `C(n, c₀) = 80^{n+2} + (1 + 32/c₀)^{n+2}`.
-/

noncomputable section

namespace ParabolicRectifiability

namespace NeckHubTree

open MeasureTheory Set Metric
open scoped ENNReal NNReal

universe u

/-- The uniform content constant `C(n, c₀) = 80^{n+2} + (1 + 32/c₀)^{n+2}`. -/
def nk4_contentConstant (n : ℕ) (c₀ : ℝ) : ℝ := 80 ^ (n + 2) + (1 + 32 / c₀) ^ (n + 2)

theorem nk4_one_le_contentConstant (n : ℕ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    1 ≤ nk4_contentConstant n c₀ := by
  unfold nk4_contentConstant
  have h1 : (1 : ℝ) ≤ 80 ^ (n + 2) := one_le_pow₀ (by norm_num)
  have h2 : (0 : ℝ) ≤ (1 + 32 / c₀) ^ (n + 2) := by positivity
  linarith

/-- The constant of the general content lemma at `L = 2`, `D = 10^k` is at most the uniform
constant whenever `k ≤ n + 2`. -/
theorem nk4_distortion_two_constant_le {n k : ℕ} (hk : k ≤ n + 2) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    (2 : ℝ) ^ k * 10 ^ k * (2 * 2) ^ k + ((2 * 2 + c₀ / (4 * 2)) / (c₀ / (4 * 2))) ^ k ≤
      nk4_contentConstant n c₀ := by
  unfold nk4_contentConstant
  have h80 : (2 : ℝ) ^ k * 10 ^ k * (2 * 2) ^ k = 80 ^ k := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  have hne : c₀ / (4 * 2) ≠ 0 := by positivity
  have hbase : (2 * 2 + c₀ / (4 * 2)) / (c₀ / (4 * 2)) = 1 + 32 / c₀ := by
    rw [add_div, div_self hne, div_div_eq_mul_div]
    ring
  rw [h80, hbase]
  have hb : (1 : ℝ) ≤ 1 + 32 / c₀ := le_add_of_nonneg_right (by positivity)
  exact add_le_add (pow_le_pow_right₀ (by norm_num) hk) (pow_le_pow_right₀ hb hk)

/-- `10^k (2ω)⁻¹ (2ω r^k) = 10^k r^k` for a positive finite coefficient. -/
theorem nk4_cancel_ball_coefficient (k : ℕ) {w : ℝ≥0∞} (hw0 : w ≠ 0) (hwtop : w ≠ ∞)
    {r : ℝ} (hr : 0 < r) :
    (10 : ℝ≥0∞) ^ k * w⁻¹ * (w * ENNReal.ofReal r ^ k) = ENNReal.ofReal (10 ^ k * r ^ k) := by
  rw [mul_assoc, ENNReal.inv_mul_cancel_left hw0 hwtop,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_pow hr.le, ENNReal.ofReal_ofNat]

/-- **Local content, vertical parameter space `ℝ^{k-2} × ℝ`**, with the type of
`vertical_localContent_of_parametrization`. -/
theorem vertical_localContent_of_parametrization_proof (n : ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {k : ℕ} {ι : Type u} {q : Space n} {R Cd Cs σ δ E κ θ γ : ℝ}
        (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ),
        N.HasVerticalParametrization 2 → N.HasLocalContentBound C := by
  refine ⟨nk4_contentConstant n c₀, nk4_one_le_contentConstant n hc₀, ?_⟩
  intro k ι q R Cd Cs σ δ E κ θ γ N hpar z s hs
  obtain ⟨G, A, hbi, -, himg⟩ := hpar
  have hk : 2 ≤ k ∧ k ≤ n + 2 := N.available
  have hk2 : k - 2 + 2 = k := Nat.sub_add_cancel hk.1
  have hw0 : (2 * omega (k - 2)) ≠ 0 := mul_ne_zero two_ne_zero (omega_pos _).ne'
  have hwtop : (2 * omega (k - 2)) ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (omega_lt_top _).ne
  have hball : ∀ (x : Space (k - 2)) (r : ℝ), 0 < r →
      parabolicVolume (k - 2) (ball x r) = 2 * omega (k - 2) * ENNReal.ofReal r ^ k := by
    intro x r hr
    rw [parabolicVolume_ball x r hr, hk2]
  have hH : ∀ (x : Space (k - 2)) (r : ℝ), 0 < r →
      (Measure.hausdorffMeasure (k : ℝ) : Measure (Space (k - 2))) (ball x r) ≤
        ENNReal.ofReal (10 ^ k * r ^ k) := by
    intro x r hr
    have h1 := (parabolic_hausdorff_comparison (k - 2) (ball x r)).2
    rw [hausdorffP_eq, hk2, hball x r hr] at h1
    refine h1.trans (le_of_eq ?_)
    unfold verticalHausdorffConstant
    rw [hk2]
    exact nk4_cancel_ball_coefficient k hw0 hwtop hr
  have hψ : ∀ u v : A, (2 : ℝ)⁻¹ * dist u v ≤
      dist ((fun p : A => timePreservingMap G p) u) ((fun p : A => timePreservingMap G p) v) ∧
      dist ((fun p : A => timePreservingMap G p) u) ((fun p : A => timePreservingMap G p) v) ≤
        2 * dist u v := fun u v => hbi u v
  have hrange : range (fun p : A => timePreservingMap G p) = N.centers :=
    (image_eq_range _ _).symm.trans himg
  have hcen : ∀ c ∈ N.centers, c ∈ range (fun p : A => timePreservingMap G p) := by
    intro c hc
    rw [hrange]
    exact hc
  have hmain := nk4_localContent_of_distortion k (parabolicVolume (k - 2)) hw0 hwtop hball
    (by positivity) hH two_pos hc₀ (fun p : A => timePreservingMap G p) hψ (C₀ := N.core)
    (S := N.stopping) (fun c hc => hcen c hc.1) (fun c hc => hcen c hc.1) N.radius
    (fun c hc => hc.2)
    (fun c hc c' hc' hne => N.stop_separation c hc.1 c' hc'.1 hc.2 hc'.2 hne) z hs
  rw [hausdorffP_eq]
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right (nk4_distortion_two_constant_le hk.2 hc₀) (by positivity)

/-- **Local content, Euclidean parameter space `ℝ^k`**, with the type of
`horizontal_localContent_of_parametrization`. The parameter map is defined only on the compact
`A`; the packed balls are full balls of `ℝ^k`. -/
theorem horizontal_localContent_of_parametrization_proof (n : ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {k : ℕ} {ι : Type u} {q : Space n} {R Cd Cs σ δ E κ θ γ : ℝ}
        (N : NeckRegion n k .horizontal ι q R c₀ Cd Cs σ δ E κ θ γ),
        N.HasHorizontalParametrization 2 → N.HasLocalContentBound C := by
  refine ⟨nk4_contentConstant n c₀, nk4_one_le_contentConstant n hc₀, ?_⟩
  intro k ι q R Cd Cs σ δ E κ θ γ N hpar z s hs
  obtain ⟨G, -, A, τ, -, hψ, hrange⟩ := hpar
  have hk : 1 ≤ k ∧ k ≤ n := N.available
  have hw0 : omega k ≠ 0 := (omega_pos k).ne'
  have hwtop : omega k ≠ ∞ := (omega_lt_top k).ne
  have hball : ∀ (x : Spatial k) (r : ℝ), 0 < r →
      (volume : Measure (Spatial k)) (ball x r) = omega k * ENNReal.ofReal r ^ k :=
    fun x r hr => volume_spatial_ball x hr
  have hH : ∀ (x : Spatial k) (r : ℝ), 0 < r →
      (Measure.hausdorffMeasure (k : ℝ) : Measure (Spatial k)) (ball x r) ≤
        ENNReal.ofReal (10 ^ k * r ^ k) := by
    intro x r hr
    have h1 := (spatial_hausdorff_comparison k (ball x r)).2
    rw [volume_spatial_ball x hr] at h1
    refine h1.trans (le_of_eq ?_)
    unfold horizontalHausdorffConstant
    exact nk4_cancel_ball_coefficient k hw0 hwtop hr
  have hcen : ∀ c ∈ N.centers, c ∈ range (fun u : A => point (G u) (τ u)) := by
    intro c hc
    rw [hrange]
    exact hc
  have hmain := nk4_localContent_of_distortion k (volume : Measure (Spatial k)) hw0 hwtop hball
    (by positivity) hH two_pos hc₀ (fun u : A => point (G u) (τ u)) hψ (C₀ := N.core)
    (S := N.stopping) (fun c hc => hcen c hc.1) (fun c hc => hcen c hc.1) N.radius
    (fun c hc => hc.2)
    (fun c hc c' hc' hne => N.stop_separation c hc.1 c' hc'.1 hc.2 hc'.2 hne) z hs
  rw [hausdorffP_eq]
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right
    (nk4_distortion_two_constant_le (hk.2.trans (Nat.le_add_right n 2)) hc₀) (by positivity)

end NeckHubTree

end ParabolicRectifiability
