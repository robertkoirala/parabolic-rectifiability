import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalCoarsePieces
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry
import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # Coarse scales of the horizontal temporal energy

Proof of `ba1_horizontal_coarse`, under the name `ba1_horizontal_coarse_proof` with the
statement type. The interpolation conclusion enters as the hypothesis `hinterp`
of the statement type.

Proof idea. Put `d = dist(·, D)`, `κ = C₁ L²` (`C₁` the interpolation constant of `hinterp`) and
`c₀ = 11 √k`.

1. **Reduction** (`b1hcoa_reduction`). On the coarse set `E_r = D ∪ ⋃_{ℓ_Q ≤ r} face Q`,
   `d ≤ c₀ r` (`b1hcoa_infDist_le_of_mem_face`; `d = 0` on `D`). Drop the time restriction
   (`{|v-u| < Lr, |T(v)-T(u)| < r²} ⊆ B(u,Lr)`) and split through the interpolation `h`:
   `|T(v) - T(u)| ≤ κ d(v)² + |h(v) - h(u)| + κ d(u)²`. The domain part and the face parts
   (disjoint Borel faces) are each bounded by the integral over `B(b,R)` of the cut-off
   majorant, so the left side is at most twice it.
2. **Coarse estimate** (`b1hcoa_coarse_main`): plateau errors
   by Tonelli and `∫ d² ∫_{d/(c₀+L)}^R r^{-3} dr`; smooth difference by the
   fundamental theorem of calculus along segments, translation of the centre variable
   `u ↦ u + s w` (Jacobian one) and `∫ d ∫_{d/(c₀+L)}^R r^{-2} dr`; all over `B(b,(1+L)R)`;
   zero-distance points contribute zero before scale integration; no logarithmic loss.

The constant is `C = 2 Y ω² (1+L)^k + 1` with `Y = b1hcoa_const k (C₁ L²) L (11 √k)` and
`ω = |B(0,1)|` in `ℝ^k`; it depends only on `k` and `L` (through `C₁ = C₁(k)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **Reduction to the coarse majorant.** If `F ≤ K` at positive scales, the domain part (all
scales) and the face parts (scales `r ≥ ℓ_Q`) of the scale integral of `F` are at most twice
the integral over `B(b,R)` of `1_{d(u) ≤ 11 √k r} K(u,r)`. -/
theorem b1hcoa_reduction {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L) (b : Spatial k)
    (R : ℝ) (F K : Spatial k → ℝ → ℝ≥0∞) (hK : ∀ u r, 0 < r → F u r ≤ K u r) :
    (∫⁻ u in Metric.ball b R ∩ H.domain, ∫⁻ r in Ioo 0 R, F u r ∂scaleMeasure) +
      (∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
        ∫⁻ r in Ico (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) R, F u r ∂scaleMeasure) ≤
      2 * ∫⁻ u in Metric.ball b R, ∫⁻ r in Ioo 0 R,
        (if Metric.infDist u H.domain ≤ 11 * Real.sqrt k * r then K u r else 0)
          ∂scaleMeasure := by
  have hDm : MeasurableSet H.domain := H.domain_compact.isClosed.measurableSet
  have h1 : ∫⁻ u in Metric.ball b R ∩ H.domain, ∫⁻ r in Ioo 0 R, F u r ∂scaleMeasure ≤
      ∫⁻ u in Metric.ball b R, ∫⁻ r in Ioo 0 R,
        (if Metric.infDist u H.domain ≤ 11 * Real.sqrt k * r then K u r else 0)
          ∂scaleMeasure := by
    refine (setLIntegral_mono' (measurableSet_ball.inter hDm) fun u hu => ?_).trans
      (lintegral_mono_set inter_subset_left)
    refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
    have hc : Metric.infDist u H.domain ≤ 11 * Real.sqrt k * r := by
      rw [Metric.infDist_zero_of_mem hu.2]
      exact mul_nonneg (by positivity) hr.1.le
    rw [ite_eq_left hc]
    exact hK u r hr.1
  have h2 : (∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
        ∫⁻ r in Ico (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) R, F u r ∂scaleMeasure) ≤
      ∫⁻ u in Metric.ball b R, ∫⁻ r in Ioo 0 R,
        (if Metric.infDist u H.domain ≤ 11 * Real.sqrt k * r then K u r else 0)
          ∂scaleMeasure := by
    calc (∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
          ∫⁻ r in Ico (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) R, F u r ∂scaleMeasure)
        ≤ ∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i, ∫⁻ r in Ioo 0 R,
            (if Metric.infDist u H.domain ≤ 11 * Real.sqrt k * r then K u r else 0)
              ∂scaleMeasure := by
          refine ENNReal.tsum_le_tsum fun i =>
            setLIntegral_mono' (measurableSet_ball.inter (H.face_measurable i)) fun u hu => ?_
          refine (setLIntegral_mono' measurableSet_Ico fun r hr => ?_).trans
            (lintegral_mono_set ?_)
          · rw [ite_eq_left (b1hcoa_infDist_le_of_mem_face H i hu.2 hr.1)]
            exact hK u r ((b1hcoa_side_pos H i).trans_le hr.1)
          · exact fun r hr => ⟨(b1hcoa_side_pos H i).trans_le hr.1, hr.2⟩
      _ = ∫⁻ u in ⋃ i : H.cubeIndex, Metric.ball b R ∩ H.face i, ∫⁻ r in Ioo 0 R,
            (if Metric.infDist u H.domain ≤ 11 * Real.sqrt k * r then K u r else 0)
              ∂scaleMeasure :=
          (lintegral_iUnion (fun i => measurableSet_ball.inter (H.face_measurable i))
            (fun i j hij => Disjoint.mono inter_subset_right inter_subset_right
              (H.face_disjoint i j hij)) _).symm
      _ ≤ _ := lintegral_mono_set (iUnion_subset fun _ => inter_subset_left)
  exact (add_le_add h1 h2).trans_eq (two_mul _).symm

/-- The temporal cost with the time restriction is at most the coarse majorant: drop the time
restriction and split `|T(v) - T(u)|` through the interpolation `h`. -/
theorem b1hcoa_cost_le_majorant {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L)
    {h : Spatial k → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hT : ∀ u, |H.height u - h u| ≤ κ * Metric.infDist u H.domain ^ 2) (u : Spatial k) (r : ℝ) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
        (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
          ENNReal.ofReal |H.height v - H.height u|) ≤
      b1hcoa_majorant (fun x => Metric.infDist x H.domain) h κ L u r := by
  unfold b1hcoa_majorant
  refine mul_le_mul_right ((lintegral_mono_set fun v hv => Metric.mem_ball.2 hv.1).trans
    (lintegral_mono fun v => ?_)) _
  have hnn1 : 0 ≤ κ * Metric.infDist v H.domain ^ 2 := mul_nonneg hκ (sq_nonneg _)
  have hnn3 : 0 ≤ κ * Metric.infDist u H.domain ^ 2 := mul_nonneg hκ (sq_nonneg _)
  have hreal : |H.height v - H.height u| ≤
      κ * Metric.infDist v H.domain ^ 2 + |h v - h u| + κ * Metric.infDist u H.domain ^ 2 := by
    have e : H.height v - H.height u =
        (H.height v - h v) + (h v - h u) + (h u - H.height u) := by ring
    have h3 := abs_add_le ((H.height v - h v) + (h v - h u)) (h u - H.height u)
    have h4 := abs_add_le (H.height v - h v) (h v - h u)
    have h1 := hT v
    have h2 := hT u
    rw [abs_sub_comm (h u)] at h3
    rw [e]
    linarith
  calc ENNReal.ofReal |H.height v - H.height u|
      ≤ ENNReal.ofReal (κ * Metric.infDist v H.domain ^ 2 + |h v - h u| +
          κ * Metric.infDist u H.domain ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (κ * Metric.infDist v H.domain ^ 2) + ENNReal.ofReal |h v - h u| +
          ENNReal.ofReal (κ * Metric.infDist u H.domain ^ 2) := by
        rw [ENNReal.ofReal_add (add_nonneg hnn1 (abs_nonneg _)) hnn3,
          ENNReal.ofReal_add hnn1 (abs_nonneg _)]

/-- **`ba1_horizontal_coarse`**, with the statement type: the coarse
part of the temporal energy of a horizontal reference is at most `C R^k`, `C = C(k, L)`. -/
theorem ba1_horizontal_coarse_proof
    (hinterp : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (L : ℝ), 1 ≤ L →
      ∀ H : HorizontalReference n k L,
        ∃ h : Spatial k → ℝ, ContDiff ℝ 1 h ∧ (∀ u ∈ H.domain, h u = H.height u) ∧
          (∀ u, |H.height u - h u| ≤ C * L ^ 2 * Metric.infDist u H.domain ^ 2) ∧
          (∀ u, ‖fderiv ℝ h u‖ ≤ C * L ^ 2 * Metric.infDist u H.domain)) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ (H : HorizontalReference n k L) (b : Spatial k) (R : ℝ), 0 < R →
        (∫⁻ u in Metric.ball b R ∩ H.domain, ∫⁻ r in Ioo 0 R,
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) +
          (∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
            ∫⁻ r in Ico (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) R,
              (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
                (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                  ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) ≤
          ENNReal.ofReal (C * R ^ k) := by
  intro n k L hL
  obtain ⟨C₁, hC₁, hint⟩ := hinterp k
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hκ : 0 ≤ C₁ * L ^ 2 := mul_nonneg hC₁.le (sq_nonneg L)
  have hc₀ : 0 ≤ 11 * Real.sqrt k := by positivity
  have hY0 : 0 ≤ b1hcoa_const k (C₁ * L ^ 2) L (11 * Real.sqrt k) :=
    b1hcoa_const_nonneg k hκ hL0.le hc₀
  obtain ⟨ω, hω0, hW⟩ : ∃ x : ℝ, 0 ≤ x ∧
      volume (Metric.ball (0 : Spatial k) 1) = ENNReal.ofReal x :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal (b1hcoa_volume_unitBall_ne_top k)).symm⟩
  have hX0 : 0 ≤ 2 * b1hcoa_const k (C₁ * L ^ 2) L (11 * Real.sqrt k) * ω * ω * (1 + L) ^ k :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hY0) hω0) hω0)
      (pow_nonneg (by linarith) k)
  refine ⟨2 * b1hcoa_const k (C₁ * L ^ 2) L (11 * Real.sqrt k) * ω * ω * (1 + L) ^ k + 1,
    by linarith, fun H b R hR => ?_⟩
  obtain ⟨h, hh, -, hT, hgrad⟩ := hint n L hL H
  have hmain := b1hcoa_coarse_main (d := fun x => Metric.infDist x H.domain)
    (Metric.continuous_infDist_pt _) (fun _ => Metric.infDist_nonneg)
    (fun _ _ => Metric.infDist_le_infDist_add_dist) hh (κ := C₁ * L ^ 2) hκ hgrad b hR hL0 hc₀
  rw [hW] at hmain
  have hRk : 0 ≤ R ^ k := pow_nonneg hR.le k
  have hP0 : 0 ≤ ((1 + L) * R) ^ k := pow_nonneg (mul_nonneg (by linarith) hR.le) k
  calc _ ≤ 2 * ∫⁻ u in Metric.ball b R, ∫⁻ r in Ioo 0 R,
        (if Metric.infDist u H.domain ≤ 11 * Real.sqrt k * r then
          b1hcoa_majorant (fun x => Metric.infDist x H.domain) h (C₁ * L ^ 2) L u r else 0)
          ∂scaleMeasure :=
        b1hcoa_reduction H b R _ _ fun u r _ => b1hcoa_cost_le_majorant H hκ hT u r
    _ ≤ 2 * (ENNReal.ofReal (b1hcoa_const k (C₁ * L ^ 2) L (11 * Real.sqrt k)) *
          ENNReal.ofReal ω * (ENNReal.ofReal (((1 + L) * R) ^ k) * ENNReal.ofReal ω)) :=
        mul_le_mul_right hmain _
    _ = ENNReal.ofReal (2 * (b1hcoa_const k (C₁ * L ^ 2) L (11 * Real.sqrt k) * ω *
          (((1 + L) * R) ^ k * ω))) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (mul_nonneg hY0 hω0), ENNReal.ofReal_mul hY0,
          ENNReal.ofReal_mul hP0, ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal ((2 * b1hcoa_const k (C₁ * L ^ 2) L (11 * Real.sqrt k) * ω * ω *
          (1 + L) ^ k + 1) * R ^ k) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_pow, add_mul, one_mul]
        linarith
