import ParabolicRectifiability.Analysis.ParabolicBMO
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.L2Space

/-! # Local vector mean oscillation

The actual average first cancels constant offsets. Averaging a pairwise tail
bound then controls its mean oscillation, while Cauchy--Schwarz controls the
square-integrable summand. Restriction to an intrinsic parabolic ball supplies
the positive finite volume. Global derivative representatives are not inputs
or conclusions of this local averaging module.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology

namespace ParabolicRectifiability.MeanOscillation

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure α} {f g a b : α → E}

/-- The norm is taken before averaging; the center is the actual vector average. -/
def oscillation (μ : Measure α) (f : α → E) : ℝ :=
  ⨍ x, ‖f x - ⨍ y, f y ∂μ‖ ∂μ

omit [CompleteSpace E] in
theorem norm_average_le (f : α → E) : ‖⨍ x, f x ∂μ‖ ≤ ⨍ x, ‖f x‖ ∂μ :=
  norm_integral_le_integral_norm f

theorem average_mono_real {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : f ≤ᵐ[μ] g) : (⨍ x, f x ∂μ) ≤ ⨍ x, g x ∂μ := by
  simp only [average_eq, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hf hg h)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

omit [CompleteSpace E] in
/-- A.e. replacement retains genuine integrability on both sides. -/
theorem oscillation_congr (_hf : Integrable f μ) (_hg : Integrable g μ)
    (h : f =ᵐ[μ] g) : oscillation μ f = oscillation μ g := by
  unfold oscillation
  rw [average_congr h]
  apply average_congr
  filter_upwards [h] with x hx
  rw [hx]

section FinitePositive
variable [IsFiniteMeasure μ] [NeZero μ]

theorem mass_pos : 0 < μ.real univ :=
  ENNReal.toReal_pos (measure_univ_ne_zero.mpr (NeZero.ne μ)) (measure_ne_top _ _)

omit [NormedSpace ℝ E] [CompleteSpace E] [NeZero μ] in
theorem integrable_deviation (hf : Integrable f μ) (c : E) :
    Integrable (fun x => ‖f x-c‖) μ := (hf.sub (integrable_const c)).norm

/-- Any constant center costs at most a factor two. -/
theorem oscillation_le_twice_average_dist (hf : Integrable f μ) (c : E) :
    oscillation μ f ≤ 2 * ⨍ x, ‖f x-c‖ ∂μ := by
  have hm : ‖(⨍ x, f x ∂μ)-c‖ ≤ ⨍ x, ‖f x-c‖ ∂μ := by
    calc
      _ = ‖⨍ x, f x-c ∂μ‖ := by rw [average_fun_sub hf (integrable_const c), average_const]
      _ ≤ _ := norm_average_le _
  have hp : ∀ x, ‖f x-(⨍ y, f y ∂μ)‖ ≤ ‖f x-c‖ + ‖(⨍ y, f y ∂μ)-c‖ := by
    intro x
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (f x-c) ((⨍ y, f y ∂μ)-c)
  have h := average_mono_real (integrable_deviation hf _)
    ((integrable_deviation hf c).add (integrable_const _)) (Eventually.of_forall hp)
  simp only [Pi.add_apply] at h
  rw [average_fun_add (integrable_deviation hf c) (integrable_const _), average_const] at h
  unfold oscillation
  linarith

/-- Constant offsets of arbitrary size disappear from the actual mean oscillation. -/
theorem oscillation_add_const (hf : Integrable f μ) (c : E) :
    oscillation μ (fun x => f x+c) = oscillation μ f := by
  unfold oscillation
  rw [average_fun_add hf (integrable_const c), average_const]
  apply average_congr
  exact Eventually.of_forall fun x => by simp

omit [CompleteSpace E] [IsFiniteMeasure μ] [NeZero μ] in
/-- Positive finite rescaling of the measure preserves the actual average. -/
theorem average_smul_measure (_hf : Integrable f μ) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    (⨍ x, f x ∂c • μ) = ⨍ x, f x ∂μ := by
  have hc : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc0,hct⟩
  simp only [average_eq, Measure.real, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, integral_smul_measure, smul_smul,
    mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc, mul_one]

omit [CompleteSpace E] [NeZero μ] in
/-- In particular mean oscillation is unchanged when positive mass is rescaled. -/
theorem oscillation_smul_measure (hf : Integrable f μ) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hct : c ≠ ∞) : oscillation (c • μ) f = oscillation μ f := by
  unfold oscillation
  rw [average_smul_measure hf c hc0 hct,
    average_smul_measure (integrable_deviation hf _) c hc0 hct]

/-- Tail control before the last average: averaging the actual pairwise difference. -/
theorem deviation_le_of_ae_pairwise (hb : Integrable b μ) {B : ℝ}
    (hpair : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ‖b x-b y‖ ≤ B) :
    ∀ᵐ x ∂μ, ‖b x-(⨍ y, b y ∂μ)‖ ≤ B := by
  filter_upwards [hpair] with x hx
  calc
    _ = ‖⨍ y, b x-b y ∂μ‖ := by rw [average_fun_sub (integrable_const _) hb, average_const]
    _ ≤ ⨍ y, ‖b x-b y‖ ∂μ := norm_average_le _
    _ ≤ ⨍ _y, B ∂μ := average_mono_real ((integrable_const _).sub hb).norm
      (integrable_const B) hx
    _ = B := average_const μ B

/-- An almost-everywhere pairwise oscillation bound controls the tail mean. -/
theorem oscillation_le_of_ae_pairwise (hb : Integrable b μ) {B : ℝ}
    (hpair : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ‖b x-b y‖ ≤ B) : oscillation μ b ≤ B := by
  calc
    _ ≤ ⨍ _x, B ∂μ := average_mono_real (integrable_deviation hb _)
      (integrable_const B) (deviation_le_of_ae_pairwise hb hpair)
    _ = B := average_const μ B

/-- Finite measure supplies the Fubini premises for a genuine product-a.e. bound. -/
theorem oscillation_le_of_ae_prod (hb : Integrable b μ) {B : ℝ}
    (hpair : ∀ᵐ p ∂μ.prod μ, ‖b p.1-b p.2‖ ≤ B) : oscillation μ b ≤ B :=
  oscillation_le_of_ae_pairwise hb (ae_ae_of_ae_prod hpair)

omit [CompleteSpace E] [NeZero μ] in
/-- Actual average additivity gives subadditivity of vector mean oscillation. -/
theorem oscillation_add_le (ha : Integrable a μ) (hb : Integrable b μ) :
    oscillation μ (fun x => a x+b x) ≤ oscillation μ a + oscillation μ b := by
  unfold oscillation
  rw [average_fun_add ha hb]
  calc
    _ ≤ ⨍ x, (‖a x-(⨍ y, a y ∂μ)‖ + ‖b x-(⨍ y, b y ∂μ)‖) ∂μ := by
      apply average_mono_real (integrable_deviation (ha.add hb) _)
        ((integrable_deviation ha _).add (integrable_deviation hb _))
      exact Eventually.of_forall fun x => by
        simpa only [Pi.add_apply, add_sub_add_comm] using norm_add_le (a x-(⨍ y, a y ∂μ)) (b x-(⨍ y, b y ∂μ))
    _ = _ := average_fun_add (integrable_deviation ha _) (integrable_deviation hb _)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The precise finite-volume Cauchy--Schwarz normalization. -/
theorem average_norm_le_L2 (ha : MemLp a 2 μ) :
    (⨍ x, ‖a x‖ ∂μ) ≤ (μ.real univ)^(-1/2 : ℝ) * Real.sqrt (∫ x, ‖a x‖^2 ∂μ) := by
  have hv : 0 < μ.real univ := mass_pos
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp (fun x => ‖a x‖) (ENNReal.ofReal 2) μ by simpa using ha.norm)
    (show MemLp (fun _x : α => (1 : ℝ)) (ENNReal.ofReal 2) μ from memLp_const 1)
  have hcs : (∫ x, ‖a x‖ ∂μ) ≤ Real.sqrt (∫ x, ‖a x‖^2 ∂μ) * Real.sqrt (μ.real univ) := by
    simpa [Real.rpow_two, Real.sqrt_eq_rpow] using hh
  rw [average_eq, smul_eq_mul]
  calc
    _ ≤ (μ.real univ)⁻¹ * (Real.sqrt (∫ x, ‖a x‖^2 ∂μ) * Real.sqrt (μ.real univ)) :=
      mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hv.le)
    _ = ((μ.real univ)⁻¹ * Real.sqrt (μ.real univ)) * Real.sqrt (∫ x, ‖a x‖^2 ∂μ) := by ring
    _ = _ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hv]
      norm_num

/-- Local L2 plus pairwise tail oscillation, with the a.e. sum justified. -/
theorem oscillation_le_L2_add_pairwise (ha : MemLp a 2 μ) (hb : Integrable b μ)
    (hrep : g =ᵐ[μ] fun x => a x+b x) {B : ℝ} (_hB : 0 ≤ B)
    (hpair : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ‖b x-b y‖ ≤ B) :
    oscillation μ g ≤ 2 * (μ.real univ)^(-1/2 : ℝ) * Real.sqrt (∫ x, ‖a x‖^2 ∂μ) + B := by
  have ha1 : Integrable a μ := ha.integrable (by norm_num)
  have hg : Integrable g μ := (ha1.add hb).congr hrep.symm
  rw [oscillation_congr hg (ha1.add hb) hrep]
  have h₁ := oscillation_add_le ha1 hb
  have h₂ := oscillation_le_twice_average_dist ha1 (0 : E)
  simp only [sub_zero] at h₂
  have h₃ := average_norm_le_L2 ha
  have h₄ := oscillation_le_of_ae_pairwise hb hpair
  calc
    _ ≤ oscillation μ a + oscillation μ b := h₁
    _ ≤ 2 * (⨍ x, ‖a x‖ ∂μ) + B := add_le_add h₂ h₄
    _ ≤ 2 * ((μ.real univ)^(-1/2 : ℝ) * Real.sqrt (∫ x, ‖a x‖^2 ∂μ)) + B :=
      add_le_add (mul_le_mul_of_nonneg_left h₃ (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ = _ := by ring

/-- The local mean-oscillation bound under a product-a.e. pairwise tail hypothesis. -/
theorem oscillation_le_L2_add_prod (ha : MemLp a 2 μ) (hb : Integrable b μ)
    (hrep : g =ᵐ[μ] fun x => a x+b x) {B : ℝ} (hB : 0 ≤ B)
    (hpair : ∀ᵐ p ∂μ.prod μ, ‖b p.1-b p.2‖ ≤ B) :
    oscillation μ g ≤ 2 * (μ.real univ)^(-1/2 : ℝ) * Real.sqrt (∫ x, ‖a x‖^2 ∂μ) + B :=
  oscillation_le_L2_add_pairwise ha hb hrep hB (ae_ae_of_ae_prod hpair)

end FinitePositive

omit [CompleteSpace E] in
/-- A restricted average is exactly the normalized integral used by BMO. -/
theorem oscillation_restrict_eq (μ : Measure α) (Q : Set α) (g : α → E) :
    oscillation (μ.restrict Q) g =
      (∫ x in Q, ‖g x-(μ.real Q)⁻¹ • ∫ y in Q, g y ∂μ‖ ∂μ) / μ.real Q := by
  simp only [oscillation, average_eq, measureReal_restrict_apply_univ, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

/-- Measurable-set assembly derives the finite-measure and nonzero instances. -/
theorem oscillation_restrict_le_L2_add (Q : Set α) (_hQ : MeasurableSet Q)
    (hQ0 : 0 < μ Q) (hQt : μ Q < ∞)
    (ha : MemLp a 2 (μ.restrict Q)) (hb : IntegrableOn b Q μ)
    (hrep : g =ᵐ[μ.restrict Q] fun x => a x+b x) {B : ℝ} (hB : 0 ≤ B)
    (hpair : ∀ᵐ p ∂(μ.restrict Q).prod (μ.restrict Q), ‖b p.1-b p.2‖ ≤ B) :
    oscillation (μ.restrict Q) g ≤
      2 * (μ.real Q)^(-1/2 : ℝ) * Real.sqrt (∫ x in Q, ‖a x‖^2 ∂μ) + B := by
  let : IsFiniteMeasure (μ.restrict Q) := ⟨by simpa using hQt⟩
  let : NeZero (μ.restrict Q) := ⟨fun h => hQ0.ne' (restrict_eq_zero.mp h)⟩
  simpa only [measureReal_restrict_apply_univ] using oscillation_le_L2_add_prod ha hb hrep hB hpair

/-- The same bound from pointwise tail data on `Q`. -/
theorem oscillation_restrict_le_L2_add_of_pairwise (Q : Set α) (hQ : MeasurableSet Q)
    (hQ0 : 0 < μ Q) (hQt : μ Q < ∞)
    (ha : MemLp a 2 (μ.restrict Q)) (hb : IntegrableOn b Q μ)
    (hrep : g =ᵐ[μ.restrict Q] fun x => a x+b x) {B : ℝ} (hB : 0 ≤ B)
    (hpair : ∀ x ∈ Q, ∀ y ∈ Q, ‖b x-b y‖ ≤ B) :
    oscillation (μ.restrict Q) g ≤
      2 * (μ.real Q)^(-1/2 : ℝ) * Real.sqrt (∫ x in Q, ‖a x‖^2 ∂μ) + B := by
  let : IsFiniteMeasure (μ.restrict Q) := ⟨by simpa using hQt⟩
  let : NeZero (μ.restrict Q) := ⟨fun h => hQ0.ne' (restrict_eq_zero.mp h)⟩
  have hp : ∀ᵐ x ∂μ.restrict Q, ∀ᵐ y ∂μ.restrict Q, ‖b x-b y‖ ≤ B := by
    filter_upwards [ae_restrict_mem hQ] with x hx
    filter_upwards [ae_restrict_mem hQ] with y hy
    exact hpair x hx y hy
  simpa only [measureReal_restrict_apply_univ] using oscillation_le_L2_add_pairwise ha hb hrep hB hp

end ParabolicRectifiability.MeanOscillation

namespace ParabolicRectifiability
open MeanOscillation

/-- The existing intrinsic volume is positive and finite at every positive radius. -/
theorem intrinsicBall_volume_pos_lt_top {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p : SubspaceSpace W) {r : ℝ} (hr : 0 < r) :
    0 < intrinsicParabolicVolume W (Metric.ball p r) ∧
      intrinsicParabolicVolume W (Metric.ball p r) < ∞ := by
  rw [intrinsicParabolicVolume_ball W p r hr]
  constructor
  · have ho := omega_pos (Module.finrank ℝ W)
    have hr' := ENNReal.ofReal_pos.mpr hr
    positivity
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (omega_lt_top _))
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)

/-- The local vector inequality with the actual intrinsic-ball average used in BMO. -/
theorem parabolicBall_meanOscillation_le_L2_add {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p : SubspaceSpace W) {r : ℝ} (hr : 0 < r)
    {g a b : SubspaceSpace W → W.orthogonal}
    (ha : MemLp a 2 ((intrinsicParabolicVolume W).restrict (Metric.ball p r)))
    (hb : IntegrableOn b (Metric.ball p r) (intrinsicParabolicVolume W))
    (hrep : g =ᵐ[(intrinsicParabolicVolume W).restrict (Metric.ball p r)] fun x => a x+b x)
    {B : ℝ} (hB : 0 ≤ B)
    (hpair : ∀ᵐ xy ∂((intrinsicParabolicVolume W).restrict (Metric.ball p r)).prod
      ((intrinsicParabolicVolume W).restrict (Metric.ball p r)), ‖b xy.1-b xy.2‖ ≤ B) :
    (∫ x in Metric.ball p r, ‖g x-parabolicBallAverage W g p r‖ ∂intrinsicParabolicVolume W) /
      (intrinsicParabolicVolume W).real (Metric.ball p r) ≤
      2 * ((intrinsicParabolicVolume W).real (Metric.ball p r))^(-1/2 : ℝ) *
        Real.sqrt (∫ x in Metric.ball p r, ‖a x‖^2 ∂intrinsicParabolicVolume W) + B := by
  have hv := intrinsicBall_volume_pos_lt_top W p hr
  have h := oscillation_restrict_le_L2_add (Metric.ball p r) Metric.isOpen_ball.measurableSet
    hv.1 hv.2 ha hb hrep hB hpair
  simpa only [oscillation_restrict_eq, parabolicBallAverage, Measure.real] using h

end ParabolicRectifiability
