import ParabolicRectifiability.Characterization.Proofs.Fourier.EstimateStatements
import ParabolicRectifiability.Characterization.Proofs.Fourier.SpatialAffineMultiplier

/-! # The global spatial Fourier affine-square estimate

Scale-free global estimate underlying `ba1_spatial_affine_square_proof`.

**Competitor.** For a centre `u` and a scale `s > 0` test the affine map
`v ↦ (G(u) - B u) + B v`, `B = b1sas_grad G s u` the finite-difference gradient
`B_j = (G(u + s e_j) - G(u)) / s`. For `v = u + h` the residual
`G(v) - (G(u) - B u) - B v` is the finite combination of translate differences
`b1sas_resid G s h u` (`b1sas_resid_eq`), so the best affine error is bounded by the residual
energy `b1sas_residEnergy G u s = s^{-k-2} ∫_{B(0,s)} |b1sas_resid G s h u|² dh`; for vector
maps the competitor is taken coordinatewise (`b1sas_spatialAffineErrorSq_le`).

**Global estimate** (`b1sas_global_residual`, `b1sas_spatial_global`). Tonelli in `(u,s)` and
`(u,h)`, Plancherel for translate combinations (`b1sas_lintegral_comb_sq`), the residual
multiplier bound `|M_{s,h}(ξ)| ≤ K_k min(1, (s|ξ|)²)` for `‖h‖ < s`
(`b1sas_norm_mult_le_min`), the exact volume `|B(0,s)| = s^k |B(0,1)|` and the scale integral
`∫_0^∞ s^{-2} min(1, s²|ξ|²)² ds/s ≤ |ξ|²` give, for every measurable real `G ∈ L²(ℝ^k)`,
`∫_{ℝ^k} ∫_0^∞ residEnergy G u s ds/s du ≤ |B(0,1)| K_k² ∫ |ξ|² |Ĝ(ξ)|² dξ`,
and hence for `F : ℝ^k → ℝ^d` measurable with `L²` coordinates
`∫_{ℝ^k} ∫_0^∞ spatialAffineErrorSq F u s ds/s du ≤ |B(0,1)| K_k² ∑_i ∫ |ξ|² |F̂_i(ξ)|² dξ`.
With mathlib's phase `e^{-2πi⟨x,ξ⟩}`, `∫ |ξ|² |Ĝ|² = (4π²)⁻¹ ‖∇G‖₂²` for `G ∈ W^{1,2}`; the
form used for Lipschitz maps is the translate bound `b1sas_fourierEnergy_le`.
No smoothing kernel is used: the competitor is the finite-difference Taylor polynomial, whose
residual multiplier vanishes to second order at `ξ = 0` (it is the multiplier of the residual,
not of the competitor, that is small). All helpers carry the prefix `b1sas_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

variable {k : ℕ}

/-! ### The competitor and its residual -/

/-- The finite-difference gradient `B_j = (G(u + s e_j) - G(u)) / s` at the centre `u`. -/
def b1sas_grad (G : Spatial k → ℝ) (s : ℝ) (u : Spatial k) : Spatial k →L[ℝ] ℝ :=
  ∑ j : Fin k, ((G (u + s • b1sas_unit j) - G u) / s) • EuclideanSpace.proj j

theorem b1sas_grad_apply (G : Spatial k → ℝ) (s : ℝ) (u v : Spatial k) :
    b1sas_grad G s u v = ∑ j : Fin k, (G (u + s • b1sas_unit j) - G u) / s * v j := by
  simp [b1sas_grad]

/-- The residual `G(u + h) - G(u) - ∑_j (h_j / s) (G(u + s e_j) - G(u))`. -/
def b1sas_resid (G : Spatial k → ℝ) (s : ℝ) (h u : Spatial k) : ℝ :=
  ∑ i : Option (Fin k), b1sas_coef s h i * (G (u + b1sas_vec s h i) - G u)

theorem b1sas_resid_eq (G : Spatial k → ℝ) (s : ℝ) (h u : Spatial k) :
    G (u + h) - ((G u - b1sas_grad G s u u) + b1sas_grad G s u (u + h)) =
      b1sas_resid G s h u := by
  rw [map_add, b1sas_grad_apply G s u h]
  simp only [b1sas_resid, Fintype.sum_option, b1sas_coef, b1sas_vec, one_mul]
  have hs : ∑ j : Fin k, -(h j / s) * (G (u + s • b1sas_unit j) - G u) =
      -∑ j : Fin k, (G (u + s • b1sas_unit j) - G u) / s * h j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs]
  ring

/-- The residual energy `s^{-k-2} ∫_{B(0,s)} |b1sas_resid G s h u|² dh` of the competitor. -/
def b1sas_residEnergy (G : Spatial k → ℝ) (u : Spatial k) (s : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal s)⁻¹ ^ (k + 2) *
    ∫⁻ h in Metric.ball (0 : Spatial k) s, ‖b1sas_resid G s h u‖ₑ ^ 2

theorem b1sas_add_mem_ball {u h : Spatial k} {s : ℝ} :
    u + h ∈ Metric.ball u s ↔ h ∈ Metric.ball (0 : Spatial k) s := by
  rw [mem_ball_iff_norm, mem_ball_zero_iff, add_sub_cancel_left]

/-- Translation of the testing ball to the origin. -/
theorem b1sas_lintegral_ball_translate (G : Spatial k → ℝ) (u : Spatial k) (s : ℝ) :
    ∫⁻ v in Metric.ball u s, ‖G v - ((G u - b1sas_grad G s u u) + b1sas_grad G s u v)‖ₑ ^ 2 =
      ∫⁻ h in Metric.ball (0 : Spatial k) s, ‖b1sas_resid G s h u‖ₑ ^ 2 := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball,
    ← lintegral_add_left_eq_self ((Metric.ball u s).indicator fun v =>
      ‖G v - ((G u - b1sas_grad G s u u) + b1sas_grad G s u v)‖ₑ ^ 2) u]
  congr 1
  funext h
  by_cases hh : h ∈ Metric.ball (0 : Spatial k) s
  · rw [indicator_of_mem (b1sas_add_mem_ball.2 hh), indicator_of_mem hh, b1sas_resid_eq]
  · rw [indicator_of_notMem (fun h' => hh (b1sas_add_mem_ball.1 h')), indicator_of_notMem hh]

theorem b1sas_enorm_sq_eq_sum {d : ℕ} (x : Spatial d) : ‖x‖ₑ ^ 2 = ∑ i, ‖x i‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem b1sas_measurable_coord {d : ℕ} {F : Spatial k → Spatial d} (hF : Measurable F)
    (i : Fin d) : Measurable fun v => F v i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp hF

/-- The vector with coordinates `c`. -/
def b1sas_vecConst {d : ℕ} (c : Fin d → ℝ) : Spatial d := WithLp.toLp 2 c

theorem b1sas_vecConst_apply {d : ℕ} (c : Fin d → ℝ) (i : Fin d) :
    b1sas_vecConst c i = c i := rfl

/-- The linear map with coordinate functionals `B i`. -/
def b1sas_vecLin {d : ℕ} (B : Fin d → (Spatial k →L[ℝ] ℝ)) : Spatial k →L[ℝ] Spatial d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap ∘L ContinuousLinearMap.pi B

theorem b1sas_vecLin_apply {d : ℕ} (B : Fin d → (Spatial k →L[ℝ] ℝ)) (v : Spatial k)
    (i : Fin d) : b1sas_vecLin B v i = B i v := rfl

/-- The coordinatewise competitor. -/
theorem b1sas_competitor_coord {d : ℕ} (F : Spatial k → Spatial d) (u : Spatial k) (s : ℝ)
    (v : Spatial k) (i : Fin d) :
    (F v - (b1sas_vecConst (fun i => F u i - b1sas_grad (fun v => F v i) s u u) +
        b1sas_vecLin (fun i => b1sas_grad (fun v => F v i) s u) v)) i =
      F v i - ((F u i - b1sas_grad (fun v => F v i) s u u) +
        b1sas_grad (fun v => F v i) s u v) := by
  rw [PiLp.sub_apply, PiLp.add_apply, b1sas_vecConst_apply, b1sas_vecLin_apply]

/-- The constant part of the coordinatewise competitor. -/
def b1sas_cst {d : ℕ} (F : Spatial k → Spatial d) (u : Spatial k) (s : ℝ) : Spatial d :=
  b1sas_vecConst (fun i => F u i - b1sas_grad (fun v => F v i) s u u)

/-- The linear part of the coordinatewise competitor. -/
def b1sas_lin {d : ℕ} (F : Spatial k → Spatial d) (u : Spatial k) (s : ℝ) :
    Spatial k →L[ℝ] Spatial d :=
  b1sas_vecLin (fun i => b1sas_grad (fun v => F v i) s u)

/-- The squared coordinate error of the competitor at `v`. -/
def b1sas_coordErr {d : ℕ} (F : Spatial k → Spatial d) (u : Spatial k) (s : ℝ) (i : Fin d)
    (v : Spatial k) : ℝ≥0∞ :=
  ‖F v i - ((F u i - b1sas_grad (fun v => F v i) s u u) + b1sas_grad (fun v => F v i) s u v)‖ₑ ^ 2

theorem b1sas_competitor_enorm {d : ℕ} (F : Spatial k → Spatial d) (u : Spatial k) (s : ℝ)
    (v : Spatial k) :
    ‖F v - (b1sas_cst F u s + b1sas_lin F u s v)‖ₑ ^ 2 = ∑ i : Fin d, b1sas_coordErr F u s i v := by
  refine (b1sas_enorm_sq_eq_sum (F v - (b1sas_cst F u s + b1sas_lin F u s v))).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : (F v - (b1sas_cst F u s + b1sas_lin F u s v)) i =
      F v i - ((F u i - b1sas_grad (fun v => F v i) s u u) +
        b1sas_grad (fun v => F v i) s u v) :=
    b1sas_competitor_coord F u s v i
  exact congrArg (fun z : ℝ => ‖z‖ₑ ^ 2) hc

theorem b1sas_measurable_coordErr {d : ℕ} {F : Spatial k → Spatial d} (hF : Measurable F)
    (u : Spatial k) (s : ℝ) (i : Fin d) : Measurable (b1sas_coordErr F u s i) := by
  have hFi : Measurable fun v => F v i := b1sas_measurable_coord hF i
  have hg : Measurable fun v => b1sas_grad (fun v => F v i) s u v :=
    (b1sas_grad (fun v => F v i) s u).continuous.measurable
  have h : Measurable fun v => ‖F v i - ((F u i - b1sas_grad (fun v => F v i) s u u) +
      b1sas_grad (fun v => F v i) s u v)‖ₑ ^ 2 :=
    (hFi.sub (measurable_const.add hg)).enorm.pow_const 2
  exact h

theorem b1sas_lintegral_competitor {d : ℕ} {F : Spatial k → Spatial d} (hF : Measurable F)
    (u : Spatial k) (s : ℝ) :
    ∫⁻ v in Metric.ball u s, ‖F v - (b1sas_cst F u s + b1sas_lin F u s v)‖ₑ ^ 2 =
      ∑ i : Fin d, ∫⁻ v in Metric.ball u s, b1sas_coordErr F u s i v := by
  have h1 : ∫⁻ v in Metric.ball u s, ‖F v - (b1sas_cst F u s + b1sas_lin F u s v)‖ₑ ^ 2 =
      ∫⁻ v in Metric.ball u s, ∑ i : Fin d, b1sas_coordErr F u s i v :=
    lintegral_congr fun v => b1sas_competitor_enorm F u s v
  have h2 : ∫⁻ v in Metric.ball u s, ∑ i : Fin d, b1sas_coordErr F u s i v =
      ∑ i : Fin d, ∫⁻ v in Metric.ball u s, b1sas_coordErr F u s i v :=
    lintegral_finsetSum Finset.univ fun i _ => b1sas_measurable_coordErr hF u s i
  exact h1.trans h2

theorem b1sas_coordErr_ball {d : ℕ} (F : Spatial k → Spatial d) (u : Spatial k) (s : ℝ)
    (i : Fin d) :
    (ENNReal.ofReal s)⁻¹ ^ (k + 2) * ∫⁻ v in Metric.ball u s, b1sas_coordErr F u s i v =
      b1sas_residEnergy (fun v => F v i) u s := by
  have h : ∫⁻ v in Metric.ball u s, b1sas_coordErr F u s i v =
      ∫⁻ h in Metric.ball (0 : Spatial k) s, ‖b1sas_resid (fun v => F v i) s h u‖ₑ ^ 2 :=
    b1sas_lintegral_ball_translate (fun v => F v i) u s
  rw [h]
  rfl

theorem b1sas_errorSq_of_pos {d : ℕ} (F : Spatial k → Spatial d) (u : Spatial k) {s : ℝ}
    (hs : 0 < s) :
    spatialAffineErrorSq F u s = (ENNReal.ofReal s)⁻¹ ^ (k + 2) *
      ⨅ (a : Spatial d) (B : Spatial k →L[ℝ] Spatial d),
        ∫⁻ v in Metric.ball u s, ‖F v - (a + B v)‖ₑ ^ 2 := by
  unfold spatialAffineErrorSq
  exact ite_eq_left hs

theorem b1sas_errorSq_of_nonpos {d : ℕ} (F : Spatial k → Spatial d) (u : Spatial k) {s : ℝ}
    (hs : s ≤ 0) : spatialAffineErrorSq F u s = 0 := by
  unfold spatialAffineErrorSq
  exact ite_eq_right (not_lt.2 hs)

theorem b1sas_iInf_le_competitor {d : ℕ} (F : Spatial k → Spatial d) (u : Spatial k) (s : ℝ) :
    (⨅ (a : Spatial d) (B : Spatial k →L[ℝ] Spatial d),
        ∫⁻ v in Metric.ball u s, ‖F v - (a + B v)‖ₑ ^ 2) ≤
      ∫⁻ v in Metric.ball u s, ‖F v - (b1sas_cst F u s + b1sas_lin F u s v)‖ₑ ^ 2 :=
  (iInf_le (fun a : Spatial d => ⨅ B : Spatial k →L[ℝ] Spatial d,
      ∫⁻ v in Metric.ball u s, ‖F v - (a + B v)‖ₑ ^ 2) (b1sas_cst F u s)).trans
    (iInf_le (fun B : Spatial k →L[ℝ] Spatial d =>
      ∫⁻ v in Metric.ball u s, ‖F v - (b1sas_cst F u s + B v)‖ₑ ^ 2) (b1sas_lin F u s))

/-- **The pointwise competitor bound** (vector form, coordinatewise competitor). -/
theorem b1sas_spatialAffineErrorSq_le {d : ℕ} {F : Spatial k → Spatial d} (hF : Measurable F)
    (u : Spatial k) (s : ℝ) :
    spatialAffineErrorSq F u s ≤ ∑ i : Fin d, b1sas_residEnergy (fun v => F v i) u s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [b1sas_errorSq_of_nonpos F u hs]
    exact zero_le
  · calc spatialAffineErrorSq F u s
        = (ENNReal.ofReal s)⁻¹ ^ (k + 2) * ⨅ (a : Spatial d) (B : Spatial k →L[ℝ] Spatial d),
            ∫⁻ v in Metric.ball u s, ‖F v - (a + B v)‖ₑ ^ 2 := b1sas_errorSq_of_pos F u hs
      _ ≤ (ENNReal.ofReal s)⁻¹ ^ (k + 2) *
            ∫⁻ v in Metric.ball u s, ‖F v - (b1sas_cst F u s + b1sas_lin F u s v)‖ₑ ^ 2 :=
          mul_le_mul_right (b1sas_iInf_le_competitor F u s) _
      _ = (ENNReal.ofReal s)⁻¹ ^ (k + 2) *
            ∑ i : Fin d, ∫⁻ v in Metric.ball u s, b1sas_coordErr F u s i v :=
          congrArg (fun X => (ENNReal.ofReal s)⁻¹ ^ (k + 2) * X) (b1sas_lintegral_competitor hF u s)
      _ = ∑ i : Fin d, (ENNReal.ofReal s)⁻¹ ^ (k + 2) *
            ∫⁻ v in Metric.ball u s, b1sas_coordErr F u s i v :=
          Finset.mul_sum _ _ _
      _ = ∑ i : Fin d, b1sas_residEnergy (fun v => F v i) u s :=
          Finset.sum_congr rfl fun i _ => b1sas_coordErr_ball F u s i

/-! ### Measurability -/

theorem b1sas_measurable_resid {G : Spatial k → ℝ} (hG : Measurable G) :
    Measurable fun x : (Spatial k × ℝ) × Spatial k => b1sas_resid G x.1.2 x.2 x.1.1 := by
  unfold b1sas_resid
  refine Finset.measurable_sum _ fun i _ => ?_
  cases i with
  | none =>
    simp only [b1sas_coef, b1sas_vec, one_mul]
    exact (hG.comp (continuous_fst.fst.add continuous_snd).measurable).sub
      (hG.comp measurable_fst.fst)
  | some j =>
    simp only [b1sas_coef, b1sas_vec]
    have hc : Measurable fun x : (Spatial k × ℝ) × Spatial k => x.2 j :=
      ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp continuous_snd).measurable
    exact ((hc.div measurable_fst.snd).neg).mul
      ((hG.comp (continuous_fst.fst.add
        (continuous_fst.snd.smul continuous_const)).measurable).sub (hG.comp measurable_fst.fst))

theorem b1sas_measurableSet_graph :
    MeasurableSet {x : (Spatial k × ℝ) × Spatial k | x.2 ∈ Metric.ball (0 : Spatial k) x.1.2} := by
  simp only [mem_ball_zero_iff]
  exact measurableSet_lt continuous_snd.norm.measurable measurable_fst.snd

theorem b1sas_measurable_integrand {G : Spatial k → ℝ} (hG : Measurable G) :
    Measurable fun y : (Spatial k × ℝ) × Spatial k =>
      (Metric.ball (0 : Spatial k) y.1.2).indicator
        (fun h => ‖b1sas_resid G y.1.2 h y.1.1‖ₑ ^ 2) y.2 := by
  have heq : (fun y : (Spatial k × ℝ) × Spatial k =>
      (Metric.ball (0 : Spatial k) y.1.2).indicator
        (fun h => ‖b1sas_resid G y.1.2 h y.1.1‖ₑ ^ 2) y.2) =
      {y : (Spatial k × ℝ) × Spatial k | y.2 ∈ Metric.ball (0 : Spatial k) y.1.2}.indicator
        (fun y => ‖b1sas_resid G y.1.2 y.2 y.1.1‖ₑ ^ 2) := by
    funext y
    by_cases hy : y.2 ∈ Metric.ball (0 : Spatial k) y.1.2
    · rw [indicator_of_mem hy, indicator_of_mem
        (show y ∈ {y : (Spatial k × ℝ) × Spatial k |
          y.2 ∈ Metric.ball (0 : Spatial k) y.1.2} from hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem
        (show y ∉ {y : (Spatial k × ℝ) × Spatial k |
          y.2 ∈ Metric.ball (0 : Spatial k) y.1.2} from hy)]
  rw [heq]
  exact ((b1sas_measurable_resid hG).enorm.pow_const 2).indicator b1sas_measurableSet_graph

/-- The residual energy as a measurable function of `(u, s)`. -/
theorem b1sas_measurable_residEnergy {G : Spatial k → ℝ} (hG : Measurable G) :
    Measurable fun x : Spatial k × ℝ => b1sas_residEnergy G x.1 x.2 := by
  have heq : (fun x : Spatial k × ℝ => b1sas_residEnergy G x.1 x.2) = fun x =>
      (ENNReal.ofReal x.2)⁻¹ ^ (k + 2) * ∫⁻ h, (Metric.ball (0 : Spatial k) x.2).indicator
        (fun h => ‖b1sas_resid G x.2 h x.1‖ₑ ^ 2) h := by
    funext x
    rw [b1sas_residEnergy, lintegral_indicator measurableSet_ball]
  rw [heq]
  exact ((ENNReal.measurable_ofReal.comp measurable_snd).inv.pow_const _).mul
    (b1sas_measurable_integrand hG).lintegral_prod_right'

/-! ### Volumes of the testing balls -/

theorem b1sas_volume_ball_one_lt_top :
    volume (Metric.ball (0 : Spatial k) 1) < ⊤ :=
  MeasureTheory.measure_ball_lt_top

theorem b1sas_volume_ball {s : ℝ} (hs : 0 < s) :
    volume (Metric.ball (0 : Spatial k) s) =
      ENNReal.ofReal (s ^ k) * volume (Metric.ball (0 : Spatial k) 1) := by
  rw [Measure.addHaar_ball_of_pos volume (0 : Spatial k) hs, finrank_euclideanSpace_fin]

/-! ### Plancherel at a fixed scale and increment -/

theorem b1sas_resid_plancherel {G : Spatial k → ℝ} (hG : MemLp G 2 volume) (s : ℝ)
    (h : Spatial k) :
    ∫⁻ u, ‖b1sas_resid G s h u‖ₑ ^ 2 =
      ∫⁻ ξ, ‖b1sas_mult Finset.univ (b1sas_coef s h) (b1sas_vec s h) ξ‖ₑ ^ 2 *
        ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 :=
  b1sas_lintegral_comb_sq Finset.univ (b1sas_coef s h) (b1sas_vec s h) hG

theorem b1sas_ennreal_alg (A B I V D : ℝ≥0∞) (h : A * B = D) :
    A * (I * (B * V)) = V * (D * I) := by
  rw [← h]
  ring

theorem b1sas_pow_identity {s : ℝ} (hs : 0 < s) :
    (ENNReal.ofReal s)⁻¹ ^ (k + 2) * ENNReal.ofReal (s ^ k) = (ENNReal.ofReal s)⁻¹ ^ 2 := by
  have hx0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 hs).ne'
  rw [ENNReal.ofReal_pow hs.le, pow_add (ENNReal.ofReal s)⁻¹ k 2, mul_comm, ← mul_assoc,
    ← mul_pow (ENNReal.ofReal s) (ENNReal.ofReal s)⁻¹ k,
    ENNReal.mul_inv_cancel hx0 ENNReal.ofReal_ne_top, one_pow, one_mul]

theorem b1sas_measurable_slice {G : Spatial k → ℝ} (hG : Measurable G) (s : ℝ) :
    Measurable (Function.uncurry fun (u h : Spatial k) =>
      (Metric.ball (0 : Spatial k) s).indicator (fun h => ‖b1sas_resid G s h u‖ₑ ^ 2) h) := by
  have hg : Measurable fun z : Spatial k × Spatial k => ((z.1, s), z.2) :=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hcomp := (b1sas_measurable_integrand hG).comp hg
  exact hcomp

theorem b1sas_measurable_slice_u {G : Spatial k → ℝ} (hG : Measurable G) (s : ℝ) :
    Measurable fun u : Spatial k =>
      ∫⁻ h, (Metric.ball (0 : Spatial k) s).indicator (fun h => ‖b1sas_resid G s h u‖ₑ ^ 2) h := by
  have hpm0 := (b1sas_measurable_slice hG s).lintegral_prod_right' (ν := volume)
  exact hpm0

/-- Tonelli in `(u, h)` at a fixed scale. -/
theorem b1sas_slice_swap {G : Spatial k → ℝ} (hG : Measurable G) (s : ℝ) (c : ℝ≥0∞) :
    ∫⁻ u, c * ∫⁻ h, (Metric.ball (0 : Spatial k) s).indicator
        (fun h => ‖b1sas_resid G s h u‖ₑ ^ 2) h =
      c * ∫⁻ h, ∫⁻ u, (Metric.ball (0 : Spatial k) s).indicator
        (fun h => ‖b1sas_resid G s h u‖ₑ ^ 2) h := by
  have hmeas2 := b1sas_measurable_slice hG s
  have hpm := b1sas_measurable_slice_u hG s
  calc ∫⁻ u, c * ∫⁻ h, (Metric.ball (0 : Spatial k) s).indicator
        (fun h => ‖b1sas_resid G s h u‖ₑ ^ 2) h
      = c * ∫⁻ u, ∫⁻ h, (Metric.ball (0 : Spatial k) s).indicator
          (fun h => ‖b1sas_resid G s h u‖ₑ ^ 2) h :=
        lintegral_const_mul c hpm
    _ = c * ∫⁻ h, ∫⁻ u, (Metric.ball (0 : Spatial k) s).indicator
          (fun h => ‖b1sas_resid G s h u‖ₑ ^ 2) h :=
        congrArg (fun X => c * X)
          (lintegral_lintegral_swap (μ := volume) (ν := volume) hmeas2.aemeasurable)

/-- Plancherel and the multiplier bound at a fixed increment. -/
theorem b1sas_slice_inner {G : Spatial k → ℝ} (hG : MemLp G 2 volume) {s : ℝ}
    (hs : 0 < s) (h : Spatial k) :
    ∫⁻ u, (Metric.ball (0 : Spatial k) s).indicator (fun h => ‖b1sas_resid G s h u‖ₑ ^ 2) h ≤
      (Metric.ball (0 : Spatial k) s).indicator (fun _ =>
        ∫⁻ ξ, ENNReal.ofReal (b1sas_K k ^ 2 * min 1 (s ^ 2 * ‖ξ‖ ^ 2) ^ 2) *
          ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2) h := by
  by_cases hh : h ∈ Metric.ball (0 : Spatial k) s
  · rw [indicator_of_mem hh]
    simp only [indicator_of_mem hh]
    rw [b1sas_resid_plancherel hG s h]
    exact lintegral_mono fun ξ =>
      mul_le_mul_left (b1sas_enorm_mult_sq_le hs (mem_ball_zero_iff.1 hh) ξ) _
  · rw [indicator_of_notMem hh]
    simp only [indicator_of_notMem hh, lintegral_zero, le_refl]

/-- The `u`-integral at a fixed scale `s > 0`. -/
theorem b1sas_scale_slice {G : Spatial k → ℝ} (hGm : Measurable G)
    (hG : MemLp G 2 volume) {s : ℝ} (hs : 0 < s) :
    ∫⁻ u, (ENNReal.ofReal s)⁻¹ ^ (k + 2) *
        ∫⁻ h, (Metric.ball (0 : Spatial k) s).indicator (fun h => ‖b1sas_resid G s h u‖ₑ ^ 2) h ≤
      volume (Metric.ball (0 : Spatial k) 1) *
        ∫⁻ ξ, (ENNReal.ofReal s)⁻¹ ^ 2 *
          ENNReal.ofReal (b1sas_K k ^ 2 * min 1 (s ^ 2 * ‖ξ‖ ^ 2) ^ 2) *
          ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 := by
  have hfin : (ENNReal.ofReal s)⁻¹ ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hs).ne')
  rw [b1sas_slice_swap hGm s]
  refine (mul_le_mul_right (lintegral_mono (b1sas_slice_inner hG hs)) _).trans (le_of_eq ?_)
  rw [lintegral_indicator_const measurableSet_ball, b1sas_volume_ball hs,
    b1sas_ennreal_alg _ _ _ _ _ (b1sas_pow_identity hs), ← lintegral_const_mul' _ _ hfin]
  simp only [mul_assoc]

/-- The scale integral at a fixed frequency. -/
theorem b1sas_scale_frequency (ξ : Spatial k) :
    ∫⁻ s, (ENNReal.ofReal s)⁻¹ ^ 2 *
        ENNReal.ofReal (b1sas_K k ^ 2 * min 1 (s ^ 2 * ‖ξ‖ ^ 2) ^ 2) ∂scaleMeasure ≤
      ENNReal.ofReal (b1sas_K k ^ 2) * ENNReal.ofReal (‖ξ‖ ^ 2) := by
  have h : ∀ s : ℝ, (ENNReal.ofReal s)⁻¹ ^ 2 *
      ENNReal.ofReal (b1sas_K k ^ 2 * min 1 (s ^ 2 * ‖ξ‖ ^ 2) ^ 2) =
      ENNReal.ofReal (b1sas_K k ^ 2) * ((ENNReal.ofReal s)⁻¹ ^ 2 *
        ENNReal.ofReal (min 1 (s ^ 2 * ‖ξ‖ ^ 2) ^ 2)) := by
    intro s
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    ring
  simp only [h]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul_right (b1sas_lintegral_scale_le (sq_nonneg ‖ξ‖)) _

/-! ### The global estimate -/

/-- The constant `C_k = |B(0,1)| K_k²` of the global estimate. -/
def b1sas_C (k : ℕ) : ℝ := (volume (Metric.ball (0 : Spatial k) 1)).toReal * b1sas_K k ^ 2

theorem b1sas_C_nonneg (k : ℕ) : 0 ≤ b1sas_C k :=
  mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

/-- **The global Fourier estimate for the residual energy** (scalar form).
For every measurable real `G ∈ L²(ℝ^k)`,
`∫_{ℝ^k} ∫_0^∞ s^{-k-2} ∫_{B(0,s)} |G(u+h) - G(u) - ∑_j (h_j/s)(G(u+se_j) - G(u))|² dh ds/s du
  ≤ C_k ∫ |ξ|² |Ĝ(ξ)|² dξ`, `C_k = |B(0,1)| (24π² + 2k + 2)²`. -/
theorem b1sas_global_residual {G : Spatial k → ℝ} (hGm : Measurable G) (hG : MemLp G 2 volume) :
    ∫⁻ u, ∫⁻ s, b1sas_residEnergy G u s ∂scaleMeasure ≤
      ENNReal.ofReal (b1sas_C k) *
        ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) *
          ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 := by
  have hVt : volume (Metric.ball (0 : Spatial k) 1) ≠ ⊤ := b1sas_volume_ball_one_lt_top.ne
  have hpos : ∀ᵐ s ∂scaleMeasure, 0 < s := by
    rw [ae_iff]
    have hs : {s : ℝ | ¬ 0 < s} = (Ioi 0)ᶜ := by
      ext s
      simp
    rw [hs]
    exact scaleMeasure_compl_positive
  have hΦm : Measurable (Function.uncurry fun (u : Spatial k) (s : ℝ) =>
      (ENNReal.ofReal s)⁻¹ ^ (k + 2) *
        ∫⁻ h, (Metric.ball (0 : Spatial k) s).indicator
          (fun h => ‖b1sas_resid G s h u‖ₑ ^ 2) h) :=
    ((ENNReal.measurable_ofReal.comp measurable_snd).inv.pow_const _).mul
      (b1sas_measurable_integrand hGm).lintegral_prod_right'
  have hc : Continuous fun x : ℝ × Spatial k =>
      b1sas_K k ^ 2 * min 1 (x.1 ^ 2 * ‖x.2‖ ^ 2) ^ 2 :=
    continuous_const.mul ((continuous_const.min ((continuous_fst.pow 2).mul
      (continuous_snd.norm.pow 2))).pow 2)
  have hΨm : Measurable (Function.uncurry fun (s : ℝ) (ξ : Spatial k) =>
      (ENNReal.ofReal s)⁻¹ ^ 2 *
        ENNReal.ofReal (b1sas_K k ^ 2 * min 1 (s ^ 2 * ‖ξ‖ ^ 2) ^ 2) *
        ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2) :=
    (((ENNReal.measurable_ofReal.comp measurable_fst).inv.pow_const 2).mul
      (ENNReal.measurable_ofReal.comp hc.measurable)).mul
      (((Lp.stronglyMeasurable (𝓕 (b1sas_realLp hG) :
        Lp ℂ 2 (volume : Measure (Spatial k)))).measurable.enorm.pow_const 2).comp
        measurable_snd)
  have hrm : ∀ ξ : Spatial k, Measurable fun s : ℝ => (ENNReal.ofReal s)⁻¹ ^ 2 *
      ENNReal.ofReal (b1sas_K k ^ 2 * min 1 (s ^ 2 * ‖ξ‖ ^ 2) ^ 2) := fun ξ =>
    (ENNReal.measurable_ofReal.inv.pow_const 2).mul (ENNReal.measurable_ofReal.comp
      (hc.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => ξ))).measurable)
  calc ∫⁻ u, ∫⁻ s, b1sas_residEnergy G u s ∂scaleMeasure
      = ∫⁻ u, ∫⁻ s, (ENNReal.ofReal s)⁻¹ ^ (k + 2) *
          (∫⁻ h, (Metric.ball (0 : Spatial k) s).indicator
            (fun h => ‖b1sas_resid G s h u‖ₑ ^ 2) h) ∂scaleMeasure := by
        refine lintegral_congr fun u => lintegral_congr fun s => ?_
        rw [b1sas_residEnergy, lintegral_indicator measurableSet_ball]
    _ = ∫⁻ s, ∫⁻ u, (ENNReal.ofReal s)⁻¹ ^ (k + 2) *
          (∫⁻ h, (Metric.ball (0 : Spatial k) s).indicator
            (fun h => ‖b1sas_resid G s h u‖ₑ ^ 2) h) ∂volume ∂scaleMeasure :=
        lintegral_lintegral_swap hΦm.aemeasurable
    _ ≤ ∫⁻ s, volume (Metric.ball (0 : Spatial k) 1) *
          (∫⁻ ξ, (ENNReal.ofReal s)⁻¹ ^ 2 *
            ENNReal.ofReal (b1sas_K k ^ 2 * min 1 (s ^ 2 * ‖ξ‖ ^ 2) ^ 2) *
            ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2)
              ∂scaleMeasure := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpos] with s hs
        exact b1sas_scale_slice hGm hG hs
    _ = volume (Metric.ball (0 : Spatial k) 1) * ∫⁻ ξ, ∫⁻ s, (ENNReal.ofReal s)⁻¹ ^ 2 *
            ENNReal.ofReal (b1sas_K k ^ 2 * min 1 (s ^ 2 * ‖ξ‖ ^ 2) ^ 2) *
            ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2
              ∂scaleMeasure := by
        rw [lintegral_const_mul' _ _ hVt, lintegral_lintegral_swap hΨm.aemeasurable]
    _ ≤ volume (Metric.ball (0 : Spatial k) 1) * ∫⁻ ξ, ENNReal.ofReal (b1sas_K k ^ 2) *
            ENNReal.ofReal (‖ξ‖ ^ 2) *
            ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 := by
        refine mul_le_mul_right (lintegral_mono fun ξ => ?_) _
        rw [lintegral_mul_const _ (hrm ξ)]
        exact mul_le_mul_left (b1sas_scale_frequency ξ) _
    _ = ENNReal.ofReal (b1sas_C k) *
          ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) *
            ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 := by
        simp only [mul_assoc]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, b1sas_C,
          ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hVt]

theorem b1sas_measurable_residEnergy_left {G : Spatial k → ℝ} (hG : Measurable G)
    (u : Spatial k) : Measurable fun s : ℝ => b1sas_residEnergy G u s := by
  have hf : Measurable fun s : ℝ => ((u, s) : Spatial k × ℝ) :=
    measurable_const.prodMk measurable_id
  have h := (b1sas_measurable_residEnergy hG).comp hf
  exact h

theorem b1sas_measurable_residEnergy_int {G : Spatial k → ℝ} (hG : Measurable G) :
    Measurable fun u : Spatial k => ∫⁻ s, b1sas_residEnergy G u s ∂scaleMeasure :=
  (b1sas_measurable_residEnergy hG).lintegral_prod_right'

/-- Summing the coordinate residual energies. -/
theorem b1sas_lintegral_sum_residEnergy {d : ℕ} {F : Spatial k → Spatial d}
    (hF : Measurable F) :
    ∫⁻ u, ∫⁻ s, ∑ i : Fin d, b1sas_residEnergy (fun v => F v i) u s ∂scaleMeasure =
      ∑ i : Fin d, ∫⁻ u, ∫⁻ s, b1sas_residEnergy (fun v => F v i) u s ∂scaleMeasure := by
  have h1 : ∀ u : Spatial k,
      ∫⁻ s, ∑ i : Fin d, b1sas_residEnergy (fun v => F v i) u s ∂scaleMeasure =
        ∑ i : Fin d, ∫⁻ s, b1sas_residEnergy (fun v => F v i) u s ∂scaleMeasure := fun u =>
    lintegral_finsetSum _ fun i _ =>
      b1sas_measurable_residEnergy_left (b1sas_measurable_coord hF i) u
  rw [lintegral_congr h1]
  exact lintegral_finsetSum _ fun i _ =>
    b1sas_measurable_residEnergy_int (b1sas_measurable_coord hF i)

/-- **The global spatial Fourier affine-square estimate** (vector form).
For every measurable `F : ℝ^k → ℝ^d` whose coordinates `F_i` are in `L²`,
`∫_{ℝ^k} ∫_0^∞ spatialAffineErrorSq F u s ds/s du ≤ C_k ∑_i ∫ |ξ|² |F̂_i(ξ)|² dξ`. -/
theorem b1sas_spatial_global {d : ℕ} {F : Spatial k → Spatial d} (hF : Measurable F)
    (hL2 : ∀ i : Fin d, MemLp (fun v => F v i) 2 volume) :
    ∫⁻ u, ∫⁻ s, spatialAffineErrorSq F u s ∂scaleMeasure ≤
      ENNReal.ofReal (b1sas_C k) * ∑ i : Fin d,
        ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) *
          ‖(𝓕 (b1sas_realLp (hL2 i)) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 := by
  have hmono : ∫⁻ u, ∫⁻ s, spatialAffineErrorSq F u s ∂scaleMeasure ≤
      ∫⁻ u, ∫⁻ s, ∑ i : Fin d, b1sas_residEnergy (fun v => F v i) u s ∂scaleMeasure :=
    lintegral_mono fun u => lintegral_mono fun s => b1sas_spatialAffineErrorSq_le hF u s
  have hsum : ∑ i : Fin d, ∫⁻ u, ∫⁻ s, b1sas_residEnergy (fun v => F v i) u s ∂scaleMeasure ≤
      ∑ i : Fin d, ENNReal.ofReal (b1sas_C k) *
        ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) *
          ‖(𝓕 (b1sas_realLp (hL2 i)) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 :=
    Finset.sum_le_sum fun i _ => b1sas_global_residual (b1sas_measurable_coord hF i) (hL2 i)
  rw [b1sas_lintegral_sum_residEnergy hF] at hmono
  rw [Finset.mul_sum]
  exact hmono.trans hsum

end ParabolicRectifiability.Characterization
