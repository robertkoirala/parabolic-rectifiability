import ParabolicRectifiability.Analysis.TraceExtension.SourceAllocation

/-! # Allocated node estimates and the node Carleson bound

Four auxiliary estimates for the trace extension: the allocated node estimates (anchor
estimate, exact affine reproduction, signed Jensen), the Lipschitz bound for the node
function on the node set, the change of scale for `ds/s`
(`lintegral_Ioi_scaleMeasure_le_of_le_comp_mul_proof`) and the node Carleson bound
(`whitney_node_carleson_le_proof`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Function

namespace ParabolicRectifiability

/-! ## Elementary facts in `ℝ≥0∞` -/

theorem ennreal_sq_rpow_half (x : ℝ≥0∞) : (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem ennreal_rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Weighted Cauchy–Schwarz: `(∫ k ‖G‖)² ≤ (∫ k) (∫ ‖G‖² k)`. -/
theorem lintegral_mul_enorm_sq_le {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {k : X → ℝ≥0∞} (hk : AEMeasurable k μ) {G : X → E}
    (hG : AEStronglyMeasurable G μ) :
    (∫⁻ x, k x * ‖G x‖ₑ ∂μ) ^ 2 ≤ (∫⁻ x, k x ∂μ) * ∫⁻ x, ‖G x‖ₑ ^ 2 * k x ∂μ := by
  have hGk : AEMeasurable (fun x => ‖G x‖ₑ ^ 2 * k x) μ := (hG.enorm.pow_const 2).mul hk
  have hH := ENNReal.lintegral_mul_norm_pow_le (p := 1 / 2) (q := 1 / 2) hk hGk
    (by norm_num) (by norm_num) (by norm_num)
  have hpt : ∀ x, k x ^ (1 / 2 : ℝ) * (‖G x‖ₑ ^ 2 * k x) ^ (1 / 2 : ℝ) = k x * ‖G x‖ₑ := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ennreal_sq_rpow_half]
    calc k x ^ (1 / 2 : ℝ) * (‖G x‖ₑ * k x ^ (1 / 2 : ℝ))
        = (k x ^ (1 / 2 : ℝ) * k x ^ (1 / 2 : ℝ)) * ‖G x‖ₑ := by ring
      _ = (k x ^ 2) ^ (1 / 2 : ℝ) * ‖G x‖ₑ := by
          rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), sq]
      _ = k x * ‖G x‖ₑ := by rw [ennreal_sq_rpow_half]
  simp only [hpt] at hH
  calc (∫⁻ x, k x * ‖G x‖ₑ ∂μ) ^ 2
      ≤ ((∫⁻ x, k x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, ‖G x‖ₑ ^ 2 * k x ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le hH 2
    _ = (∫⁻ x, k x ∂μ) * ∫⁻ x, ‖G x‖ₑ ^ 2 * k x ∂μ := by
        rw [mul_pow, ennreal_rpow_half_sq, ennreal_rpow_half_sq]

/-! ## Allocated averages -/

namespace WhitneySourceAllocation

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a : ℝ} {W : WhitneyData m ι F₀ D a}
  {σ : Measure (Space m)} {A C_B c₂ : ℝ}

theorem lintegral_density_ne_top (S : WhitneySourceAllocation W σ A C_B c₂) (i : ι)
    (l : Fin (m + 1)) : ∫⁻ x, S.density i l x ∂σ ≠ ∞ := by
  rw [S.lintegral_density i l]
  exact ENNReal.ofReal_ne_top

theorem integrable_density_toReal (S : WhitneySourceAllocation W σ A C_B c₂) (i : ι)
    (l : Fin (m + 1)) : Integrable (fun x => (S.density i l x).toReal) σ :=
  integrable_toReal_of_lintegral_ne_top (S.measurable_density i l).aemeasurable
    (S.lintegral_density_ne_top i l)

theorem integral_density_toReal (S : WhitneySourceAllocation W σ A C_B c₂) (i : ι)
    (l : Fin (m + 1)) : ∫ x, (S.density i l x).toReal ∂σ = W.radius i ^ (m + 2) := by
  rw [integral_toReal (S.measurable_density i l).aemeasurable
      (ae_lt_top (S.measurable_density i l) (S.lintegral_density_ne_top i l)),
    S.lintegral_density i l, ENNReal.toReal_ofReal (pow_nonneg (W.radius_pos i).le _)]

/-- A density times a function that is bounded around `y₀` on the reservoir is integrable. -/
theorem integrable_density_smul (S : WhitneySourceAllocation W σ A C_B c₂) (i : ι)
    (l : Fin (m + 1)) {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {G : Space m → Y}
    (hG : AEStronglyMeasurable G σ) (y₀ : Y) (K : ℝ)
    (hb : ∀ᵐ x ∂σ, x ∈ S.reservoir i l → ‖G x - y₀‖ ≤ K) :
    Integrable (fun x => (S.density i l x).toReal • G x) σ := by
  have hint := S.integrable_density_toReal i l
  have h1 : Integrable (fun x => (S.density i l x).toReal • (G x - y₀)) σ := by
    refine Integrable.mono' (hint.mul_const K)
      (((S.measurable_density i l).ennreal_toReal.aestronglyMeasurable).smul
        (hG.sub aestronglyMeasurable_const)) ?_
    filter_upwards [hb] with x hx
    rw [norm_smul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    by_cases hxr : x ∈ S.reservoir i l
    · exact mul_le_mul_of_nonneg_left (hx hxr) ENNReal.toReal_nonneg
    · rw [S.density_eq_zero i l x hxr, ENNReal.toReal_zero, zero_mul, zero_mul]
  refine (h1.add (hint.smul_const y₀)).congr (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, smul_sub, sub_add_cancel]

/-- An average minus a vector `y₀` is the average of the differences. -/
theorem average_sub_eq (S : WhitneySourceAllocation W σ A C_B c₂) (i : ι) (l : Fin (m + 1))
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] {G : Space m → Y}
    (hGi : Integrable (fun x => (S.density i l x).toReal • G x) σ) (y₀ : Y) :
    S.average G i l - y₀ =
      (W.radius i ^ (m + 2))⁻¹ • ∫ x, (S.density i l x).toReal • (G x - y₀) ∂σ := by
  have hV : 0 < W.radius i ^ (m + 2) := pow_pos (W.radius_pos i) _
  have hc : Integrable (fun x => (S.density i l x).toReal • y₀) σ :=
    (S.integrable_density_toReal i l).smul_const y₀
  have hsplit : (fun x => (S.density i l x).toReal • (G x - y₀)) =
      fun x => (S.density i l x).toReal • G x - (S.density i l x).toReal • y₀ := by
    funext x
    rw [smul_sub]
  rw [hsplit, integral_sub hGi hc, integral_smul_const, S.integral_density_toReal i l, smul_sub,
    smul_smul, inv_mul_cancel₀ hV.ne', one_smul]
  rfl

/-- The average of a function within `K` of `y₀` on the reservoir is within `K` of `y₀`. -/
theorem norm_average_sub_le (S : WhitneySourceAllocation W σ A C_B c₂) (i : ι)
    (l : Fin (m + 1)) {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {G : Space m → Y} (hG : AEStronglyMeasurable G σ) (y₀ : Y) (K : ℝ)
    (hb : ∀ᵐ x ∂σ, x ∈ S.reservoir i l → ‖G x - y₀‖ ≤ K) :
    ‖S.average G i l - y₀‖ ≤ K := by
  have hV : 0 < W.radius i ^ (m + 2) := pow_pos (W.radius_pos i) _
  rw [S.average_sub_eq i l (S.integrable_density_smul i l hG y₀ K hb) y₀, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 hV.le)]
  have hbd : ∀ᵐ x ∂σ, ‖(S.density i l x).toReal • (G x - y₀)‖ ≤
      (S.density i l x).toReal * K := by
    filter_upwards [hb] with x hx
    rw [norm_smul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    by_cases hxr : x ∈ S.reservoir i l
    · exact mul_le_mul_of_nonneg_left (hx hxr) ENNReal.toReal_nonneg
    · rw [S.density_eq_zero i l x hxr, ENNReal.toReal_zero, zero_mul, zero_mul]
  calc (W.radius i ^ (m + 2))⁻¹ * ‖∫ x, (S.density i l x).toReal • (G x - y₀) ∂σ‖
      ≤ (W.radius i ^ (m + 2))⁻¹ * ∫ x, (S.density i l x).toReal * K ∂σ :=
        mul_le_mul_of_nonneg_left
          (norm_integral_le_of_norm_le ((S.integrable_density_toReal i l).mul_const K) hbd)
          (inv_nonneg.2 hV.le)
    _ = K := by
        rw [integral_mul_const, S.integral_density_toReal i l, ← mul_assoc,
          inv_mul_cancel₀ hV.ne', one_mul]

/-- Points of a reservoir are spatially within `|C_B| r_i` of the anchor. -/
theorem norm_sub_anchor_le_of_mem_reservoir (S : WhitneySourceAllocation W σ A C_B c₂)
    {i : ι} {l : Fin (m + 1)} {x : Space m} (hx : x ∈ S.reservoir i l) :
    ‖x.1 - (S.anchor i).1‖ ≤ |C_B| * W.radius i := by
  have hd : dist x (S.anchor i) < C_B * W.radius i := S.reservoir_subset i l hx
  have h1 : dist x.1 (S.anchor i).1 ≤ dist x (S.anchor i) := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  rw [← dist_eq_norm]
  exact h1.trans (hd.le.trans
    (mul_le_mul_of_nonneg_right (le_abs_self _) (W.radius_pos i).le))

end WhitneySourceAllocation

/-! ## Allocated node estimates -/

/-- **Allocated node estimates.** `f` is replaced σ-a.e. by a Lipschitz extension to get
measurability; the averages of `f` and of affine maps are genuine (integrable) averages
against the probability densities `h_{i,l}/|Q_i|`. Anchor estimate: each average is within
`L |C_B| r_i` of `f(a_i)`, and `Σ_l c_{i,l} = 1`, `Σ_l |c_{i,l}| ≤ Cm`. Reproduction: the
average of `a₀ + B u` is `a₀ + B b_{i,l}`, and the moment identities give `a₀ + B u_i`.
Signed Jensen: `g(p_i) - A(u_i) = |Q_i|⁻¹ ∫ (Σ_l c_{i,l} h_{i,l}) (f - A) dσ`, then
weighted Cauchy–Schwarz with the weight `Σ_l |c_{i,l}| h_{i,l}` of mass `≤ Cm |Q_i|`.
The constant is `C = Cm² + |Cm| |C_B|`. -/
theorem allocated_node_estimates_proof (m : ℕ) (D a A C_B c₂ Cm : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a) (σ : Measure (Space m)), σ ≤ parabolicVolume m →
      ∀ (S : WhitneySourceAllocation W σ A C_B c₂) (coef : ι → Fin (m + 1) → ℝ),
        S.IsMomentCoefficients coef Cm →
      ∀ {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
        (f : Space m → Y) (L : ℝ≥0) (T : Set (Space m)),
        σ Tᶜ = 0 → F₀ ⊆ T → LipschitzOnWith L f T →
        (∀ i, ‖S.nodeValue coef f i - f (S.anchor i)‖ ≤ C * L * W.radius i) ∧
        (∀ i (a₀ : Y) (B : Spatial m →L[ℝ] Y),
          ∑ l, coef i l • S.average (fun x => a₀ + B x.1) i l = a₀ + B (W.center i).1) ∧
        ∀ i (a₀ : Y) (B : Spatial m →L[ℝ] Y),
          ENNReal.ofReal (W.radius i ^ (m + 2)) *
              ‖S.nodeValue coef f i - (a₀ + B (W.center i).1)‖ₑ ^ 2 ≤
            ENNReal.ofReal C *
              ∑ l, ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * S.density i l x ∂σ := by
  refine ⟨Cm ^ 2 + |Cm| * |C_B|, by positivity, ?_⟩
  intro ι _ F₀ W σ _ S coef hcoef Y _ _ _ f L T hT hF₀T hfL
  have hTae : ∀ᵐ x ∂σ, x ∈ T := mem_ae_iff.2 hT
  obtain ⟨F, hFlip, hFeq⟩ := hfL.extend_finite_dimension
  have hfm : AEStronglyMeasurable f σ :=
    hFlip.continuous.aestronglyMeasurable.congr (hTae.mono fun x hx => (hFeq hx).symm)
  have hfb : ∀ i l, ∀ᵐ x ∂σ, x ∈ S.reservoir i l →
      ‖f x - f (S.anchor i)‖ ≤ L * |C_B| * W.radius i := by
    intro i l
    filter_upwards [hTae] with x hxT hxr
    have hd : dist x (S.anchor i) < C_B * W.radius i := S.reservoir_subset i l hxr
    have h1 : dist (f x) (f (S.anchor i)) ≤ L * dist x (S.anchor i) :=
      hfL.dist_le_mul x hxT _ (hF₀T (S.anchor_mem i))
    rw [← dist_eq_norm]
    calc dist (f x) (f (S.anchor i)) ≤ L * dist x (S.anchor i) := h1
      _ ≤ L * (|C_B| * W.radius i) :=
          mul_le_mul_of_nonneg_left (hd.le.trans
            (mul_le_mul_of_nonneg_right (le_abs_self _) (W.radius_pos i).le)) L.coe_nonneg
      _ = L * |C_B| * W.radius i := by ring
  have hfi : ∀ i l, Integrable (fun x => (S.density i l x).toReal • f x) σ :=
    fun i l => S.integrable_density_smul i l hfm _ _ (hfb i l)
  have hAm : ∀ (a₀ : Y) (B : Spatial m →L[ℝ] Y),
      AEStronglyMeasurable (fun x : Space m => a₀ + B x.1) σ :=
    fun a₀ B => (continuous_const.add (B.continuous.comp continuous_fst)).aestronglyMeasurable
  have hAi : ∀ (a₀ : Y) (B : Spatial m →L[ℝ] Y) i l,
      Integrable (fun x => (S.density i l x).toReal • (a₀ + B x.1)) σ := by
    intro a₀ B i l
    refine S.integrable_density_smul i l (hAm a₀ B) (a₀ + B (S.anchor i).1)
      (‖B‖ * (|C_B| * W.radius i)) (ae_of_all _ fun x hxr => ?_)
    rw [add_sub_add_left_eq_sub, ← map_sub]
    exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (S.norm_sub_anchor_le_of_mem_reservoir hxr) (norm_nonneg _))
  have hxi : ∀ i l, Integrable (fun x : Space m => (S.density i l x).toReal • x.1) σ :=
    fun i l => S.integrable_density_smul i l continuous_fst.aestronglyMeasurable (S.anchor i).1
      (|C_B| * W.radius i) (ae_of_all _ fun x hxr => S.norm_sub_anchor_le_of_mem_reservoir hxr)
  -- exact reproduction of affine maps
  have hrep : ∀ i (a₀ : Y) (B : Spatial m →L[ℝ] Y),
      ∑ l, coef i l • S.average (fun x => a₀ + B x.1) i l = a₀ + B (W.center i).1 := by
    intro i a₀ B
    have hV : 0 < W.radius i ^ (m + 2) := pow_pos (W.radius_pos i) _
    have havg : ∀ l, S.average (fun x => a₀ + B x.1) i l = a₀ + B (S.barycenter i l) := by
      intro l
      have e1 : (fun x : Space m => (S.density i l x).toReal • (a₀ + B x.1)) =
          fun x => (S.density i l x).toReal • a₀ + B ((S.density i l x).toReal • x.1) := by
        funext x
        rw [smul_add, map_smul]
      show (W.radius i ^ (m + 2))⁻¹ • ∫ x, (S.density i l x).toReal • (a₀ + B x.1) ∂σ =
        a₀ + B ((W.radius i ^ (m + 2))⁻¹ • ∫ x, (S.density i l x).toReal • x.1 ∂σ)
      rw [e1, integral_add ((S.integrable_density_toReal i l).smul_const a₀)
          (B.integrable_comp (hxi i l)), integral_smul_const, S.integral_density_toReal i l,
        B.integral_comp_comm (hxi i l), smul_add, smul_smul, inv_mul_cancel₀ hV.ne', one_smul,
        map_smul]
    have hB : ∑ l, coef i l • B (S.barycenter i l) = B (W.center i).1 := by
      rw [← hcoef.sum_smul_barycenter i, map_sum]
      simp only [map_smul]
    simp only [havg, smul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_smul, hcoef.sum_eq_one i, one_smul, hB]
  -- anchor estimate
  have hanchor : ∀ i, ‖S.nodeValue coef f i - f (S.anchor i)‖ ≤
      (Cm ^ 2 + |Cm| * |C_B|) * L * W.radius i := by
    intro i
    have hr := W.radius_pos i
    have hsum : ∑ l, coef i l • f (S.anchor i) = f (S.anchor i) := by
      rw [← Finset.sum_smul, hcoef.sum_eq_one i, one_smul]
    have hl : ∀ l, ‖S.average f i l - f (S.anchor i)‖ ≤ L * |C_B| * W.radius i := fun l =>
      S.norm_average_sub_le i l hfm _ _ (hfb i l)
    have hCm : ∑ l, |coef i l| ≤ Cm := hcoef.sum_abs_le i
    have hLr : 0 ≤ (L : ℝ) * |C_B| * W.radius i := by positivity
    calc ‖S.nodeValue coef f i - f (S.anchor i)‖
        = ‖∑ l, coef i l • (S.average f i l - f (S.anchor i))‖ := by
          congr 1
          simp only [WhitneySourceAllocation.nodeValue, smul_sub, Finset.sum_sub_distrib, hsum]
      _ ≤ ∑ l, ‖coef i l • (S.average f i l - f (S.anchor i))‖ := norm_sum_le _ _
      _ = ∑ l, |coef i l| * ‖S.average f i l - f (S.anchor i)‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ l, |coef i l| * (L * |C_B| * W.radius i) :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hl l) (abs_nonneg _)
      _ = (∑ l, |coef i l|) * (L * |C_B| * W.radius i) := (Finset.sum_mul _ _ _).symm
      _ ≤ |Cm| * (L * |C_B| * W.radius i) :=
          mul_le_mul_of_nonneg_right (hCm.trans (le_abs_self _)) hLr
      _ ≤ (Cm ^ 2 + |Cm| * |C_B|) * L * W.radius i := by
          have h0 : 0 ≤ Cm ^ 2 * (L : ℝ) * W.radius i := by positivity
          nlinarith [h0]
  -- signed Jensen
  have hjensen : ∀ i (a₀ : Y) (B : Spatial m →L[ℝ] Y),
      ENNReal.ofReal (W.radius i ^ (m + 2)) *
          ‖S.nodeValue coef f i - (a₀ + B (W.center i).1)‖ₑ ^ 2 ≤
        ENNReal.ofReal (Cm ^ 2 + |Cm| * |C_B|) *
          ∑ l, ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * S.density i l x ∂σ := by
    intro i a₀ B
    have hVpos : 0 < W.radius i ^ (m + 2) := pow_pos (W.radius_pos i) _
    have hGm : AEStronglyMeasurable (fun x => f x - (a₀ + B x.1)) σ := hfm.sub (hAm a₀ B)
    have hGi : ∀ l, Integrable
        (fun x => (S.density i l x).toReal • (f x - (a₀ + B x.1))) σ := by
      intro l
      have := (hfi i l).sub (hAi a₀ B i l)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [Pi.sub_apply, smul_sub]
    have hdiff : S.nodeValue coef f i - (a₀ + B (W.center i).1) =
        (W.radius i ^ (m + 2))⁻¹ • ∫ x, (∑ l, coef i l * (S.density i l x).toReal) •
          (f x - (a₀ + B x.1)) ∂σ := by
      rw [← hrep i a₀ B]
      have h1 : ∀ l, S.average f i l - S.average (fun x => a₀ + B x.1) i l =
          (W.radius i ^ (m + 2))⁻¹ •
            ∫ x, (S.density i l x).toReal • (f x - (a₀ + B x.1)) ∂σ := by
        intro l
        show (W.radius i ^ (m + 2))⁻¹ • ∫ x, (S.density i l x).toReal • f x ∂σ -
            (W.radius i ^ (m + 2))⁻¹ • ∫ x, (S.density i l x).toReal • (a₀ + B x.1) ∂σ = _
        rw [← smul_sub, ← integral_sub (hfi i l) (hAi a₀ B i l)]
        simp only [smul_sub]
      calc S.nodeValue coef f i - ∑ l, coef i l • S.average (fun x => a₀ + B x.1) i l
          = ∑ l, coef i l • (S.average f i l - S.average (fun x => a₀ + B x.1) i l) := by
            simp only [WhitneySourceAllocation.nodeValue, smul_sub, Finset.sum_sub_distrib]
        _ = ∑ l, coef i l • ((W.radius i ^ (m + 2))⁻¹ •
              ∫ x, (S.density i l x).toReal • (f x - (a₀ + B x.1)) ∂σ) := by
            simp only [h1]
        _ = (W.radius i ^ (m + 2))⁻¹ • ∑ l, ∫ x, coef i l •
              ((S.density i l x).toReal • (f x - (a₀ + B x.1))) ∂σ := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [integral_smul]
            exact smul_comm _ _ _
        _ = (W.radius i ^ (m + 2))⁻¹ • ∫ x, ∑ l, coef i l •
              ((S.density i l x).toReal • (f x - (a₀ + B x.1))) ∂σ := by
            rw [integral_finsetSum (f := fun l x =>
              coef i l • ((S.density i l x).toReal • (f x - (a₀ + B x.1)))) _
              fun l _ => (hGi l).smul (coef i l)]
        _ = _ := by simp only [smul_smul, ← Finset.sum_smul]
    set k : Space m → ℝ≥0∞ := fun x => ∑ l, ENNReal.ofReal |coef i l| * S.density i l x
      with hk
    have hkm : Measurable k :=
      Finset.measurable_sum _ fun l _ => measurable_const.mul (S.measurable_density i l)
    have hφk : ∀ x, ‖∑ l, coef i l * (S.density i l x).toReal‖ₑ ≤ k x := by
      intro x
      calc ‖∑ l, coef i l * (S.density i l x).toReal‖ₑ
          ≤ ∑ l, ‖coef i l * (S.density i l x).toReal‖ₑ := enorm_sum_le _ _
        _ ≤ ∑ l, ENNReal.ofReal |coef i l| * S.density i l x := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
            abs_of_nonneg ENNReal.toReal_nonneg]
          gcongr
          exact ENNReal.ofReal_toReal_le
    have hI : ‖∫ x, (∑ l, coef i l * (S.density i l x).toReal) • (f x - (a₀ + B x.1)) ∂σ‖ₑ ≤
        ∫⁻ x, k x * ‖f x - (a₀ + B x.1)‖ₑ ∂σ := by
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
      rw [enorm_smul]
      gcongr
      exact hφk x
    have hCS := lintegral_mul_enorm_sq_le (μ := σ) hkm.aemeasurable hGm
    have hk1 : ∫⁻ x, k x ∂σ ≤ ENNReal.ofReal |Cm| * ENNReal.ofReal (W.radius i ^ (m + 2)) := by
      calc ∫⁻ x, k x ∂σ = ∑ l, ∫⁻ x, ENNReal.ofReal |coef i l| * S.density i l x ∂σ :=
            lintegral_finsetSum _ fun l _ => measurable_const.mul (S.measurable_density i l)
        _ = ∑ l, ENNReal.ofReal |coef i l| * ENNReal.ofReal (W.radius i ^ (m + 2)) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [lintegral_const_mul _ (S.measurable_density i l), S.lintegral_density i l]
        _ = ENNReal.ofReal (∑ l, |coef i l|) * ENNReal.ofReal (W.radius i ^ (m + 2)) := by
            rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun l _ => abs_nonneg _]
        _ ≤ ENNReal.ofReal |Cm| * ENNReal.ofReal (W.radius i ^ (m + 2)) := by
            gcongr
            exact (hcoef.sum_abs_le i).trans (le_abs_self _)
    have hk2 : ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * k x ∂σ ≤ ENNReal.ofReal |Cm| *
        ∑ l, ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * S.density i l x ∂σ := by
      calc ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * k x ∂σ
          = ∫⁻ x, ∑ l, ENNReal.ofReal |coef i l| *
              (‖f x - (a₀ + B x.1)‖ₑ ^ 2 * S.density i l x) ∂σ := by
            refine lintegral_congr fun x => ?_
            simp only [hk, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
        _ = ∑ l, ENNReal.ofReal |coef i l| *
              ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * S.density i l x ∂σ := by
            rw [lintegral_finsetSum' (f := fun l x => ENNReal.ofReal |coef i l| *
              (‖f x - (a₀ + B x.1)‖ₑ ^ 2 * S.density i l x)) _ fun l _ =>
              (((hGm.enorm.pow_const 2).mul (S.measurable_density i l).aemeasurable).const_mul _)]
            exact Finset.sum_congr rfl fun l _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ∑ l, ENNReal.ofReal |Cm| *
              ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * S.density i l x ∂σ := by
            refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right
              (ENNReal.ofReal_le_ofReal ((Finset.single_le_sum (fun l _ => abs_nonneg (coef i l))
                (Finset.mem_univ l)).trans ((hcoef.sum_abs_le i).trans (le_abs_self _)))) zero_le
        _ = _ := (Finset.mul_sum _ _ _).symm
    rw [hdiff, enorm_smul, Real.enorm_eq_ofReal (inv_nonneg.2 hVpos.le), mul_pow]
    calc ENNReal.ofReal (W.radius i ^ (m + 2)) * (ENNReal.ofReal (W.radius i ^ (m + 2))⁻¹ ^ 2 *
          ‖∫ x, (∑ l, coef i l * (S.density i l x).toReal) • (f x - (a₀ + B x.1)) ∂σ‖ₑ ^ 2)
        ≤ ENNReal.ofReal (W.radius i ^ (m + 2)) * (ENNReal.ofReal (W.radius i ^ (m + 2))⁻¹ ^ 2 *
          ((∫⁻ x, k x ∂σ) * ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * k x ∂σ)) := by
          gcongr
          exact (pow_le_pow_left₀ zero_le hI 2).trans hCS
      _ ≤ ENNReal.ofReal (W.radius i ^ (m + 2)) * (ENNReal.ofReal (W.radius i ^ (m + 2))⁻¹ ^ 2 *
          ((ENNReal.ofReal |Cm| * ENNReal.ofReal (W.radius i ^ (m + 2))) *
            (ENNReal.ofReal |Cm| *
              ∑ l, ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * S.density i l x ∂σ))) := by
          gcongr
      _ = (ENNReal.ofReal (W.radius i ^ (m + 2)) * ENNReal.ofReal (W.radius i ^ (m + 2))⁻¹) ^ 2 *
          (ENNReal.ofReal |Cm| * ENNReal.ofReal |Cm|) *
            ∑ l, ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * S.density i l x ∂σ := by ring
      _ = ENNReal.ofReal (Cm ^ 2) *
            ∑ l, ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * S.density i l x ∂σ := by
          rw [← ENNReal.ofReal_mul hVpos.le, mul_inv_cancel₀ hVpos.ne', ENNReal.ofReal_one,
            one_pow, one_mul, ← ENNReal.ofReal_mul (abs_nonneg _), abs_mul_abs_self, sq Cm]
      _ ≤ ENNReal.ofReal (Cm ^ 2 + |Cm| * |C_B|) *
            ∑ l, ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * S.density i l x ∂σ := by
          gcongr
          exact le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  exact ⟨hanchor, hrep, hjensen⟩

/-! ## The node function is Lipschitz -/

/-- **Lipschitz node function.** Centers lie in their own disjoint cells,
hence outside `F₀` and pairwise distinct, so the node function takes the node value at
`p_i` and `f` on `F₀`. Lipschitz bounds: `F₀`/`F₀` by `f`; `p_i`/`y ∈ F₀` by the anchor
estimate, `a r_i ≤ dist(p_i, F₀) ≤ dist(p_i, y)` and `dist(a_i, y) ≤ 2 dist(p_i, y)`;
`p_i`/`p_j` by the anchor estimate, `dist(p_i, a_i) ≤ b r_i` and the separation
`max(r_i, r_j) ≤ dist(p_i, p_j)/s₀`. -/
theorem allocated_node_lipschitz_proof (m : ℕ) (D a b s₀ A C_B c₂ Cm : ℝ) (hs₀ : 0 < s₀) :
    ∃ C : ℝ≥0, ∀ {ι : Type*} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsCompact F₀ → F₀.Nonempty →
      (∀ j, Metric.infDist (W.center j) F₀ ≤ b * W.radius j) →
      (∀ i j, i ≠ j → s₀ * max (W.radius i) (W.radius j) ≤ dist (W.center i) (W.center j)) →
      ∀ (σ : Measure (Space m)), σ ≤ parabolicVolume m →
      ∀ (S : WhitneySourceAllocation W σ A C_B c₂) (coef : ι → Fin (m + 1) → ℝ),
        S.IsMomentCoefficients coef Cm →
      ∀ {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
        (f : Space m → Y) (L : ℝ≥0) (T : Set (Space m)),
        σ Tᶜ = 0 → F₀ ⊆ T → LipschitzOnWith L f T →
        (∀ i, S.nodeFunction coef f (W.center i) = S.nodeValue coef f i) ∧
        (∀ x ∈ F₀, S.nodeFunction coef f x = f x) ∧
        LipschitzOnWith (C * L) (S.nodeFunction coef f) W.nodeSet := by
  obtain ⟨C₁, hC₁, hest⟩ := allocated_node_estimates_proof m D a A C_B c₂ Cm
  refine ⟨Real.toNNReal (C₁ / a + 2 + (2 * C₁ / s₀ + 1 + 2 * |b| / s₀)), ?_⟩
  intro ι _ F₀ W _ _ hb hsep σ hσ S coef hcoef Y _ _ _ f L T hT hF₀T hfL
  obtain ⟨hanc, -, -⟩ := hest W σ hσ S coef hcoef f L T hT hF₀T hfL
  have ha : 0 < a := W.a_pos
  have hL := L.coe_nonneg
  have hpart1 : 0 ≤ C₁ / a + 2 := by positivity
  have hpart2 : 0 ≤ 2 * C₁ / s₀ + 1 + 2 * |b| / s₀ := by positivity
  have hK0 : 0 ≤ C₁ / a + 2 + (2 * C₁ / s₀ + 1 + 2 * |b| / s₀) := by linarith
  have hcenter_notMem : ∀ i, W.center i ∉ F₀ := by
    intro i h
    have hmem : W.center i ∈ ⋃ j, W.cell j := Set.mem_iUnion.2 ⟨i, W.center_mem i⟩
    rw [W.iUnion_cell] at hmem
    exact hmem h
  have hinj : ∀ i j, W.center i = W.center j → i = j := by
    intro i j hij
    by_contra hne
    have hj : W.center i ∈ W.cell j := hij ▸ W.center_mem j
    exact Set.disjoint_left.1 (W.pairwise_disjoint hne) (W.center_mem i) hj
  have hnodeC : ∀ i, S.nodeFunction coef f (W.center i) = S.nodeValue coef f i := by
    intro i
    have hex : ∃ j, W.center j = W.center i := ⟨i, rfl⟩
    simp only [WhitneySourceAllocation.nodeFunction, dite_eq_left hex]
    rw [hinj _ _ hex.choose_spec]
  have hnodeF : ∀ x ∈ F₀, S.nodeFunction coef f x = f x := by
    intro x hx
    have hex : ¬∃ j, W.center j = x := fun ⟨j, hj⟩ => hcenter_notMem j (hj ▸ hx)
    simp only [WhitneySourceAllocation.nodeFunction, dite_eq_right hex]
  -- a center against a point of `F₀`
  have h2 : ∀ i, ∀ y ∈ F₀, dist (S.nodeValue coef f i) (f y) ≤
      (C₁ / a + 2 + (2 * C₁ / s₀ + 1 + 2 * |b| / s₀)) * L * dist (W.center i) y := by
    intro i y hy
    have hr := W.radius_pos i
    have hinf : a * W.radius i ≤ Metric.infDist (W.center i) F₀ :=
      W.le_infDist i _ (W.center_mem i)
    have hinfy : Metric.infDist (W.center i) F₀ ≤ dist (W.center i) y :=
      Metric.infDist_le_dist_of_mem hy
    have hdan : dist (W.center i) (S.anchor i) = Metric.infDist (W.center i) F₀ :=
      S.dist_anchor i
    have hay : dist (S.anchor i) y ≤ 2 * dist (W.center i) y := by
      have h := dist_triangle (S.anchor i) (W.center i) y
      rw [dist_comm (S.anchor i) (W.center i)] at h
      linarith
    have hfa : dist (f (S.anchor i)) (f y) ≤ L * dist (S.anchor i) y :=
      hfL.dist_le_mul _ (hF₀T (S.anchor_mem i)) _ (hF₀T hy)
    have hri : W.radius i ≤ dist (W.center i) y / a := by
      rw [le_div_iff₀ ha]
      linarith
    have hnv : dist (S.nodeValue coef f i) (f (S.anchor i)) ≤ C₁ * L * W.radius i := by
      rw [dist_eq_norm]
      exact hanc i
    calc dist (S.nodeValue coef f i) (f y)
        ≤ dist (S.nodeValue coef f i) (f (S.anchor i)) + dist (f (S.anchor i)) (f y) :=
          dist_triangle _ _ _
      _ ≤ C₁ * L * (dist (W.center i) y / a) + L * (2 * dist (W.center i) y) :=
          add_le_add (hnv.trans (mul_le_mul_of_nonneg_left hri (by positivity)))
            (hfa.trans (mul_le_mul_of_nonneg_left hay hL))
      _ = (C₁ / a + 2) * (L * dist (W.center i) y) := by ring
      _ ≤ (C₁ / a + 2 + (2 * C₁ / s₀ + 1 + 2 * |b| / s₀)) * (L * dist (W.center i) y) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  -- two distinct centers
  have h3 : ∀ i j, i ≠ j → dist (S.nodeValue coef f i) (S.nodeValue coef f j) ≤
      (C₁ / a + 2 + (2 * C₁ / s₀ + 1 + 2 * |b| / s₀)) * L *
        dist (W.center i) (W.center j) := by
    intro i j hij
    have hmax := hsep i j hij
    have hri : W.radius i ≤ dist (W.center i) (W.center j) / s₀ := by
      rw [le_div_iff₀ hs₀]
      have := mul_le_mul_of_nonneg_left (le_max_left (W.radius i) (W.radius j)) hs₀.le
      linarith
    have hrj : W.radius j ≤ dist (W.center i) (W.center j) / s₀ := by
      rw [le_div_iff₀ hs₀]
      have := mul_le_mul_of_nonneg_left (le_max_right (W.radius i) (W.radius j)) hs₀.le
      linarith
    have hai : dist (W.center i) (S.anchor i) ≤ |b| * W.radius i := by
      rw [S.dist_anchor i]
      exact (hb i).trans (mul_le_mul_of_nonneg_right (le_abs_self b) (W.radius_pos i).le)
    have haj : dist (W.center j) (S.anchor j) ≤ |b| * W.radius j := by
      rw [S.dist_anchor j]
      exact (hb j).trans (mul_le_mul_of_nonneg_right (le_abs_self b) (W.radius_pos j).le)
    have haa : dist (S.anchor i) (S.anchor j) ≤
        |b| * W.radius i + dist (W.center i) (W.center j) + |b| * W.radius j := by
      have h1 := dist_triangle4 (S.anchor i) (W.center i) (W.center j) (S.anchor j)
      rw [dist_comm (S.anchor i) (W.center i)] at h1
      linarith
    have hfa : dist (f (S.anchor i)) (f (S.anchor j)) ≤ L * dist (S.anchor i) (S.anchor j) :=
      hfL.dist_le_mul _ (hF₀T (S.anchor_mem i)) _ (hF₀T (S.anchor_mem j))
    have hni : dist (S.nodeValue coef f i) (f (S.anchor i)) ≤ C₁ * L * W.radius i := by
      rw [dist_eq_norm]
      exact hanc i
    have hnj : dist (f (S.anchor j)) (S.nodeValue coef f j) ≤ C₁ * L * W.radius j := by
      rw [dist_comm, dist_eq_norm]
      exact hanc j
    have htri := dist_triangle4 (S.nodeValue coef f i) (f (S.anchor i)) (f (S.anchor j))
      (S.nodeValue coef f j)
    have hLaa := mul_le_mul_of_nonneg_left haa hL
    calc dist (S.nodeValue coef f i) (S.nodeValue coef f j)
        ≤ C₁ * L * W.radius i +
            L * (|b| * W.radius i + dist (W.center i) (W.center j) + |b| * W.radius j) +
            C₁ * L * W.radius j := by linarith
      _ ≤ C₁ * L * (dist (W.center i) (W.center j) / s₀) +
            L * (|b| * (dist (W.center i) (W.center j) / s₀) + dist (W.center i) (W.center j) +
              |b| * (dist (W.center i) (W.center j) / s₀)) +
            C₁ * L * (dist (W.center i) (W.center j) / s₀) := by
          gcongr
      _ = (2 * C₁ / s₀ + 1 + 2 * |b| / s₀) * (L * dist (W.center i) (W.center j)) := by ring
      _ ≤ (C₁ / a + 2 + (2 * C₁ / s₀ + 1 + 2 * |b| / s₀)) *
            (L * dist (W.center i) (W.center j)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  refine ⟨hnodeC, hnodeF, LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_⟩
  rw [NNReal.coe_mul, Real.coe_toNNReal _ hK0]
  simp only [WhitneyData.nodeSet, Set.mem_union, Set.mem_range] at hp hq
  rcases hp with hp | ⟨i, rfl⟩ <;> rcases hq with hq | ⟨j, rfl⟩
  · rw [hnodeF p hp, hnodeF q hq]
    have hCa : 0 ≤ C₁ / a := by positivity
    have hK1 : 1 ≤ C₁ / a + 2 + (2 * C₁ / s₀ + 1 + 2 * |b| / s₀) := by linarith
    calc dist (f p) (f q) ≤ L * dist p q := hfL.dist_le_mul _ (hF₀T hp) _ (hF₀T hq)
      _ = 1 * (L * dist p q) := by ring
      _ ≤ (C₁ / a + 2 + (2 * C₁ / s₀ + 1 + 2 * |b| / s₀)) * (L * dist p q) :=
          mul_le_mul_of_nonneg_right hK1 (by positivity)
      _ = _ := by ring
  · rw [hnodeF p hp, hnodeC j, dist_comm (f p), dist_comm p]
    exact h2 j p hp
  · rw [hnodeC i, hnodeF q hq]
    exact h2 i q hq
  · rw [hnodeC i, hnodeC j]
    by_cases hij : i = j
    · subst hij
      simp
    · exact h3 i j hij

/-! ## Change of scale for `ds/s` -/

/-- The scale measure `ds/s` is invariant under `s ↦ c s`, `c > 0`. -/
theorem scaleMeasure_map_mul_left {c : ℝ} (hc : 0 < c) :
    Measure.map (fun s => c * s) scaleMeasure = scaleMeasure := by
  ext A hA
  have hA' : MeasurableSet (A ∩ Ioi 0) := hA.inter measurableSet_Ioi
  have hpre : MeasurableSet ((fun s => c * s) ⁻¹' A) := measurable_const_mul c hA
  rw [Measure.map_apply (measurable_const_mul c) hA, scaleMeasure_apply _ hpre,
    scaleMeasure_apply _ hA]
  have hset : (fun s => c * s) ⁻¹' A ∩ Ioi 0 = (fun s => c * s) ⁻¹' (A ∩ Ioi 0) := by
    ext r
    simp only [mem_inter_iff, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, mul_pos hc h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, pos_of_mul_pos_right h2 hc.le⟩
  rw [hset, ← lintegral_indicator (measurable_const_mul c hA'), ← lintegral_indicator hA']
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ≥0∞,
      G = (A ∩ Ioi 0).indicator (fun t => ENNReal.ofReal (1 / t)) := ⟨_, rfl⟩
  rw [← hG]
  have hfun : ∀ r, ((fun s => c * s) ⁻¹' (A ∩ Ioi 0)).indicator
      (fun r => ENNReal.ofReal (1 / r)) r = ENNReal.ofReal c * G (c * r) := by
    intro r
    rw [hG]
    by_cases hr : c * r ∈ A ∩ Ioi 0
    · rw [indicator_of_mem (show r ∈ (fun s => c * s) ⁻¹' (A ∩ Ioi 0) from hr),
        indicator_of_mem hr, ← ENNReal.ofReal_mul hc.le, mul_one_div,
        div_mul_cancel_left₀ hc.ne', one_div]
    · rw [indicator_of_notMem (show r ∉ (fun s => c * s) ⁻¹' (A ∩ Ioi 0) from hr),
        indicator_of_notMem hr, mul_zero]
  have hmap : ∫⁻ r, G (c * r) = ENNReal.ofReal |c⁻¹| * ∫⁻ t, G t := by
    calc
      ∫⁻ r, G (c * r) = ∫⁻ t, G t ∂(Measure.map (fun s => c * s) volume) :=
        (lintegral_map_equiv G (MeasurableEquiv.mulLeft₀ c hc.ne')).symm
      _ = ∫⁻ t, G t ∂(ENNReal.ofReal |c⁻¹| • volume) := by
        rw [Real.map_volume_mul_left hc.ne']
      _ = ENNReal.ofReal |c⁻¹| * ∫⁻ t, G t := by
        rw [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_congr hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmap, ← mul_assoc,
    ← ENNReal.ofReal_mul hc.le, abs_of_pos (inv_pos.mpr hc), mul_inv_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]

/-- Change of scale `t = c s` for `ds/s`, valid for every function. -/
theorem setLIntegral_scaleMeasure_comp_mul_left {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ≥0∞)
    (T : Set ℝ) :
    ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure = ∫⁻ t in T, f t ∂scaleMeasure := by
  set e := MeasurableEquiv.mulLeft₀ c hc.ne' with he_def
  have he : ⇑e = fun s => c * s := MeasurableEquiv.coe_mulLeft₀ hc.ne'
  symm
  calc
    ∫⁻ t in T, f t ∂scaleMeasure = ∫⁻ t in T, f t ∂(Measure.map e scaleMeasure) := by
      rw [he, scaleMeasure_map_mul_left hc]
    _ = ∫⁻ t, f t ∂((scaleMeasure.restrict (e ⁻¹' T)).map e) := by
      rw [e.measurableEmbedding.restrict_map]
    _ = ∫⁻ s, f (e s) ∂(scaleMeasure.restrict (e ⁻¹' T)) := lintegral_map_equiv f e
    _ = ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure := by
      rw [he]

/-- **Change of scale.** Bound
the integrand, enlarge `(ρ, ∞)` to `(0, ∞)`, and substitute `r = C₁ s`; the measure `ds/s`
is dilation invariant and the substitution is valid for arbitrary integrands. -/
theorem lintegral_Ioi_scaleMeasure_le_of_le_comp_mul_proof (e γ : ℝ → ℝ≥0∞) (ρ C C₁ : ℝ)
    (hρ : 0 ≤ ρ) (hC₁ : 0 < C₁) (h : ∀ s, ρ < s → e s ≤ ENNReal.ofReal C * γ (C₁ * s)) :
    ∫⁻ s in Ioi ρ, e s ∂scaleMeasure ≤ ENNReal.ofReal C * ∫⁻ r in Ioi 0, γ r ∂scaleMeasure := by
  have hpre : (fun s => C₁ * s) ⁻¹' Ioi 0 = Ioi 0 := by
    ext s
    simp only [mem_preimage, mem_Ioi]
    exact ⟨fun h => pos_of_mul_pos_right h hC₁.le, fun h => mul_pos hC₁ h⟩
  calc ∫⁻ s in Ioi ρ, e s ∂scaleMeasure
      ≤ ∫⁻ s in Ioi ρ, ENNReal.ofReal C * γ (C₁ * s) ∂scaleMeasure :=
        setLIntegral_mono' measurableSet_Ioi fun s hs => h s hs
    _ = ENNReal.ofReal C * ∫⁻ s in Ioi ρ, γ (C₁ * s) ∂scaleMeasure :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ∫⁻ s in Ioi 0, γ (C₁ * s) ∂scaleMeasure :=
        mul_le_mul_right (lintegral_mono_set (Ioi_subset_Ioi hρ)) _
    _ = ENNReal.ofReal C * ∫⁻ r in Ioi 0, γ r ∂scaleMeasure := by
        rw [← setLIntegral_scaleMeasure_comp_mul_left hC₁ γ (Ioi 0), hpre]

/-! ## Node Carleson bound -/

/-- **Node Carleson bound.** The trace part is
at most `B |P(z,R)|`. A cell term vanishes unless `p_j ∈ P(z,R)` and `r_j < R`; then it is at
most `B |Q_j|`, and those disjoint cells lie in `P(z,(1+D)R)`. Hence the bound with
`C = 2 ω_m (1 + (1+|D|)^(m+2))`. -/
theorem whitney_node_carleson_le_proof (m : ℕ) (D a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a) {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      (g : Space m → Y) (L : ℝ≥0) (B : ℝ), 0 ≤ B →
      (∀ p ∈ F₀, ∫⁻ s in Ioi 0, constrainedAffineErrorSq W.nodeMeasure g L p s ∂scaleMeasure ≤
        ENNReal.ofReal B) →
      (∀ i, ∫⁻ s in Ioi (W.radius i),
          constrainedAffineErrorSq W.nodeMeasure g L (W.center i) s ∂scaleMeasure ≤
        ENNReal.ofReal B) →
      ∀ (z : Space m) (R : ℝ), 0 < R →
        W.nodeCarlesonIntegral g L z R ≤ ENNReal.ofReal (C * B * R ^ (m + 2)) := by
  classical
  set ω : ℝ := (omega m).toReal with hω
  have hωeq : omega m = ENNReal.ofReal ω := (ENNReal.ofReal_toReal (omega_lt_top m).ne).symm
  have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
  refine ⟨2 * ω * (1 + (1 + |D|) ^ (m + 2)), by positivity, ?_⟩
  intro ι _ F₀ W Y _ _ g L B hB hF hc z R hR
  have hD : 1 ≤ D := W.one_le_D
  have hDabs : |D| = D := abs_of_pos (by linarith)
  have hball : ∀ ρ : ℝ, 0 < ρ →
      parabolicVolume m (Metric.ball z ρ) = ENNReal.ofReal (2 * ω * ρ ^ (m + 2)) := by
    intro ρ hρ
    rw [parabolicVolume_ball z ρ hρ, hωeq, ← ENNReal.ofReal_pow hρ.le,
      ENNReal.ofReal_mul (mul_nonneg (by norm_num) hω0),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hF₀m : MeasurableSet F₀ := by
    have h := MeasurableSet.iUnion W.measurableSet_cell
    rw [W.iUnion_cell] at h
    exact h.of_compl
  -- the trace part
  have h1 : ∫⁻ p in F₀ ∩ Metric.ball z R, ∫⁻ s in Ioo 0 R,
        constrainedAffineErrorSq W.nodeMeasure g L p s ∂scaleMeasure ∂parabolicVolume m ≤
      ENNReal.ofReal B * ENNReal.ofReal (2 * ω * R ^ (m + 2)) := by
    calc ∫⁻ p in F₀ ∩ Metric.ball z R, ∫⁻ s in Ioo 0 R,
          constrainedAffineErrorSq W.nodeMeasure g L p s ∂scaleMeasure ∂parabolicVolume m
        ≤ ∫⁻ _p in F₀ ∩ Metric.ball z R, ENNReal.ofReal B ∂parabolicVolume m :=
          setLIntegral_mono' (hF₀m.inter measurableSet_ball) fun p hp =>
            (lintegral_mono_set Ioo_subset_Ioi_self).trans (hF p hp.1)
      _ = ENNReal.ofReal B * parabolicVolume m (F₀ ∩ Metric.ball z R) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal (2 * ω * R ^ (m + 2)) := by
          rw [← hball R hR]
          exact mul_le_mul_right (measure_mono Set.inter_subset_right) _
  -- the cells that contribute
  let c : ι → Set (Space m) := fun j =>
    if W.center j ∈ Metric.ball z R ∧ W.radius j < R then W.cell j else ∅
  have hcm : ∀ j, MeasurableSet (c j) := by
    intro j
    simp only [c]
    split_ifs
    · exact W.measurableSet_cell j
    · exact MeasurableSet.empty
  have hcd : Pairwise (Disjoint on c) := by
    intro i j hij
    simp only [Function.onFun, c]
    split_ifs
    · exact W.pairwise_disjoint hij
    · exact Set.disjoint_empty _
    · exact Set.empty_disjoint _
    · exact Set.disjoint_empty _
  have hDR : 0 < (1 + D) * R := mul_pos (by linarith) hR
  have hcsub : ⋃ j, c j ⊆ Metric.ball z ((1 + D) * R) := by
    refine Set.iUnion_subset fun j q hq => ?_
    simp only [c] at hq
    split_ifs at hq with hcond
    · have hq' := W.cell_subset j hq
      rw [Metric.mem_closedBall] at hq'
      rw [Metric.mem_ball]
      have hpz : dist (W.center j) z < R := hcond.1
      have htri := dist_triangle q (W.center j) z
      have hDr : D * W.radius j ≤ D * R := mul_le_mul_of_nonneg_left hcond.2.le (by linarith)
      linarith
    · exact hq.elim
  have hterm : ∀ j, (Metric.ball z R).indicator
        (fun _ => ENNReal.ofReal (W.radius j ^ (m + 2))) (W.center j) *
      ∫⁻ s in Ioo (W.radius j) R,
        constrainedAffineErrorSq W.nodeMeasure g L (W.center j) s ∂scaleMeasure ≤
      ENNReal.ofReal B * parabolicVolume m (c j) := by
    intro j
    by_cases hpz : W.center j ∈ Metric.ball z R
    · rw [Set.indicator_of_mem hpz]
      by_cases hrR : W.radius j < R
      · have hcj : c j = W.cell j := ite_eq_left ⟨hpz, hrR⟩
        rw [hcj, W.volume_cell j, mul_comm (ENNReal.ofReal B)]
        exact mul_le_mul_right ((lintegral_mono_set Ioo_subset_Ioi_self).trans (hc j)) _
      · rw [Set.Ioo_eq_empty hrR]
        simp
    · rw [Set.indicator_of_notMem hpz, zero_mul]
      exact zero_le
  have h2 : (∑' j, (Metric.ball z R).indicator
        (fun _ => ENNReal.ofReal (W.radius j ^ (m + 2))) (W.center j) *
      ∫⁻ s in Ioo (W.radius j) R,
        constrainedAffineErrorSq W.nodeMeasure g L (W.center j) s ∂scaleMeasure) ≤
      ENNReal.ofReal B * ENNReal.ofReal (2 * ω * ((1 + D) * R) ^ (m + 2)) := by
    calc _ ≤ ∑' j, ENNReal.ofReal B * parabolicVolume m (c j) := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal B * parabolicVolume m (⋃ j, c j) := by
          rw [ENNReal.tsum_mul_left, measure_iUnion hcd hcm]
      _ ≤ ENNReal.ofReal B * parabolicVolume m (Metric.ball z ((1 + D) * R)) :=
          mul_le_mul_right (measure_mono hcsub) _
      _ = _ := by rw [hball _ hDR]
  unfold WhitneyData.nodeCarlesonIntegral
  have hn1 : 0 ≤ B * (2 * ω * R ^ (m + 2)) := by positivity
  have hn2 : 0 ≤ B * (2 * ω * ((1 + D) * R) ^ (m + 2)) :=
    mul_nonneg hB (mul_nonneg (mul_nonneg (by norm_num) hω0) (pow_nonneg hDR.le _))
  calc _ ≤ ENNReal.ofReal B * ENNReal.ofReal (2 * ω * R ^ (m + 2)) +
        ENNReal.ofReal B * ENNReal.ofReal (2 * ω * ((1 + D) * R) ^ (m + 2)) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * ω * (1 + (1 + |D|) ^ (m + 2)) * B * R ^ (m + 2)) := by
        rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_add hn1 hn2,
          hDabs, mul_pow]
        congr 1
        ring

end ParabolicRectifiability
