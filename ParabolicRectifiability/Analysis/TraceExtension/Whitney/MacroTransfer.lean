import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Filling
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Defect

/-! # Macroscopic transfer from the nodes to the Whitney filling

Let
`F = whitneyFilling φ g` for an `L`-Lipschitz `g` on the node set, let `ν` be the
full node measure, `s > 0` and `d_P(y,F₀) ≤ 2s`, and put `C₂ = 1 + 3D/a`.

For a fixed spatial affine competitor `A(q) = c₀ + B q_u` with `‖B‖ ≤ L`, on each cell
`Q_j` the node deviation of `whitneyFilling_sub_le_proof` gives
`‖F(q) - A(q)‖ ≤ ‖g(p_j) - A(p_j)‖ + (H+D) L r_j`. Incident cells have
`p_j ∈ P(y, C₂ s)` (open ball, no enlargement) and `|Q_j| = r_j^k`. Splitting
`P(y,s)` into `F₀` and the measurable cell pieces, where `F = g` on `F₀`, gives the
fixed-affine integral comparison
`∫_{P(y,s)} ‖F - A‖² ≤ 2 ∫_{P(y,C₂ s)} ‖g - A‖² dν + 2(H+D)² L² Σ_{J(y,s)} r_j^(k+2)`.
Multiplying by `s^(-k-2) = C₂^(k+2) (C₂ s)^(-k-2)` and taking the constrained infimum
on the right after the unrestricted infimum on the left gives the transfer
inequality. No measurability of the residuals and no attainment is needed: all
comparisons are monotonicity, subadditivity and countable subadditivity of the
lower Lebesgue integral.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-- The homogeneous dimension of the ordinary spatial base is `k = m + 2`. -/
theorem baseDimension_spatial (m : ℕ) : baseDimension (Spatial m) = m + 2 := by
  rw [baseDimension, finrank_euclideanSpace_fin]

theorem baseDimension_spatial_add_two (m : ℕ) : baseDimension (Spatial m) + 2 = m + 4 := by
  have h := baseDimension_spatial m
  omega

namespace WhitneyData

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a : ℝ}

/-- Decomposition of a set integral against the full node measure into its continuous
part on `F₀` and its atoms `r_j^k δ_{p_j}`. -/
theorem setLIntegral_nodeMeasure (W : WhitneyData m ι F₀ D a) {S : Set (Space m)}
    (hS : MeasurableSet S) (f : Space m → ℝ≥0∞) :
    ∫⁻ q in S, f q ∂W.nodeMeasure =
      ∫⁻ q in S ∩ F₀, f q ∂parabolicVolume m +
        ∑' j, ENNReal.ofReal (W.radius j ^ (m + 2)) * S.indicator f (W.center j) := by
  rw [← lintegral_indicator hS, nodeMeasure, lintegral_add_measure, lintegral_indicator hS,
    Measure.restrict_restrict hS, lintegral_sum_measure]
  congr 1
  refine tsum_congr fun j => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

end WhitneyData

section Transfer

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a H : ℝ}
  {W : WhitneyData m ι F₀ D a} {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Pointwise fixed-affine comparison on a cell:
`‖F(q) - A(q)‖ ≤ ‖g(p_j) - A(p_j)‖ + (H+D) L r_j` for `‖B‖ ≤ L`. -/
theorem norm_whitneyFilling_sub_affine_le (φ : WhitneyWeights W H) (g : Space m → Y)
    {L : ℝ≥0} (hg : LipschitzOnWith L g W.nodeSet) {j : ι} {q : Space m}
    (hq : q ∈ W.cell j) (c₀ : Y) {B : Spatial m →L[ℝ] Y} (hB : ‖B‖ ≤ L) :
    ‖whitneyFilling φ g q - (c₀ + B q.1)‖ ≤
      ‖g (W.center j) - (c₀ + B (W.center j).1)‖ + (H + D) * L * W.radius j := by
  have h1 := norm_whitneyFilling_sub_center_le φ g hg hq
  have h2 : ‖B ((W.center j).1 - q.1)‖ ≤ L * (D * W.radius j) := by
    calc
      ‖B ((W.center j).1 - q.1)‖ ≤ ‖B‖ * ‖(W.center j).1 - q.1‖ := B.le_opNorm _
      _ ≤ L * (D * W.radius j) := by
        refine mul_le_mul hB ?_ (norm_nonneg _) (NNReal.coe_nonneg L)
        calc
          ‖(W.center j).1 - q.1‖ = dist (W.center j).1 q.1 := (dist_eq_norm _ _).symm
          _ ≤ dist (W.center j) q := by
            rw [Prod.dist_eq]
            exact le_max_left _ _
          _ = dist q (W.center j) := dist_comm _ _
          _ ≤ D * W.radius j := W.dist_center_le hq
  have hdecomp : whitneyFilling φ g q - (c₀ + B q.1) =
      (whitneyFilling φ g q - g (W.center j)) + (g (W.center j) - (c₀ + B (W.center j).1)) +
        B ((W.center j).1 - q.1) := by
    rw [map_sub]
    abel
  rw [hdecomp]
  calc
    ‖(whitneyFilling φ g q - g (W.center j)) + (g (W.center j) - (c₀ + B (W.center j).1)) +
        B ((W.center j).1 - q.1)‖
        ≤ ‖whitneyFilling φ g q - g (W.center j)‖ +
            ‖g (W.center j) - (c₀ + B (W.center j).1)‖ + ‖B ((W.center j).1 - q.1)‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ ‖g (W.center j) - (c₀ + B (W.center j).1)‖ + (H + D) * L * W.radius j := by
      linarith

/-- Elementary squaring: `u ≤ e + d` with `0 ≤ u, e` gives `u² ≤ 2e² + 2d²`. -/
theorem ofReal_sq_le_two_mul_add {u e d : ℝ} (hu : 0 ≤ u) (he : 0 ≤ e) (hle : u ≤ e + d) :
    ENNReal.ofReal u ^ 2 ≤ 2 * ENNReal.ofReal e ^ 2 + ENNReal.ofReal (2 * d ^ 2) := by
  have h1 : u ^ 2 ≤ (e + d) ^ 2 := pow_le_pow_left₀ hu hle 2
  have key : u ^ 2 ≤ 2 * e ^ 2 + 2 * d ^ 2 := by nlinarith [sq_nonneg (e - d)]
  rw [← ENNReal.ofReal_pow hu, ← ENNReal.ofReal_pow he]
  calc
    ENNReal.ofReal (u ^ 2) ≤ ENNReal.ofReal (2 * e ^ 2 + 2 * d ^ 2) :=
      ENNReal.ofReal_le_ofReal key
    _ = 2 * ENNReal.ofReal (e ^ 2) + ENNReal.ofReal (2 * d ^ 2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- Squared pointwise comparison on a cell. -/
theorem enorm_whitneyFilling_sub_affine_sq_le (φ : WhitneyWeights W H) (g : Space m → Y)
    {L : ℝ≥0} (hg : LipschitzOnWith L g W.nodeSet) {j : ι} {q : Space m}
    (hq : q ∈ W.cell j) (c₀ : Y) {B : Spatial m →L[ℝ] Y} (hB : ‖B‖ ≤ L) :
    ‖whitneyFilling φ g q - (c₀ + B q.1)‖ₑ ^ 2 ≤
      2 * ‖g (W.center j) - (c₀ + B (W.center j).1)‖ₑ ^ 2 +
        ENNReal.ofReal (2 * ((H + D) * L * W.radius j) ^ 2) := by
  rw [← ofReal_norm, ← ofReal_norm]
  exact ofReal_sq_le_two_mul_add (norm_nonneg _) (norm_nonneg _)
    (norm_whitneyFilling_sub_affine_le φ g hg hq c₀ hB)

/-- Cell contribution: the integral of the squared residual over `P(y,s) ∩ Q_j` is
controlled by the atom of `ν` at `p_j ∈ P(y, C₂ s)` and the cube-defect term. -/
theorem setLIntegral_ball_inter_cell_le (φ : WhitneyWeights W H) (g : Space m → Y)
    {L : ℝ≥0} (hg : LipschitzOnWith L g W.nodeSet) {y : Space m} {s : ℝ}
    (hy : Metric.infDist y F₀ ≤ 2 * s) (c₀ : Y) {B : Spatial m →L[ℝ] Y} (hB : ‖B‖ ≤ L)
    (j : ι) :
    ∫⁻ q in Metric.ball y s ∩ W.cell j, ‖whitneyFilling φ g q - (c₀ + B q.1)‖ₑ ^ 2
        ∂parabolicVolume m ≤
      2 * (ENNReal.ofReal (W.radius j ^ (m + 2)) *
          (Metric.ball y ((1 + 3 * D / a) * s)).indicator
            (fun q => ‖g q - (c₀ + B q.1)‖ₑ ^ 2) (W.center j)) +
        ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) *
          (W.incidence y s).indicator (fun j => ENNReal.ofReal (W.radius j ^ (m + 4))) j := by
  by_cases hj : j ∈ W.incidence y s
  · rw [indicator_of_mem (W.center_mem_ball_of_mem_incidence hy hj), indicator_of_mem hj]
    have e1 : ENNReal.ofReal (2 * ((H + D) * L * W.radius j) ^ 2) *
          ENNReal.ofReal (W.radius j ^ (m + 2)) =
        ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) *
          ENNReal.ofReal (W.radius j ^ (m + 4)) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * ((H + D) * L * W.radius j) ^ 2),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (H + D) ^ 2 * (L : ℝ) ^ 2)]
      congr 1
      ring
    calc
      ∫⁻ q in Metric.ball y s ∩ W.cell j, ‖whitneyFilling φ g q - (c₀ + B q.1)‖ₑ ^ 2
          ∂parabolicVolume m
          ≤ ∫⁻ _ in Metric.ball y s ∩ W.cell j,
              (2 * ‖g (W.center j) - (c₀ + B (W.center j).1)‖ₑ ^ 2 +
                ENNReal.ofReal (2 * ((H + D) * L * W.radius j) ^ 2)) ∂parabolicVolume m :=
        setLIntegral_mono' (measurableSet_ball.inter (W.measurableSet_cell j)) fun q hq =>
          enorm_whitneyFilling_sub_affine_sq_le φ g hg hq.2 c₀ hB
      _ = (2 * ‖g (W.center j) - (c₀ + B (W.center j).1)‖ₑ ^ 2 +
            ENNReal.ofReal (2 * ((H + D) * L * W.radius j) ^ 2)) *
            parabolicVolume m (Metric.ball y s ∩ W.cell j) := setLIntegral_const _ _
      _ ≤ (2 * ‖g (W.center j) - (c₀ + B (W.center j).1)‖ₑ ^ 2 +
            ENNReal.ofReal (2 * ((H + D) * L * W.radius j) ^ 2)) *
            parabolicVolume m (W.cell j) := mul_le_mul_right (measure_mono inter_subset_right) _
      _ = _ := by
        rw [W.volume_cell j, add_mul, e1]
        ring
  · have hempty : Metric.ball y s ∩ W.cell j = ∅ := by
      rw [inter_comm]
      exact not_nonempty_iff_eq_empty.mp hj
    rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le

/-- The fixed-affine integral comparison: for an admissible competitor `‖B‖ ≤ L`,
`∫_{P(y,s)} ‖F - A‖² ≤ 2 ∫_{P(y,C₂ s)} ‖g - A‖² dν + 2(H+D)² L² Σ_{J(y,s)} r_j^(k+2)`. -/
theorem affineFitIntegral_whitneyFilling_le [Countable ι] (hF₀ : IsClosed F₀)
    (φ : WhitneyWeights W H)
    (g : Space m → Y) {L : ℝ≥0} (hg : LipschitzOnWith L g W.nodeSet) {y : Space m} {s : ℝ}
    (hs : 0 < s) (hy : Metric.infDist y F₀ ≤ 2 * s) (c₀ : Y) {B : Spatial m →L[ℝ] Y}
    (hB : ‖B‖ ≤ L) :
    affineFitIntegral (parabolicVolume m) (whitneyFilling φ g) c₀ B y s ≤
      2 * affineFitIntegral W.nodeMeasure g c₀ B y ((1 + 3 * D / a) * s) +
        ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) *
          ∑' j, (W.incidence y s).indicator (fun j => ENNReal.ofReal (W.radius j ^ (m + 4))) j := by
  have ha : 0 < a := W.a_pos
  have hD : 0 ≤ D := zero_le_one.trans W.one_le_D
  have hss : s ≤ (1 + 3 * D / a) * s := by
    have : 0 ≤ 3 * D / a * s := mul_nonneg (div_nonneg (by linarith) ha.le) hs.le
    linarith
  have hcover : Metric.ball y s ⊆ (Metric.ball y s ∩ F₀) ∪ ⋃ j, Metric.ball y s ∩ W.cell j := by
    intro q hq
    by_cases hqF : q ∈ F₀
    · exact Or.inl ⟨hq, hqF⟩
    · obtain ⟨j, hj⟩ := W.exists_mem_cell hqF
      exact Or.inr (mem_iUnion.mpr ⟨j, hq, hj⟩)
  have hF0part : ∫⁻ q in Metric.ball y s ∩ F₀, ‖whitneyFilling φ g q - (c₀ + B q.1)‖ₑ ^ 2
        ∂parabolicVolume m ≤
      ∫⁻ q in Metric.ball y ((1 + 3 * D / a) * s) ∩ F₀, ‖g q - (c₀ + B q.1)‖ₑ ^ 2
        ∂parabolicVolume m := by
    calc
      ∫⁻ q in Metric.ball y s ∩ F₀, ‖whitneyFilling φ g q - (c₀ + B q.1)‖ₑ ^ 2
          ∂parabolicVolume m =
          ∫⁻ q in Metric.ball y s ∩ F₀, ‖g q - (c₀ + B q.1)‖ₑ ^ 2 ∂parabolicVolume m :=
        setLIntegral_congr_fun (measurableSet_ball.inter hF₀.measurableSet) fun q hq => by
          simp only [whitneyFilling_of_mem φ g hq.2]
      _ ≤ _ := lintegral_mono_set (inter_subset_inter_left _ (Metric.ball_subset_ball hss))
  unfold affineFitIntegral
  rw [W.setLIntegral_nodeMeasure measurableSet_ball]
  calc
    ∫⁻ q in Metric.ball y s, ‖whitneyFilling φ g q - (c₀ + B q.1)‖ₑ ^ 2 ∂parabolicVolume m
        ≤ ∫⁻ q in (Metric.ball y s ∩ F₀) ∪ ⋃ j, Metric.ball y s ∩ W.cell j,
            ‖whitneyFilling φ g q - (c₀ + B q.1)‖ₑ ^ 2 ∂parabolicVolume m :=
      lintegral_mono_set hcover
    _ ≤ (∫⁻ q in Metric.ball y s ∩ F₀, ‖whitneyFilling φ g q - (c₀ + B q.1)‖ₑ ^ 2
            ∂parabolicVolume m) +
          ∑' j, ∫⁻ q in Metric.ball y s ∩ W.cell j,
            ‖whitneyFilling φ g q - (c₀ + B q.1)‖ₑ ^ 2 ∂parabolicVolume m :=
      (lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_iUnion_le _ _))
    _ ≤ (∫⁻ q in Metric.ball y ((1 + 3 * D / a) * s) ∩ F₀, ‖g q - (c₀ + B q.1)‖ₑ ^ 2
            ∂parabolicVolume m) +
          ∑' j, (2 * (ENNReal.ofReal (W.radius j ^ (m + 2)) *
              (Metric.ball y ((1 + 3 * D / a) * s)).indicator
                (fun q => ‖g q - (c₀ + B q.1)‖ₑ ^ 2) (W.center j)) +
            ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) *
              (W.incidence y s).indicator (fun j => ENNReal.ofReal (W.radius j ^ (m + 4))) j) :=
      add_le_add hF0part (ENNReal.tsum_le_tsum fun j =>
        setLIntegral_ball_inter_cell_le φ g hg hy c₀ hB j)
    _ = (∫⁻ q in Metric.ball y ((1 + 3 * D / a) * s) ∩ F₀, ‖g q - (c₀ + B q.1)‖ₑ ^ 2
            ∂parabolicVolume m) +
          (2 * ∑' j, ENNReal.ofReal (W.radius j ^ (m + 2)) *
              (Metric.ball y ((1 + 3 * D / a) * s)).indicator
                (fun q => ‖g q - (c₀ + B q.1)‖ₑ ^ 2) (W.center j) +
            ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) *
              ∑' j, (W.incidence y s).indicator
                (fun j => ENNReal.ofReal (W.radius j ^ (m + 4))) j) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ 2 * ((∫⁻ q in Metric.ball y ((1 + 3 * D / a) * s) ∩ F₀, ‖g q - (c₀ + B q.1)‖ₑ ^ 2
            ∂parabolicVolume m) +
          ∑' j, ENNReal.ofReal (W.radius j ^ (m + 2)) *
              (Metric.ball y ((1 + 3 * D / a) * s)).indicator
                (fun q => ‖g q - (c₀ + B q.1)‖ₑ ^ 2) (W.center j)) +
          ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) *
            ∑' j, (W.incidence y s).indicator
              (fun j => ENNReal.ofReal (W.radius j ^ (m + 4))) j := by
      set I₀ := ∫⁻ q in Metric.ball y ((1 + 3 * D / a) * s) ∩ F₀, ‖g q - (c₀ + B q.1)‖ₑ ^ 2
        ∂parabolicVolume m
      have h2 : I₀ ≤ 2 * I₀ := by
        rw [two_mul]
        exact le_self_add
      calc
        _ ≤ 2 * I₀ + _ := add_le_add h2 le_rfl
        _ = _ := by ring

end Transfer

section Bookkeeping

/-- Infimum bookkeeping: a bound for every admissible competitor passes to the
unrestricted infimum on the left and the constrained infimum on the right. -/
theorem iInf₂_le_two_mul_iInf_add {α β : Sort*} {P : α → β → Prop} {F G : α → β → ℝ≥0∞}
    {K : ℝ≥0∞} (h : ∀ a b, P a b → F a b ≤ 2 * G a b + K) :
    (⨅ (a) (b), F a b) ≤ 2 * (⨅ (a) (b) (_ : P a b), G a b) + K := by
  rw [ENNReal.mul_iInf_of_ne two_ne_zero ENNReal.ofNat_ne_top, ENNReal.iInf_add]
  refine le_iInf fun a => ?_
  rw [ENNReal.mul_iInf_of_ne two_ne_zero ENNReal.ofNat_ne_top, ENNReal.iInf_add]
  refine le_iInf fun b => ?_
  rw [ENNReal.mul_iInf_of_ne two_ne_zero ENNReal.ofNat_ne_top, ENNReal.iInf_add]
  exact le_iInf fun hP => (iInf₂_le a b).trans (h a b hP)

/-- Change of normalization: `C^n (C s)^(-n) = s^(-n)` for `C > 0`. -/
theorem ofReal_pow_mul_inv_ofReal_mul_pow {C s : ℝ} (hC : 0 < C) (n : ℕ) :
    ENNReal.ofReal (C ^ n) * (ENNReal.ofReal (C * s))⁻¹ ^ n = (ENNReal.ofReal s)⁻¹ ^ n := by
  have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  rw [ENNReal.ofReal_pow hC.le, ← mul_pow, ENNReal.ofReal_mul hC.le,
    ENNReal.mul_inv (Or.inl hC0) (Or.inl ENNReal.ofReal_ne_top), ← mul_assoc,
    ENNReal.mul_inv_cancel hC0 ENNReal.ofReal_ne_top, one_mul]

/-- Normalized form of the transfer inequality. -/
theorem mul_le_two_mul_mul_add_of_le {T T' X I J S K : ℝ≥0∞} (hT : X * T' = T)
    (h : J ≤ 2 * I + K * S) : T * J ≤ 2 * X * (T' * I) + K * (T * S) :=
  calc
    T * J ≤ T * (2 * I + K * S) := mul_le_mul_right h T
    _ = 2 * X * (T' * I) + K * (T * S) := by
      rw [← hT]
      ring

end Bookkeeping

/-- **Macroscopic transfer:** for `s > 0` and `dist(y,F₀) ≤ 2s`, with `C₂ = 1 + 3D/a`,
`κ_F(y,s)^2 ≤ 2 C₂^(k+2) α_{g,ν,L}(y, C₂ s)^2 + 2(H+D)^2 L^2 s^(-k-2) Σ_{J(y,s)} r_j^(k+2)`,
for the actual filling `F` of an `L`-Lipschitz `g` on the node set, the full node
measure `ν`, and the constrained infimum taken after the fixed-affine comparison. -/
theorem whitney_macro_transfer_proof {m : ℕ} {ι : Type*} [Countable ι] {F₀ : Set (Space m)}
    {D a H : ℝ} (W : WhitneyData m ι F₀ D a) (hF₀ : IsClosed F₀) (_hne : F₀.Nonempty)
    (_hH : 0 ≤ H) (φ : WhitneyWeights W H) {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0) (hg : LipschitzOnWith L g W.nodeSet)
    (y : Space m) (s : ℝ) (hs : 0 < s) (hy : Metric.infDist y F₀ ≤ 2 * s) :
    affineErrorSq (parabolicVolume m) (whitneyFilling φ g) y s ≤
      2 * ENNReal.ofReal ((1 + 3 * D / a) ^ (m + 4)) *
          constrainedAffineErrorSq W.nodeMeasure g L y ((1 + 3 * D / a) * s) +
        ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) * W.cubeDefect y s := by
  have ha : 0 < a := W.a_pos
  have hD : 0 ≤ D := zero_le_one.trans W.one_le_D
  have hC : 0 < 1 + 3 * D / a := by
    have : 0 ≤ 3 * D / a := div_nonneg (by linarith) ha.le
    linarith
  have hs' : 0 < (1 + 3 * D / a) * s := mul_pos hC hs
  rw [affineErrorSq_of_pos _ _ _ hs, constrainedAffineErrorSq, ite_eq_left hs',
    baseDimension_spatial_add_two, WhitneyData.cubeDefect]
  refine mul_le_two_mul_mul_add_of_le (ofReal_pow_mul_inv_ofReal_mul_pow hC (m + 4)) ?_
  exact iInf₂_le_two_mul_iInf_add fun c₀ B hB =>
    affineFitIntegral_whitneyFilling_le hF₀ φ g hg hs hy c₀ hB

end ParabolicRectifiability
