import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalWhitneyPartition
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry
import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # The flat Whitney interpolation of a horizontal reference

Proof of `ba1_horizontal_interpolation`, under the name `ba1_horizontal_interpolation_proof` with
the statement type.

With the Whitney cutoffs `ψ_i`, put `h = T` on `D` and
`h = Σ_i ψ_i τ(a_i) / Σ_i ψ_i` off `D` (`b1hint_interp`). Near `x ∉ D`, on `B(x, d(x)/2)`, only
the finitely many indices of the active set contribute, their sum of cutoffs is at least one (the
cube containing the point has cutoff one), so `h` is `C¹` there. All active anchors lie within
`10 d(x)` of `x`, so their anchor times differ by at most `400 L² d(x)²`:

* `|T(x) - h(x)| ≤ 400 L² d(x)²`, since `T(x) = τ(a_j)` for the face `j` containing `x` and `h(x)`
  is a normalized nonnegative combination of anchor times;
* subtracting `c = τ(a_j)`, `h = c + Σ ψ_i (τ(a_i) - c) / Σ ψ_i`, and the quotient rule with
  `‖∇ψ_i‖ ≤ M_k / s_i ≤ 24 M_k / d(x)` and at most `N_k` active indices gives
  `‖∇h(x)‖ ≤ 19200 N_k M_k L² d(x)`;
* at `a ∈ D`, `|h(x) - h(a)| ≤ 121 L² |x - a|²` for every `x`, so `∇h(a) = 0`, and
  `‖∇h(y)‖ ≤ C L² d(y) ≤ C L² |y - a|` gives continuity of `∇h` at `a`.

The constant is `C_k = 400 + 19200 N_k M_k` (`b1hint_const`), a function of `k` only. The
hypothesis `1 ≤ L` of the statement is not needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-! ### Two generic facts -/

section Generic

open Filter Asymptotics Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- A normalized nonnegative combination of values within `Δ` of `c` is within `Δ` of `c`. -/
theorem b1hint_abs_wavg_sub_le (F : Finset ι) (w v : ι → ℝ) (c Δ : ℝ)
    (hw : ∀ i ∈ F, 0 ≤ w i) (hpos : 0 < ∑ i ∈ F, w i) (hv : ∀ i ∈ F, |v i - c| ≤ Δ) :
    |(∑ i ∈ F, w i * v i) / (∑ i ∈ F, w i) - c| ≤ Δ := by
  have hsum : ∑ i ∈ F, w i * (v i - c) = (∑ i ∈ F, w i * v i) - (∑ i ∈ F, w i) * c := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : (∑ i ∈ F, w i * v i) / (∑ i ∈ F, w i) - c =
      (∑ i ∈ F, w i * (v i - c)) / (∑ i ∈ F, w i) := by
    rw [hsum, sub_div, mul_div_cancel_left₀ _ hpos.ne']
  rw [key, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |∑ i ∈ F, w i * (v i - c)| ≤ ∑ i ∈ F, |w i * (v i - c)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ F, w i * Δ := Finset.sum_le_sum fun i hi => by
        rw [abs_mul, abs_of_nonneg (hw i hi)]
        exact mul_le_mul_of_nonneg_left (hv i hi) (hw i hi)
    _ = Δ * ∑ i ∈ F, w i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Quotient rule with bounds: if `Σ ψ_i(x) ≥ 1`, `ψ_i(x) ≥ 0`, `|δ_i| ≤ Δ` and `‖∇ψ_i(x)‖ ≤ B`,
then `y ↦ Σ ψ_i(y) δ_i / Σ ψ_i(y)` has a derivative at `x` of norm at most `2 #F B Δ`. -/
theorem b1hint_hasFDerivAt_wavg (F : Finset ι) (ψ : ι → E → ℝ) (ψ' : ι → E →L[ℝ] ℝ)
    (δ : ι → ℝ) (x : E) {Δ B : ℝ}
    (hψ : ∀ i ∈ F, HasFDerivAt (ψ i) (ψ' i) x) (hnn : ∀ i ∈ F, 0 ≤ ψ i x)
    (hsum : 1 ≤ ∑ i ∈ F, ψ i x) (hδ : ∀ i ∈ F, |δ i| ≤ Δ) (hB : ∀ i ∈ F, ‖ψ' i‖ ≤ B) :
    ∃ g' : E →L[ℝ] ℝ,
      HasFDerivAt (fun y => (∑ i ∈ F, ψ i y * δ i) / ∑ i ∈ F, ψ i y) g' x ∧
        ‖g'‖ ≤ 2 * F.card * B * Δ := by
  have hPpos : 0 < ∑ i ∈ F, ψ i x := lt_of_lt_of_le one_pos hsum
  have hP0 : (∑ i ∈ F, ψ i x) ≠ 0 := hPpos.ne'
  obtain ⟨i₀, hi₀⟩ := Finset.nonempty_of_sum_ne_zero hP0
  have hΔ : 0 ≤ Δ := (abs_nonneg _).trans (hδ i₀ hi₀)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i₀ hi₀)
  have hGd : HasFDerivAt (fun y => ∑ i ∈ F, ψ i y * δ i) (∑ i ∈ F, δ i • ψ' i) x :=
    HasFDerivAt.fun_sum fun i hi => (hψ i hi).mul_const (δ i)
  have hPd : HasFDerivAt (fun y => ∑ i ∈ F, ψ i y) (∑ i ∈ F, ψ' i) x :=
    HasFDerivAt.fun_sum fun i hi => hψ i hi
  have hinv : HasFDerivAt (fun y => (∑ i ∈ F, ψ i y)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((∑ i ∈ F, ψ i x) ^ 2)⁻¹)).comp
        (∑ i ∈ F, ψ' i)) x :=
    (hasFDerivAt_inv hP0).comp x hPd
  have hmul := hGd.mul hinv
  have hfun : (fun y => (∑ i ∈ F, ψ i y * δ i) / ∑ i ∈ F, ψ i y) =
      (fun y => ∑ i ∈ F, ψ i y * δ i) * (fun y => (∑ i ∈ F, ψ i y)⁻¹) := by
    funext y
    simp only [Pi.mul_apply, div_eq_mul_inv]
  refine ⟨(∑ i ∈ F, ψ i x * δ i) • ((ContinuousLinearMap.toSpanSingleton ℝ
      (-((∑ i ∈ F, ψ i x) ^ 2)⁻¹)).comp (∑ i ∈ F, ψ' i)) +
      (∑ i ∈ F, ψ i x)⁻¹ • ∑ i ∈ F, δ i • ψ' i, ?_, ?_⟩
  · rw [hfun]
    exact hmul
  · set P := ∑ i ∈ F, ψ i x with hPdef
    have hsumB : ‖∑ i ∈ F, ψ' i‖ ≤ F.card * B :=
      (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul F _ B hB).trans
        (le_of_eq (nsmul_eq_mul _ _)))
    have hP2 : 0 < (P ^ 2)⁻¹ := inv_pos.2 (pow_pos hPpos 2)
    have hA : ‖(ContinuousLinearMap.toSpanSingleton ℝ (-(P ^ 2)⁻¹)).comp
        (∑ i ∈ F, ψ' i)‖ ≤ (P ^ 2)⁻¹ * (F.card * B) := by
      calc _ ≤ ‖ContinuousLinearMap.toSpanSingleton ℝ (-(P ^ 2)⁻¹)‖ *
            ‖∑ i ∈ F, ψ' i‖ := ContinuousLinearMap.opNorm_comp_le ..
        _ ≤ (P ^ 2)⁻¹ * (F.card * B) := by
            rw [ContinuousLinearMap.norm_toSpanSingleton, norm_neg, Real.norm_eq_abs,
              abs_of_pos hP2]
            exact mul_le_mul_of_nonneg_left hsumB hP2.le
    have hGabs : |∑ i ∈ F, ψ i x * δ i| ≤ Δ * P := by
      calc |∑ i ∈ F, ψ i x * δ i| ≤ ∑ i ∈ F, |ψ i x * δ i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ F, ψ i x * Δ := Finset.sum_le_sum fun i hi => by
            rw [abs_mul, abs_of_nonneg (hnn i hi)]
            exact mul_le_mul_of_nonneg_left (hδ i hi) (hnn i hi)
        _ = Δ * P := by
            rw [hPdef, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hGd' : ‖∑ i ∈ F, δ i • ψ' i‖ ≤ F.card * (Δ * B) := by
      calc ‖∑ i ∈ F, δ i • ψ' i‖ ≤ ∑ i ∈ F, ‖δ i • ψ' i‖ := norm_sum_le _ _
        _ ≤ ∑ _i ∈ F, Δ * B := Finset.sum_le_sum fun i hi => by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul (hδ i hi) (hB i hi) (norm_nonneg _) hΔ
        _ = F.card * (Δ * B) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hPinv : P⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsum
    have hX : 0 ≤ (F.card : ℝ) * B * Δ := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB0) hΔ
    have hPP : P * (P ^ 2)⁻¹ = P⁻¹ := by
      rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hP0, one_mul]
    calc _ ≤ ‖(∑ i ∈ F, ψ i x * δ i) • ((ContinuousLinearMap.toSpanSingleton ℝ
            (-(P ^ 2)⁻¹)).comp (∑ i ∈ F, ψ' i))‖ +
          ‖P⁻¹ • ∑ i ∈ F, δ i • ψ' i‖ := norm_add_le _ _
      _ = |∑ i ∈ F, ψ i x * δ i| * ‖(ContinuousLinearMap.toSpanSingleton ℝ
            (-(P ^ 2)⁻¹)).comp (∑ i ∈ F, ψ' i)‖ + P⁻¹ * ‖∑ i ∈ F, δ i • ψ' i‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (inv_pos.2 hPpos)]
      _ ≤ (Δ * P) * ((P ^ 2)⁻¹ * (F.card * B)) + P⁻¹ * (F.card * (Δ * B)) :=
          add_le_add (mul_le_mul hGabs hA (norm_nonneg _) (mul_nonneg hΔ hPpos.le))
            (mul_le_mul_of_nonneg_left hGd' (inv_pos.2 hPpos).le)
      _ = Δ * (F.card * B) * (P * (P ^ 2)⁻¹) + P⁻¹ * (F.card * (Δ * B)) := by ring
      _ = 2 * P⁻¹ * ((F.card : ℝ) * B * Δ) := by rw [hPP]; ring
      _ ≤ 2 * 1 * ((F.card : ℝ) * B * Δ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPinv two_pos.le) hX
      _ = 2 * F.card * B * Δ := by ring

/-- A function with `|f(x) - f(a)| ≤ K |x - a|²` has derivative zero at `a`. -/
theorem b1hint_hasFDerivAt_zero_of_sq (f : E → ℝ) (a : E) (K : ℝ)
    (hK : ∀ x, |f x - f a| ≤ K * ‖x - a‖ ^ 2) : HasFDerivAt f (0 : E →L[ℝ] ℝ) a := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h1 : (fun h : E => f (a + h) - f a - (0 : E →L[ℝ] ℝ) h) =O[𝓝 0]
      fun h : E => ‖h‖ ^ 2 := by
    refine IsBigO.of_bound K (Eventually.of_forall fun h => ?_)
    rw [zero_apply, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖h‖)]
    have := hK (a + h)
    rwa [add_sub_cancel_left] at this
  exact h1.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)

end Generic

/-! ### The interpolation -/

section Interpolation

open Metric Filter Topology

variable {n k : ℕ} {L : ℝ}

open Classical in
/-- The flat Whitney interpolation: `T` on `D`, and `Σ_i ψ_i τ(a_i) / Σ_i ψ_i` off `D`. -/
def b1hint_interp (H : HorizontalReference n k L) (y : Spatial k) : ℝ :=
  if y ∈ H.domain then H.height y
  else (∑ᶠ i, b1hint_weight H i y * H.height (H.anchor i)) / ∑ᶠ i, b1hint_weight H i y

theorem b1hint_interp_of_mem (H : HorizontalReference n k L) {y : Spatial k}
    (hy : y ∈ H.domain) : b1hint_interp H y = H.height y := by
  unfold b1hint_interp
  simp only [hy, ↓reduceIte]

theorem b1hint_infDist_near (H : HorizontalReference n k L) {x y : Spatial k}
    (hy : dist y x < infDist x H.domain / 2) : infDist x H.domain / 2 < infDist y H.domain := by
  have h := infDist_le_infDist_add_dist (x := x) (y := y) (s := H.domain)
  rw [dist_comm] at h
  linarith

theorem b1hint_not_mem_of_near (H : HorizontalReference n k L) {x : Spatial k}
    (hx : x ∉ H.domain) {y : Spatial k} (hy : dist y x < infDist x H.domain / 2) :
    y ∉ H.domain := by
  intro hyD
  have h1 := b1hint_infDist_near H hy
  rw [infDist_zero_of_mem hyD] at h1
  linarith [b1hint_infDist_pos H hx]

theorem b1hint_self_near (H : HorizontalReference n k L) {x : Spatial k} (hx : x ∉ H.domain) :
    dist x x < infDist x H.domain / 2 := by
  rw [dist_self]
  exact half_pos (b1hint_infDist_pos H hx)

/-- Near `x ∉ D` the interpolation is the finite quotient over the active indices. -/
theorem b1hint_interp_eq_local (H : HorizontalReference n k L) {x : Spatial k}
    (hx : x ∉ H.domain) {y : Spatial k} (hy : dist y x < infDist x H.domain / 2) :
    b1hint_interp H y =
      (∑ i ∈ b1hint_activeFinset H hx, b1hint_weight H i y * H.height (H.anchor i)) /
        ∑ i ∈ b1hint_activeFinset H hx, b1hint_weight H i y := by
  have hyD : y ∉ H.domain := b1hint_not_mem_of_near H hx hy
  have hsupp : ∀ i, b1hint_weight H i y ≠ 0 → i ∈ b1hint_activeFinset H hx := fun i hi =>
    (b1hint_mem_activeFinset H hx).2
      (by by_contra h; exact hi (b1hint_weight_eq_zero_of_not_mem H h hy))
  have h1 : Function.support (fun i => b1hint_weight H i y * H.height (H.anchor i)) ⊆
      (b1hint_activeFinset H hx : Set H.cubeIndex) := by
    intro i hi
    rw [Function.mem_support] at hi
    exact hsupp i (left_ne_zero_of_mul hi)
  have h2 : Function.support (fun i => b1hint_weight H i y) ⊆
      (b1hint_activeFinset H hx : Set H.cubeIndex) := by
    intro i hi
    rw [Function.mem_support] at hi
    exact hsupp i hi
  unfold b1hint_interp
  simp only [hyD, ↓reduceIte]
  rw [finsum_eq_sum_of_support_subset _ h1, finsum_eq_sum_of_support_subset _ h2]

/-- Near `x ∉ D` the active cutoffs sum to at least one. -/
theorem b1hint_one_le_sum (H : HorizontalReference n k L) {x : Spatial k} (hx : x ∉ H.domain)
    {y : Spatial k} (hy : dist y x < infDist x H.domain / 2) :
    1 ≤ ∑ i ∈ b1hint_activeFinset H hx, b1hint_weight H i y := by
  have hyD := b1hint_not_mem_of_near H hx hy
  have hcov : y ∈ ⋃ j, H.cube j := by
    rw [H.cubes_cover]
    exact hyD
  obtain ⟨j, hj⟩ := mem_iUnion.1 hcov
  have hjF : j ∈ b1hint_activeFinset H hx := by
    refine (b1hint_mem_activeFinset H hx).2 ⟨y, hy, ?_⟩
    have := b1hint_dist_le_scale H j hj (b1hint_center_mem H j)
    linarith [b1hint_scale_pos H j]
  calc (1 : ℝ) = b1hint_weight H j y := (b1hint_weight_eq_one H j hj).symm
    _ ≤ ∑ i ∈ b1hint_activeFinset H hx, b1hint_weight H i y :=
        Finset.single_le_sum (fun i _ => b1hint_weight_nonneg H i y) hjF

/-- Off `D` the plateau time is the anchor time of an active index (the face containing `x`). -/
theorem b1hint_height_eq (H : HorizontalReference n k L) {x : Spatial k} (hx : x ∉ H.domain) :
    ∃ j ∈ b1hint_activeFinset H hx, H.height x = H.height (H.anchor j) := by
  have hcov : x ∈ ⋃ j, H.face j := by
    rw [H.faces_cover]
    exact hx
  obtain ⟨j, hj⟩ := mem_iUnion.1 hcov
  refine ⟨j, (b1hint_mem_activeFinset H hx).2 ⟨x, b1hint_self_near H hx, ?_⟩,
    H.height_plateau j x hj⟩
  have := b1hint_dist_le_scale H j (H.face_subset_cube j hj) (b1hint_center_mem H j)
  linarith [b1hint_scale_pos H j]

/-- Active anchor times differ by at most `400 L² d(x)²`. -/
theorem b1hint_anchorTime_sub_le (H : HorizontalReference n k L) {x : Spatial k}
    (hx : x ∉ H.domain) {i j : H.cubeIndex} (hi : i ∈ b1hint_activeFinset H hx)
    (hj : j ∈ b1hint_activeFinset H hx) :
    |H.height (H.anchor i) - H.height (H.anchor j)| ≤ 400 * L ^ 2 * infDist x H.domain ^ 2 := by
  have hi' := (b1hint_activeSet_props H ((b1hint_mem_activeFinset H hx).1 hi)).2.1
  have hj' := (b1hint_activeSet_props H ((b1hint_mem_activeFinset H hx).1 hj)).2.1
  have hd : dist (H.anchor i) (H.anchor j) ≤ 20 * infDist x H.domain := by
    have := dist_triangle (H.anchor i) x (H.anchor j)
    rw [dist_comm (H.anchor i) x] at this
    linarith
  calc _ ≤ L ^ 2 * dist (H.anchor i) (H.anchor j) ^ 2 :=
        H.height_trace _ (H.anchor_mem i) _ (H.anchor_mem j)
    _ ≤ L ^ 2 * (20 * infDist x H.domain) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg hd 2) (sq_nonneg L)
    _ = 400 * L ^ 2 * infDist x H.domain ^ 2 := by ring

/-- The plateau error off `D`: `|T(x) - h(x)| ≤ 400 L² d(x)²`. -/
theorem b1hint_value_bound (H : HorizontalReference n k L) {x : Spatial k} (hx : x ∉ H.domain) :
    |H.height x - b1hint_interp H x| ≤ 400 * L ^ 2 * infDist x H.domain ^ 2 := by
  obtain ⟨j, hj, hTj⟩ := b1hint_height_eq H hx
  have hxx := b1hint_self_near H hx
  rw [b1hint_interp_eq_local H hx hxx, hTj, abs_sub_comm]
  exact b1hint_abs_wavg_sub_le _ _ _ _ _ (fun i _ => b1hint_weight_nonneg H i x)
    (lt_of_lt_of_le one_pos (b1hint_one_le_sum H hx hxx))
    (fun i hi => b1hint_anchorTime_sub_le H hx hi hj)

/-- Flatness at the domain: `|h(x) - h(a)| ≤ 121 L² |x - a|²` for `a ∈ D` and every `x`. -/
theorem b1hint_flat (H : HorizontalReference n k L) {a : Spatial k} (ha : a ∈ H.domain)
    (x : Spatial k) :
    |b1hint_interp H x - b1hint_interp H a| ≤ 121 * L ^ 2 * ‖x - a‖ ^ 2 := by
  rw [b1hint_interp_of_mem H ha, ← dist_eq_norm]
  by_cases hx : x ∈ H.domain
  · rw [b1hint_interp_of_mem H hx]
    have h0 : 0 ≤ L ^ 2 * dist x a ^ 2 := mul_nonneg (sq_nonneg L) (sq_nonneg _)
    calc _ ≤ L ^ 2 * dist x a ^ 2 := H.height_trace x hx a ha
      _ ≤ 121 * (L ^ 2 * dist x a ^ 2) := by linarith
      _ = 121 * L ^ 2 * dist x a ^ 2 := by ring
  · have hxx := b1hint_self_near H hx
    rw [b1hint_interp_eq_local H hx hxx]
    refine b1hint_abs_wavg_sub_le _ _ _ _ _ (fun i _ => b1hint_weight_nonneg H i x)
      (lt_of_lt_of_le one_pos (b1hint_one_le_sum H hx hxx)) fun i hi => ?_
    have h1 := (b1hint_activeSet_props H ((b1hint_mem_activeFinset H hx).1 hi)).2.1
    have h2 : infDist x H.domain ≤ dist x a := infDist_le_dist_of_mem ha
    have h3 : dist (H.anchor i) a ≤ 11 * dist x a := by
      have := dist_triangle (H.anchor i) x a
      rw [dist_comm (H.anchor i) x] at this
      linarith
    calc _ ≤ L ^ 2 * dist (H.anchor i) a ^ 2 := H.height_trace _ (H.anchor_mem i) a ha
      _ ≤ L ^ 2 * (11 * dist x a) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg h3 2) (sq_nonneg L)
      _ = 121 * L ^ 2 * dist x a ^ 2 := by ring

theorem b1hint_eventuallyEq_local (H : HorizontalReference n k L) {x : Spatial k}
    (hx : x ∉ H.domain) :
    b1hint_interp H =ᶠ[𝓝 x] fun y =>
      (∑ i ∈ b1hint_activeFinset H hx, b1hint_weight H i y * H.height (H.anchor i)) /
        ∑ i ∈ b1hint_activeFinset H hx, b1hint_weight H i y := by
  filter_upwards [ball_mem_nhds x (half_pos (b1hint_infDist_pos H hx))] with y hy
  exact b1hint_interp_eq_local H hx hy

/-- Off `D` the interpolation is `C¹` near the point. -/
theorem b1hint_contDiffAt_interp (H : HorizontalReference n k L) {x : Spatial k}
    (hx : x ∉ H.domain) : ContDiffAt ℝ 1 (b1hint_interp H) x := by
  have hN : ContDiff ℝ 1 fun y =>
      ∑ i ∈ b1hint_activeFinset H hx, b1hint_weight H i y * H.height (H.anchor i) :=
    ContDiff.sum fun i _ => (b1hint_contDiff_weight H i).mul contDiff_const
  have hP : ContDiff ℝ 1 fun y => ∑ i ∈ b1hint_activeFinset H hx, b1hint_weight H i y :=
    ContDiff.sum fun i _ => b1hint_contDiff_weight H i
  have hne : (∑ i ∈ b1hint_activeFinset H hx, b1hint_weight H i x) ≠ 0 :=
    (lt_of_lt_of_le one_pos (b1hint_one_le_sum H hx (b1hint_self_near H hx))).ne'
  exact (hN.contDiffAt.div hP.contDiffAt hne).congr_of_eventuallyEq
    (b1hint_eventuallyEq_local H hx)

/-- The gradient bound off `D`: `‖∇h(x)‖ ≤ 19200 N_k M_k L² d(x)`. -/
theorem b1hint_fderiv_bound (H : HorizontalReference n k L) {x : Spatial k}
    (hx : x ∉ H.domain) :
    ‖fderiv ℝ (b1hint_interp H) x‖ ≤
      19200 * b1hint_overlap k * b1hint_M k * L ^ 2 * infDist x H.domain := by
  have hd : 0 < infDist x H.domain := b1hint_infDist_pos H hx
  have hd0 : infDist x H.domain ≠ 0 := hd.ne'
  have hxx := b1hint_self_near H hx
  obtain ⟨j, hj, -⟩ := b1hint_height_eq H hx
  have hloc : b1hint_interp H =ᶠ[𝓝 x] fun y => H.height (H.anchor j) +
      (∑ i ∈ b1hint_activeFinset H hx,
          b1hint_weight H i y * (H.height (H.anchor i) - H.height (H.anchor j))) /
        ∑ i ∈ b1hint_activeFinset H hx, b1hint_weight H i y := by
    filter_upwards [ball_mem_nhds x (half_pos hd)] with y hy
    rw [b1hint_interp_eq_local H hx hy]
    have hne : (∑ i ∈ b1hint_activeFinset H hx, b1hint_weight H i y) ≠ 0 :=
      (lt_of_lt_of_le one_pos (b1hint_one_le_sum H hx hy)).ne'
    have hsum : ∑ i ∈ b1hint_activeFinset H hx,
          b1hint_weight H i y * (H.height (H.anchor i) - H.height (H.anchor j)) =
        (∑ i ∈ b1hint_activeFinset H hx, b1hint_weight H i y * H.height (H.anchor i)) -
          (∑ i ∈ b1hint_activeFinset H hx, b1hint_weight H i y) * H.height (H.anchor j) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, sub_div, mul_div_cancel_left₀ _ hne]
    ring
  have hBi : ∀ i ∈ b1hint_activeFinset H hx,
      ‖fderiv ℝ (b1hint_weight H i) x‖ ≤ 24 * b1hint_M k / infDist x H.domain := by
    intro i hi
    have hs := (b1hint_activeSet_props H ((b1hint_mem_activeFinset H hx).1 hi)).1
    calc _ ≤ b1hint_M k / b1hint_scale H i := b1hint_norm_fderiv_weight_le H i x
      _ ≤ b1hint_M k / (infDist x H.domain / 24) :=
          div_le_div_of_nonneg_left (b1hint_M_nonneg k) (by positivity) hs
      _ = 24 * b1hint_M k / infDist x H.domain := by rw [div_div_eq_mul_div, mul_comm]
  obtain ⟨g', hg', hnorm⟩ := b1hint_hasFDerivAt_wavg (b1hint_activeFinset H hx)
    (b1hint_weight H) (fun i => fderiv ℝ (b1hint_weight H i) x)
    (fun i => H.height (H.anchor i) - H.height (H.anchor j)) x
    (fun i _ => ((b1hint_contDiff_weight H i).differentiable one_ne_zero x).hasFDerivAt)
    (fun i _ => b1hint_weight_nonneg H i x) (b1hint_one_le_sum H hx hxx)
    (fun i hi => b1hint_anchorTime_sub_le H hx hi hj) hBi
  have hfd : HasFDerivAt (b1hint_interp H) g' x :=
    (hg'.const_add (H.height (H.anchor j))).congr_of_eventuallyEq hloc
  rw [hfd.fderiv]
  have hcard := b1hint_card_activeFinset_le H hx
  have hB0 : 0 ≤ 24 * b1hint_M k / infDist x H.domain :=
    div_nonneg (mul_nonneg (by norm_num) (b1hint_M_nonneg k)) hd.le
  have hΔ0 : 0 ≤ 400 * L ^ 2 * infDist x H.domain ^ 2 := by positivity
  calc ‖g'‖ ≤ 2 * ((b1hint_activeFinset H hx).card : ℝ) * (24 * b1hint_M k / infDist x H.domain) *
        (400 * L ^ 2 * infDist x H.domain ^ 2) := hnorm
    _ ≤ 2 * b1hint_overlap k * (24 * b1hint_M k / infDist x H.domain) *
        (400 * L ^ 2 * infDist x H.domain ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcard two_pos.le) hB0) hΔ0
    _ = 19200 * b1hint_overlap k * b1hint_M k * L ^ 2 *
          (infDist x H.domain ^ 2 / infDist x H.domain) := by ring
    _ = 19200 * b1hint_overlap k * b1hint_M k * L ^ 2 * infDist x H.domain := by
        rw [pow_two (infDist x H.domain), mul_div_assoc, div_self hd0, mul_one]

/-- The constant `C_k = 400 + 19200 N_k M_k`. -/
def b1hint_const (k : ℕ) : ℝ := 400 + 19200 * b1hint_overlap k * b1hint_M k

theorem b1hint_const_nonneg_aux (k : ℕ) : 0 ≤ 19200 * b1hint_overlap k * b1hint_M k :=
  mul_nonneg (mul_nonneg (by norm_num) (b1hint_overlap_nonneg k)) (b1hint_M_nonneg k)

theorem b1hint_const_pos (k : ℕ) : 0 < b1hint_const k := by
  unfold b1hint_const
  linarith [b1hint_const_nonneg_aux k]

/-- All four conclusions of the statement for the interpolation `b1hint_interp H`. -/
theorem b1hint_interp_spec (H : HorizontalReference n k L) :
    ContDiff ℝ 1 (b1hint_interp H) ∧ (∀ u ∈ H.domain, b1hint_interp H u = H.height u) ∧
      (∀ u, |H.height u - b1hint_interp H u| ≤
        b1hint_const k * L ^ 2 * Metric.infDist u H.domain ^ 2) ∧
      (∀ u, ‖fderiv ℝ (b1hint_interp H) u‖ ≤
        b1hint_const k * L ^ 2 * Metric.infDist u H.domain) := by
  have hX := b1hint_const_nonneg_aux k
  have hC := b1hint_const_pos k
  have hD : ∀ a ∈ H.domain, HasFDerivAt (b1hint_interp H) (0 : Spatial k →L[ℝ] ℝ) a :=
    fun a ha => b1hint_hasFDerivAt_zero_of_sq _ a _ (b1hint_flat H ha)
  have hgrad : ∀ u, ‖fderiv ℝ (b1hint_interp H) u‖ ≤
      b1hint_const k * L ^ 2 * infDist u H.domain := by
    intro u
    by_cases hu : u ∈ H.domain
    · rw [(hD u hu).fderiv, norm_zero, infDist_zero_of_mem hu, mul_zero]
    · refine (b1hint_fderiv_bound H hu).trans ?_
      have hLd : 0 ≤ L ^ 2 * infDist u H.domain := mul_nonneg (sq_nonneg L) infDist_nonneg
      unfold b1hint_const
      calc 19200 * b1hint_overlap k * b1hint_M k * L ^ 2 * infDist u H.domain
            = (19200 * b1hint_overlap k * b1hint_M k) * (L ^ 2 * infDist u H.domain) := by ring
        _ ≤ (400 + 19200 * b1hint_overlap k * b1hint_M k) * (L ^ 2 * infDist u H.domain) :=
            mul_le_mul_of_nonneg_right (by linarith) hLd
        _ = (400 + 19200 * b1hint_overlap k * b1hint_M k) * L ^ 2 * infDist u H.domain := by
            ring
  have hvalue : ∀ u, |H.height u - b1hint_interp H u| ≤
      b1hint_const k * L ^ 2 * infDist u H.domain ^ 2 := by
    intro u
    have hLd : 0 ≤ L ^ 2 * infDist u H.domain ^ 2 := mul_nonneg (sq_nonneg L) (sq_nonneg _)
    by_cases hu : u ∈ H.domain
    · rw [b1hint_interp_of_mem H hu, sub_self, abs_zero]
      calc (0 : ℝ) ≤ b1hint_const k * (L ^ 2 * infDist u H.domain ^ 2) := mul_nonneg hC.le hLd
        _ = b1hint_const k * L ^ 2 * infDist u H.domain ^ 2 := by ring
    · refine (b1hint_value_bound H hu).trans ?_
      unfold b1hint_const
      calc 400 * L ^ 2 * infDist u H.domain ^ 2 = 400 * (L ^ 2 * infDist u H.domain ^ 2) := by
            ring
        _ ≤ (400 + 19200 * b1hint_overlap k * b1hint_M k) * (L ^ 2 * infDist u H.domain ^ 2) :=
            mul_le_mul_of_nonneg_right (by linarith) hLd
        _ = (400 + 19200 * b1hint_overlap k * b1hint_M k) * L ^ 2 * infDist u H.domain ^ 2 := by
            ring
  have hdiff : Differentiable ℝ (b1hint_interp H) := fun u => by
    by_cases hu : u ∈ H.domain
    · exact (hD u hu).differentiableAt
    · exact (b1hint_contDiffAt_interp H hu).differentiableAt one_ne_zero
  have hcont : Continuous (fderiv ℝ (b1hint_interp H)) := by
    refine continuous_iff_continuousAt.2 fun u => ?_
    by_cases hu : u ∈ H.domain
    · refine continuousAt_of_locally_lipschitz one_pos (b1hint_const k * L ^ 2) fun y _ => ?_
      rw [(hD u hu).fderiv, dist_zero_right]
      calc _ ≤ b1hint_const k * L ^ 2 * infDist y H.domain := hgrad y
        _ ≤ b1hint_const k * L ^ 2 * dist y u :=
            mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem hu)
              (mul_nonneg hC.le (sq_nonneg L))
    · exact ((b1hint_contDiffAt_interp H hu).fderiv_right (m := 0)
        (zero_add (1 : WithTop ℕ∞)).le).continuousAt
  exact ⟨contDiff_one_iff_fderiv.2 ⟨hdiff, hcont⟩, fun u hu => b1hint_interp_of_mem H hu,
    hvalue, hgrad⟩

end Interpolation

/-- **`ba1_horizontal_interpolation`**.
The constant is `C_k = b1hint_const k = 400 + 19200 N_k M_k`, and the interpolation is
`b1hint_interp H`. -/
theorem ba1_horizontal_interpolation_proof :
    ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      ∃ h : Spatial k → ℝ, ContDiff ℝ 1 h ∧ (∀ u ∈ H.domain, h u = H.height u) ∧
        (∀ u, |H.height u - h u| ≤ C * L ^ 2 * Metric.infDist u H.domain ^ 2) ∧
        (∀ u, ‖fderiv ℝ h u‖ ≤ C * L ^ 2 * Metric.infDist u H.domain) := by
  intro k
  exact ⟨b1hint_const k, b1hint_const_pos k, fun n L _ H => ⟨b1hint_interp H, b1hint_interp_spec H⟩⟩

end ParabolicRectifiability.QuantitativeCharacterization
