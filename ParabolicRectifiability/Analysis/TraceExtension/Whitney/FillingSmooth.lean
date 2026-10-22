import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Filling

/-! # Smoothness of the Whitney filling and cancellation identities

Let `P` be a smooth Whitney partition and `F` the filling
of `g`. Around a point `q ∉ F₀` there is an open set `U ⊆ F₀ᶜ` and a finite index set
`S` such that every weight outside `S` vanishes on `U` (local finiteness). On `U`

* `F = Σ_{i∈S} φ_i g(p_i)` is a finite sum of `C²` functions, so the filling is `C²` in
  ordinary coordinates off the closed set `F₀`;
* `Σ_{i∈S} φ_i ≡ 1`, hence the first spatial derivatives and the time derivatives of
  the weights sum to zero (*cancellation*), and every first derivative of `F` can be
  written with the differences `g(p_i) - c` for an arbitrary vector `c`.

A nonnegative weight vanishing at a point has a local minimum there, so its first
spatial and time derivatives vanish (Fermat). No such claim is made for second
derivatives: it is false in general, and the second-order bound
in `WhitneyDerivBounds` is obtained from Lipschitz control of the first derivative
instead.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

section Slices

variable {m : ℕ}

theorem continuous_point_left (t : ℝ) : Continuous fun w : Spatial m => point w t := by
  have h := continuous_point.comp
    (continuous_id.prodMk (continuous_const : Continuous fun _ : Spatial m => t))
  exact h

theorem continuous_point_right (u : Spatial m) : Continuous fun s : ℝ => point u s := by
  have h := continuous_point.comp
    ((continuous_const : Continuous fun _ : ℝ => u).prodMk continuous_id)
  exact h

theorem dist_point_same_time (u x : Spatial m) (t : ℝ) :
    dist (point u t) (point x t) = ‖u - x‖ := by
  rw [dist_point, sub_self, abs_zero, Real.sqrt_zero]
  exact max_eq_left (norm_nonneg _)

/-- The spatial slices of a function with parabolic derivative bounds are `C²`. -/
theorem HasParabolicDerivBounds.contDiff_spaceSlice {φ : Space m → ℝ} {K r : ℝ}
    (h : HasParabolicDerivBounds φ K r) (t : ℝ) :
    ContDiff ℝ 2 fun v : Spatial m => φ (point v t) := by
  have h' := h.contDiff.comp (contDiff_id.prodMk (contDiff_const (c := t)))
  exact h'

/-- The time slices of a function with parabolic derivative bounds are `C²`. -/
theorem HasParabolicDerivBounds.contDiff_timeSlice {φ : Space m → ℝ} {K r : ℝ}
    (h : HasParabolicDerivBounds φ K r) (u : Spatial m) :
    ContDiff ℝ 2 fun s : ℝ => φ (point u s) := by
  have h' := h.contDiff.comp ((contDiff_const (c := u)).prodMk contDiff_id)
  exact h'

end Slices

section LocalFinite

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a H : ℝ} {W : WhitneyData m ι F₀ D a}

/-- Local finite representation: around a point off the closed set `F₀` there is an open
set `U ⊆ F₀ᶜ` and a finite index set outside of which all weights vanish on `U`. -/
theorem WhitneyWeights.exists_open_finset (φ : WhitneyWeights W H) (hF₀ : IsClosed F₀)
    {q : Space m} (hq : q ∉ F₀) :
    ∃ U : Set (Space m), IsOpen U ∧ q ∈ U ∧ U ⊆ F₀ᶜ ∧
      ∃ S : Finset ι, ∀ x ∈ U, ∀ i ∉ S, φ.weight i x = 0 := by
  obtain ⟨U₀, hU₀, hfin⟩ := φ.locallyFinite q hq
  refine ⟨interior U₀ ∩ F₀ᶜ, isOpen_interior.inter hF₀.isOpen_compl,
    ⟨mem_interior_iff_mem_nhds.mpr hU₀, hq⟩, inter_subset_right, hfin.toFinset,
    fun x hx i hi => ?_⟩
  by_contra h
  exact hi (hfin.mem_toFinset.mpr ⟨x, interior_subset hx.1, h⟩)

/-- A weight vanishing at a point has vanishing spatial derivative there (it is a local
minimum of a nonnegative function). -/
theorem WhitneyWeights.fderiv_spaceSlice_eq_zero (φ : WhitneyWeights W H) {i : ι}
    {v : Spatial m} {t : ℝ} (hz : φ.weight i (point v t) = 0) :
    fderiv ℝ (fun w => φ.weight i (point w t)) v = 0 :=
  IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun w => by
    show φ.weight i (point v t) ≤ φ.weight i (point w t)
    rw [hz]
    exact φ.nonneg i _)

/-- A weight vanishing at a point has vanishing time derivative there. -/
theorem WhitneyWeights.deriv_timeSlice_eq_zero (φ : WhitneyWeights W H) {i : ι}
    {u : Spatial m} {t : ℝ} (hz : φ.weight i (point u t) = 0) :
    deriv (fun s => φ.weight i (point u s)) t = 0 :=
  IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall fun s => by
    show φ.weight i (point u t) ≤ φ.weight i (point u s)
    rw [hz]
    exact φ.nonneg i _)

end LocalFinite

section Smooth

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a H b K : ℝ} {N : ℕ}
  {W : WhitneyData m ι F₀ D a} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (P : WhitneyPartition W H b K N) (g : Space m → Y) {U : Set (Space m)} {S : Finset ι}

theorem WhitneyPartition.filling_eq_sum_on (hUF : U ⊆ F₀ᶜ)
    (hS : ∀ x ∈ U, ∀ i ∉ S, P.weight i x = 0) {x : Space m} (hx : x ∈ U) :
    whitneyFilling P.toWhitneyWeights g x = ∑ i ∈ S, P.weight i x • g (W.center i) :=
  whitneyFilling_eq_sum P.toWhitneyWeights g (hUF hx) (hS x hx)

theorem WhitneyPartition.sum_weight_eq_one_on (hUF : U ⊆ F₀ᶜ)
    (hS : ∀ x ∈ U, ∀ i ∉ S, P.weight i x = 0) {x : Space m} (hx : x ∈ U) :
    ∑ i ∈ S, P.weight i x = 1 :=
  P.sum_weight_eq_one (hUF hx) (hS x hx)

/-- The spatial slice of the filling near a point of `U`, as a finite sum. -/
theorem WhitneyPartition.spaceSlice_filling_eventuallyEq (hU : IsOpen U) (hUF : U ⊆ F₀ᶜ)
    (hS : ∀ x ∈ U, ∀ i ∉ S, P.weight i x = 0) {v : Spatial m} {t : ℝ} (hv : point v t ∈ U) :
    (fun w => whitneyFilling P.toWhitneyWeights g (point w t)) =ᶠ[𝓝 v]
      fun w => ∑ i ∈ S, P.weight i (point w t) • g (W.center i) := by
  filter_upwards [(hU.preimage (continuous_point_left t)).mem_nhds hv] with w hw
  exact P.filling_eq_sum_on g hUF hS hw

/-- The time slice of the filling near a point of `U`, as a finite sum. -/
theorem WhitneyPartition.timeSlice_filling_eventuallyEq (hU : IsOpen U) (hUF : U ⊆ F₀ᶜ)
    (hS : ∀ x ∈ U, ∀ i ∉ S, P.weight i x = 0) {u : Spatial m} {t : ℝ} (hu : point u t ∈ U) :
    (fun s => whitneyFilling P.toWhitneyWeights g (point u s)) =ᶠ[𝓝 t]
      fun s => ∑ i ∈ S, P.weight i (point u s) • g (W.center i) := by
  filter_upwards [(hU.preimage (continuous_point_right u)).mem_nhds hu] with s hs
  exact P.filling_eq_sum_on g hUF hS hs

/-- **Smoothness**: off `F₀` the filling is `C²` in ordinary coordinates. -/
theorem WhitneyPartition.contDiffOn_whitneyFilling (hF₀ : IsClosed F₀) :
    ContDiffOn ℝ 2 (fun y : Coordinates m => whitneyFilling P.toWhitneyWeights g (point y.1 y.2))
      {y | point y.1 y.2 ∉ F₀} := by
  intro y hy
  have hy' : point y.1 y.2 ∉ F₀ := hy
  obtain ⟨U, hU, hyU, hUF, S, hS⟩ := P.toWhitneyWeights.exists_open_finset hF₀ hy'
  have hev : (fun z : Coordinates m => whitneyFilling P.toWhitneyWeights g (point z.1 z.2)) =ᶠ[𝓝 y]
      fun z => ∑ i ∈ S, P.weight i (point z.1 z.2) • g (W.center i) := by
    filter_upwards [(hU.preimage continuous_point).mem_nhds hyU] with z hz
    exact P.filling_eq_sum_on g hUF hS hz
  have hsmooth : ContDiff ℝ 2 fun z : Coordinates m =>
      ∑ i ∈ S, P.weight i (point z.1 z.2) • g (W.center i) :=
    ContDiff.sum fun i _ => (P.derivBounds i).contDiff.smul contDiff_const
  exact (hsmooth.contDiffAt.congr_of_eventuallyEq hev).contDiffWithinAt

/-- The spatial slice of the filling is `C²` near every point of `U`. -/
theorem WhitneyPartition.contDiffAt_spaceSlice_filling (hU : IsOpen U) (hUF : U ⊆ F₀ᶜ)
    (hS : ∀ x ∈ U, ∀ i ∉ S, P.weight i x = 0) {v : Spatial m} {t : ℝ} (hv : point v t ∈ U) :
    ContDiffAt ℝ 2 (fun w => whitneyFilling P.toWhitneyWeights g (point w t)) v := by
  have hsmooth : ContDiff ℝ 2 fun w : Spatial m =>
      ∑ i ∈ S, P.weight i (point w t) • g (W.center i) :=
    ContDiff.sum fun i _ => ((P.derivBounds i).contDiff_spaceSlice t).smul contDiff_const
  exact hsmooth.contDiffAt.congr_of_eventuallyEq
    (P.spaceSlice_filling_eventuallyEq g hU hUF hS hv)

/-- The spatial derivative of the filling is differentiable near every point of `U`. -/
theorem WhitneyPartition.differentiableAt_fderiv_spaceSlice_filling (hU : IsOpen U)
    (hUF : U ⊆ F₀ᶜ) (hS : ∀ x ∈ U, ∀ i ∉ S, P.weight i x = 0) {v : Spatial m} {t : ℝ}
    (hv : point v t ∈ U) :
    DifferentiableAt ℝ
      (fun w => fderiv ℝ (fun w' => whitneyFilling P.toWhitneyWeights g (point w' t)) w) v :=
  ((P.contDiffAt_spaceSlice_filling g hU hUF hS hv).fderiv_right
    one_add_one_eq_two.le).differentiableAt one_ne_zero

/-- Spatial derivative of the filling as a finite sum. -/
theorem WhitneyPartition.hasFDerivAt_spaceSlice_filling (hU : IsOpen U) (hUF : U ⊆ F₀ᶜ)
    (hS : ∀ x ∈ U, ∀ i ∉ S, P.weight i x = 0) {v : Spatial m} {t : ℝ} (hv : point v t ∈ U) :
    HasFDerivAt (fun w => whitneyFilling P.toWhitneyWeights g (point w t))
      (∑ i ∈ S, (fderiv ℝ (fun w => P.weight i (point w t)) v).smulRight (g (W.center i))) v := by
  refine HasFDerivAt.congr_of_eventuallyEq ?_ (P.spaceSlice_filling_eventuallyEq g hU hUF hS hv)
  exact HasFDerivAt.fun_sum fun i _ =>
    ((((P.derivBounds i).contDiff_spaceSlice t).differentiable two_ne_zero) v).hasFDerivAt.smul_const
      _

/-- Time derivative of the filling as a finite sum. -/
theorem WhitneyPartition.hasDerivAt_timeSlice_filling (hU : IsOpen U) (hUF : U ⊆ F₀ᶜ)
    (hS : ∀ x ∈ U, ∀ i ∉ S, P.weight i x = 0) {u : Spatial m} {t : ℝ} (hu : point u t ∈ U) :
    HasDerivAt (fun s => whitneyFilling P.toWhitneyWeights g (point u s))
      (∑ i ∈ S, deriv (fun s => P.weight i (point u s)) t • g (W.center i)) t := by
  refine HasDerivAt.congr_of_eventuallyEq ?_ (P.timeSlice_filling_eventuallyEq g hU hUF hS hu)
  exact HasDerivAt.fun_sum fun i _ =>
    ((((P.derivBounds i).contDiff_timeSlice u).differentiable two_ne_zero) t).hasDerivAt.smul_const
      _

/-- **Cancellation** of the first spatial derivatives of the weights on `U`. -/
theorem WhitneyPartition.sum_fderiv_spaceSlice_weight_eq_zero (hU : IsOpen U)
    (hUF : U ⊆ F₀ᶜ) (hS : ∀ x ∈ U, ∀ i ∉ S, P.weight i x = 0) {v : Spatial m} {t : ℝ}
    (hv : point v t ∈ U) :
    ∑ i ∈ S, fderiv ℝ (fun w => P.weight i (point w t)) v = 0 := by
  have hev : (fun w => ∑ i ∈ S, P.weight i (point w t)) =ᶠ[𝓝 v] fun _ => (1 : ℝ) := by
    filter_upwards [(hU.preimage (continuous_point_left t)).mem_nhds hv] with w hw
    exact P.sum_weight_eq_one_on hUF hS hw
  have h1 : HasFDerivAt (fun w => ∑ i ∈ S, P.weight i (point w t))
      (∑ i ∈ S, fderiv ℝ (fun w => P.weight i (point w t)) v) v :=
    HasFDerivAt.fun_sum fun i _ =>
      (((P.derivBounds i).contDiff_spaceSlice t).differentiable two_ne_zero v).hasFDerivAt
  have h2 : HasFDerivAt (fun w => ∑ i ∈ S, P.weight i (point w t))
      (0 : Spatial m →L[ℝ] ℝ) v :=
    (hasFDerivAt_const (1 : ℝ) v).congr_of_eventuallyEq hev
  exact h1.unique h2

/-- **Cancellation** of the time derivatives of the weights on `U`. -/
theorem WhitneyPartition.sum_deriv_timeSlice_weight_eq_zero (hU : IsOpen U)
    (hUF : U ⊆ F₀ᶜ) (hS : ∀ x ∈ U, ∀ i ∉ S, P.weight i x = 0) {u : Spatial m} {t : ℝ}
    (hu : point u t ∈ U) :
    ∑ i ∈ S, deriv (fun s => P.weight i (point u s)) t = 0 := by
  have hev : (fun s => ∑ i ∈ S, P.weight i (point u s)) =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [(hU.preimage (continuous_point_right u)).mem_nhds hu] with s hs
    exact P.sum_weight_eq_one_on hUF hS hs
  have h1 : HasDerivAt (fun s => ∑ i ∈ S, P.weight i (point u s))
      (∑ i ∈ S, deriv (fun s => P.weight i (point u s)) t) t :=
    HasDerivAt.fun_sum fun i _ =>
      (((P.derivBounds i).contDiff_timeSlice u).differentiable two_ne_zero t).hasDerivAt
  have h2 : HasDerivAt (fun s => ∑ i ∈ S, P.weight i (point u s)) 0 t :=
    (hasDerivAt_const (x := t) (c := (1 : ℝ))).congr_of_eventuallyEq hev
  exact h1.unique h2

/-- The spatial derivative of the filling applied to a vector, with the node values
recentred at an arbitrary `c` (cancellation). -/
theorem WhitneyPartition.fderiv_spaceSlice_filling_apply (hU : IsOpen U) (hUF : U ⊆ F₀ᶜ)
    (hS : ∀ x ∈ U, ∀ i ∉ S, P.weight i x = 0) {v : Spatial m} {t : ℝ} (hv : point v t ∈ U)
    (c : Y) (h : Spatial m) :
    fderiv ℝ (fun w => whitneyFilling P.toWhitneyWeights g (point w t)) v h =
      ∑ i ∈ S, fderiv ℝ (fun w => P.weight i (point w t)) v h • (g (W.center i) - c) := by
  rw [(P.hasFDerivAt_spaceSlice_filling g hU hUF hS hv).fderiv]
  have h0 : ∑ i ∈ S, fderiv ℝ (fun w => P.weight i (point w t)) v h = 0 := by
    have := congrArg (fun A : Spatial m →L[ℝ] ℝ => A h)
      (P.sum_fderiv_spaceSlice_weight_eq_zero hU hUF hS hv)
    simpa only [sum_apply, zero_apply] using this
  calc
    (∑ i ∈ S, (fderiv ℝ (fun w => P.weight i (point w t)) v).smulRight (g (W.center i))) h =
        ∑ i ∈ S, fderiv ℝ (fun w => P.weight i (point w t)) v h • g (W.center i) := by
      simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
    _ = ∑ i ∈ S, fderiv ℝ (fun w => P.weight i (point w t)) v h • g (W.center i) -
          (∑ i ∈ S, fderiv ℝ (fun w => P.weight i (point w t)) v h) • c := by
      rw [h0, zero_smul, sub_zero]
    _ = _ := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      simp only [smul_sub]

/-- The time derivative of the filling, with the node values recentred at `c`. -/
theorem WhitneyPartition.deriv_timeSlice_filling (hU : IsOpen U) (hUF : U ⊆ F₀ᶜ)
    (hS : ∀ x ∈ U, ∀ i ∉ S, P.weight i x = 0) {u : Spatial m} {t : ℝ} (hu : point u t ∈ U)
    (c : Y) :
    deriv (fun s => whitneyFilling P.toWhitneyWeights g (point u s)) t =
      ∑ i ∈ S, deriv (fun s => P.weight i (point u s)) t • (g (W.center i) - c) := by
  rw [(P.hasDerivAt_timeSlice_filling g hU hUF hS hu).deriv]
  have h0 := P.sum_deriv_timeSlice_weight_eq_zero hU hUF hS hu
  calc
    ∑ i ∈ S, deriv (fun s => P.weight i (point u s)) t • g (W.center i) =
        ∑ i ∈ S, deriv (fun s => P.weight i (point u s)) t • g (W.center i) -
          (∑ i ∈ S, deriv (fun s => P.weight i (point u s)) t) • c := by
      rw [h0, zero_smul, sub_zero]
    _ = _ := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      simp only [smul_sub]

end Smooth

end ParabolicRectifiability
