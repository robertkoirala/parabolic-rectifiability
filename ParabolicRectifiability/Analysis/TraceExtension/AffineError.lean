import ParabolicRectifiability.Measure.ScaleEnergy

/-! # Spatial-affine fitting errors on a parabolic base

The base is `E × Time`, where `E` is a real inner-product space (in every use a
finite-dimensional one: `Spatial m`, or an intrinsic spatial subspace `W`) and
`Time` carries the snowflaked metric. Its balls `P(y,s)` are therefore products
of open spatial balls of radius `s` and open time intervals of half-length `s^2`.
Values lie in a real inner-product space (Euclidean `ℝ^d`, or a normal space).

Spatial affine maps are `u ↦ a + B u` with `B : E →L[ℝ] Y`. There is no
time-linear term and `‖B‖` is the operator norm. Put `k = dim E + 2`
(`baseDimension E`). Every squared error below carries the normalization
`s^(-k-2)`, is an extended nonnegative integral against the given measure and is
never divided by a ball mass. Nonpositive radii give zero. The infima are taken
over all admissible pairs `(a, B)`; no chosen or attained fit is part of the
definitions.

* `affineErrorSq μ f y s` is `κ_f(y,s)^2`: the unrestricted infimum.
* `constrainedAffineErrorSq ν g L y s` is `α_{g,ν,L}(y,s)^2`: the same integral
  against a node measure `ν`, restricted to `‖B‖ ≤ L`.
  `L = 0` leaves exactly the constant maps.
* `traceErrorSq μ K f p r` is `γ_K(p,r)^2`: the unrestricted error for `μ`
  restricted to the trace set `K`.
* `HasAffineCarlesonBound μ f B` is the affine Carleson bound
  `∫_{P(z,R)} ∫_0^R κ_f(y,s)^2 ds/s dμ(y) ≤ B R^k` for every `z` and `R > 0`
  (the hypothesis of affine localization).

Only the values on a set carrying the measure enter these integrals, so a
partially defined trace is represented by any total function agreeing with it
on the trace set. Scale integrals use `scaleMeasure` (`dr/r`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-- The parabolic homogeneous dimension `k = dim E + 2` of the base `E × Time`. -/
def baseDimension (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : ℕ :=
  Module.finrank ℝ E + 2

section Definitions

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Unnormalized squared distance from the spatial affine map `u ↦ a + B u`,
integrated against `μ` over the open ball `P(y,s)`. -/
def affineFitIntegral (μ : Measure (E × Time)) (f : E × Time → Y) (a : Y)
    (B : E →L[ℝ] Y) (y : E × Time) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ q in Metric.ball y s, ‖f q - (a + B q.1)‖ₑ ^ 2 ∂μ

/-- Unrestricted squared affine error `κ_f(y,s)^2`, with normalization `s^(-k-2)`
and zero at nonpositive radii. -/
def affineErrorSq (μ : Measure (E × Time)) (f : E × Time → Y) (y : E × Time)
    (s : ℝ) : ℝ≥0∞ :=
  if 0 < s then
    (ENNReal.ofReal s)⁻¹ ^ (baseDimension E + 2) *
      ⨅ (a : Y) (B : E →L[ℝ] Y), affineFitIntegral μ f a B y s
  else 0

/-- Constrained squared affine error `α_{g,ν,L}(y,s)^2`: the slope ranges over
operator norm at most `L`. The same normalization and radius guard. -/
def constrainedAffineErrorSq (ν : Measure (E × Time)) (g : E × Time → Y) (L : ℝ≥0)
    (y : E × Time) (s : ℝ) : ℝ≥0∞ :=
  if 0 < s then
    (ENNReal.ofReal s)⁻¹ ^ (baseDimension E + 2) *
      ⨅ (a : Y) (B : E →L[ℝ] Y) (_ : ‖B‖ ≤ (L : ℝ)), affineFitIntegral ν g a B y s
  else 0

/-- Squared trace error `γ_K(p,r)^2`: the unrestricted error for `μ` restricted
to the trace set `K`. With `μ` the base volume this is the integral over
`K ∩ P(p,r)` against ordinary volume. -/
def traceErrorSq (μ : Measure (E × Time)) (K : Set (E × Time)) (f : E × Time → Y)
    (p : E × Time) (r : ℝ) : ℝ≥0∞ :=
  affineErrorSq (μ.restrict K) f p r

/-- The Carleson integral `∫_{P(z,R)} ∫_0^R κ_f(y,s)^2 ds/s dμ(y)`. -/
def affineCarlesonIntegral (μ : Measure (E × Time)) (f : E × Time → Y)
    (z : E × Time) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R, affineErrorSq μ f y s ∂scaleMeasure ∂μ

/-- The affine Carleson bound with constant `B ≥ 0`, at every center and every
positive radius, normalized by `R^k`. -/
def HasAffineCarlesonBound (μ : Measure (E × Time)) (f : E × Time → Y) (B : ℝ) : Prop :=
  0 ≤ B ∧ ∀ (z : E × Time) (R : ℝ), 0 < R →
    affineCarlesonIntegral μ f z R ≤ ENNReal.ofReal (B * R ^ baseDimension E)

end Definitions

section BasicLaws

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

@[simp] theorem affineErrorSq_of_nonpos (μ : Measure (E × Time)) (f : E × Time → Y)
    (y : E × Time) {s : ℝ} (hs : s ≤ 0) : affineErrorSq μ f y s = 0 := by
  simp [affineErrorSq, not_lt.mpr hs]

theorem affineErrorSq_of_pos (μ : Measure (E × Time)) (f : E × Time → Y)
    (y : E × Time) {s : ℝ} (hs : 0 < s) :
    affineErrorSq μ f y s = (ENNReal.ofReal s)⁻¹ ^ (baseDimension E + 2) *
      ⨅ (a : Y) (B : E →L[ℝ] Y), affineFitIntegral μ f a B y s := by
  simp only [affineErrorSq, hs, ↓reduceIte]

@[simp] theorem constrainedAffineErrorSq_of_nonpos (ν : Measure (E × Time))
    (g : E × Time → Y) (L : ℝ≥0) (y : E × Time) {s : ℝ} (hs : s ≤ 0) :
    constrainedAffineErrorSq ν g L y s = 0 := by
  simp [constrainedAffineErrorSq, not_lt.mpr hs]

/-- Fixed-affine comparison: any single competitor bounds the error. -/
theorem affineErrorSq_le_fitIntegral (μ : Measure (E × Time)) (f : E × Time → Y)
    (y : E × Time) {s : ℝ} (hs : 0 < s) (a : Y) (B : E →L[ℝ] Y) :
    affineErrorSq μ f y s ≤
      (ENNReal.ofReal s)⁻¹ ^ (baseDimension E + 2) * affineFitIntegral μ f a B y s := by
  rw [affineErrorSq_of_pos μ f y hs]
  gcongr _ * ?_
  exact iInf_le_of_le a (iInf_le _ B)

/-- Fixed-affine comparison for an admissible constrained competitor. -/
theorem constrainedAffineErrorSq_le_fitIntegral (ν : Measure (E × Time))
    (g : E × Time → Y) (L : ℝ≥0) (y : E × Time) {s : ℝ} (hs : 0 < s) (a : Y)
    (B : E →L[ℝ] Y) (hB : ‖B‖ ≤ (L : ℝ)) :
    constrainedAffineErrorSq ν g L y s ≤
      (ENNReal.ofReal s)⁻¹ ^ (baseDimension E + 2) * affineFitIntegral ν g a B y s := by
  simp only [constrainedAffineErrorSq, hs, ↓reduceIte]
  gcongr _ * ?_
  exact iInf_le_of_le a (iInf_le_of_le B (iInf_le _ hB))

/-- The unrestricted error is at most the constrained one for the same measure. -/
theorem affineErrorSq_le_constrained (ν : Measure (E × Time)) (g : E × Time → Y)
    (L : ℝ≥0) (y : E × Time) (s : ℝ) :
    affineErrorSq ν g y s ≤ constrainedAffineErrorSq ν g L y s := by
  unfold affineErrorSq constrainedAffineErrorSq
  split_ifs
  · gcongr _ * ?_
    exact iInf_mono fun _ => iInf_mono fun _ => le_iInf fun _ => le_rfl
  · exact le_rfl

/-- A larger measure has a larger unrestricted error. -/
theorem affineErrorSq_mono_measure {μ μ' : Measure (E × Time)} (h : μ ≤ μ')
    (f : E × Time → Y) (y : E × Time) (s : ℝ) :
    affineErrorSq μ f y s ≤ affineErrorSq μ' f y s := by
  unfold affineErrorSq affineFitIntegral
  split_ifs
  · gcongr _ * ?_
    exact iInf_mono fun _ => iInf_mono fun _ =>
      lintegral_mono' (Measure.restrict_mono subset_rfl h) le_rfl
  · exact le_rfl

/-- Restricting to a trace set can only decrease the error. -/
theorem traceErrorSq_le_affineErrorSq (μ : Measure (E × Time)) (K : Set (E × Time))
    (f : E × Time → Y) (p : E × Time) (r : ℝ) :
    traceErrorSq μ K f p r ≤ affineErrorSq μ f p r :=
  affineErrorSq_mono_measure Measure.restrict_le_self f p r

/-- A constant function has zero unrestricted error. -/
theorem affineErrorSq_const (μ : Measure (E × Time)) (c : Y) (y : E × Time) (s : ℝ) :
    affineErrorSq μ (fun _ => c) y s = 0 := by
  rcases le_or_gt s 0 with hs | hs
  · exact affineErrorSq_of_nonpos μ _ y hs
  · refine le_antisymm ?_ zero_le
    calc
      _ ≤ (ENNReal.ofReal s)⁻¹ ^ (baseDimension E + 2) *
          affineFitIntegral μ (fun _ => c) c 0 y s :=
        affineErrorSq_le_fitIntegral μ _ y hs c 0
      _ = 0 := by simp [affineFitIntegral]

/-- A constant function has zero constrained error for every `L`, including `L = 0`. -/
theorem constrainedAffineErrorSq_const (ν : Measure (E × Time)) (c : Y) (L : ℝ≥0)
    (y : E × Time) (s : ℝ) :
    constrainedAffineErrorSq ν (fun _ => c) L y s = 0 := by
  rcases le_or_gt s 0 with hs | hs
  · exact constrainedAffineErrorSq_of_nonpos ν _ L y hs
  · refine le_antisymm ?_ zero_le
    calc
      _ ≤ (ENNReal.ofReal s)⁻¹ ^ (baseDimension E + 2) *
          affineFitIntegral ν (fun _ => c) c 0 y s :=
        constrainedAffineErrorSq_le_fitIntegral ν _ L y hs c 0 (by simp)
      _ = 0 := by simp [affineFitIntegral]

/-- The zero measure has zero unrestricted error. -/
theorem affineErrorSq_zero_measure (f : E × Time → Y) (y : E × Time) (s : ℝ) :
    affineErrorSq (0 : Measure (E × Time)) f y s = 0 := by
  rcases le_or_gt s 0 with hs | hs
  · exact affineErrorSq_of_nonpos _ f y hs
  · refine le_antisymm ?_ zero_le
    calc
      _ ≤ (ENNReal.ofReal s)⁻¹ ^ (baseDimension E + 2) *
          affineFitIntegral (0 : Measure (E × Time)) f 0 0 y s :=
        affineErrorSq_le_fitIntegral _ f y hs 0 0
      _ = 0 := by simp [affineFitIntegral]

/-- The empty trace set has zero trace error. -/
@[simp] theorem traceErrorSq_empty (μ : Measure (E × Time)) (f : E × Time → Y)
    (p : E × Time) (r : ℝ) : traceErrorSq μ ∅ f p r = 0 := by
  rw [traceErrorSq, Measure.restrict_empty]
  exact affineErrorSq_zero_measure f p r

/-- A constant function satisfies the affine Carleson bound with constant zero. -/
theorem hasAffineCarlesonBound_const (μ : Measure (E × Time)) (c : Y) :
    HasAffineCarlesonBound μ (fun _ => c) 0 := by
  refine ⟨le_rfl, fun z R _ => ?_⟩
  simp [affineCarlesonIntegral, affineErrorSq_const]

end BasicLaws

end ParabolicRectifiability
