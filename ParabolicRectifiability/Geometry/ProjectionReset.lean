import ParabolicRectifiability.Geometry.CoherentProjection
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Reset by a full-weight projection

This file proves the reset lemma for the weighted projection `sigma` of
`CoherentProjection`. The proof has four steps:

1. local full weight, `∑ θ_a = 1` on a spatial neighbourhood of `x` at the fixed
   time `t`, gives `∑ θ_a(x,t) = 1` and `∑ D_x θ_a(x,t) = 0`
   (`local_full_weight`; a space-time neighbourhood also suffices,
   `eventually_spatial_of_spacetime`);
2. subtracting the reference affine projection gives the two reset identities
   (`sigma_sub_projection`, `fderiv_sub_projection`) and hence the affine
   distance and operator estimates (`reset_estimates`);
3. a linear bridge: an operator within `q ≤ 1/10` of `P_U`, on an incoming
   subspace `T` with projection gap at most `1/10`, is injective on `T`; the gap
   forces `dim T = dim U`, so the projected image map `T → U` is bijective and
   the actual image is the graph over `U` of a normal map of norm at most `2q`
   (`linear_graph_bridge`);
4. the orthogonal projection onto such a graph differs from `P_U` by at most
   twice the graph norm (`graph_projection_bound`).

The theorem `reset` combines these steps for the actual spatial derivative
of `sigma`, with constant `8 * (1 + B * C₀)`. All spatial dimensions and rank zero
are allowed. Pointwise full weight is not enough: the weights must sum to one on a
neighbourhood.
-/

noncomputable section

namespace ParabolicRectifiability.ProjectionReset

open Finset ContinuousLinearMap
open CoherentProjection
open scoped Topology

variable {ι : Type*} {n m : ℕ}

/-! ### Step 1: local full weight -/

/-- Local full weight: the local equality is differentiated, not merely its point value. -/
theorem local_full_weight (s : Finset ι) (θ : ι → Spatial n → ℝ → ℝ)
    (x : Spatial n) (t : ℝ)
    (hθ : ∀ a ∈ s, DifferentiableAt ℝ (fun y => θ a y t) x)
    (hfull : ∀ᶠ y in 𝓝 x, ∑ a ∈ s, θ a y t = 1) :
    (∑ a ∈ s, θ a x t) = 1 ∧ (∑ a ∈ s, dx θ a x t) = 0 := by
  refine ⟨hfull.self_of_nhds, ?_⟩
  have hd := HasFDerivAt.fun_sum (fun a ha => (hθ a ha).hasFDerivAt)
  have heq : (fun y => ∑ a ∈ s, θ a y t) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := hfull
  have hc : HasFDerivAt (𝕜 := ℝ) (fun y => ∑ a ∈ s, θ a y t)
      (0 : Spatial n →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).congr_of_eventuallyEq heq
  exact hd.unique hc

/-- Full weight on a space-time neighbourhood gives full weight on a spatial one. -/
theorem eventually_spatial_of_spacetime (s : Finset ι) (θ : ι → Spatial n → ℝ → ℝ)
    (x : Spatial n) (t : ℝ)
    (hfull : ∀ᶠ p in 𝓝 (x, t), ∑ a ∈ s, θ a p.1 p.2 = 1) :
    ∀ᶠ y in 𝓝 x, ∑ a ∈ s, θ a y t = 1 := by
  have hc : Filter.Tendsto (fun y : Spatial n => (y, t)) (𝓝 x) (𝓝 (x, t)) :=
    (continuous_id.prodMk continuous_const).tendsto x
  exact hc.eventually hfull

/-! ### Step 2: the reset identities and estimates -/

/-- The first reset identity is an identity of actual affine projections. -/
theorem sigma_sub_projection (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t : ℝ)
    (K : AffineSpatialPlane n m) (hs : (∑ a ∈ s, θ a x t) = 1) :
    sigma s L θ x t - K.projection x =
      ∑ a ∈ s, θ a x t • ((L a).projection x - K.projection x) := by
  simp only [sigma, smul_sub, sum_sub_distrib, ← sum_smul, hs, one_smul]
  abel

/-- The second reset identity, for operators, uses the actual fderiv and the vanishing weight derivative sum. -/
theorem fderiv_sub_projection (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t : ℝ)
    (K : AffineSpatialPlane n m)
    (hθ : ∀ a ∈ s, DifferentiableAt ℝ (fun y => θ a y t) x)
    (hs : (∑ a ∈ s, θ a x t) = 1) (hds : (∑ a ∈ s, dx θ a x t) = 0) :
    fderiv ℝ (fun y => sigma s L θ y t) x - K.linearProjection =
      (∑ a ∈ s, θ a x t • ((L a).linearProjection - K.linearProjection)) +
      ∑ a ∈ s, (dx θ a x t).smulRight ((L a).projection x - K.projection x) := by
  rw [fderiv_sigma s L θ x t hθ]
  apply ContinuousLinearMap.ext
  intro v
  have hdv : (∑ a ∈ s, dx θ a x t v) = 0 := by
    simpa using congrArg (fun A : Spatial n →L[ℝ] ℝ => A v) hds
  simp only [spatialDerivative, sub_apply, add_apply, id_apply, _root_.sum_apply,
    smul_apply, smulRight_apply, smul_sub, sum_add_distrib, sum_sub_distrib,
    ← sum_smul, hs, hdv, one_smul, zero_smul]
  abel

/-- The genuine affine orthogonal residual is the distance to the represented affine set. -/
theorem residual_eq_infDist (K : AffineSpatialPlane n m) (x : Spatial n) :
    ‖x - K.projection x‖ = Metric.infDist x K.toSet := by
  apply le_antisymm
  · apply (Metric.le_infDist K.nonempty).mpr
    intro y hy
    simpa [dist_eq_norm] using K.nearest x hy
  · simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem (K.projection_mem x)

theorem reset_displacement (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t B r d : ℝ)
    (K : AffineSpatialPlane n m) (hn : ∀ a ∈ s, 0 ≤ θ a x t)
    (hs : (∑ a ∈ s, θ a x t) = 1)
    (he : ∀ a ∈ s, Active θ a x t →
      ‖(L a).projection x - K.projection x‖ ≤ B * r * d) :
    ‖sigma s L θ x t - K.projection x‖ ≤ B * r * d := by
  rw [sigma_sub_projection s L θ x t K hs]
  have h := norm_sum_smul_le s (fun a => θ a x t)
    (fun a => (L a).projection x - K.projection x) (B * r * d)
    (fun a ha hz => he a ha (Or.inl hz))
  have hn' : (∑ a ∈ s, |θ a x t|) = 1 := by
    calc
      _ = ∑ a ∈ s, θ a x t := sum_congr rfl fun a ha => abs_of_nonneg (hn a ha)
      _ = 1 := hs
  simpa [hn'] using h

theorem reset_operator_bound (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t B C₀ r d : ℝ)
    (hr : 0 < r) (hB : 0 ≤ B) (hC : 0 ≤ C₀) (hd : 0 ≤ d)
    (K : AffineSpatialPlane n m) (hn : ∀ a ∈ s, 0 ≤ θ a x t)
    (hθ : ∀ a ∈ s, DifferentiableAt ℝ (fun y => θ a y t) x)
    (hs : (∑ a ∈ s, θ a x t) = 1) (hds : (∑ a ∈ s, dx θ a x t) = 0)
    (hdθ : ∑ a ∈ s, ‖dx θ a x t‖ ≤ C₀ / r)
    (hp : ∀ a ∈ s, Active θ a x t → ‖(L a).linearProjection - K.linearProjection‖ ≤ d)
    (he : ∀ a ∈ s, Active θ a x t →
      ‖(L a).projection x - K.projection x‖ ≤ B * r * d) :
    ‖fderiv ℝ (fun y => sigma s L θ y t) x - K.linearProjection‖ ≤ (1 + B * C₀) * d := by
  rw [fderiv_sub_projection s L θ x t K hθ hs hds]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hn' : (∑ a ∈ s, |θ a x t|) = 1 := by
    calc
      _ = ∑ a ∈ s, θ a x t := sum_congr rfl fun a ha => abs_of_nonneg (hn a ha)
      _ = 1 := hs
  have h₁ : ‖∑ a ∈ s, θ a x t • (((L a).linearProjection - K.linearProjection) v)‖ ≤ d * ‖v‖ := by
    have h := norm_sum_smul_le s (fun a => θ a x t)
      (fun a => ((L a).linearProjection - K.linearProjection) v) (d * ‖v‖) ?_
    · simpa [hn'] using h
    · intro a ha hz
      exact (((L a).linearProjection - K.linearProjection).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hp a ha (Or.inl hz)) (norm_nonneg v))
  have hsum : (∑ a ∈ s, |dx θ a x t v|) ≤ (C₀ / r) * ‖v‖ := by
    calc
      _ ≤ ∑ a ∈ s, ‖dx θ a x t‖ * ‖v‖ := sum_le_sum fun a _ => (dx θ a x t).le_opNorm v
      _ = (∑ a ∈ s, ‖dx θ a x t‖) * ‖v‖ := (sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hdθ (norm_nonneg v)
  have h₂ : ‖∑ a ∈ s, dx θ a x t v • ((L a).projection x - K.projection x)‖ ≤
      (B * C₀ * d) * ‖v‖ := by
    calc
      _ ≤ (∑ a ∈ s, |dx θ a x t v|) * (B * r * d) := by
        apply CoherentProjection.norm_sum_smul_le
        intro a ha hz
        exact he a ha (Or.inr (Or.inl (fun hzero => hz (by simp [hzero]))))
      _ ≤ ((C₀ / r) * ‖v‖) * (B * r * d) := mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = _ := by field_simp
  simp only [add_apply, _root_.sum_apply, smul_apply, smulRight_apply]
  calc
    _ ≤ ‖∑ a ∈ s, θ a x t • (((L a).linearProjection - K.linearProjection) v)‖ +
        ‖∑ a ∈ s, dx θ a x t v • ((L a).projection x - K.projection x)‖ := norm_add_le _ _
    _ ≤ d * ‖v‖ + (B * C₀ * d) * ‖v‖ := add_le_add h₁ h₂
    _ = _ := by ring

/-- The reset estimates: full weight locally supplies both hypotheses of the two reset estimates. -/
theorem reset_estimates (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t B C₀ r d : ℝ)
    (hr : 0 < r) (hB : 0 ≤ B) (hC : 0 ≤ C₀) (hd : 0 ≤ d)
    (K : AffineSpatialPlane n m) (hn : ∀ a ∈ s, 0 ≤ θ a x t)
    (hθ : ∀ a ∈ s, DifferentiableAt ℝ (fun y => θ a y t) x)
    (hfull : ∀ᶠ y in 𝓝 x, ∑ a ∈ s, θ a y t = 1)
    (hdθ : ∑ a ∈ s, ‖dx θ a x t‖ ≤ C₀ / r)
    (hp : ∀ a ∈ s, Active θ a x t → ‖(L a).linearProjection - K.linearProjection‖ ≤ d)
    (he : ∀ a ∈ s, Active θ a x t →
      ‖(L a).projection x - K.projection x‖ ≤ B * r * d) :
    Metric.infDist (sigma s L θ x t) K.toSet ≤ B * r * d ∧
    ‖fderiv ℝ (fun y => sigma s L θ y t) x - K.linearProjection‖ ≤ (1 + B * C₀) * d := by
  obtain ⟨hs, hds⟩ := local_full_weight s θ x t hθ hfull
  refine ⟨?_, reset_operator_bound s L θ x t B C₀ r d hr hB hC hd K hn hθ hs hds hdθ hp he⟩
  rw [← residual_eq_infDist]
  exact (K.nearest _ (K.projection_mem x)).trans (reset_displacement s L θ x t B r d K hn hs he)

/-! ### Step 3: the linear graph bridge -/

/-- The restriction of a spatial operator to a subspace. -/
def restrictedMap (S : Spatial n →L[ℝ] Spatial n) (T : Submodule ℝ (Spatial n)) :
    T →L[ℝ] Spatial n := S.comp T.subtypeL

/-- The restriction followed by orthogonal projection onto `U`, as a map `T → U`. -/
def projectedMap (S : Spatial n →L[ℝ] Spatial n) (T U : Submodule ℝ (Spatial n)) :
    T →L[ℝ] U := U.orthogonalProjectionOnto.comp (restrictedMap S T)

/-- The actual image `S T` of the subspace `T`. -/
def restrictedRange (S : Spatial n →L[ℝ] Spatial n) (T : Submodule ℝ (Spatial n)) :
    Submodule ℝ (Spatial n) := (restrictedMap S T).range

/-- The graph `{y + g y : y ∈ U}` of a map defined on `U`. -/
def graphOver (U : Submodule ℝ (Spatial n)) (g : U →L[ℝ] Spatial n) :
    Submodule ℝ (Spatial n) := (U.subtypeL + g).range

theorem projected_lower_bound (S : Spatial n →L[ℝ] Spatial n)
    (T U : Submodule ℝ (Spatial n)) (q : ℝ)
    (hS : ‖S - U.starProjection‖ ≤ q)
    (hT : ‖T.starProjection - U.starProjection‖ ≤ 1 / 10)
    (hq : q ≤ 1 / 10) (v : Spatial n) (hv : v ∈ T) :
    (4 / 5 : ℝ) * ‖v‖ ≤ ‖U.starProjection (S v)‖ := by
  have he : ‖v - U.starProjection v‖ ≤ (1 / 10 : ℝ) * ‖v‖ := by
    have h := (T.starProjection - U.starProjection).le_opNorm v
    rw [sub_apply, T.starProjection_eq_self_iff.mpr hv] at h
    exact h.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg v))
  have hs : ‖S v - U.starProjection v‖ ≤ q * ‖v‖ :=
    ((S - U.starProjection).le_opNorm v).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg v))
  have hp : ‖U.starProjection (S v - U.starProjection v)‖ ≤ q * ‖v‖ :=
    (U.norm_starProjection_apply_le _).trans hs
  have htri : ‖v‖ ≤ ‖v - U.starProjection v‖ +
      ‖U.starProjection (S v - U.starProjection v)‖ + ‖U.starProjection (S v)‖ := by
    calc
      ‖v‖ = ‖(v - U.starProjection v) - U.starProjection (S v - U.starProjection v) +
          U.starProjection (S v)‖ := by
            congr 1
            rw [map_sub, U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem v)]
            abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have hqv := mul_le_mul_of_nonneg_right hq (norm_nonneg v)
  linarith

theorem operator_lower_bound (S : Spatial n →L[ℝ] Spatial n)
    (T U : Submodule ℝ (Spatial n)) (q : ℝ)
    (hS : ‖S - U.starProjection‖ ≤ q)
    (hT : ‖T.starProjection - U.starProjection‖ ≤ 1 / 10)
    (hq : q ≤ 1 / 10) (v : Spatial n) (hv : v ∈ T) :
    (4 / 5 : ℝ) * ‖v‖ ≤ ‖S v‖ :=
  (projected_lower_bound S T U q hS hT hq v hv).trans (U.norm_starProjection_apply_le _)

theorem normal_component_le (S : Spatial n →L[ℝ] Spatial n)
    (U : Submodule ℝ (Spatial n)) (q : ℝ) (hS : ‖S - U.starProjection‖ ≤ q)
    (v : Spatial n) : ‖S v - U.starProjection (S v)‖ ≤ q * ‖v‖ := by
  have h := Uᗮ.norm_starProjection_apply_le (S v - U.starProjection v)
  have hid : Uᗮ.starProjection (S v - U.starProjection v) = S v - U.starProjection (S v) := by
    rw [Submodule.starProjection_orthogonal_val, map_sub,
      U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem v)]
    abel
  rw [hid] at h
  exact h.trans (((S - U.starProjection).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hS (norm_nonneg v)))

theorem projectedMap_injective (S : Spatial n →L[ℝ] Spatial n)
    (T U : Submodule ℝ (Spatial n)) (q : ℝ)
    (hS : ‖S - U.starProjection‖ ≤ q)
    (hT : ‖T.starProjection - U.starProjection‖ ≤ 1 / 10)
    (hq : q ≤ 1 / 10) : Function.Injective (projectedMap S T U) := by
  intro v w h
  have he : U.starProjection (S (v : Spatial n)) = U.starProjection (S (w : Spatial n)) :=
    congrArg (fun y : U => (y : Spatial n)) h
  have hl := projected_lower_bound S T U q hS hT hq ((v : Spatial n) - w)
    (T.sub_mem v.property w.property)
  have hz : U.starProjection (S ((v : Spatial n) - w)) = 0 := by simp [map_sub, he]
  rw [hz, norm_zero] at hl
  have hvw : (v : Spatial n) - w = 0 :=
    norm_eq_zero.mp (by nlinarith [norm_nonneg ((v : Spatial n) - w)])
  exact Subtype.ext (sub_eq_zero.mp hvw)

/-- A projection gap below one tenth forces equal dimensions (injections both ways). -/
theorem equal_finrank_of_gap (T U : Submodule ℝ (Spatial n))
    (hT : ‖T.starProjection - U.starProjection‖ ≤ 1 / 10) :
    Module.finrank ℝ T = Module.finrank ℝ U := by
  have h₁ := projectedMap_injective U.starProjection T U 0 (by simp) hT (by norm_num)
  have h₂ := projectedMap_injective T.starProjection U T 0 (by simp)
    (by simpa only [norm_sub_rev] using hT) (by norm_num)
  exact le_antisymm
    (LinearMap.finrank_le_finrank_of_injective
      (f := (projectedMap U.starProjection T U).toLinearMap) h₁)
    (LinearMap.finrank_le_finrank_of_injective
      (f := (projectedMap T.starProjection U T).toLinearMap) h₂)

/-- The linear graph bridge: dimension equality supplies the surjectivity needed for a genuine graph. -/
theorem linear_graph_bridge (S : Spatial n →L[ℝ] Spatial n)
    (T U : Submodule ℝ (Spatial n)) (q : ℝ) (hq0 : 0 ≤ q)
    (hS : ‖S - U.starProjection‖ ≤ q)
    (hT : ‖T.starProjection - U.starProjection‖ ≤ 1 / 10) (hq : q ≤ 1 / 10) :
    Function.Injective (restrictedMap S T) ∧
    Module.finrank ℝ (restrictedRange S T) = Module.finrank ℝ U ∧
    Function.Bijective (projectedMap S T U) ∧
    ∃ g : U →L[ℝ] Spatial n, (∀ y, g y ∈ Uᗮ) ∧ ‖g‖ ≤ 2 * q ∧
      restrictedRange S T = graphOver U g := by
  have hinj := projectedMap_injective S T U q hS hT hq
  have hrank := equal_finrank_of_gap T U hT
  have hsurj : Function.Surjective (projectedMap S T U) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (projectedMap S T U).toLinearMap) hrank).mp hinj
  have hSinj : Function.Injective (restrictedMap S T) := by
    intro v w he
    apply hinj
    apply Subtype.ext
    exact congrArg U.starProjection he
  let e : T ≃L[ℝ] U := (LinearEquiv.ofBijective
    (projectedMap S T U).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have he (v : T) : (e v : Spatial n) = U.starProjection (S v) := rfl
  let g : U →L[ℝ] Spatial n :=
    (Uᗮ.starProjection.comp (restrictedMap S T)).comp e.symm.toContinuousLinearMap
  have hg (y : U) : g y = S (e.symm y) - (y : Spatial n) := by
    change Uᗮ.starProjection (S (e.symm y)) = _
    rw [Submodule.starProjection_orthogonal_val, ← he, e.apply_symm_apply]
  have hgn : ‖g‖ ≤ 2 * q := by
    apply g.opNorm_le_bound (by positivity)
    intro y
    have hlo := projected_lower_bound S T U q hS hT hq (e.symm y) (e.symm y).property
    have hno := normal_component_le S U q hS (e.symm y)
    rw [← he, e.apply_symm_apply] at hlo hno
    rw [hg]
    have hy : ‖(y : Spatial n)‖ = ‖y‖ := rfl
    rw [hy] at hlo
    have h₁ : ‖((e.symm y : T) : Spatial n)‖ ≤ (5 / 4 : ℝ) * ‖y‖ := by linarith
    calc
      ‖S ((e.symm y : T) : Spatial n) - (y : Spatial n)‖
          ≤ q * ‖((e.symm y : T) : Spatial n)‖ := hno
      _ ≤ q * ((5 / 4 : ℝ) * ‖y‖) := mul_le_mul_of_nonneg_left h₁ hq0
      _ ≤ 2 * q * ‖y‖ := by nlinarith [mul_nonneg hq0 (norm_nonneg y)]
  refine ⟨hSinj, ?_, ⟨hinj, hsurj⟩, g, ?_, hgn, ?_⟩
  · exact (LinearMap.finrank_range_of_inj (f := (restrictedMap S T).toLinearMap) hSinj).trans hrank
  · intro y
    exact Uᗮ.starProjection_apply_mem _
  · ext z
    change (∃ v : T, S (v : Spatial n) = z) ↔ (∃ y : U, (y : Spatial n) + g y = z)
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨e v, ?_⟩
      rw [hg, e.symm_apply_apply]
      abel
    · rintro ⟨y, rfl⟩
      refine ⟨e.symm y, ?_⟩
      rw [hg]
      abel

/-! ### Step 4: the projection onto a graph -/

theorem graph_projection (U : Submodule ℝ (Spatial n)) (g : U →L[ℝ] Spatial n)
    (hg : ∀ y, g y ∈ Uᗮ) (y : U) : U.starProjection ((y : Spatial n) + g y) = y := by
  have hz : U.starProjection (g y) = 0 := by
    have h : g y ∈ U.starProjection.ker := by simpa using hg y
    exact h
  simp [map_add, hz]

theorem graph_residual_le (U : Submodule ℝ (Spatial n)) (g : U →L[ℝ] Spatial n)
    (hg : ∀ y, g y ∈ Uᗮ) (z : Spatial n) (hz : z ∈ graphOver U g) :
    ‖z - U.starProjection z‖ ≤ ‖g‖ * ‖z‖ := by
  obtain ⟨y, rfl⟩ := hz
  change ‖(y : Spatial n) + g y - U.starProjection ((y : Spatial n) + g y)‖ ≤
    ‖g‖ * ‖(y : Spatial n) + g y‖
  rw [graph_projection U g hg, add_sub_cancel_left]
  have hy : ‖y‖ ≤ ‖(y : Spatial n) + g y‖ := by
    have h := U.norm_starProjection_apply_le ((y : Spatial n) + g y)
    rw [graph_projection U g hg] at h
    exact h
  exact (g.le_opNorm y).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg g))

theorem reference_residual_le (U : Submodule ℝ (Spatial n)) (g : U →L[ℝ] Spatial n)
    (y : U) : ‖(y : Spatial n) - (graphOver U g).starProjection y‖ ≤ ‖g‖ * ‖y‖ := by
  have hm : (y : Spatial n) + g y ∈ graphOver U g := ⟨y, rfl⟩
  have h := Metric.infDist_le_dist_of_mem (x := (y : Spatial n)) hm
  rw [← (graphOver U g).dist_starProjection_eq_infDist, dist_eq_norm, dist_eq_norm] at h
  have he : (y : Spatial n) - ((y : Spatial n) + g y) = -g y := by abel
  rw [he, norm_neg] at h
  exact h.trans (g.le_opNorm y)

/-- Projection onto a graph: the graph has two controlled residuals; adjoints give the projection bound. -/
theorem graph_projection_bound (U : Submodule ℝ (Spatial n)) (g : U →L[ℝ] Spatial n)
    (hg : ∀ y, g y ∈ Uᗮ) : ‖(graphOver U g).starProjection - U.starProjection‖ ≤ 2 * ‖g‖ := by
  let V := graphOver U g
  let A := (ContinuousLinearMap.id ℝ (Spatial n) - U.starProjection).comp V.starProjection
  let B := (ContinuousLinearMap.id ℝ (Spatial n) - V.starProjection).comp U.starProjection
  have hA : ‖A‖ ≤ ‖g‖ := by
    apply A.opNorm_le_bound (norm_nonneg g)
    intro x
    exact (graph_residual_le U g hg _ (V.starProjection_apply_mem x)).trans
      (mul_le_mul_of_nonneg_left (V.norm_starProjection_apply_le x) (norm_nonneg g))
  have hB : ‖B‖ ≤ ‖g‖ := by
    apply B.opNorm_le_bound (norm_nonneg g)
    intro x
    exact (reference_residual_le U g (U.orthogonalProjectionOnto x)).trans
      (mul_le_mul_of_nonneg_left (U.norm_starProjection_apply_le x) (norm_nonneg g))
  have hU : U.starProjection.adjoint = U.starProjection :=
    isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection U)
  have hV : V.starProjection.adjoint = V.starProjection :=
    isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection V)
  have hBadj : B.adjoint = U.starProjection - U.starProjection.comp V.starProjection := by
    simp only [B, adjoint_comp, map_sub, adjoint_id, hU, hV, comp_sub, comp_id]
  have he : V.starProjection - U.starProjection = A - B.adjoint := by
    rw [hBadj]
    ext x
    simp only [A, sub_apply, comp_apply, id_apply]
    abel_nf
  change ‖V.starProjection - U.starProjection‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖A‖ + ‖B.adjoint‖ := norm_sub_le _ _
    _ = ‖A‖ + ‖B‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 2 * ‖g‖ := by linarith

/-! ### Assembly -/

/-- The reset lemma, obtained from the four steps above
for the actual weighted projection `sigma` and its actual spatial derivative.

Hypotheses: nonnegative weights at `(x,t)`, spatially differentiable at `x`, with
`∑ θ_a = 1` on a spatial neighbourhood of `x` at time `t`, `∑ ‖D_x θ_a‖ ≤ C₀/r`, and for
every active index `‖P_a - P_K‖ ≤ d`, `‖π_a x - π_K x‖ ≤ B r d`; an incoming linear
subspace `T` with `‖P_T - P_K‖ ≤ 1/10`, and `(1 + B C₀) d ≤ 1/10`.

Conclusions: `dist(σ(x,t), K) ≤ B r d`; `‖D_xσ - P_K‖ ≤ (1 + B C₀) d`; `D_xσ` is injective
on `T`; its actual image `T'` has dimension `m`; `P_K` maps `T'` onto `K`'s direction
bijectively (as the map `T → dir K`); and `‖P_{T'} - P_K‖ ≤ 8 (1 + B C₀) d`. -/
theorem reset (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t B C₀ r d : ℝ)
    (hr : 0 < r) (hB : 0 ≤ B) (hC : 0 ≤ C₀) (hd : 0 ≤ d)
    (K : AffineSpatialPlane n m) (hn : ∀ a ∈ s, 0 ≤ θ a x t)
    (hθ : ∀ a ∈ s, DifferentiableAt ℝ (fun y => θ a y t) x)
    (hfull : ∀ᶠ y in 𝓝 x, ∑ a ∈ s, θ a y t = 1)
    (hdθ : ∑ a ∈ s, ‖dx θ a x t‖ ≤ C₀ / r)
    (hp : ∀ a ∈ s, Active θ a x t → ‖(L a).linearProjection - K.linearProjection‖ ≤ d)
    (he : ∀ a ∈ s, Active θ a x t →
      ‖(L a).projection x - K.projection x‖ ≤ B * r * d)
    (T : Submodule ℝ (Spatial n))
    (hT : ‖T.starProjection - K.linearProjection‖ ≤ 1 / 10)
    (hsmall : (1 + B * C₀) * d ≤ 1 / 10) :
    Metric.infDist (sigma s L θ x t) K.toSet ≤ B * r * d ∧
    ‖fderiv ℝ (fun y => sigma s L θ y t) x - K.linearProjection‖ ≤ (1 + B * C₀) * d ∧
    Function.Injective (restrictedMap (fderiv ℝ (fun y => sigma s L θ y t) x) T) ∧
    Module.finrank ℝ (restrictedRange (fderiv ℝ (fun y => sigma s L θ y t) x) T) = m ∧
    Function.Bijective (projectedMap (fderiv ℝ (fun y => sigma s L θ y t) x) T K.direction) ∧
    ‖(restrictedRange (fderiv ℝ (fun y => sigma s L θ y t) x) T).starProjection -
        K.linearProjection‖ ≤ 8 * (1 + B * C₀) * d := by
  have hb := reset_estimates s L θ x t B C₀ r d hr hB hC hd K hn hθ hfull hdθ hp he
  have hq0 : 0 ≤ (1 + B * C₀) * d := by positivity
  obtain ⟨hinj, hrank, hbij, g, hg, hgn, himage⟩ :=
    linear_graph_bridge (fderiv ℝ (fun y => sigma s L θ y t) x)
      T K.direction ((1 + B * C₀) * d) hq0 hb.2 hT hsmall
  refine ⟨hb.1, hb.2, hinj, hrank.trans K.rank_eq, hbij, ?_⟩
  rw [himage]
  exact (graph_projection_bound K.direction g hg).trans (by linarith)

/-- The same reset under full weight on a space-time neighbourhood of `(x,t)`. -/
theorem reset_of_spacetime (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t B C₀ r d : ℝ)
    (hr : 0 < r) (hB : 0 ≤ B) (hC : 0 ≤ C₀) (hd : 0 ≤ d)
    (K : AffineSpatialPlane n m) (hn : ∀ a ∈ s, 0 ≤ θ a x t)
    (hθ : ∀ a ∈ s, DifferentiableAt ℝ (fun y => θ a y t) x)
    (hfull : ∀ᶠ p in 𝓝 (x, t), ∑ a ∈ s, θ a p.1 p.2 = 1)
    (hdθ : ∑ a ∈ s, ‖dx θ a x t‖ ≤ C₀ / r)
    (hp : ∀ a ∈ s, Active θ a x t → ‖(L a).linearProjection - K.linearProjection‖ ≤ d)
    (he : ∀ a ∈ s, Active θ a x t →
      ‖(L a).projection x - K.projection x‖ ≤ B * r * d)
    (T : Submodule ℝ (Spatial n))
    (hT : ‖T.starProjection - K.linearProjection‖ ≤ 1 / 10)
    (hsmall : (1 + B * C₀) * d ≤ 1 / 10) :
    Metric.infDist (sigma s L θ x t) K.toSet ≤ B * r * d ∧
    ‖fderiv ℝ (fun y => sigma s L θ y t) x - K.linearProjection‖ ≤ (1 + B * C₀) * d ∧
    Function.Injective (restrictedMap (fderiv ℝ (fun y => sigma s L θ y t) x) T) ∧
    Module.finrank ℝ (restrictedRange (fderiv ℝ (fun y => sigma s L θ y t) x) T) = m ∧
    Function.Bijective (projectedMap (fderiv ℝ (fun y => sigma s L θ y t) x) T K.direction) ∧
    ‖(restrictedRange (fderiv ℝ (fun y => sigma s L θ y t) x) T).starProjection -
        K.linearProjection‖ ≤ 8 * (1 + B * C₀) * d :=
  reset s L θ x t B C₀ r d hr hB hC hd K hn hθ
    (eventually_spatial_of_spacetime s θ x t hfull) hdθ hp he T hT hsmall

end ParabolicRectifiability.ProjectionReset
