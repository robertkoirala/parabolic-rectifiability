import ParabolicRectifiability.Examples.Proofs.Reductions.TimeSliceStatements

/-! # The time-slice identity for `B_p`

Stated as an implication over the affine enlargement statement `E2AffineEnlargementStatement`.
For the slice map `ι y = point y t₀`, every measure `ν` on `ℝⁿ`,
`1 ≤ k ≤ n`, `p > 0`, the horizontal or mixed family, every centre and every real radius,
`B_{p,ι_#ν}(ιx, r) = b^E_{p,ν,k}(x, r)`.

Route (pointwise before any power or infimum; no interchange of infimum and integral):
* change of variables `setLIntegral_map` (no finiteness of `ν`), with `ι⁻¹(P(ιx,r)) = B(x,r)`;
* every model set `S` whose points have spatial part in `A` satisfies
  `infEDist(y, A) ≤ infEDist(ιy, S)` (the parabolic distance dominates the spatial one);
  for the horizontal model `A × {t₀}` this is an equality;
* a vertical model `V × ℝ` of spatial rank `k - 2` is first enlarged by
  `E2AffineEnlargementStatement` (the hypothesis) to a spatial `k`-plane `U ⊇ V`, so `infEDist(y, U) ≤ infEDist(y, V) ≤ infEDist(ιy, V × ℝ)`;
* hence the two infima agree, and the normalizations `(ofReal r)⁻¹ ^ (k + p)` are identical. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The slice map `y ↦ (y, t₀)` is measurable. -/
private theorem e2_tsb_measurable_slice {n : ℕ} (t₀ : ℝ) :
    Measurable (fun y : Spatial n => point y t₀) :=
  (measurable_point (n := n)).comp (measurable_id.prodMk measurable_const)

/-- The slice map pulls the parabolic ball `P(ιx, r)` back to the Euclidean ball `B(x, r)`, for
every real radius. -/
private theorem e2_tsb_preimage_ball {n : ℕ} (t₀ : ℝ) (x : Spatial n) (r : ℝ) :
    (fun y : Spatial n => point y t₀) ⁻¹' Metric.ball (point x t₀) r = Metric.ball x r := by
  ext y
  simp only [mem_preimage, Metric.mem_ball, dist_point, sub_self, abs_zero, Real.sqrt_zero,
    max_eq_left (norm_nonneg _), dist_eq_norm]

/-- If every point of `S` has spatial part in `A`, the parabolic distance from `ιy` to `S`
dominates the spatial distance from `y` to `A`. -/
private theorem e2_tsb_infEDist_le {n : ℕ} {A : Set (Spatial n)} {S : Set (Space n)}
    (hS : ∀ w ∈ S, w.1 ∈ A) (y : Spatial n) (t : ℝ) :
    Metric.infEDist y A ≤ Metric.infEDist (point y t) S := by
  refine Metric.le_infEDist.mpr fun w hw => ?_
  calc Metric.infEDist y A ≤ edist y w.1 := Metric.infEDist_le_edist_of_mem (hS w hw)
    _ ≤ edist (point y t) w := by
      rw [Prod.edist_eq]
      exact le_max_left _ _

/-- If moreover `A × {t}` lies in `S`, the two distances are equal. -/
private theorem e2_tsb_infEDist_slice {n : ℕ} {A : Set (Spatial n)} {S : Set (Space n)}
    (hS : ∀ w ∈ S, w.1 ∈ A) (t : ℝ) (hA : ∀ u ∈ A, point u t ∈ S) (y : Spatial n) :
    Metric.infEDist (point y t) S = Metric.infEDist y A := by
  refine le_antisymm (Metric.le_infEDist.mpr fun u hu => ?_) (e2_tsb_infEDist_le hS y t)
  calc Metric.infEDist (point y t) S ≤ edist (point y t) (point u t) :=
        Metric.infEDist_le_edist_of_mem (hA u hu)
    _ = edist y u := by
      rw [edist_dist, edist_dist, dist_point, sub_self, abs_zero, Real.sqrt_zero,
        max_eq_left (norm_nonneg _), dist_eq_norm]

/-- The same-time horizontal model `U × {t₀}` realizes the spatial distance to `U`. -/
private theorem e2_tsb_horizontal_eq {n k : ℕ} (hk : 1 ≤ k) (U : AffineSpatialPlane n k)
    (t₀ : ℝ) (y : Spatial n) :
    Metric.infEDist (point y t₀) (HorizontalModel.mk hk U t₀).toSet =
      Metric.infEDist y U.toSet :=
  e2_tsb_infEDist_slice (A := U.toSet) (S := (HorizontalModel.mk hk U t₀).toSet)
    (fun _ hw => hw.1) t₀ (fun _ hu => ⟨hu, rfl⟩) y

/-- Every horizontal model `U × {τ}` is at least as far as its spatial plane `U`. -/
private theorem e2_tsb_horizontal_le {n k : ℕ} (L : HorizontalModel n k) (y : Spatial n)
    (t₀ : ℝ) :
    Metric.infEDist y L.spatial.toSet ≤ Metric.infEDist (point y t₀) L.toSet :=
  e2_tsb_infEDist_le (A := L.spatial.toSet) (S := L.toSet) (fun _ hw => hw.1) y t₀

/-- Every vertical model `V × ℝ` is at least as far as its spatial plane `V`. -/
private theorem e2_tsb_vertical_le {n k : ℕ} (L : VerticalModel n k) (y : Spatial n)
    (t₀ : ℝ) :
    Metric.infEDist y L.spatial.toSet ≤ Metric.infEDist (point y t₀) L.toSet :=
  e2_tsb_infEDist_le (A := L.spatial.toSet) (S := L.toSet) (fun _ hw => hw) y t₀

/-- The fixed-model change of variables: the fitting integral of `ι_#ν` over `P(ιx, r)` is the
`ν`-integral over `B(x, r)` of the parabolic distance from `ιy`. No finiteness of `ν`. -/
private theorem e2_tsb_fitPow_map {n k : ℕ} {T : FamilyKind} (ν : Measure (Spatial n))
    (p t₀ : ℝ) (L : Models n k T) (x : Spatial n) (r : ℝ) :
    fitPow (ν.map (fun y : Spatial n => point y t₀)) p L (point x t₀) r =
      ∫⁻ y in Metric.ball x r, Metric.infEDist (point y t₀) (modelSet L) ^ p ∂ν := by
  unfold fitPow
  rw [setLIntegral_map measurableSet_ball (measurable_infEDist.pow_const p)
    (e2_tsb_measurable_slice t₀), e2_tsb_preimage_ball]

/-- The pointwise comparisons for the horizontal and mixed families: every spatial `k`-plane is
matched by a model at no larger distance, and every model is bounded below by some spatial
`k`-plane (vertical models via the enlargement statement). -/
private theorem e2_tsb_families {n k : ℕ} (hE : E2AffineEnlargementStatement) (hk : 1 ≤ k)
    (hkn : k ≤ n) (t₀ : ℝ) {T : FamilyKind} (hT : T = .horizontal ∨ T = .mixed) :
    (∀ U : AffineSpatialPlane n k, ∃ L : Models n k T,
      ∀ y, Metric.infEDist (point y t₀) (modelSet L) ≤ Metric.infEDist y U.toSet) ∧
    (∀ L : Models n k T, ∃ U : AffineSpatialPlane n k,
      ∀ y, Metric.infEDist y U.toSet ≤ Metric.infEDist (point y t₀) (modelSet L)) := by
  rcases hT with rfl | rfl
  · refine ⟨fun U => ⟨(HorizontalModel.mk hk U t₀ : HorizontalModel n k),
      fun y => (e2_tsb_horizontal_eq hk U t₀ y).le⟩, fun L => ?_⟩
    change HorizontalModel n k at L
    exact ⟨L.spatial, fun y => e2_tsb_horizontal_le L y t₀⟩
  · refine ⟨fun U => ⟨(Sum.inl (HorizontalModel.mk hk U t₀) : AdmissibleModel n k),
      fun y => (e2_tsb_horizontal_eq hk U t₀ y).le⟩, fun L => ?_⟩
    change AdmissibleModel n k at L
    rcases L with L | L
    · exact ⟨L.spatial, fun y => e2_tsb_horizontal_le L y t₀⟩
    · obtain ⟨U, hsub⟩ := hE n L.spatialRank k (by have := L.rank_eq; omega) hkn L.spatial
      exact ⟨U, fun y => (Metric.infEDist_anti hsub).trans (e2_tsb_vertical_le L y t₀)⟩

/-- Equality of the two fitting infima from the pointwise comparisons (each candidate compared
pointwise, no interchange of infimum and integral; valid for every `p ≥ 0`). -/
private theorem e2_tsb_iInf_eq {n k : ℕ} {T : FamilyKind} (ν : Measure (Spatial n)) {p : ℝ}
    (hp : 0 ≤ p) (t₀ : ℝ) (x : Spatial n) (r : ℝ)
    (hle : ∀ U : AffineSpatialPlane n k, ∃ L : Models n k T,
      ∀ y, Metric.infEDist (point y t₀) (modelSet L) ≤ Metric.infEDist y U.toSet)
    (hge : ∀ L : Models n k T, ∃ U : AffineSpatialPlane n k,
      ∀ y, Metric.infEDist y U.toSet ≤ Metric.infEDist (point y t₀) (modelSet L)) :
    ⨅ L : Models n k T,
        ∫⁻ y in Metric.ball x r, Metric.infEDist (point y t₀) (modelSet L) ^ p ∂ν =
      ⨅ U : AffineSpatialPlane n k,
        ∫⁻ y in Metric.ball x r, Metric.infEDist y U.toSet ^ p ∂ν := by
  refine le_antisymm (le_iInf fun U => ?_) (le_iInf fun L => ?_)
  · obtain ⟨L, hL⟩ := hle U
    exact (iInf_le _ L).trans (lintegral_mono fun y => ENNReal.rpow_le_rpow (hL y) hp)
  · obtain ⟨U, hU⟩ := hge L
    exact (iInf_le _ U).trans (lintegral_mono fun y => ENNReal.rpow_le_rpow (hU y) hp)

/-- The time-slice identity `B_{p,ι_#ν}(ιx, r) = b^E_{p,ν,k}(x, r)`, from the
affine enlargement statement `E2AffineEnlargementStatement`. -/
theorem e2_timeSlice_betaPow_of_enlarge_proof :
    E2AffineEnlargementStatement → E2TimeSliceBetaPowStatement := by
  intro hE n k hk hkn ν p hp t₀ T hT x r
  obtain ⟨hle, hge⟩ := e2_tsb_families hE hk hkn t₀ hT
  unfold betaPow euclideanBetaPow
  by_cases hr : 0 < r
  · rw [ite_eq_left hr, ite_eq_left hr]
    simp only [e2_tsb_fitPow_map]
    rw [e2_tsb_iInf_eq ν hp.le t₀ x r hle hge]
  · rw [ite_eq_right hr, ite_eq_right hr]

end ParabolicRectifiability.Examples
