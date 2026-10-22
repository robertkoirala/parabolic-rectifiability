import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry

/-! # Monotonicity in the covering constants

Increasing the reference parameter `L` keeps every reference with
the same data (its measure, carrier and type are unchanged); increasing `K` and `L` keeps every
regular mixed covering with the same balls, bad set and scale sets. Hence the approximants,
residuals, typed trace splits and measure identities of a covering are unchanged, and the
relative tail weakens. This proves monotonicity of the `(K,L)` property, and supplies the
constant changes used by the other modules of this part.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

theorem hasStandardParabolicBMOBound_mono {m : ℕ} {g : Space m → ℝ} {B B' : ℝ}
    (h : HasStandardParabolicBMOBound m g B) (hB : B ≤ B') :
    HasStandardParabolicBMOBound m g B' :=
  ⟨h.1.trans hB, h.2.1, fun p r hr => (h.2.2 p r hr).trans hB⟩

theorem hasCoordinateHalfTimeBMOBound_mono {m d : ℕ}
    {F : Space m → EuclideanSpace ℝ (Fin d)} {B B' : ℝ}
    (h : HasCoordinateHalfTimeBMOBound m d F B) (hB : B ≤ B') :
    HasCoordinateHalfTimeBMOBound m d F B' := by
  intro α
  obtain ⟨hlip, f, hf, hrep⟩ := h α
  exact ⟨hlip, f, hasStandardParabolicBMOBound_mono hf hB, hrep⟩

namespace HorizontalReference

variable {n k : ℕ}

/-- A horizontal `L`-reference is a horizontal `L'`-reference for `0 ≤ L ≤ L'`, with the same
data. -/
def mono {L L' : ℝ} (H : HorizontalReference n k L) (hL : 0 ≤ L) (hLL' : L ≤ L') :
    HorizontalReference n k L' where
  available := H.available
  spatialMap := H.spatialMap
  spatialMap_bilipschitz := fun u v =>
    ⟨(H.spatialMap_bilipschitz u v).1.trans (mul_le_mul_of_nonneg_right hLL' dist_nonneg),
      (H.spatialMap_bilipschitz u v).2.trans (mul_le_mul_of_nonneg_right hLL' dist_nonneg)⟩
  domain := H.domain
  domain_nonempty := H.domain_nonempty
  domain_compact := H.domain_compact
  height := H.height
  height_trace := fun u hu v hv => (H.height_trace u hu v hv).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL hLL' 2) (sq_nonneg _))
  gridOrigin := H.gridOrigin
  gridScale := H.gridScale
  gridScale_pos := H.gridScale_pos
  cubeIndex := H.cubeIndex
  cube := H.cube
  cubeLevel := H.cubeLevel
  cubeCorner := H.cubeCorner
  cube_eq := H.cube_eq
  cube_interior_disjoint := H.cube_interior_disjoint
  cubes_cover := H.cubes_cover
  whitney_lower := H.whitney_lower
  whitney_upper := H.whitney_upper
  anchor := H.anchor
  anchor_mem := H.anchor_mem
  anchor_nearest := H.anchor_nearest
  face := H.face
  face_measurable := H.face_measurable
  interior_subset_face := H.interior_subset_face
  face_subset_cube := H.face_subset_cube
  face_disjoint := H.face_disjoint
  faces_cover := H.faces_cover
  height_plateau := H.height_plateau

end HorizontalReference

namespace VerticalReference

variable {n k : ℕ}

/-- A vertical `L`-reference is a vertical `L'`-reference for `L ≤ L'`, with the same data. -/
def mono {L L' : ℝ} (V : VerticalReference n k L) (hLL' : L ≤ L') :
    VerticalReference n k L' where
  spatialRank := V.spatialRank
  rank_eq := V.rank_eq
  lt_ambient := V.lt_ambient
  spatialMap := V.spatialMap
  bilipschitz := fun p q =>
    ⟨(V.bilipschitz p q).1.trans (mul_le_mul_of_nonneg_right hLL' dist_nonneg),
      (V.bilipschitz p q).2.trans (mul_le_mul_of_nonneg_right hLL' dist_nonneg)⟩
  coordinate_bmo := hasCoordinateHalfTimeBMOBound_mono V.coordinate_bmo hLL'

end VerticalReference

namespace Reference

variable {n k : ℕ} {L L' : ℝ}

/-- The same reference, viewed with a larger parameter `L' ≥ L ≥ 0`. -/
def mono (hL : 0 ≤ L) (hLL' : L ≤ L') : Reference n k L → Reference n k L'
  | horizontal H => horizontal (H.mono hL hLL')
  | vertical V => vertical (V.mono hLL')
  | ambient h => ambient h

@[simp] theorem kind_mono (hL : 0 ≤ L) (hLL' : L ≤ L') (ρ : Reference n k L) :
    (ρ.mono hL hLL').kind = ρ.kind := by
  cases ρ <;> rfl

@[simp] theorem carrier_mono (hL : 0 ≤ L) (hLL' : L ≤ L') (ρ : Reference n k L) :
    (ρ.mono hL hLL').carrier = ρ.carrier := by
  cases ρ <;> rfl

@[simp] theorem measure_mono (hL : 0 ≤ L) (hLL' : L ≤ L') (ρ : Reference n k L) :
    (ρ.mono hL hLL').measure = ρ.measure := by
  cases ρ <;> rfl

end Reference

namespace RegularMixedCovering

variable {n k : ℕ} {K L K' L' : ℝ} {μ : Measure (Space n)} {a : Space n} {R : ℝ}

/-- A `(K,L)`-regular mixed covering is a `(K',L')`-regular mixed covering for `K ≤ K'`,
`0 < L ≤ L'` and `R ≥ 0`, with the same balls, bad set, scale sets and references. -/
def mono (𝒞 : RegularMixedCovering k K L μ a R) (hR : 0 ≤ R) (hL : 0 < L) (hKK' : K ≤ K')
    (hLL' : L ≤ L') : RegularMixedCovering k K' L' μ a R where
  index := 𝒞.index
  reference := fun i => (𝒞.reference i).mono hL.le hLL'
  center := 𝒞.center
  radius := 𝒞.radius
  badSet := 𝒞.badSet
  scaleSet := 𝒞.scaleSet
  center_mem_support := 𝒞.center_mem_support
  radius_pos := 𝒞.radius_pos
  ball_subset := fun i =>
    (𝒞.ball_subset i).trans (Metric.ball_subset_ball (mul_le_mul_of_nonneg_right hLL' hR))
  ball_meets_carrier := fun i => by
    rw [Reference.carrier_mono]
    exact 𝒞.ball_meets_carrier i
  root_packing := 𝒞.root_packing.trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKK' (pow_nonneg hR k)))
  local_packing := fun b s hs => (𝒞.local_packing b s hs).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKK' (pow_nonneg hs.le k)))
  measurable_badSet := 𝒞.measurable_badSet
  measurable_scaleSet := 𝒞.measurable_scaleSet
  badSet_subset := 𝒞.badSet_subset
  scaleSet_subset := 𝒞.scaleSet_subset
  bad_inter_scale_null := 𝒞.bad_inter_scale_null
  scale_inter_scale_null := 𝒞.scale_inter_scale_null
  cover_null := 𝒞.cover_null
  scaleSet_cover := fun i p hp => by
    obtain ⟨h1, h2, h3⟩ := 𝒞.scaleSet_cover i hp
    refine ⟨h1, ?_, h3⟩
    rw [Reference.carrier_mono]
    exact le_trans
      (mul_le_mul_of_nonneg_right (inv_anti₀ hL hLL') Metric.infDist_nonneg) h2
  bad_bound := 𝒞.bad_bound.trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKK' (pow_nonneg hR k)))

variable (𝒞 : RegularMixedCovering k K L μ a R) (hR : 0 ≤ R) (hL : 0 < L) (hKK' : K ≤ K')
  (hLL' : L ≤ L')

theorem mono_approximant (F : Set (Space n)) (N : ℕ) :
    (𝒞.mono hR hL hKK' hLL').approximant F N = 𝒞.approximant F N := rfl

theorem mono_residual (N : ℕ) : (𝒞.mono hR hL hKK' hLL').residual N = 𝒞.residual N := rfl

theorem mono_typedTrace (T : FamilyKind) :
    (𝒞.mono hR hL hKK' hLL').typedTrace T = 𝒞.typedTrace T := by
  ext z
  simp only [typedTrace, ball, mono, Reference.kind_mono, Reference.carrier_mono, mem_iUnion]

variable {𝒞 hR hL hKK' hLL'}

theorem IsTypedTraceSplit.mono {FH FV : Set (Space n)} (h : 𝒞.IsTypedTraceSplit FH FV) :
    (𝒞.mono hR hL hKK' hLL').IsTypedTraceSplit FH FV where
  measurable_horizontal := h.measurable_horizontal
  measurable_vertical := h.measurable_vertical
  disjoint := h.disjoint
  horizontal_subset_root := h.horizontal_subset_root
  vertical_subset_root := h.vertical_subset_root
  horizontal_subset_trace := by
    rw [mono_typedTrace]
    exact h.horizontal_subset_trace
  vertical_subset_trace := by
    rw [mono_typedTrace]
    exact h.vertical_subset_trace
  null_remainder := h.null_remainder

theorem MeasureIdentity.mono {FH FV : Set (Space n)} (h : 𝒞.MeasureIdentity FH FV) :
    (𝒞.mono hR hL hKK' hLL').MeasureIdentity FH FV := fun N => by
  rw [mono_approximant, mono_approximant, mono_residual]
  exact h N

/-- The relative tail weakens when the covering constant increases. -/
theorem RelativeTail.mono {Ctail : ℝ} (hC : 0 < Ctail) (hK : 0 < K)
    (h : 𝒞.RelativeTail Ctail) : (𝒞.mono hR hL hKK' hLL').RelativeTail Ctail := fun N => by
  rw [mono_residual]
  refine (h N).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (mul_pos hC hK)
    (mul_le_mul_of_nonneg_left hKK' hC.le)

end RegularMixedCovering

/-- Monotonicity of the `(K,L)` property in both constants. -/
theorem IsQuantitativelyMixedRectifiable.mono {n k : ℕ} {K K' L L' : ℝ}
    {μ : Measure (Space n)} (hL : 0 < L) (hKK' : K ≤ K') (hLL' : L ≤ L')
    (h : IsQuantitativelyMixedRectifiable k K L μ) :
    IsQuantitativelyMixedRectifiable k K' L' μ := by
  refine ⟨h.1, fun a ha R hR => ?_⟩
  obtain ⟨𝒞⟩ := h.2 a ha R hR
  exact ⟨𝒞.mono hR.le hL hKK' hLL'⟩

/-- **Monotonicity** of the `(K,L)` property in `K` and `L`. -/
theorem quantitativeRectifiability_mono_skeleton : QuantitativeRectifiabilityMonoStatement := by
  intro n _ k _ _ μ _ _ K K' L L' _ hKK' hL hLL' h
  exact h.mono (by linarith) hKK' hLL'

end ParabolicRectifiability.QuantitativeCharacterization
