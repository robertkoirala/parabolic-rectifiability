import ParabolicRectifiability.QuantitativeCharacterization.References

/-! # Basic facts of the closed ADR references

Proof of `ba1_horizontal_basic`, `ba1_vertical_basic` and `ba1_ambient_basic`.

* `b1basic_innerRegular`: a measure on `Space n` that is finite on compacts is inner regular
  (`Space n` is proper and second countable, hence Polish and σ-compact).
* Horizontal references (`σ = (F,T)_# L^k`, `Γ = supp σ`):
  - `b1basic_measurable_height`: the plateau function `T` is Borel (`T` is continuous on the
    closed `D` by the quadratic trace bound, and constant on each of the countably many Borel
    faces, which partition `Dᶜ`); `b1basic_measurable_map`: `(F,T)` is Borel.
  - `b1basic_horizontal_finiteOnCompacts`: `(F,T)⁻¹ K ⊆ F⁻¹(π₁ K)`, which is compact since
    `F` is a bi-Lipschitz closed embedding of `ℝ^k`.
* Vertical references (`Φ(p) = (F(p), t)`, `σ = Φ_# L^{m+1}`, `Γ = im Φ`):
  - `b1basic_vertical_isClosedEmbedding`: `Φ` is bi-Lipschitz on the complete `Space m`.
  - `b1basic_vertical_support`: `supp σ = im Φ` (preimages of neighbourhoods of `Φ p` contain
    balls of positive volume; the open complement of the range is `σ`-null).
* The ambient reference: `b1basic_parabolicVolume_support` (every ball has volume
  `2 ω_n r^{n+2} > 0`).

None of the helpers uses a sign condition on `L`; the hypothesis `1 ≤ L` of the statement types is
not needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-! ### Generalities on `Space n` -/

/-- A measure on parabolic space that is finite on compact sets is inner regular: it is
σ-finite (locally finite on a σ-compact space) and inner regular by compacts on sets of finite
measure (complete second-countable metric space). -/
theorem b1basic_innerRegular {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ] :
    μ.InnerRegular := by
  have : SigmaFinite μ := inferInstance
  have : μ.InnerRegularCompactLTTop := inferInstance
  infer_instance

/-- Every open parabolic ball of positive radius has positive volume `2 ω_n r^{n+2}`. -/
theorem b1basic_parabolicVolume_ball_pos {n : ℕ} (z : Space n) {r : ℝ} (hr : 0 < r) :
    0 < parabolicVolume n (Metric.ball z r) := by
  rw [parabolicVolume_ball z r hr]
  refine ENNReal.mul_pos (ENNReal.mul_pos (by norm_num) (omega_pos n).ne').ne' ?_
  exact pow_ne_zero _ (ENNReal.ofReal_pos.2 hr).ne'

/-- A point is in the support of a push-forward of `parabolicVolume` under a measurable map
that is continuous at a preimage point. -/
theorem b1basic_mem_support_map {n m : ℕ} {f : Space m → Space n} (hf : Measurable f)
    {p : Space m} (hc : ContinuousAt f p) :
    f p ∈ (Measure.map f (parabolicVolume m)).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hc.preimage_mem_nhds hU)
  calc (0 : ℝ≥0∞) < parabolicVolume m (Metric.ball p r) := b1basic_parabolicVolume_ball_pos p hr
    _ ≤ parabolicVolume m (f ⁻¹' U) := measure_mono hball
    _ ≤ Measure.map f (parabolicVolume m) U := Measure.le_map_apply hf.aemeasurable U

/-! ### Horizontal references -/

section Horizontal

variable {n k : ℕ} {L : ℝ}

/-- `F` is Lipschitz with constant `L⁺`. -/
theorem b1basic_spatialMap_lipschitz (H : HorizontalReference n k L) :
    LipschitzWith (Real.toNNReal L) H.spatialMap :=
  LipschitzWith.of_dist_le' fun u v => (H.spatialMap_bilipschitz u v).2

/-- `F` is antilipschitz with constant `L⁺`. -/
theorem b1basic_spatialMap_antilipschitz (H : HorizontalReference n k L) :
    AntilipschitzWith (Real.toNNReal L) H.spatialMap :=
  AntilipschitzWith.of_le_mul_dist fun u v =>
    (H.spatialMap_bilipschitz u v).1.trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) dist_nonneg)

/-- `F` is a closed embedding of `ℝ^k` (complete) into `ℝ^n`. -/
theorem b1basic_spatialMap_isClosedEmbedding (H : HorizontalReference n k L) :
    IsClosedEmbedding H.spatialMap :=
  (b1basic_spatialMap_antilipschitz H).isClosedEmbedding
    (b1basic_spatialMap_lipschitz H).uniformContinuous

/-- The trace `τ = T|_D` is continuous on `D`: `|τ u - τ v| ≤ L² diam(D) |u - v|` on the
bounded set `D`. -/
theorem b1basic_continuousOn_height (H : HorizontalReference n k L) :
    ContinuousOn H.height H.domain := by
  have hb := H.domain_compact.isBounded
  refine (LipschitzOnWith.of_dist_le' (K := L ^ 2 * Metric.diam H.domain) ?_).continuousOn
  intro u hu v hv
  rw [Real.dist_eq]
  have huv : dist u v ≤ Metric.diam H.domain := Metric.dist_le_diam_of_mem hb hu hv
  have h0 : 0 ≤ dist u v := dist_nonneg
  have hL : 0 ≤ L ^ 2 := sq_nonneg L
  calc |H.height u - H.height v| ≤ L ^ 2 * dist u v ^ 2 := H.height_trace u hu v hv
    _ = (L ^ 2 * dist u v) * dist u v := by ring
    _ ≤ (L ^ 2 * Metric.diam H.domain) * dist u v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huv hL) h0

/-- Every base point lies in `D` or in one of the faces. -/
theorem b1basic_mem_domain_or_face (H : HorizontalReference n k L) (u : Spatial k) :
    u ∈ H.domain ∨ ∃ i, u ∈ H.face i := by
  by_cases hu : u ∈ H.domain
  · exact Or.inl hu
  · right
    have : u ∈ ⋃ i, H.face i := by
      rw [H.faces_cover]
      exact hu
    exact mem_iUnion.1 this

/-- The plateau function `T` is Borel. For open `s`, `T⁻¹ s ∩ D` is relatively open in the
closed `D`, and `T⁻¹ s ∩ face i` is `face i` or empty. -/
theorem b1basic_measurable_height (H : HorizontalReference n k L) :
    Measurable H.height := by
  refine measurable_of_isOpen fun s hs => ?_
  obtain ⟨U, hU, hUs⟩ := continuousOn_iff'.1 (b1basic_continuousOn_height H) s hs
  have hD : MeasurableSet (H.height ⁻¹' s ∩ H.domain) := by
    rw [hUs]
    exact hU.measurableSet.inter H.domain_compact.isClosed.measurableSet
  have hF : ∀ i, MeasurableSet (H.height ⁻¹' s ∩ H.face i) := by
    intro i
    by_cases hi : H.height (H.anchor i) ∈ s
    · have he : H.height ⁻¹' s ∩ H.face i = H.face i := by
        refine inter_eq_right.2 fun u hu => ?_
        show H.height u ∈ s
        rw [H.height_plateau i u hu]
        exact hi
      rw [he]
      exact H.face_measurable i
    · have he : H.height ⁻¹' s ∩ H.face i = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun u hu => hi ?_
        have h1 : H.height u ∈ s := hu.1
        rwa [H.height_plateau i u hu.2] at h1
      rw [he]
      exact MeasurableSet.empty
  have heq : H.height ⁻¹' s = (H.height ⁻¹' s ∩ H.domain) ∪ ⋃ i, (H.height ⁻¹' s ∩ H.face i) := by
    ext u
    simp only [mem_union, mem_inter_iff, mem_iUnion]
    constructor
    · intro hu
      rcases b1basic_mem_domain_or_face H u with h | ⟨i, h⟩
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨i, hu, h⟩
    · rintro (⟨hu, _⟩ | ⟨_, hu, _⟩) <;> exact hu
  rw [heq]
  exact hD.union (MeasurableSet.iUnion hF)

/-- The map `(F,T) : ℝ^k → X` is Borel. -/
theorem b1basic_measurable_map (H : HorizontalReference n k L) : Measurable H.map := by
  have h : Measurable (fun u => ((H.spatialMap u, H.height u) : Coordinates n)) :=
    (b1basic_spatialMap_lipschitz H).continuous.measurable.prodMk (b1basic_measurable_height H)
  exact measurable_point.comp h

/-- `σ = (F,T)_# L^k` is finite on compact sets: `(F,T)⁻¹ K ⊆ F⁻¹(π₁ K)`, a compact set. -/
theorem b1basic_horizontal_finiteOnCompacts (H : HorizontalReference n k L) :
    IsFiniteMeasureOnCompacts H.measure := by
  refine ⟨fun K hK => ?_⟩
  have hK' : IsCompact (H.spatialMap ⁻¹' ((fun z : Space n => z.1) '' K)) :=
    (b1basic_spatialMap_isClosedEmbedding H).isCompact_preimage (hK.image continuous_spatial)
  rw [HorizontalReference.measure, Measure.map_apply (b1basic_measurable_map H) hK.measurableSet]
  refine lt_of_le_of_lt (measure_mono fun u hu => ?_) hK'.measure_lt_top
  exact ⟨H.map u, hu, rfl⟩

/-- The horizontal measure `σ` is not zero: `σ(X) = L^k(ℝ^k)`. -/
theorem b1basic_horizontal_measure_ne_zero (H : HorizontalReference n k L) : H.measure ≠ 0 := by
  rw [HorizontalReference.measure, Ne,
    Measure.map_eq_zero_iff (b1basic_measurable_map H).aemeasurable]
  exact NeZero.ne _

end Horizontal

/-! ### Vertical references -/

section Vertical

variable {n k : ℕ} {L : ℝ}

/-- `Φ` is Lipschitz with constant `L⁺`. -/
theorem b1basic_vertical_lipschitz (V : VerticalReference n k L) :
    LipschitzWith (Real.toNNReal L) V.map :=
  LipschitzWith.of_dist_le' fun p q => (V.bilipschitz p q).2

/-- `Φ` is antilipschitz with constant `L⁺`. -/
theorem b1basic_vertical_antilipschitz (V : VerticalReference n k L) :
    AntilipschitzWith (Real.toNNReal L) V.map :=
  AntilipschitzWith.of_le_mul_dist fun p q =>
    (V.bilipschitz p q).1.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) dist_nonneg)

/-- `Φ` is a closed embedding (bi-Lipschitz on the complete space `Space m`). -/
theorem b1basic_vertical_isClosedEmbedding (V : VerticalReference n k L) :
    IsClosedEmbedding V.map :=
  (b1basic_vertical_antilipschitz V).isClosedEmbedding (b1basic_vertical_lipschitz V).uniformContinuous

/-- `supp σ = im Φ`. -/
theorem b1basic_vertical_support (V : VerticalReference n k L) :
    V.measure.support = V.carrier := by
  have hΦ := b1basic_vertical_isClosedEmbedding V
  apply Subset.antisymm
  · intro z hz
    by_contra hzr
    have hopen : IsOpen (range V.map)ᶜ := hΦ.isClosed_range.isOpen_compl
    have hpos := (Measure.mem_support_iff_forall z).1 hz _ (hopen.mem_nhds hzr)
    have he : V.map ⁻¹' (range V.map)ᶜ = ∅ := by
      rw [preimage_compl, preimage_range, compl_univ]
    rw [VerticalReference.measure, Measure.map_apply hΦ.continuous.measurable hopen.measurableSet,
      he, measure_empty] at hpos
    exact lt_irrefl _ hpos
  · rintro _ ⟨p, rfl⟩
    exact b1basic_mem_support_map hΦ.continuous.measurable hΦ.continuous.continuousAt

/-- `σ = Φ_# L^{m+1}` is finite on compact sets (compact preimages under the closed embedding). -/
theorem b1basic_vertical_finiteOnCompacts (V : VerticalReference n k L) :
    IsFiniteMeasureOnCompacts V.measure := by
  have hΦ := b1basic_vertical_isClosedEmbedding V
  refine ⟨fun K hK => ?_⟩
  rw [VerticalReference.measure, Measure.map_apply hΦ.continuous.measurable hK.measurableSet]
  exact (hΦ.isCompact_preimage hK).measure_lt_top

end Vertical

/-! ### The ambient reference -/

/-- The support of `parabolicVolume n` is all of `X`. -/
theorem b1basic_parabolicVolume_support (n : ℕ) : (parabolicVolume n).support = Set.univ := by
  refine eq_univ_of_forall fun z => ?_
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  exact lt_of_lt_of_le (b1basic_parabolicVolume_ball_pos z hr) (measure_mono hball)

/-! ### The statements -/

/-- **`ba1_horizontal_basic`** (statement type). -/
theorem ba1_horizontal_basic_proof :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      Measurable H.map ∧ IsClosed H.carrier ∧ IsFiniteMeasureOnCompacts H.measure ∧
        H.measure.InnerRegular := by
  intro n k L _ H
  have := b1basic_horizontal_finiteOnCompacts H
  exact ⟨b1basic_measurable_map H, Measure.isClosed_support, inferInstance,
    b1basic_innerRegular _⟩

/-- **`ba1_vertical_basic`** (statement type). -/
theorem ba1_vertical_basic_proof :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ V : VerticalReference n k L,
      MeasurableEmbedding V.map ∧ IsClosed V.carrier ∧ V.measure.support = V.carrier ∧
        IsFiniteMeasureOnCompacts V.measure ∧ V.measure.InnerRegular := by
  intro n k L _ V
  have := b1basic_vertical_finiteOnCompacts V
  exact ⟨(b1basic_vertical_isClosedEmbedding V).measurableEmbedding,
    (b1basic_vertical_isClosedEmbedding V).isClosed_range, b1basic_vertical_support V,
    inferInstance, b1basic_innerRegular _⟩

/-- **`ba1_ambient_basic`** (statement type). -/
theorem ba1_ambient_basic_proof :
    ∀ n : ℕ, (parabolicVolume n).InnerRegular ∧ (parabolicVolume n).support = Set.univ :=
  fun n => ⟨b1basic_innerRegular _, b1basic_parabolicVolume_support n⟩

end ParabolicRectifiability.QuantitativeCharacterization
