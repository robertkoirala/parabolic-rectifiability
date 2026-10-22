import ParabolicRectifiability.QuantitativeCharacterization.References

/-! # Trace points of a horizontal reference lie in its closed carrier

Proof of `b2_horizontalReference_map_mem_carrier`, with the shared geometry of the horizontal ADR
statement `ba1_horizontal_adr`.

Let `H` be a horizontal `L`-reference: spatial map `F`, compact domain `D`, plateau function
`T` (`τ = T|_D`), closed Whitney cubes `Q_i` with nearest anchors `a_i ∈ D`, faces `Φ_i`
(`int Q_i ⊆ Φ_i ⊆ Q_i`, partitioning `Dᶜ`) and `T = τ(a_i)` on `Φ_i`;
`σ = (F,T)_# L^k`, `Γ = supp σ`.

* `b1adrh_L_pos`: `0 < L` (`1 ≤ k` gives two distinct base points; `|u - v| ≤ L|F u - F v|`).
* `b1adrh_anchor_dist_le`: for `u ∈ D` and `v ∈ Q_i`, `|a_i - u| ≤ 3|v - u|`
  (`|a_i - x| = dist(Q_i,D) ≤ |v - u|` for the nearest point `x ∈ Q_i`, and
  `diam Q_i ≤ dist(Q_i,D)/4`).
* `b1adrh_height_sub_le`: for `u ∈ D` and every `v`, `|T v - τ u| ≤ 9 L² |v - u|²`.
* `b1adrh_measurable_map`: `(F,T)` is Borel (`T` is continuous on the closed `D` by the trace
  bound and constant on each of the countably many Borel faces).
* `b1adrh_ball_subset`: `B(u, r/(3L)) ⊆ (F,T)⁻¹ P((F u, τ u), r)` for `u ∈ D`.
* `b1adrh_map_mem_carrier`: trace points lie in `Γ` (`Measure.mem_support_iff_forall`).

The statement proof `Characterization.b2_horizontalReference_map_mem_carrier_proof` is at the end, in
the namespace its type requires.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

variable {n k : ℕ} {L : ℝ}

/-! ### The bi-Lipschitz constant -/

/-- `0 < L`: since `1 ≤ k` there are two distinct base points `u ≠ v`, and
`0 < |u - v| ≤ L |F u - F v|`. -/
theorem b1adrh_L_pos (H : HorizontalReference n k L) : 0 < L := by
  have hk : 0 < k := H.available.1
  have hpos : 0 < dist (EuclideanSpace.single (⟨0, hk⟩ : Fin k) (1 : ℝ)) 0 := by
    rw [dist_zero_right]
    simp
  have h1 := (H.spatialMap_bilipschitz (EuclideanSpace.single (⟨0, hk⟩ : Fin k) (1 : ℝ)) 0).1
  have hd : 0 ≤ dist (H.spatialMap (EuclideanSpace.single (⟨0, hk⟩ : Fin k) (1 : ℝ)))
      (H.spatialMap 0) := dist_nonneg
  by_contra hL
  have hL' : L ≤ 0 := not_lt.1 hL
  nlinarith

/-- `F` is Lipschitz, hence continuous. -/
theorem b1adrh_lipschitz (H : HorizontalReference n k L) :
    LipschitzWith (Real.toNNReal L) H.spatialMap :=
  LipschitzWith.of_dist_le' fun u v => (H.spatialMap_bilipschitz u v).2

/-! ### Whitney cubes as coordinate boxes -/

/-- The side `ℓ_i = λ 2^{j_i}` of the Whitney cube `Q_i`. -/
def b1adrh_side (H : HorizontalReference n k L) (i : H.cubeIndex) : ℝ :=
  H.gridScale * (2 : ℝ) ^ H.cubeLevel i

theorem b1adrh_side_pos (H : HorizontalReference n k L) (i : H.cubeIndex) :
    0 < b1adrh_side H i :=
  mul_pos H.gridScale_pos (zpow_pos two_pos _)

/-- The lower corner `c_α + ℓ_i m_α` of the Whitney cube `Q_i`. -/
def b1adrh_lo (H : HorizontalReference n k L) (i : H.cubeIndex) (α : Fin k) : ℝ :=
  H.gridOrigin α + b1adrh_side H i * (H.cubeCorner i α : ℝ)

/-- The closed Whitney cube `Q_i` is the box `[lo, lo + ℓ_i]^k`. -/
theorem b1adrh_mem_cube (H : HorizontalReference n k L) (i : H.cubeIndex) (x : Spatial k) :
    x ∈ H.cube i ↔ ∀ α, b1adrh_lo H i α ≤ x α ∧ x α ≤ b1adrh_lo H i α + b1adrh_side H i := by
  rw [H.cube_eq i]
  simp only [dyadicCube, mem_ofPred_eq, b1adrh_lo, b1adrh_side]
  have e : ∀ α : Fin k, H.gridOrigin α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i *
      ((H.cubeCorner i α : ℝ) + 1) = H.gridOrigin α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i *
        (H.cubeCorner i α : ℝ) + H.gridScale * (2 : ℝ) ^ H.cubeLevel i := fun α => by ring
  constructor
  · intro h α
    obtain ⟨h1, h2⟩ := h α
    exact ⟨h1, by linarith [e α]⟩
  · intro h α
    obtain ⟨h1, h2⟩ := h α
    exact ⟨h1, by linarith [e α]⟩

/-- Two points of `Q_i` are at distance at most `√k ℓ_i`. -/
theorem b1adrh_dist_le (H : HorizontalReference n k L) (i : H.cubeIndex) {y z : Spatial k}
    (hy : y ∈ H.cube i) (hz : z ∈ H.cube i) : dist y z ≤ √(k : ℝ) * b1adrh_side H i := by
  have hc : ∀ α, |y α - z α| ≤ b1adrh_side H i := fun α => by
    obtain ⟨hy1, hy2⟩ := (b1adrh_mem_cube H i y).1 hy α
    obtain ⟨hz1, hz2⟩ := (b1adrh_mem_cube H i z).1 hz α
    rw [abs_sub_le_iff]
    constructor <;> linarith
  rw [EuclideanSpace.dist_eq]
  calc √(∑ α, dist (y α) (z α) ^ 2) ≤ √(∑ _α : Fin k, b1adrh_side H i ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro α _
        rw [Real.dist_eq]
        exact pow_le_pow_left₀ (abs_nonneg _) (hc α) 2
    _ = √(k : ℝ) * b1adrh_side H i := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (b1adrh_side_pos H i).le]

theorem b1adrh_isBounded (H : HorizontalReference n k L) (i : H.cubeIndex) :
    Bornology.IsBounded (H.cube i) :=
  Metric.isBounded_iff.2 ⟨_, fun _ hy _ hz => b1adrh_dist_le H i hy hz⟩

theorem b1adrh_diam_le (H : HorizontalReference n k L) (i : H.cubeIndex) :
    Metric.diam (H.cube i) ≤ √(k : ℝ) * b1adrh_side H i :=
  Metric.diam_le_of_forall_dist_le
    (mul_nonneg (Real.sqrt_nonneg _) (b1adrh_side_pos H i).le)
    fun _ hy _ hz => b1adrh_dist_le H i hy hz

/-- `dist(Q_i, D) ≤ dist(y, D)` for `y ∈ Q_i`. -/
theorem b1adrh_setDist_le (H : HorizontalReference n k L) (i : H.cubeIndex) {y : Spatial k}
    (hy : y ∈ H.cube i) : setDist (H.cube i) H.domain ≤ Metric.infDist y H.domain := by
  unfold setDist
  exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact Metric.infDist_nonneg⟩ (⟨y, hy⟩ : H.cube i)

/-- Every base point lies in `D` or in exactly one face; here: in `D` or in some face. -/
theorem b1adrh_domain_or_face (H : HorizontalReference n k L) (v : Spatial k) :
    v ∈ H.domain ∨ ∃ i, v ∈ H.face i := by
  by_cases hv : v ∈ H.domain
  · exact Or.inl hv
  · right
    have h : v ∈ ⋃ i, H.face i := by
      rw [H.faces_cover]
      exact hv
    exact mem_iUnion.1 h

/-! ### The anchor bound -/

/-- **Anchors near a trace point**: for `u ∈ D` and `v ∈ Q_i` (the closed cube),
`|a_i - u| ≤ 3 |v - u|`. With `x ∈ Q_i` nearest to `D` and `|x - a_i| = dist(Q_i,D)`:
`dist(Q_i,D) ≤ dist(v,D) ≤ |v - u|`, `diam Q_i ≤ dist(Q_i,D)/4`, so
`|a_i - u| ≤ |a_i - x| + |x - v| + |v - u| ≤ (9/4)|v - u|`. -/
theorem b1adrh_anchor_dist_le (H : HorizontalReference n k L) {u v : Spatial k}
    (hu : u ∈ H.domain) (i : H.cubeIndex) (hv : v ∈ H.cube i) :
    dist (H.anchor i) u ≤ 3 * dist v u := by
  obtain ⟨x, hx, hxa⟩ := H.anchor_nearest i
  have h1 : setDist (H.cube i) H.domain ≤ Metric.infDist v H.domain := b1adrh_setDist_le H i hv
  have h2 : Metric.infDist v H.domain ≤ dist v u := Metric.infDist_le_dist_of_mem hu
  have h3 := H.whitney_lower i
  have h4 : dist x v ≤ Metric.diam (H.cube i) :=
    Metric.dist_le_diam_of_mem (b1adrh_isBounded H i) hx hv
  have h5 := dist_triangle (H.anchor i) x u
  have h6 := dist_triangle x v u
  rw [dist_comm (H.anchor i) x] at h5
  have h0 : 0 ≤ dist v u := dist_nonneg
  linarith

/-- The plateau height of a cube containing `v`, compared with the trace at `u ∈ D`:
`|τ(a_i) - τ(u)| ≤ 9 L² |v - u|²`. -/
theorem b1adrh_anchor_height_sub_le (H : HorizontalReference n k L) {u v : Spatial k}
    (hu : u ∈ H.domain) (i : H.cubeIndex) (hv : v ∈ H.cube i) :
    |H.height (H.anchor i) - H.height u| ≤ 9 * L ^ 2 * dist v u ^ 2 := by
  have h1 := H.height_trace (H.anchor i) (H.anchor_mem i) u hu
  have h2 := b1adrh_anchor_dist_le H hu i hv
  have h3 : dist (H.anchor i) u ^ 2 ≤ (3 * dist v u) ^ 2 := pow_le_pow_left₀ dist_nonneg h2 2
  calc |H.height (H.anchor i) - H.height u| ≤ L ^ 2 * dist (H.anchor i) u ^ 2 := h1
    _ ≤ L ^ 2 * (3 * dist v u) ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg L)
    _ = 9 * L ^ 2 * dist v u ^ 2 := by ring

/-- **The anchor bound**: for `u ∈ D` and every `v`, `|T v - τ u| ≤ 9 L² |v - u|²`. -/
theorem b1adrh_height_sub_le (H : HorizontalReference n k L) {u : Spatial k}
    (hu : u ∈ H.domain) (v : Spatial k) :
    |H.height v - H.height u| ≤ 9 * L ^ 2 * dist v u ^ 2 := by
  rcases b1adrh_domain_or_face H v with hv | ⟨i, hv⟩
  · have h1 := H.height_trace v hv u hu
    have h0 : 0 ≤ L ^ 2 * dist v u ^ 2 := by positivity
    linarith
  · rw [H.height_plateau i v hv]
    exact b1adrh_anchor_height_sub_le H hu i (H.face_subset_cube i hv)

/-! ### Measurability of `(F,T)` -/

/-- `τ = T|_D` is continuous on `D`: on the bounded `D`,
`|τ u - τ v| ≤ L² |u - v|² ≤ L² diam(D) |u - v|`. -/
theorem b1adrh_continuousOn_height (H : HorizontalReference n k L) :
    ContinuousOn H.height H.domain := by
  have hb := H.domain_compact.isBounded
  refine (LipschitzOnWith.of_dist_le' (K := L ^ 2 * Metric.diam H.domain) ?_).continuousOn
  intro a ha b hb'
  rw [Real.dist_eq]
  have hab : dist a b ≤ Metric.diam H.domain := Metric.dist_le_diam_of_mem hb ha hb'
  calc |H.height a - H.height b| ≤ L ^ 2 * dist a b ^ 2 := H.height_trace a ha b hb'
    _ = L ^ 2 * dist a b * dist a b := by ring
    _ ≤ L ^ 2 * Metric.diam H.domain * dist a b := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        exact mul_le_mul_of_nonneg_left hab (sq_nonneg L)

/-- The plateau function `T` is Borel: `T⁻¹ s = (D ∩ T⁻¹ s) ∪ ⋃_i (Φ_i ∩ T⁻¹ s)`, where the
first piece is relatively Borel in the closed `D` (continuity there) and each face piece is
`Φ_i` or empty. -/
theorem b1adrh_measurable_height (H : HorizontalReference n k L) : Measurable H.height := by
  intro s hs
  have hD : MeasurableSet (H.domain ∩ H.height ⁻¹' s) := by
    have hm : Measurable (H.domain.domRestrict H.height) :=
      (continuousOn_iff_continuous_domRestrict.1 (b1adrh_continuousOn_height H)).measurable
    have h := (MeasurableEmbedding.subtype_coe
      H.domain_compact.isClosed.measurableSet).measurableSet_image.2 (hm hs)
    rwa [Set.domRestrict_eq, Set.preimage_comp, Subtype.image_preimage_coe] at h
  have hF : ∀ i, MeasurableSet (H.face i ∩ H.height ⁻¹' s) := by
    intro i
    by_cases hi : H.height (H.anchor i) ∈ s
    · have he : H.face i ∩ H.height ⁻¹' s = H.face i := by
        apply inter_eq_left.2
        intro x hx
        rw [mem_preimage, H.height_plateau i x hx]
        exact hi
      rw [he]
      exact H.face_measurable i
    · have he : H.face i ∩ H.height ⁻¹' s = ∅ := by
        apply eq_empty_iff_forall_notMem.2
        rintro x ⟨hx, hxs⟩
        rw [mem_preimage, H.height_plateau i x hx] at hxs
        exact hi hxs
      rw [he]
      exact MeasurableSet.empty
  have heq : H.height ⁻¹' s =
      (H.domain ∩ H.height ⁻¹' s) ∪ ⋃ i, (H.face i ∩ H.height ⁻¹' s) := by
    ext x
    simp only [mem_union, mem_inter_iff, mem_iUnion]
    constructor
    · intro hx
      rcases b1adrh_domain_or_face H x with h | ⟨i, h⟩
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨i, h, hx⟩
    · rintro (⟨_, hx⟩ | ⟨i, _, hx⟩) <;> exact hx
  rw [heq]
  exact hD.union (MeasurableSet.iUnion hF)

/-- The map `(F,T)` is Borel. -/
theorem b1adrh_measurable_map (H : HorizontalReference n k L) : Measurable H.map := by
  have hT : Measurable (fun u => (Metric.Snowflaking.toSnowflaking (H.height u) : Time)) :=
    Metric.Snowflaking.continuous_toSnowflaking.measurable.comp (b1adrh_measurable_height H)
  exact (b1adrh_lipschitz H).continuous.measurable.prodMk hT

/-! ### Trace points -/

/-- **A base ball maps into the reference ball** at a trace point: for `u ∈ D` and `r > 0`,
`B(u, r/(3L)) ⊆ (F,T)⁻¹ P((F u, τ u), r)`, since `|F v - F u| ≤ L|v - u| < r/3` and
`|T v - τ u| ≤ 9 L² |v - u|² < r²`. -/
theorem b1adrh_ball_subset (H : HorizontalReference n k L) {u : Spatial k}
    (hu : u ∈ H.domain) {r : ℝ} (hr : 0 < r) :
    Metric.ball u (r / (3 * L)) ⊆ H.map ⁻¹' Metric.ball (H.map u) r := by
  have hL := b1adrh_L_pos H
  intro v hv
  rw [Metric.mem_ball, lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * L)] at hv
  have hd0 : 0 ≤ dist v u := dist_nonneg
  have hδ : 3 * L * dist v u < r := by linarith
  simp only [mem_preimage, HorizontalReference.map]
  rw [mem_ball_point _ _ _ _ _ hr]
  constructor
  · rw [← dist_eq_norm]
    calc dist (H.spatialMap v) (H.spatialMap u) ≤ L * dist v u := (H.spatialMap_bilipschitz v u).2
      _ < r := by nlinarith
  · have h0 : 0 ≤ 3 * L * dist v u := by positivity
    calc |H.height v - H.height u| ≤ 9 * L ^ 2 * dist v u ^ 2 := b1adrh_height_sub_le H hu v
      _ = (3 * L * dist v u) ^ 2 := by ring
      _ < r ^ 2 := pow_lt_pow_left₀ hδ h0 two_ne_zero

/-- **Trace points lie in the closed carrier**: for `u ∈ D`, `(F u, τ u) ∈ Γ = supp σ`. Every
neighbourhood contains a ball `P((F u, τ u), r)`, whose `σ`-measure is at least the volume of
`B(u, r/(3L))`. -/
theorem b1adrh_map_mem_carrier (H : HorizontalReference n k L) {u : Spatial k}
    (hu : u ∈ H.domain) : H.map u ∈ H.carrier := by
  have hL := b1adrh_L_pos H
  rw [HorizontalReference.carrier, Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hδ : 0 < r / (3 * L) := by positivity
  calc (0 : ℝ≥0∞) < volume (Metric.ball u (r / (3 * L))) := Metric.measure_ball_pos volume u hδ
    _ ≤ volume (H.map ⁻¹' Metric.ball (H.map u) r) := measure_mono (b1adrh_ball_subset H hu hr)
    _ ≤ H.measure (Metric.ball (H.map u) r) :=
        Measure.le_map_apply (b1adrh_measurable_map H).aemeasurable _
    _ ≤ H.measure U := measure_mono hrU

end ParabolicRectifiability.QuantitativeCharacterization

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.QuantitativeCharacterization

/-- **`b2_horizontalReference_map_mem_carrier`** (anchor bound): for every horizontal `L`-reference and every `u ∈ D`, the trace
point `(F(u), τ(u))` belongs to `Γ = supp σ`, `σ = (F,T)_# L^k`.

Route: `(F,T)` is Borel (`b1adrh_measurable_map`); the anchors give
`|T v - τ u| ≤ 9 L² |v - u|²` (`b1adrh_height_sub_le`); the base ball `B(u, r/(3L))` maps into
`P((F u, τ u), r)` (`b1adrh_ball_subset`), so every neighbourhood of the trace point has positive
`σ`-measure (`Measure.mem_support_iff_forall`). `0 < L` is derived from bi-Lipschitzness on
`ℝ^k`, `k ≥ 1`. No hypotheses. -/
theorem b2_horizontalReference_map_mem_carrier_proof :
    ∀ (n k : ℕ) (L : ℝ) (H : HorizontalReference n k L) (u : Spatial k),
      u ∈ H.domain → H.map u ∈ H.carrier :=
  fun _ _ _ H _ hu => b1adrh_map_mem_carrier H hu

end ParabolicRectifiability.Characterization
