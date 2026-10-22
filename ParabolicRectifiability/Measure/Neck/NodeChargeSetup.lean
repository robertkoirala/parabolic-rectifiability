import ParabolicRectifiability.Measure.Neck.ConstructionConclusions

/-!
# Node charge data of the source construction: construction-side helpers

Helpers (prefix `ms5_`) for `nodeChargeData_of_construction`.

* `ms5_card_le_of_separated`: a `ρ`-separated finite set inside a ball of radius `L ρ` has
  at most `(2L+1)^d` points, for a measure with `μ(B(z,t)) = c t^d`.
* `ms5_nodes`: the charged nodes, i.e. the centers of the continuing candidates of every
  stage `j ≥ 1`; the level-zero node set is empty (the artificial root is not charged).
* `ms5_model`, `ms5_fit_le`: the attained original-source fit of a node as a model of the
  admissible family, and the fit inequality with the natural beta number.
* `ms5_nodeError_subset`: the node error set lies in the union over the nodes of the parts
  of `P(g, r_j)` outside the `θ r_j`-tube of the node's fitted model.
* `ms5_vertical_card_le`, `ms5_horizontal_card_le`: same-level multiplicity of the incidence
  balls `P(g, r_j)` (vertical) and spatial balls `B(x_g, r_j)` (horizontal, using time
  compatibility of the occurrences with `γ ≤ 1/64`).
* `ms5_vertical_witness`, `ms5_horizontal_witness`: the incident-witness comparison with
  constant `2`.
* `ms5_nodeChargeData_of_incidence`: the charging data from incidence sets and reference
  measures with the stated properties.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-! ## Packing of separated points -/

/-- A `ρ`-separated finite set inside the open ball of radius `L ρ` about `x` has at most
`(2L+1)^d` points, if every open ball of radius `t > 0` has measure `c t^d` with
`0 < c < ∞`: the balls of radius `ρ/2` about the points are disjoint and lie in the ball of
radius `(2L+1) ρ/2` about `x`. -/
theorem ms5_card_le_of_separated {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) (c : ℝ≥0∞) (d : ℕ) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hball : ∀ (z : X) (t : ℝ), 0 < t → μ (Metric.ball z t) = c * ENNReal.ofReal t ^ d)
    (s : Finset X) (x : X) (L : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ρ ≤ dist a b)
    (hmem : ∀ a ∈ s, dist a x < L * ρ) : s.card ≤ (2 * L + 1) ^ d := by
  have hρ2 : 0 < ρ / 2 := half_pos hρ
  have hdisj : (s : Set X).PairwiseDisjoint (fun a => Metric.ball a (ρ / 2)) := by
    intro a ha b hb hab
    refine Set.disjoint_left.2 fun z hza hzb => ?_
    have h1 := hsep a ha b hb hab
    rw [Metric.mem_ball] at hza hzb
    have h2 : dist a b < ρ := by
      calc dist a b ≤ dist z a + dist z b := dist_triangle_left a b z
        _ < ρ / 2 + ρ / 2 := add_lt_add hza hzb
        _ = ρ := by ring
    linarith
  have hL : (0 : ℝ) < 2 * (L : ℝ) + 1 := by positivity
  have hR : 0 < (2 * (L : ℝ) + 1) * (ρ / 2) := mul_pos hL hρ2
  have hsub : (⋃ a ∈ s, Metric.ball a (ρ / 2)) ⊆
      Metric.ball x ((2 * (L : ℝ) + 1) * (ρ / 2)) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨a, ha, hza⟩ := hz
    rw [Metric.mem_ball] at hza ⊢
    calc dist z x ≤ dist z a + dist a x := dist_triangle z a x
      _ < ρ / 2 + L * ρ := add_lt_add hza (hmem a ha)
      _ = (2 * (L : ℝ) + 1) * (ρ / 2) := by ring
  have hb2 : ∀ z, μ (Metric.ball z (ρ / 2)) = c * ENNReal.ofReal (ρ / 2) ^ d :=
    fun z => hball z _ hρ2
  have hsum : μ (⋃ a ∈ s, Metric.ball a (ρ / 2)) =
      (s.card : ℝ≥0∞) * (c * ENNReal.ofReal (ρ / 2) ^ d) := by
    rw [measure_biUnion_finset hdisj (fun a _ => measurableSet_ball)]
    simp only [hb2, Finset.sum_const, nsmul_eq_mul]
  have hle := measure_mono (μ := μ) hsub
  rw [hsum, hball x _ hR, ENNReal.ofReal_mul hL.le, mul_pow] at hle
  have hne0 : c * ENNReal.ofReal (ρ / 2) ^ d ≠ 0 :=
    mul_ne_zero hc0 (pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ2).ne')
  have hnet : c * ENNReal.ofReal (ρ / 2) ^ d ≠ ∞ :=
    ENNReal.mul_ne_top hct (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hle' : (s.card : ℝ≥0∞) * (c * ENNReal.ofReal (ρ / 2) ^ d) ≤
      ENNReal.ofReal (2 * (L : ℝ) + 1) ^ d * (c * ENNReal.ofReal (ρ / 2) ^ d) := by
    calc (s.card : ℝ≥0∞) * (c * ENNReal.ofReal (ρ / 2) ^ d)
        ≤ c * (ENNReal.ofReal (2 * (L : ℝ) + 1) ^ d * ENNReal.ofReal (ρ / 2) ^ d) := hle
      _ = ENNReal.ofReal (2 * (L : ℝ) + 1) ^ d * (c * ENNReal.ofReal (ρ / 2) ^ d) := by ring
  have hcard := (ENNReal.mul_le_mul_iff_left hne0 hnet).1 hle'
  have hcast : ENNReal.ofReal (2 * (L : ℝ) + 1) ^ d = (((2 * L + 1) ^ d : ℕ) : ℝ≥0∞) := by
    rw [show (2 * (L : ℝ) + 1) = ((2 * L + 1 : ℕ) : ℝ) by norm_cast, ENNReal.ofReal_natCast]
    norm_cast
  rw [hcast] at hcard
  exact_mod_cast hcard

/-- Open Euclidean balls of positive radius have measure `c t^d`, `c = vol(B(0,1))`,
`d = dim`. -/
theorem ms5_spatial_ball (n : ℕ) (z : Spatial n) (t : ℝ) (ht : 0 < t) :
    (volume : Measure (Spatial n)) (Metric.ball z t) =
      volume (Metric.ball (0 : Spatial n) 1) * ENNReal.ofReal t ^ Module.finrank ℝ (Spatial n) := by
  rw [MeasureTheory.Measure.addHaar_ball_of_pos volume z ht, ENNReal.ofReal_pow ht.le, mul_comm]

/-- The parabolic distance in coordinates. -/
theorem ms5_dist_eq {n : ℕ} (g y : Space n) :
    dist g y = max ‖g.1 - y.1‖ (Real.sqrt |g.2.val - y.2.val|) := by
  obtain ⟨gx, gt⟩ := g
  obtain ⟨yx, yt⟩ := y
  cases gt
  cases yt
  exact dist_point gx yx _ _

/-! ## Facts about the construction -/

section Construction

variable {n k : ℕ} {T : NeckType}

open Classical in
theorem ms5_mem_contIndex {D : ConstructionData n k T} {P : SourceSetup n} {j i : ℕ} :
    i ∈ D.contIndex P j ↔ i < D.candCount j ∧ D.IsContinuing P j i := by
  unfold ConstructionData.contIndex
  rw [Finset.mem_filter, Finset.mem_range]

theorem ms5_family_index (D : ConstructionData n k T) (P : SourceSetup n) (hR : 0 < P.R)
    {j : ℕ} (hj : j ≠ 0) : (D.family P hR).index j = D.contIndex P j := by
  show (if j = 0 then {0} else D.contIndex P j) = D.contIndex P j
  exact ite_eq_right hj

theorem ms5_family_center (D : ConstructionData n k T) (P : SourceSetup n) (hR : 0 < P.R)
    {j : ℕ} (hj : j ≠ 0) (i : ℕ) : (D.family P hR).center j i = D.cand j i := by
  show (if j = 0 then D.rootCenter else D.cand j i) = D.cand j i
  exact ite_eq_right hj

/-- Every kept set lies in the source set `S`. -/
theorem ms5_kept_subset (D : ConstructionData n k T) (P : SourceSetup n) :
    ∀ j, D.kept P j ⊆ P.S
  | 0 => fun z hz => by
      change z ∈ D.tubeSet P at hz
      exact hz.1
  | j + 1 => by
      intro z hz
      change z ∈ D.stageKept P (j + 1) (D.kept P j) at hz
      simp only [ConstructionData.stageKept, Set.mem_iUnion] at hz
      obtain ⟨i, _, hz⟩ := hz
      have h1 : z ∈ D.parentPiece P (j + 1) (D.kept P j) i := hz.1
      have h2 : z ∈ D.afterColl P (j + 1) (D.kept P j) := h1.1
      have h3 : z ∈ D.afterTerm P (j + 1) (D.kept P j) := h2.1
      exact ms5_kept_subset D P j h3.1

/-- Candidates are source points. -/
theorem ms5_cand_mem_S {D : ConstructionData n k T} {P : SourceSetup n}
    (hD : D.IsSourceConstruction P) {j i : ℕ} (hj : 1 ≤ j) (hi : i < D.candCount j) :
    D.cand j i ∈ P.S :=
  ms5_kept_subset D P (j - 1) (hD.cand_mem j hj i hi).1

/-- Distinct candidate indices of one stage have distinct centers (net separation). -/
theorem ms5_cand_inj {D : ConstructionData n k T} {P : SourceSetup n} (hR : 0 < P.R)
    (hD : D.IsSourceConstruction P) {j i l : ℕ} (hj : 1 ≤ j) (hi : i < D.candCount j)
    (hl : l < D.candCount j) (h : D.cand j i = D.cand j l) : i = l := by
  by_contra hne
  have hsep := hD.cand_separated j hj i hi l hl hne
  rw [h, dist_self] at hsep
  have := mul_pos T.sourceSeparation_pos (P.scale_pos T hR j)
  linarith

open Classical in
/-- The charged nodes of level `j`: the centers of the continuing candidates of stage `j`
for `j ≥ 1`, and none at level `0` (the artificial root is not charged). -/
def ms5_nodes (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) : Finset (Space n) :=
  if j = 0 then ∅ else (D.contIndex P j).image (D.cand j)

theorem ms5_nodes_zero (D : ConstructionData n k T) (P : SourceSetup n) :
    ms5_nodes D P 0 = ∅ := by
  unfold ms5_nodes
  exact ite_eq_left rfl

open Classical in
theorem ms5_mem_nodes {D : ConstructionData n k T} {P : SourceSetup n} {j : ℕ} {g : Space n} :
    g ∈ ms5_nodes D P j ↔
      j ≠ 0 ∧ ∃ i, i < D.candCount j ∧ D.IsContinuing P j i ∧ D.cand j i = g := by
  unfold ms5_nodes
  by_cases hj : j = 0
  · simp [hj]
  · rw [ite_eq_right hj, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hj, i, (ms5_mem_contIndex.1 hi).1, (ms5_mem_contIndex.1 hi).2, rfl⟩
    · rintro ⟨-, i, hi, hc, rfl⟩
      exact ⟨i, ms5_mem_contIndex.2 ⟨hi, hc⟩, rfl⟩

open Classical in
/-- The candidate index of a node `g` of level `j`. -/
def ms5_nodeIndex (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) (g : Space n) : ℕ :=
  if h : ∃ i, i < D.candCount j ∧ D.IsContinuing P j i ∧ D.cand j i = g then h.choose else 0

theorem ms5_nodeIndex_spec {D : ConstructionData n k T} {P : SourceSetup n} {j : ℕ}
    {g : Space n} (hg : g ∈ ms5_nodes D P j) :
    ms5_nodeIndex D P j g < D.candCount j ∧ D.IsContinuing P j (ms5_nodeIndex D P j g) ∧
      D.cand j (ms5_nodeIndex D P j g) = g := by
  have h := (ms5_mem_nodes.1 hg).2
  unfold ms5_nodeIndex
  rw [dite_eq_left h]
  exact h.choose_spec

theorem ms5_nodeIndex_eq {D : ConstructionData n k T} {P : SourceSetup n} (hR : 0 < P.R)
    (hD : D.IsSourceConstruction P) {j i : ℕ} (hj : 1 ≤ j) (hi : i < D.candCount j)
    (hc : D.IsContinuing P j i) : ms5_nodeIndex D P j (D.cand j i) = i := by
  have hg : D.cand j i ∈ ms5_nodes D P j := ms5_mem_nodes.2 ⟨by omega, i, hi, hc, rfl⟩
  obtain ⟨h1, -, h3⟩ := ms5_nodeIndex_spec hg
  exact ms5_cand_inj hR hD hj h1 hi h3

/-- Nodes are source points. -/
theorem ms5_nodes_mem_S {D : ConstructionData n k T} {P : SourceSetup n}
    (hD : D.IsSourceConstruction P) {j : ℕ} {g : Space n} (hg : g ∈ ms5_nodes D P j) :
    g ∈ P.S := by
  obtain ⟨hj, i, hi, -, rfl⟩ := ms5_mem_nodes.1 hg
  exact ms5_cand_mem_S hD (Nat.one_le_iff_ne_zero.2 hj) hi

/-- The cutoff of a node is below the stage scale (the terminal phase is over). -/
theorem ms5_nodes_cutoff_lt {D : ConstructionData n k T} {P : SourceSetup n}
    (hD : D.IsSourceConstruction P) {j : ℕ} {g : Space n} (hg : g ∈ ms5_nodes D P j) :
    P.f g < coherentScale (T.rootRadius P.R) j := by
  obtain ⟨hj, i, hi, -, rfl⟩ := ms5_mem_nodes.1 hg
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hj
  exact hD.term_done j hj1 _ (hD.cand_mem j hj1 i hi)

end Construction

/-! ## Models and fits -/

/-- The model of the admissible family of type `T` with spatial plane `L` and (horizontal
case) time `τ`. -/
def ms5_model {n k : ℕ} : (T : NeckType) → T.Available n k → AffineSpatialPlane n (T.rank k) →
    ℝ → Models n k T.toFamilyKind
  | .horizontal, h, L, τ => (⟨(show 1 ≤ k ∧ k ≤ n from h).1, L, τ⟩ : HorizontalModel n k)
  | .vertical, h, L, _ =>
      (⟨k - 2, (show 2 ≤ k ∧ k ≤ n + 2 from h).1,
        Nat.sub_add_cancel (show 2 ≤ k ∧ k ≤ n + 2 from h).1, L⟩ : VerticalModel n k)

theorem ms5_modelSet_model {n k : ℕ} (T : NeckType) (h : T.Available n k)
    (L : AffineSpatialPlane n (T.rank k)) (τ : ℝ) :
    modelSet (ms5_model T h L τ) = T.lowerModelSet L τ := by
  cases T <;> rfl

/-- The attained fit of a candidate (`fit_minimal`) bounds its fit by the natural beta number:
`∫_{P(g,40r_j)} d_P(z, Π_g)² dν ≤ (40 r_j)^{k+2} b_ν(g, 40 r_j)`. -/
theorem ms5_fit_le {n k : ℕ} {T : NeckType} (hT : T.Available n k) {P : SourceSetup n}
    {D : ConstructionData n k T} (hR : 0 < P.R) (hD : D.IsSourceConstruction P) {j i : ℕ}
    (hj : 1 ≤ j) (hi : i < D.candCount j) :
    fit P.ν (ms5_model T hT (D.plane j i) (D.time j i)) (D.cand j i)
        (40 * coherentScale (T.rootRadius P.R) j) ≤
      ENNReal.ofReal ((40 * coherentScale (T.rootRadius P.R) j) ^ (k + 2)) *
        betaSq P.ν k T.toFamilyKind (D.cand j i) (40 * coherentScale (T.rootRadius P.R) j) := by
  have hr : 0 < 40 * coherentScale (T.rootRadius P.R) j :=
    mul_pos (by norm_num) (P.scale_pos T hR j)
  have hfit : fit P.ν (ms5_model T hT (D.plane j i) (D.time j i)) (D.cand j i)
        (40 * coherentScale (T.rootRadius P.R) j) =
      ∫⁻ z in Metric.ball (D.cand j i) (40 * P.scale T j),
        Metric.infEDist z (D.modelSet j i) ^ 2 ∂P.ν := by
    simp only [fit, modelCost, ms5_modelSet_model]
    try rfl
  rw [hfit, betaSq_of_pos _ _ _ _ hr, ← mul_assoc, ENNReal.ofReal_pow hr.le, ← mul_pow,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top, one_pow,
    one_mul]
  exact hD.fit_minimal j hj i hi

/-- The model attached to a node `g` of level `j`: the fitted model of its candidate. -/
def ms5_nodeModel {n k : ℕ} {T : NeckType} (hT : T.Available n k) (D : ConstructionData n k T)
    (P : SourceSetup n) (j : ℕ) (g : Space n) : Models n k T.toFamilyKind :=
  ms5_model T hT (D.plane j (ms5_nodeIndex D P j g)) (D.time j (ms5_nodeIndex D P j g))

/-- The error piece of a node: the part of `P(g, r_j)` outside the `θ r_j`-tube of its
fitted model. -/
def ms5_nodeErrorPiece {n k : ℕ} {T : NeckType} (hT : T.Available n k)
    (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) (g : Space n) : Set (Space n) :=
  Metric.ball g (coherentScale (T.rootRadius P.R) j) ∩
    {z | ENNReal.ofReal ((P.θ * coherentScale (T.rootRadius P.R) j) ^ 2) <
      modelCost (ms5_nodeModel hT D P j g) z}

/-- The node error set lies in the union of the node error pieces. -/
theorem ms5_nodeError_subset {n k : ℕ} {T : NeckType} (hT : T.Available n k)
    {P : SourceSetup n} {D : ConstructionData n k T} (hP : P.IsAdmissible)
    (hD : D.IsSourceConstruction P) :
    D.nodeErrorSet P ⊆ ⋃ j, ⋃ g ∈ ms5_nodes D P j, ms5_nodeErrorPiece hT D P j g := by
  intro z hz
  simp only [ConstructionData.nodeErrorSet, Set.mem_iUnion] at hz
  obtain ⟨j, hj, i, ⟨hi, hc⟩, hz⟩ := hz
  have hg : D.cand j i ∈ ms5_nodes D P j := ms5_mem_nodes.2 ⟨by omega, i, hi, hc, rfl⟩
  have hidx := ms5_nodeIndex_eq hP.R_pos hD hj hi hc
  have hr : 0 < coherentScale (T.rootRadius P.R) j := P.scale_pos T hP.R_pos j
  simp only [Set.mem_iUnion]
  refine ⟨j, D.cand j i, hg, ?_⟩
  unfold ms5_nodeErrorPiece
  refine Set.mem_inter ?_ ?_
  · have hpar : z ∈ D.parentPiece P j (D.entering P j) i := hz.1
    have hb : z ∈ Metric.ball (D.cand j i) (T.sourceSeparation * P.scale T j) := hpar.2.1
    exact Metric.ball_subset_ball (mul_le_of_le_one_left hr.le T.sourceSeparation_le_one) hb
  · rw [Set.mem_ofPred_eq]
    have hnk : ¬ (Metric.infEDist z (D.modelSet j i) ≤ ENNReal.ofReal (P.θ * P.scale T j)) :=
      fun h => hz.2 (Set.mem_inter hz.1 h)
    have hlt := not_le.1 hnk
    have hθr : 0 ≤ P.θ * coherentScale (T.rootRadius P.R) j :=
      mul_nonneg hP.θ_pos.le hr.le
    rw [ms5_nodeModel, hidx, modelCost, ms5_modelSet_model, ENNReal.ofReal_pow hθr]
    exact ENNReal.pow_lt_pow_left two_ne_zero hlt

/-! ## Multiplicity and witnesses -/

section Incidence

variable {n k : ℕ}

/-- Vertical same-level multiplicity: at most `3^{n+2}` nodes of one level have `x` in their
incidence ball `P(g, r_j)` (the nodes are `r_j`-separated). -/
theorem ms5_vertical_card_le (P : SourceSetup n) (D : ConstructionData n k .vertical)
    (hR : 0 < P.R) (hD : D.IsSourceConstruction P) (j : ℕ) (x : Space n)
    (s : Finset (Space n)) (hs : s ⊆ ms5_nodes D P j)
    (hx : ∀ g ∈ s, x ∈ Metric.ball g (coherentScale (NeckType.vertical.rootRadius P.R) j)) :
    s.card ≤ 3 ^ (n + 2) := by
  have hr : 0 < coherentScale (NeckType.vertical.rootRadius P.R) j := P.scale_pos _ hR j
  have hc0 : (2 * omega n : ℝ≥0∞) ≠ 0 := mul_ne_zero two_ne_zero (omega_pos n).ne'
  have hct : (2 * omega n : ℝ≥0∞) ≠ ∞ := ENNReal.mul_ne_top (by simp) (omega_lt_top n).ne
  have hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      coherentScale (NeckType.vertical.rootRadius P.R) j ≤ dist a b := by
    intro a ha b hb hab
    obtain ⟨hj, i, hi, -, rfl⟩ := ms5_mem_nodes.1 (hs ha)
    obtain ⟨-, l, hl, -, rfl⟩ := ms5_mem_nodes.1 (hs hb)
    have hil : i ≠ l := fun h => hab (h ▸ rfl)
    have h1 := hD.cand_separated j (Nat.one_le_iff_ne_zero.2 hj) i hi l hl hil
    have h2 : NeckType.vertical.sourceSeparation = 1 := rfl
    rw [h2, one_mul] at h1
    exact h1
  have hmem : ∀ a ∈ s,
      dist a x < ((1 : ℕ) : ℝ) * coherentScale (NeckType.vertical.rootRadius P.R) j := by
    intro a ha
    have h1 := hx a ha
    rw [Metric.mem_ball, dist_comm] at h1
    rw [Nat.cast_one, one_mul]
    exact h1
  have h := ms5_card_le_of_separated (parabolicVolume n) (2 * omega n) (n + 2) hc0 hct
    (fun z t ht => parabolicVolume_ball z t ht) s x 1 _ hr hsep hmem
  simpa using h

/-- Horizontal same-level spatial separation: two distinct nodes of one level have spatial
distance at least `r_j/4` when the occurrences are time compatible with `γ ≤ 1/64` (the
nodes are `r_j/4`-separated in the parabolic metric, and nearby nodes have close times). -/
theorem ms5_horizontal_sep (P : SourceSetup n) (D : ConstructionData n k .horizontal)
    (hR : 0 < P.R) (hD : D.IsSourceConstruction P) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 64)
    (htime : RecordsTimeCompatible (D.family P hR) (D.centers P) (D.radius P) γ) {j : ℕ}
    {g g' : Space n} (hg : g ∈ ms5_nodes D P j) (hg' : g' ∈ ms5_nodes D P j) (hne : g ≠ g') :
    coherentScale (NeckType.horizontal.rootRadius P.R) j / 4 ≤ dist g.1 g'.1 := by
  obtain ⟨hj, i, hi, hc, rfl⟩ := ms5_mem_nodes.1 hg
  obtain ⟨-, l, hl, hc', rfl⟩ := ms5_mem_nodes.1 hg'
  have hr : 0 < coherentScale (NeckType.horizontal.rootRadius P.R) j := P.scale_pos _ hR j
  have hil : i ≠ l := fun h => hne (h ▸ rfl)
  have hsep : 1 / 4 * coherentScale (NeckType.horizontal.rootRadius P.R) j ≤
      dist (D.cand j i) (D.cand j l) :=
    hD.cand_separated j (Nat.one_le_iff_ne_zero.2 hj) i hi l hl hil
  have hiF : i ∈ (D.family P hR).index j := by
    rw [ms5_family_index D P hR hj]
    exact ms5_mem_contIndex.2 ⟨hi, hc⟩
  have hlF : l ∈ (D.family P hR).index j := by
    rw [ms5_family_index D P hR hj]
    exact ms5_mem_contIndex.2 ⟨hl, hc'⟩
  have ht := htime (Sum.inl (j, i)) (Sum.inl (j, l)) hiF hlF
  change |((D.family P hR).center j i).2.val - ((D.family P hR).center j l).2.val| ≤
    γ * max (‖((D.family P hR).center j i).1 - ((D.family P hR).center j l).1‖ ^ 2)
      (max (coherentScale (NeckType.horizontal.rootRadius P.R) j ^ 2)
        (coherentScale (NeckType.horizontal.rootRadius P.R) j ^ 2)) at ht
  rw [ms5_family_center D P hR hj, ms5_family_center D P hR hj, max_self] at ht
  by_contra hlt
  rw [not_le, dist_eq_norm] at hlt
  have hn0 := norm_nonneg ((D.cand j i).1 - (D.cand j l).1)
  have hmax : max (‖(D.cand j i).1 - (D.cand j l).1‖ ^ 2)
      (coherentScale (NeckType.horizontal.rootRadius P.R) j ^ 2) ≤
      coherentScale (NeckType.horizontal.rootRadius P.R) j ^ 2 :=
    max_le (pow_le_pow_left₀ hn0 (by linarith) 2) le_rfl
  have htle : |(D.cand j i).2.val - (D.cand j l).2.val| ≤
      (coherentScale (NeckType.horizontal.rootRadius P.R) j / 8) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hmax hγ0
    have h2 : γ * coherentScale (NeckType.horizontal.rootRadius P.R) j ^ 2 ≤
        (coherentScale (NeckType.horizontal.rootRadius P.R) j / 8) ^ 2 :=
      calc γ * coherentScale (NeckType.horizontal.rootRadius P.R) j ^ 2
          ≤ 1 / 64 * coherentScale (NeckType.horizontal.rootRadius P.R) j ^ 2 :=
            mul_le_mul_of_nonneg_right hγ (sq_nonneg _)
        _ = (coherentScale (NeckType.horizontal.rootRadius P.R) j / 8) ^ 2 := by ring
    linarith
  have hsq : Real.sqrt |(D.cand j i).2.val - (D.cand j l).2.val| ≤
      coherentScale (NeckType.horizontal.rootRadius P.R) j / 8 := by
    calc Real.sqrt |(D.cand j i).2.val - (D.cand j l).2.val|
        ≤ Real.sqrt ((coherentScale (NeckType.horizontal.rootRadius P.R) j / 8) ^ 2) :=
          Real.sqrt_le_sqrt htle
      _ = coherentScale (NeckType.horizontal.rootRadius P.R) j / 8 :=
          Real.sqrt_sq (by positivity)
  rw [ms5_dist_eq] at hsep
  have hm : max ‖(D.cand j i).1 - (D.cand j l).1‖
      (Real.sqrt |(D.cand j i).2.val - (D.cand j l).2.val|) <
      1 / 4 * coherentScale (NeckType.horizontal.rootRadius P.R) j :=
    max_lt (by linarith) (by linarith)
  linarith

/-- Horizontal same-level multiplicity: at most `9^n` nodes of one level have the spatial
point `x` in their spatial incidence ball `B(x_g, r_j)`. -/
theorem ms5_horizontal_card_le (P : SourceSetup n) (D : ConstructionData n k .horizontal)
    (hR : 0 < P.R) (hD : D.IsSourceConstruction P) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 64)
    (htime : RecordsTimeCompatible (D.family P hR) (D.centers P) (D.radius P) γ) (j : ℕ)
    (x : Spatial n) (s : Finset (Space n)) (hs : s ⊆ ms5_nodes D P j)
    (hx : ∀ g ∈ s,
      x ∈ Metric.ball g.1 (coherentScale (NeckType.horizontal.rootRadius P.R) j)) :
    s.card ≤ 9 ^ n := by
  classical
  have hr : 0 < coherentScale (NeckType.horizontal.rootRadius P.R) j := P.scale_pos _ hR j
  have hsep : ∀ g ∈ s, ∀ g' ∈ s, g ≠ g' →
      coherentScale (NeckType.horizontal.rootRadius P.R) j / 4 ≤ dist g.1 g'.1 :=
    fun g hg g' hg' hne => ms5_horizontal_sep P D hR hD hγ0 hγ htime (hs hg) (hs hg') hne
  have hinj : Set.InjOn Prod.fst (s : Set (Space n)) := by
    intro g hg g' hg' heq
    by_contra hne
    have := hsep g hg g' hg' hne
    rw [heq, dist_self] at this
    linarith
  rw [← Finset.card_image_of_injOn hinj]
  have hc0 : volume (Metric.ball (0 : Spatial n) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 one_pos).ne'
  have hct : volume (Metric.ball (0 : Spatial n) 1) ≠ ∞ := MeasureTheory.measure_ball_ne_top
  have hsep' : ∀ a ∈ s.image Prod.fst, ∀ b ∈ s.image Prod.fst, a ≠ b →
      coherentScale (NeckType.horizontal.rootRadius P.R) j / 4 ≤ dist a b := by
    intro a ha b hb hab
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hb
    exact hsep g hg g' hg' (fun h => hab (h ▸ rfl))
  have hmem : ∀ a ∈ s.image Prod.fst, dist a x <
      ((4 : ℕ) : ℝ) * (coherentScale (NeckType.horizontal.rootRadius P.R) j / 4) := by
    intro a ha
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 ha
    have h1 := hx g hg
    rw [Metric.mem_ball, dist_comm] at h1
    calc dist g.1 x < coherentScale (NeckType.horizontal.rootRadius P.R) j := h1
      _ = ((4 : ℕ) : ℝ) * (coherentScale (NeckType.horizontal.rootRadius P.R) j / 4) := by
          push_cast
          ring
  have h := ms5_card_le_of_separated (volume : Measure (Spatial n))
    (volume (Metric.ball (0 : Spatial n) 1)) (Module.finrank ℝ (Spatial n)) hc0 hct
    (ms5_spatial_ball n) (s.image Prod.fst) x 4
    (coherentScale (NeckType.horizontal.rootRadius P.R) j / 4) (by positivity) hsep' hmem
  have hd : Module.finrank ℝ (Spatial n) = n := finrank_euclideanSpace_fin
  rw [hd] at h
  simpa using h

/-- Vertical incident witness: two incidence balls `P(g, r_j)` and `P(y, r_{j'})`,
`j ≤ j'`, containing one point give `d_P(g, y) ≤ 2 r_j`. -/
theorem ms5_vertical_witness {T : NeckType} (P : SourceSetup n) (hR : 0 < P.R) {x : Space n}
    {j j' : ℕ} (hjj : j ≤ j') {g y : Space n}
    (hg : x ∈ Metric.ball g (coherentScale (T.rootRadius P.R) j))
    (hy : x ∈ Metric.ball y (coherentScale (T.rootRadius P.R) j')) :
    dist g y ≤ 2 * coherentScale (T.rootRadius P.R) j := by
  rw [Metric.mem_ball] at hg hy
  have hanti := ChargeCollapse.coherentScale_anti (T.rootRadius_pos hR) hjj
  have := dist_triangle_left g y x
  linarith

/-- Horizontal incident witness: two spatial incidence balls `B(x_g, r_j)` and
`B(x_y, r_{j'})`, `j ≤ j'`, containing one spatial point give `d_P(g, y) ≤ 2 r_j`, by the
pairwise witness bridge with time compatibility, `γ ≤ 1`. -/
theorem ms5_horizontal_witness (P : SourceSetup n) (D : ConstructionData n k .horizontal)
    (hR : 0 < P.R) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (htime : RecordsTimeCompatible (D.family P hR) (D.centers P) (D.radius P) γ)
    {x : Spatial n} {j j' : ℕ} (hjj : j ≤ j') {g y : Space n} (hg : g ∈ ms5_nodes D P j)
    (hy : y ∈ ms5_nodes D P j')
    (hxg : x ∈ Metric.ball g.1 (coherentScale (NeckType.horizontal.rootRadius P.R) j))
    (hxy : x ∈ Metric.ball y.1 (coherentScale (NeckType.horizontal.rootRadius P.R) j')) :
    dist g y ≤ 2 * coherentScale (NeckType.horizontal.rootRadius P.R) j := by
  obtain ⟨hj, i, hi, hc, rfl⟩ := ms5_mem_nodes.1 hg
  obtain ⟨hj', l, hl, hc', rfl⟩ := ms5_mem_nodes.1 hy
  have hiF : i ∈ (D.family P hR).index j := by
    rw [ms5_family_index D P hR hj]
    exact ms5_mem_contIndex.2 ⟨hi, hc⟩
  have hlF : l ∈ (D.family P hR).index j' := by
    rw [ms5_family_index D P hR hj']
    exact ms5_mem_contIndex.2 ⟨hl, hc'⟩
  have hxa : dist x ((D.family P hR).center j i).1 < 1 * (D.family P hR).scale j := by
    rw [ms5_family_center D P hR hj, one_mul]
    exact hxg
  have hxb : dist x ((D.family P hR).center j' l).1 < 1 * (D.family P hR).scale j' := by
    rw [ms5_family_center D P hR hj', one_mul]
    exact hxy
  have h := (D.family P hR).horizontal_occurrence_witness hγ0 zero_le_one htime hjj hiF hlF
    hxa hxb
  rw [ms5_family_center D P hR hj, ms5_family_center D P hR hj'] at h
  have hs1 : Real.sqrt γ ≤ 1 := by
    have := Real.sqrt_le_sqrt hγ1
    rwa [Real.sqrt_one] at this
  have hmax : max (2 * (1 : ℝ)) (Real.sqrt γ * max (2 * 1) 1) ≤ 2 := by
    have h21 : max (2 * (1 : ℝ)) 1 = 2 := by norm_num
    rw [h21]
    exact max_le (by norm_num) (by linarith)
  have hr : 0 < coherentScale (NeckType.horizontal.rootRadius P.R) j := P.scale_pos _ hR j
  calc dist (D.cand j i) (D.cand j' l)
      ≤ max (2 * (1 : ℝ)) (Real.sqrt γ * max (2 * 1) 1) * (D.family P hR).scale j := h
    _ ≤ 2 * coherentScale (NeckType.horizontal.rootRadius P.R) j :=
        mul_le_mul_of_nonneg_right hmax hr.le

end Incidence

/-! ## Assembly of the charging data -/

open Classical in
/-- The charging data of a construction from incidence sets `E` on a measurable reference
space `X` and reference measures `ω N`, given Borel incidence sets, same-level multiplicity
`N₀`, the incident-witness comparison with constant `A`, total masses `≤ C_ω R^k` and lower
patch masses `≥ c₁ r_j^k` on the nodes. The nodes are `ms5_nodes` (none at level `0`), the
cutoff constant is any `F_c ≥ 1`, the models are the attained fits and the error pieces are
`ms5_nodeErrorPiece`. -/
theorem ms5_nodeChargeData_of_incidence {n k : ℕ} {T : NeckType} (P : SourceSetup n)
    (D : ConstructionData n k T) (hT : T.Available n k) (hP : P.IsAdmissible)
    (hD : D.IsSourceConstruction P) (Fc A Cω c₁ : ℝ) (N₀ : ℕ) (hFc : 1 ≤ Fc) {X : Type}
    [MeasurableSpace X] (E : ℕ → Space n → Set X) (ω : ℕ → Measure X)
    (hE : ∀ j, ∀ g ∈ ms5_nodes D P j, MeasurableSet (E j g))
    (hmult : ∀ (x : X) (j : ℕ), ((ms5_nodes D P j).filter fun g => x ∈ E j g).card ≤ N₀)
    (hwit : ∀ (x : X) (j : ℕ), ∀ g ∈ ms5_nodes D P j, x ∈ E j g → ∀ j', j ≤ j' →
      ∀ y ∈ ms5_nodes D P j', x ∈ E j' y → dist g y ≤ A * coherentScale (T.rootRadius P.R) j)
    (hω : ∀ N, ω N univ ≤ ENNReal.ofReal (Cω * P.R ^ k))
    (hlow : ∀ N, ∀ j ≤ N, ∀ g ∈ ms5_nodes D P j,
      ENNReal.ofReal (c₁ * coherentScale (T.rootRadius P.R) j ^ k) ≤ ω N (E j g)) :
    D.NodeChargeData P Fc A Cω c₁ N₀ := by
  unfold ConstructionData.NodeChargeData
  refine ⟨X, inferInstance, ms5_nodes D P, E, ω, ms5_nodeModel hT D P,
    ms5_nodeErrorPiece hT D P, ms5_nodes_zero D P, fun j g hg => ms5_nodes_mem_S hD hg,
    ?_, hE, hmult, hwit, hω, hlow, ?_, ?_, ?_, ?_, ms5_nodeError_subset hT hP hD⟩
  · intro j g hg
    have hr : 0 < coherentScale (T.rootRadius P.R) j := P.scale_pos T hP.R_pos j
    exact (ms5_nodes_cutoff_lt hD hg).le.trans (le_mul_of_one_le_left hr.le hFc)
  · intro j g hg
    obtain ⟨hj, i, hi, hc, rfl⟩ := ms5_mem_nodes.1 hg
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hj
    rw [ms5_nodeModel, ms5_nodeIndex_eq hP.R_pos hD hj1 hi hc]
    exact ms5_fit_le hT hP.R_pos hD hj1 hi
  · intro j g _
    exact measurableSet_ball.inter
      (measurableSet_lt measurable_const (measurable_modelCost _))
  · intro j g _
    exact Set.inter_subset_left
  · intro j g _ z hz
    exact ((Set.mem_inter_iff _ _ _).1 hz).2

end ParabolicRectifiability
