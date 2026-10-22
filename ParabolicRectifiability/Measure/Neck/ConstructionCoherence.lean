import ParabolicRectifiability.Measure.Neck.ConstructionEstimates

/-!
# Coherence, center heights and stopping parents of the source construction

Proofs of two auxiliary statements about the construction of a neck from a source, in
implication form: each takes the statement `planeComparison_sq_le` (plane comparison) as
the hypothesis `hcomp`.

* `coherent_of_construction_proof` (`coherent_of_construction`): every truncation
  of the constructed family is coherent with separation `T.sourceSeparation` (nets),
  stored parents within `r_j`, and root, same-level and adjacent comparisons at most `δ`
  for `δ ≥ C √(B/a)`.
* `centerHeight_stoppingParent_of_construction_proof` (`centerHeight_stoppingParent_of_construction`): center heights
  `dist(x_g, L_g) ≤ κ r_j` for `κ ≥ C (θ + √(B/a))`, and every stopping center has its
  preceding parent (or the initial plane) as stopping parent with tube tolerance `θ`.

`planeComparison_sq_le` bounds the squared comparisons by `C/a` times node betas and the global error,
which `nodeBeta_le_proof` bounds by `C B` and `C B R^{k+2}`; this is
`comparison_le_of_planeComparison_sq`. A candidate lies in the kept piece of its
preceding parent: within `κ r_{j-1} ≤ r_{j-1}` of the parent's center and within
`θ r_{j-1}` of its fitted model; the comparison transports this to its own plane.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal

/-! ## Spatial distances to planes -/

/-- The spatial part of the parabolic distance. -/
theorem ms2_norm_fst_sub_le_dist {n : ℕ} (z w : Space n) : ‖z.1 - w.1‖ ≤ dist z w := by
  rw [Prod.dist_eq, ← dist_eq_norm]
  exact le_max_left _ _

/-- A point within `ε` of a model set `L × {τ}` or `L × ℝ` is spatially within `ε` of `L`. -/
theorem infDist_spatial_le_of_infEDist_le {n m : ℕ} (T : NeckType)
    (L : AffineSpatialPlane n m) (τ : ℝ) {z : Space n} {ε : ℝ} (hε : 0 ≤ ε)
    (h : Metric.infEDist z (T.lowerModelSet L τ) ≤ ENNReal.ofReal ε) :
    Metric.infDist z.1 L.toSet ≤ ε := by
  have hle : Metric.infEDist z.1 L.toSet ≤ Metric.infEDist z (T.lowerModelSet L τ) := by
    refine Metric.le_infEDist.2 fun w hw => ?_
    have hw1 : w.1 ∈ L.toSet := by
      cases T
      · exact hw.1
      · exact hw
    calc Metric.infEDist z.1 L.toSet ≤ edist z.1 w.1 := Metric.infEDist_le_edist_of_mem hw1
      _ ≤ edist z w := by
          rw [Prod.edist_eq]
          exact le_max_left _ _
  exact ENNReal.toReal_le_of_le_ofReal hε (hle.trans h)

namespace AffineSpatialPlane

variable {n m : ℕ}

theorem norm_sub_projection_le_infDist (L : AffineSpatialPlane n m) (x : Spatial n) :
    ‖x - L.projection x‖ ≤ Metric.infDist x L.toSet :=
  (Metric.le_infDist L.nonempty).2 fun y hy => by
    rw [dist_eq_norm]
    exact L.nearest x hy

theorem ms2_infDist_le_infDist_add (L L' : AffineSpatialPlane n m) (x : Spatial n) :
    Metric.infDist x L'.toSet ≤ Metric.infDist x L.toSet + ‖L.projection x - L'.projection x‖ :=
  calc Metric.infDist x L'.toSet ≤ dist x (L'.projection x) :=
        Metric.infDist_le_dist_of_mem (L'.projection_mem x)
    _ = ‖x - L'.projection x‖ := dist_eq_norm _ _
    _ ≤ ‖x - L.projection x‖ + ‖L.projection x - L'.projection x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Metric.infDist x L.toSet + ‖L.projection x - L'.projection x‖ :=
        add_le_add (L.norm_sub_projection_le_infDist x) le_rfl

end AffineSpatialPlane

theorem planeComparison_nonneg {n m : ℕ} {x : Spatial n} {r : ℝ} (hr : 0 < r)
    (L L' : AffineSpatialPlane n m) : 0 ≤ planeComparison x r L L' :=
  add_nonneg (norm_nonneg _) (mul_nonneg (inv_nonneg.2 hr.le) (norm_nonneg _))

@[simp] theorem planeComparison_self {n m : ℕ} (x : Spatial n) (r : ℝ)
    (L : AffineSpatialPlane n m) : planeComparison x r L L = 0 := by
  simp [planeComparison]

/-- A plane comparison anchored at `x₀` controls the projections at every point within `r`
of the anchor. -/
theorem norm_projection_sub_le {n m : ℕ} {x₀ : Spatial n} {r : ℝ}
    {L L' : AffineSpatialPlane n m} (hr : 0 < r) (y : Spatial n) (hy : ‖y - x₀‖ ≤ r) :
    ‖L.projection y - L'.projection y‖ ≤ r * planeComparison x₀ r L L' := by
  have hid : L.projection y - L'.projection y =
      (L.projection x₀ - L'.projection x₀) +
        (L.linearProjection - L'.linearProjection) (y - x₀) := by
    simp only [AffineSpatialPlane.projection, sub_apply, map_sub]
    abel
  have hP : ‖(L.linearProjection - L'.linearProjection) (y - x₀)‖ ≤
      ‖L.linearProjection - L'.linearProjection‖ * r :=
    ((L.linearProjection - L'.linearProjection).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
  rw [hid]
  calc _ ≤ ‖L.projection x₀ - L'.projection x₀‖ +
        ‖(L.linearProjection - L'.linearProjection) (y - x₀)‖ := norm_add_le _ _
    _ ≤ ‖L.projection x₀ - L'.projection x₀‖ +
        ‖L.linearProjection - L'.linearProjection‖ * r := add_le_add le_rfl hP
    _ = r * planeComparison x₀ r L L' := by
        unfold planeComparison
        rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
        ring

/-- Transport of a spatial plane distance through a plane comparison. -/
theorem infDist_le_of_planeComparison {n m : ℕ} {x₀ y : Spatial n} {r e b : ℝ}
    {L L' : AffineSpatialPlane n m} (hr : 0 < r) (hy : ‖y - x₀‖ ≤ r)
    (hL' : Metric.infDist y L'.toSet ≤ e) (hpc : planeComparison x₀ r L L' ≤ b) :
    Metric.infDist y L.toSet ≤ e + r * b :=
  calc Metric.infDist y L.toSet
      ≤ Metric.infDist y L'.toSet + ‖L'.projection y - L.projection y‖ :=
        AffineSpatialPlane.ms2_infDist_le_infDist_add L' L y
    _ = Metric.infDist y L'.toSet + ‖L.projection y - L'.projection y‖ := by
        rw [norm_sub_rev]
    _ ≤ e + r * planeComparison x₀ r L L' := add_le_add hL' (norm_projection_sub_le hr y hy)
    _ ≤ e + r * b := add_le_add le_rfl (mul_le_mul_of_nonneg_left hpc hr.le)

namespace CoherentFamily

variable {n m : ℕ} {ι : Type*}

theorem isStoppingParent_some (F : CoherentFamily n m ι) (θ : ℝ) (c : Space n) (d : ℝ)
    (j : ℕ) (a : ι) :
    F.IsStoppingParent θ c d (some (j, a)) ↔ a ∈ F.index j ∧ dist c (F.center j a) ≤ F.scale j ∧
      Metric.infDist c.1 (F.plane j a).toSet ≤ θ * F.scale j ∧ F.scale j / 10 ≤ d :=
  Iff.rfl

theorem isStoppingParent_none (F : CoherentFamily n m ι) (θ : ℝ) (c : Space n) (d : ℝ) :
    F.IsStoppingParent θ c d none ↔
      Metric.infDist c.1 F.initialPlane.toSet ≤ θ * F.initialRadius ∧
        F.initialRadius / 10 ≤ d :=
  Iff.rfl

end CoherentFamily

/-! ## Scales -/

theorem NeckType.four_mul_le_rootRadius (T : NeckType) {R : ℝ} (hR : 0 ≤ R) :
    4 * R ≤ T.rootRadius R := by
  cases T
  · show 4 * R ≤ 8 * R
    linarith
  · show 4 * R ≤ 4 * R
    exact le_rfl

namespace SourceSetup

variable {n : ℕ}

theorem scale_zero (P : SourceSetup n) (T : NeckType) : P.scale T 0 = T.rootRadius P.R :=
  show T.rootRadius P.R / 10 ^ 0 = T.rootRadius P.R by rw [pow_zero, div_one]

theorem scale_succ (P : SourceSetup n) (T : NeckType) (j : ℕ) :
    P.scale T (j + 1) = P.scale T j / 10 :=
  show T.rootRadius P.R / 10 ^ (j + 1) = T.rootRadius P.R / 10 ^ j / 10 by
    rw [pow_succ, div_div]

end SourceSetup

/-! ## The constructed family -/

namespace ConstructionData

variable {n k : ℕ} {T : NeckType} {D : ConstructionData n k T} {P : SourceSetup n}
  {hR : 0 < P.R}

theorem family_index_zero : (D.family P hR).index 0 = {0} :=
  show (if (0 : ℕ) = 0 then ({0} : Finset ℕ) else D.contIndex P 0) = {0} from ite_eq_left rfl

theorem family_index_of_ne_zero {j : ℕ} (hj : j ≠ 0) :
    (D.family P hR).index j = D.contIndex P j :=
  show (if j = 0 then ({0} : Finset ℕ) else D.contIndex P j) = D.contIndex P j from ite_eq_right hj

theorem family_center_zero (a : ℕ) : (D.family P hR).center 0 a = D.rootCenter :=
  show (if (0 : ℕ) = 0 then D.rootCenter else D.cand 0 a) = D.rootCenter from ite_eq_left rfl

theorem family_center_of_ne_zero {j : ℕ} (hj : j ≠ 0) (a : ℕ) :
    (D.family P hR).center j a = D.cand j a :=
  show (if j = 0 then D.rootCenter else D.cand j a) = D.cand j a from ite_eq_right hj

theorem family_plane_zero (a : ℕ) : (D.family P hR).plane 0 a = D.rootPlane :=
  show (if (0 : ℕ) = 0 then D.rootPlane else D.plane 0 a) = D.rootPlane from ite_eq_left rfl

theorem family_plane_of_ne_zero {j : ℕ} (hj : j ≠ 0) (a : ℕ) :
    (D.family P hR).plane j a = D.plane j a :=
  show (if j = 0 then D.rootPlane else D.plane j a) = D.plane j a from ite_eq_right hj

theorem family_parent_of_le_one {j : ℕ} (hj : j ≤ 1) (a : ℕ) :
    (D.family P hR).parent j a = 0 :=
  show (if j ≤ 1 then 0 else D.parentIndex P (j - 1) a) = 0 from ite_eq_left hj

theorem family_parent_of_two_le {j : ℕ} (hj : 2 ≤ j) (a : ℕ) :
    (D.family P hR).parent j a = D.parentIndex P (j - 1) a :=
  show (if j ≤ 1 then 0 else D.parentIndex P (j - 1) a) = D.parentIndex P (j - 1) a from
    ite_eq_right (by omega)

theorem family_scale (j : ℕ) : (D.family P hR).scale j = P.scale T j := rfl

theorem family_initialPlane : (D.family P hR).initialPlane = D.rootPlane := rfl

theorem family_initialRadius : (D.family P hR).initialRadius = T.rootRadius P.R := rfl

theorem mem_contIndex {j i : ℕ} :
    i ∈ D.contIndex P j ↔ i < D.candCount j ∧ D.IsContinuing P j i := by
  simp only [contIndex, Finset.mem_filter, Finset.mem_range]

theorem entering_succ (j : ℕ) : D.entering P (j + 1) = D.kept P j := rfl

/-- A point of the kept piece of candidate `i` of stage `j` lies in the entering set,
within `r_j` of the candidate, and spatially within `θ r_j` of its fitted plane. -/
theorem mem_keptPiece_spec (hP : P.IsAdmissible) {j : ℕ} {E : Set (Space n)} {i : ℕ}
    {z : Space n} (h : z ∈ D.keptPiece P j E i) :
    z ∈ E ∧ dist z (D.cand j i) ≤ P.scale T j ∧
      Metric.infDist z.1 (D.plane j i).toSet ≤ P.θ * P.scale T j := by
  have hr := P.scale_pos T hP.R_pos j
  refine ⟨h.1.1.1.1, ?_, ?_⟩
  · have hb : z ∈ Metric.ball (D.cand j i) (T.sourceSeparation * P.scale T j) := h.1.2.1
    exact (Metric.mem_ball.1 hb).le.trans
      (mul_le_of_le_one_left hr.le T.sourceSeparation_le_one)
  · exact infDist_spatial_le_of_infEDist_le T (D.plane j i) (D.time j i)
      (mul_nonneg hP.θ_pos.le hr.le) h.2

/-- A point entering stage `j + 1 ≥ 2` lies in the kept piece of a continuing candidate
of stage `j`. -/
theorem exists_parent_of_mem_entering {j : ℕ} (hj : 1 ≤ j) {z : Space n}
    (hz : z ∈ D.entering P (j + 1)) :
    ∃ i, (i < D.candCount j ∧ D.IsContinuing P j i) ∧
      z ∈ D.keptPiece P j (D.entering P j) i := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [entering_succ, kept_succ] at hz
  simp only [stageKept, mem_iUnion] at hz
  obtain ⟨i, hi, hz⟩ := hz
  exact ⟨i, hi, by rwa [entering_succ]⟩

open Classical in
/-- The stored preceding parent of a candidate of stage `j + 1 ≥ 2`. -/
theorem parentIndex_spec (hD : D.IsSourceConstruction P) {j : ℕ} (hj : 1 ≤ j) {a : ℕ}
    (ha : a < D.candCount (j + 1)) :
    D.parentIndex P j a < D.candCount j ∧ D.IsContinuing P j (D.parentIndex P j a) ∧
      D.cand (j + 1) a ∈ D.keptPiece P j (D.entering P j) (D.parentIndex P j a) := by
  have hmem : D.cand (j + 1) a ∈ D.entering P (j + 1) :=
    (hD.cand_mem (j + 1) (by omega) a ha).1
  obtain ⟨i, hi, hz⟩ := exists_parent_of_mem_entering hj hmem
  have hex : ∃ i, i < D.candCount j ∧ D.IsContinuing P j i ∧
      D.cand (j + 1) a ∈ D.keptPiece P j (D.entering P j) i := ⟨i, hi.1, hi.2, hz⟩
  unfold parentIndex
  split
  · rename_i h
    exact Nat.find_spec h
  · contradiction

/-- A candidate of any stage is within `r_0` of the artificial root. -/
theorem dist_cand_root_le (hP : P.IsAdmissible) (hD : D.IsSourceConstruction P) {j i : ℕ}
    (hj : 1 ≤ j) (hi : i < D.candCount j) : dist (D.cand j i) D.rootCenter ≤ P.scale T 0 := by
  have hgS := (cand_mem_S_and_cutoff_lt hD hj hi).1
  have h1 : dist (D.cand j i) P.q < P.R := Metric.mem_ball.1 (hP.S_subset hgS)
  have h2 : dist D.rootCenter P.q ≤ P.R := hD.root_dist
  have h3 := T.four_mul_le_rootRadius hP.R_pos.le
  rw [SourceSetup.scale_zero]
  calc dist (D.cand j i) D.rootCenter ≤ dist (D.cand j i) P.q + dist D.rootCenter P.q :=
        dist_triangle_right _ _ _
    _ ≤ T.rootRadius P.R := by linarith [hP.R_pos]

open Classical in
/-- The stage of a stopping center: it is positive, the center enters it, and its radius is
at least the stage scale. -/
theorem stopStage_spec (hP : P.IsAdmissible) (hD : D.IsSourceConstruction P) {c : Space n}
    (hc : 0 < D.radius P c) :
    1 ≤ D.stopStage P c ∧ c ∈ D.entering P (D.stopStage P c) ∧
      P.scale T (D.stopStage P c) ≤ D.radius P c := by
  by_cases hT : D.IsTermCenter c
  · have hst : D.stopStage P c = Classical.choose hT := dite_eq_left hT
    have hrad : D.radius P c = P.f c := ite_eq_left hT
    obtain ⟨hj, i, hi, hci⟩ := Classical.choose_spec hT
    rw [hst, hrad]
    refine ⟨hj, ?_, ?_⟩
    · have h := (hD.term_mem _ hj i hi).1
      rwa [hci] at h
    · have h := hD.term_large _ hj i hi
      rwa [hci] at h
  · by_cases hC : D.IsCollCenter P c
    · have hst : D.stopStage P c = Classical.choose hC := by
        rw [stopStage, dite_eq_right hT]
        exact dite_eq_left hC
      have hrad : D.radius P c = 5 * P.scale T (Classical.choose hC) := by
        rw [radius, ite_eq_right hT, ite_eq_left hC, collStage, dite_eq_left hC]
      obtain ⟨hj, i, hi, -, hci, -⟩ := Classical.choose_spec hC
      rw [hst, hrad]
      refine ⟨hj, ?_, ?_⟩
      · have h := (hD.cand_mem _ hj i hi).1
        rwa [hci] at h
      · have h := P.scale_pos T hP.R_pos (Classical.choose hC)
        linarith
    · exfalso
      have hrad : D.radius P c = 0 := by rw [radius, ite_eq_right hT, ite_eq_right hC]
      linarith

open Classical in
/-- The stopping parent of a stopping center: the continuing candidate of
the preceding stage whose kept piece contains it, or the initial plane at stage one. -/
theorem isStoppingParent_of_construction (hP : P.IsAdmissible) (hD : D.IsSourceConstruction P)
    {c : Space n} (hc : 0 < D.radius P c) :
    (D.family P hP.R_pos).IsStoppingParent P.θ c (D.radius P c) (D.stoppingParent P c) := by
  obtain ⟨hs1, hsE, hsr⟩ := stopStage_spec hP hD hc
  have hθ := hP.θ_pos
  have hR := hP.R_pos
  by_cases h : 2 ≤ D.stopStage P c ∧ ∃ i, i < D.candCount (D.stopStage P c - 1) ∧
      D.IsContinuing P (D.stopStage P c - 1) i ∧
      c ∈ D.keptPiece P (D.stopStage P c - 1) (D.entering P (D.stopStage P c - 1)) i
  · have hsp : D.stoppingParent P c = some (D.stopStage P c - 1, Nat.find h.2) := dite_eq_left h
    obtain ⟨h1, h2, h3⟩ := Nat.find_spec h.2
    have hne : D.stopStage P c - 1 ≠ 0 := by omega
    obtain ⟨-, hdist, hinf⟩ := mem_keptPiece_spec hP h3
    have hscale : P.scale T (D.stopStage P c - 1) / 10 = P.scale T (D.stopStage P c) := by
      have h' := P.scale_succ T (D.stopStage P c - 1)
      rw [Nat.sub_add_cancel hs1] at h'
      exact h'.symm
    rw [hsp, CoherentFamily.isStoppingParent_some, family_index_of_ne_zero hne,
      family_center_of_ne_zero hne, family_plane_of_ne_zero hne, family_scale]
    exact ⟨mem_contIndex.2 ⟨h1, h2⟩, hdist, hinf, by rw [hscale]; exact hsr⟩
  · have hsp : D.stoppingParent P c = none := dite_eq_right h
    have hs : D.stopStage P c = 1 := by
      by_contra hne
      apply h
      refine ⟨by omega, ?_⟩
      have hE : c ∈ D.entering P (D.stopStage P c - 1 + 1) := by
        rwa [Nat.sub_add_cancel hs1]
      obtain ⟨i, hi, hz⟩ := exists_parent_of_mem_entering (by omega) hE
      exact ⟨i, hi.1, hi.2, hz⟩
    rw [hs] at hsE hsr
    have htube : c ∈ D.tubeSet P := hsE
    have hinf : Metric.infDist c.1 D.rootPlane.toSet ≤ P.θ * P.R :=
      infDist_spatial_le_of_infEDist_le T D.rootPlane D.rootTime
        (mul_nonneg hθ.le hR.le) htube.2
    have h4 := T.four_mul_le_rootRadius hR.le
    rw [hsp, CoherentFamily.isStoppingParent_none, family_initialPlane, family_initialRadius]
    refine ⟨hinf.trans (mul_le_mul_of_nonneg_left (by linarith) hθ.le), ?_⟩
    have h1 : P.scale T 1 = T.rootRadius P.R / 10 := by
      rw [P.scale_succ T 0, SourceSetup.scale_zero]
    rw [← h1]
    exact hsr

/-- A continuing candidate of stage one is within `10 (θ + b) r_1` of its plane, if `b`
bounds its root comparison. -/
theorem infDist_cand_one_le (hP : P.IsAdmissible) (hD : D.IsSourceConstruction P) {b : ℝ}
    {a : ℕ} (ha : a ∈ D.contIndex P 1)
    (hb : planeComparison D.rootCenter.1 (P.scale T 0) (D.plane 1 a) D.rootPlane ≤ b) :
    Metric.infDist (D.cand 1 a).1 (D.plane 1 a).toSet ≤ 10 * (P.θ + b) * P.scale T 1 := by
  have hR := hP.R_pos
  have hr0 := P.scale_pos T hR 0
  have hai := (mem_contIndex.1 ha).1
  have hgE : D.cand 1 a ∈ D.tubeSet P := (hD.cand_mem 1 le_rfl a hai).1
  have hinf : Metric.infDist (D.cand 1 a).1 D.rootPlane.toSet ≤ P.θ * P.R :=
    infDist_spatial_le_of_infEDist_le T D.rootPlane D.rootTime
      (mul_nonneg hP.θ_pos.le hR.le) hgE.2
  have hdist : ‖(D.cand 1 a).1 - D.rootCenter.1‖ ≤ P.scale T 0 :=
    (ms2_norm_fst_sub_le_dist _ _).trans (dist_cand_root_le hP hD le_rfl hai)
  have h := infDist_le_of_planeComparison hr0 hdist hinf hb
  have h0 : P.scale T 0 = 10 * P.scale T 1 := by
    rw [P.scale_succ T 0]
    ring
  have hRs : P.R ≤ P.scale T 0 := by
    rw [SourceSetup.scale_zero]
    linarith [T.four_mul_le_rootRadius hR.le]
  calc Metric.infDist (D.cand 1 a).1 (D.plane 1 a).toSet ≤ P.θ * P.R + P.scale T 0 * b := h
    _ ≤ P.θ * P.scale T 0 + P.scale T 0 * b :=
        add_le_add (mul_le_mul_of_nonneg_left hRs hP.θ_pos.le) le_rfl
    _ = 10 * (P.θ + b) * P.scale T 1 := by
        rw [h0]
        ring

/-- A continuing candidate of stage `j + 1 ≥ 2` is within `10 (θ + b) r_{j+1}` of its plane,
if `b` bounds its adjacent comparisons. -/
theorem infDist_cand_succ_le (hP : P.IsAdmissible) (hD : D.IsSourceConstruction P) {j : ℕ}
    (hj : 1 ≤ j) {a : ℕ} (ha : a ∈ D.contIndex P (j + 1)) {b : ℝ}
    (hb : ∀ l ∈ D.contIndex P j, dist (D.cand (j + 1) a) (D.cand j l) ≤ 20 * P.scale T j →
      planeComparison (D.cand j l).1 (P.scale T j) (D.plane (j + 1) a) (D.plane j l) ≤ b) :
    Metric.infDist (D.cand (j + 1) a).1 (D.plane (j + 1) a).toSet ≤
      10 * (P.θ + b) * P.scale T (j + 1) := by
  obtain ⟨hpi, hpc, hpk⟩ := parentIndex_spec hD hj (mem_contIndex.1 ha).1
  obtain ⟨-, hdist, hinf⟩ := mem_keptPiece_spec hP hpk
  have hr := P.scale_pos T hP.R_pos j
  have hpb := hb (D.parentIndex P j a) (mem_contIndex.2 ⟨hpi, hpc⟩) (by linarith)
  have h := infDist_le_of_planeComparison hr ((ms2_norm_fst_sub_le_dist _ _).trans hdist) hinf hpb
  have h0 : P.scale T j = 10 * P.scale T (j + 1) := by
    rw [P.scale_succ T j]
    ring
  calc Metric.infDist (D.cand (j + 1) a).1 (D.plane (j + 1) a).toSet
      ≤ P.θ * P.scale T j + P.scale T j * b := h
    _ = 10 * (P.θ + b) * P.scale T (j + 1) := by
        rw [h0]
        ring

end ConstructionData

/-! ## The comparisons from `planeComparison_sq_le` -/

/-- The plane comparisons of `planeComparison_sq_le`, with `nodeBeta_le_proof`, are at most `K √(B/a)`. -/
theorem comparison_le_of_planeComparison_sq (n : ℕ)
    (hcomp : ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
      (D : ConstructionData n k T),
      T.Available n k → k < n + 2 → P.IsAdmissible → D.IsSourceConstruction P →
      (∀ j, 1 ≤ j → ∀ i ∈ D.contIndex P j, ∀ l ∈ D.contIndex P j,
        dist (D.cand j i) (D.cand j l) ≤ 20 * P.scale T j →
        ENNReal.ofReal
            (planeComparison (D.cand j i).1 (P.scale T j) (D.plane j i) (D.plane j l) ^ 2) ≤
          ENNReal.ofReal (C / P.a) *
            (betaSq P.ν k T.toFamilyKind (D.cand j i) (40 * P.scale T j) +
              betaSq P.ν k T.toFamilyKind (D.cand j l) (40 * P.scale T j))) ∧
      (∀ j, 1 ≤ j → ∀ i ∈ D.contIndex P (j + 1), ∀ l ∈ D.contIndex P j,
        dist (D.cand (j + 1) i) (D.cand j l) ≤ 20 * P.scale T j →
        ENNReal.ofReal
            (planeComparison (D.cand j l).1 (P.scale T j) (D.plane (j + 1) i) (D.plane j l) ^ 2) ≤
          ENNReal.ofReal (C / P.a) *
            (betaSq P.ν k T.toFamilyKind (D.cand (j + 1) i) (40 * P.scale T (j + 1)) +
              ENNReal.ofReal (10 ^ (k + 2)) *
                betaSq P.ν k T.toFamilyKind (D.cand j l) (40 * P.scale T j))) ∧
      (∀ i ∈ D.contIndex P 1,
        ENNReal.ofReal (planeComparison D.rootCenter.1 (P.scale T 0) (D.plane 1 i) D.rootPlane ^ 2) ≤
          ENNReal.ofReal (C / P.a) *
            (betaSq P.ν k T.toFamilyKind (D.cand 1 i) (40 * P.scale T 1) +
              ENNReal.ofReal ((P.scale T 0)⁻¹ ^ (k + 2)) *
                ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν))) :
    ∃ K : ℝ, 0 < K ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T)
      (B : ℝ), T.Available n k → k < n + 2 → P.IsAdmissible → 0 < B → P.TailBound k T B →
      D.IsSourceConstruction P →
      (∀ j, 1 ≤ j → ∀ i ∈ D.contIndex P j, ∀ l ∈ D.contIndex P j,
        dist (D.cand j i) (D.cand j l) ≤ 20 * P.scale T j →
        planeComparison (D.cand j i).1 (P.scale T j) (D.plane j i) (D.plane j l) ≤
          K * Real.sqrt (B / P.a)) ∧
      (∀ j, 1 ≤ j → ∀ i ∈ D.contIndex P (j + 1), ∀ l ∈ D.contIndex P j,
        dist (D.cand (j + 1) i) (D.cand j l) ≤ 20 * P.scale T j →
        planeComparison (D.cand j l).1 (P.scale T j) (D.plane (j + 1) i) (D.plane j l) ≤
          K * Real.sqrt (B / P.a)) ∧
      (∀ i ∈ D.contIndex P 1,
        planeComparison D.rootCenter.1 (P.scale T 0) (D.plane 1 i) D.rootPlane ≤
          K * Real.sqrt (B / P.a)) := by
  obtain ⟨C₈, hC₈, h₈⟩ := hcomp
  obtain ⟨C₇, hC₇, h₇⟩ := nodeBeta_le_proof n
  set M : ℝ := C₈ * C₇ * (2 + 10 ^ (n + 3)) with hM
  have hM0 : 0 < M := by
    rw [hM]
    positivity
  refine ⟨Real.sqrt M, Real.sqrt_pos.2 hM0, ?_⟩
  intro k T P D B hT hk hP hB htail hD
  obtain ⟨hβ, hI⟩ := h₇ P D B hT hk hP hB htail hD
  obtain ⟨h₁, h₂, h₃⟩ := h₈ P D hT hk hP hD
  have ha := hP.a_pos
  have hR := hP.R_pos
  have hc : 0 ≤ C₈ / P.a := div_nonneg hC₈.le ha.le
  have hu : 0 ≤ C₇ * B := mul_nonneg hC₇.le hB.le
  have h10 : (0 : ℝ) ≤ 10 ^ (n + 3) := by positivity
  have hconv : ∀ x : ℝ, 0 ≤ x → ∀ X Y : ℝ≥0∞, ∀ v : ℝ, 0 ≤ v →
      v ≤ (1 + 10 ^ (n + 3)) * (C₇ * B) → X ≤ ENNReal.ofReal (C₇ * B) →
      Y ≤ ENNReal.ofReal v → ENNReal.ofReal (x ^ 2) ≤ ENNReal.ofReal (C₈ / P.a) * (X + Y) →
      x ≤ Real.sqrt M * Real.sqrt (B / P.a) := by
    intro x hx X Y v hv hvle hX hY h
    have h' : ENNReal.ofReal (x ^ 2) ≤ ENNReal.ofReal (C₈ / P.a * (C₇ * B + v)) := by
      refine h.trans ?_
      rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_add hu hv]
      exact mul_le_mul' le_rfl (add_le_add hX hY)
    have hsum : C₇ * B + v ≤ C₇ * B * (2 + 10 ^ (n + 3)) := by linarith
    have hsq : x ^ 2 ≤ M * (B / P.a) := by
      refine ((ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h').trans ?_
      calc C₈ / P.a * (C₇ * B + v) ≤ C₈ / P.a * (C₇ * B * (2 + 10 ^ (n + 3))) :=
            mul_le_mul_of_nonneg_left hsum hc
        _ = M * (B / P.a) := by
            rw [hM]
            ring
    rw [← Real.sqrt_mul hM0.le]
    calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
      _ ≤ Real.sqrt (M * (B / P.a)) := Real.sqrt_le_sqrt hsq
  have hle1 : C₇ * B ≤ (1 + 10 ^ (n + 3)) * (C₇ * B) := by nlinarith
  refine ⟨fun j hj i hi l hl hdist => ?_, fun j hj i hi l hl hdist => ?_, fun i hi => ?_⟩
  · exact hconv _ (planeComparison_nonneg (P.scale_pos T hR j) _ _) _ _ (C₇ * B) hu hle1
      (hβ j hj i (ConstructionData.mem_contIndex.1 hi).1)
      (hβ j hj l (ConstructionData.mem_contIndex.1 hl).1) (h₁ j hj i hi l hl hdist)
  · have hpow : (10 : ℝ) ^ (k + 2) ≤ 10 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hp0 : (0 : ℝ) ≤ 10 ^ (k + 2) := by positivity
    refine hconv _ (planeComparison_nonneg (P.scale_pos T hR j) _ _) _ _
      (10 ^ (k + 2) * (C₇ * B)) (mul_nonneg hp0 hu) ?_
      (hβ (j + 1) (by omega) i (ConstructionData.mem_contIndex.1 hi).1) ?_
      (h₂ j hj i hi l hl hdist)
    · nlinarith
    · rw [ENNReal.ofReal_mul hp0]
      exact mul_le_mul' le_rfl (hβ j hj l (ConstructionData.mem_contIndex.1 hl).1)
  · have hr0 := P.scale_pos T hR 0
    have hRs : P.R ≤ P.scale T 0 := by
      rw [SourceSetup.scale_zero]
      linarith [T.four_mul_le_rootRadius hR.le]
    have hq : (P.scale T 0)⁻¹ ^ (k + 2) * (C₇ * B * P.R ^ (k + 2)) =
        C₇ * B * (P.R / P.scale T 0) ^ (k + 2) := by
      rw [div_pow, inv_pow]
      ring
    have hle : (P.R / P.scale T 0) ^ (k + 2) ≤ 1 :=
      pow_le_one₀ (div_nonneg hR.le hr0.le) (div_le_one_of_le₀ hRs hr0.le)
    have hp0 : (0 : ℝ) ≤ (P.scale T 0)⁻¹ ^ (k + 2) := by positivity
    have hv0 : 0 ≤ (P.scale T 0)⁻¹ ^ (k + 2) * (C₇ * B * P.R ^ (k + 2)) := by positivity
    refine hconv _ (planeComparison_nonneg hr0 _ _) _ _
      ((P.scale T 0)⁻¹ ^ (k + 2) * (C₇ * B * P.R ^ (k + 2))) hv0 ?_
      (hβ 1 le_rfl i (ConstructionData.mem_contIndex.1 hi).1) ?_ (h₃ i hi)
    · rw [hq]
      have : C₇ * B * (P.R / P.scale T 0) ^ (k + 2) ≤ C₇ * B :=
        mul_le_of_le_one_right hu hle
      linarith
    · rw [ENNReal.ofReal_mul hp0]
      exact mul_le_mul' le_rfl hI

/-! ## The statements -/

/-- **`coherent_of_construction`**, in implication form: the statement
`planeComparison_sq_le` (hypothesis `hcomp`) implies coherence of the construction. -/
theorem coherent_of_construction_proof (n : ℕ)
    (hcomp : ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
      (D : ConstructionData n k T),
      T.Available n k → k < n + 2 → P.IsAdmissible → D.IsSourceConstruction P →
      (∀ j, 1 ≤ j → ∀ i ∈ D.contIndex P j, ∀ l ∈ D.contIndex P j,
        dist (D.cand j i) (D.cand j l) ≤ 20 * P.scale T j →
        ENNReal.ofReal
            (planeComparison (D.cand j i).1 (P.scale T j) (D.plane j i) (D.plane j l) ^ 2) ≤
          ENNReal.ofReal (C / P.a) *
            (betaSq P.ν k T.toFamilyKind (D.cand j i) (40 * P.scale T j) +
              betaSq P.ν k T.toFamilyKind (D.cand j l) (40 * P.scale T j))) ∧
      (∀ j, 1 ≤ j → ∀ i ∈ D.contIndex P (j + 1), ∀ l ∈ D.contIndex P j,
        dist (D.cand (j + 1) i) (D.cand j l) ≤ 20 * P.scale T j →
        ENNReal.ofReal
            (planeComparison (D.cand j l).1 (P.scale T j) (D.plane (j + 1) i) (D.plane j l) ^ 2) ≤
          ENNReal.ofReal (C / P.a) *
            (betaSq P.ν k T.toFamilyKind (D.cand (j + 1) i) (40 * P.scale T (j + 1)) +
              ENNReal.ofReal (10 ^ (k + 2)) *
                betaSq P.ν k T.toFamilyKind (D.cand j l) (40 * P.scale T j))) ∧
      (∀ i ∈ D.contIndex P 1,
        ENNReal.ofReal (planeComparison D.rootCenter.1 (P.scale T 0) (D.plane 1 i) D.rootPlane ^ 2) ≤
          ENNReal.ofReal (C / P.a) *
            (betaSq P.ν k T.toFamilyKind (D.cand 1 i) (40 * P.scale T 1) +
              ENNReal.ofReal ((P.scale T 0)⁻¹ ^ (k + 2)) *
                ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T)
      (B : ℝ), T.Available n k → k < n + 2 → ∀ hP : P.IsAdmissible, 0 < B →
      P.TailBound k T B → D.IsSourceConstruction P → ∀ δ : ℝ, C * Real.sqrt (B / P.a) ≤ δ →
      ∀ N : ℕ, (D.family P hP.R_pos).IsCoherentUpTo T.sourceSeparation δ N := by
  obtain ⟨K, hK, hcmp⟩ := comparison_le_of_planeComparison_sq n hcomp
  refine ⟨K, hK, ?_⟩
  intro k T P D B hT hk hP hB htail hD δ hδ N
  obtain ⟨hsame, hadj, hroot⟩ := hcmp P D B hT hk hP hB htail hD
  have hδ0 : 0 ≤ δ := le_trans (mul_nonneg hK.le (Real.sqrt_nonneg _)) hδ
  open ConstructionData in
  refine
    { separated := ?_
      parent_mem := ?_
      parent_dist := ?_
      root := ?_
      same := ?_
      adjacent := ?_ }
  · intro j _ a ha b hb hab
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [family_index_zero, Finset.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab
    · have hne : j ≠ 0 := hj.ne'
      rw [family_index_of_ne_zero hne] at ha hb
      rw [family_center_of_ne_zero hne, family_center_of_ne_zero hne, family_scale]
      exact hD.cand_separated j hj a (mem_contIndex.1 ha).1 b (mem_contIndex.1 hb).1 hab
  · intro j _ a ha
    rw [family_index_of_ne_zero (Nat.succ_ne_zero j)] at ha
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [family_parent_of_le_one (j := 0 + 1) le_rfl, family_index_zero]
      exact Finset.mem_singleton_self 0
    · rw [family_parent_of_two_le (j := j + 1) (by omega), Nat.add_sub_cancel,
        family_index_of_ne_zero hj.ne']
      obtain ⟨h1, h2, -⟩ := parentIndex_spec hD hj (mem_contIndex.1 ha).1
      exact mem_contIndex.2 ⟨h1, h2⟩
  · intro j _ a ha
    have hne : j + 1 ≠ 0 := Nat.succ_ne_zero j
    rw [family_index_of_ne_zero hne] at ha
    have hai := (mem_contIndex.1 ha).1
    rw [family_center_of_ne_zero hne, family_scale]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [family_parent_of_le_one (j := 0 + 1) le_rfl, family_center_zero]
      exact dist_cand_root_le hP hD (by norm_num) hai
    · rw [family_parent_of_two_le (j := j + 1) (by omega), Nat.add_sub_cancel,
        family_center_of_ne_zero hj.ne']
      obtain ⟨-, -, hpk⟩ := parentIndex_spec hD hj hai
      exact (mem_keptPiece_spec hP hpk).2.1
  · intro a _
    rw [family_plane_zero, family_initialPlane, planeComparison_self]
    exact hδ0
  · intro j _ a ha b hb hdist
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [family_plane_zero, family_plane_zero, planeComparison_self]
      exact hδ0
    · have hne : j ≠ 0 := hj.ne'
      rw [family_index_of_ne_zero hne] at ha hb
      rw [family_center_of_ne_zero hne, family_center_of_ne_zero hne, family_scale] at hdist
      rw [family_center_of_ne_zero hne, family_plane_of_ne_zero hne,
        family_plane_of_ne_zero hne, family_scale]
      exact (hsame j hj a ha b hb hdist).trans hδ
  · intro j _ a ha b hb hdist
    have hne : j + 1 ≠ 0 := Nat.succ_ne_zero j
    rw [family_index_of_ne_zero hne] at ha
    rw [family_plane_of_ne_zero hne, family_scale]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [family_index_zero, Finset.mem_singleton] at hb
      subst hb
      rw [family_center_zero, family_plane_zero]
      exact (hroot a ha).trans hδ
    · have hne' : j ≠ 0 := hj.ne'
      rw [family_index_of_ne_zero hne'] at hb
      rw [family_center_of_ne_zero hne, family_center_of_ne_zero hne', family_scale] at hdist
      rw [family_center_of_ne_zero hne', family_plane_of_ne_zero hne']
      exact (hadj j hj a ha b hb hdist).trans hδ

/-- **`centerHeight_stoppingParent_of_construction`**, in implication form: the statement
`planeComparison_sq_le` (hypothesis `hcomp`) implies the center-height and stopping-parent
bounds. -/
theorem centerHeight_stoppingParent_of_construction_proof (n : ℕ)
    (hcomp : ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
      (D : ConstructionData n k T),
      T.Available n k → k < n + 2 → P.IsAdmissible → D.IsSourceConstruction P →
      (∀ j, 1 ≤ j → ∀ i ∈ D.contIndex P j, ∀ l ∈ D.contIndex P j,
        dist (D.cand j i) (D.cand j l) ≤ 20 * P.scale T j →
        ENNReal.ofReal
            (planeComparison (D.cand j i).1 (P.scale T j) (D.plane j i) (D.plane j l) ^ 2) ≤
          ENNReal.ofReal (C / P.a) *
            (betaSq P.ν k T.toFamilyKind (D.cand j i) (40 * P.scale T j) +
              betaSq P.ν k T.toFamilyKind (D.cand j l) (40 * P.scale T j))) ∧
      (∀ j, 1 ≤ j → ∀ i ∈ D.contIndex P (j + 1), ∀ l ∈ D.contIndex P j,
        dist (D.cand (j + 1) i) (D.cand j l) ≤ 20 * P.scale T j →
        ENNReal.ofReal
            (planeComparison (D.cand j l).1 (P.scale T j) (D.plane (j + 1) i) (D.plane j l) ^ 2) ≤
          ENNReal.ofReal (C / P.a) *
            (betaSq P.ν k T.toFamilyKind (D.cand (j + 1) i) (40 * P.scale T (j + 1)) +
              ENNReal.ofReal (10 ^ (k + 2)) *
                betaSq P.ν k T.toFamilyKind (D.cand j l) (40 * P.scale T j))) ∧
      (∀ i ∈ D.contIndex P 1,
        ENNReal.ofReal (planeComparison D.rootCenter.1 (P.scale T 0) (D.plane 1 i) D.rootPlane ^ 2) ≤
          ENNReal.ofReal (C / P.a) *
            (betaSq P.ν k T.toFamilyKind (D.cand 1 i) (40 * P.scale T 1) +
              ENNReal.ofReal ((P.scale T 0)⁻¹ ^ (k + 2)) *
                ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T)
      (B : ℝ), T.Available n k → k < n + 2 → ∀ hP : P.IsAdmissible, 0 < B →
      P.TailBound k T B → D.IsSourceConstruction P →
      (∀ κ : ℝ, C * (P.θ + Real.sqrt (B / P.a)) ≤ κ → (D.family P hP.R_pos).HasCenterHeight κ) ∧
      ∀ c ∈ D.centers P, 0 < D.radius P c →
        (D.family P hP.R_pos).IsStoppingParent P.θ c (D.radius P c) (D.stoppingParent P c) := by
  obtain ⟨K, hK, hcmp⟩ := comparison_le_of_planeComparison_sq n hcomp
  refine ⟨10 * (1 + K), by positivity, ?_⟩
  intro k T P D B hT hk hP hB htail hD
  obtain ⟨-, hadj, hroot⟩ := hcmp P D B hT hk hP hB htail hD
  refine ⟨fun κ hκ => ?_, fun c _ hc => ConstructionData.isStoppingParent_of_construction hP hD hc⟩
  have hθ := hP.θ_pos
  have hR := hP.R_pos
  have hsq := Real.sqrt_nonneg (B / P.a)
  have hκ' : 10 * (P.θ + K * Real.sqrt (B / P.a)) ≤ κ := by nlinarith
  have hκ0 : 0 ≤ κ := by nlinarith
  intro j a ha
  open ConstructionData in
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [family_center_zero, family_plane_zero, Metric.infDist_zero_of_mem hD.root_mem]
    exact mul_nonneg hκ0 (P.scale_pos T hR 0).le
  · have hne : j ≠ 0 := hj.ne'
    rw [family_index_of_ne_zero hne] at ha
    rw [family_center_of_ne_zero hne, family_plane_of_ne_zero hne, family_scale]
    have hrj := P.scale_pos T hR j
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · obtain rfl : j = 1 := by omega
      exact (infDist_cand_one_le hP hD ha (hroot a ha)).trans
        (mul_le_mul_of_nonneg_right hκ' hrj.le)
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact (infDist_cand_succ_le hP hD (by omega) ha (hadj j (by omega) a ha)).trans
        (mul_le_mul_of_nonneg_right hκ' hrj.le)

end ParabolicRectifiability
