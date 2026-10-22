import ParabolicRectifiability.Measure.Neck.PlaneTime.PlaneComparison
import ParabolicRectifiability.Metric.Measure

/-!
# The finite comparison-incidence bound of the construction

Proof of `ambientSquare_finite_of_construction`.

Fix a truncation level `N` and a reference point `w` (in `X` for vertical, in `ℝ^n` for
horizontal necks). Level zero of the family is the artificial root with the initial plane,
so `E_0(w) = 0`. For `j ≥ 0`, `E_{j+1}(w)` is the larger of the same-level comparisons at
level `j` and the adjacent comparisons between levels `j + 1` and `j`, among centers within
`12 r_j` of `w`; every such center of level `i` is in the incident set
`I_i(w) = {g_{i,a} : dist(g_{i,a}, w) ≤ 120 r_i}` (`12 r_j = 120 r_{j+1}`). Plane comparison
(`planeComparison_sq_le_proof`) bounds the square of each comparison by
`C/a` times the betas of the two incident centers (with `10^{k+2}` for the coarser one), and
the level-one comparisons with the root add the global error once. In the horizontal case,
the time compatibility of the records with `0 ≤ γ ≤ 1` converts a spatial distance at most
`20 s` into a parabolic one, and the pairwise witness bridge
`CoherentFamily.horizontal_occurrence_witness` gives `d_P(g, y) ≤ 242 r_j` for incident
centers of levels `j ≤ J`; in the vertical case this is the triangle inequality. These give
the dimensional incidence multiplicity `1937^{n+2}` (ambient volume of disjoint balls) and the
deepest-witness hypothesis of the last-witness bound (`ChargeCollapse.lastWitness_sum`, taken as a
hypothesis), so `∑_{j ≤ N} E_j(w)^2 ≤ C B/a`. The global error is
bounded by `nodeBeta_le`, taken as a hypothesis.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-! ## Elementary facts -/

theorem ms3_iSup_sq_le {ι : Sort*} {f : ι → ℝ≥0∞} {X : ℝ≥0∞} (h : ∀ i, f i ^ 2 ≤ X) :
    (⨆ i, f i) ^ 2 ≤ X := by
  rw [sq, ENNReal.iSup_mul]
  refine iSup_le fun i => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun j => ?_
  rcases le_total (f i) (f j) with hij | hij
  · calc f i * f j ≤ f j * f j := by gcongr
      _ = f j ^ 2 := (sq _).symm
      _ ≤ X := h j
  · calc f i * f j ≤ f i * f i := by gcongr
      _ = f i ^ 2 := (sq _).symm
      _ ≤ X := h i

theorem ms3_mul_le_mul_left {a b c : ℝ≥0∞} (h : b ≤ c) : a * b ≤ a * c := by
  gcongr

theorem ms3_mul_le_mul_right {a b c : ℝ≥0∞} (h : a ≤ b) : a * c ≤ b * c := by
  gcongr

theorem ms3_max_sq_le {a b X : ℝ≥0∞} (ha : a ^ 2 ≤ X) (hb : b ^ 2 ≤ X) :
    max a b ^ 2 ≤ X := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    exact hb
  · rw [max_eq_left h]
    exact ha

theorem ms3_ofReal_sq_le {x : ℝ} {X : ℝ≥0∞} (hx : 0 ≤ x) (h : ENNReal.ofReal (x ^ 2) ≤ X) :
    ENNReal.ofReal x ^ 2 ≤ X := by
  rwa [← ENNReal.ofReal_pow hx]

theorem ms3_planeComparison_nonneg {n m : ℕ} (x : Spatial n) {r : ℝ} (hr : 0 ≤ r)
    (L L' : AffineSpatialPlane n m) : 0 ≤ planeComparison x r L L' :=
  affineComparison_nonneg L L' x hr

theorem ms3_planeComparison_self {n m : ℕ} (x : Spatial n) (r : ℝ)
    (L : AffineSpatialPlane n m) : planeComparison x r L L = 0 := by
  simp [planeComparison]

theorem NeckType.ms3_quarter_le_sourceSeparation (T : NeckType) :
    1 / 4 ≤ T.sourceSeparation := by
  cases T
  · show (1 / 4 : ℝ) ≤ 1 / 4
    exact le_rfl
  · show (1 / 4 : ℝ) ≤ 1
    norm_num

/-- A `ρ`-separated finite subset of a closed parabolic ball of radius `R` has at most
`((2R + ρ)/ρ)^{n+2}` points (ambient volume of disjoint balls). The proof is that of
`card_le_of_separated_subset_closedBall`. -/
theorem ms3_card_le_of_separated {n : ℕ} (c : Space n) {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ)
    (F : Finset (Space n)) (hF : ↑F ⊆ Metric.closedBall c R)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ρ ≤ dist x y) :
    (F.card : ℝ) ≤ ((2 * R + ρ) / ρ) ^ (n + 2) := by
  have hρ2 : 0 < ρ / 2 := half_pos hρ
  have hdisj : (F : Set (Space n)).PairwiseDisjoint (fun x => Metric.ball x (ρ / 2)) := by
    intro x hx y hy hxy
    exact Metric.ball_disjoint_ball (by linarith [hsep x hx y hy hxy])
  have hsub : (⋃ x ∈ F, Metric.ball x (ρ / 2)) ⊆ Metric.ball c (R + ρ / 2) := by
    intro w hw
    obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.mp hw
    have h1 : dist x c ≤ R := hF hx
    have h2 : dist w x < ρ / 2 := hwx
    rw [Metric.mem_ball]
    linarith [dist_triangle w x c]
  have hvol := measure_biUnion_finset (μ := parabolicVolume n) hdisj
    (fun x _ => measurableSet_ball)
  have hle : ∑ x ∈ F, parabolicVolume n (Metric.ball x (ρ / 2)) ≤
      parabolicVolume n (Metric.ball c (R + ρ / 2)) := by
    rw [← hvol]
    exact measure_mono hsub
  simp only [parabolicVolume_ball _ _ hρ2, Finset.sum_const, nsmul_eq_mul,
    parabolicVolume_ball _ _ (by linarith : (0 : ℝ) < R + ρ / 2)] at hle
  have hfin : 2 * omega n * ENNReal.ofReal (R + ρ / 2) ^ (n + 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (omega_lt_top n).ne)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have h3 := ENNReal.toReal_mono hfin hle
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ2.le,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ R + ρ / 2), ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat] at h3
  have hω : 0 < (omega n).toReal := ENNReal.toReal_pos (omega_pos n).ne' (omega_lt_top n).ne
  have hx : 0 < (ρ / 2) ^ (n + 2) := pow_pos hρ2 _
  have h4 : (2 * (omega n).toReal) * ((F.card : ℝ) * (ρ / 2) ^ (n + 2)) ≤
      (2 * (omega n).toReal) * (R + ρ / 2) ^ (n + 2) := by
    calc (2 * (omega n).toReal) * ((F.card : ℝ) * (ρ / 2) ^ (n + 2))
        = (F.card : ℝ) * (2 * (omega n).toReal * (ρ / 2) ^ (n + 2)) := by ring
      _ ≤ _ := h3
  have h5 := le_of_mul_le_mul_left h4 (mul_pos two_pos hω)
  have he : (2 * R + ρ) / ρ = (R + ρ / 2) / (ρ / 2) := by
    rw [div_eq_div_iff hρ.ne' hρ2.ne']
    ring
  rw [he, div_pow, le_div_iff₀ hx]
  exact h5

/-- The deepest-witness selection of `incidentWitness_sum_le`, with the last-witness bound
`lastWitness_sum` replaced by the hypothesis `hLW` of the same type. -/
theorem ms3_incidentWitness_sum_le
    (hLW : ∀ {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ)
      (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
      (_htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
      (r₀ : ℝ) (_hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n)) (N₀ : ℕ)
      (_hcard : ∀ j ≤ N, (I j).card ≤ N₀) (J : ℕ) (_hJ : J ≤ N)
      (_hdeep : ∀ j, J < j → j ≤ N → I j = ∅) (y : Space n) (_hyI : y ∈ I J) (_hyS : y ∈ S)
      (Fc : ℝ) (_hfy : f y ≤ Fc * coherentScale r₀ J) (A : ℝ)
      (_hA : ∀ j ≤ J, ∀ g ∈ I j, dist g y ≤ A * coherentScale r₀ j)
      (c H : ℝ) (_hc : 0 < c) (_hH₁ : Fc ≤ H) (_hH₂ : A + c ≤ H),
      ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) ≤
        ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B))
    {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ)
    (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n)) (N₀ : ℕ)
    (hcard : ∀ j ≤ N, (I j).card ≤ N₀) (hS : ∀ j ≤ N, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j ≤ N, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (A : ℝ)
    (hwit : ∀ j ≤ N, ∀ g ∈ I j, ∀ j', j ≤ j' → j' ≤ N → ∀ y ∈ I j',
      dist g y ≤ A * coherentScale r₀ j)
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : A + c ≤ H) :
    ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) := by
  classical
  by_cases hne : ∃ j ∈ Finset.range (N + 1), (I j).Nonempty
  · obtain ⟨J, hJL, hJmax⟩ : ∃ J ∈ (Finset.range (N + 1)).filter (fun j => (I j).Nonempty),
        ∀ j ∈ (Finset.range (N + 1)).filter (fun j => (I j).Nonempty), j ≤ J := by
      have hLne : ((Finset.range (N + 1)).filter (fun j => (I j).Nonempty)).Nonempty := by
        obtain ⟨j, hj, hjn⟩ := hne
        exact ⟨j, Finset.mem_filter.mpr ⟨hj, hjn⟩⟩
      exact ⟨_, Finset.max'_mem _ hLne, fun j hj => Finset.le_max' _ j hj⟩
    obtain ⟨hJr, y, hy⟩ := Finset.mem_filter.mp hJL
    have hJN : J ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hJr)
    have hdeep : ∀ j, J < j → j ≤ N → I j = ∅ := by
      intro j hJj hjN
      by_contra hne'
      have hj : j ∈ (Finset.range (N + 1)).filter (fun j => (I j).Nonempty) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hjN),
          Finset.nonempty_iff_ne_empty.mpr hne'⟩
      exact absurd (hJmax j hj) (not_le.mpr hJj)
    exact hLW μ k F S f B htail r₀ hr₀ N I N₀ hcard J hJN hdeep y hy
      (hS J hJN y hy) Fc (hf J hJN y hy) A
      (fun j hjJ g hg => hwit j (hjJ.trans hJN) g hg J hjJ hJN y hy) c H hc hH₁ hH₂
  · have hzero : ∀ j ∈ Finset.range (N + 1),
        ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) = 0 := by
      intro j hj
      rw [Finset.not_nonempty_iff_eq_empty.mp (fun h => hne ⟨j, hj, h⟩), Finset.sum_empty]
    rw [Finset.sum_eq_zero hzero]
    exact zero_le

/-! ## Incident candidates -/

namespace ConstructionData

variable {n k : ℕ} {T : NeckType} {W : Type*} [PseudoMetricSpace W]
  (D : ConstructionData n k T) (P : SourceSetup n) (pos : Space n → W) (w : W)

open Classical in
/-- The candidates of level `j ≥ 1` incident to `w`: within `120 r_j` of `w` for the
distance determined by `pos`. Level zero (the artificial root) has none. -/
def ms3_incident (j : ℕ) : Finset (Space n) :=
  if j = 0 then ∅ else
    ((D.contIndex P j).filter
      (fun a => dist (pos (D.cand j a)) w ≤ 120 * P.scale T j)).image (D.cand j)

theorem ms3_cand_mem_incident {j a : ℕ} (hj : j ≠ 0) (ha : a ∈ D.contIndex P j)
    (hw : dist (pos (D.cand j a)) w ≤ 120 * P.scale T j) :
    D.cand j a ∈ D.ms3_incident P pos w j := by
  classical
  unfold ms3_incident
  rw [ite_eq_right hj]
  exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨ha, hw⟩)

theorem ms3_of_mem_incident {j : ℕ} {g : Space n} (hg : g ∈ D.ms3_incident P pos w j) :
    j ≠ 0 ∧ ∃ a ∈ D.contIndex P j, dist (pos (D.cand j a)) w ≤ 120 * P.scale T j ∧
      D.cand j a = g := by
  classical
  unfold ms3_incident at hg
  by_cases hj : j = 0
  · rw [ite_eq_left hj] at hg
    exact absurd hg (Finset.notMem_empty g)
  · rw [ite_eq_right hj] at hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    exact ⟨hj, a, ha1, ha2, rfl⟩

end ConstructionData

/-! ## The generic finite square bound -/

/-- **The finite square bound for one reference point**, for any choice of distance `pos`
satisfying the two incidence hypotheses (`hpos20`: `pos`-distance at most `20 s` between
occurrences of scales at most `s` gives parabolic distance at most `20 s`; `hwit`: two
candidates of levels `j ≤ J` incident to `w` are within `242 r_j`). -/
theorem ConstructionData.ms3_squareBound_generic {n k : ℕ} {T : NeckType} {W : Type*}
    [PseudoMetricSpace W] (pos : Space n → W) (P : SourceSetup n) (D : ConstructionData n k T)
    (B : ℝ) (hT : T.Available n k) (hk : k < n + 2) (hP : P.IsAdmissible) (hB : 0 < B)
    (htail : P.TailBound k T B) (hD : D.IsSourceConstruction P) {Cβ : ℝ} (hCβ : 0 < Cβ)
    (hglob : ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν ≤
      ENNReal.ofReal (Cβ * B * P.R ^ (k + 2)))
    (hLW : ∀ {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ)
      (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
      (_htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
      (r₀ : ℝ) (_hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n)) (N₀ : ℕ)
      (_hcard : ∀ j ≤ N, (I j).card ≤ N₀) (J : ℕ) (_hJ : J ≤ N)
      (_hdeep : ∀ j, J < j → j ≤ N → I j = ∅) (y : Space n) (_hyI : y ∈ I J) (_hyS : y ∈ S)
      (Fc : ℝ) (_hfy : f y ≤ Fc * coherentScale r₀ J) (A : ℝ)
      (_hA : ∀ j ≤ J, ∀ g ∈ I j, dist g y ≤ A * coherentScale r₀ j)
      (c H : ℝ) (_hc : 0 < c) (_hH₁ : Fc ≤ H) (_hH₂ : A + c ≤ H),
      ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) ≤
        ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B))
    (hpos20 : ∀ i j a b (s : ℝ), a ∈ D.contIndex P i → b ∈ D.contIndex P j → 1 ≤ i →
      1 ≤ j → P.scale T i ≤ s → P.scale T j ≤ s →
      dist (pos (D.cand i a)) (pos (D.cand j b)) ≤ 20 * s →
      dist (D.cand i a) (D.cand j b) ≤ 20 * s)
    (w : W)
    (hwit : ∀ j J a b, 1 ≤ j → j ≤ J → a ∈ D.contIndex P j → b ∈ D.contIndex P J →
      dist (pos (D.cand j a)) w ≤ 120 * P.scale T j →
      dist (pos (D.cand J b)) w ≤ 120 * P.scale T J →
      dist (D.cand j a) (D.cand J b) ≤ 242 * P.scale T j)
    (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), (D.family P hP.R_pos).comparisonEnergy pos j w ^ 2 ≤
      ENNReal.ofReal (20000 * 8 ^ (n + 3) * (4 * 10 ^ (n + 3) *
        (((1937 ^ (n + 2) : ℕ) : ℝ) / Real.log 2 * 15 ^ (n + 3)) + Cβ) * (B / P.a)) := by
  classical
  have := P.finite
  have ha := hP.a_pos
  have hRpos := hP.R_pos
  obtain ⟨h8₁, h8₂, h8₃⟩ := ms3_planeComparison_explicit n P D hT hk hP hD
  set c8 : ℝ≥0∞ := ENNReal.ofReal (20000 * 8 ^ (n + 3) / P.a) with hc8
  set d : ℝ≥0∞ := ENNReal.ofReal (2 * 10 ^ (k + 2)) with hd
  set Root : ℝ≥0∞ := ENNReal.ofReal ((P.scale T 0)⁻¹ ^ (k + 2)) *
    ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν with hRoot
  set I := D.ms3_incident P pos w with hI
  set S : ℕ → ℝ≥0∞ := fun j => ∑ g ∈ I j, betaSq P.ν k T.toFamilyKind g (40 * P.scale T j)
    with hS
  have hbeta_le : ∀ j, ∀ g ∈ I j, betaSq P.ν k T.toFamilyKind g (40 * P.scale T j) ≤ S j :=
    fun j g hg => Finset.single_le_sum (f := fun g => betaSq P.ν k T.toFamilyKind g
      (40 * P.scale T j)) (fun _ _ => zero_le) hg
  have hd1 : (1 : ℝ≥0∞) ≤ d := by
    rw [hd, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by
      have : (1 : ℝ) ≤ 10 ^ (k + 2) := one_le_pow₀ (by norm_num)
      linarith)
  have hd2 : (2 : ℝ≥0∞) ≤ d := by
    rw [hd, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by
      have : (1 : ℝ) ≤ 10 ^ (k + 2) := one_le_pow₀ (by norm_num)
      linarith)
  have hd10 : ENNReal.ofReal (10 ^ (k + 2)) ≤ d :=
    ENNReal.ofReal_le_ofReal (by
      have : (0 : ℝ) ≤ 10 ^ (k + 2) := by positivity
      linarith)
  -- level zero vanishes
  have hzero : (D.family P hP.R_pos).comparisonEnergy pos 0 w ^ 2 = 0 := by
    refine le_antisymm ?_ zero_le
    show (D.family P hP.R_pos).rootComparisonTerm pos w ^ 2 ≤ 0
    unfold CoherentFamily.rootComparisonTerm
    refine ms3_iSup_sq_le fun a => ms3_iSup_sq_le fun _ => ms3_iSup_sq_le fun _ => ?_
    rw [D.ms3_family_plane_zero P hP.R_pos, D.ms3_family_initialPlane P hP.R_pos,
      ms3_planeComparison_self]
    simp
  -- the same-level comparisons at level `j`
  have hsame : ∀ j, (D.family P hP.R_pos).sameLevelComparisonTerm pos j w ^ 2 ≤
      c8 * (d * (S j + S (j + 1))) := by
    intro j
    unfold CoherentFamily.sameLevelComparisonTerm
    refine ms3_iSup_sq_le fun a => ms3_iSup_sq_le fun ha => ms3_iSup_sq_le fun b =>
      ms3_iSup_sq_le fun hb => ms3_iSup_sq_le fun hc => ?_
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      rw [D.ms3_family_plane_zero P hP.R_pos, D.ms3_family_plane_zero P hP.R_pos,
        ms3_planeComparison_self]
      simp
    have hj0 : j ≠ 0 := by omega
    have hr := P.scale_pos T hRpos j
    rw [D.ms3_family_index_pos P hP.R_pos hj0] at ha hb
    rw [D.ms3_family_center_pos P hP.R_pos hj0 a, D.ms3_family_center_pos P hP.R_pos hj0 b,
      D.ms3_family_scale P hP.R_pos] at hc
    rw [D.ms3_family_plane_pos P hP.R_pos hj0 a, D.ms3_family_plane_pos P hP.R_pos hj0 b,
      D.ms3_family_center_pos P hP.R_pos hj0 a]
    obtain ⟨hab, haw, hbw⟩ := hc
    have hdist := hpos20 j j a b (P.scale T j) ha hb hj hj le_rfl le_rfl hab
    have hga : D.cand j a ∈ I j := D.ms3_cand_mem_incident P pos w hj0 ha (by linarith)
    have hgb : D.cand j b ∈ I j := D.ms3_cand_mem_incident P pos w hj0 hb (by linarith)
    refine ms3_ofReal_sq_le (ms3_planeComparison_nonneg _ hr.le _ _)
      ((h8₁ j hj a ha b hb hdist).trans ?_)
    refine ms3_mul_le_mul_left ?_
    calc betaSq P.ν k T.toFamilyKind (D.cand j a) (40 * P.scale T j) +
          betaSq P.ν k T.toFamilyKind (D.cand j b) (40 * P.scale T j) ≤ S j + S j :=
          add_le_add (hbeta_le j _ hga) (hbeta_le j _ hgb)
      _ = 2 * S j := (two_mul _).symm
      _ ≤ d * S j := ms3_mul_le_mul_right hd2
      _ ≤ d * (S j + S (j + 1)) := ms3_mul_le_mul_left le_self_add
  -- the adjacent comparisons at level `j ≥ 1`
  have hadj : ∀ j, 1 ≤ j → (D.family P hP.R_pos).adjacentComparisonTerm pos j w ^ 2 ≤
      c8 * (d * (S j + S (j + 1))) := by
    intro j hj
    unfold CoherentFamily.adjacentComparisonTerm
    refine ms3_iSup_sq_le fun a => ms3_iSup_sq_le fun ha => ms3_iSup_sq_le fun b =>
      ms3_iSup_sq_le fun hb => ms3_iSup_sq_le fun hc => ?_
    have hj0 : j ≠ 0 := by omega
    have hj1 : j + 1 ≠ 0 := by omega
    have hr := P.scale_pos T hRpos j
    have hr1 := P.ms3_scale_succ T j
    rw [D.ms3_family_index_pos P hP.R_pos hj1] at ha
    rw [D.ms3_family_index_pos P hP.R_pos hj0] at hb
    rw [D.ms3_family_center_pos P hP.R_pos hj1 a, D.ms3_family_center_pos P hP.R_pos hj0 b,
      D.ms3_family_scale P hP.R_pos] at hc
    rw [D.ms3_family_plane_pos P hP.R_pos hj1 a, D.ms3_family_plane_pos P hP.R_pos hj0 b,
      D.ms3_family_center_pos P hP.R_pos hj0 b]
    obtain ⟨hab, haw, hbw⟩ := hc
    have hdist := hpos20 (j + 1) j a b (P.scale T j) ha hb (by omega) hj
      (by rw [hr1]; linarith) le_rfl hab
    have hga : D.cand (j + 1) a ∈ I (j + 1) :=
      D.ms3_cand_mem_incident P pos w hj1 ha (by rw [hr1]; linarith)
    have hgb : D.cand j b ∈ I j := D.ms3_cand_mem_incident P pos w hj0 hb (by linarith)
    refine ms3_ofReal_sq_le (ms3_planeComparison_nonneg _ hr.le _ _)
      ((h8₂ j hj a ha b hb hdist).trans ?_)
    refine ms3_mul_le_mul_left ?_
    calc betaSq P.ν k T.toFamilyKind (D.cand (j + 1) a) (40 * P.scale T (j + 1)) +
          ENNReal.ofReal (10 ^ (k + 2)) *
            betaSq P.ν k T.toFamilyKind (D.cand j b) (40 * P.scale T j)
        ≤ S (j + 1) + ENNReal.ofReal (10 ^ (k + 2)) * S j :=
          add_le_add (hbeta_le (j + 1) _ hga) (ms3_mul_le_mul_left (hbeta_le j _ hgb))
      _ ≤ d * S (j + 1) + d * S j :=
          add_le_add (le_mul_of_one_le_left' hd1) (ms3_mul_le_mul_right hd10)
      _ = d * (S j + S (j + 1)) := by ring
  -- the adjacent comparisons at level zero (with the root)
  have hadj0 : (D.family P hP.R_pos).adjacentComparisonTerm pos 0 w ^ 2 ≤
      c8 * (d * (S 0 + S 1) + Root) := by
    unfold CoherentFamily.adjacentComparisonTerm
    refine ms3_iSup_sq_le fun a => ms3_iSup_sq_le fun ha => ms3_iSup_sq_le fun b =>
      ms3_iSup_sq_le fun hb => ms3_iSup_sq_le fun hc => ?_
    have hr0 := P.scale_pos T hRpos 0
    have hr1 := P.ms3_scale_succ T 0
    have h1 : (0 : ℕ) + 1 ≠ 0 := by omega
    rw [D.ms3_family_index_pos P hP.R_pos h1] at ha
    rw [D.ms3_family_index_zero P hP.R_pos, Finset.mem_singleton] at hb
    subst hb
    rw [D.ms3_family_center_pos P hP.R_pos h1 a, D.ms3_family_scale P hP.R_pos] at hc
    rw [D.ms3_family_plane_pos P hP.R_pos h1 a, D.ms3_family_plane_zero P hP.R_pos,
      D.ms3_family_center_zero P hP.R_pos]
    obtain ⟨-, haw, -⟩ := hc
    have hga : D.cand (0 + 1) a ∈ I (0 + 1) :=
      D.ms3_cand_mem_incident P pos w h1 ha (by rw [hr1]; linarith)
    refine ms3_ofReal_sq_le (ms3_planeComparison_nonneg _ hr0.le _ _)
      ((h8₃ a ha).trans ?_)
    refine ms3_mul_le_mul_left (add_le_add ?_ le_rfl)
    calc betaSq P.ν k T.toFamilyKind (D.cand 1 a) (40 * P.scale T 1) ≤ S 1 :=
          hbeta_le (0 + 1) _ hga
      _ ≤ d * S 1 := le_mul_of_one_le_left' hd1
      _ ≤ d * (S 0 + S 1) := ms3_mul_le_mul_left le_add_self
  -- every level
  have hlevel : ∀ j, (D.family P hP.R_pos).comparisonEnergy pos (j + 1) w ^ 2 ≤
      c8 * (d * (S j + S (j + 1)) + if j = 0 then Root else 0) := by
    intro j
    show max ((D.family P hP.R_pos).sameLevelComparisonTerm pos j w)
      ((D.family P hP.R_pos).adjacentComparisonTerm pos j w) ^ 2 ≤ _
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      rw [ite_eq_left rfl]
      exact ms3_max_sq_le ((hsame 0).trans (ms3_mul_le_mul_left le_self_add)) hadj0
    · rw [ite_eq_right (by omega : j ≠ 0), add_zero]
      exact ms3_max_sq_le (hsame j) (hadj j hj)
  -- the incident sets: multiplicity, witnesses, cutoffs
  have hcard : ∀ j ≤ N, (I j).card ≤ 1937 ^ (n + 2) := by
    intro j _
    by_cases hne : (I j).Nonempty
    · obtain ⟨g₀, hg₀⟩ := hne
      obtain ⟨hj0, a₀, ha₀, haw₀, rfl⟩ := D.ms3_of_mem_incident P pos w hg₀
      have hj : 1 ≤ j := by omega
      have hr := P.scale_pos T hRpos j
      have hκ := T.ms3_quarter_le_sourceSeparation
      have hsub : (↑(I j) : Set (Space n)) ⊆ Metric.closedBall (D.cand j a₀) (242 * P.scale T j) := by
        intro g hg
        obtain ⟨-, b, hb, hbw, rfl⟩ := D.ms3_of_mem_incident P pos w hg
        rw [Metric.mem_closedBall, dist_comm]
        exact hwit j j a₀ b hj le_rfl ha₀ hb haw₀ hbw
      have hsep : ∀ x ∈ I j, ∀ y ∈ I j, x ≠ y → P.scale T j / 4 ≤ dist x y := by
        intro x hx y hy hxy
        obtain ⟨-, a, ha, -, rfl⟩ := D.ms3_of_mem_incident P pos w hx
        obtain ⟨-, b, hb, -, rfl⟩ := D.ms3_of_mem_incident P pos w hy
        have hab : a ≠ b := fun h => hxy (by rw [h])
        have h1 := hD.cand_separated j hj a ((D.ms3_mem_contIndex P).1 ha).1 b
          ((D.ms3_mem_contIndex P).1 hb).1 hab
        nlinarith
      have h := ms3_card_le_of_separated (D.cand j a₀) (by positivity) (by positivity) (I j)
        hsub hsep
      have he : (2 * (242 * P.scale T j) + P.scale T j / 4) / (P.scale T j / 4) = 1937 := by
        rw [div_eq_iff (by positivity)]
        ring
      rw [he] at h
      exact_mod_cast h
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
      simp
  have hSmem : ∀ j ≤ N, ∀ g ∈ I j, g ∈ P.S := by
    intro j _ g hg
    obtain ⟨hj0, a, ha, -, rfl⟩ := D.ms3_of_mem_incident P pos w hg
    exact D.ms3_cand_mem_S P hD (by omega) ((D.ms3_mem_contIndex P).1 ha).1
  have hfcut : ∀ j ≤ N, ∀ g ∈ I j, P.f g ≤ 1 * coherentScale (T.rootRadius P.R) j := by
    intro j _ g hg
    obtain ⟨hj0, a, ha, -, rfl⟩ := D.ms3_of_mem_incident P pos w hg
    rw [one_mul]
    exact (D.ms3_cand_cutoff_lt P hD (by omega) ((D.ms3_mem_contIndex P).1 ha).1).le
  have hwit' : ∀ j ≤ N, ∀ g ∈ I j, ∀ j', j ≤ j' → j' ≤ N → ∀ y ∈ I j',
      dist g y ≤ 242 * coherentScale (T.rootRadius P.R) j := by
    intro j _ g hg j' hjj' _ y hy
    obtain ⟨hj0, a, ha, haw, rfl⟩ := D.ms3_of_mem_incident P pos w hg
    obtain ⟨-, b, hb, hbw, rfl⟩ := D.ms3_of_mem_incident P pos w hy
    exact hwit j j' a b (by omega) hjj' ha hb haw hbw
  have hLWsum := ms3_incidentWitness_sum_le hLW P.ν k T.toFamilyKind P.S P.f B htail
    (T.rootRadius P.R) (T.rootRadius_pos hRpos) N I (1937 ^ (n + 2)) hcard hSmem 1 hfcut 242
    hwit' 40 282 (by norm_num) (by norm_num) (by norm_num)
  -- the root term
  have hRoot_le : Root ≤ ENNReal.ofReal (Cβ * B) := by
    have h4R : 4 * P.R ≤ P.scale T 0 := by
      rw [P.ms3_scale_zero T]
      exact T.ms3_four_le_rootRadius hRpos.le
    have hr0 : 0 < P.scale T 0 := by linarith
    have hq : 0 ≤ (P.scale T 0)⁻¹ ^ (k + 2) := by positivity
    calc Root ≤ ENNReal.ofReal ((P.scale T 0)⁻¹ ^ (k + 2)) *
          ENNReal.ofReal (Cβ * B * P.R ^ (k + 2)) := by
          rw [hRoot]
          gcongr
      _ = ENNReal.ofReal ((P.scale T 0)⁻¹ ^ (k + 2) * (Cβ * B * P.R ^ (k + 2))) :=
          (ENNReal.ofReal_mul hq).symm
      _ ≤ ENNReal.ofReal (Cβ * B) := by
          apply ENNReal.ofReal_le_ofReal
          have hRr : P.R ^ (k + 2) * (P.scale T 0)⁻¹ ^ (k + 2) ≤ 1 := by
            rw [← mul_pow]
            apply pow_le_one₀ (by positivity)
            rw [mul_inv_le_iff₀ hr0]
            linarith
          have hCB : 0 ≤ Cβ * B := by positivity
          calc (P.scale T 0)⁻¹ ^ (k + 2) * (Cβ * B * P.R ^ (k + 2))
              = Cβ * B * (P.R ^ (k + 2) * (P.scale T 0)⁻¹ ^ (k + 2)) := by ring
            _ ≤ Cβ * B * 1 := by gcongr
            _ = Cβ * B := mul_one _
  -- the sum over the levels
  have hsum : ∑ j ∈ Finset.range (N + 1),
      (D.family P hP.R_pos).comparisonEnergy pos j w ^ 2 ≤
      c8 * (d * (2 * ∑ j ∈ Finset.range (N + 1), S j) + Root) := by
    rw [Finset.sum_range_succ', hzero, add_zero]
    calc ∑ j ∈ Finset.range N, (D.family P hP.R_pos).comparisonEnergy pos (j + 1) w ^ 2
        ≤ ∑ j ∈ Finset.range N, c8 * (d * (S j + S (j + 1)) + if j = 0 then Root else 0) :=
          Finset.sum_le_sum fun j _ => hlevel j
      _ = c8 * (d * ∑ j ∈ Finset.range N, (S j + S (j + 1)) +
            ∑ j ∈ Finset.range N, if j = 0 then Root else 0) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ c8 * (d * (2 * ∑ j ∈ Finset.range (N + 1), S j) + Root) := by
          refine ms3_mul_le_mul_left (add_le_add (ms3_mul_le_mul_left ?_) ?_)
          · rw [Finset.sum_add_distrib, two_mul]
            refine add_le_add (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ N)))
              ?_
            rw [Finset.sum_range_succ' S N]
            exact le_self_add
          · rw [Finset.sum_ite_eq']
            split_ifs <;> simp
  -- final arithmetic
  set LW : ℝ := ((1937 ^ (n + 2) : ℕ) : ℝ) / Real.log 2 * 15 ^ (n + 3) with hLWdef
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLW0 : 0 ≤ LW := by positivity
  have hS_le : ∑ j ∈ Finset.range (N + 1), S j ≤ ENNReal.ofReal (LW * B) := by
    refine hLWsum.trans (ENNReal.ofReal_le_ofReal ?_)
    have h14 : (2 * 282 / 40 : ℝ) ^ (k + 2) ≤ 15 ^ (n + 3) := by
      calc (2 * 282 / 40 : ℝ) ^ (k + 2) ≤ 15 ^ (k + 2) :=
            pow_le_pow_left₀ (by norm_num) (by norm_num) _
        _ ≤ 15 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hN0 : 0 ≤ ((1937 ^ (n + 2) : ℕ) : ℝ) / Real.log 2 := by positivity
    calc ((1937 ^ (n + 2) : ℕ) : ℝ) / Real.log 2 * (2 * 282 / 40) ^ (k + 2) * B
        ≤ ((1937 ^ (n + 2) : ℕ) : ℝ) / Real.log 2 * 15 ^ (n + 3) * B := by gcongr
      _ = LW * B := rfl
  have h10 : (2 : ℝ) * 10 ^ (k + 2) * 2 ≤ 4 * 10 ^ (n + 3) := by
    have : (10 : ℝ) ^ (k + 2) ≤ 10 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  calc ∑ j ∈ Finset.range (N + 1), (D.family P hP.R_pos).comparisonEnergy pos j w ^ 2
      ≤ c8 * (d * (2 * ∑ j ∈ Finset.range (N + 1), S j) + Root) := hsum
    _ ≤ c8 * (d * (2 * ENNReal.ofReal (LW * B)) + ENNReal.ofReal (Cβ * B)) := by
        gcongr
    _ = ENNReal.ofReal (20000 * 8 ^ (n + 3) / P.a *
          (2 * 10 ^ (k + 2) * (2 * (LW * B)) + Cβ * B)) := by
        have hLWB : 0 ≤ LW * B := by positivity
        have e1 : (2 : ℝ≥0∞) * ENNReal.ofReal (LW * B) = ENNReal.ofReal (2 * (LW * B)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          simp
        have e2 : d * ENNReal.ofReal (2 * (LW * B)) =
            ENNReal.ofReal (2 * 10 ^ (k + 2) * (2 * (LW * B))) := by
          rw [hd, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * 10 ^ (k + 2))]
        have e3 : ENNReal.ofReal (2 * 10 ^ (k + 2) * (2 * (LW * B))) + ENNReal.ofReal (Cβ * B) =
            ENNReal.ofReal (2 * 10 ^ (k + 2) * (2 * (LW * B)) + Cβ * B) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
        have e4 : c8 * ENNReal.ofReal (2 * 10 ^ (k + 2) * (2 * (LW * B)) + Cβ * B) =
            ENNReal.ofReal (20000 * 8 ^ (n + 3) / P.a *
              (2 * 10 ^ (k + 2) * (2 * (LW * B)) + Cβ * B)) := by
          rw [hc8, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 20000 * 8 ^ (n + 3) / P.a)]
        rw [e1, e2, e3, e4]
    _ ≤ ENNReal.ofReal (20000 * 8 ^ (n + 3) * (4 * 10 ^ (n + 3) * LW + Cβ) * (B / P.a)) := by
        apply ENNReal.ofReal_le_ofReal
        have hLWB : 0 ≤ LW * B := by positivity
        have e5 : 20000 * 8 ^ (n + 3) * (4 * 10 ^ (n + 3) * LW + Cβ) * (B / P.a) =
            20000 * 8 ^ (n + 3) / P.a * (4 * 10 ^ (n + 3) * (LW * B) + Cβ * B) := by
          ring
        rw [e5]
        have h6 : 2 * 10 ^ (k + 2) * (2 * (LW * B)) ≤ 4 * 10 ^ (n + 3) * (LW * B) := by
          calc 2 * 10 ^ (k + 2) * (2 * (LW * B)) = (2 * 10 ^ (k + 2) * 2) * (LW * B) := by ring
            _ ≤ 4 * 10 ^ (n + 3) * (LW * B) := mul_le_mul_of_nonneg_right h10 hLWB
        exact mul_le_mul_of_nonneg_left (add_le_add h6 le_rfl) (by positivity)

/-! ## The finite ambient square -/

/-- **`ambientSquare_finite_of_construction`**, from `nodeBeta_le` (hypothesis `hβ`)
and `ChargeCollapse.lastWitness_sum` (hypothesis `hLW`). Constants: `C = 20000·8^{n+3} (4·10^{n+3}·1937^{n+2}/log 2·15^{n+3} + C_β)`,
`θ₁ = A₁ = 1`. -/
theorem ambientSquare_finite_of_construction_proof (n : ℕ)
    (hβ : ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T)
      (B : ℝ), T.Available n k → k < n + 2 → P.IsAdmissible → 0 < B → P.TailBound k T B →
      D.IsSourceConstruction P →
      (∀ j, 1 ≤ j → ∀ i, i < D.candCount j →
        betaSq P.ν k T.toFamilyKind (D.cand j i) (40 * P.scale T j) ≤
          ENNReal.ofReal (C * B)) ∧
      ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν ≤ ENNReal.ofReal (C * B * P.R ^ (k + 2)))
    (hLW : ∀ {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ)
      (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
      (_htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
      (r₀ : ℝ) (_hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n)) (N₀ : ℕ)
      (_hcard : ∀ j ≤ N, (I j).card ≤ N₀) (J : ℕ) (_hJ : J ≤ N)
      (_hdeep : ∀ j, J < j → j ≤ N → I j = ∅) (y : Space n) (_hyI : y ∈ I J) (_hyS : y ∈ S)
      (Fc : ℝ) (_hfy : f y ≤ Fc * coherentScale r₀ J) (A : ℝ)
      (_hA : ∀ j ≤ J, ∀ g ∈ I j, dist g y ≤ A * coherentScale r₀ j)
      (c H : ℝ) (_hc : 0 < c) (_hH₁ : Fc ≤ H) (_hH₂ : A + c ≤ H),
      ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) ≤
        ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B)) :
    ∃ C θ₁ A₁ : ℝ, 0 < C ∧ 0 < θ₁ ∧ 0 < A₁ ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
      (D : ConstructionData n k T) (B : ℝ), T.Available n k → k < n + 2 →
      ∀ hP : P.IsAdmissible, 0 < B → P.TailBound k T B → D.IsSourceConstruction P →
      P.θ ≤ θ₁ → A₁ * B ≤ P.a →
      (T = .horizontal → ∃ γ : ℝ, 0 ≤ γ ∧ γ ≤ 1 ∧
        RecordsTimeCompatible (D.family P hP.R_pos) (D.centers P) (D.radius P) γ) →
      ∀ N : ℕ,
        (T = .vertical →
          (D.family P hP.R_pos).VerticalSquareBoundUpTo (C * (B / P.a)) N) ∧
        (T = .horizontal →
          (D.family P hP.R_pos).HorizontalSquareBoundUpTo (C * (B / P.a)) N) := by
  obtain ⟨Cβ, hCβ, hβ'⟩ := hβ
  refine ⟨20000 * 8 ^ (n + 3) * (4 * 10 ^ (n + 3) *
      (((1937 ^ (n + 2) : ℕ) : ℝ) / Real.log 2 * 15 ^ (n + 3)) + Cβ), 1, 1, ?_, one_pos,
    one_pos, ?_⟩
  · have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  intro k T P D B hT hk hP hB htail hD _ _ htimeH N
  obtain ⟨-, hglob⟩ := hβ' P D B hT hk hP hB htail hD
  have hRpos := hP.R_pos
  refine ⟨fun hV => ?_, fun hH => ?_⟩
  · -- vertical: parabolic incidence
    subst hV
    intro w
    refine D.ms3_squareBound_generic (fun z : Space n => z) P B hT hk hP hB htail hD hCβ hglob
      hLW (fun i j a b s _ _ _ _ _ _ h => h) w ?_ N
    intro j J a b hj hjJ _ _ haw hbw
    have hJ := P.ms3_scale_anti .vertical hRpos hjJ
    calc dist (D.cand j a) (D.cand J b) ≤ dist (D.cand j a) w + dist w (D.cand J b) :=
          dist_triangle _ _ _
      _ ≤ 120 * P.scale .vertical j + 120 * P.scale .vertical J := by
          rw [dist_comm w]
          exact add_le_add haw hbw
      _ ≤ 242 * P.scale .vertical j := by
          have := P.scale_pos .vertical hRpos j
          linarith
  · -- horizontal: spatial incidence and time compatibility
    subst hH
    obtain ⟨γ, hγ0, hγ1, htime⟩ := htimeH rfl
    intro w
    have hrec : ∀ {j a : ℕ}, 1 ≤ j → a ∈ D.contIndex P j →
        a ∈ (D.family P hP.R_pos).index j := by
      intro j a hj ha
      rw [D.ms3_family_index_pos P hP.R_pos (by omega)]
      exact ha
    refine D.ms3_squareBound_generic (fun z : Space n => z.1) P B hT hk hP hB htail hD hCβ
      hglob hLW ?_ w ?_ N
    · intro i j a b s ha hb hi hj hsi hsj h
      have hs : 0 ≤ s := (P.scale_pos .horizontal hRpos i).le.trans hsi
      have ht := htime (Sum.inl (i, a)) (Sum.inl (j, b)) (hrec hi ha) (hrec hj hb)
      simp only [NeckRecord.position, NeckRecord.scale,
        D.ms3_family_center_pos P hP.R_pos (show i ≠ 0 by omega),
        D.ms3_family_center_pos P hP.R_pos (show j ≠ 0 by omega),
        D.ms3_family_scale P hP.R_pos] at ht
      have hx : ‖(D.cand i a).1 - (D.cand j b).1‖ ≤ 20 * s := by
        rw [← dist_eq_norm]
        exact h
      have hmax : max (‖(D.cand i a).1 - (D.cand j b).1‖ ^ 2)
          (max (P.scale .horizontal i ^ 2) (P.scale .horizontal j ^ 2)) ≤ (20 * s) ^ 2 := by
        have hi0 := (P.scale_pos .horizontal hRpos i).le
        have hj0 := (P.scale_pos .horizontal hRpos j).le
        refine max_le (pow_le_pow_left₀ (norm_nonneg _) hx 2) (max_le ?_ ?_)
        · exact pow_le_pow_left₀ hi0 (by linarith) 2
        · exact pow_le_pow_left₀ hj0 (by linarith) 2
      refine ms3_dist_le_of (by positivity) hx ?_
      calc |(D.cand i a).2.val - (D.cand j b).2.val|
          ≤ γ * max (‖(D.cand i a).1 - (D.cand j b).1‖ ^ 2)
            (max (P.scale .horizontal i ^ 2) (P.scale .horizontal j ^ 2)) := ht
        _ ≤ 1 * (20 * s) ^ 2 := mul_le_mul hγ1 hmax (by positivity) zero_le_one
        _ = (20 * s) ^ 2 := one_mul _
    · intro j J a b hj hjJ ha hb haw hbw
      have hr := P.scale_pos .horizontal hRpos j
      have hrJ := P.scale_pos .horizontal hRpos J
      have h := CoherentFamily.horizontal_occurrence_witness (D.family P hP.R_pos)
        (A₀ := 121) hγ0 (by norm_num) htime hjJ (hrec hj ha) (hrec (hj.trans hjJ) hb)
        (x := w)
        (by rw [D.ms3_family_center_pos P hP.R_pos (show j ≠ 0 by omega) a, dist_comm,
              D.ms3_family_scale P hP.R_pos]
            exact lt_of_le_of_lt haw (by linarith))
        (by rw [D.ms3_family_center_pos P hP.R_pos (show J ≠ 0 by omega) b, dist_comm,
              D.ms3_family_scale P hP.R_pos]
            exact lt_of_le_of_lt hbw (by linarith))
      rw [D.ms3_family_center_pos P hP.R_pos (show j ≠ 0 by omega) a,
        D.ms3_family_center_pos P hP.R_pos (show J ≠ 0 by omega) b,
        D.ms3_family_scale P hP.R_pos] at h
      have hsq : Real.sqrt γ ≤ 1 := Real.sqrt_le_one.mpr hγ1
      have hm : max (2 * (121 : ℝ)) (Real.sqrt γ * max (2 * 121) 1) ≤ 242 := by
        refine max_le (by norm_num) ?_
        rw [show max (2 * (121 : ℝ)) 1 = 242 by norm_num]
        nlinarith [Real.sqrt_nonneg γ]
      calc dist (D.cand j a) (D.cand J b)
          ≤ max (2 * 121) (Real.sqrt γ * max (2 * 121) 1) * P.scale .horizontal j := h
        _ ≤ 242 * P.scale .horizontal j := by gcongr

end ParabolicRectifiability
