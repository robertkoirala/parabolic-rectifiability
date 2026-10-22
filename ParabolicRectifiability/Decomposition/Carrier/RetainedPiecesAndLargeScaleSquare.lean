import ParabolicRectifiability.Decomposition.Carrier.Definitions
import ParabolicRectifiability.Decomposition.Interfaces
import ParabolicRectifiability.Measure.ScaleIntegrals
import ParabolicRectifiability.Metric.BaseVolume

/-! # Regular vertical carrier: retained pieces and the large-scale square of a partial graph

Proofs of two intermediate statements in the construction of the regular vertical
carrier.

* `vertical_core_retained_pieces_proof` (retained pieces with small square tail).
  Positive lower density selects a dyadic level `2^{-j}`; continuity
  from above of the finite square integral makes the level budget `b_j` attainable
  below a radius `r₀ 2^{-p}`. The lower-mass condition is closed and the tail
  condition is measurable, so inner regularity of `η = H^k_P ⌞ K` gives compact
  subsets exhausting each level set up to an `η`-null set; balls about a dense
  sequence localize them. An `η`-null subset of `K` is `H^k_P`-null.
* `partial_graph_large_scale_square_le_proof` (large-scale square of a partial
  graph). The
  vertical plane through one lifted point parallel to the base has squared distance
  at most `(2ℓρ)²` on the lifted piece, whose Hausdorff mass is at most a dimensional
  multiple of `ρ^{m+2}`; integrating `s^{-(m+4)} ds/s` over `[T,∞)` gives the bound.
  No measurability of the domain is used.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-! ## Retained pieces -/

/-- Lower mass at every radius `0 < r ≤ T` is a closed condition on the center:
open balls about nearby centers are contained in a slightly larger ball. -/
theorem isClosed_setOf_lowerMass {n : ℕ} (η : Measure (Space n)) (k : ℕ) (a T : ℝ) :
    IsClosed {z : Space n | ∀ r : ℝ, 0 < r → r ≤ T →
      ENNReal.ofReal (a * r ^ k) ≤ η (Metric.ball z r)} := by
  refine isClosed_of_closure_subset fun z hz r hr hrT => ?_
  have key : ∀ s : ℝ, 0 < s → s < r →
      ENNReal.ofReal (a * s ^ k) ≤ η (Metric.ball z r) := by
    intro s hs hsr
    obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.1 hz (r - s) (sub_pos.2 hsr)
    refine (hw s hs (hsr.le.trans hrT)).trans (measure_mono fun y hy => ?_)
    rw [Metric.mem_ball] at hy ⊢
    calc dist y z ≤ dist y w + dist z w := dist_triangle_right y z w
      _ < s + (r - s) := add_lt_add hy hzw
      _ = r := by ring
  have hlim : Tendsto (fun s : ℝ => ENNReal.ofReal (a * s ^ k)) (𝓝[<] r)
      (𝓝 (ENNReal.ofReal (a * r ^ k))) :=
    ((ENNReal.continuous_ofReal.comp
      (continuous_const.mul (continuous_pow k))).tendsto r).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hr] with s hs using key s hs.1 hs.2

/-- Continuity from above of the square integral: if it is finite up to `R 0`, it
tends to zero along radii decreasing to zero. -/
theorem tendsto_squareEnergy_zero {n : ℕ} (η : Measure (Space n))
    [IsFiniteMeasureOnCompacts η] (k : ℕ) (z : Space n) {R : ℕ → ℝ} (hR : Antitone R)
    (hR0 : Tendsto R atTop (𝓝 0)) (hfin : squareEnergy η k .vertical (R 0) z ≠ ⊤) :
    Tendsto (fun p => squareEnergy η k .vertical (R p) z) atTop (𝓝 0) := by
  have hν : ∀ p, squareEnergy η k .vertical (R p) z =
      scaleMeasure.withDensity (fun r : ℝ => betaSq η k .vertical z r) (Ioo 0 (R p)) :=
    fun p => by
    rw [withDensity_apply _ measurableSet_Ioo]
    rfl
  have hinter : (⋂ p, Ioo (0 : ℝ) (R p)) = ∅ := by
    refine eq_empty_of_forall_notMem fun r hr => ?_
    rw [mem_iInter] at hr
    obtain ⟨p, hp⟩ := (hR0.eventually (gt_mem_nhds (hr 0).1)).exists
    exact lt_irrefl r ((hr p).2.trans hp)
  have h := tendsto_measure_iInter_atTop
    (μ := scaleMeasure.withDensity (fun r : ℝ => betaSq η k .vertical z r))
    (s := fun p => Ioo (0 : ℝ) (R p))
    (fun _ => measurableSet_Ioo.nullMeasurableSet)
    (fun p q hpq => Ioo_subset_Ioo_right (hR hpq)) ⟨0, by rwa [← hν]⟩
  rw [hinter, measure_empty] at h
  exact (tendsto_congr hν).2 h

/-- Retained compact pieces of the vertical core with lower mass and small square
tail; this is the statement `vertical_core_retained_pieces`. -/
theorem vertical_core_retained_pieces_proof {n k : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hfin : hausdorffP n k K < ⊤) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hae : ∀ᵐ z ∂(hausdorffP n k).restrict K,
      HasPositiveLowerDensity ((hausdorffP n k).restrict K) k z ∧
        squareEnergy ((hausdorffP n k).restrict K) k .vertical r₀ z < ⊤)
    (c : ℝ) (hc : 0 < c) (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) :
    ∃ (level : ℕ → ℕ) (T : ℕ → ℝ) (center : ℕ → Space n) (F : ℕ → Set (Space n)),
      (∀ i, 0 < T i ∧ T i ≤ r₀) ∧
      (∀ i, F i ⊆ K ∧ F i ⊆ Metric.ball (center i) (c * T i) ∧
        IsCarrierPiece ((hausdorffP n k).restrict K) k ((1 / 2 : ℝ) ^ level i)
          (b (level i)) (T i) (F i)) ∧
      hausdorffP n k (K \ ⋃ i, F i) = 0 := by
  set η := (hausdorffP n k).restrict K with hη
  have : IsFiniteMeasure η := hausdorffP_restrict_isFinite hfin
  have : η.InnerRegular := hausdorffP_restrict_innerRegular hK hfin
  -- the radii `r₀ 2^{-p}`
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ → ℝ, R = fun p => r₀ * (1 / 2 : ℝ) ^ p := ⟨_, rfl⟩
  have hRpos : ∀ p, 0 < R p := fun p => by rw [hRdef]; positivity
  have hRle : ∀ p, R p ≤ r₀ := fun p => by
    rw [hRdef]
    exact mul_le_of_le_one_right hr₀.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hR0eq : R 0 = r₀ := by rw [hRdef]; simp
  have hRanti : Antitone R := fun p q hpq => by
    rw [hRdef]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hpq) hr₀.le
  have hR0 : Tendsto R atTop (𝓝 0) := by
    rw [hRdef]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul r₀
  -- the density/tail sets
  let A : ℕ → ℕ → Set (Space n) := fun j p =>
    (K ∩ {z | ∀ r : ℝ, 0 < r → r ≤ R p →
      ENNReal.ofReal ((1 / 2 : ℝ) ^ j * r ^ k) ≤ η (Metric.ball z r)}) ∩
      {z | squareEnergy η k .vertical (R p) z ≤ ENNReal.ofReal (b j)}
  have hAmeas : ∀ j p, MeasurableSet (A j p) := fun j p =>
    (hK.measurableSet.inter (isClosed_setOf_lowerMass η k _ _).measurableSet).inter
      (measurableSet_le (measurable_squareEnergy η k .vertical (R p)) measurable_const)
  -- almost every point lies in one of them
  have hcov : ∀ᵐ z ∂η, ∃ j p, z ∈ A j p := by
    filter_upwards [hae, ae_restrict_mem hK.measurableSet] with z hz hzK
    obtain ⟨⟨a, r₁, ha, hr₁, hlow⟩, hfinE⟩ := hz
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one ha (by norm_num : (1 / 2 : ℝ) < 1)
    have hE : Tendsto (fun p => squareEnergy η k .vertical (R p) z) atTop (𝓝 0) :=
      tendsto_squareEnergy_zero η k z hRanti hR0 (by rw [hR0eq]; exact hfinE.ne)
    obtain ⟨p, hp1, hp2⟩ := ((hR0.eventually (ge_mem_nhds hr₁)).and
      (hE.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 (hb j))))).exists
    refine ⟨j, p, ⟨hzK, fun r hr hrp => ?_⟩, hp2⟩
    calc ENNReal.ofReal ((1 / 2 : ℝ) ^ j * r ^ k) ≤ ENNReal.ofReal (a * r ^ k) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hj.le (by positivity))
      _ ≤ η (Metric.ball z r) := hlow r hr (hrp.trans hp1)
  -- compact subsets exhausting each set
  have hcpt : ∀ j p q : ℕ, ∃ C : Set (Space n), C ⊆ A j p ∧ IsCompact C ∧
      η (A j p \ C) < (q : ℝ≥0∞)⁻¹ := fun j p q =>
    (hAmeas j p).exists_isCompact_sdiff_lt (measure_ne_top η _)
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top q))
  choose C hCA hCc hCη using hcpt
  have hnull : ∀ j p, η (A j p \ ⋃ q, C j p q) = 0 := by
    intro j p
    by_contra hne
    obtain ⟨q, hq⟩ := ENNReal.exists_inv_nat_lt hne
    exact lt_irrefl _ ((hq.trans_le (measure_mono
      (sdiff_subset_sdiff_right (subset_iUnion (C j p) q)))).trans (hCη j p q))
  -- localization by balls about a dense sequence
  have : Nonempty (Space n) := ⟨point 0 0⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (Space n)
  let G : ℕ × ℕ × ℕ × ℕ → Set (Space n) := fun x =>
    C x.1 x.2.1 x.2.2.1 ∩ Metric.closedBall (u x.2.2.2) (c * R x.2.1 / 2)
  have hpiece : ∀ x : ℕ × ℕ × ℕ × ℕ, G x ⊆ K ∧
      G x ⊆ Metric.ball (u x.2.2.2) (c * R x.2.1) ∧
      IsCarrierPiece η k ((1 / 2 : ℝ) ^ x.1) (b x.1) (R x.2.1) (G x) := by
    rintro ⟨j, p, q, l⟩
    have hGA : G (j, p, q, l) ⊆ A j p := inter_subset_left.trans (hCA j p q)
    refine ⟨fun z hz => (hGA hz).1.1, inter_subset_right.trans
      (Metric.closedBall_subset_ball (half_lt_self (mul_pos hc (hRpos p)))), ?_⟩
    exact { compact := (hCc j p q).inter_right Metric.isClosed_closedBall
            lower_mass := fun z hz => (hGA hz).1.2
            small_tail := fun z hz => (hGA hz).2 }
  let e : ℕ → ℕ × ℕ × ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ × ℕ × ℕ)).symm
  refine ⟨fun i => (e i).1, fun i => R (e i).2.1, fun i => u (e i).2.2.2, fun i => G (e i),
    fun i => ⟨hRpos _, hRle _⟩, fun i => hpiece (e i), ?_⟩
  show hausdorffP n k (K \ ⋃ i, G (e i)) = 0
  have hsub : K \ ⋃ i, G (e i) ⊆
      {z | ¬ ∃ j p, z ∈ A j p} ∪ ⋃ j, ⋃ p, (A j p \ ⋃ q, C j p q) := by
    rintro z ⟨_, hzF⟩
    by_cases h : ∃ j p, z ∈ A j p
    · obtain ⟨j, p, hz⟩ := h
      refine Or.inr (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨p, hz, fun hzC => hzF ?_⟩⟩)
      obtain ⟨q, hq⟩ := mem_iUnion.1 hzC
      obtain ⟨l, hl⟩ := hu.exists_dist_lt z (half_pos (mul_pos hc (hRpos p)))
      have he : e (Denumerable.eqv (ℕ × ℕ × ℕ × ℕ) (j, p, q, l)) = (j, p, q, l) :=
        Equiv.symm_apply_apply _ _
      refine mem_iUnion.2 ⟨Denumerable.eqv (ℕ × ℕ × ℕ × ℕ) (j, p, q, l), ?_⟩
      rw [he]
      exact ⟨hq, Metric.mem_closedBall.2 hl.le⟩
    · exact Or.inl h
  have hηnull : η (K \ ⋃ i, G (e i)) = 0 :=
    measure_mono_null hsub (measure_union_null (ae_iff.1 hcov)
      (measure_iUnion_null fun j => measure_iUnion_null fun p => hnull j p))
  calc hausdorffP n k (K \ ⋃ i, G (e i)) = η (K \ ⋃ i, G (e i)) := by
        rw [hη, Measure.restrict_apply' hK.measurableSet, inter_eq_left.2 sdiff_subset]
    _ = 0 := hηnull

/-! ## The large-scale square of a partial graph -/

/-- The fit against a model whose cost is at most `c` on `S` is at most `c` times
the mass of `S`, for the restriction to an arbitrary (possibly non-measurable) `S`. -/
theorem fit_restrict_le_of_modelCost_le {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n))
    (S : Set (Space n)) (L : Models n k T) (c : ℝ≥0∞)
    (hc : ∀ w ∈ S, modelCost L w ≤ c) (z : Space n) (r : ℝ) :
    fit (μ.restrict S) L z r ≤ c * μ S := by
  have hae : ∀ᵐ w ∂μ.restrict S, modelCost L w ≤ c :=
    (ae_restrict_iff (measurableSet_le (measurable_modelCost L) measurable_const)).2
      (Filter.Eventually.of_forall hc)
  calc fit (μ.restrict S) L z r ≤ ∫⁻ w, modelCost L w ∂μ.restrict S :=
        setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ _w, c ∂μ.restrict S := lintegral_mono_ae hae
    _ = c * μ S := by rw [lintegral_const, Measure.restrict_apply_univ]

section PartialGraph

variable {n : ℕ} (W : Submodule ℝ (Spatial n))

/-- The base distance is at most the distance of the lifted points: the spatial base
difference lies in `W` and the normal difference in `Wᗮ`. -/
theorem dist_le_dist_verticalLift (g : SubspaceSpace W → W.orthogonal)
    (q p : SubspaceSpace W) :
    dist q p ≤ dist (verticalLift W g q) (verticalLift W g p) := by
  have hu : (q.1 : Spatial n) - p.1 ∈ W := W.sub_mem q.1.2 p.1.2
  have hv : (g q : Spatial n) - g p ∈ W.orthogonal := W.orthogonal.sub_mem (g q).2 (g p).2
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_real
    (Submodule.inner_right_of_mem_orthogonal hu hv)
  have e1 : dist q.1 p.1 = ‖(q.1 : Spatial n) - p.1‖ := by rw [dist_eq_norm]; rfl
  have hsp : dist q.1 p.1 ≤ dist (verticalLift W g q).1 (verticalLift W g p).1 := by
    have heq : (verticalLift W g q).1 - (verticalLift W g p).1 =
        ((q.1 : Spatial n) - p.1) + ((g q : Spatial n) - g p) := by
      dsimp only; abel
    rw [e1, dist_eq_norm, heq]
    exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2
      (by rw [hpy]; exact le_add_of_nonneg_right (mul_self_nonneg _))
  rw [Prod.dist_eq, Prod.dist_eq]
  exact max_le_max hsp le_rfl

/-- The lift of an `ℓ`-Lipschitz normal function, `ℓ ≤ 1`, is `2`-Lipschitz. -/
theorem lipschitzOnWith_verticalLift {g : SubspaceSpace W → W.orthogonal}
    {D : Set (SubspaceSpace W)} {ℓ : ℝ≥0} (hℓ : (ℓ : ℝ) ≤ 1) (hg : LipschitzOnWith ℓ g D) :
    LipschitzOnWith 2 (verticalLift W g) D := by
  refine LipschitzOnWith.of_dist_le_mul fun q hq p hp => ?_
  have hgd := hg.dist_le_mul q hq p hp
  have hdnn : 0 ≤ dist q p := dist_nonneg
  have h1 : dist q.1 p.1 ≤ dist q p := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h2 : dist q.2 p.2 ≤ dist q p := by rw [Prod.dist_eq]; exact le_max_right _ _
  have h3 : (ℓ : ℝ) * dist q p ≤ dist q p := mul_le_of_le_one_left hdnn hℓ
  have e1 : dist q.1 p.1 = ‖(q.1 : Spatial n) - p.1‖ := by rw [dist_eq_norm]; rfl
  have e2 : dist (g q) (g p) = ‖(g q : Spatial n) - g p‖ := by rw [dist_eq_norm]; rfl
  have hsp : dist (verticalLift W g q).1 (verticalLift W g p).1 ≤
      dist q.1 p.1 + dist (g q) (g p) := by
    have heq : (verticalLift W g q).1 - (verticalLift W g p).1 =
        ((q.1 : Spatial n) - p.1) + ((g q : Spatial n) - g p) := by
      dsimp only; abel
    rw [dist_eq_norm, heq, e1, e2]
    exact norm_add_le _ _
  have hfin : max (dist (verticalLift W g q).1 (verticalLift W g p).1) (dist q.2 p.2) ≤
      2 * dist q p := max_le (by linarith) (by linarith)
  rw [Prod.dist_eq]
  push_cast
  exact hfin

/-- The vertical plane through the lift of `p`, parallel to `W`, is within the normal
oscillation `|g q - g p|` of the lift of `q`. -/
theorem modelCost_verticalLift_le {m : ℕ} (hW : Module.finrank ℝ W = m)
    (g : SubspaceSpace W → W.orthogonal) (p q : SubspaceSpace W) :
    modelCost (verticalPlaneModel (AffineSpatialPlane.ofTranslate W hW (g p : Spatial n)))
      (verticalLift W g q) ≤ ENNReal.ofReal (dist (g q) (g p)) ^ 2 := by
  have hmem : (((q.1 : Spatial n) + (g p : Spatial n), q.2) : Space n) ∈
      modelSet (verticalPlaneModel (AffineSpatialPlane.ofTranslate W hW (g p : Spatial n))) := by
    show (q.1 : Spatial n) + (g p : Spatial n) ∈
      (AffineSpatialPlane.ofTranslate W hW (g p : Spatial n)).toSet
    rw [AffineSpatialPlane.ofTranslate_toSet]
    simpa only [mem_ofPred_eq, add_sub_cancel_right] using q.1.2
  refine (modelCost_le_edist_sq _ hmem _).trans ?_
  rw [edist_dist]
  gcongr
  rw [Prod.dist_eq]
  show max (dist ((q.1 : Spatial n) + (g q : Spatial n)) ((q.1 : Spatial n) + (g p : Spatial n)))
    (dist q.2 q.2) ≤ dist (g q) (g p)
  rw [dist_self, dist_add_left]
  exact max_le le_rfl dist_nonneg

/-- Hausdorff mass of the lift of a piece of the base contained in a ball of radius `R`. -/
theorem hausdorffP_verticalLift_image_le {m : ℕ} (hW : Module.finrank ℝ W = m)
    {g : SubspaceSpace W → W.orthogonal} {D : Set (SubspaceSpace W)} {ℓ : ℝ≥0}
    (hℓ : (ℓ : ℝ) ≤ 1) (hg : LipschitzOnWith ℓ g D) {p : SubspaceSpace W} {R : ℝ}
    (hR : 0 < R) (hD : D ⊆ Metric.ball p R) :
    hausdorffP n (m + 2) (verticalLift W g '' D) ≤
      ENNReal.ofReal (2 ^ (m + 2) * (verticalHausdorffConstant m * (2 * omega m)).toReal *
        R ^ (m + 2)) := by
  have hfin : verticalHausdorffConstant m * (2 * omega m) ≠ ⊤ :=
    ENNReal.mul_ne_top (verticalHausdorffConstant_lt_top m).ne
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (omega_lt_top m).ne)
  have himg := hausdorffMeasure_image_le_of_subset (lipschitzOnWith_verticalLift W hℓ hg)
    subset_rfl (m + 2)
  have hcmp := (vertical_base_hausdorff_comparison W (Metric.ball p R)).2
  rw [intrinsicParabolicVolume_ball W p R hR, hW] at hcmp
  rw [hausdorffP_eq]
  refine himg.trans ?_
  calc ((2 : ℝ≥0) : ℝ≥0∞) ^ (m + 2) * Measure.hausdorffMeasure ((m + 2 : ℕ) : ℝ) D
      ≤ ((2 : ℝ≥0) : ℝ≥0∞) ^ (m + 2) * (verticalHausdorffConstant m *
          (2 * omega m * ENNReal.ofReal R ^ (m + 2))) := by
        gcongr
        exact (measure_mono hD).trans hcmp
    _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin,
          ENNReal.ofReal_pow hR.le, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
          ENNReal.coe_ofNat]
        ring

end PartialGraph

/-- Quantitative large-scale square tail of a partial graph piece; this is the
statement `partial_graph_large_scale_square_le`. -/
theorem partial_graph_large_scale_square_le_proof (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (W : Submodule ℝ (Spatial n)), Module.finrank ℝ W = m →
      ∀ (D : Set (SubspaceSpace W)) (g : SubspaceSpace W → W.orthogonal) (ℓ : ℝ≥0),
        (ℓ : ℝ) ≤ 1 → LipschitzOnWith ℓ g D →
        ∀ (z₀ : Space n) (ρ T : ℝ), 0 < ρ → 0 < T →
          verticalLift W g '' D ⊆ Metric.ball z₀ ρ →
          ∀ z : Space n,
            ∫⁻ s in Ici T,
                betaSq ((hausdorffP n (m + 2)).restrict (verticalLift W g '' D))
                  (m + 2) .vertical z s ∂scaleMeasure ≤
              ENNReal.ofReal (C * (ℓ : ℝ) ^ 2 * (ρ / T) ^ (m + 4) / ((m : ℝ) + 4)) := by
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = (verticalHausdorffConstant m * (2 * omega m)).toReal :=
    ⟨_, rfl⟩
  have hv : 0 ≤ v := by rw [hvdef]; exact ENNReal.toReal_nonneg
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = 4 * 2 ^ (m + 2) * v * 2 ^ (m + 2) := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by rw [hC']; positivity
  refine ⟨C' + 1, by linarith, ?_⟩
  intro n W hW D g ℓ hℓ hg z₀ ρ T hρ hT hsub z
  rcases D.eq_empty_or_nonempty with hD | ⟨p, hp⟩
  · have : Nonempty (Models n (m + 2) .vertical) :=
      ⟨verticalPlaneModel (AffineSpatialPlane.ofTranslate W hW 0)⟩
    simp only [hD, image_empty, Measure.restrict_empty, betaSq_zero, lintegral_zero, zero_le]
  · set G := verticalLift W g '' D with hG
    set μ := hausdorffP n (m + 2) with hμ
    have hlift : ∀ q ∈ D, dist q p < 2 * ρ := by
      intro q hq
      have hq' := hsub (mem_image_of_mem _ hq)
      have hp' := hsub (mem_image_of_mem _ hp)
      rw [Metric.mem_ball] at hq' hp'
      calc dist q p ≤ dist (verticalLift W g q) (verticalLift W g p) :=
            dist_le_dist_verticalLift W g q p
        _ ≤ dist (verticalLift W g q) z₀ + dist (verticalLift W g p) z₀ :=
            dist_triangle_right _ _ _
        _ < ρ + ρ := add_lt_add hq' hp'
        _ = 2 * ρ := by ring
    have hcost : ∀ w ∈ G, modelCost (verticalPlaneModel
        (AffineSpatialPlane.ofTranslate W hW (g p : Spatial n))) w ≤
        ENNReal.ofReal (2 * ℓ * ρ) ^ 2 := by
      rintro _ ⟨q, hq, rfl⟩
      refine (modelCost_verticalLift_le W hW g p q).trans ?_
      gcongr
      calc dist (g q) (g p) ≤ ℓ * dist q p := hg.dist_le_mul q hq p hp
        _ ≤ ℓ * (2 * ρ) := mul_le_mul_of_nonneg_left (hlift q hq).le (NNReal.coe_nonneg ℓ)
        _ = 2 * ℓ * ρ := by ring
    have hmass : μ G ≤ ENNReal.ofReal (2 ^ (m + 2) * v * (2 * ρ) ^ (m + 2)) := by
      rw [hvdef]
      exact hausdorffP_verticalLift_image_le W hW hℓ hg (by positivity)
        (fun q hq => Metric.mem_ball.2 (hlift q hq))
    have hpt : ∀ s ∈ Ioi T, betaSq (μ.restrict G) (m + 2) .vertical z s ≤
        (ENNReal.ofReal s)⁻¹ ^ (m + 2 + 2) * (ENNReal.ofReal (2 * ℓ * ρ) ^ 2 * μ G) := by
      intro s hs
      rw [betaSq_of_pos _ _ _ _ (hT.trans hs)]
      gcongr
      exact (iInf_le _ _).trans (fit_restrict_le_of_modelCost_le μ G _ _ hcost z s)
    have hreal : (T ^ (m + 2 + 2))⁻¹ / ((m + 2 + 2 : ℕ) : ℝ) *
        ((2 * ℓ * ρ) ^ 2 * (2 ^ (m + 2) * v * (2 * ρ) ^ (m + 2))) =
        C' * ((ℓ : ℝ) ^ 2 * (ρ / T) ^ (m + 4) / ((m : ℝ) + 4)) := by
      have h4 : ((m + 2 + 2 : ℕ) : ℝ) = (m : ℝ) + 4 := by push_cast; ring
      rw [hC', h4]
      ring
    have hX : 0 ≤ (ℓ : ℝ) ^ 2 * (ρ / T) ^ (m + 4) / ((m : ℝ) + 4) := by positivity
    calc ∫⁻ s in Ici T, betaSq (μ.restrict G) (m + 2) .vertical z s ∂scaleMeasure
        = ∫⁻ s in Ioi T, betaSq (μ.restrict G) (m + 2) .vertical z s ∂scaleMeasure :=
          setLIntegral_congr (Ioi_ae_eq_Ici' (scaleMeasure_singleton T)).symm
      _ ≤ ∫⁻ s in Ioi T, (ENNReal.ofReal s)⁻¹ ^ (m + 2 + 2) *
            (ENNReal.ofReal (2 * ℓ * ρ) ^ 2 * μ G) ∂scaleMeasure :=
          setLIntegral_mono ((measurable_inv_pow_ofReal _).mul_const _) hpt
      _ = ENNReal.ofReal ((T ^ (m + 2 + 2))⁻¹ / ((m + 2 + 2 : ℕ) : ℝ)) *
            (ENNReal.ofReal (2 * ℓ * ρ) ^ 2 * μ G) := by
          rw [lintegral_mul_const _ (measurable_inv_pow_ofReal _),
            lintegral_inv_pow_Ioi_scaleMeasure (m + 2 + 2) (by omega) hT]
      _ ≤ ENNReal.ofReal ((T ^ (m + 2 + 2))⁻¹ / ((m + 2 + 2 : ℕ) : ℝ)) *
            (ENNReal.ofReal (2 * ℓ * ρ) ^ 2 *
              ENNReal.ofReal (2 ^ (m + 2) * v * (2 * ρ) ^ (m + 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass zero_le) zero_le
      _ = ENNReal.ofReal ((T ^ (m + 2 + 2))⁻¹ / ((m + 2 + 2 : ℕ) : ℝ) *
            ((2 * ℓ * ρ) ^ 2 * (2 ^ (m + 2) * v * (2 * ρ) ^ (m + 2)))) := by
          rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((C' + 1) * (ℓ : ℝ) ^ 2 * (ρ / T) ^ (m + 4) / ((m : ℝ) + 4)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hreal]
          have hsplit : (C' + 1) * (ℓ : ℝ) ^ 2 * (ρ / T) ^ (m + 4) / ((m : ℝ) + 4) =
              C' * ((ℓ : ℝ) ^ 2 * (ρ / T) ^ (m + 4) / ((m : ℝ) + 4)) +
                (ℓ : ℝ) ^ 2 * (ρ / T) ^ (m + 4) / ((m : ℝ) + 4) := by ring
          rw [hsplit]
          linarith

end ParabolicRectifiability
