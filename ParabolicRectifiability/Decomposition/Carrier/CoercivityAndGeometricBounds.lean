import ParabolicRectifiability.Decomposition.Carrier.Definitions
import ParabolicRectifiability.Geometry.CovarianceComparison
import ParabolicRectifiability.Measure.BetaLaws
import Mathlib.MeasureTheory.Covering.Vitali

/-! # Carrier coercivity and uniform geometric bounds

Uniform geometric estimates for the regular vertical carrier.

* `fit_lower_bound_of_tube_proof`: under lower mass and upper growth, the fit of
  every vertical model over a spatial `(m-1)`-plane is at least `c₁ r^{m+4}`. The
  tube estimate uses intrinsic parabolic volume on the projected base, with the
  source measure unchanged.
* `planeComparison_sq_le_of_coercive_proof` and
  `planeComparison_sq_le_of_lower_mass_proof`: two spatial `m`-planes are close on
  `P(z,r)` in terms of their two fits. The covariance comparison includes both
  sizes of the minimum rank-`m` error.
* `isCarrierFamily_isCoherent_proof` and `isCarrierFamily_hasCenterHeight_proof`:
  coherence and center heights of the carrier family. Both take the beta point
  bound (`β(z,s)²` controlled by `∫_s^{2s} β(z,r)² dr/r`) as an explicit hypothesis.
-/

noncomputable section
namespace ParabolicRectifiability
open MeasureTheory Set
open scoped ENNReal NNReal

private theorem intrinsic_ball_volume {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p : SubspaceSpace W) {r : ℝ} (hr : 0 < r) :
    intrinsicParabolicVolume W (Metric.ball p r) =
      (2 * omega (Module.finrank ℝ W)) * ENNReal.ofReal r ^ (Module.finrank ℝ W + 2) := by
  let e := subspaceParabolicIsometry W
  have h := (subspaceParabolic_measurePreserving W).measure_preimage_equiv
    (Metric.ball (e p) r)
  have he : subspaceParabolicMeasurableEquiv W ⁻¹' Metric.ball (e p) r =
      Metric.ball p r := e.isometry.preimage_ball p r
  rw [he] at h
  exact h.trans (parabolicVolume_ball (e p) r hr)

/-- A disjoint selection controls the total intrinsic radius cost, while its
fivefold enlargements cover the base ball. The dimension is the intrinsic rank
plus two, including the rank-zero base. -/
private theorem intrinsic_ball_cover {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p : SubspaceSpace W) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r) :
    ∃ u : Set (SubspaceSpace W), u.Countable ∧ u ⊆ Metric.ball p r ∧
      (Metric.ball p r ⊆ ⋃ q : u, Metric.ball (q : SubspaceSpace W) (5 * δ)) ∧
      (∑' _q : u, ENNReal.ofReal δ ^ (Module.finrank ℝ W + 2)) ≤
        ENNReal.ofReal (2 * r) ^ (Module.finrank ℝ W + 2) := by
  classical
  obtain ⟨u, hu, hd, hc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    (Metric.ball p r) id (fun _ => δ) δ (fun _ _ => le_rfl) 5 (by norm_num)
  have hcount : u.Countable := hd.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
    (fun q _ => ⟨q, Metric.mem_ball_self hδ⟩)
  let : Countable u := hcount.to_subtype
  refine ⟨u, hcount, hu, ?_, ?_⟩
  · intro q hq
    obtain ⟨b, hb, hqb⟩ := hc q hq
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, hqb (Metric.mem_ball_self hδ)⟩
  · have hsub : (⋃ q : u, Metric.ball (q : SubspaceSpace W) δ) ⊆ Metric.ball p (2 * r) := by
      intro x hx
      obtain ⟨q, hq⟩ := mem_iUnion.mp hx
      have hqp := Metric.mem_ball.mp (hu q.property)
      have hxq := Metric.mem_ball.mp hq
      have htri := dist_triangle x (q : SubspaceSpace W) p
      exact Metric.mem_ball.mpr (by linarith)
    have hbound := measure_mono (μ := intrinsicParabolicVolume W) hsub
    have hdisj : Pairwise fun q q' : u =>
        Disjoint (Metric.ball (q : SubspaceSpace W) δ) (Metric.ball (q' : SubspaceSpace W) δ) :=
      hd.subtype _ _
    have hvol : intrinsicParabolicVolume W (⋃ q : u, Metric.ball (q : SubspaceSpace W) δ) =
        ∑' q : u, intrinsicParabolicVolume W (Metric.ball (q : SubspaceSpace W) δ) :=
      measure_iUnion hdisj (fun _ => measurableSet_ball)
    rw [hvol, intrinsic_ball_volume W p (by positivity)] at hbound
    simp only [intrinsic_ball_volume W _ hδ, ENNReal.tsum_mul_left] at hbound
    exact (ENNReal.mul_le_mul_iff_right
      (show (2 * omega (Module.finrank ℝ W)) ≠ 0 from
        mul_ne_zero (by norm_num) (omega_pos _).ne')
      (ENNReal.mul_ne_top (by norm_num) (omega_lt_top _).ne)).mp hbound

private def planeBasePoint {n l : ℕ} (L : AffineSpatialPlane n l) (z : Space n) :
    SubspaceSpace L.direction := (L.direction.orthogonalProjectionOnto z.1, z.2)

private def planeBaseLift {n l : ℕ} (L : AffineSpatialPlane n l)
    (q : SubspaceSpace L.direction) : Space n := (L.anchor + q.1, q.2)

private theorem planeBasePoint_dist_le {n l : ℕ} (L : AffineSpatialPlane n l)
    (z w : Space n) : dist (planeBasePoint L z) (planeBasePoint L w) ≤ dist z w := by
  change max (dist (L.direction.orthogonalProjectionOnto z.1)
    (L.direction.orthogonalProjectionOnto w.1)) (dist z.2 w.2) ≤
      max (dist z.1 w.1) (dist z.2 w.2)
  apply max_le_max _ le_rfl
  simpa only [NNReal.coe_one, one_mul] using
    L.direction.lipschitzWith_orthogonalProjectionOnto.dist_le_mul z.1 w.1

private theorem planeBaseLift_dist {n l : ℕ} (L : AffineSpatialPlane n l)
    (p q : SubspaceSpace L.direction) : dist (planeBaseLift L p) (planeBaseLift L q) =
      dist p q := by
  change max (dist (L.anchor + (p.1 : Spatial n)) (L.anchor + (q.1 : Spatial n)))
    (dist p.2 q.2) = max (dist p.1 q.1) (dist p.2 q.2)
  rw [dist_add_left]
  rfl

private theorem dist_planeBaseLift {n l : ℕ} (L : AffineSpatialPlane n l)
    (z : Space n) : dist z (planeBaseLift L (planeBasePoint L z)) =
      ‖z.1 - L.projection z.1‖ := by
  change max (dist z.1 (L.projection z.1)) (dist z.2 z.2) = _
  rw [dist_self, max_eq_left dist_nonneg, dist_eq_norm]

/-- The tube over an affine spatial plane inherits a countable cover with the
intrinsic exponent. No growth hypothesis on the projected measure is used. -/
private theorem vertical_tube_cover {n l : ℕ} (L : AffineSpatialPlane n l)
    (z : Space n) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r) :
    ∃ u : Set (SubspaceSpace L.direction), u.Countable ∧
      {w ∈ Metric.ball z r | ‖w.1 - L.projection w.1‖ < δ} ⊆
        ⋃ q : u, Metric.ball (planeBaseLift L q) (6 * δ) ∧
      (∑' _q : u, ENNReal.ofReal δ ^ (l + 2)) ≤ ENNReal.ofReal (2 * r) ^ (l + 2) := by
  obtain ⟨u, hcount, _, hcover, hcost⟩ :=
    intrinsic_ball_cover L.direction (planeBasePoint L z) hr hδ hδr
  refine ⟨u, hcount, ?_, ?_⟩
  · intro w hw
    have hp : planeBasePoint L w ∈ Metric.ball (planeBasePoint L z) r :=
      Metric.mem_ball.mpr ((planeBasePoint_dist_le L w z).trans_lt hw.1)
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover hp)
    refine mem_iUnion.mpr ⟨q, Metric.mem_ball.mpr ?_⟩
    have htri := dist_triangle w (planeBaseLift L (planeBasePoint L w)) (planeBaseLift L q)
    rw [dist_planeBaseLift, planeBaseLift_dist] at htri
    have hdist := Metric.mem_ball.mp hq
    linarith [hw.2]
  · simpa only [L.rank_eq] using hcost

private theorem vertical_tube_mass {n l : ℕ} (ν : Measure (Space n))
    (L : AffineSpatialPlane n l) (z : Space n) {r δ U : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hδr : 6 * δ ≤ r) (hU : 0 ≤ U)
    (hgrowth : HasUpperGrowthUpTo ν (l + 3) U r) :
    ν {w ∈ Metric.ball z r | ‖w.1 - L.projection w.1‖ < δ} ≤
      ENNReal.ofReal (U * 6 ^ (l + 3) * δ * (2 * r) ^ (l + 2)) := by
  obtain ⟨u, hcount, hcover, hcost⟩ := vertical_tube_cover L z hr hδ (by linarith)
  let : Countable u := hcount.to_subtype
  have hbound (q : u) : ν (Metric.ball (planeBaseLift L q) (6 * δ)) ≤
      ENNReal.ofReal (U * 6 ^ (l + 3) * δ) * ENNReal.ofReal δ ^ (l + 2) := by
    refine (hgrowth _ _ (by positivity) hδr).trans_eq ?_
    rw [← ENNReal.ofReal_pow hδ.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow, show l + 3 = (l + 2) + 1 by omega, pow_succ δ]
    ring
  calc
    _ ≤ ν (⋃ q : u, Metric.ball (planeBaseLift L q) (6 * δ)) := measure_mono hcover
    _ ≤ ∑' q : u, ν (Metric.ball (planeBaseLift L q) (6 * δ)) := measure_iUnion_le _
    _ ≤ ∑' _q : u, ENNReal.ofReal (U * 6 ^ (l + 3) * δ) *
        ENNReal.ofReal δ ^ (l + 2) := ENNReal.tsum_le_tsum hbound
    _ = ENNReal.ofReal (U * 6 ^ (l + 3) * δ) *
        ∑' _q : u, ENNReal.ofReal δ ^ (l + 2) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (U * 6 ^ (l + 3) * δ) * ENNReal.ofReal (2 * r) ^ (l + 2) :=
      mul_le_mul_right hcost _
    _ = _ := by rw [← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]

private theorem vertical_modelCost_eq {n l : ℕ} (L : AffineSpatialPlane n l)
    (w : Space n) : modelCost (verticalPlaneModel L) w =
      ENNReal.ofReal (‖w.1 - L.projection w.1‖ ^ 2) := by
  rw [modelCost_eq_ofReal]
  change ENNReal.ofReal (‖w.1 - L.direction.starProjection w.1 - L.anchor‖ ^ 2) = _
  rw [← L.residual]

/-- Splitting off a tube gives an error lower bound without any regularity or
finiteness assumption on the source. -/
private theorem fit_add_tube_mass_lower_bound {n l : ℕ} (ν : Measure (Space n))
    (L : AffineSpatialPlane n l) (z : Space n) (r : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ENNReal.ofReal (δ ^ 2) * ν (Metric.ball z r) ≤
      fit ν (verticalPlaneModel L) z r + ENNReal.ofReal (δ ^ 2) *
        ν {w ∈ Metric.ball z r | ‖w.1 - L.projection w.1‖ < δ} := by
  let B := Metric.ball z r
  let A := {w ∈ B | ‖w.1 - L.projection w.1‖ < δ}
  have hsplit : ν B ≤ ν (B \ A) + ν A :=
    (measure_mono (show B ⊆ (B \ A) ∪ A by intro w hw; by_cases h : w ∈ A <;> simp [hw, h])).trans
      (measure_union_le _ _)
  have hout : ENNReal.ofReal (δ ^ 2) * ν (B \ A) ≤ fit ν (verticalPlaneModel L) z r := by
    rw [← setLIntegral_const]
    refine (setLIntegral_mono (measurable_modelCost _) ?_).trans
      (lintegral_mono_set sdiff_subset)
    intro w hw
    rw [vertical_modelCost_eq]
    apply ENNReal.ofReal_le_ofReal
    have hnot : δ ≤ ‖w.1 - L.projection w.1‖ := by
      by_contra! h
      exact hw.2 ⟨hw.1, h⟩
    exact pow_le_pow_left₀ hδ hnot 2
  calc
    _ ≤ ENNReal.ofReal (δ ^ 2) * (ν (B \ A) + ν A) := mul_le_mul_right hsplit _
    _ = ENNReal.ofReal (δ ^ 2) * ν (B \ A) + ENNReal.ofReal (δ ^ 2) * ν A := mul_add _ _ _
    _ ≤ _ := add_le_add hout le_rfl

/-- Coercivity: on a ball with lower mass `a r^{m+2}` and upper growth `U`, every
vertical model over a spatial `(m-1)`-plane has fit at least `c₁ r^{m+4}`. -/
theorem fit_lower_bound_of_tube_proof (n m : ℕ) (hm : 1 ≤ m) {a U : ℝ} (ha : 0 < a)
    (hU : 0 ≤ U) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (ν : Measure (Space n)) (z : Space n) (r : ℝ), 0 < r →
      ENNReal.ofReal (a * r ^ (m + 2)) ≤ ν (Metric.ball z r) →
      HasUpperGrowthUpTo ν (m + 2) U r →
      ∀ L : AffineSpatialPlane n (m - 1),
        ENNReal.ofReal (c₁ * r ^ (m + 4)) ≤ fit ν (verticalPlaneModel L) z r := by
  let C : ℝ := 6 ^ (m + 2) * 2 ^ (m + 1)
  have hC : 0 < C := by positivity
  let d : ℝ := min (1 / 6) (a / (2 * (U * C + 1)))
  have hd : 0 < d := lt_min (by norm_num) (div_pos ha (by positivity))
  have hd6 : 6 * d ≤ 1 := by
    have h := min_le_left (1 / 6 : ℝ) (a / (2 * (U * C + 1)))
    change d ≤ 1 / 6 at h
    linarith
  have hdU : U * C * d ≤ a / 2 := by
    have h := min_le_right (1 / 6 : ℝ) (a / (2 * (U * C + 1)))
    change d ≤ a / (2 * (U * C + 1)) at h
    have h' := (le_div_iff₀ (by positivity : 0 < 2 * (U * C + 1))).mp h
    nlinarith
  refine ⟨a * d ^ 2 / 2, by positivity, ?_⟩
  intro ν z r hr hmass hgrowth L
  have hk : m - 1 + 3 = m + 2 := by omega
  have hl : m - 1 + 2 = m + 1 := by omega
  have hδ : 0 < d * r := mul_pos hd hr
  have hδr : 6 * (d * r) ≤ r := by nlinarith [mul_le_mul_of_nonneg_right hd6 hr.le]
  have htube := vertical_tube_mass ν L z hr hδ hδr hU (hk.symm ▸ hgrowth)
  rw [hl, hk] at htube
  have hid : U * 6 ^ (m + 2) * (d * r) * (2 * r) ^ (m + 1) =
      (U * C * d) * r ^ (m + 2) := by
    dsimp [C]
    rw [mul_pow, show m + 2 = (m + 1) + 1 by omega, pow_succ r]
    ring
  rw [hid] at htube
  have htube' : ν {w ∈ Metric.ball z r | ‖w.1 - L.projection w.1‖ < d * r} ≤
      ENNReal.ofReal (a / 2 * r ^ (m + 2)) := htube.trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hdU (pow_nonneg hr.le _)))
  have hhalf : ENNReal.ofReal (a / 2 * r ^ (m + 2)) +
      ENNReal.ofReal (a / 2 * r ^ (m + 2)) ≤ ν (Metric.ball z r) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    convert hmass using 1
    congr 1
    ring
  have h := (mul_le_mul_right hhalf (ENNReal.ofReal ((d * r) ^ 2))).trans
    ((fit_add_tube_mass_lower_bound ν L z r hδ.le).trans
      (add_le_add le_rfl (mul_le_mul_right htube' _)))
  rw [mul_add] at h
  have hh := (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top)).mp h
  have heq : ENNReal.ofReal (a * d ^ 2 / 2 * r ^ (m + 4)) =
      ENNReal.ofReal ((d * r) ^ 2) * ENNReal.ofReal (a / 2 * r ^ (m + 2)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show m + 4 = (m + 2) + 2 by omega, pow_add, mul_pow]
    ring
  exact heq.trans_le hh

private theorem comparison_sq_of_direction_bound {n m : ℕ} (S : SpatialSource n)
    (L L' : AffineSpatialPlane n m) {q : ℝ} (hq : 0 < q)
    (hsize : q ≤ S.mass * S.radius ^ 2)
    (hdir : ‖L.linearProjection - L'.linearProjection‖ ^ 2 ≤
      4 * (S.fittingError L + S.fittingError L') / q) :
    planeComparison S.center.1 S.radius L L' ^ 2 ≤
      36 * (S.fittingError L + S.fittingError L') / q := by
  have hM : 0 < S.mass := pos_of_mul_pos_left (hq.trans_le hsize) (sq_nonneg _)
  have hbar : ‖L.projection S.barycenter - L'.projection S.barycenter‖ ≤
      ‖S.barycenter - L.projection S.barycenter‖ +
        ‖S.barycenter - L'.projection S.barycenter‖ := by
    simpa only [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub
      (L.projection S.barycenter) S.barycenter (L'.projection S.barycenter)
  have hcenter : ‖S.center.1 - S.barycenter‖ ≤ S.radius := by
    simpa only [norm_sub_rev] using S.barycenter_mem_ball hM
  have ha := (L.affine_anchor_inequality L' S.barycenter S.center.1).trans
    (add_le_add hbar (mul_le_mul_of_nonneg_left hcenter (norm_nonneg _)))
  have h := mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr S.radius_pos.le)
  have hcancel : S.radius⁻¹ * (‖S.barycenter - L.projection S.barycenter‖ +
        ‖S.barycenter - L'.projection S.barycenter‖ +
        ‖L.linearProjection - L'.linearProjection‖ * S.radius) =
      S.radius⁻¹ * ‖S.barycenter - L.projection S.barycenter‖ +
      S.radius⁻¹ * ‖S.barycenter - L'.projection S.barycenter‖ +
      ‖L.linearProjection - L'.linearProjection‖ := by field_simp [S.radius_pos.ne']
  rw [hcancel] at h
  have hanchor : S.radius⁻¹ * ‖L.projection S.center.1 - L'.projection S.center.1‖ ≤
      ‖L.linearProjection - L'.linearProjection‖ + Real.sqrt (S.fittingError L / q) +
        Real.sqrt (S.fittingError L' / q) := by
    linarith [S.scaled_barycenter_residual_le_sqrt L q hq hsize,
      S.scaled_barycenter_residual_le_sqrt L' q hq hsize]
  let E := (S.fittingError L + S.fittingError L') / q
  have hE : 0 ≤ E := div_nonneg (add_nonneg (S.fittingError_nonneg L)
    (S.fittingError_nonneg L')) hq.le
  have hD : ‖L.linearProjection - L'.linearProjection‖ ^ 2 ≤ 4 * E := by
    simpa only [E, mul_div_assoc] using hdir
  have hs : Real.sqrt (S.fittingError L / q) + Real.sqrt (S.fittingError L' / q) ≤
      Real.sqrt (2 * E) := by
    have h1 := Real.sq_sqrt (div_nonneg (S.fittingError_nonneg L) hq.le)
    have h2 := Real.sq_sqrt (div_nonneg (S.fittingError_nonneg L') hq.le)
    have h3 := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE)
    have he : S.fittingError L / q + S.fittingError L' / q = E := by dsimp [E]; ring
    nlinarith [sq_nonneg (Real.sqrt (S.fittingError L / q) -
      Real.sqrt (S.fittingError L' / q)), Real.sqrt_nonneg (2 * E),
      Real.sqrt_nonneg (S.fittingError L / q), Real.sqrt_nonneg (S.fittingError L' / q)]
  have htotal : planeComparison S.center.1 S.radius L L' ≤ 6 * Real.sqrt E := by
    have hn := two_mul_add_sqrt_le_six_mul_sqrt (norm_nonneg _) hE hD
    dsimp [planeComparison]
    linarith
  have hsq := pow_le_pow_left₀
    (affineComparison_nonneg L L' S.center.1 S.radius_pos.le) htotal 2
  have he := Real.sq_sqrt hE
  rw [mul_div_assoc]
  change _ ≤ 36 * E
  change planeComparison S.center.1 S.radius L L' ^ 2 ≤ (6 * Real.sqrt E) ^ 2 at hsq
  nlinarith

/-- If the ball has lower mass and every vertical model of one dimension lower fits
badly, then the squared comparison of two spatial `m`-planes on `P(z,r)` is at most
`K r^{-(m+4)}` times the sum of their fits. -/
theorem planeComparison_sq_le_of_coercive_proof (n m : ℕ) (hm : 1 ≤ m) {a c₁ : ℝ}
    (ha : 0 < a) (hc₁ : 0 < c₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ν : Measure (Space n)) (z : Space n) (r : ℝ), 0 < r →
      ENNReal.ofReal (a * r ^ (m + 2)) ≤ ν (Metric.ball z r) → ν (Metric.ball z r) < ⊤ →
      (∀ L : AffineSpatialPlane n (m - 1),
        ENNReal.ofReal (c₁ * r ^ (m + 4)) ≤ fit ν (verticalPlaneModel L) z r) →
      ∀ L L' : AffineSpatialPlane n m,
        ENNReal.ofReal (planeComparison z.1 r L L' ^ 2) ≤
          ENNReal.ofReal (K / r ^ (m + 4)) *
            (fit ν (verticalPlaneModel L) z r + fit ν (verticalPlaneModel L') z r) := by
  let c₀ := min a (c₁ / 2)
  have hc₀ : 0 < c₀ := lt_min ha (by positivity)
  refine ⟨36 / c₀, by positivity, ?_⟩
  intro ν z r hr hmass hfin hcoerce L L'
  have hmn : m ≤ n := AffineSpatialPlane.nonempty_iff.mp ⟨L⟩
  let S : SpatialSource n :=
    { measure := ν.restrict (Metric.ball z r)
      finite := isFiniteMeasure_restrict.mpr hfin.ne
      center := z
      radius := r
      radius_pos := hr
      carried := (ae_restrict_mem measurableSet_ball).mono fun _ hw =>
        Metric.ball_subset_closedBall hw }
  have hfit (l : ℕ) (M : AffineSpatialPlane n l) :
      ENNReal.ofReal (S.fittingError M) = fit ν (verticalPlaneModel M) z r := by
    rw [S.ofReal_fittingError]
    simp only [spatialFittingIntegral, fit, vertical_modelCost_eq]
    rfl
  have hmass_eq : ENNReal.ofReal S.mass = ν (Metric.ball z r) := by
    change ENNReal.ofReal ((ν.restrict (Metric.ball z r)) univ).toReal = _
    rw [Measure.restrict_apply_univ, ENNReal.ofReal_toReal hfin.ne]
  have hmassR : a * r ^ (m + 2) ≤ S.mass := by
    rw [← hmass_eq] at hmass
    exact (ENNReal.ofReal_le_ofReal_iff S.mass_nonneg).mp hmass
  let q := c₀ * r ^ (m + 4)
  have hq : 0 < q := mul_pos hc₀ (pow_pos hr _)
  have hqsize : q ≤ S.mass * S.radius ^ 2 := by
    have hc : c₀ ≤ a := min_le_left _ _
    calc
      q = (c₀ * r ^ (m + 2)) * r ^ 2 := by dsimp [q]; rw [show m + 4 = (m + 2) + 2 by omega, pow_add]; ring
      _ ≤ (a * r ^ (m + 2)) * r ^ 2 := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right hmassR (sq_nonneg r)
  have hcoerceR : 2 * q ≤ S.minimumError (m - 1) := by
    have h := hcoerce (S.topPlane (m - 1) (by omega))
    rw [← hfit, S.minimumError_attained] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff (S.minimumError_nonneg (m - 1) (by omega))).mp h
    have hc : c₀ ≤ c₁ / 2 := min_le_right _ _
    have hh : 2 * q ≤ c₁ * r ^ (m + 4) := by
      dsimp [q]
      nlinarith [mul_le_mul_of_nonneg_right hc (pow_nonneg hr.le (m + 4))]
    exact hh.trans h'
  have hdir : ‖L.linearProjection - L'.linearProjection‖ ^ 2 ≤
      4 * (S.fittingError L + S.fittingError L') / q := by
    by_cases hsmall : S.minimumError m ≤ q
    · have heigen : q ≤ S.eigenvalue ⟨m - 1, by omega⟩ := by
        rw [S.minimumError_step m hm hmn] at hcoerceR
        linarith
      exact S.linearProjection_sub_sq_le hm hmn q hq heigen L L'
    · have hmin : q ≤ S.fittingError L := (le_of_not_ge hsmall).trans
        ((S.minimumError_eq_tail m hmn).trans_le (S.spectralTail_le_fittingError hmn L))
      have hnorm : ‖L.linearProjection - L'.linearProjection‖ ≤ 2 := by
        have h1 := L.direction.starProjection_norm_le
        have h2 := L'.direction.starProjection_norm_le
        change ‖L.linearProjection‖ ≤ 1 at h1
        change ‖L'.linearProjection‖ ≤ 1 at h2
        exact (norm_sub_le _ _).trans (by linarith)
      apply (le_div_iff₀ hq).mpr
      have hs : ‖L.linearProjection - L'.linearProjection‖ ^ 2 ≤ 4 := by
        nlinarith [norm_nonneg (L.linearProjection - L'.linearProjection)]
      nlinarith [mul_le_mul_of_nonneg_right hs hq.le, S.fittingError_nonneg L']
  have hcomp := comparison_sq_of_direction_bound S L L' hq hqsize hdir
  have hid : 36 * (S.fittingError L + S.fittingError L') / q =
      ((36 / c₀) / r ^ (m + 4)) * (S.fittingError L + S.fittingError L') := by
    dsimp [q]
    rw [div_mul_eq_div_div]
    ring
  rw [hid] at hcomp
  have h := ENNReal.ofReal_le_ofReal hcomp
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add
    (S.fittingError_nonneg L) (S.fittingError_nonneg L'), hfit, hfit] at h
  exact h

/-- Plane comparison under lower mass and upper growth, combining
`fit_lower_bound_of_tube_proof` with `planeComparison_sq_le_of_coercive_proof`. -/
theorem planeComparison_sq_le_of_lower_mass_proof (n m : ℕ) (hm : 1 ≤ m) {a U : ℝ}
    (ha : 0 < a) (hU : 0 ≤ U) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ν : Measure (Space n)) (z : Space n) (r : ℝ), 0 < r →
      ENNReal.ofReal (a * r ^ (m + 2)) ≤ ν (Metric.ball z r) →
      HasUpperGrowthUpTo ν (m + 2) U r →
      ∀ L L' : AffineSpatialPlane n m,
        ENNReal.ofReal (planeComparison z.1 r L L' ^ 2) ≤
          ENNReal.ofReal (K / r ^ (m + 4)) *
            (fit ν (verticalPlaneModel L) z r + fit ν (verticalPlaneModel L') z r) := by
  obtain ⟨c₁, hc₁, htube⟩ := fit_lower_bound_of_tube_proof n m hm ha hU
  obtain ⟨K, hK, hcomp⟩ := planeComparison_sq_le_of_coercive_proof n m hm ha hc₁
  refine ⟨K, hK, fun ν z r hr hmass hgrowth => hcomp ν z r hr hmass ?_
    (htube ν z r hr hmass hgrowth)⟩
  exact (hgrowth z r hr le_rfl).trans_lt ENNReal.ofReal_lt_top

section BetaPointInput

variable (beta_point : ∀ {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (z : Space n) {s : ℝ} (_hs : 0 < s),
    betaSq μ k T z s ≤ ENNReal.ofReal (2 ^ (k + 2) / Real.log 2) *
      ∫⁻ r in Icc s (2 * s), betaSq μ k T z r ∂scaleMeasure)

private theorem carrier_scale_pos {n m : ℕ} (Φ : CoherentFamily n m (Space n))
    (hR : 0 < Φ.initialRadius) (j : ℕ) : 0 < Φ.scale j := by
  exact div_pos hR (by positivity)

private theorem carrier_scale_le {n m : ℕ} (Φ : CoherentFamily n m (Space n))
    (hR : 0 ≤ Φ.initialRadius) (j : ℕ) : Φ.scale j ≤ Φ.initialRadius := by
  change Φ.initialRadius / 10 ^ j ≤ Φ.initialRadius
  exact div_le_self hR (one_le_pow₀ (by norm_num))

private theorem carrier_scale_succ {n m : ℕ} (Φ : CoherentFamily n m (Space n))
    (j : ℕ) : 10 * Φ.scale (j + 1) = Φ.scale j := by
  simp only [CoherentFamily.scale, coherentScale, pow_succ]
  rw [div_mul_eq_div_div]
  ring

include beta_point in
private theorem carrier_fit_le {n m : ℕ} {Λ : ℝ} (hΛ : 0 < Λ)
    (η : Measure (Space n)) (F : Set (Space n)) (R T a b : ℝ)
    (Φ : CoherentFamily n m (Space n)) (hR : 0 < R) (hT : (4 * Λ) * R ≤ T)
    (_hb : 0 ≤ b) (hinit : Φ.initialRadius = R) (hf : IsCarrierFamily η F Λ Φ)
    (hp : IsCarrierPiece η (m + 2) a b T F) (j : ℕ) (z : Space n) (hz : z ∈ Φ.index j) :
    fit η (verticalPlaneModel (Φ.plane j z)) z (Λ * Φ.scale j) ≤
      ENNReal.ofReal ((2 ^ (m + 4) / Real.log 2) * b * (Λ * Φ.scale j) ^ (m + 4)) := by
  have hs : 0 < Φ.scale j := carrier_scale_pos Φ (hinit.symm ▸ hR) j
  have hsR : Φ.scale j ≤ R := hinit ▸ carrier_scale_le Φ (hinit.symm ▸ hR.le) j
  have hpos : 0 < Λ * Φ.scale j := mul_pos hΛ hs
  have hsub : Icc (Λ * Φ.scale j) (2 * (Λ * Φ.scale j)) ⊆ Ioo 0 T := by
    intro s h
    constructor
    · exact hpos.trans_le h.1
    · nlinarith [h.2, mul_le_mul_of_nonneg_left hsR hΛ.le]
  have ht : (∫⁻ s in Icc (Λ * Φ.scale j) (2 * (Λ * Φ.scale j)),
      betaSq η (m + 2) .vertical z s ∂scaleMeasure) ≤ ENNReal.ofReal b :=
    (lintegral_mono_set hsub).trans (hp.small_tail z (hf.index_subset j hz))
  have hbeta := (beta_point η (m + 2) .vertical z hpos).trans (mul_le_mul_right ht _)
  have heq : fit η (verticalPlaneModel (Φ.plane j z)) z (Λ * Φ.scale j) =
      ENNReal.ofReal (Λ * Φ.scale j) ^ (m + 4) * betaSq η (m + 2) .vertical z (Λ * Φ.scale j) := by
    rw [betaSq_of_pos _ _ _ _ hpos, ← hf.best_fit j z hz]
    change _ = ENNReal.ofReal (Λ * Φ.scale j) ^ (m + 4) *
      ((ENNReal.ofReal (Λ * Φ.scale j))⁻¹ ^ (m + 4) * _)
    rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hpos).ne'
      ENNReal.ofReal_ne_top, one_pow, one_mul]
  rw [heq]
  refine (mul_le_mul_right hbeta _).trans_eq ?_
  rw [← ENNReal.ofReal_pow hpos.le, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

include beta_point in
/-- The carrier family of a carrier piece with upper growth is coherent, with
coherence error `√(K b)` controlled by the square tail `b`. -/
theorem isCarrierFamily_isCoherent_proof (n m : ℕ) (hm : 1 ≤ m) {Λ : ℝ} (hΛ : 21 ≤ Λ) :
    ∃ A : ℝ, 0 < A ∧ ∀ a U : ℝ, 0 < a → 0 ≤ U → ∃ K : ℝ, 0 < K ∧
      ∀ (η : Measure (Space n)) (F : Set (Space n)) (R T b : ℝ)
        (Φ : CoherentFamily n m (Space n)),
        0 < R → A * R ≤ T → 0 ≤ b → Φ.initialRadius = R → IsCarrierFamily η F Λ Φ →
        HasUpperGrowthUpTo η (m + 2) U T → IsCarrierPiece η (m + 2) a b T F →
        Φ.IsCoherent 1 (Real.sqrt (K * b)) := by
  have hΛpos : 0 < Λ := by linarith
  refine ⟨4 * Λ, by positivity, ?_⟩
  intro a U ha hU
  obtain ⟨K₀, hK₀, hcomparison⟩ := planeComparison_sq_le_of_lower_mass_proof n m hm ha hU
  let C : ℝ := 2 ^ (m + 4) / Real.log 2
  have hC : 0 < C := div_pos (by positivity) (Real.log_pos (by norm_num))
  let Q : ℝ := 2 * K₀ * C * (10 * Λ) ^ (m + 4)
  have hQ : 0 < Q := by positivity
  refine ⟨484 * Q, by positivity, ?_⟩
  intro η F R T b Φ hR hT hb hinit hf hgrowth hp
  have hs (j : ℕ) : 0 < Φ.scale j := carrier_scale_pos Φ (hinit.symm ▸ hR) j
  have hsR (j : ℕ) : Φ.scale j ≤ R := hinit ▸ carrier_scale_le Φ (hinit.symm ▸ hR.le) j
  have hsT (j : ℕ) : Φ.scale j ≤ T := by
    have := hsR j
    nlinarith [mul_le_mul_of_nonneg_right hΛ hR.le]
  have hfit (j : ℕ) (z : Space n) (hz : z ∈ Φ.index j) :=
    carrier_fit_le beta_point hΛpos η F R T a b Φ hR hT hb hinit hf hp j z hz
  have compare (j j' : ℕ) (z w : Space n) (hz : z ∈ Φ.index j) (hw : w ∈ Φ.index j')
      (r : ℝ) (hr : 0 < r) (hrT : r ≤ T)
      (hsub : Metric.ball z r ⊆ Metric.ball z (Λ * Φ.scale j))
      (hsub' : Metric.ball z r ⊆ Metric.ball w (Λ * Φ.scale j'))
      (hscale : Φ.scale j ≤ 10 * r) (hscale' : Φ.scale j' ≤ 10 * r) :
      planeComparison z.1 r (Φ.plane j z) (Φ.plane j' w) ^ 2 ≤ Q * b := by
    have hc := hcomparison η z r hr (hp.lower_mass z (hf.index_subset j hz) r hr hrT)
      (fun q s hs hsr => hgrowth q s hs (hsr.trans hrT)) (Φ.plane j z) (Φ.plane j' w)
    have hleft : fit η (verticalPlaneModel (Φ.plane j z)) z r ≤
        ENNReal.ofReal (C * b * ((10 * Λ) * r) ^ (m + 4)) := by
      refine ((fit_mono_ball η _ hsub).trans (hfit j z hz)).trans ?_
      apply ENNReal.ofReal_le_ofReal
      change C * b * (Λ * Φ.scale j) ^ (m + 4) ≤ _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hb)
      apply pow_le_pow_left₀ (mul_nonneg hΛpos.le (hs j).le)
      nlinarith [mul_le_mul_of_nonneg_left hscale hΛpos.le]
    have hright : fit η (verticalPlaneModel (Φ.plane j' w)) z r ≤
        ENNReal.ofReal (C * b * ((10 * Λ) * r) ^ (m + 4)) := by
      refine ((fit_mono_ball η _ hsub').trans (hfit j' w hw)).trans ?_
      apply ENNReal.ofReal_le_ofReal
      change C * b * (Λ * Φ.scale j') ^ (m + 4) ≤ _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hb)
      apply pow_le_pow_left₀ (mul_nonneg hΛpos.le (hs j').le)
      nlinarith [mul_le_mul_of_nonneg_left hscale' hΛpos.le]
    have hc' := hc.trans (mul_le_mul_right (add_le_add hleft hright) _)
    have heq : ENNReal.ofReal (K₀ / r ^ (m + 4)) *
        (ENNReal.ofReal (C * b * ((10 * Λ) * r) ^ (m + 4)) +
          ENNReal.ofReal (C * b * ((10 * Λ) * r) ^ (m + 4))) = ENNReal.ofReal (Q * b) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [Q]
      rw [mul_pow]
      field_simp [hr.ne']
      ring
    rw [heq] at hc'
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hQ.le hb)).mp hc'
  have hball (z w : Space n) {r s : ℝ} (hr : 0 < r)
      (hnear : dist z w ≤ 20 * s) (hrs : r ≤ s) :
      Metric.ball z r ⊆ Metric.ball w (Λ * s) := by
    intro x hx
    have hxs := dist_triangle x z w
    have hxz := Metric.mem_ball.mp hx
    have hspos : 0 < s := hr.trans_le hrs
    exact Metric.mem_ball.mpr (by nlinarith [mul_le_mul_of_nonneg_right hΛ hspos.le])
  intro N
  refine
    { separated := ?_
      parent_mem := ?_
      parent_dist := ?_
      root := ?_
      same := ?_
      adjacent := ?_ }
  · intro j _ z hz w hw hzw
    simpa only [one_mul, hf.center_eq] using hf.separated j z hz w hw hzw
  · intro j _ z hz
    exact hf.parent_mem j z hz
  · intro j _ z hz
    simpa only [hf.center_eq] using hf.parent_dist j z hz
  · intro z hz
    rw [hf.initial_plane z hz]
    simp only [planeComparison, sub_self, norm_zero, mul_zero, add_zero]
    exact Real.sqrt_nonneg _
  · intro j _ z hz w hw hnear
    rw [hf.center_eq, hf.center_eq] at hnear
    rw [hf.center_eq]
    apply Real.le_sqrt_of_sq_le
    have hc := compare j j z w hz hw (Φ.scale j) (hs j) (hsT j)
      (Metric.ball_subset_ball (by nlinarith [hs j, mul_le_mul_of_nonneg_right hΛ (hs j).le]))
      (hball z w (hs j) hnear le_rfl) (by nlinarith [hs j]) (by nlinarith [hs j])
    exact hc.trans (by nlinarith [mul_nonneg hQ.le hb])
  · intro j _ z hz w hw hnear
    rw [hf.center_eq, hf.center_eq] at hnear
    rw [hf.center_eq]
    have hsc := carrier_scale_succ Φ j
    have hle : Φ.scale (j + 1) ≤ Φ.scale j := by nlinarith [hs (j + 1)]
    have hc := compare (j + 1) j z w hz hw (Φ.scale (j + 1)) (hs (j + 1)) (hsT (j + 1))
      (Metric.ball_subset_ball (by nlinarith [hs (j + 1), mul_le_mul_of_nonneg_right hΛ (hs (j + 1)).le]))
      (hball z w (hs (j + 1)) hnear hle) (by nlinarith [hs (j + 1)]) hsc.symm.le
    have hnorm : ‖w.1 - z.1‖ ≤ 200 * Φ.scale (j + 1) := by
      have hd : ‖w.1 - z.1‖ ≤ dist z w := by
        rw [norm_sub_rev]
        exact le_max_left _ _
      nlinarith
    have hanchor := affineComparison_change_anchor_radius (Φ.plane (j + 1) z) (Φ.plane j w)
      z.1 w.1 (Φ.scale (j + 1)) (Φ.scale j) 200 (hs (j + 1)) (hs j) (by norm_num) hnorm
    have hfactor : 1 + (200 + 1) * Φ.scale (j + 1) / Φ.scale j ≤ 22 := by
      have hd : (200 + 1) * Φ.scale (j + 1) / Φ.scale j ≤ 21 :=
        (div_le_iff₀ (hs j)).mpr (by nlinarith)
      nlinarith
    have hanchor' : planeComparison w.1 (Φ.scale j) (Φ.plane (j + 1) z) (Φ.plane j w) ≤
        22 * planeComparison z.1 (Φ.scale (j + 1)) (Φ.plane (j + 1) z) (Φ.plane j w) :=
      hanchor.trans (mul_le_mul_of_nonneg_right hfactor
        (affineComparison_nonneg _ _ _ (hs (j + 1)).le))
    apply Real.le_sqrt_of_sq_le
    have hsq := pow_le_pow_left₀
      (affineComparison_nonneg _ _ _ (hs j).le) hanchor' 2
    rw [mul_pow] at hsq
    norm_num only [show (22 : ℝ) ^ 2 = 484 by norm_num] at hsq
    exact hsq.trans (by nlinarith)

private theorem fit_lower_of_center_distance {n l : ℕ} (ν : Measure (Space n))
    (L : AffineSpatialPlane n l) (z : Space n) {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s)
    (hD : 2 * t ≤ Metric.infDist z.1 L.toSet) :
    ENNReal.ofReal (t ^ 2) * ν (Metric.ball z t) ≤ fit ν (verticalPlaneModel L) z s := by
  rw [← setLIntegral_const]
  refine (setLIntegral_mono (measurable_modelCost _) ?_).trans
    (lintegral_mono_set (Metric.ball_subset_ball hts))
  intro w hw
  have hd := Metric.infDist_le_infDist_add_dist (x := z.1) (y := w.1) (s := L.toSet)
  have hdist : dist z.1 w.1 ≤ dist w z := by
    rw [dist_comm w z]
    exact le_max_left _ _
  have hw' := Metric.mem_ball.mp hw
  have hlower : t ≤ Metric.infDist w.1 L.toSet := by linarith
  rw [vertical_modelCost_eq, ← L.spatial_infDist_eq]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht hlower 2)

include beta_point in
/-- When the square tail `b` is small compared with the lower mass `a`, every center
`z_{j,a}` of the carrier family satisfies `dist(x_{j,a}, L_{j,a}) ≤ κ r_j`. -/
theorem isCarrierFamily_hasCenterHeight_proof (n m : ℕ) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
      ∀ (η : Measure (Space n)) (F : Set (Space n)) (R T a b κ : ℝ)
        (Φ : CoherentFamily n m (Space n)),
        0 < R → A * R ≤ T → 0 < a → 0 ≤ b → 0 < κ → Φ.initialRadius = R →
        IsCarrierFamily η F Λ Φ → IsCarrierPiece η (m + 2) a b T F →
        C * Λ ^ (m + 4) * b < a → C * (2 * Λ) ^ (m + 4) * b ≤ κ ^ (m + 4) * a →
        Φ.HasCenterHeight κ := by
  let C : ℝ := 2 ^ (m + 4) / Real.log 2
  have hC : 0 < C := div_pos (by positivity) (Real.log_pos (by norm_num))
  have hΛpos : 0 < Λ := by linarith
  refine ⟨4 * Λ, C, by positivity, hC, ?_⟩
  intro η F R T a b κ Φ hR hT ha hb hκ hinit hf hp hsmall hheight j z hz
  have hs : 0 < Φ.scale j := carrier_scale_pos Φ (hinit.symm ▸ hR) j
  have hsR : Φ.scale j ≤ R := hinit ▸ carrier_scale_le Φ (hinit.symm ▸ hR.le) j
  have hsT : Φ.scale j ≤ T := by nlinarith [mul_le_mul_of_nonneg_right hΛ hR.le]
  let L := Φ.plane j z
  let D := Metric.infDist z.1 L.toSet
  have hD : 0 ≤ D := Metric.infDist_nonneg
  have hfit := carrier_fit_le beta_point hΛpos η F R T a b Φ hR hT hb hinit hf hp j z hz
  change fit η (verticalPlaneModel L) z (Λ * Φ.scale j) ≤
    ENNReal.ofReal (C * b * (Λ * Φ.scale j) ^ (m + 4)) at hfit
  have hlower (t : ℝ) (ht : 0 < t) (hts : t ≤ Φ.scale j) (htD : 2 * t ≤ D) :
      a * t ^ (m + 4) ≤ C * b * (Λ * Φ.scale j) ^ (m + 4) := by
    have hm := hp.lower_mass z (hf.index_subset j hz) t ht (hts.trans hsT)
    have h := (mul_le_mul_right hm (ENNReal.ofReal (t ^ 2))).trans
      (fit_lower_of_center_distance η L z (s := Λ * Φ.scale j) ht.le
        (by nlinarith [mul_le_mul_of_nonneg_right hΛ hs.le]) htD)
    have heq : ENNReal.ofReal (t ^ 2) * ENNReal.ofReal (a * t ^ (m + 2)) =
        ENNReal.ofReal (a * t ^ (m + 4)) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg t)]
      congr 1
      rw [show m + 4 = (m + 2) + 2 by omega, pow_add]
      ring
    rw [heq] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (h.trans hfit)
  have hDtwo : D ≤ 2 * Φ.scale j := by
    by_contra! h
    have he := hlower (Φ.scale j) hs le_rfl h.le
    rw [mul_pow] at he
    have hcancel : a ≤ C * Λ ^ (m + 4) * b := by
      apply (mul_le_mul_iff_left₀ (pow_pos hs (m + 4))).mp
      nlinarith
    exact (not_le_of_gt hsmall) hcancel
  rw [hf.center_eq]
  change D ≤ κ * Φ.scale j
  by_cases hzero : D = 0
  · rw [hzero]
    positivity
  have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hzero)
  have he := hlower (D / 2) (by positivity) (by linarith) (by linarith)
  have he' : a * D ^ (m + 4) ≤ C * (2 * Λ) ^ (m + 4) * b * Φ.scale j ^ (m + 4) := by
    have hh := mul_le_mul_of_nonneg_right he (show 0 ≤ (2 : ℝ) ^ (m + 4) by positivity)
    rw [div_pow] at hh
    have hid : a * (D ^ (m + 4) / 2 ^ (m + 4)) * 2 ^ (m + 4) =
        a * D ^ (m + 4) := by field_simp
    rw [hid] at hh
    simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hh
  have hpows : D ^ (m + 4) ≤ (κ * Φ.scale j) ^ (m + 4) := by
    have hh := he'.trans (mul_le_mul_of_nonneg_right hheight (pow_nonneg hs.le _))
    rw [mul_pow]
    apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith
  exact (pow_le_pow_iff_left₀ hD (mul_nonneg hκ.le hs.le) (by omega : m + 4 ≠ 0)).mp hpows

end BetaPointInput

end ParabolicRectifiability
