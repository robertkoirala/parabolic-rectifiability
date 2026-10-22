import ParabolicRectifiability.Decomposition.Carrier.Definitions
import ParabolicRectifiability.Measure.BetaLaws
import ParabolicRectifiability.Measure.FittingMinimum

/-! # Regular vertical carrier: beta point bound, rank zero, countable unions and nets

Proofs of six intermediate statements in the construction of the regular vertical
carrier, each under the name `<statement name>_proof`.

* `betaSq_le_lintegral_Icc_proof` (beta point bound): ball monotonicity gives `β(z,s)² ≤ 2^{k+2} β(z,r)²` for `s ≤ r ≤ 2s`; integrating
  over `[s,2s]` against `dr/r`, whose mass is exactly `log 2`, gives the bound.
* `rank_zero_partial_time_graph_proof` (spatial rank zero): the two-ball
  estimate `inf_q ∫_{P(z,2d)} |y-q|² dη ≥ a h⁴/1024` and the beta point bound on
  `[2d,4d]` give `h ≤ ℓ d`; with `ℓ < 1` the time projection is injective and the
  spatial part is a parabolic `ℓ`-Lipschitz function of time.
* `hasRegularVerticalGraphCover_of_iUnion_proof`: countable reindexing into a
  subset of `ℕ` and countable subadditivity for the null exception.
* `exists_maximal_separated_finset_proof`, `exists_verticalPlane_bestFit_proof`
  and `exists_isCarrierFamily_proof`: maximal finite nets by a maximal-cardinality
  argument, best fitted planes by the global attainment theorem for the source restricted to the ball, and the
  carrier family assembled from them.

The source `η` is never replaced: fits, betas and square tails are those of the
unchanged measure.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal

/-! ## The beta point bound -/

/-- The scale measure of a dyadic annulus `[s, 2s]` is exactly `log 2`. -/
theorem scaleMeasure_Icc_two_mul {s : ℝ} (hs : 0 < s) :
    scaleMeasure (Icc s (2 * s)) = ENNReal.ofReal (Real.log 2) := by
  have hsub : Icc s (2 * s) ⊆ Ioi 0 := fun r hr => hs.trans_le hr.1
  have hcont : ContinuousOn (fun r : ℝ => 1 / r) (Icc s (2 * s)) :=
    continuousOn_const.div continuousOn_id fun r hr => (hs.trans_le hr.1).ne'
  have hint : IntegrableOn (fun r : ℝ => 1 / r) (Icc s (2 * s)) :=
    hcont.integrableOn_compact isCompact_Icc
  rw [scaleMeasure_apply _ measurableSet_Icc, inter_eq_left.mpr hsub]
  calc
    _ = ENNReal.ofReal (∫ r in Icc s (2 * s), 1 / r) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hint
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (one_div_pos.mpr (hs.trans_le hr.1)).le
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
        integral_one_div_of_pos hs (by linarith), mul_div_assoc, div_self hs.ne', mul_one]

/-- **Beta point bound.** For every source, family
and positive radius, `β(z,s)² ≤ (2^{k+2} / log 2) ∫_s^{2s} β(z,r)² dr/r`. -/
theorem betaSq_le_lintegral_Icc_proof {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (z : Space n) {s : ℝ} (hs : 0 < s) :
    betaSq μ k T z s ≤ ENNReal.ofReal (2 ^ (k + 2) / Real.log 2) *
      ∫⁻ r in Icc s (2 * s), betaSq μ k T z r ∂scaleMeasure := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpt : ∀ r ∈ Icc s (2 * s),
      betaSq μ k T z s ≤ ENNReal.ofReal (2 ^ (k + 2)) * betaSq μ k T z r := by
    intro r hr
    have hr0 : 0 < r := hs.trans_le hr.1
    refine (betaSq_le_of_ball_subset μ k T hs hr0 (Metric.ball_subset_ball hr.1)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    rw [← ENNReal.ofReal_pow (div_pos hr0 hs).le]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (div_pos hr0 hs).le ?_ _)
    rw [div_le_iff₀ hs]
    exact hr.2
  have hint : betaSq μ k T z s * ENNReal.ofReal (Real.log 2) ≤
      ENNReal.ofReal (2 ^ (k + 2)) * ∫⁻ r in Icc s (2 * s), betaSq μ k T z r ∂scaleMeasure := by
    rw [← scaleMeasure_Icc_two_mul hs, ← setLIntegral_const,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' measurableSet_Icc hpt
  have hinv : (0 : ℝ) ≤ 1 / Real.log 2 := (one_div_pos.mpr hlog).le
  calc betaSq μ k T z s
      = ENNReal.ofReal (1 / Real.log 2) *
          (betaSq μ k T z s * ENNReal.ofReal (Real.log 2)) := by
        rw [mul_comm (betaSq μ k T z s), ← mul_assoc, ← ENNReal.ofReal_mul hinv,
          one_div_mul_cancel hlog.ne', ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (1 / Real.log 2) * (ENNReal.ofReal (2 ^ (k + 2)) *
          ∫⁻ r in Icc s (2 * s), betaSq μ k T z r ∂scaleMeasure) :=
        mul_le_mul_of_nonneg_left hint zero_le
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hinv,
          show 1 / Real.log 2 * 2 ^ (k + 2) = 2 ^ (k + 2) / Real.log 2 by ring]

/-! ## Spatial rank zero -/

/-- Every vertical model of dimension two is the vertical line over one spatial
point: its squared distance is the squared spatial distance to that point. -/
private theorem rankZero_modelCost {n : ℕ} (L : Models n 2 .vertical) :
    ∃ q : Spatial n, ∀ y : Space n, modelCost L y = ENNReal.ofReal (‖y.1 - q‖ ^ 2) := by
  change VerticalModel n 2 at L
  have hr : L.spatialRank = 0 := by have := L.rank_eq; omega
  have hbot : L.spatial.direction = ⊥ := by
    rw [← Submodule.finrank_eq_zero, L.spatial.rank_eq]
    exact hr
  refine ⟨L.spatial.anchor, fun y => ?_⟩
  rcases y with ⟨x, ⟨t⟩⟩
  have h0 : L.spatial.direction.starProjection x = 0 :=
    (Submodule.eq_bot_iff _).mp hbot _ (L.spatial.direction.starProjection_apply_mem x)
  have hc := L.modelCost_point x t
  rw [h0, sub_zero] at hc
  exact hc

/-- A ball whose spatial center is far from `q` contributes its mass times the
squared spatial gap to the fit of the vertical line over `q`. -/
private theorem fit_rankZero_ball_lower {n : ℕ} (η : Measure (Space n))
    (L : Models n 2 .vertical) (q : Spatial n)
    (hq : ∀ y : Space n, modelCost L y = ENNReal.ofReal (‖y.1 - q‖ ^ 2))
    {z y : Space n} {R ρ δ : ℝ} (hδ : 0 ≤ δ) (hfar : δ + ρ ≤ ‖y.1 - q‖)
    (hsub : Metric.ball y ρ ⊆ Metric.ball z R) :
    ENNReal.ofReal (δ ^ 2) * η (Metric.ball y ρ) ≤ fit η L z R := by
  rw [← setLIntegral_const]
  refine (setLIntegral_mono' measurableSet_ball fun u hu => ?_).trans (lintegral_mono_set hsub)
  rw [hq u]
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hδ ?_ 2)
  have h1 : dist u.1 y.1 ≤ dist u y := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have h2 := Metric.mem_ball.mp hu
  have h3 := norm_sub_le_norm_sub_add_norm_sub y.1 u.1 q
  have h4 : ‖y.1 - u.1‖ = dist u.1 y.1 := by rw [dist_comm, dist_eq_norm]
  linarith

/-- The two-ball estimate: two source balls of radius `h/8` around points at spatial
distance `h` give every vertical line a fit at least `(h/4)²` times their mass. -/
private theorem two_ball_fit_lower {n : ℕ} (η : Measure (Space n)) (L : Models n 2 .vertical)
    {z w : Space n} {R c h : ℝ} (hh : ‖z.1 - w.1‖ = h) (hpos : 0 < h)
    (hz : Metric.ball z (h / 8) ⊆ Metric.ball z R)
    (hw : Metric.ball w (h / 8) ⊆ Metric.ball z R)
    (hmz : ENNReal.ofReal c ≤ η (Metric.ball z (h / 8)))
    (hmw : ENNReal.ofReal c ≤ η (Metric.ball w (h / 8))) :
    ENNReal.ofReal ((h / 4) ^ 2) * ENNReal.ofReal c ≤ fit η L z R := by
  obtain ⟨q, hq⟩ := rankZero_modelCost L
  have htri : h ≤ ‖z.1 - q‖ + ‖w.1 - q‖ := by
    rw [← hh, ← norm_sub_rev q w.1]
    exact norm_sub_le_norm_sub_add_norm_sub z.1 q w.1
  have hδ : (0 : ℝ) ≤ h / 4 := by linarith
  rcases le_total (h / 2) ‖z.1 - q‖ with hfar | hfar
  · exact (mul_le_mul_of_nonneg_left hmz zero_le).trans
      (fit_rankZero_ball_lower η L q hq hδ (by linarith) hz)
  · exact (mul_le_mul_of_nonneg_left hmw zero_le).trans
      (fit_rankZero_ball_lower η L q hq hδ (by linarith) hw)

/-- The rank-zero key estimate: on a carrier piece with `C b ≤ ℓ⁴ a`, two points
`z, w` with `4 d_P(z,w) < T` satisfy `|x_z - x_w| ≤ ℓ d_P(z,w)`. -/
private theorem rank_zero_spatial_le {n : ℕ} (η : Measure (Space n)) (F : Set (Space n))
    {T a b ℓ : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hℓ : 0 ≤ ℓ)
    (hp : IsCarrierPiece η 2 a b T F) (hC : 2 ^ 18 / Real.log 2 * b ≤ ℓ ^ 4 * a)
    {z w : Space n} (hz : z ∈ F) (hw : w ∈ F) (hT : 4 * dist z w < T) :
    ‖z.1 - w.1‖ ≤ ℓ * dist z w := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨h, hh⟩ : ∃ h, ‖z.1 - w.1‖ = h := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, dist z w = d := ⟨_, rfl⟩
  rw [hh, hd]
  rw [hd] at hT
  have hd0 : 0 ≤ d := by rw [← hd]; exact dist_nonneg
  have hhd : h ≤ d := by
    rw [← hh, ← hd, Prod.dist_eq, dist_eq_norm]
    exact le_max_left _ _
  rcases (show (0 : ℝ) ≤ h by rw [← hh]; exact norm_nonneg _).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg hℓ hd0
  have hdpos : 0 < d := hpos.trans_le hhd
  have hr : 0 < h / 8 := by linarith
  have hrT : h / 8 ≤ T := by linarith
  have hmz := hp.lower_mass z hz (h / 8) hr hrT
  have hmw := hp.lower_mass w hw (h / 8) hr hrT
  have hsubz : Metric.ball z (h / 8) ⊆ Metric.ball z (2 * d) :=
    Metric.ball_subset_ball (by linarith)
  have hsubw : Metric.ball w (h / 8) ⊆ Metric.ball z (2 * d) := by
    intro u hu
    rw [Metric.mem_ball] at hu ⊢
    have h1 := dist_triangle u w z
    rw [dist_comm w z, hd] at h1
    linarith
  have hinf : ENNReal.ofReal ((h / 4) ^ 2) * ENNReal.ofReal (a * (h / 8) ^ 2) ≤
      ⨅ L : Models n 2 .vertical, fit η L z (2 * d) :=
    le_iInf fun L => two_ball_fit_lower η L hh hpos hsubz hsubw hmz hmw
  have hs : 0 < 2 * d := by linarith
  have hbeta := betaSq_le_lintegral_Icc_proof η 2 .vertical z hs
  have htail : ∫⁻ r in Icc (2 * d) (2 * (2 * d)), betaSq η 2 .vertical z r ∂scaleMeasure ≤
      ENNReal.ofReal b := by
    refine (lintegral_mono_set ?_).trans (hp.small_tail z hz)
    intro r hr'
    exact ⟨hs.trans_le hr'.1, by linarith [hr'.2]⟩
  have heq : ⨅ L : Models n 2 .vertical, fit η L z (2 * d) =
      ENNReal.ofReal (2 * d) ^ (2 + 2) * betaSq η 2 .vertical z (2 * d) := by
    rw [betaSq_of_pos _ _ _ _ hs, ← mul_assoc, ← mul_pow,
      ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top, one_pow,
      one_mul]
  have hA : ENNReal.ofReal ((h / 4) ^ 2) * ENNReal.ofReal (a * (h / 8) ^ 2) ≤
      ENNReal.ofReal (2 * d) ^ (2 + 2) *
        (ENNReal.ofReal (2 ^ (2 + 2) / Real.log 2) * ENNReal.ofReal b) := by
    refine (hinf.trans_eq heq).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
    exact hbeta.trans (mul_le_mul_of_nonneg_left htail zero_le)
  have hcoef : (0 : ℝ) ≤ 2 ^ (2 + 2) / Real.log 2 :=
    div_nonneg (pow_nonneg zero_le_two _) hlog.le
  have hB : ENNReal.ofReal ((h / 4) ^ 2 * (a * (h / 8) ^ 2)) ≤
      ENNReal.ofReal ((2 * d) ^ (2 + 2) * (2 ^ (2 + 2) / Real.log 2 * b)) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (pow_nonneg hs.le _),
      ENNReal.ofReal_mul hcoef, ENNReal.ofReal_pow hs.le]
    exact hA
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (pow_nonneg hs.le _) (mul_nonneg hcoef hb))).mp hB
  have hkey : a * h ^ 4 ≤ a * (ℓ * d) ^ 4 := by
    calc a * h ^ 4 = 1024 * ((h / 4) ^ 2 * (a * (h / 8) ^ 2)) := by ring
      _ ≤ 1024 * ((2 * d) ^ (2 + 2) * (2 ^ (2 + 2) / Real.log 2 * b)) :=
        mul_le_mul_of_nonneg_left hreal (by norm_num)
      _ = 2 ^ 18 / Real.log 2 * b * d ^ 4 := by ring
      _ ≤ ℓ ^ 4 * a * d ^ 4 := mul_le_mul_of_nonneg_right hC (pow_nonneg hd0 _)
      _ = a * (ℓ * d) ^ 4 := by ring
  have h4 : h ^ 4 ≤ (ℓ * d) ^ 4 := le_of_mul_le_mul_left hkey ha
  exact (pow_le_pow_iff_left₀ hpos.le (mul_nonneg hℓ hd0) (by norm_num)).mp h4

/-- The rank-zero base `W = {0}`. -/
private abbrev zeroBase (n : ℕ) : Submodule ℝ (Spatial n) := ⊥

/-- A set whose spatial part is a parabolic `ℓ`-Lipschitz function of time is the
lift of a partial map on the rank-zero base. -/
private theorem exists_rankZero_lift {n : ℕ} (F : Set (Space n)) (ℓ : ℝ≥0)
    (htime : ∀ z ∈ F, ∀ w ∈ F, ‖z.1 - w.1‖ ≤ ℓ * dist z.2 w.2) :
    ∃ (W : Submodule ℝ (Spatial n)) (D : Set (SubspaceSpace W))
      (g : SubspaceSpace W → W.orthogonal),
      Module.finrank ℝ W = 0 ∧ LipschitzOnWith ℓ g D ∧ F = verticalLift W g '' D := by
  have hinj : ∀ z ∈ F, ∀ w ∈ F, z.2 = w.2 → z = w := by
    intro z hz w hw h2
    have h := htime z hz w hw
    rw [h2, dist_self, mul_zero] at h
    exact Prod.ext (sub_eq_zero.mp (norm_le_zero_iff.mp h)) h2
  have : Nonempty (Space n) := ⟨point 0 0⟩
  have hWo : ∀ v : Spatial n, v ∈ (zeroBase n)ᗮ := fun v => by
    rw [zeroBase, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  obtain ⟨g, hg⟩ : ∃ g : SubspaceSpace (zeroBase n) → (zeroBase n).orthogonal,
      ∀ z ∈ F, (g ((0 : zeroBase n), z.2) : Spatial n) = z.1 := by
    refine ⟨fun q => ⟨(Classical.epsilon fun y : Space n => y ∈ F ∧ y.2 = q.2).1, hWo _⟩, ?_⟩
    intro z hz
    have hspec := Classical.epsilon_spec (p := fun y : Space n => y ∈ F ∧ y.2 = z.2) ⟨z, hz, rfl⟩
    exact congrArg Prod.fst (hinj _ hspec.1 z hz hspec.2)
  have hlift : ∀ z ∈ F, verticalLift (zeroBase n) g ((0 : zeroBase n), z.2) = z := by
    intro z hz
    refine Prod.ext ?_ rfl
    show ((0 : zeroBase n) : Spatial n) + (g ((0 : zeroBase n), z.2) : Spatial n) = z.1
    rw [hg z hz, Submodule.coe_zero, zero_add]
  refine ⟨zeroBase n, (fun z : Space n => ((0 : zeroBase n), z.2)) '' F, g, by simp, ?_, ?_⟩
  · refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    show dist (g ((0 : zeroBase n), z.2) : Spatial n) (g ((0 : zeroBase n), w.2) : Spatial n) ≤
      (ℓ : ℝ) * dist ((0 : zeroBase n), z.2) ((0 : zeroBase n), w.2)
    have hp : dist ((0 : zeroBase n), z.2) ((0 : zeroBase n), w.2) = dist z.2 w.2 := by
      rw [Prod.dist_eq]
      exact max_eq_right (by rw [dist_self]; exact dist_nonneg)
    rw [hg z hz, hg w hw, hp, dist_eq_norm]
    exact htime z hz w hw
  · ext y
    constructor
    · intro hy
      exact ⟨_, ⟨y, hy, rfl⟩, hlift y hy⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact (congrArg (· ∈ F) (hlift z hz)).mpr hz

/-- **Spatial rank zero.** There are dimensional `A = 8` and
`C = 2^18 / log 2` such that a carrier piece `F ⊆ P(z₀, ρ)` of dimension two with
`A ρ ≤ T`, lower mass `a`, square tail `b` and `C b ≤ ℓ⁴ a`, `ℓ < 1`, is the lift of
a parabolic `ℓ`-Lipschitz partial map over the rank-zero base. -/
theorem rank_zero_partial_time_graph_proof (n : ℕ) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
      ∀ (η : Measure (Space n)) (F : Set (Space n)) (z₀ : Space n) (ρ T a b : ℝ)
        (ℓ : ℝ≥0),
        0 < ρ → A * ρ ≤ T → 0 < a → 0 ≤ b → (ℓ : ℝ) < 1 →
        F ⊆ Metric.ball z₀ ρ → IsCarrierPiece η 2 a b T F → C * b ≤ (ℓ : ℝ) ^ 4 * a →
        ∃ (W : Submodule ℝ (Spatial n)) (D : Set (SubspaceSpace W))
          (g : SubspaceSpace W → W.orthogonal),
          Module.finrank ℝ W = 0 ∧ LipschitzOnWith ℓ g D ∧ F = verticalLift W g '' D := by
  refine ⟨8, 2 ^ 18 / Real.log 2, by norm_num, div_pos (by norm_num) (Real.log_pos one_lt_two),
    ?_⟩
  intro η F z₀ ρ T a b ℓ hρ hAT ha hb hℓ hFρ hp hC
  have hkey : ∀ z ∈ F, ∀ w ∈ F, ‖z.1 - w.1‖ ≤ ℓ * dist z w := by
    intro z hz w hw
    have h1 := Metric.mem_ball.mp (hFρ hz)
    have h2 := Metric.mem_ball.mp (hFρ hw)
    have h3 := dist_triangle_right z w z₀
    exact rank_zero_spatial_le η F ha hb (NNReal.coe_nonneg ℓ) hp hC hz hw (by linarith)
  refine exists_rankZero_lift F ℓ fun z hz w hw => ?_
  have h := hkey z hz w hw
  rw [Prod.dist_eq, ← dist_eq_norm] at h
  rw [← dist_eq_norm]
  rcases le_total (dist z.1 w.1) (dist z.2 w.2) with hle | hle
  · rwa [max_eq_right hle] at h
  · rw [max_eq_left hle] at h
    have hz0 : dist z.1 w.1 ≤ 0 := by
      by_contra hpos
      have := mul_lt_mul_of_pos_right hℓ (not_le.mp hpos)
      linarith
    exact hz0.trans (mul_nonneg (NNReal.coe_nonneg ℓ) dist_nonneg)

/-! ## Countable unions of regular vertical covers -/

/-- Countable unions with a Hausdorff-null remainder: the families are
reindexed into a subset of `ℕ` and the exception is a countable union of null sets. -/
theorem hasRegularVerticalGraphCover_of_iUnion_proof {n k : ℕ} {ι : Type*} [Countable ι]
    {K : Set (Space n)} {ε : ℝ} (S : ι → Set (Space n))
    (hnull : hausdorffP n k (K \ ⋃ i, S i) = 0)
    (hS : ∀ i, HasRegularVerticalGraphCover k (S i) ε) :
    HasRegularVerticalGraphCover k K ε := by
  have hS' : ∀ i, ∃ (I : Set ℕ) (G : I → RegularVerticalGraph n k ε),
      hausdorffP n k (S i \ ⋃ l, (G l).image) = 0 := hS
  choose I G hG using hS'
  obtain ⟨e, he⟩ := Countable.exists_injective_nat (Σ i, I i)
  let σ := Equiv.ofInjective e he
  refine ⟨Set.range e, fun j => G (σ.symm j).1 (σ.symm j).2, ?_⟩
  refine measure_mono_null ?_ (measure_union_null hnull (measure_iUnion_null hG))
  rintro x ⟨hxK, hx⟩
  by_cases hxS : x ∈ ⋃ i, S i
  · right
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxS
    refine mem_iUnion.mpr ⟨i, hi, fun hmem => hx ?_⟩
    obtain ⟨l, hl⟩ := mem_iUnion.mp hmem
    refine mem_iUnion.mpr ⟨σ ⟨i, l⟩, ?_⟩
    show x ∈ (G (σ.symm (σ ⟨i, l⟩)).1 (σ.symm (σ ⟨i, l⟩)).2).image
    rw [Equiv.symm_apply_apply]
    exact hl
  · exact Or.inl ⟨hxK, hxS⟩

/-! ## Nets, best fits and the carrier family -/

/-- A compact set has, for every `s > 0`, a
finite `s`-separated subset at distance `< s` from every point of the set. A
separated subset of maximal cardinality exists because a cover by balls of radius
`s/2` bounds the cardinality of every separated subset. -/
theorem exists_maximal_separated_finset_proof {n : ℕ} {F : Set (Space n)} (hF : IsCompact F)
    {s : ℝ} (hs : 0 < s) :
    ∃ Z : Finset (Space n), (↑Z : Set (Space n)) ⊆ F ∧
      (∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → s ≤ dist z w) ∧ ∀ x ∈ F, ∃ w ∈ Z, dist x w < s := by
  classical
  obtain ⟨t, -, htfin, hcov⟩ := hF.finite_cover_balls (half_pos hs)
  have hpt : ∀ x ∈ F, ∃ c ∈ htfin.toFinset, dist x c < s / 2 := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hcov hx)
    exact ⟨c, htfin.mem_toFinset.mpr hc, hxc⟩
  choose! f hfC hfd using hpt
  let Sep : Finset (Space n) → Prop := fun Z => (↑Z : Set (Space n)) ⊆ F ∧
    ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → s ≤ dist z w
  have hbound : ∀ Z, Sep Z → Z.card ≤ htfin.toFinset.card := by
    intro Z hZ
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro z hz
      exact hfC z (hZ.1 hz)
    · intro z hz w hw hzw
      by_contra hne
      have h1 := hfd z (hZ.1 hz)
      have h2 := hfd w (hZ.1 hw)
      have h3 := hZ.2 z hz w hw hne
      have h4 := dist_triangle_right z w (f z)
      rw [← hzw] at h2
      linarith
  let P : ℕ → Prop := fun k => ∃ Z, Sep Z ∧ Z.card = k
  have hP0 : P 0 := ⟨∅, ⟨by simp, by simp⟩, rfl⟩
  obtain ⟨Z, hZ, hcard⟩ : P (Nat.findGreatest P htfin.toFinset.card) :=
    Nat.findGreatest_spec (Nat.zero_le _) hP0
  refine ⟨Z, hZ.1, hZ.2, fun x hx => ?_⟩
  by_contra! hfar
  have hxZ : x ∉ Z := fun h => by
    have := hfar x h
    rw [dist_self] at this
    linarith
  have hsep : Sep (insert x Z) := by
    refine ⟨?_, ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hx hZ.1
    · intro u hu v hv huv
      rw [Finset.mem_insert] at hu hv
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact absurd rfl huv
      · exact hfar v hv
      · rw [dist_comm]
        exact hfar u hu
      · exact hZ.2 u hu v hv huv
  have hcard' : (insert x Z).card = Nat.findGreatest P htfin.toFinset.card + 1 := by
    rw [Finset.card_insert_of_notMem hxZ, hcard]
  have hbd : Nat.findGreatest P htfin.toFinset.card + 1 ≤ htfin.toFinset.card := by
    rw [← hcard']
    exact hbound _ hsep
  have hle := Nat.le_findGreatest (P := P) hbd ⟨insert x Z, hsep, hcard'⟩
  omega

/-- Attainment of the vertical fitting infimum on every ball, for a source
finite on compact sets and `m ≤ n`: apply the global attainment theorem to
the source restricted to the ball (carried by the compact closed ball). A vertical
model of dimension `m + 2` has spatial rank `m`. Nonpositive radii give the empty
ball, which needs no separate case. -/
theorem exists_verticalPlane_bestFit_proof {n m : ℕ} (hmn : m ≤ n) (η : Measure (Space n))
    [IsFiniteMeasureOnCompacts η] (z : Space n) (r : ℝ) :
    ∃ L : AffineSpatialPlane n m,
      fit η (verticalPlaneModel L) z r = ⨅ M : Models n (m + 2) .vertical, fit η M z r := by
  have : IsFiniteMeasure (η.restrict (Metric.ball z r)) :=
    isFiniteMeasure_restrict.mpr (measure_ball_lt_top η z r).ne
  obtain ⟨L₀⟩ := AffineSpatialPlane.nonempty_iff.mpr hmn
  have hne : Nonempty (Models n (m + 2) .vertical) := ⟨verticalPlaneModel L₀⟩
  have hK : ∀ᵐ w ∂(η.restrict (Metric.ball z r)), w ∈ Metric.closedBall z r :=
    (ae_restrict_mem measurableSet_ball).mono fun w hw => Metric.ball_subset_closedBall hw
  obtain ⟨M, hM, -⟩ := exists_globalFittingError_minimizer (η.restrict (Metric.ball z r)) hne
    (isCompact_closedBall z r) hK
  change VerticalModel n (m + 2) at M
  obtain ⟨m', h2, hrank, L⟩ := M
  obtain rfl : m' = m := by omega
  exact ⟨L, hM⟩

/-- For a compact `F ⊆ P(z₀, R/2)`, a source
finite on compact sets and `Λ > 0`, the carrier family: maximal `r_j`-separated nets
of `F`, parents from the covering property, best fitted planes on `P(z, Λ r_j)`, and
the plane of the (at most one) level-zero center as initial plane. -/
theorem exists_isCarrierFamily_proof {n m : ℕ} (hmn : m ≤ n) (η : Measure (Space n))
    [IsFiniteMeasureOnCompacts η] {F : Set (Space n)} (hF : IsCompact F) (z₀ : Space n)
    {R : ℝ} (hR : 0 < R) (hFR : F ⊆ Metric.ball z₀ (R / 2)) {Λ : ℝ} (_hΛ : 0 < Λ) :
    ∃ Φ : CoherentFamily n m (Space n), Φ.initialRadius = R ∧ IsCarrierFamily η F Λ Φ := by
  have : Nonempty (Space n) := ⟨z₀⟩
  choose Z hZsub hZsep hZcov using fun j : ℕ =>
    exists_maximal_separated_finset_proof hF (s := R / 10 ^ j) (div_pos hR (by positivity))
  choose Lf hLf using fun (z : Space n) (r : ℝ) => exists_verticalPlane_bestFit_proof hmn η z r
  have hcov := hZcov
  choose! P hPmem hPdist using hZcov
  obtain ⟨c₀, hc₀⟩ : ∃ c : Space n, (∃ y, y ∈ Z 0) → c ∈ Z 0 :=
    ⟨Classical.epsilon fun c => c ∈ Z 0, fun h => Classical.epsilon_spec h⟩
  refine ⟨{ initialRadius := R
            initialRadius_pos := hR
            index := Z
            center := fun _ z => z
            plane := fun j z => Lf z (Λ * (R / 10 ^ j))
            parent := fun j z => P (j - 1) z
            initialPlane := Lf c₀ (Λ * (R / 10 ^ 0)) }, rfl, ?_⟩
  refine
    { center_eq := fun _ _ => rfl
      index_subset := hZsub
      separated := hZsep
      covering := hcov
      parent_mem := fun j z hz => hPmem j z (hZsub (j + 1) hz)
      parent_dist := fun j z hz => (hPdist j z (hZsub (j + 1) hz)).le
      initial_plane := ?_
      best_fit := fun j z _ => hLf z (Λ * (R / 10 ^ j)) }
  intro z hz
  have hc : c₀ ∈ Z 0 := hc₀ ⟨z, hz⟩
  have hzc : z = c₀ := by
    by_contra hne
    have h1 := hZsep 0 z hz c₀ hc hne
    have h2 := Metric.mem_ball.mp (hFR (hZsub 0 hz))
    have h3 := Metric.mem_ball.mp (hFR (hZsub 0 hc))
    have h4 := dist_triangle_right z c₀ z₀
    rw [pow_zero, div_one] at h1
    linarith
  show Lf z (Λ * (R / 10 ^ 0)) = Lf c₀ (Λ * (R / 10 ^ 0))
  rw [hzc]

end ParabolicRectifiability
