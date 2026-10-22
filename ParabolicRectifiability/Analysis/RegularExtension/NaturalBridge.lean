import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Metric.BaseVolume

/-! # Natural beta controls the affine trace error (small slope)

Let `K` be compact in the intrinsic base `W × Time` of a spatial subspace `W` of
rank `m`, let `f : K → Wᗮ` be parabolic `L`-Lipschitz with `L ≤ L₀(m)`, and put
`Φ(q) = (q.1 + f q, q.2)` and `η = H^{m+2}_P ⌞ Φ(K)`. If `K` fills half of the
base ball `P_b(p,r)`, then `γ_K(p,r)^2 ≤ C β_{η,V_{m+2},m+2}(Φ(p),2r)^2`.

The argument compares the trace error with every vertical competitor plane
`Π = x₀ + V` separately, so no minimizing plane is needed.

* `slab_lintegral_lower_bound` is the needed special case of the reservoir
  lemma: a half-dense source in `P_b(p,r)` has
  `∫ |⟪w,u⟫ - b|^2 ≥ c ‖w‖^2 r^2 |P_b(p,r)|`. The slab volume is bounded by
  disjoint spatial translates (`slab_volume_le`).
* If the plane error `I(Π)` is large compared with `r^{k+2}`, the constant
  competitor `f(p)` already suffices. Otherwise every normal `ν` of `V` has
  `16 ‖P_W ν‖^2 ≤ ‖ν‖^2`, so `Π` is the graph of an affine map with slope at most
  one (`exists_affine_graph_of_normal_bound`) and that map has error at most
  `2 I(Π)`.
* The lifted base ball lies in `P(Φ(p),2r)`, and the push-forward of base volume
  is at most `2 ω_m η` (`lintegral_comp_lift_le`, from the base Hausdorff
  comparison and the `1`-Lipschitz base projection).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal InnerProductSpace

namespace ParabolicRectifiability

namespace NaturalBridge

variable {n : ℕ}

/-! ### Spatial translations of the intrinsic base -/

/-- Translation of the intrinsic base by a spatial vector. -/
def spatialShift (W : Submodule ℝ (Spatial n)) (v : W) (q : SubspaceSpace W) :
    SubspaceSpace W :=
  (v + q.1, q.2)

theorem spatialShift_measurePreserving (W : Submodule ℝ (Spatial n)) (v : W) :
    MeasurePreserving (spatialShift W v) (intrinsicParabolicVolume W)
      (intrinsicParabolicVolume W) := by
  have h := (subspaceTime_symm_measurePreserving W).comp
    ((measurePreserving_add_left ((volume : Measure W).prod (volume : Measure ℝ))
      ((v, 0) : W × ℝ)).comp (subspaceTime_measurePreserving W))
  convert h using 1
  funext q
  change (v + q.1, q.2) = (v + q.1, Metric.Snowflaking.toSnowflaking (0 + q.2.val))
  rw [zero_add]
  rfl

theorem intrinsicParabolicVolume_ball_ne_zero (W : Submodule ℝ (Spatial n))
    (p : SubspaceSpace W) {r : ℝ} (hr : 0 < r) :
    intrinsicParabolicVolume W (ball p r) ≠ 0 := by
  rw [intrinsicParabolicVolume_ball W p r hr]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (omega_pos _).ne')
    (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr).ne')

theorem intrinsicParabolicVolume_ball_ne_top (W : Submodule ℝ (Spatial n))
    (p : SubspaceSpace W) {r : ℝ} (hr : 0 < r) :
    intrinsicParabolicVolume W (ball p r) ≠ ∞ := by
  rw [intrinsicParabolicVolume_ball W p r hr]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (omega_lt_top _).ne)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

/-! ### The reservoir slab bound -/

/-- A slab of half-width `‖w‖ h`, `h = r/2^{m+5}`, normal to `w ≠ 0`, meets the base
ball `P_b(p,r)` in at most a quarter of its volume. Disjoint spatial translates of
the slab piece lie in `P_b(p,2r)`. -/
theorem slab_volume_le (W : Submodule ℝ (Spatial n)) (p : SubspaceSpace W) {r : ℝ}
    (hr : 0 < r) (w : W) (hw : w ≠ 0) (b : ℝ) :
    4 * intrinsicParabolicVolume W
        ({q : SubspaceSpace W |
          |⟪w, q.1⟫_ℝ - b| < ‖w‖ * (r / 2 ^ (Module.finrank ℝ W + 5))} ∩ ball p r) ≤
      intrinsicParabolicVolume W (ball p r) := by
  set m := Module.finrank ℝ W with hm
  have hhpos : 0 < r / 2 ^ (m + 5) := div_pos hr (by positivity)
  set h : ℝ := r / 2 ^ (m + 5) with hh
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hw0' : ‖w‖ ≠ 0 := hw0.ne'
  set S := {q : SubspaceSpace W | |⟪w, q.1⟫_ℝ - b| < ‖w‖ * h} ∩ ball p r with hS
  have hSm : MeasurableSet S := by
    refine (IsOpen.measurableSet ?_).inter measurableSet_ball
    exact isOpen_lt ((continuous_const.inner continuous_fst).sub continuous_const).abs
      continuous_const
  set N : ℕ := 2 ^ (m + 4) with hN
  have hNh : 2 * (N : ℝ) * h = r := by
    rw [hh, hN]
    push_cast
    field_simp
    ring
  let v : Fin N → W := fun j => (-(2 * ((j : ℕ) : ℝ) * h / ‖w‖)) • w
  let T : Fin N → Set (SubspaceSpace W) := fun j => spatialShift W (v j) ⁻¹' S
  have hTm : ∀ j, MeasurableSet (T j) := fun j =>
    (spatialShift_measurePreserving W (v j)).measurable hSm
  have hTvol : ∀ j, intrinsicParabolicVolume W (T j) = intrinsicParabolicVolume W S :=
    fun j => (spatialShift_measurePreserving W (v j)).measure_preimage hSm.nullMeasurableSet
  have hvi : ∀ j : Fin N, ⟪w, v j⟫_ℝ = -(2 * ((j : ℕ) : ℝ) * h / ‖w‖) * ‖w‖ ^ 2 := by
    intro j
    rw [← real_inner_self_eq_norm_sq]
    exact real_inner_smul_right w w _
  have hinner : ∀ (j : Fin N) (q : SubspaceSpace W),
      ⟪w, (spatialShift W (v j) q).1⟫_ℝ = ⟪w, q.1⟫_ℝ - 2 * ((j : ℕ) : ℝ) * h * ‖w‖ := by
    intro j q
    have hc : -(2 * ((j : ℕ) : ℝ) * h / ‖w‖) * ‖w‖ ^ 2 = -(2 * ((j : ℕ) : ℝ) * h * ‖w‖) := by
      rw [neg_mul, sq, ← mul_assoc, div_mul_cancel₀ _ hw0']
    rw [show (spatialShift W (v j) q).1 = v j + q.1 from rfl, inner_add_right, hvi j, hc]
    ring
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro q hi hj
    have hi' : |⟪w, (spatialShift W (v i) q).1⟫_ℝ - b| < ‖w‖ * h :=
      (show spatialShift W (v i) q ∈ S from hi).1
    have hj' : |⟪w, (spatialShift W (v j) q).1⟫_ℝ - b| < ‖w‖ * h :=
      (show spatialShift W (v j) q ∈ S from hj).1
    rw [hinner] at hi' hj'
    rw [abs_lt] at hi' hj'
    obtain ⟨hi1, hi2⟩ := hi'
    obtain ⟨hj1, hj2⟩ := hj'
    have hpos : 0 < h * ‖w‖ := mul_pos hhpos hw0
    apply hij
    have h1 : ((i : ℕ) : ℝ) < (j : ℕ) + 1 := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith
    have h2 : ((j : ℕ) : ℝ) < (i : ℕ) + 1 := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith
    have h1' : (i : ℕ) < (j : ℕ) + 1 := by exact_mod_cast h1
    have h2' : (j : ℕ) < (i : ℕ) + 1 := by exact_mod_cast h2
    exact Fin.ext (by omega)
  have hsub : ∀ j, T j ⊆ ball p (2 * r) := by
    intro j q hq
    have hq' : spatialShift W (v j) q ∈ ball p r := (show spatialShift W (v j) q ∈ S from hq).2
    have hvn : ‖v j‖ = 2 * ((j : ℕ) : ℝ) * h := by
      simp only [v, norm_smul, Real.norm_eq_abs, abs_neg]
      rw [abs_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _))
        hhpos.le) (norm_nonneg _))]
      field_simp
    have hd : dist q (spatialShift W (v j) q) = 2 * ((j : ℕ) : ℝ) * h := by
      rw [Prod.dist_eq]
      simp only [spatialShift, dist_self]
      rw [dist_eq_norm, show q.1 - (v j + q.1) = -(v j) by abel, norm_neg, hvn]
      exact max_eq_left (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) hhpos.le)
    have hjN : ((j : ℕ) : ℝ) < N := by exact_mod_cast j.2
    rw [mem_ball] at hq' ⊢
    calc dist q p ≤ dist q (spatialShift W (v j) q) + dist (spatialShift W (v j) q) p :=
          dist_triangle _ _ _
      _ < 2 * ((j : ℕ) : ℝ) * h + r := by rw [hd]; linarith
      _ ≤ 2 * r := by nlinarith
  have hsum : (N : ℝ≥0∞) * intrinsicParabolicVolume W S ≤
      intrinsicParabolicVolume W (ball p (2 * r)) := by
    calc (N : ℝ≥0∞) * intrinsicParabolicVolume W S
        = ∑ j : Fin N, intrinsicParabolicVolume W (T j) := by
          simp only [hTvol, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = intrinsicParabolicVolume W (⋃ j, T j) := by
          rw [measure_iUnion hdisj hTm, tsum_fintype]
      _ ≤ intrinsicParabolicVolume W (ball p (2 * r)) := measure_mono (iUnion_subset hsub)
  have hball2 : intrinsicParabolicVolume W (ball p (2 * r)) =
      2 ^ (m + 2) * intrinsicParabolicVolume W (ball p r) := by
    rw [intrinsicParabolicVolume_ball W p _ (mul_pos two_pos hr),
      intrinsicParabolicVolume_ball W p r hr,
      ENNReal.ofReal_mul (by norm_num), mul_pow, ENNReal.ofReal_ofNat]
    ring
  rw [hball2] at hsum
  have hN' : (N : ℝ≥0∞) = 2 ^ (m + 2) * 4 := by
    rw [hN]
    push_cast
    ring
  rw [hN', mul_assoc] at hsum
  exact (ENNReal.mul_le_mul_iff_right (by positivity) (by finiteness)).mp hsum

/-- **Reservoir slab bound** (a special case of the reservoir lemma). If `G` fills half of `P_b(p,r)`, then for every `w ∈ W` and
`b ∈ ℝ`, `‖w‖^2 h^2 |P_b(p,r)| ≤ 4 ∫_{P_b(p,r) ∩ G} |⟪w,u⟫ - b|^2`, where
`h = r/2^{m+5}`. -/
theorem slab_lintegral_lower_bound (W : Submodule ℝ (Spatial n)) (p : SubspaceSpace W)
    {r : ℝ} (hr : 0 < r) (G : Set (SubspaceSpace W)) (hG : MeasurableSet G)
    (hdens : intrinsicParabolicVolume W (ball p r) ≤
      2 * intrinsicParabolicVolume W (G ∩ ball p r)) (w : W) (b : ℝ) :
    ENNReal.ofReal (‖w‖ ^ 2 * (r / 2 ^ (Module.finrank ℝ W + 5)) ^ 2) *
        intrinsicParabolicVolume W (ball p r) ≤
      4 * ∫⁻ q in ball p r ∩ G, ENNReal.ofReal ((⟪w, q.1⟫_ℝ - b) ^ 2)
        ∂intrinsicParabolicVolume W := by
  rcases eq_or_ne w 0 with rfl | hw
  · have h0 : ENNReal.ofReal (‖(0 : W)‖ ^ 2 * (r / 2 ^ (Module.finrank ℝ W + 5)) ^ 2) = 0 := by
      rw [norm_zero]
      norm_num
    rw [h0, zero_mul]
    exact zero_le
  have hhpos : 0 < r / 2 ^ (Module.finrank ℝ W + 5) := div_pos hr (by positivity)
  set h : ℝ := r / 2 ^ (Module.finrank ℝ W + 5) with hh
  have hS := slab_volume_le W p hr w hw b
  rw [← hh] at hS
  set S := {q : SubspaceSpace W | |⟪w, q.1⟫_ℝ - b| < ‖w‖ * h} ∩ ball p r with hSdef
  have hSm : MeasurableSet S := by
    refine (IsOpen.measurableSet ?_).inter measurableSet_ball
    exact isOpen_lt ((continuous_const.inner continuous_fst).sub continuous_const).abs
      continuous_const
  set D := (ball p r ∩ G) \ S with hDdef
  have hDm : MeasurableSet D := (measurableSet_ball.inter hG).diff hSm
  have hbt := intrinsicParabolicVolume_ball_ne_top W p hr
  have hD : intrinsicParabolicVolume W (ball p r) ≤ 4 * intrinsicParabolicVolume W D := by
    have h1 : intrinsicParabolicVolume W (G ∩ ball p r) ≤
        intrinsicParabolicVolume W D + intrinsicParabolicVolume W S := by
      refine (measure_mono ?_).trans (measure_union_le D S)
      intro q hq
      by_cases hqS : q ∈ S
      · exact Or.inr hqS
      · exact Or.inl ⟨⟨hq.2, hq.1⟩, hqS⟩
    have h2 : intrinsicParabolicVolume W (ball p r) + intrinsicParabolicVolume W (ball p r) ≤
        4 * intrinsicParabolicVolume W D + intrinsicParabolicVolume W (ball p r) := by
      calc intrinsicParabolicVolume W (ball p r) + intrinsicParabolicVolume W (ball p r)
          = 2 * intrinsicParabolicVolume W (ball p r) := (two_mul _).symm
        _ ≤ 2 * (2 * intrinsicParabolicVolume W (G ∩ ball p r)) := by gcongr
        _ ≤ 2 * (2 * (intrinsicParabolicVolume W D + intrinsicParabolicVolume W S)) := by
          gcongr
        _ = 4 * intrinsicParabolicVolume W D + 4 * intrinsicParabolicVolume W S := by ring
        _ ≤ 4 * intrinsicParabolicVolume W D + intrinsicParabolicVolume W (ball p r) := by
          gcongr
    exact ENNReal.le_of_add_le_add_right hbt h2
  have hint : ENNReal.ofReal (‖w‖ ^ 2 * h ^ 2) * intrinsicParabolicVolume W D ≤
      ∫⁻ q in ball p r ∩ G, ENNReal.ofReal ((⟪w, q.1⟫_ℝ - b) ^ 2)
        ∂intrinsicParabolicVolume W := by
    calc ENNReal.ofReal (‖w‖ ^ 2 * h ^ 2) * intrinsicParabolicVolume W D
        = ∫⁻ _ in D, ENNReal.ofReal (‖w‖ ^ 2 * h ^ 2) ∂intrinsicParabolicVolume W :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ q in D, ENNReal.ofReal ((⟪w, q.1⟫_ℝ - b) ^ 2) ∂intrinsicParabolicVolume W := by
          refine setLIntegral_mono' hDm fun q hq => ENNReal.ofReal_le_ofReal ?_
          have hq' : ¬ (|⟪w, q.1⟫_ℝ - b| < ‖w‖ * h) := fun hlt => hq.2 ⟨hlt, hq.1.1⟩
          rw [not_lt] at hq'
          have h0 : 0 ≤ ‖w‖ * h := mul_nonneg (norm_nonneg _) hhpos.le
          calc ‖w‖ ^ 2 * h ^ 2 = (‖w‖ * h) ^ 2 := by ring
            _ ≤ |⟪w, q.1⟫_ℝ - b| ^ 2 := pow_le_pow_left₀ h0 hq' 2
            _ = (⟪w, q.1⟫_ℝ - b) ^ 2 := sq_abs _
      _ ≤ _ := lintegral_mono_set sdiff_subset
  calc ENNReal.ofReal (‖w‖ ^ 2 * h ^ 2) * intrinsicParabolicVolume W (ball p r)
      ≤ ENNReal.ofReal (‖w‖ ^ 2 * h ^ 2) * (4 * intrinsicParabolicVolume W D) := by gcongr
    _ = 4 * (ENNReal.ofReal (‖w‖ ^ 2 * h ^ 2) * intrinsicParabolicVolume W D) := by ring
    _ ≤ _ := by gcongr

/-! ### The lift, the base projection and the push-forward comparison -/

/-- The lift `Φ(q) = (q.1 + f q, q.2)`. -/
def lift (W : Submodule ℝ (Spatial n)) (f : SubspaceSpace W → W.orthogonal)
    (q : SubspaceSpace W) : Space n :=
  ((q.1 : Spatial n) + (f q : Spatial n), q.2)

/-- Orthogonal projection of parabolic space onto the intrinsic base. -/
def baseProj (W : Submodule ℝ (Spatial n)) (z : Space n) : SubspaceSpace W :=
  (W.orthogonalProjectionOnto z.1, z.2)

theorem baseProj_lift (W : Submodule ℝ (Spatial n)) (f : SubspaceSpace W → W.orthogonal)
    (q : SubspaceSpace W) : baseProj W (lift W f q) = q := by
  simp only [baseProj, lift, map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (f q).2, add_zero]

theorem lipschitzWith_baseProj (W : Submodule ℝ (Spatial n)) :
    LipschitzWith 1 (baseProj W) := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [NNReal.coe_one, one_mul, Prod.dist_eq, Prod.dist_eq]
  refine max_le_max ?_ le_rfl
  change dist (W.orthogonalProjectionOnto z.1) (W.orthogonalProjectionOnto z'.1) ≤ dist z.1 z'.1
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact Submodule.norm_orthogonalProjectionOnto_apply_le (K := W) _

/-- The lifted base ball lies in the parabolic ball of twice the radius. -/
theorem lift_mem_ball {W : Submodule ℝ (Spatial n)} {K : Set (SubspaceSpace W)}
    {f : SubspaceSpace W → W.orthogonal} {L : ℝ≥0} (hf : LipschitzOnWith L f K)
    (hL : (L : ℝ) ≤ 1) {p q : SubspaceSpace W} (hp : p ∈ K) (hq : q ∈ K) {r : ℝ}
    (hqp : dist q p < r) : lift W f q ∈ ball (lift W f p) (2 * r) := by
  have hd : dist q p = max (dist q.1 p.1) (dist q.2 p.2) := Prod.dist_eq
  have h1 : dist q.1 p.1 ≤ dist q p := hd ▸ le_max_left _ _
  have h2 : dist q.2 p.2 ≤ dist q p := hd ▸ le_max_right _ _
  have hfq : dist (f q) (f p) ≤ L * dist q p := hf.dist_le_mul q hq p hp
  have hLd : (L : ℝ) * dist q p ≤ dist q p := by
    nlinarith [dist_nonneg (x := q) (y := p), L.2]
  have hsp : dist (lift W f q).1 (lift W f p).1 ≤ dist q.1 p.1 + dist (f q) (f p) := by
    simp only [lift]
    rw [Subtype.dist_eq q.1 p.1, Subtype.dist_eq (f q) (f p)]
    exact dist_add_add_le _ _ _ _
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  constructor
  · linarith
  · change dist q.2 p.2 < 2 * r
    linarith [dist_nonneg (x := q) (y := p)]

/-- Push-forward comparison: base volume on `P_b(p,r) ∩ K`, lifted by `Φ`, is at most
`2 ω_m` times the Hausdorff measure `η` of `Φ(K)` on `P(Φ(p),2r)`. -/
theorem lintegral_comp_lift_le {W : Submodule ℝ (Spatial n)} {m : ℕ}
    (hW : Module.finrank ℝ W = m) {K : Set (SubspaceSpace W)} (hK : IsCompact K)
    {f : SubspaceSpace W → W.orthogonal} {L : ℝ≥0} (hf : LipschitzOnWith L f K)
    (hL : (L : ℝ) ≤ 1) {p : SubspaceSpace W} (hp : p ∈ K) {r : ℝ}
    {g : Space n → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ q in ball p r ∩ K, g (lift W f q) ∂intrinsicParabolicVolume W ≤
      (2 * omega m) * ∫⁻ z in ball (lift W f p) (2 * r), g z
        ∂((hausdorffP n (m + 2)).restrict (lift W f '' K)) := by
  subst hW
  have hs : MeasurableSet (ball p r ∩ K) := measurableSet_ball.inter hK.isClosed.measurableSet
  have hcont : ContinuousOn (lift W f) K := by
    unfold lift
    exact ((continuous_subtype_val.comp continuous_fst).continuousOn.add
      (continuous_subtype_val.comp_continuousOn hf.continuousOn)).prodMk
        continuous_snd.continuousOn
  have hΦ : AEMeasurable (lift W f) ((intrinsicParabolicVolume W).restrict (ball p r ∩ K)) :=
    (hcont.mono inter_subset_right).aemeasurable hs
  rw [← lintegral_map' hg.aemeasurable hΦ]
  have hω0 : (2 * omega (Module.finrank ℝ W)) ≠ 0 :=
    (ENNReal.mul_pos (by norm_num) (omega_pos _).ne').ne'
  have hωt : (2 * omega (Module.finrank ℝ W)) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (omega_lt_top _).ne
  have hle : Measure.map (lift W f) ((intrinsicParabolicVolume W).restrict (ball p r ∩ K)) ≤
      (2 * omega (Module.finrank ℝ W)) •
        ((hausdorffP n (Module.finrank ℝ W + 2)).restrict (lift W f '' K)).restrict
          (ball (lift W f p) (2 * r)) := by
    rw [Measure.le_iff]
    intro S hS
    rw [Measure.map_apply_of_aemeasurable hΦ hS, Measure.restrict_apply' hs, Measure.smul_apply,
      smul_eq_mul, Measure.restrict_apply hS, Measure.restrict_apply (hS.inter measurableSet_ball)]
    set A := lift W f ⁻¹' S ∩ (ball p r ∩ K) with hA
    have h1 : intrinsicParabolicVolume W A ≤ 2 * omega (Module.finrank ℝ W) *
        Measure.hausdorffMeasure ((Module.finrank ℝ W + 2 : ℕ) : ℝ) A :=
      (ENNReal.inv_mul_le_iff hω0 hωt).mp (vertical_base_hausdorff_comparison W A).1
    have h2 : Measure.hausdorffMeasure ((Module.finrank ℝ W + 2 : ℕ) : ℝ) A ≤
        hausdorffP n (Module.finrank ℝ W + 2) (lift W f '' A) := by
      have himg : baseProj W '' (lift W f '' A) = A := by
        rw [image_image]
        simp only [baseProj_lift, image_id']
      have := (lipschitzWith_baseProj W).hausdorffMeasure_image_le
        (Nat.cast_nonneg (Module.finrank ℝ W + 2)) (lift W f '' A)
      rw [himg, ENNReal.coe_one, ENNReal.one_rpow, one_mul] at this
      exact this
    have h3 : lift W f '' A ⊆ S ∩ ball (lift W f p) (2 * r) ∩ lift W f '' K := by
      rintro _ ⟨q, ⟨hqS, hqB, hqK⟩, rfl⟩
      exact ⟨⟨hqS, lift_mem_ball hf hL hp hqK hqB⟩, mem_image_of_mem _ hqK⟩
    calc intrinsicParabolicVolume W A
        ≤ 2 * omega (Module.finrank ℝ W) *
            Measure.hausdorffMeasure ((Module.finrank ℝ W + 2 : ℕ) : ℝ) A := h1
      _ ≤ 2 * omega (Module.finrank ℝ W) *
            hausdorffP n (Module.finrank ℝ W + 2) (lift W f '' A) := mul_le_mul_right h2 _
      _ ≤ _ := mul_le_mul_right (measure_mono h3) _
  calc ∫⁻ z, g z ∂Measure.map (lift W f) ((intrinsicParabolicVolume W).restrict (ball p r ∩ K))
      ≤ ∫⁻ z, g z ∂((2 * omega (Module.finrank ℝ W)) •
          ((hausdorffP n (Module.finrank ℝ W + 2)).restrict (lift W f '' K)).restrict
            (ball (lift W f p) (2 * r))) := lintegral_mono' hle le_rfl
    _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]

/-! ### Planes with nearly vertical normals are graphs of slope at most one -/

/-- If every normal `ν` of the `m`-dimensional subspace `V` satisfies
`16 ‖P_W ν‖^2 ≤ ‖ν‖^2`, where `W` also has rank `m`, then `x₀ + V` is the graph over `W`
of an affine map `a + B u` with `‖B u‖ ≤ ‖u‖`, and for every `u ∈ W`, `y ∈ Wᗮ`,
`‖y - (a + B u)‖^2 ≤ 2 dist(u + y, x₀ + V)^2`. -/
theorem exists_affine_graph_of_normal_bound (W V : Submodule ℝ (Spatial n))
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W) (x₀ : Spatial n)
    (hν : ∀ ν ∈ V.orthogonal, 16 * ‖W.starProjection ν‖ ^ 2 ≤ ‖ν‖ ^ 2) :
    ∃ (a : W.orthogonal) (B : W →L[ℝ] W.orthogonal), ∀ (u : W) (y : W.orthogonal),
      ‖y - (a + B u)‖ ^ 2 ≤
        2 * ‖((u : Spatial n) + (y : Spatial n)) -
          V.starProjection ((u : Spatial n) + (y : Spatial n)) - x₀‖ ^ 2 := by
  classical
  let T : V →ₗ[ℝ] W := (W.orthogonalProjectionOnto : Spatial n →ₗ[ℝ] W).comp V.subtype
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, ← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro w hw
    have hwV : (w : Spatial n) ∈ V.orthogonal := by
      rw [Submodule.mem_orthogonal]
      intro v hv
      have h1 : ⟪T ⟨v, hv⟩, w⟫_ℝ = 0 :=
        (Submodule.mem_orthogonal _ _).mp hw _ (LinearMap.mem_range_self T ⟨v, hv⟩)
      have h2 : ⟪T ⟨v, hv⟩, w⟫_ℝ = ⟪v, (w : Spatial n)⟫_ℝ :=
        calc ⟪T ⟨v, hv⟩, w⟫_ℝ = ⟪w, W.orthogonalProjectionOnto v⟫_ℝ := real_inner_comm _ _
          _ = ⟪(w : Spatial n), v⟫_ℝ := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left w v
          _ = ⟪v, (w : Spatial n)⟫_ℝ := real_inner_comm _ _
      rw [← h2, h1]
    have h16 := hν _ hwV
    rw [(Submodule.starProjection_eq_self_iff).mpr w.2] at h16
    have h0 : ‖(w : Spatial n)‖ = 0 := by nlinarith [norm_nonneg (w : Spatial n)]
    have h0' : (w : Spatial n) = 0 := norm_eq_zero.mp h0
    exact_mod_cast h0'
  have hinj : Function.Injective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  let e : V ≃ₗ[ℝ] W := LinearEquiv.ofBijective T ⟨hinj, hsurj⟩
  let B : W →L[ℝ] W.orthogonal := LinearMap.toContinuousLinearMap
    (((W.orthogonal.orthogonalProjectionOnto : Spatial n →ₗ[ℝ] W.orthogonal).comp V.subtype).comp e.symm.toLinearMap)
  have hB : ∀ v ∈ V, B (W.orthogonalProjectionOnto v) = Wᗮ.orthogonalProjectionOnto v := by
    intro v hv
    have he : e.symm (W.orthogonalProjectionOnto v) = ⟨v, hv⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    change Wᗮ.orthogonalProjectionOnto (V.subtype (e.symm (W.orthogonalProjectionOnto v))) = Wᗮ.orthogonalProjectionOnto v
    rw [he]
    rfl
  have hBn : ∀ w : W, ‖B w‖ ≤ ‖w‖ := by
    intro w
    set y := B w with hy
    set z : W := (ContinuousLinearMap.adjoint B) y with hzdef
    have hz : ∀ x : W, ⟪x, z⟫_ℝ = ⟪B x, y⟫_ℝ := fun x => by
      rw [hzdef]
      exact ContinuousLinearMap.adjoint_inner_right B x y
    have hνV : (y : Spatial n) - (z : Spatial n) ∈ V.orthogonal := by
      rw [Submodule.mem_orthogonal]
      intro v hv
      have hv' : v = (W.orthogonalProjectionOnto v : Spatial n) + (B (W.orthogonalProjectionOnto v) : Spatial n) := by
        rw [hB v hv]
        exact (Submodule.starProjection_add_starProjection_orthogonal (K := W) v).symm
      have e3 : ⟪(W.orthogonalProjectionOnto v : Spatial n), (z : Spatial n)⟫_ℝ =
          ⟪(B (W.orthogonalProjectionOnto v) : Spatial n), (y : Spatial n)⟫_ℝ := by
        rw [← Submodule.coe_inner, ← Submodule.coe_inner, hz]
      rw [hv', inner_add_left, inner_sub_right, inner_sub_right,
        Submodule.inner_right_of_mem_orthogonal (W.orthogonalProjectionOnto v).2 y.2,
        Submodule.inner_left_of_mem_orthogonal z.2 (B (W.orthogonalProjectionOnto v)).2, e3]
      ring
    have h16 := hν _ hνV
    have hproj : W.starProjection ((y : Spatial n) - (z : Spatial n)) = -(z : Spatial n) := by
      rw [map_sub, (Submodule.starProjection_apply_eq_zero_iff W).mpr y.2,
        (Submodule.starProjection_eq_self_iff).mpr z.2, zero_sub]
    rw [hproj, norm_neg] at h16
    have hyz : ⟪(y : Spatial n), (z : Spatial n)⟫_ℝ = 0 :=
      Submodule.inner_left_of_mem_orthogonal z.2 y.2
    have hpy : ‖(y : Spatial n) - (z : Spatial n)‖ ^ 2 =
        ‖(y : Spatial n)‖ ^ 2 + ‖(z : Spatial n)‖ ^ 2 := by
      rw [norm_sub_sq_real, hyz]
      ring
    rw [hpy] at h16
    have hzn : ‖(z : Spatial n)‖ = ‖z‖ := rfl
    have hyn : ‖(y : Spatial n)‖ = ‖y‖ := rfl
    rw [hzn, hyn] at h16
    have hzy : ‖z‖ ≤ ‖y‖ := by nlinarith [norm_nonneg z, norm_nonneg y]
    have hyy : ‖y‖ ^ 2 ≤ ‖w‖ * ‖y‖ := by
      calc ‖y‖ ^ 2 = ⟪y, y⟫_ℝ := (real_inner_self_eq_norm_sq y).symm
        _ = ⟪w, z⟫_ℝ := (hz w).symm
        _ ≤ ‖w‖ * ‖z‖ := real_inner_le_norm w z
        _ ≤ ‖w‖ * ‖y‖ := mul_le_mul_of_nonneg_left hzy (norm_nonneg w)
    nlinarith [norm_nonneg y, norm_nonneg w]
  refine ⟨Wᗮ.orthogonalProjectionOnto x₀ - B (W.orthogonalProjectionOnto x₀), B, fun u y => ?_⟩
  generalize hx : (u : Spatial n) + (y : Spatial n) = x
  obtain ⟨Y, hY⟩ : ∃ Y : Spatial n, Y = V.starProjection x + x₀ := ⟨_, rfl⟩
  have hPx : W.orthogonalProjectionOnto x = u := by
    rw [← hx, map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal y.2, add_zero]
  have hQx : Wᗮ.orthogonalProjectionOnto x = y := by
    rw [← hx, map_add, Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero u.2,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, zero_add]
  have hQY : Wᗮ.orthogonalProjectionOnto Y = (Wᗮ.orthogonalProjectionOnto x₀ -
      B (W.orthogonalProjectionOnto x₀)) + B (W.orthogonalProjectionOnto Y) := by
    have h1 := hB _ (V.starProjection_apply_mem x)
    rw [hY, map_add Wᗮ.orthogonalProjectionOnto, map_add W.orthogonalProjectionOnto, map_add B, h1]
    abel
  have key : y - ((Wᗮ.orthogonalProjectionOnto x₀ - B (W.orthogonalProjectionOnto x₀)) + B u) =
      Wᗮ.orthogonalProjectionOnto (x - Y) - B (W.orthogonalProjectionOnto (x - Y)) := by
    rw [map_sub Wᗮ.orthogonalProjectionOnto x Y, map_sub W.orthogonalProjectionOnto x Y, hPx, hQx,
      hQY, map_sub B]
    abel
  rw [key]
  have hxY : x - V.starProjection x - x₀ = x - Y := by
    rw [hY]
    abel
  rw [hxY]
  have hn := Submodule.norm_sq_eq_add_norm_sq_projection (x - Y) W
  have hb := hBn (W.orthogonalProjectionOnto (x - Y))
  calc ‖Wᗮ.orthogonalProjectionOnto (x - Y) - B (W.orthogonalProjectionOnto (x - Y))‖ ^ 2
      ≤ (‖Wᗮ.orthogonalProjectionOnto (x - Y)‖ + ‖W.orthogonalProjectionOnto (x - Y)‖) ^ 2 := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add le_rfl hb)
    _ ≤ 2 * (‖W.orthogonalProjectionOnto (x - Y)‖ ^ 2 +
          ‖Wᗮ.orthogonalProjectionOnto (x - Y)‖ ^ 2) := by
        nlinarith [sq_nonneg (‖Wᗮ.orthogonalProjectionOnto (x - Y)‖ -
          ‖W.orthogonalProjectionOnto (x - Y)‖)]
    _ = 2 * ‖x - Y‖ ^ 2 := by rw [hn]

/-! ### The trace error against one vertical plane -/

/-- The reservoir scale ratio `κ = 2^{-(m+5)}`. -/
def kappa (m : ℕ) : ℝ := 1 / 2 ^ (m + 5)

theorem kappa_pos (m : ℕ) : 0 < kappa m := by
  unfold kappa
  positivity

theorem kappa_le_one (m : ℕ) : kappa m ≤ 1 := by
  unfold kappa
  rw [div_le_one (by positivity)]
  exact one_le_pow₀ (by norm_num)

theorem sq_inner_le (ν z : Spatial n) : ⟪ν, z⟫_ℝ ^ 2 ≤ ‖ν‖ ^ 2 * ‖z‖ ^ 2 := by
  rw [← mul_pow, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm ν z) 2

/-- For every affine spatial plane `x₀ + V` of rank `m`, the best affine fit of `f` on
`P_b(p,r) ∩ K` costs at most `256/κ^2` times the squared distance of the lifted
points to the plane. -/
theorem fit_le_planeCost {W : Submodule ℝ (Spatial n)} {m : ℕ}
    (hW : Module.finrank ℝ W = m) {K : Set (SubspaceSpace W)} (hK : IsCompact K)
    {f : SubspaceSpace W → W.orthogonal} {L : ℝ≥0} (hf : LipschitzOnWith L f K)
    (hL : (L : ℝ) ≤ kappa m / 16) {p : SubspaceSpace W} (hp : p ∈ K) {r : ℝ} (hr : 0 < r)
    (hdens : intrinsicParabolicVolume W (ball p r) ≤
      2 * intrinsicParabolicVolume W (K ∩ ball p r))
    (V : Submodule ℝ (Spatial n)) (hV : Module.finrank ℝ V = m) (x₀ : Spatial n) :
    ⨅ (a : W.orthogonal) (B : W →L[ℝ] W.orthogonal),
        ∫⁻ q in ball p r ∩ K, ‖f q - (a + B q.1)‖ₑ ^ 2 ∂intrinsicParabolicVolume W ≤
      ENNReal.ofReal (256 / kappa m ^ 2) *
        ∫⁻ q in ball p r ∩ K,
          ENNReal.ofReal (‖(lift W f q).1 - V.starProjection (lift W f q).1 - x₀‖ ^ 2)
          ∂intrinsicParabolicVolume W := by
  subst hW
  set κ := kappa (Module.finrank ℝ W) with hκdef
  have hκ : 0 < κ := kappa_pos _
  have hκ1 : κ ≤ 1 := kappa_le_one _
  have hL0 : 0 ≤ (L : ℝ) := L.2
  set s := ball p r ∩ K with hsdef
  have hs : MeasurableSet s := measurableSet_ball.inter hK.isClosed.measurableSet
  set μ := intrinsicParabolicVolume W with hμ
  set cost : SubspaceSpace W → ℝ :=
    fun q => ‖(lift W f q).1 - V.starProjection (lift W f q).1 - x₀‖ ^ 2 with hcostdef
  have hcost : ∀ q, 0 ≤ cost q := fun q => sq_nonneg _
  set I := ∫⁻ q in s, ENNReal.ofReal (cost q) ∂μ with hIdef
  set Vb := μ (ball p r) with hVbdef
  have hVb0 : Vb ≠ 0 := intrinsicParabolicVolume_ball_ne_zero W p hr
  have hVbt : Vb ≠ ∞ := intrinsicParabolicVolume_ball_ne_top W p hr
  have hsVb : μ s ≤ Vb := measure_mono inter_subset_left
  have hfr : ∀ q ∈ s, ‖(f q : Spatial n) - (f p : Spatial n)‖ ≤ L * r := by
    intro q hq
    have h1 : dist (f q) (f p) ≤ L * dist q p := hf.dist_le_mul q hq.2 p hp
    have h2 : dist q p < r := hq.1
    rw [Subtype.dist_eq, dist_eq_norm] at h1
    nlinarith
  have hLr : ∀ q ∈ s, ‖(f q : Spatial n) - (f p : Spatial n)‖ ≤ r := by
    intro q hq
    have hκL : (L : ℝ) ≤ 1 := by linarith
    exact (hfr q hq).trans (by nlinarith)
  have hconst : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (256 / κ ^ 2) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (pow_pos hκ 2)]
    nlinarith
  by_cases hcase : ENNReal.ofReal (κ ^ 2 / 256 * r ^ 2) * Vb < I
  · -- The plane error is large: compare with the constant `f p`.
    calc ⨅ (a : W.orthogonal) (B : W →L[ℝ] W.orthogonal),
          ∫⁻ q in s, ‖f q - (a + B q.1)‖ₑ ^ 2 ∂μ
        ≤ ∫⁻ q in s, ‖f q - (f p + (0 : W →L[ℝ] W.orthogonal) q.1)‖ₑ ^ 2 ∂μ :=
          iInf_le_of_le (f p) (iInf_le _ 0)
      _ ≤ ∫⁻ _ in s, ENNReal.ofReal (r ^ 2) ∂μ := by
          refine setLIntegral_mono' hs fun q hq => ?_
          rw [zero_apply, add_zero, ← ofReal_norm,
            ← ENNReal.ofReal_pow (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hLr q hq) 2)
      _ = ENNReal.ofReal (r ^ 2) * μ s := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (r ^ 2) * Vb := by gcongr
      _ = ENNReal.ofReal (256 / κ ^ 2) * (ENNReal.ofReal (κ ^ 2 / 256 * r ^ 2) * Vb) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 256 / κ ^ 2 by positivity)]
          congr 2
          field_simp
      _ ≤ ENNReal.ofReal (256 / κ ^ 2) * I := mul_le_mul_right hcase.le _
  · -- The plane error is small: the plane is a graph of slope at most one.
    rw [not_lt] at hcase
    have hnormal : ∀ ν ∈ V.orthogonal, 16 * ‖W.starProjection ν‖ ^ 2 ≤ ‖ν‖ ^ 2 := by
      intro ν hν
      set w : W := W.orthogonalProjectionOnto ν with hwdef
      set β : ℝ := ⟪ν, x₀⟫_ℝ - ⟪ν, (f p : Spatial n)⟫_ℝ with hβ
      have hpt : ∀ q ∈ s, (⟪w, q.1⟫_ℝ - β) ^ 2 ≤
          2 * ‖ν‖ ^ 2 * cost q + 2 * ‖ν‖ ^ 2 * ((L : ℝ) * r) ^ 2 := by
        intro q hq
        set z := (lift W f q).1 - V.starProjection (lift W f q).1 - x₀ with hz
        have e1 : ⟪w, q.1⟫_ℝ = ⟪ν, (q.1 : Spatial n)⟫_ℝ := by
          rw [hwdef, real_inner_comm q.1, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
            real_inner_comm ν]
        have e2 : ⟪ν, V.starProjection (lift W f q).1⟫_ℝ = 0 :=
          Submodule.inner_left_of_mem_orthogonal (V.starProjection_apply_mem _) hν
        have hid : ⟪w, q.1⟫_ℝ - β =
            ⟪ν, z⟫_ℝ - ⟪ν, (f q : Spatial n) - (f p : Spatial n)⟫_ℝ := by
          have ez : ⟪ν, z⟫_ℝ = ⟪ν, (q.1 : Spatial n)⟫_ℝ + ⟪ν, (f q : Spatial n)⟫_ℝ -
              ⟪ν, x₀⟫_ℝ := by
            rw [hz, inner_sub_right, inner_sub_right, e2, sub_zero]
            simp only [lift, inner_add_right]
          rw [e1, ez, hβ, inner_sub_right]
          ring
        have h1 : ⟪ν, z⟫_ℝ ^ 2 ≤ ‖ν‖ ^ 2 * cost q := sq_inner_le ν z
        have h2 : ⟪ν, (f q : Spatial n) - (f p : Spatial n)⟫_ℝ ^ 2 ≤
            ‖ν‖ ^ 2 * ((L : ℝ) * r) ^ 2 :=
          (sq_inner_le _ _).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hfr q hq) 2) (sq_nonneg _))
        rw [hid]
        nlinarith [sq_nonneg (⟪ν, z⟫_ℝ + ⟪ν, (f q : Spatial n) - (f p : Spatial n)⟫_ℝ)]
      have hR : ∫⁻ q in s, ENNReal.ofReal ((⟪w, q.1⟫_ℝ - β) ^ 2) ∂μ ≤
          ENNReal.ofReal (2 * ‖ν‖ ^ 2) * I +
            ENNReal.ofReal (2 * ‖ν‖ ^ 2 * ((L : ℝ) * r) ^ 2) * Vb := by
        calc ∫⁻ q in s, ENNReal.ofReal ((⟪w, q.1⟫_ℝ - β) ^ 2) ∂μ
            ≤ ∫⁻ q in s, (ENNReal.ofReal (2 * ‖ν‖ ^ 2) * ENNReal.ofReal (cost q) +
                ENNReal.ofReal (2 * ‖ν‖ ^ 2 * ((L : ℝ) * r) ^ 2)) ∂μ := by
              refine setLIntegral_mono' hs fun q hq => ?_
              rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * ‖ν‖ ^ 2 by positivity),
                ← ENNReal.ofReal_add (mul_nonneg (by positivity) (hcost q))
                  (show (0 : ℝ) ≤ 2 * ‖ν‖ ^ 2 * ((L : ℝ) * r) ^ 2 by positivity)]
              exact ENNReal.ofReal_le_ofReal (hpt q hq)
          _ = ENNReal.ofReal (2 * ‖ν‖ ^ 2) * I +
                ENNReal.ofReal (2 * ‖ν‖ ^ 2 * ((L : ℝ) * r) ^ 2) * μ s := by
              rw [lintegral_add_right _ measurable_const,
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_const]
          _ ≤ _ := by gcongr
      have hres := slab_lintegral_lower_bound W p hr K hK.isClosed.measurableSet hdens w β
      have hκr : r / 2 ^ (Module.finrank ℝ W + 5) = κ * r := by
        rw [hκdef, kappa]
        ring
      rw [hκr] at hres
      have hA : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
          (4 : ℝ≥0∞) * (ENNReal.ofReal a * (ENNReal.ofReal b * Vb) + ENNReal.ofReal c * Vb) =
            ENNReal.ofReal (4 * (a * b + c)) * Vb := by
        intro a b c ha hb hc
        rw [← mul_assoc (ENNReal.ofReal a), ← ENNReal.ofReal_mul ha, ← add_mul,
          ← ENNReal.ofReal_add (mul_nonneg ha hb) hc, ← mul_assoc,
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num), ENNReal.ofReal_ofNat]
      have hcomb : ENNReal.ofReal (‖w‖ ^ 2 * (κ * r) ^ 2) * Vb ≤
          ENNReal.ofReal (4 * (2 * ‖ν‖ ^ 2 * (κ ^ 2 / 256 * r ^ 2) +
            2 * ‖ν‖ ^ 2 * ((L : ℝ) * r) ^ 2)) * Vb := by
        calc ENNReal.ofReal (‖w‖ ^ 2 * (κ * r) ^ 2) * Vb
            ≤ 4 * ∫⁻ q in s, ENNReal.ofReal ((⟪w, q.1⟫_ℝ - β) ^ 2) ∂μ := hres
          _ ≤ 4 * (ENNReal.ofReal (2 * ‖ν‖ ^ 2) * I +
              ENNReal.ofReal (2 * ‖ν‖ ^ 2 * ((L : ℝ) * r) ^ 2) * Vb) := by gcongr
          _ ≤ 4 * (ENNReal.ofReal (2 * ‖ν‖ ^ 2) * (ENNReal.ofReal (κ ^ 2 / 256 * r ^ 2) * Vb) +
              ENNReal.ofReal (2 * ‖ν‖ ^ 2 * ((L : ℝ) * r) ^ 2) * Vb) := by gcongr
          _ = _ := hA _ _ _ (by positivity) (by positivity) (by positivity)
      have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
        ((ENNReal.mul_le_mul_iff_left hVb0 hVbt).mp hcomb)
      have hL2 : (L : ℝ) ^ 2 ≤ κ ^ 2 / 256 := by nlinarith
      have hL3 := mul_le_mul_of_nonneg_left hL2 (show (0 : ℝ) ≤ 8 * ‖ν‖ ^ 2 * r ^ 2 by positivity)
      have hfinal : ‖w‖ ^ 2 * (κ * r) ^ 2 ≤ (‖ν‖ ^ 2 / 16) * (κ * r) ^ 2 := by
        nlinarith [hL3]
      have hw2 : ‖w‖ ^ 2 ≤ ‖ν‖ ^ 2 / 16 :=
        le_of_mul_le_mul_right hfinal (pow_pos (mul_pos hκ hr) 2)
      have hwn : ‖W.starProjection ν‖ = ‖w‖ := rfl
      rw [hwn]
      linarith
    obtain ⟨a, B, hAB⟩ := exists_affine_graph_of_normal_bound W V hV x₀ hnormal
    calc ⨅ (a : W.orthogonal) (B : W →L[ℝ] W.orthogonal),
          ∫⁻ q in s, ‖f q - (a + B q.1)‖ₑ ^ 2 ∂μ
        ≤ ∫⁻ q in s, ‖f q - (a + B q.1)‖ₑ ^ 2 ∂μ := iInf_le_of_le a (iInf_le _ B)
      _ ≤ ∫⁻ q in s, 2 * ENNReal.ofReal (cost q) ∂μ := by
          refine lintegral_mono fun q => ?_
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
          calc ENNReal.ofReal (‖f q - (a + B q.1)‖ ^ 2) ≤ ENNReal.ofReal (2 * cost q) :=
                ENNReal.ofReal_le_ofReal (hAB q.1 (f q))
            _ = 2 * ENNReal.ofReal (cost q) := by
                rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      _ = 2 * I := lintegral_const_mul' _ _ (by norm_num)
      _ ≤ ENNReal.ofReal (256 / κ ^ 2) * I := mul_le_mul_left hconst _

/-- The scale change `2^k (2r)^{-k} = r^{-k}` in extended reals. -/
theorem two_pow_mul_inv_ofReal_two_mul {r : ℝ} (hr : 0 < r) (k : ℕ) :
    2 ^ k * (ENNReal.ofReal (2 * r))⁻¹ ^ k = (ENNReal.ofReal r)⁻¹ ^ k := by
  have _ := hr
  rw [← mul_pow, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← mul_assoc,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

end NaturalBridge

open NaturalBridge in
/-- **Natural beta controls the trace error**, small slope: the estimate
`traceErrorSq_le_vertical_betaSq` with `L₀ = 2^{-(m+9)}` and
`C = 2^{m+4} · 2 ω_m · 256 κ^{-2}`, `κ = 2^{-(m+5)}`. -/
theorem traceErrorSq_le_vertical_betaSq_small (m : ℕ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ L₀ ≤ 1 ∧ ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (W : Submodule ℝ (Spatial n)),
      Module.finrank ℝ W = m → Module.finrank ℝ W.orthogonal = d →
      ∀ (K : Set (SubspaceSpace W)) (f : SubspaceSpace W → W.orthogonal) (L : ℝ≥0),
        IsCompact K → LipschitzOnWith L f K → (L : ℝ) ≤ L₀ →
        ∀ p ∈ K, ∀ r : ℝ, 0 < r →
          intrinsicParabolicVolume W (Metric.ball p r) ≤
            2 * intrinsicParabolicVolume W (K ∩ Metric.ball p r) →
          traceErrorSq (intrinsicParabolicVolume W) K f p r ≤
            ENNReal.ofReal C *
              betaSq ((hausdorffP n (m + 2)).restrict
                  ((fun q : SubspaceSpace W =>
                    (((q.1 : Spatial n) + (f q : Spatial n), q.2) : Space n)) '' K))
                (m + 2) .vertical
                (((p.1 : Spatial n) + (f p : Spatial n), p.2) : Space n) (2 * r) := by
  have hκ := kappa_pos m
  have hκ1 := kappa_le_one m
  refine ⟨kappa m / 16, div_pos hκ (by norm_num), by linarith, fun d => ?_⟩
  set c₀ : ℝ≥0∞ := 2 ^ (m + 4) * (2 * omega m) * ENNReal.ofReal (256 / kappa m ^ 2) with hc₀
  have hc₀0 : c₀ ≠ 0 := by
    have h1 : (0 : ℝ≥0∞) < 2 * omega m := ENNReal.mul_pos (by norm_num) (omega_pos m).ne'
    have h2 : (0 : ℝ≥0∞) < ENNReal.ofReal (256 / kappa m ^ 2) :=
      ENNReal.ofReal_pos.mpr (div_pos (by norm_num) (pow_pos hκ 2))
    have h3 : (0 : ℝ≥0∞) < 2 ^ (m + 4) := by positivity
    exact (ENNReal.mul_pos (ENNReal.mul_pos h3.ne' h1.ne').ne' h2.ne').ne'
  have hc₀t : c₀ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness)
      (ENNReal.mul_ne_top (by norm_num) (omega_lt_top m).ne)) ENNReal.ofReal_ne_top
  refine ⟨c₀.toReal, ENNReal.toReal_pos hc₀0 hc₀t, ?_⟩
  intro n W hW _ K f L hK hf hL p hp r hr hdens
  rw [ENNReal.ofReal_toReal hc₀t]
  change affineErrorSq ((intrinsicParabolicVolume W).restrict K) f p r ≤
    c₀ * betaSq ((hausdorffP n (m + 2)).restrict (lift W f '' K)) (m + 2) .vertical
      (lift W f p) (2 * r)
  have h2r : 0 < 2 * r := mul_pos two_pos hr
  have hL1 : (L : ℝ) ≤ 1 := by linarith
  rw [affineErrorSq_of_pos _ _ _ hr, betaSq_of_pos _ _ _ _ h2r]
  have hbd : baseDimension W + 2 = m + 2 + 2 := by rw [baseDimension, hW]
  rw [hbd]
  have hk0 : (ENNReal.ofReal (2 * r))⁻¹ ^ (m + 2 + 2) ≠ 0 :=
    pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
  have hkt : (ENNReal.ofReal (2 * r))⁻¹ ^ (m + 2 + 2) ≠ ∞ :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr h2r).ne')
  rw [ENNReal.mul_iInf_of_ne hk0 hkt, ENNReal.mul_iInf_of_ne hc₀0 hc₀t]
  refine le_iInf fun M => ?_
  let M' : VerticalModel n (m + 2) := M
  have hV : Module.finrank ℝ M'.spatial.direction = m := by
    have h1 := M'.spatial.rank_eq
    have h2 := M'.rank_eq
    omega
  -- The trace fit against this plane.
  have hfit := fit_le_planeCost hW hK hf hL hp hr hdens M'.spatial.direction hV
    M'.spatial.anchor
  -- The plane cost is the model cost of the lifted points.
  have hcost : ∀ q, ENNReal.ofReal (‖(lift W f q).1 -
      M'.spatial.direction.starProjection (lift W f q).1 - M'.spatial.anchor‖ ^ 2) =
      modelCost (T := .vertical) M' (lift W f q) := fun q =>
    (VerticalModel.modelCost_point M' _ q.2.val).symm
  simp only [hcost] at hfit
  have hpush := lintegral_comp_lift_le hW hK hf hL1 hp (r := r)
    (measurable_modelCost (T := .vertical) M')
  have hrestr : ∀ (a : W.orthogonal) (B : W →L[ℝ] W.orthogonal),
      affineFitIntegral ((intrinsicParabolicVolume W).restrict K) f a B p r =
        ∫⁻ q in ball p r ∩ K, ‖f q - (a + B q.1)‖ₑ ^ 2 ∂intrinsicParabolicVolume W := by
    intro a B
    rw [affineFitIntegral, Measure.restrict_restrict measurableSet_ball]
  simp only [hrestr]
  calc (ENNReal.ofReal r)⁻¹ ^ (m + 2 + 2) *
        ⨅ (a : W.orthogonal) (B : W →L[ℝ] W.orthogonal),
          ∫⁻ q in ball p r ∩ K, ‖f q - (a + B q.1)‖ₑ ^ 2 ∂intrinsicParabolicVolume W
      ≤ (ENNReal.ofReal r)⁻¹ ^ (m + 2 + 2) *
          (ENNReal.ofReal (256 / kappa m ^ 2) *
            ((2 * omega m) * fit ((hausdorffP n (m + 2)).restrict (lift W f '' K)) M
              (lift W f p) (2 * r))) := by
        exact mul_le_mul_right (hfit.trans (mul_le_mul_right hpush _)) _
    _ = c₀ * ((ENNReal.ofReal (2 * r))⁻¹ ^ (m + 2 + 2) *
          fit ((hausdorffP n (m + 2)).restrict (lift W f '' K)) M (lift W f p) (2 * r)) := by
        rw [← two_pow_mul_inv_ofReal_two_mul hr (m + 2 + 2), hc₀]
        ring

end ParabolicRectifiability
