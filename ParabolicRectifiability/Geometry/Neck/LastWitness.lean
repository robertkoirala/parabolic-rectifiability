import ParabolicRectifiability.Geometry.Neck.CoherentData
import ParabolicRectifiability.Measure.BetaLaws
import ParabolicRectifiability.Measure.ScaleIntegrals

/-!
# Charging: the last witness and the node error mass

Proofs of the last-witness bound and the node error mass bound. Each `*_proof` theorem
has the type of the statement of the same name without the suffix in
the `ChargeCollapse` namespace.

* `lastWitness_sum_proof` (the last-witness bound). For `s ∈ (H r_j, 2 H r_j)` the testing ball `P(g, c r_j)` lies in `P(y, s)`
  because `d_P(g, y) ≤ A r_j` and `A + c ≤ H`; ball monotonicity of the natural beta
  (`betaSq_le_of_ball_subset`) gives `b(g, c r_j) ≤ (2H/c)^{k+2} b(y, s)`. Integrating
  against `ds/s` over the window, whose `ds/s`-measure is `log 2`, charges `b(g, c r_j)` to
  the window integral at `y`. The windows of the levels `j ≤ J` are pairwise disjoint
  (`r_{j+1} = r_j / 10`) and lie above `H r_J ≥ F r_J ≥ f(y)`, so their integrals add up to
  at most the tail `∫_{f(y)}^∞ b(y,s) ds/s ≤ B`. Levels deeper than `J` are empty.
* `lastWitness_commonCenter_proof` and `lastWitness_movingPoint_proof`
  select the deepest nonempty level `J ≤ N` and one center `y` on it, check the comparison
  `d_P(g, y) ≤ A r_j` by the triangle inequality (and, for a moving point, the geometric sum
  `∑_{l=j}^{J-1} r_l ≤ (10/9) r_j`), and apply the first proof; an empty collection has sum
  zero. The witness is chosen once for the finite collection; no measurable choice is used.
* `nodeErrorMass_le_proof` is Chebyshev's inequality for the fit of the
  original source at radius `40 r`, followed by cancellation of the finite positive factor
  `r^2`.

The source is always the given measure; no restriction or subtraction is formed. All
quantities are extended nonnegative reals; unavailable families need no separate argument
(their positive-radius betas are `⊤`, and the inequalities hold in `ℝ≥0∞`).
-/

noncomputable section

namespace ParabolicRectifiability

namespace ChargeCollapse

open MeasureTheory Set
open scoped ENNReal

/-! ## Scales and windows -/

/-- The scales `r_j = 10^{-j} r_0` are positive. -/
theorem gm1_coherentScale_pos {r₀ : ℝ} (hr₀ : 0 < r₀) (j : ℕ) : 0 < coherentScale r₀ j :=
  div_pos hr₀ (pow_pos (by norm_num) j)

/-- Consecutive scales differ by the factor ten. -/
theorem gm1_coherentScale_succ (r₀ : ℝ) (j : ℕ) :
    coherentScale r₀ (j + 1) = coherentScale r₀ j / 10 := by
  simp only [coherentScale, pow_succ, div_div]

/-- The scales decrease with the level. -/
theorem gm1_coherentScale_anti {r₀ : ℝ} (hr₀ : 0 < r₀) {i j : ℕ} (h : i ≤ j) :
    coherentScale r₀ j ≤ coherentScale r₀ i := by
  simp only [coherentScale]
  exact div_le_div_of_nonneg_left hr₀.le (by positivity) (pow_le_pow_right₀ (by norm_num) h)

/-- Windows of distinct levels are separated: `2 H r_{l'} < H r_l` for `l < l'`. -/
theorem gm1_window_gap {r₀ H : ℝ} (hr₀ : 0 < r₀) (hH : 0 < H) {l l' : ℕ} (h : l < l') :
    2 * (H * coherentScale r₀ l') < H * coherentScale r₀ l := by
  have h1 : H * coherentScale r₀ l' ≤ H * coherentScale r₀ (l + 1) :=
    mul_le_mul_of_nonneg_left (gm1_coherentScale_anti hr₀ h) hH.le
  have h2 : H * coherentScale r₀ (l + 1) = H * coherentScale r₀ l / 10 := by
    rw [gm1_coherentScale_succ]
    ring
  have h3 : 0 < H * coherentScale r₀ l := mul_pos hH (gm1_coherentScale_pos hr₀ l)
  linarith

/-- The `dr/r` measure of the dyadic window `(ρ, 2ρ)` is `log 2`. (The same computation
as `scaleMeasure_Ioo_two_mul` of the time-flattening lemmas,
repeated here to avoid importing the horizontal cover modules.) -/
theorem gm1_scaleMeasure_Ioo_two_mul {ρ : ℝ} (hρ : 0 < ρ) :
    scaleMeasure (Ioo ρ (2 * ρ)) = ENNReal.ofReal (Real.log 2) := by
  rw [scaleMeasure_apply _ measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo ρ (2 * ρ) ⊆ Ioi 0 from fun r hr => hρ.trans hr.1)]
  have hcont : ContinuousOn (fun r : ℝ => 1 / r) (Icc ρ (2 * ρ)) :=
    continuousOn_const.div continuousOn_id fun r hr => (hρ.trans_le hr.1).ne'
  have hint : IntegrableOn (fun r : ℝ => 1 / r) (Ioo ρ (2 * ρ)) volume :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
      integral_one_div_of_pos hρ (by linarith), mul_div_cancel_right₀ _ hρ.ne']
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (one_div_pos.mpr (hρ.trans hr.1)).le

/-- **Window transfer** (the beta transfer integrated over one window). If
`d_P(g, y) ≤ A r` and `A + c ≤ H`, then
`log 2 · b(g, c r) ≤ (2H/c)^{k+2} ∫_{(Hr, 2Hr)} b(y, s) ds/s`. -/
theorem gm1_log_two_mul_betaSq_le_window {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (F : FamilyKind) {g y : Space n} {A c H r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hgy : dist g y ≤ A * r) (hH : A + c ≤ H) (hH0 : 0 < H) :
    ENNReal.ofReal (Real.log 2) * betaSq μ k F g (c * r) ≤
      ENNReal.ofReal (2 * H / c) ^ (k + 2) *
        ∫⁻ s in Ioo (H * r) (2 * (H * r)), betaSq μ k F y s ∂scaleMeasure := by
  have hcr : 0 < c * r := mul_pos hc hr
  have hHr : 0 < H * r := mul_pos hH0 hr
  have hAcH : A * r + c * r ≤ H * r := by
    have := mul_le_mul_of_nonneg_right hH hr.le
    rw [add_mul] at this
    exact this
  have hcmp : ∀ s ∈ Ioo (H * r) (2 * (H * r)),
      betaSq μ k F g (c * r) ≤ ENNReal.ofReal (2 * H / c) ^ (k + 2) * betaSq μ k F y s := by
    intro s hs
    have hs0 : 0 < s := hHr.trans hs.1
    have hball : Metric.ball g (c * r) ⊆ Metric.ball y s := by
      apply Metric.ball_subset_ball'
      linarith [hs.1]
    have hratio : ENNReal.ofReal (s / (c * r)) ≤ ENNReal.ofReal (2 * H / c) := by
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_div_iff₀ hcr hc]
      nlinarith [mul_lt_mul_of_pos_right hs.2 hc]
    calc betaSq μ k F g (c * r)
        ≤ ENNReal.ofReal (s / (c * r)) ^ (k + 2) * betaSq μ k F y s :=
          betaSq_le_of_ball_subset μ k F hcr hs0 hball
      _ ≤ ENNReal.ofReal (2 * H / c) ^ (k + 2) * betaSq μ k F y s := by gcongr
  calc ENNReal.ofReal (Real.log 2) * betaSq μ k F g (c * r)
      = ∫⁻ _s in Ioo (H * r) (2 * (H * r)), betaSq μ k F g (c * r) ∂scaleMeasure := by
        rw [setLIntegral_const, gm1_scaleMeasure_Ioo_two_mul hHr, mul_comm]
    _ ≤ ∫⁻ s in Ioo (H * r) (2 * (H * r)),
          ENNReal.ofReal (2 * H / c) ^ (k + 2) * betaSq μ k F y s ∂scaleMeasure :=
        setLIntegral_mono' measurableSet_Ioo hcmp
    _ = ENNReal.ofReal (2 * H / c) ^ (k + 2) *
          ∫⁻ s in Ioo (H * r) (2 * (H * r)), betaSq μ k F y s ∂scaleMeasure :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

/-- The windows `(H r_j, 2 H r_j)`, `j ≤ J`, are pairwise disjoint and lie above `H r_J`;
hence their integrals at one point add up to at most its integral over `(H r_J, ∞)`. -/
theorem gm1_sum_window_le {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (F : FamilyKind)
    (y : Space n) {r₀ H : ℝ} (hr₀ : 0 < r₀) (hH : 0 < H) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1),
        ∫⁻ s in Ioo (H * coherentScale r₀ j) (2 * (H * coherentScale r₀ j)),
          betaSq μ k F y s ∂scaleMeasure ≤
      ∫⁻ s in Ioi (H * coherentScale r₀ J), betaSq μ k F y s ∂scaleMeasure := by
  have hd : Set.PairwiseDisjoint (↑(Finset.range (J + 1)) : Set ℕ)
      (fun j => Ioo (H * coherentScale r₀ j) (2 * (H * coherentScale r₀ j))) := by
    intro l _ l' _ hne
    simp only [Function.onFun]
    rcases lt_or_gt_of_ne hne with h | h
    · refine Set.disjoint_left.mpr fun s hs hs' => ?_
      have := gm1_window_gap hr₀ hH h
      linarith [hs.1, hs'.2]
    · refine Set.disjoint_left.mpr fun s hs hs' => ?_
      have := gm1_window_gap hr₀ hH h
      linarith [hs.2, hs'.1]
  calc ∑ j ∈ Finset.range (J + 1),
        ∫⁻ s in Ioo (H * coherentScale r₀ j) (2 * (H * coherentScale r₀ j)),
          betaSq μ k F y s ∂scaleMeasure
      = ∫⁻ s in ⋃ j ∈ Finset.range (J + 1),
          Ioo (H * coherentScale r₀ j) (2 * (H * coherentScale r₀ j)),
          betaSq μ k F y s ∂scaleMeasure :=
        (lintegral_biUnion_finset hd (fun j _ => measurableSet_Ioo) _).symm
    _ ≤ ∫⁻ s in Ioi (H * coherentScale r₀ J), betaSq μ k F y s ∂scaleMeasure := by
        apply lintegral_mono_set
        intro s hs
        simp only [Set.mem_iUnion] at hs
        obtain ⟨j, hj, hsj⟩ := hs
        have hjJ : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have h1 : H * coherentScale r₀ J ≤ H * coherentScale r₀ j :=
          mul_le_mul_of_nonneg_left (gm1_coherentScale_anti hr₀ hjJ) hH.le
        exact Set.mem_Ioi.mpr (lt_of_le_of_lt h1 hsj.1)

/-- Division by `log 2` and collection of the real constants. -/
theorem gm1_bound_of_log_two_mul {X : ℝ≥0∞} {N₀ : ℕ} {P B : ℝ} (hP : 0 ≤ P)
    (h : ENNReal.ofReal (Real.log 2) * X ≤ (N₀ : ℝ≥0∞) * ENNReal.ofReal P * ENNReal.ofReal B) :
    X ≤ ENNReal.ofReal (N₀ / Real.log 2 * P * B) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hinv : ENNReal.ofReal (1 / Real.log 2) * ENNReal.ofReal (Real.log 2) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hlog.ne', ENNReal.ofReal_one]
  have hN : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
  have hrhs : ENNReal.ofReal (1 / Real.log 2) *
      ((N₀ : ℝ≥0∞) * ENNReal.ofReal P * ENNReal.ofReal B) =
      ENNReal.ofReal (N₀ / Real.log 2 * P * B) := by
    have e : (N₀ / Real.log 2 * P * B : ℝ) = 1 / Real.log 2 * ((N₀ * P) * B) := by ring
    rw [e, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / Real.log 2),
      ENNReal.ofReal_mul (mul_nonneg hN hP), ENNReal.ofReal_mul hN, ENNReal.ofReal_natCast]
  calc X = ENNReal.ofReal (1 / Real.log 2) * (ENNReal.ofReal (Real.log 2) * X) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ ENNReal.ofReal (1 / Real.log 2) *
        ((N₀ : ℝ≥0∞) * ENNReal.ofReal P * ENNReal.ofReal B) := by gcongr
    _ = ENNReal.ofReal (N₀ / Real.log 2 * P * B) := hrhs

/-! ## The last witness -/

/-- **Last-witness bound.** The type of `ChargeCollapse.lastWitness_sum`. -/
theorem lastWitness_sum_proof {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ)
    (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n)) (N₀ : ℕ)
    (hcard : ∀ j ≤ N, (I j).card ≤ N₀) (J : ℕ) (hJ : J ≤ N)
    (hdeep : ∀ j, J < j → j ≤ N → I j = ∅) (y : Space n) (hyI : y ∈ I J) (hyS : y ∈ S)
    (Fc : ℝ) (hfy : f y ≤ Fc * coherentScale r₀ J) (A : ℝ)
    (hA : ∀ j ≤ J, ∀ g ∈ I j, dist g y ≤ A * coherentScale r₀ j)
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : A + c ≤ H) :
    ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) := by
  have hr : ∀ j, 0 < coherentScale r₀ j := gm1_coherentScale_pos hr₀
  -- the witness forces `A ≥ 0`, hence `H > 0`
  have hA0 : 0 ≤ A := by
    have h := hA J le_rfl y hyI
    rw [dist_self] at h
    nlinarith [hr J]
  have hH0 : 0 < H := by linarith
  have h2Hc : 0 ≤ 2 * H / c := div_nonneg (by linarith) hc.le
  -- levels deeper than `J` are empty
  have hsplit : ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) =
      ∑ j ∈ Finset.range (J + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro j hjN hjJ
      simp only [Finset.mem_range] at hjN hjJ
      rw [hdeep j (by omega) (by omega), Finset.sum_empty]
  -- one level: at most `N₀` centers, each charged to the window of the level
  have hlevel : ∀ j ≤ J, ENNReal.ofReal (Real.log 2) *
      ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) ≤
      (N₀ : ℝ≥0∞) * (ENNReal.ofReal (2 * H / c) ^ (k + 2) *
        ∫⁻ s in Ioo (H * coherentScale r₀ j) (2 * (H * coherentScale r₀ j)),
          betaSq μ k F y s ∂scaleMeasure) := by
    intro j hj
    rw [Finset.mul_sum]
    calc ∑ g ∈ I j, ENNReal.ofReal (Real.log 2) * betaSq μ k F g (c * coherentScale r₀ j)
        ≤ (I j).card • (ENNReal.ofReal (2 * H / c) ^ (k + 2) *
            ∫⁻ s in Ioo (H * coherentScale r₀ j) (2 * (H * coherentScale r₀ j)),
              betaSq μ k F y s ∂scaleMeasure) :=
          Finset.sum_le_card_nsmul _ _ _ fun g hg =>
            gm1_log_two_mul_betaSq_le_window μ k F hc (hr j) (hA j hj g hg) hH₂ hH0
      _ = ((I j).card : ℝ≥0∞) * (ENNReal.ofReal (2 * H / c) ^ (k + 2) *
            ∫⁻ s in Ioo (H * coherentScale r₀ j) (2 * (H * coherentScale r₀ j)),
              betaSq μ k F y s ∂scaleMeasure) := nsmul_eq_mul _ _
      _ ≤ (N₀ : ℝ≥0∞) * (ENNReal.ofReal (2 * H / c) ^ (k + 2) *
            ∫⁻ s in Ioo (H * coherentScale r₀ j) (2 * (H * coherentScale r₀ j)),
              betaSq μ k F y s ∂scaleMeasure) := by
          gcongr
          exact_mod_cast hcard j (hj.trans hJ)
  -- the windows lie above `f(y)`
  have hwin : ∑ j ∈ Finset.range (J + 1),
      ∫⁻ s in Ioo (H * coherentScale r₀ j) (2 * (H * coherentScale r₀ j)),
        betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B := by
    refine (gm1_sum_window_le μ k F y hr₀ hH0 J).trans ?_
    refine le_trans (lintegral_mono_set ?_) (htail y hyS)
    intro s hs
    have h1 : Fc * coherentScale r₀ J ≤ H * coherentScale r₀ J :=
      mul_le_mul_of_nonneg_right hH₁ (hr J).le
    exact Set.mem_Ioi.mpr (lt_of_le_of_lt (hfy.trans h1) hs)
  have hmain : ENNReal.ofReal (Real.log 2) *
      ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) ≤
      (N₀ : ℝ≥0∞) * ENNReal.ofReal ((2 * H / c) ^ (k + 2)) * ENNReal.ofReal B := by
    rw [hsplit, Finset.mul_sum, ENNReal.ofReal_pow h2Hc]
    calc ∑ j ∈ Finset.range (J + 1), ENNReal.ofReal (Real.log 2) *
          ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j)
        ≤ ∑ j ∈ Finset.range (J + 1), (N₀ : ℝ≥0∞) *
            (ENNReal.ofReal (2 * H / c) ^ (k + 2) *
              ∫⁻ s in Ioo (H * coherentScale r₀ j) (2 * (H * coherentScale r₀ j)),
                betaSq μ k F y s ∂scaleMeasure) :=
          Finset.sum_le_sum fun j hj =>
            hlevel j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      _ = (N₀ : ℝ≥0∞) * ENNReal.ofReal (2 * H / c) ^ (k + 2) *
            ∑ j ∈ Finset.range (J + 1),
              ∫⁻ s in Ioo (H * coherentScale r₀ j) (2 * (H * coherentScale r₀ j)),
                betaSq μ k F y s ∂scaleMeasure := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
      _ ≤ (N₀ : ℝ≥0∞) * ENNReal.ofReal (2 * H / c) ^ (k + 2) * ENNReal.ofReal B := by
          gcongr
  exact gm1_bound_of_log_two_mul (pow_nonneg h2Hc _) hmain

/-! ## The two forms -/

/-- **Last witness, common center.** The type of `ChargeCollapse.lastWitness_commonCenter`. -/
theorem lastWitness_commonCenter_proof {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ]
    (k : ℕ) (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n)) (N₀ : ℕ)
    (hcard : ∀ j ≤ N, (I j).card ≤ N₀) (hS : ∀ j ≤ N, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j ≤ N, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (w : Space n) (A₀ : ℝ)
    (hw : ∀ j ≤ N, ∀ g ∈ I j, dist g w ≤ A₀ * coherentScale r₀ j)
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : 2 * A₀ + c ≤ H) :
    ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : Finset ℕ, L = (Finset.range (N + 1)).filter (fun j => (I j).Nonempty) :=
    ⟨_, rfl⟩
  by_cases hne : L.Nonempty
  · have hJmem := Finset.max'_mem L hne
    have hJle : ∀ j ∈ L, j ≤ L.max' hne := fun j hj => Finset.le_max' L j hj
    generalize L.max' hne = J at hJmem hJle
    rw [hL, Finset.mem_filter, Finset.mem_range] at hJmem
    obtain ⟨hJN, y, hyI⟩ := hJmem
    have hJN' : J ≤ N := Nat.lt_succ_iff.mp hJN
    have hdeep : ∀ j, J < j → j ≤ N → I j = ∅ := by
      intro j hj hjN
      by_contra hne'
      have hjL : j ∈ L := by
        rw [hL, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.lt_succ_of_le hjN, Finset.nonempty_iff_ne_empty.mpr hne'⟩
      have := hJle j hjL
      omega
    have hr : ∀ j, 0 < coherentScale r₀ j := gm1_coherentScale_pos hr₀
    have hA₀ : 0 ≤ A₀ := by
      have h := hw J hJN' y hyI
      nlinarith [dist_nonneg (x := y) (y := w), hr J]
    have hA : ∀ j ≤ J, ∀ g ∈ I j, dist g y ≤ 2 * A₀ * coherentScale r₀ j := by
      intro j hj g hg
      have h1 := hw j (hj.trans hJN') g hg
      have h2 := hw J hJN' y hyI
      have h4 : A₀ * coherentScale r₀ J ≤ A₀ * coherentScale r₀ j :=
        mul_le_mul_of_nonneg_left (gm1_coherentScale_anti hr₀ hj) hA₀
      have h5 := dist_triangle_right g y w
      linarith
    exact lastWitness_sum_proof μ k F S f B htail r₀ hr₀ N I N₀ hcard J hJN' hdeep y hyI
      (hS J hJN' y hyI) Fc (hf J hJN' y hyI) (2 * A₀) hA c H hc hH₁ hH₂
  · have hzero : ∀ j ∈ Finset.range (N + 1),
        ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) = 0 := by
      intro j hj
      have hIj : I j = ∅ := by
        by_contra hne'
        exact hne ⟨j, by
          rw [hL, Finset.mem_filter]
          exact ⟨hj, Finset.nonempty_iff_ne_empty.mpr hne'⟩⟩
      rw [hIj, Finset.sum_empty]
    rw [Finset.sum_eq_zero hzero]
    exact zero_le

/-- Along a moving point with steps `d_P(q_{l+1}, q_l) ≤ D₀ r_l`, the displacement over the
levels `j, …, j + m` is at most `(10/9) D₀ (r_j - r_{j+m})`. -/
theorem gm1_movingPoint_dist {n : ℕ} {r₀ : ℝ} {N : ℕ} {q : ℕ → Space n} {D₀ : ℝ}
    (hq : ∀ j < N, dist (q (j + 1)) (q j) ≤ D₀ * coherentScale r₀ j) (j : ℕ) :
    ∀ m, j + m ≤ N →
      dist (q (j + m)) (q j) ≤ 10 / 9 * D₀ * (coherentScale r₀ j - coherentScale r₀ (j + m)) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have e : j + (m + 1) = j + m + 1 := by omega
    rw [e]
    have h1 := ih (by omega)
    have h2 := hq (j + m) (by omega)
    have h3 := dist_triangle (q (j + m + 1)) (q (j + m)) (q j)
    have h4 := gm1_coherentScale_succ r₀ (j + m)
    rw [h4]
    linarith

/-- **Last witness, moving point.** The type of `ChargeCollapse.lastWitness_movingPoint`. -/
theorem lastWitness_movingPoint_proof {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ]
    (k : ℕ) (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n)) (N₀ : ℕ)
    (hcard : ∀ j ≤ N, (I j).card ≤ N₀) (hS : ∀ j ≤ N, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j ≤ N, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (q : ℕ → Space n) (A₀ D₀ : ℝ)
    (hD₀ : 0 ≤ D₀) (hq : ∀ j < N, dist (q (j + 1)) (q j) ≤ D₀ * coherentScale r₀ j)
    (hw : ∀ j ≤ N, ∀ g ∈ I j, dist g (q j) ≤ A₀ * coherentScale r₀ j)
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : 2 * A₀ + 10 / 9 * D₀ + c ≤ H) :
    ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : Finset ℕ, L = (Finset.range (N + 1)).filter (fun j => (I j).Nonempty) :=
    ⟨_, rfl⟩
  by_cases hne : L.Nonempty
  · have hJmem := Finset.max'_mem L hne
    have hJle : ∀ j ∈ L, j ≤ L.max' hne := fun j hj => Finset.le_max' L j hj
    generalize L.max' hne = J at hJmem hJle
    rw [hL, Finset.mem_filter, Finset.mem_range] at hJmem
    obtain ⟨hJN, y, hyI⟩ := hJmem
    have hJN' : J ≤ N := Nat.lt_succ_iff.mp hJN
    have hdeep : ∀ j, J < j → j ≤ N → I j = ∅ := by
      intro j hj hjN
      by_contra hne'
      have hjL : j ∈ L := by
        rw [hL, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.lt_succ_of_le hjN, Finset.nonempty_iff_ne_empty.mpr hne'⟩
      have := hJle j hjL
      omega
    have hr : ∀ j, 0 < coherentScale r₀ j := gm1_coherentScale_pos hr₀
    have hA₀ : 0 ≤ A₀ := by
      have h := hw J hJN' y hyI
      nlinarith [dist_nonneg (x := y) (y := q J), hr J]
    have hA : ∀ j ≤ J, ∀ g ∈ I j,
        dist g y ≤ (2 * A₀ + 10 / 9 * D₀) * coherentScale r₀ j := by
      intro j hj g hg
      have h1 := hw j (hj.trans hJN') g hg
      have h2 := hw J hJN' y hyI
      have h3 := gm1_movingPoint_dist hq j (J - j) (by omega)
      rw [Nat.add_sub_of_le hj] at h3
      have h4 : A₀ * coherentScale r₀ J ≤ A₀ * coherentScale r₀ j :=
        mul_le_mul_of_nonneg_left (gm1_coherentScale_anti hr₀ hj) hA₀
      have h5 : 0 ≤ D₀ * coherentScale r₀ J := mul_nonneg hD₀ (hr J).le
      have h6 := dist_triangle g (q j) y
      have h7 := dist_triangle (q j) (q J) y
      rw [dist_comm (q j) (q J)] at h7
      rw [dist_comm (q J) y] at h7
      linarith
    exact lastWitness_sum_proof μ k F S f B htail r₀ hr₀ N I N₀ hcard J hJN' hdeep y hyI
      (hS J hJN' y hyI) Fc (hf J hJN' y hyI) (2 * A₀ + 10 / 9 * D₀) hA c H hc hH₁ hH₂
  · have hzero : ∀ j ∈ Finset.range (N + 1),
        ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) = 0 := by
      intro j hj
      have hIj : I j = ∅ := by
        by_contra hne'
        exact hne ⟨j, by
          rw [hL, Finset.mem_filter]
          exact ⟨hj, Finset.nonempty_iff_ne_empty.mpr hne'⟩⟩
      rw [hIj, Finset.sum_empty]
    rw [Finset.sum_eq_zero hzero]
    exact zero_le

/-! ## Node error mass -/

/-- **Node error by Chebyshev.** The type of `ChargeCollapse.nodeErrorMass_le`. On `e ⊆ P(g, r) ⊆ P(g, 40 r)` the cost exceeds
`(θ r)^2`, so `(θ r)^2 μ(e) ≤ fit_{40r}(Pm) ≤ (40 r)^{k+2} b(g, 40 r)`; cancel `r^2`. -/
theorem nodeErrorMass_le_proof {n k : ℕ} {F : FamilyKind} (μ : Measure (Space n)) (g : Space n)
    {r θ : ℝ} (hr : 0 < r) (_hθ : 0 < θ) (Pm : Models n k F)
    (hfit : fit μ Pm g (40 * r) ≤ ENNReal.ofReal ((40 * r) ^ (k + 2)) * betaSq μ k F g (40 * r))
    (e : Set (Space n)) (hem : MeasurableSet e) (he : e ⊆ Metric.ball g r)
    (htube : ∀ z ∈ e, ENNReal.ofReal ((θ * r) ^ 2) < modelCost Pm z) :
    ENNReal.ofReal (θ ^ 2) * μ e ≤
      ENNReal.ofReal (40 ^ (k + 2)) * ENNReal.ofReal (r ^ k) * betaSq μ k F g (40 * r) := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hsub : e ⊆ Metric.ball g (40 * r) := he.trans (Metric.ball_subset_ball (by linarith))
  have hcheb : ENNReal.ofReal ((θ * r) ^ 2) * μ e ≤ fit μ Pm g (40 * r) := by
    calc ENNReal.ofReal ((θ * r) ^ 2) * μ e
        = ∫⁻ _z in e, ENNReal.ofReal ((θ * r) ^ 2) ∂μ := (setLIntegral_const e _).symm
      _ ≤ ∫⁻ z in e, modelCost Pm z ∂μ := setLIntegral_mono' hem fun z hz => (htube z hz).le
      _ ≤ ∫⁻ z in Metric.ball g (40 * r), modelCost Pm z ∂μ := lintegral_mono_set hsub
      _ = fit μ Pm g (40 * r) := rfl
  have h1 : ENNReal.ofReal ((θ * r) ^ 2) =
      ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (θ ^ 2) := by
    rw [← ENNReal.ofReal_mul hr2.le]
    congr 1
    ring
  have h2 : ENNReal.ofReal ((40 * r) ^ (k + 2)) =
      ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal (40 ^ (k + 2)) * ENNReal.ofReal (r ^ k)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hr2.le]
    congr 1
    ring
  have hmain : ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal (θ ^ 2) * μ e) ≤
      ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal (40 ^ (k + 2)) * ENNReal.ofReal (r ^ k) *
        betaSq μ k F g (40 * r)) := by
    calc ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal (θ ^ 2) * μ e)
        = ENNReal.ofReal ((θ * r) ^ 2) * μ e := by rw [h1, mul_assoc]
      _ ≤ fit μ Pm g (40 * r) := hcheb
      _ ≤ ENNReal.ofReal ((40 * r) ^ (k + 2)) * betaSq μ k F g (40 * r) := hfit
      _ = ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal (40 ^ (k + 2)) * ENNReal.ofReal (r ^ k) *
            betaSq μ k F g (40 * r)) := by rw [h2, mul_assoc]
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hr2).ne'
    ENNReal.ofReal_ne_top).mp hmain

end ChargeCollapse

end ParabolicRectifiability
