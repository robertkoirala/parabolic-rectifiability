import ParabolicRectifiability.Decomposition.Carrier.BetaPointBoundAndRankZero
import ParabolicRectifiability.Decomposition.Carrier.CoercivityAndGeometricBounds
import ParabolicRectifiability.Geometry.Neck.ComparisonEnergy

/-! # The ambient comparison square bound of the carrier family

Proof of the statement `isCarrierFamily_verticalSquareBound` for the regular
vertical carrier, under the name `isCarrierFamily_verticalSquareBound_proof`.

The argument is the finite-window local form of the last-witness lemma. Fix the reference
point `w` and a finite partial sum `∑_{j ≤ N} E_j(w)²`. Every center taking part in
`E_{j+1}(w)` lies, at its own level `l`, within `12 r_j ≤ 120 r_l` of `w`. Choose one
such center `y` at the deepest level `J ≤ N` that has one. Then every participating
level-`l` center `g` satisfies `d_P(g, y) ≤ 120 r_l + 120 r_J ≤ 240 r_l`, so with
`H = Λ + 240` its fitting ball `P(g, Λ r_l)` lies in `P(y, H r_l)`. Ball monotonicity of
the unnormalized error and the beta point bound (`betaSq_le_lintegral_Icc_proof`) give
`fit(g, Λ r_l) ≤ (2^{m+4}/log 2) H^{m+4} r_l^{m+4} I_l(y)` with
`I_l(y) = ∫_{H r_l}^{2 H r_l} β_η(y,s)² ds/s`. The plane comparison bound
(`planeComparison_sq_le_of_lower_mass_proof`) and the
change of anchor (factor `22`) then give
`E_{j+1}(w)² ≤ 484 · 10^{m+4} K₀ c (I_{j+1}(y) + I_j(y))`. The windows are disjoint
because `r_{l+1} = r_l/10`, and they lie in `(0, T)` because `2 H r_0 < 4 H r_0 ≤ T`;
the root term vanishes. Since `y` lies in the retained set, its square tail is at most
`b`. The witness is chosen separately for each finite partial sum; no global finiteness
of the source and no infinite selection is used.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal

/-! ## Scales of a coherent family -/

private theorem scale_pos' {n m : ℕ} (Φ : CoherentFamily n m (Space n)) (j : ℕ) :
    0 < Φ.scale j :=
  div_pos Φ.initialRadius_pos (pow_pos (by norm_num) _)

private theorem scale_succ' {n m : ℕ} (Φ : CoherentFamily n m (Space n)) (j : ℕ) :
    Φ.scale j = 10 * Φ.scale (j + 1) := by
  simp only [CoherentFamily.scale, coherentScale, pow_succ]
  rw [div_mul_eq_div_div]
  ring

private theorem scale_anti {n m : ℕ} (Φ : CoherentFamily n m (Space n)) {i j : ℕ}
    (h : i ≤ j) : Φ.scale j ≤ Φ.scale i := by
  simp only [CoherentFamily.scale, coherentScale]
  exact div_le_div_of_nonneg_left Φ.initialRadius_pos.le (by positivity)
    (pow_le_pow_right₀ (by norm_num) h)

private theorem scale_le_initialRadius {n m : ℕ} (Φ : CoherentFamily n m (Space n)) (j : ℕ) :
    Φ.scale j ≤ Φ.initialRadius := by
  change Φ.initialRadius / 10 ^ j ≤ Φ.initialRadius
  exact div_le_self Φ.initialRadius_pos.le (one_le_pow₀ (by norm_num))

/-- Windows of distinct levels are separated: `2 H r_{l'} < H r_l` for `l < l'`. -/
private theorem window_gap {n m : ℕ} (Φ : CoherentFamily n m (Space n)) {H : ℝ} (hH : 0 < H)
    {l l' : ℕ} (h : l < l') : 2 * (H * Φ.scale l') < H * Φ.scale l := by
  have h1 : H * Φ.scale l' ≤ H * Φ.scale (l + 1) :=
    mul_le_mul_of_nonneg_left (scale_anti Φ h) hH.le
  have h2 : H * Φ.scale l = 10 * (H * Φ.scale (l + 1)) := by
    rw [scale_succ' Φ l]
    ring
  have h3 : 0 < H * Φ.scale (l + 1) := mul_pos hH (scale_pos' Φ _)
  linarith

/-! ## Extended-real bookkeeping -/

private theorem ofReal_div_pow_mul {K c r : ℝ} {p : ℕ} (hr : 0 < r) (hK : 0 ≤ K)
    {Y : ℝ≥0∞} :
    ENNReal.ofReal (K / r ^ p) * (ENNReal.ofReal (c * r ^ p) * Y) =
      ENNReal.ofReal (K * c) * Y := by
  have hrp : 0 < r ^ p := pow_pos hr p
  have e : K / r ^ p * (c * r ^ p) = K * c := by
    rw [div_mul_eq_mul_div, div_eq_iff hrp.ne']
    ring
  rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hK hrp.le), e]

private theorem ofReal_mul_mul {x y : ℝ} (hx : 0 ≤ x) (Y : ℝ≥0∞) :
    ENNReal.ofReal x * (ENNReal.ofReal y * Y) = ENNReal.ofReal (x * y) * Y := by
  rw [← mul_assoc, ENNReal.ofReal_mul hx]

/-- A square bound through the square root `X^{1/2}`. -/
private theorem ofReal_le_rpow_inv_two {t : ℝ} (ht : 0 ≤ t) {X : ℝ≥0∞}
    (h : ENNReal.ofReal (t ^ 2) ≤ X) : ENNReal.ofReal t ≤ X ^ (2 : ℝ)⁻¹ := by
  rw [ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2), ENNReal.rpow_two,
    ← ENNReal.ofReal_pow ht]
  exact h

/-! ## The window transfer -/

/-- **Window transfer.** If `d_P(g, y) ≤ 240 r` and `L` is a best plane for `η` on
`P(g, Λ r)`, then for `H ≥ Λ + 240` the fitted error is controlled by the beta square
integral of `y` over `[H r, 2 H r]`:
`fit(g, Λ r) ≤ (2^{m+4}/log 2) H^{m+4} r^{m+4} ∫_{H r}^{2 H r} β_η(y,s)² ds/s`. -/
private theorem fit_le_window {n m : ℕ} (η : Measure (Space n)) {Λ H : ℝ}
    (hΛH : Λ + 240 ≤ H) (hH : 0 < H) (L : AffineSpatialPlane n m) (g y : Space n) {r : ℝ}
    (hr : 0 < r)
    (hbest : fit η (verticalPlaneModel L) g (Λ * r) =
      ⨅ L' : Models n (m + 2) .vertical, fit η L' g (Λ * r))
    (hgy : dist g y ≤ 240 * r) :
    fit η (verticalPlaneModel L) g (Λ * r) ≤
      ENNReal.ofReal (2 ^ (m + 4) / Real.log 2 * H ^ (m + 4) * r ^ (m + 4)) *
        ∫⁻ s in Icc (H * r) (2 * (H * r)), betaSq η (m + 2) .vertical y s ∂scaleMeasure := by
  have hHr : 0 < H * r := mul_pos hH hr
  have hball : Metric.ball g (Λ * r) ⊆ Metric.ball y (H * r) := by
    apply Metric.ball_subset_ball'
    linarith [mul_le_mul_of_nonneg_right hΛH hr.le]
  have h1 : fit η (verticalPlaneModel L) g (Λ * r) ≤
      ⨅ L' : Models n (m + 2) .vertical, fit η L' y (H * r) := by
    rw [hbest]
    exact iInf_mono fun L' => fit_mono_ball η L' hball
  have h2 : (⨅ L' : Models n (m + 2) .vertical, fit η L' y (H * r)) =
      ENNReal.ofReal (H * r) ^ (m + 4) * betaSq η (m + 2) .vertical y (H * r) := by
    rw [betaSq_of_pos _ _ _ _ hHr]
    change _ = ENNReal.ofReal (H * r) ^ (m + 4) *
      ((ENNReal.ofReal (H * r))⁻¹ ^ (m + 4) * _)
    rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hHr).ne'
      ENNReal.ofReal_ne_top, one_pow, one_mul]
  have h3 := betaSq_le_lintegral_Icc_proof η (m + 2) .vertical y hHr
  calc fit η (verticalPlaneModel L) g (Λ * r)
      ≤ ENNReal.ofReal (H * r) ^ (m + 4) * betaSq η (m + 2) .vertical y (H * r) :=
        h1.trans_eq h2
    _ ≤ ENNReal.ofReal (H * r) ^ (m + 4) * (ENNReal.ofReal (2 ^ (m + 2 + 2) / Real.log 2) *
        ∫⁻ s in Icc (H * r) (2 * (H * r)), betaSq η (m + 2) .vertical y s ∂scaleMeasure) :=
        mul_le_mul_right h3 _
    _ = ENNReal.ofReal (2 ^ (m + 4) / Real.log 2 * H ^ (m + 4) * r ^ (m + 4)) *
        ∫⁻ s in Icc (H * r) (2 * (H * r)), betaSq η (m + 2) .vertical y s ∂scaleMeasure := by
        rw [← mul_assoc, ← ENNReal.ofReal_pow hHr.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

/-- The windows `[H r_l, 2 H r_l]`, `l < N`, are disjoint and lie in `(0, T)` when
`2 H r_0 < T`; hence their beta square integrals at one point sum to at most its
square tail below `T`. -/
private theorem sum_window_le_squareEnergy {n m : ℕ} (μ : Measure (Space n))
    (Φ : CoherentFamily n m (Space n)) {H T : ℝ} (hH : 0 < H)
    (hT : 2 * H * Φ.initialRadius < T) (k : ℕ) (y : Space n) (N : ℕ) :
    ∑ l ∈ Finset.range N,
        ∫⁻ s in Icc (H * Φ.scale l) (2 * (H * Φ.scale l)), betaSq μ k .vertical y s
          ∂scaleMeasure ≤
      squareEnergy μ k .vertical T y := by
  have hd : Set.PairwiseDisjoint (↑(Finset.range N) : Set ℕ)
      (fun l => Icc (H * Φ.scale l) (2 * (H * Φ.scale l))) := by
    intro l _ l' _ hne
    simp only [Function.onFun]
    rcases lt_or_gt_of_ne hne with h | h
    · refine Set.disjoint_left.mpr fun s hs hs' => ?_
      have := window_gap Φ hH h
      linarith [hs.1, hs'.2]
    · refine Set.disjoint_left.mpr fun s hs hs' => ?_
      have := window_gap Φ hH h
      linarith [hs.2, hs'.1]
  calc ∑ l ∈ Finset.range N,
        ∫⁻ s in Icc (H * Φ.scale l) (2 * (H * Φ.scale l)), betaSq μ k .vertical y s
          ∂scaleMeasure
      = ∫⁻ s in ⋃ l ∈ Finset.range N, Icc (H * Φ.scale l) (2 * (H * Φ.scale l)),
          betaSq μ k .vertical y s ∂scaleMeasure :=
        (lintegral_biUnion_finset hd (fun l _ => measurableSet_Icc) _).symm
    _ ≤ ∫⁻ s in Ioo 0 T, betaSq μ k .vertical y s ∂scaleMeasure := by
        apply lintegral_mono_set
        intro s hs
        simp only [Set.mem_iUnion] at hs
        obtain ⟨l, -, hl⟩ := hs
        have h0 := scale_le_initialRadius Φ l
        refine ⟨(mul_pos hH (scale_pos' Φ l)).trans_le hl.1, ?_⟩
        linarith [hl.2, mul_le_mul_of_nonneg_left h0 hH.le]
    _ = squareEnergy μ k .vertical T y := rfl

/-! ## The comparison functions of a carrier family -/

/-- The root comparison term vanishes: every level-zero plane is the initial plane. -/
private theorem comparisonEnergy_zero_eq {n m : ℕ} {η : Measure (Space n)}
    {F : Set (Space n)} {Λ : ℝ} {Φ : CoherentFamily n m (Space n)}
    (hf : IsCarrierFamily η F Λ Φ) (w : Space n) :
    Φ.comparisonEnergy (fun z : Space n => z) 0 w = 0 := by
  simp only [CoherentFamily.comparisonEnergy, CoherentFamily.rootComparisonTerm]
  refine le_antisymm (iSup₂_le fun p hp => iSup_le fun _ => ?_) zero_le
  rw [hf.initial_plane p hp]
  simp only [planeComparison, sub_self, norm_zero, mul_zero, add_zero, ENNReal.ofReal_zero,
    le_refl]

/-- **One level.** Suppose every center of level `l ≤ j + 1` within `120 r_l` of `w` has
fitted error `fit(g, Λ r_l) ≤ c r_l^{m+4} I_l`. Then
`E_{j+1}(w)² ≤ 484 · 10^{m+4} K₀ c (I_{j+1} + I_j)`, where `K₀` is the constant of the
plane comparison bound (`planeComparison_sq_le_of_lower_mass_proof`). Same-level pairs are compared on `P(p, r_j)`, adjacent
pairs on `P(p, r_{j+1})` followed by the change of anchor to `x_q` and radius `r_j`. -/
private theorem comparisonEnergy_succ_sq_le {n m : ℕ} {Λ : ℝ} (hΛ : 21 ≤ Λ)
    {K₀ c a U T : ℝ} (hK₀ : 0 ≤ K₀) (hc : 0 ≤ c)
    (hcomp : ∀ (ν : Measure (Space n)) (z : Space n) (r : ℝ), 0 < r →
      ENNReal.ofReal (a * r ^ (m + 2)) ≤ ν (Metric.ball z r) →
      HasUpperGrowthUpTo ν (m + 2) U r →
      ∀ L L' : AffineSpatialPlane n m,
        ENNReal.ofReal (planeComparison z.1 r L L' ^ 2) ≤
          ENNReal.ofReal (K₀ / r ^ (m + 4)) *
            (fit ν (verticalPlaneModel L) z r + fit ν (verticalPlaneModel L') z r))
    {η : Measure (Space n)} {F : Set (Space n)} {Φ : CoherentFamily n m (Space n)}
    (hf : IsCarrierFamily η F Λ Φ) (hgrowth : HasUpperGrowthUpTo η (m + 2) U T)
    (hlow : ∀ z ∈ F, ∀ r : ℝ, 0 < r → r ≤ T →
      ENNReal.ofReal (a * r ^ (m + 2)) ≤ η (Metric.ball z r))
    (hT : ∀ i, Φ.scale i ≤ T) (I : ℕ → ℝ≥0∞) (w : Space n) (j : ℕ)
    (hfit : ∀ l ≤ j + 1, ∀ g ∈ Φ.index l, dist g w ≤ 120 * Φ.scale l →
      fit η (verticalPlaneModel (Φ.plane l g)) g (Λ * Φ.scale l) ≤
        ENNReal.ofReal (c * Φ.scale l ^ (m + 4)) * I l) :
    Φ.comparisonEnergy (fun z : Space n => z) (j + 1) w ^ 2 ≤
      ENNReal.ofReal (484 * 10 ^ (m + 4) * K₀ * c) * (I (j + 1) + I j) := by
  have hs : ∀ i, 0 < Φ.scale i := scale_pos' Φ
  have hsucc : Φ.scale j = 10 * Φ.scale (j + 1) := scale_succ' Φ j
  have hgr : ∀ i, HasUpperGrowthUpTo η (m + 2) U (Φ.scale i) :=
    fun i q s hs' hsr => hgrowth q s hs' (hsr.trans (hT i))
  have h10 : (1 : ℝ) ≤ 10 ^ (m + 4) := one_le_pow₀ (by norm_num)
  have hKc : 0 ≤ K₀ * c := mul_nonneg hK₀ hc
  suffices h : Φ.comparisonEnergy (fun z : Space n => z) (j + 1) w ≤
      (ENNReal.ofReal (484 * 10 ^ (m + 4) * K₀ * c) * (I (j + 1) + I j)) ^ (2 : ℝ)⁻¹ by
    have h' := (ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2)).mp h
    rwa [ENNReal.rpow_two] at h'
  simp only [CoherentFamily.comparisonEnergy, CoherentFamily.sameLevelComparisonTerm,
    CoherentFamily.adjacentComparisonTerm]
  refine max_le ?_ ?_
  · -- same-level comparisons at level `j`
    refine iSup₂_le fun p hp => iSup₂_le fun q hq => iSup_le fun hpq => ?_
    simp only [hf.center_eq] at hpq ⊢
    obtain ⟨hpq, hpw, hqw⟩ := hpq
    refine ofReal_le_rpow_inv_two (affineComparison_nonneg _ _ _ (hs j).le) ?_
    have hc' := hcomp η p (Φ.scale j) (hs j)
      (hlow p (hf.index_subset j hp) (Φ.scale j) (hs j) (hT j)) (hgr j)
      (Φ.plane j p) (Φ.plane j q)
    have h1 : fit η (verticalPlaneModel (Φ.plane j p)) p (Φ.scale j) ≤
        ENNReal.ofReal (c * Φ.scale j ^ (m + 4)) * I j :=
      (fit_mono_ball η _ (Metric.ball_subset_ball
        (le_mul_of_one_le_left (hs j).le (by linarith)))).trans
        (hfit j (Nat.le_succ j) p hp (by linarith [hs j]))
    have h2 : fit η (verticalPlaneModel (Φ.plane j q)) p (Φ.scale j) ≤
        ENNReal.ofReal (c * Φ.scale j ^ (m + 4)) * I j :=
      (fit_mono_ball η _ (Metric.ball_subset_ball'
        (by linarith [mul_le_mul_of_nonneg_right hΛ (hs j).le]))).trans
        (hfit j (Nat.le_succ j) q hq (by linarith [hs j]))
    have e : ENNReal.ofReal (K₀ / Φ.scale j ^ (m + 4)) *
        (ENNReal.ofReal (c * Φ.scale j ^ (m + 4)) * I j) =
        ENNReal.ofReal (K₀ * c) * I j :=
      ofReal_div_pow_mul (hs j) hK₀
    calc ENNReal.ofReal (planeComparison p.1 (Φ.scale j) (Φ.plane j p) (Φ.plane j q) ^ 2)
        ≤ ENNReal.ofReal (K₀ / Φ.scale j ^ (m + 4)) *
            (ENNReal.ofReal (c * Φ.scale j ^ (m + 4)) * I j +
              ENNReal.ofReal (c * Φ.scale j ^ (m + 4)) * I j) :=
          hc'.trans (mul_le_mul_right (add_le_add h1 h2) _)
      _ = ENNReal.ofReal (K₀ * c) * I j + ENNReal.ofReal (K₀ * c) * I j := by
          rw [mul_add, e]
      _ = ENNReal.ofReal (2 * (K₀ * c)) * I j := by
          rw [← add_mul, ← ENNReal.ofReal_add hKc hKc, two_mul]
      _ ≤ ENNReal.ofReal (484 * 10 ^ (m + 4) * K₀ * c) * I j :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal
            (by nlinarith [mul_le_mul_of_nonneg_right h10 hKc])) _
      _ ≤ ENNReal.ofReal (484 * 10 ^ (m + 4) * K₀ * c) * (I (j + 1) + I j) :=
          mul_le_mul_right le_add_self _
  · -- adjacent comparisons between levels `j + 1` and `j`
    refine iSup₂_le fun p hp => iSup₂_le fun q hq => iSup_le fun hpq => ?_
    simp only [hf.center_eq] at hpq ⊢
    obtain ⟨hpq, hpw, hqw⟩ := hpq
    refine ofReal_le_rpow_inv_two (affineComparison_nonneg _ _ _ (hs j).le) ?_
    have hc' := hcomp η p (Φ.scale (j + 1)) (hs (j + 1))
      (hlow p (hf.index_subset (j + 1) hp) (Φ.scale (j + 1)) (hs (j + 1)) (hT (j + 1)))
      (hgr (j + 1)) (Φ.plane (j + 1) p) (Φ.plane j q)
    have h1 : fit η (verticalPlaneModel (Φ.plane (j + 1) p)) p (Φ.scale (j + 1)) ≤
        ENNReal.ofReal (c * Φ.scale (j + 1) ^ (m + 4)) * I (j + 1) :=
      (fit_mono_ball η _ (Metric.ball_subset_ball
        (le_mul_of_one_le_left (hs (j + 1)).le (by linarith)))).trans
        (hfit (j + 1) le_rfl p hp (by linarith))
    have h2 : fit η (verticalPlaneModel (Φ.plane j q)) p (Φ.scale (j + 1)) ≤
        ENNReal.ofReal (c * 10 ^ (m + 4) * Φ.scale (j + 1) ^ (m + 4)) * I j := by
      have hsub : Metric.ball p (Φ.scale (j + 1)) ⊆ Metric.ball q (Λ * Φ.scale j) :=
        Metric.ball_subset_ball'
          (by linarith [mul_le_mul_of_nonneg_right hΛ (hs j).le, hs (j + 1)])
      have h := (fit_mono_ball η (verticalPlaneModel (Φ.plane j q)) hsub).trans
        (hfit j (Nat.le_succ j) q hq (by linarith [hs j]))
      rwa [hsucc, mul_pow, ← mul_assoc] at h
    have hnorm : ‖q.1 - p.1‖ ≤ 200 * Φ.scale (j + 1) := by
      have hd : ‖q.1 - p.1‖ ≤ dist p q := by
        rw [norm_sub_rev]
        exact le_max_left _ _
      linarith
    have hanchor := affineComparison_change_anchor_radius (Φ.plane (j + 1) p) (Φ.plane j q)
      p.1 q.1 (Φ.scale (j + 1)) (Φ.scale j) 200 (hs (j + 1)) (hs j) (by norm_num) hnorm
    have hfactor : 1 + (200 + 1) * Φ.scale (j + 1) / Φ.scale j ≤ 22 := by
      have hd : (200 + 1) * Φ.scale (j + 1) / Φ.scale j ≤ 21 :=
        (div_le_iff₀ (hs j)).mpr (by linarith [hs (j + 1)])
      linarith
    have hanchor' : planeComparison q.1 (Φ.scale j) (Φ.plane (j + 1) p) (Φ.plane j q) ≤
        22 * planeComparison p.1 (Φ.scale (j + 1)) (Φ.plane (j + 1) p) (Φ.plane j q) :=
      hanchor.trans (mul_le_mul_of_nonneg_right hfactor
        (affineComparison_nonneg _ _ _ (hs (j + 1)).le))
    have hsq : planeComparison q.1 (Φ.scale j) (Φ.plane (j + 1) p) (Φ.plane j q) ^ 2 ≤
        484 * planeComparison p.1 (Φ.scale (j + 1)) (Φ.plane (j + 1) p) (Φ.plane j q) ^ 2 :=
      calc _ ≤ (22 * planeComparison p.1 (Φ.scale (j + 1)) (Φ.plane (j + 1) p)
              (Φ.plane j q)) ^ 2 :=
            pow_le_pow_left₀ (affineComparison_nonneg _ _ _ (hs j).le) hanchor' 2
        _ = _ := by ring
    have e1 : ENNReal.ofReal (K₀ / Φ.scale (j + 1) ^ (m + 4)) *
        (ENNReal.ofReal (c * Φ.scale (j + 1) ^ (m + 4)) * I (j + 1)) =
        ENNReal.ofReal (K₀ * c) * I (j + 1) :=
      ofReal_div_pow_mul (hs (j + 1)) hK₀
    have e2 : ENNReal.ofReal (K₀ / Φ.scale (j + 1) ^ (m + 4)) *
        (ENNReal.ofReal (c * 10 ^ (m + 4) * Φ.scale (j + 1) ^ (m + 4)) * I j) =
        ENNReal.ofReal (K₀ * (c * 10 ^ (m + 4))) * I j :=
      ofReal_div_pow_mul (hs (j + 1)) hK₀
    calc ENNReal.ofReal
          (planeComparison q.1 (Φ.scale j) (Φ.plane (j + 1) p) (Φ.plane j q) ^ 2)
        ≤ ENNReal.ofReal (484 *
            planeComparison p.1 (Φ.scale (j + 1)) (Φ.plane (j + 1) p) (Φ.plane j q) ^ 2) :=
          ENNReal.ofReal_le_ofReal hsq
      _ = ENNReal.ofReal 484 * ENNReal.ofReal
            (planeComparison p.1 (Φ.scale (j + 1)) (Φ.plane (j + 1) p) (Φ.plane j q) ^ 2) :=
          ENNReal.ofReal_mul (by norm_num)
      _ ≤ ENNReal.ofReal 484 * (ENNReal.ofReal (K₀ / Φ.scale (j + 1) ^ (m + 4)) *
            (ENNReal.ofReal (c * Φ.scale (j + 1) ^ (m + 4)) * I (j + 1) +
              ENNReal.ofReal (c * 10 ^ (m + 4) * Φ.scale (j + 1) ^ (m + 4)) * I j)) :=
          mul_le_mul_right (hc'.trans (mul_le_mul_right (add_le_add h1 h2) _)) _
      _ = ENNReal.ofReal 484 * (ENNReal.ofReal (K₀ * c) * I (j + 1)) +
            ENNReal.ofReal 484 * (ENNReal.ofReal (K₀ * (c * 10 ^ (m + 4))) * I j) := by
          rw [mul_add, e1, e2, mul_add]
      _ = ENNReal.ofReal (484 * (K₀ * c)) * I (j + 1) +
            ENNReal.ofReal (484 * (K₀ * (c * 10 ^ (m + 4)))) * I j := by
          rw [ofReal_mul_mul (by norm_num), ofReal_mul_mul (by norm_num)]
      _ ≤ ENNReal.ofReal (484 * 10 ^ (m + 4) * K₀ * c) * I (j + 1) +
            ENNReal.ofReal (484 * 10 ^ (m + 4) * K₀ * c) * I j :=
          add_le_add
            (mul_le_mul_left (ENNReal.ofReal_le_ofReal
              (by nlinarith [mul_le_mul_of_nonneg_right h10 hKc])) _)
            (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_of_eq (by ring))) _)
      _ = ENNReal.ofReal (484 * 10 ^ (m + 4) * K₀ * c) * (I (j + 1) + I j) :=
          (mul_add _ _ _).symm

/-! ## The ambient square bound -/

/-- **Ambient square bound** (`isCarrierFamily_verticalSquareBound`). With the dimensional scale factor `A = 4 (Λ + 240)` and
`K = 2 · 484 · 10^{m+4} K₀ (2^{m+4}/log 2) (Λ + 240)^{m+4}`, where `K₀ = K₀(n, m, a, U)`
is the constant of the plane comparison bound, a carrier family of a retained
piece with `A R ≤ T` satisfies `∑_j E_j(w)² ≤ K b` at every reference point `w`.
For each finite partial sum the witness `y` is a participating center at the deepest
level; the bound for the partial sum uses only the square tail of `y` below `T`. -/
theorem isCarrierFamily_verticalSquareBound_proof (n m : ℕ) (hm : 1 ≤ m) {Λ : ℝ}
    (hΛ : 21 ≤ Λ) :
    ∃ A : ℝ, 0 < A ∧ ∀ a U : ℝ, 0 < a → 0 ≤ U → ∃ K : ℝ, 0 < K ∧
      ∀ (η : Measure (Space n)) (F : Set (Space n)) (R T b : ℝ)
        (Φ : CoherentFamily n m (Space n)),
        0 < R → A * R ≤ T → 0 ≤ b → Φ.initialRadius = R → IsCarrierFamily η F Λ Φ →
        HasUpperGrowthUpTo η (m + 2) U T → IsCarrierPiece η (m + 2) a b T F →
        Φ.VerticalSquareBound (K * b) := by
  classical
  obtain ⟨H, hH_def⟩ : ∃ H : ℝ, H = Λ + 240 := ⟨_, rfl⟩
  have hH0 : 0 < H := by linarith
  have hΛH : Λ + 240 ≤ H := hH_def.ge
  refine ⟨4 * H, mul_pos (by norm_num) hH0, ?_⟩
  intro a U ha hU
  obtain ⟨K₀, hK₀, hcomp⟩ := planeComparison_sq_le_of_lower_mass_proof n m hm ha hU
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = 2 ^ (m + 4) / Real.log 2 * H ^ (m + 4) := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hc_def]
    exact mul_pos (div_pos (by positivity) (Real.log_pos (by norm_num))) (pow_pos hH0 _)
  have hD : 0 < 484 * 10 ^ (m + 4) * K₀ * c := mul_pos (mul_pos (by positivity) hK₀) hc0
  have hD0 : 0 ≤ 484 * 10 ^ (m + 4) * K₀ * c := hD.le
  refine ⟨2 * (484 * 10 ^ (m + 4) * K₀ * c), mul_pos two_pos hD, ?_⟩
  intro η F R T b Φ hR hAT hb hinit hf hgrowth hp
  have hs : ∀ i, 0 < Φ.scale i := scale_pos' Φ
  have hT : ∀ i, Φ.scale i ≤ T := by
    intro i
    have h1 := scale_le_initialRadius Φ i
    rw [hinit] at h1
    nlinarith [mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 4 * H by linarith) hR.le]
  have h2HR : 2 * H * Φ.initialRadius < T := by
    rw [hinit]
    nlinarith [mul_pos hH0 hR]
  unfold CoherentFamily.VerticalSquareBound CoherentFamily.SquareBound
  intro w
  apply ENNReal.tsum_le_of_sum_range_le
  intro N'
  rcases N' with _ | N
  · simp
  rw [Finset.sum_range_succ', comparisonEnergy_zero_eq hf w, zero_pow two_ne_zero, add_zero]
  -- the levels with a participating center
  set S : Finset ℕ := (Finset.range (N + 1)).filter
    (fun l => ∃ g ∈ Φ.index l, dist g w ≤ 120 * Φ.scale l)
  by_cases hS : S.Nonempty
  · -- the deepest participating center `y`
    obtain ⟨y, hy, hyw⟩ :
        ∃ y ∈ Φ.index (S.max' hS), dist y w ≤ 120 * Φ.scale (S.max' hS) :=
      (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
    let I : ℕ → ℝ≥0∞ := fun l =>
      ∫⁻ s in Icc (H * Φ.scale l) (2 * (H * Φ.scale l)), betaSq η (m + 2) .vertical y s
        ∂scaleMeasure
    have hfitI : ∀ l ≤ N, ∀ g ∈ Φ.index l, dist g w ≤ 120 * Φ.scale l →
        fit η (verticalPlaneModel (Φ.plane l g)) g (Λ * Φ.scale l) ≤
          ENNReal.ofReal (c * Φ.scale l ^ (m + 4)) * I l := by
      intro l hl g hg hgw
      have hlS : l ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hl), g, hg, hgw⟩
      have hJl : Φ.scale (S.max' hS) ≤ Φ.scale l := scale_anti Φ (Finset.le_max' S l hlS)
      have hgy : dist g y ≤ 240 * Φ.scale l := by
        have := dist_triangle_right g y w
        linarith
      have h := fit_le_window η hΛH hH0 (Φ.plane l g) g y (hs l) (hf.best_fit l g hg) hgy
      rw [← hc_def] at h
      exact h
    have hyF : y ∈ F := hf.index_subset _ hy
    have hwin : ∑ l ∈ Finset.range (N + 1), I l ≤ ENNReal.ofReal b :=
      (sum_window_le_squareEnergy η Φ hH0 h2HR (m + 2) y (N + 1)).trans (hp.small_tail y hyF)
    calc ∑ i ∈ Finset.range N, Φ.comparisonEnergy (fun z : Space n => z) (i + 1) w ^ 2
        ≤ ∑ i ∈ Finset.range N,
            ENNReal.ofReal (484 * 10 ^ (m + 4) * K₀ * c) * (I (i + 1) + I i) :=
          Finset.sum_le_sum fun i hi =>
            comparisonEnergy_succ_sq_le hΛ hK₀.le hc0.le hcomp hf hgrowth hp.lower_mass hT
              I w i (fun l hl => hfitI l (by have := Finset.mem_range.mp hi; omega))
      _ = ENNReal.ofReal (484 * 10 ^ (m + 4) * K₀ * c) *
            (∑ i ∈ Finset.range N, I (i + 1) + ∑ i ∈ Finset.range N, I i) := by
          simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ ENNReal.ofReal (484 * 10 ^ (m + 4) * K₀ * c) *
            (∑ l ∈ Finset.range (N + 1), I l + ∑ l ∈ Finset.range (N + 1), I l) := by
          refine mul_le_mul_right (add_le_add ?_ ?_) _
          · rw [Finset.sum_range_succ' I N]
            exact le_self_add
          · rw [Finset.sum_range_succ I N]
            exact le_self_add
      _ ≤ ENNReal.ofReal (484 * 10 ^ (m + 4) * K₀ * c) *
            (ENNReal.ofReal b + ENNReal.ofReal b) :=
          mul_le_mul_right (add_le_add hwin hwin) _
      _ = ENNReal.ofReal (2 * (484 * 10 ^ (m + 4) * K₀ * c) * b) := by
          rw [← ENNReal.ofReal_add hb hb, ← ENNReal.ofReal_mul hD0]
          congr 1
          ring
  · -- no participating center: every comparison term vanishes
    have hzero : ∀ i ∈ Finset.range N,
        Φ.comparisonEnergy (fun z : Space n => z) (i + 1) w ^ 2 ≤ 0 := by
      intro i hi
      have hiN := Finset.mem_range.mp hi
      have h := comparisonEnergy_succ_sq_le hΛ hK₀.le hc0.le hcomp hf hgrowth hp.lower_mass
        hT (fun _ => 0) w i (fun l hl g hg hgw => (hS ⟨l, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), g, hg, hgw⟩⟩).elim)
      exact h.trans (by simp)
    calc ∑ i ∈ Finset.range N, Φ.comparisonEnergy (fun z : Space n => z) (i + 1) w ^ 2
        ≤ ∑ i ∈ Finset.range N, (0 : ℝ≥0∞) := Finset.sum_le_sum hzero
      _ = 0 := Finset.sum_const_zero
      _ ≤ _ := zero_le

end ParabolicRectifiability
