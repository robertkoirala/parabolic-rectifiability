import ParabolicRectifiability.Measure.Neck.PlaneTime.ConstructionFacts

/-!
# Plane comparison of the source construction

Proof of `planeComparison_sq_le`.

For a continuing candidate `g` of stage `j`, the original source `ν ⌞ P(g, 5 r_j)` is
noncollapsed. It lies inside the fitting balls of both compared candidates, so the
covariance comparison (`SpatialSource.affineComparison_sq_le`) bounds the squared affine
comparison at radius `5 r_j` by `36/a` times the two normalized fitting errors; the
anchor and radius change (`affineComparison_change_anchor_radius`) moves it to the anchor
and radius of the coherent family. At vertical rank zero the planes are points and the
comparison is the elementary estimate `ν(P(g,5r)) |p - p'|² ≤ 2 (I(p) + I(p'))` with the
noncollapse mass `ν(P(g,5r)) ≥ a (5r)²` (the rank-zero mass argument).

* same level: covariance of `g = g_{j,i}`; both fits at radius `40 r_j`;
* adjacent levels: covariance of the child `g_{j+1,i}`; the parent fit at radius
  `40 r_j = 80 · 5 r_{j+1}` changes the normalization by `10^{k+2}` (times `8^{k+2}`);
* level one against the artificial root: covariance of `g_{1,i}`, the global fit of the
  root plane on the whole source; the root lies within `2R ≤ 5 r_1` of `g` because both
  lie within `R` of `q`.

The constant is `20000 · 8^{n+3}`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal

theorem ms3_planeComparison_eq {n m : ℕ} (x : Spatial n) (r : ℝ)
    (L L' : AffineSpatialPlane n m) : planeComparison x r L L' = affineComparison L L' x r :=
  rfl

theorem ms3_ofBall_mass {n : ℕ} (ν : Measure (Space n)) [IsFiniteMeasure ν] (g : Space n)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (SpatialSource.ofBall ν g ρ hρ).mass = (ν (Metric.ball g ρ)).toReal := by
  simp only [SpatialSource.mass, SpatialSource.ofBall, measureReal_def,
    Measure.restrict_apply_univ]

/-- A rank-zero plane has zero linear projection. -/
theorem ms3_linearProjection_eq_zero {n m : ℕ} (L : AffineSpatialPlane n m) (hm : m = 0) :
    L.linearProjection = 0 := by
  have hdir : L.direction = ⊥ := Submodule.finrank_eq_zero.1 (L.rank_eq.trans hm)
  ext1 x
  have hmem : L.linearProjection x ∈ L.direction := Submodule.starProjection_apply_mem _ x
  rw [hdir] at hmem
  simpa using (Submodule.mem_bot ℝ).1 hmem

/-- Anchor and radius change, squared. -/
theorem ms3_change_sq {n m : ℕ} (L L' : AffineSpatialPlane n m) (x y : Spatial n) {r s A : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hA : 0 ≤ A) (hxy : ‖y - x‖ ≤ A * r) :
    affineComparison L L' y s ^ 2 ≤
      (1 + (A + 1) * r / s) ^ 2 * affineComparison L L' x r ^ 2 := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (affineComparison_nonneg L L' y hs.le)
    (affineComparison_change_anchor_radius L L' x y r s A hr hs hA hxy) 2

/-- Passage from a real bound to the extended form `c (β₁ + w β₂)` of `planeComparison_sq_le`: an
infinite beta makes the right side infinite. -/
theorem ms3_ofReal_le_of_real {x c w : ℝ} (hc : 0 < c) (hw : 0 < w) (β₁ β₂ : ℝ≥0∞)
    (h : ∀ b₁ b₂ : ℝ, 0 ≤ b₁ → 0 ≤ b₂ → β₁ = ENNReal.ofReal b₁ → β₂ = ENNReal.ofReal b₂ →
      x ≤ c * (b₁ + w * b₂)) :
    ENNReal.ofReal x ≤ ENNReal.ofReal c * (β₁ + ENNReal.ofReal w * β₂) := by
  by_cases h₁ : β₁ = ⊤
  · rw [h₁, top_add, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne']
    exact le_top
  by_cases h₂ : β₂ = ⊤
  · rw [h₂, ENNReal.mul_top (ENNReal.ofReal_pos.2 hw).ne', add_top,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne']
    exact le_top
  have hx := h β₁.toReal β₂.toReal ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (ENNReal.ofReal_toReal h₁).symm (ENNReal.ofReal_toReal h₂).symm
  calc ENNReal.ofReal x ≤ ENNReal.ofReal (c * (β₁.toReal + w * β₂.toReal)) :=
        ENNReal.ofReal_le_ofReal hx
    _ = ENNReal.ofReal c * (β₁ + ENNReal.ofReal w * β₂) := by
        rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_add ENNReal.toReal_nonneg
          (mul_nonneg hw.le ENNReal.toReal_nonneg), ENNReal.ofReal_mul hw.le,
          ENNReal.ofReal_toReal h₁, ENNReal.ofReal_toReal h₂]

/-- **Common-source comparison (both ranks).** If the original source on `P(g, ρ)` passes the
continuation test (positive rank: `λ_m(Q) ≥ a ρ^{k+2}`; vertical rank zero:
`ν(P(g,ρ)) ≥ a ρ²`) and two planes fit two measures dominating `ν ⌞ P(g,ρ)` with spatial
errors `≤ ρ^{k+2} b_i`, then their squared affine comparison at `(x_g, ρ)` is at most
`36/a (b₁ + b₂)`. -/
theorem ms3_core_comparison {n k : ℕ} {T : NeckType} (hT : T.Available n k)
    (ν : Measure (Space n)) [IsFiniteMeasure ν] (g : Space n) {ρ a : ℝ} (hρ : 0 < ρ)
    (ha : 0 < a)
    (hcont : (0 < T.rank k ∧ ∃ h : 0 < ρ,
        a * ρ ^ (k + 2) ≤ (SpatialSource.ofBall ν g ρ h).rankEigenvalue (T.rank k)) ∨
      (T.rank k = 0 ∧ ENNReal.ofReal (a * ρ ^ 2) ≤ ν (Metric.ball g ρ)))
    (L₁ L₂ : AffineSpatialPlane n (T.rank k)) (μ₁ μ₂ : Measure (Space n))
    (h₁ : ν.restrict (Metric.ball g ρ) ≤ μ₁) (h₂ : ν.restrict (Metric.ball g ρ) ≤ μ₂)
    {b₁ b₂ : ℝ} (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hf₁ : spatialFittingIntegral μ₁ L₁ ≤ ENNReal.ofReal (ρ ^ (k + 2) * b₁))
    (hf₂ : spatialFittingIntegral μ₂ L₂ ≤ ENNReal.ofReal (ρ ^ (k + 2) * b₂)) :
    affineComparison L₁ L₂ g.1 ρ ^ 2 ≤ 36 / a * (b₁ + b₂) := by
  have hρk : 0 < ρ ^ (k + 2) := pow_pos hρ _
  have he₁ := (SpatialSource.ofBall ν g ρ hρ).fittingError_le_of_measure_le L₁ μ₁ h₁ _
    (mul_nonneg hρk.le hb₁) hf₁
  have he₂ := (SpatialSource.ofBall ν g ρ hρ).fittingError_le_of_measure_le L₂ μ₂ h₂ _
    (mul_nonneg hρk.le hb₂) hf₂
  rcases hcont with ⟨hm, h, hle⟩ | ⟨hm, hmass⟩
  · -- positive rank: the covariance comparison
    have hmn : T.rank k ≤ n := by
      cases T <;> simp only [NeckType.rank, NeckType.Available] at hT ⊢ <;> omega
    have hm1 : 1 ≤ T.rank k := hm
    have hrank : (SpatialSource.ofBall ν g ρ hρ).rankEigenvalue (T.rank k) =
        (SpatialSource.ofBall ν g ρ hρ).eigenvalue ⟨T.rank k - 1, by omega⟩ := by
      unfold SpatialSource.rankEigenvalue
      rw [dite_eq_left ⟨hm1, hmn⟩]
    have hlam : 0 < a * ρ ^ (k + 2) := mul_pos ha hρk
    have hcmp := (SpatialSource.ofBall ν g ρ hρ).affineComparison_sq_le hm1 hmn
      (a * ρ ^ (k + 2)) hlam (hle.trans hrank.le) L₁ L₂
    have hne := hρk.ne'
    have hane := ha.ne'
    calc affineComparison L₁ L₂ g.1 ρ ^ 2
        ≤ 36 * ((SpatialSource.ofBall ν g ρ hρ).fittingError L₁ +
            (SpatialSource.ofBall ν g ρ hρ).fittingError L₂) / (a * ρ ^ (k + 2)) := hcmp
      _ ≤ 36 * (ρ ^ (k + 2) * b₁ + ρ ^ (k + 2) * b₂) / (a * ρ ^ (k + 2)) := by
          gcongr
      _ = 36 / a * (b₁ + b₂) := by
          field_simp
  · -- vertical rank zero: the planes are points
    have hk2 : k = 2 := by
      cases T <;> simp only [NeckType.rank, NeckType.Available] at hT hm <;> omega
    subst hk2
    have hP₁ := ms3_linearProjection_eq_zero L₁ hm
    have hP₂ := ms3_linearProjection_eq_zero L₂ hm
    have hπ : ∀ L : AffineSpatialPlane n (T.rank 2), L.linearProjection = 0 →
        ∀ x, L.projection x = L.anchor := by
      intro L hL x
      simp [AffineSpatialPlane.projection, hL]
    set S := SpatialSource.ofBall ν g ρ hρ with hS
    have hb1 := S.mass_mul_barycenter_residual_sq_le L₁
    have hb2 := S.mass_mul_barycenter_residual_sq_le L₂
    rw [hπ L₁ hP₁] at hb1
    rw [hπ L₂ hP₂] at hb2
    have hmassS : a * ρ ^ 2 ≤ S.mass := by
      rw [hS, ms3_ofBall_mass]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hmass
    have hcomp : affineComparison L₁ L₂ g.1 ρ = ρ⁻¹ * ‖L₁.anchor - L₂.anchor‖ := by
      simp only [affineComparison, hP₁, hP₂, sub_self, norm_zero, zero_add, hπ L₁ hP₁,
        hπ L₂ hP₂]
    have htri : ‖L₁.anchor - L₂.anchor‖ ^ 2 ≤
        2 * (‖S.barycenter - L₁.anchor‖ ^ 2 + ‖S.barycenter - L₂.anchor‖ ^ 2) := by
      have h3 : ‖L₁.anchor - L₂.anchor‖ ≤
          ‖S.barycenter - L₁.anchor‖ + ‖S.barycenter - L₂.anchor‖ := by
        calc ‖L₁.anchor - L₂.anchor‖ =
              ‖(S.barycenter - L₂.anchor) - (S.barycenter - L₁.anchor)‖ := by
              congr 1
              abel
          _ ≤ ‖S.barycenter - L₂.anchor‖ + ‖S.barycenter - L₁.anchor‖ := norm_sub_le _ _
          _ = _ := add_comm _ _
      nlinarith [norm_nonneg (L₁.anchor - L₂.anchor), norm_nonneg (S.barycenter - L₁.anchor),
        norm_nonneg (S.barycenter - L₂.anchor),
        sq_nonneg (‖S.barycenter - L₁.anchor‖ - ‖S.barycenter - L₂.anchor‖)]
    have hmn := S.mass_nonneg
    have hD : a * ρ ^ 2 * ‖L₁.anchor - L₂.anchor‖ ^ 2 ≤
        2 * (ρ ^ (2 + 2) * b₁ + ρ ^ (2 + 2) * b₂) := by
      calc a * ρ ^ 2 * ‖L₁.anchor - L₂.anchor‖ ^ 2
          ≤ S.mass * ‖L₁.anchor - L₂.anchor‖ ^ 2 := by gcongr
        _ ≤ S.mass * (2 * (‖S.barycenter - L₁.anchor‖ ^ 2 +
              ‖S.barycenter - L₂.anchor‖ ^ 2)) := by gcongr
        _ = 2 * (S.mass * ‖S.barycenter - L₁.anchor‖ ^ 2 +
              S.mass * ‖S.barycenter - L₂.anchor‖ ^ 2) := by ring
        _ ≤ 2 * (S.fittingError L₁ + S.fittingError L₂) := by gcongr
        _ ≤ 2 * (ρ ^ (2 + 2) * b₁ + ρ ^ (2 + 2) * b₂) := by gcongr
    rw [hcomp]
    have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
    have hkey : ‖L₁.anchor - L₂.anchor‖ ^ 2 * a ≤ 2 * ρ ^ 2 * (b₁ + b₂) := by
      have h4 : ρ ^ 2 * (‖L₁.anchor - L₂.anchor‖ ^ 2 * a) ≤
          ρ ^ 2 * (2 * ρ ^ 2 * (b₁ + b₂)) := by
        have e1 : ρ ^ 2 * (‖L₁.anchor - L₂.anchor‖ ^ 2 * a) =
            a * ρ ^ 2 * ‖L₁.anchor - L₂.anchor‖ ^ 2 := by ring
        have e2 : ρ ^ 2 * (2 * ρ ^ 2 * (b₁ + b₂)) =
            2 * (ρ ^ (2 + 2) * b₁ + ρ ^ (2 + 2) * b₂) := by ring
        rw [e1, e2]
        exact hD
      exact le_of_mul_le_mul_left h4 hρ2
    have hsum : 0 ≤ b₁ + b₂ := add_nonneg hb₁ hb₂
    rw [mul_pow, inv_pow, inv_mul_eq_div, div_le_iff₀ hρ2,
      show 36 / a * (b₁ + b₂) * ρ ^ 2 = 36 * (b₁ + b₂) * ρ ^ 2 / a by ring, le_div_iff₀ ha]
    nlinarith [mul_nonneg hsum hρ2.le]

/-- **`planeComparison_sq_le` with its explicit constant `20000 · 8^{n+3}`.** -/
theorem ms3_planeComparison_explicit (n : ℕ) :
    ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T),
      T.Available n k → k < n + 2 → P.IsAdmissible → D.IsSourceConstruction P →
      (∀ j, 1 ≤ j → ∀ i ∈ D.contIndex P j, ∀ l ∈ D.contIndex P j,
        dist (D.cand j i) (D.cand j l) ≤ 20 * P.scale T j →
        ENNReal.ofReal
            (planeComparison (D.cand j i).1 (P.scale T j) (D.plane j i) (D.plane j l) ^ 2) ≤
          ENNReal.ofReal (20000 * 8 ^ (n + 3) / P.a) *
            (betaSq P.ν k T.toFamilyKind (D.cand j i) (40 * P.scale T j) +
              betaSq P.ν k T.toFamilyKind (D.cand j l) (40 * P.scale T j))) ∧
      (∀ j, 1 ≤ j → ∀ i ∈ D.contIndex P (j + 1), ∀ l ∈ D.contIndex P j,
        dist (D.cand (j + 1) i) (D.cand j l) ≤ 20 * P.scale T j →
        ENNReal.ofReal
            (planeComparison (D.cand j l).1 (P.scale T j) (D.plane (j + 1) i) (D.plane j l) ^ 2) ≤
          ENNReal.ofReal (20000 * 8 ^ (n + 3) / P.a) *
            (betaSq P.ν k T.toFamilyKind (D.cand (j + 1) i) (40 * P.scale T (j + 1)) +
              ENNReal.ofReal (10 ^ (k + 2)) *
                betaSq P.ν k T.toFamilyKind (D.cand j l) (40 * P.scale T j))) ∧
      (∀ i ∈ D.contIndex P 1,
        ENNReal.ofReal (planeComparison D.rootCenter.1 (P.scale T 0) (D.plane 1 i) D.rootPlane ^ 2) ≤
          ENNReal.ofReal (20000 * 8 ^ (n + 3) / P.a) *
            (betaSq P.ν k T.toFamilyKind (D.cand 1 i) (40 * P.scale T 1) +
              ENNReal.ofReal ((P.scale T 0)⁻¹ ^ (k + 2)) *
                ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν)) := by
  intro k T P D hT hk hP hD
  have := P.finite
  have hR := hP.R_pos
  have ha := hP.a_pos
  have hC : 0 < 20000 * 8 ^ (n + 3) / P.a := by positivity
  have h8 : (8 : ℝ) ^ (k + 2) ≤ 8 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  -- the fit of a candidate in real form
  have hfit : ∀ {j : ℕ}, 1 ≤ j → ∀ {i : ℕ}, i < D.candCount j → ∀ {b : ℝ}, 0 ≤ b →
      betaSq P.ν k T.toFamilyKind (D.cand j i) (40 * P.scale T j) = ENNReal.ofReal b →
      spatialFittingIntegral (P.ν.restrict (Metric.ball (D.cand j i) (40 * P.scale T j)))
          (D.plane j i) ≤ ENNReal.ofReal ((5 * P.scale T j) ^ (k + 2) * (8 ^ (k + 2) * b)) := by
    intro j hj i hi b hb heq
    have h := D.ms3_spatialFit_le P hD hR hj hi
    have hr := P.scale_pos T hR j
    have h40 : (0 : ℝ) ≤ 40 * P.scale T j := by positivity
    rw [heq, ← ENNReal.ofReal_pow h40, ← ENNReal.ofReal_mul (pow_nonneg h40 _)] at h
    refine h.trans_eq (congrArg ENNReal.ofReal ?_)
    rw [show (40 : ℝ) * P.scale T j = 8 * (5 * P.scale T j) by ring, mul_pow]
    ring
  refine ⟨?_, ?_, ?_⟩
  · -- same level
    intro j hj i hi l hl hdist
    obtain ⟨hic, hicont⟩ := (D.ms3_mem_contIndex P).1 hi
    obtain ⟨hlc, -⟩ := (D.ms3_mem_contIndex P).1 hl
    have hr : 0 < P.scale T j := P.scale_pos T hR j
    have hρ : 0 < 5 * P.scale T j := by linarith
    rw [ms3_planeComparison_eq,
      show betaSq P.ν k T.toFamilyKind (D.cand j l) (40 * P.scale T j) =
        ENNReal.ofReal 1 * betaSq P.ν k T.toFamilyKind (D.cand j l) (40 * P.scale T j) by
        rw [ENNReal.ofReal_one, one_mul]]
    refine ms3_ofReal_le_of_real hC one_pos _ _ fun b₁ b₂ hb₁ hb₂ he₁ he₂ => ?_
    have hcore := ms3_core_comparison hT P.ν (D.cand j i) hρ ha hicont (D.plane j i)
      (D.plane j l) _ _
      (Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl)
      (Measure.restrict_mono (Metric.ball_subset_ball' (by linarith)) le_rfl)
      (by positivity) (by positivity) (hfit hj hic hb₁ he₁) (hfit hj hlc hb₂ he₂)
    have hch := ms3_change_sq (D.plane j i) (D.plane j l) (D.cand j i).1 (D.cand j i).1 hρ hr
      le_rfl (by simp)
    have hfac : (1 + (0 + 1) * (5 * P.scale T j) / P.scale T j) = 6 := by
      field_simp
      ring
    rw [hfac] at hch
    calc affineComparison (D.plane j i) (D.plane j l) (D.cand j i).1 (P.scale T j) ^ 2
        ≤ 6 ^ 2 * affineComparison (D.plane j i) (D.plane j l) (D.cand j i).1
            (5 * P.scale T j) ^ 2 := hch
      _ ≤ 6 ^ 2 * (36 / P.a * (8 ^ (k + 2) * b₁ + 8 ^ (k + 2) * b₂)) := by gcongr
      _ = 1296 * 8 ^ (k + 2) / P.a * (b₁ + 1 * b₂) := by ring
      _ ≤ 20000 * 8 ^ (n + 3) / P.a * (b₁ + 1 * b₂) := by
          have h1 : (1296 : ℝ) * 8 ^ (k + 2) ≤ 20000 * 8 ^ (n + 3) := by
            have := pow_pos (by norm_num : (0 : ℝ) < 8) (k + 2)
            linarith
          have hX : 0 ≤ (b₁ + 1 * b₂) := by positivity
          exact mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right ha).2 h1) hX
  · -- adjacent levels
    intro j hj i hi l hl hdist
    obtain ⟨hic, hicont⟩ := (D.ms3_mem_contIndex P).1 hi
    obtain ⟨hlc, -⟩ := (D.ms3_mem_contIndex P).1 hl
    have hr : 0 < P.scale T j := P.scale_pos T hR j
    have hr1 : P.scale T (j + 1) = P.scale T j / 10 := P.ms3_scale_succ T j
    have hρ : 0 < 5 * P.scale T (j + 1) := by rw [hr1]; linarith
    rw [ms3_planeComparison_eq]
    refine ms3_ofReal_le_of_real hC (by positivity) _ _ fun b₁ b₂ hb₁ hb₂ he₁ he₂ => ?_
    have hf₂ : spatialFittingIntegral (P.ν.restrict (Metric.ball (D.cand j l) (40 * P.scale T j)))
        (D.plane j l) ≤
          ENNReal.ofReal ((5 * P.scale T (j + 1)) ^ (k + 2) * (8 ^ (k + 2) * 10 ^ (k + 2) * b₂)) := by
      refine (hfit hj hlc hb₂ he₂).trans_eq (congrArg ENNReal.ofReal ?_)
      rw [hr1, show (5 : ℝ) * P.scale T j = 10 * (5 * (P.scale T j / 10)) by ring, mul_pow]
      ring
    have hcore := ms3_core_comparison hT P.ν (D.cand (j + 1) i) hρ ha hicont (D.plane (j + 1) i)
      (D.plane j l) _ _
      (Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl)
      (Measure.restrict_mono (Metric.ball_subset_ball' (by rw [hr1]; linarith)) le_rfl)
      (by positivity) (by positivity) (hfit (by omega) hic hb₁ he₁) hf₂
    have hxy : ‖(D.cand j l).1 - (D.cand (j + 1) i).1‖ ≤ 40 * (5 * P.scale T (j + 1)) := by
      have h1 := ms3_norm_sub_le_dist (D.cand j l) (D.cand (j + 1) i)
      rw [dist_comm] at h1
      rw [hr1]
      linarith
    have hch := ms3_change_sq (D.plane (j + 1) i) (D.plane j l) (D.cand (j + 1) i).1
      (D.cand j l).1 hρ hr (by norm_num) hxy
    have hfac : (1 + (40 + 1) * (5 * P.scale T (j + 1)) / P.scale T j) = 43 / 2 := by
      rw [hr1]
      field_simp
      ring
    rw [hfac] at hch
    calc affineComparison (D.plane (j + 1) i) (D.plane j l) (D.cand j l).1 (P.scale T j) ^ 2
        ≤ (43 / 2) ^ 2 * affineComparison (D.plane (j + 1) i) (D.plane j l) (D.cand (j + 1) i).1
            (5 * P.scale T (j + 1)) ^ 2 := hch
      _ ≤ (43 / 2) ^ 2 * (36 / P.a * (8 ^ (k + 2) * b₁ + 8 ^ (k + 2) * 10 ^ (k + 2) * b₂)) := by
          gcongr
      _ = 16641 * 8 ^ (k + 2) / P.a * (b₁ + 10 ^ (k + 2) * b₂) := by ring
      _ ≤ 20000 * 8 ^ (n + 3) / P.a * (b₁ + 10 ^ (k + 2) * b₂) := by
          have h1 : (16641 : ℝ) * 8 ^ (k + 2) ≤ 20000 * 8 ^ (n + 3) := by
            have := pow_pos (by norm_num : (0 : ℝ) < 8) (k + 2)
            linarith
          have hX : 0 ≤ (b₁ + 10 ^ (k + 2) * b₂) := by positivity
          exact mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right ha).2 h1) hX
  · -- level one against the artificial root
    intro i hi
    obtain ⟨hic, hicont⟩ := (D.ms3_mem_contIndex P).1 hi
    have hr0 : 0 < P.scale T 0 := P.scale_pos T hR 0
    have hr1 : P.scale T 1 = P.scale T 0 / 10 := P.ms3_scale_succ T 0
    have hρ : 0 < 5 * P.scale T 1 := by rw [hr1]; linarith
    rw [ms3_planeComparison_eq]
    refine ms3_ofReal_le_of_real hC (by positivity) _ _ fun b₁ b₂ hb₁ hb₂ he₁ he₂ => ?_
    have hf₂ : spatialFittingIntegral P.ν D.rootPlane ≤
        ENNReal.ofReal ((5 * P.scale T 1) ^ (k + 2) *
          (2 ^ (k + 2) * ((P.scale T 0)⁻¹ ^ (k + 2) * b₂))) := by
      refine ((D.ms3_rootFit_le P).trans he₂.le).trans_eq (congrArg ENNReal.ofReal ?_)
      rw [hr1, show (5 : ℝ) * (P.scale T 0 / 10) = P.scale T 0 / 2 by ring]
      have hne : P.scale T 0 ≠ 0 := hr0.ne'
      calc b₂ = ((P.scale T 0 / 2 * 2) * (P.scale T 0)⁻¹) ^ (k + 2) * b₂ := by
            rw [div_mul_cancel₀ _ two_ne_zero, mul_inv_cancel₀ hne, one_pow, one_mul]
        _ = _ := by rw [mul_pow, mul_pow]; ring
    have hcore := ms3_core_comparison hT P.ν (D.cand 1 i) hρ ha hicont (D.plane 1 i)
      D.rootPlane _ P.ν
      (Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl)
      Measure.restrict_le_self
      (by positivity) (by positivity) (hfit le_rfl hic hb₁ he₁) hf₂
    have hgS : D.cand 1 i ∈ Metric.ball P.q P.R :=
      hP.S_subset (D.ms3_cand_mem_S P hD le_rfl hic)
    have h4R : 4 * P.R ≤ P.scale T 0 := by
      rw [P.ms3_scale_zero T]
      exact T.ms3_four_le_rootRadius hR.le
    have hxy : ‖D.rootCenter.1 - (D.cand 1 i).1‖ ≤ 1 * (5 * P.scale T 1) := by
      have h1 := ms3_norm_sub_le_dist D.rootCenter (D.cand 1 i)
      have h2 := dist_triangle D.rootCenter P.q (D.cand 1 i)
      have h3 := hD.root_dist
      have h5 : dist P.q (D.cand 1 i) < P.R := by
        rw [dist_comm]
        exact hgS
      rw [hr1]
      linarith
    have hch := ms3_change_sq (D.plane 1 i) D.rootPlane (D.cand 1 i).1 D.rootCenter.1 hρ hr0
      zero_le_one hxy
    have hfac : (1 + (1 + 1) * (5 * P.scale T 1) / P.scale T 0) = 2 := by
      rw [hr1]
      field_simp
      ring
    rw [hfac] at hch
    have h2 : (2 : ℝ) ^ (k + 2) ≤ 8 ^ (k + 2) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have hw : 0 ≤ (P.scale T 0)⁻¹ ^ (k + 2) * b₂ := by positivity
    calc affineComparison (D.plane 1 i) D.rootPlane D.rootCenter.1 (P.scale T 0) ^ 2
        ≤ 2 ^ 2 * affineComparison (D.plane 1 i) D.rootPlane (D.cand 1 i).1
            (5 * P.scale T 1) ^ 2 := hch
      _ ≤ 2 ^ 2 * (36 / P.a * (8 ^ (k + 2) * b₁ +
            2 ^ (k + 2) * ((P.scale T 0)⁻¹ ^ (k + 2) * b₂))) := by gcongr
      _ ≤ 2 ^ 2 * (36 / P.a * (8 ^ (k + 2) * b₁ +
            8 ^ (k + 2) * ((P.scale T 0)⁻¹ ^ (k + 2) * b₂))) := by gcongr
      _ = 144 * 8 ^ (k + 2) / P.a * (b₁ + (P.scale T 0)⁻¹ ^ (k + 2) * b₂) := by ring
      _ ≤ 20000 * 8 ^ (n + 3) / P.a * (b₁ + (P.scale T 0)⁻¹ ^ (k + 2) * b₂) := by
          have h1 : (144 : ℝ) * 8 ^ (k + 2) ≤ 20000 * 8 ^ (n + 3) := by
            have := pow_pos (by norm_num : (0 : ℝ) < 8) (k + 2)
            linarith
          have hX : 0 ≤ (b₁ + (P.scale T 0)⁻¹ ^ (k + 2) * b₂) := by positivity
          exact mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right ha).2 h1) hX

/-- **`planeComparison_sq_le`**: the squared comparison of two fitted planes is bounded by
the normalized fitting errors. -/
theorem planeComparison_sq_le_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T),
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
                ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν)) :=
  ⟨20000 * 8 ^ (n + 3), by positivity, ms3_planeComparison_explicit n⟩

end ParabolicRectifiability
