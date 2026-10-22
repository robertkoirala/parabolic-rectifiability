import ParabolicRectifiability.Measure.Neck.Construction

/-!
# Tail, beta and error estimates of the source construction

Proofs of five auxiliary statements about the construction of a neck from a source, with the
types of `initialTube_error_le`, `errorSet_le`, `measure_eq_of_construction`, `nodeBeta_le`
and `collapsedFit_le`:

* `initialTube_error_le_proof` (`initialTube_error_le`);
* `errorSet_le_proof` (`errorSet_le`), in implication form: it takes the statement
  `nodeError_le` as a hypothesis;
* `measure_eq_of_construction_proof` (`measure_eq_of_construction`), in implication form:
  it takes the statement `partitionFacts_of_construction` as a hypothesis;
* `nodeBeta_le_proof` (`nodeBeta_le`);
* `collapsedFit_le_proof` (`collapsedFit_le`).

The single analytic input is the elementary scale-integral comparison
`le_of_tailEnergy_le`: if `β²(z, r) ≥ c r^{-p}` on `(s, 2s)` and the tail energy above
`t ≤ s` is at most `B`, then `c ≤ 2 p B s^p` (`p = k + 2`), because
`∫_s^{2s} r^{-p} dr/r = (1 - 2^{-p}) / (p s^p) ≥ 1 / (2 p s^p)`. It is applied

* to the global fitting error, which every point of `S ⊆ P(q,R)` sees on `(2R, 4R)`
  (the source is carried by `S`), and
* to the fitting error of a candidate `g` on `P(g, 40 r_j)`, using `f(g) < r_j` and the
  monotonicity of the fit in the radius.

Every estimate is for the original source `ν`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-! ## Elementary comparisons -/

/-- The scale-integral comparison: a lower bound `c r^{-(k+2)}` for `β²(z, r)` on
`(s, 2s)`, inside the range of a tail energy bounded by `B`, gives
`c ≤ 2 (k+2) B s^{k+2}`. -/
theorem le_of_tailEnergy_le {n k : ℕ} {F : FamilyKind} {ν : Measure (Space n)}
    {z : Space n} {t s B : ℝ} {c : ℝ≥0∞} (hs : 0 < s) (hts : t ≤ s) (hB : 0 ≤ B)
    (hc : ∀ r ∈ Ioo s (2 * s), c * (ENNReal.ofReal r)⁻¹ ^ (k + 2) ≤ betaSq ν k F z r)
    (htail : tailEnergy ν k F t z ≤ ENNReal.ofReal B) :
    c ≤ ENNReal.ofReal (2 * ((k + 2 : ℕ) : ℝ) * B * s ^ (k + 2)) := by
  have hp : 0 < k + 2 := by omega
  have hpR : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by exact_mod_cast hp
  have hu : 0 < s ^ (k + 2) := pow_pos hs _
  have hv : (2 : ℝ) ≤ 2 ^ (k + 2) := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : ((2 * s) ^ (k + 2))⁻¹ ≤ (s ^ (k + 2))⁻¹ / 2 := by
    calc ((2 * s) ^ (k + 2))⁻¹ = (2 ^ (k + 2))⁻¹ * (s ^ (k + 2))⁻¹ := by rw [mul_pow, mul_inv]
      _ ≤ 2⁻¹ * (s ^ (k + 2))⁻¹ :=
          mul_le_mul_of_nonneg_right (inv_anti₀ (by norm_num) hv) (inv_nonneg.2 hu.le)
      _ = (s ^ (k + 2))⁻¹ / 2 := by ring
  set a : ℝ := ((s ^ (k + 2))⁻¹ - ((2 * s) ^ (k + 2))⁻¹) / ((k + 2 : ℕ) : ℝ) with ha_def
  have ha_ge : (s ^ (k + 2))⁻¹ / 2 / ((k + 2 : ℕ) : ℝ) ≤ a := by
    rw [ha_def]
    exact div_le_div_of_nonneg_right (by linarith) hpR.le
  have ha_low : 0 < (s ^ (k + 2))⁻¹ / 2 / ((k + 2 : ℕ) : ℝ) := by positivity
  have ha : 0 < a := lt_of_lt_of_le ha_low ha_ge
  have hint : (∫⁻ r in Ioo s (2 * s), (ENNReal.ofReal r)⁻¹ ^ (k + 2) ∂scaleMeasure) =
      ENNReal.ofReal a :=
    lintegral_inv_pow_Ioo_scaleMeasure (k + 2) hp hs (by linarith)
  have hmain : c * ENNReal.ofReal a ≤ ENNReal.ofReal B := by
    calc c * ENNReal.ofReal a
        = ∫⁻ r in Ioo s (2 * s), c * (ENNReal.ofReal r)⁻¹ ^ (k + 2) ∂scaleMeasure := by
          rw [lintegral_const_mul c (measurable_inv_pow_ofReal (k + 2)), hint]
      _ ≤ ∫⁻ r in Ioo s (2 * s), betaSq ν k F z r ∂scaleMeasure :=
          setLIntegral_mono' measurableSet_Ioo hc
      _ ≤ ∫⁻ r in Ioi t, betaSq ν k F z r ∂scaleMeasure :=
          lintegral_mono_set fun r hr => lt_of_le_of_lt hts hr.1
      _ = tailEnergy ν k F t z := rfl
      _ ≤ ENNReal.ofReal B := htail
  have hc_le : c ≤ ENNReal.ofReal (B / a) := by
    rw [ENNReal.ofReal_div_of_pos ha]
    exact (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 ha).ne')
      (Or.inl ENNReal.ofReal_ne_top)).2 hmain
  refine hc_le.trans (ENNReal.ofReal_le_ofReal ?_)
  have hu0 : s ^ (k + 2) ≠ 0 := hu.ne'
  have hp0 : ((k + 2 : ℕ) : ℝ) ≠ 0 := hpR.ne'
  calc B / a ≤ B / ((s ^ (k + 2))⁻¹ / 2 / ((k + 2 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_left hB ha_low ha_ge
    _ = 2 * ((k + 2 : ℕ) : ℝ) * B * s ^ (k + 2) := by
        field_simp

/-- Cancellation of a positive radius power. -/
theorem inv_pow_mul_ofReal_mul_pow {s X : ℝ} (hs : 0 < s) (hX : 0 ≤ X) (p : ℕ) :
    (ENNReal.ofReal s)⁻¹ ^ p * ENNReal.ofReal (X * s ^ p) = ENNReal.ofReal X := by
  rw [ENNReal.ofReal_mul hX, ENNReal.ofReal_pow hs.le, mul_left_comm, ← mul_pow,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hs).ne' ENNReal.ofReal_ne_top, one_pow,
    mul_one]

/-- The dimensional constants are uniform for `k < n + 2`. -/
theorem tailConst_le {n k : ℕ} (hk : k < n + 2) {b : ℝ} (hb : 1 ≤ b) :
    2 * ((k + 2 : ℕ) : ℝ) * b ^ (k + 2) ≤ 2 * ((n + 3 : ℕ) : ℝ) * b ^ (n + 3) := by
  have h1 : ((k + 2 : ℕ) : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 2 ≤ n + 3)
  have h2 : b ^ (k + 2) ≤ b ^ (n + 3) := pow_le_pow_right₀ hb (by omega)
  have h3 : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ b ^ (k + 2) := pow_nonneg (by linarith) _
  have h5 : (0 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul (by linarith) h2 h4 (by linarith)

/-- Monotonicity of a fit in the radius. -/
theorem fit_mono_radius {n k : ℕ} {F : FamilyKind} (ν : Measure (Space n)) (L : Models n k F)
    (z : Space n) {s r : ℝ} (hsr : s ≤ r) : fit ν L z s ≤ fit ν L z r :=
  lintegral_mono_set (Metric.ball_subset_ball hsr)

/-! ## The kept sets stay inside the source set -/

namespace ConstructionData

variable {n k : ℕ} {T : NeckType}

theorem kept_zero (D : ConstructionData n k T) (P : SourceSetup n) :
    D.kept P 0 = D.tubeSet P := rfl

theorem kept_succ (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) :
    D.kept P (j + 1) = D.stageKept P (j + 1) (D.kept P j) := rfl

theorem stageKept_subset (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ)
    (E : Set (Space n)) : D.stageKept P j E ⊆ E := by
  intro z hz
  simp only [stageKept, mem_iUnion] at hz
  obtain ⟨i, -, hz⟩ := hz
  exact hz.1.1.1.1

theorem kept_subset (D : ConstructionData n k T) (P : SourceSetup n) :
    ∀ j, D.kept P j ⊆ P.S
  | 0 => by rw [kept_zero]; exact inter_subset_left
  | j + 1 => by rw [kept_succ]; exact (D.stageKept_subset P (j + 1) _).trans (D.kept_subset P j)

theorem entering_subset (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) :
    D.entering P j ⊆ P.S :=
  D.kept_subset P (j - 1)

/-- A candidate lies in the source set and below the cutoff scale of its stage. -/
theorem cand_mem_S_and_cutoff_lt {D : ConstructionData n k T} {P : SourceSetup n}
    (hD : D.IsSourceConstruction P) {j : ℕ} (hj : 1 ≤ j) {i : ℕ} (hi : i < D.candCount j) :
    D.cand j i ∈ P.S ∧ P.f (D.cand j i) < P.scale T j := by
  have hg := hD.cand_mem j hj i hi
  exact ⟨D.entering_subset P j hg.1, hD.term_done j hj _ hg⟩

/-! ## The global error and the node fits -/

/-- The global error of the minimizing root model is bounded through the tail at any source
point: every point of `S` sees the whole source on `(2R, 4R)`. -/
theorem rootError_le {P : SourceSetup n} {D : ConstructionData n k T} {B : ℝ}
    (hP : P.IsAdmissible) (hB : 0 ≤ B) (htail : P.TailBound k T B)
    (hD : D.IsSourceConstruction P) :
    ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν ≤
      ENNReal.ofReal (2 * ((k + 2 : ℕ) : ℝ) * 2 ^ (k + 2) * B * P.R ^ (k + 2)) := by
  have hroot : ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν ≤
      globalFittingError P.ν k T.toFamilyKind := le_iInf hD.root_minimal
  rcases P.S.eq_empty_or_nonempty with hS | ⟨z, hz⟩
  · have hν : P.ν = 0 := by
      rw [← Measure.measure_univ_eq_zero]
      have h := hP.carried
      rwa [hS, compl_empty] at h
    rw [hν, lintegral_zero_measure]
    exact zero_le
  · have hR := hP.R_pos
    have hae : ∀ᵐ w ∂P.ν, w ∈ P.S := ae_iff.2 hP.carried
    have hzq : dist z P.q < P.R := Metric.mem_ball.1 (hP.S_subset hz)
    have hclaim : ∀ r ∈ Ioo (2 * P.R) (2 * (2 * P.R)),
        globalFittingError P.ν k T.toFamilyKind * (ENNReal.ofReal r)⁻¹ ^ (k + 2) ≤
          betaSq P.ν k T.toFamilyKind z r := by
      intro r hr
      have hball : ∀ᵐ w ∂P.ν, w ∈ Metric.ball z r := by
        filter_upwards [hae] with w hw
        have hwq : dist w P.q < P.R := Metric.mem_ball.1 (hP.S_subset hw)
        rw [Metric.mem_ball]
        calc dist w z ≤ dist w P.q + dist z P.q := dist_triangle_right w z P.q
          _ < P.R + P.R := add_lt_add hwq hzq
          _ < r := by linarith [hr.1]
      rw [betaSq_eq_global_of_ae_mem_ball _ _ _ _ (by linarith [hr.1]) hball]
      exact le_of_eq (mul_comm _ _)
    have key := le_of_tailEnergy_le (by linarith) (by linarith [hP.cutoff.le_radius z hz]) hB
      hclaim (htail z hz)
    refine hroot.trans (key.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
    ring

/-- The original-source fitting error of a candidate on `P(g, 40 r_j)` is bounded by the
tail at the candidate, since `f(g) < r_j`. -/
theorem candFit_le {P : SourceSetup n} {D : ConstructionData n k T} {B : ℝ}
    (hP : P.IsAdmissible) (hB : 0 ≤ B) (htail : P.TailBound k T B)
    (hD : D.IsSourceConstruction P) {j : ℕ} (hj : 1 ≤ j) {i : ℕ} (hi : i < D.candCount j) :
    (⨅ L : Models n k T.toFamilyKind, fit P.ν L (D.cand j i) (40 * P.scale T j)) ≤
      ENNReal.ofReal (2 * ((k + 2 : ℕ) : ℝ) * B * (40 * P.scale T j) ^ (k + 2)) := by
  obtain ⟨hgS, hfg⟩ := cand_mem_S_and_cutoff_lt hD hj hi
  have hr := P.scale_pos T hP.R_pos j
  have hs : 0 < 40 * P.scale T j := by linarith
  have hclaim : ∀ r ∈ Ioo (40 * P.scale T j) (2 * (40 * P.scale T j)),
      (⨅ L : Models n k T.toFamilyKind, fit P.ν L (D.cand j i) (40 * P.scale T j)) *
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) ≤
        betaSq P.ν k T.toFamilyKind (D.cand j i) r := by
    intro r hr'
    rw [betaSq_of_pos _ _ _ _ (hs.trans hr'.1)]
    exact (mul_comm _ _).le.trans
      (mul_le_mul' le_rfl (iInf_mono fun L => fit_mono_radius _ _ _ hr'.1.le))
  exact le_of_tailEnergy_le hs (by linarith) hB hclaim (htail _ hgS)

/-- Node beta at a candidate `b_ν(g, 40 r_j) ≤ 2 (k+2) B`. -/
theorem candBeta_le {P : SourceSetup n} {D : ConstructionData n k T} {B : ℝ}
    (hP : P.IsAdmissible) (hB : 0 ≤ B) (htail : P.TailBound k T B)
    (hD : D.IsSourceConstruction P) {j : ℕ} (hj : 1 ≤ j) {i : ℕ} (hi : i < D.candCount j) :
    betaSq P.ν k T.toFamilyKind (D.cand j i) (40 * P.scale T j) ≤
      ENNReal.ofReal (2 * ((k + 2 : ℕ) : ℝ) * B) := by
  have hr := P.scale_pos T hP.R_pos j
  have hs : 0 < 40 * P.scale T j := by linarith
  rw [betaSq_of_pos _ _ _ _ hs]
  calc (ENNReal.ofReal (40 * P.scale T j))⁻¹ ^ (k + 2) *
        (⨅ L : Models n k T.toFamilyKind, fit P.ν L (D.cand j i) (40 * P.scale T j))
      ≤ (ENNReal.ofReal (40 * P.scale T j))⁻¹ ^ (k + 2) *
          ENNReal.ofReal (2 * ((k + 2 : ℕ) : ℝ) * B * (40 * P.scale T j) ^ (k + 2)) :=
        mul_le_mul' le_rfl (candFit_le hP hB htail hD hj hi)
    _ = ENNReal.ofReal (2 * ((k + 2 : ℕ) : ℝ) * B) :=
        inv_pow_mul_ofReal_mul_pow hs (by positivity) _

/-! ## Countability of the stopping centers -/

/-- Every stopping center is a terminal center or a candidate of some stage. -/
theorem stopping_countable (D : ConstructionData n k T) (P : SourceSetup n) :
    (D.stopping P).Countable := by
  have hsub : D.stopping P ⊆ range (fun p : ℕ × ℕ => D.term p.1 p.2) ∪
      range (fun p : ℕ × ℕ => D.cand p.1 p.2) := by
    rintro c ⟨-, hc⟩
    by_cases hT : D.IsTermCenter c
    · obtain ⟨j, -, i, -, rfl⟩ := hT
      exact Or.inl ⟨(j, i), rfl⟩
    · by_cases hC : D.IsCollCenter P c
      · obtain ⟨j, -, i, -, -, rfl, -⟩ := hC
        exact Or.inr ⟨(j, i), rfl⟩
      · simp [radius, hT, hC] at hc
  exact ((countable_range _).union (countable_range _)).mono hsub

end ConstructionData

/-! ## The estimates -/

/-- **`initialTube_error_le`**: `ν(S \ S₀) ≤ C B R^k / θ²`,
by Chebyshev's inequality for the global error. -/
theorem initialTube_error_le_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T)
      (B : ℝ), T.Available n k → k < n + 2 → P.IsAdmissible → 0 < B → P.TailBound k T B →
      D.IsSourceConstruction P →
      P.ν (P.S \ D.tubeSet P) ≤ ENNReal.ofReal (C * B * P.R ^ k / P.θ ^ 2) := by
  refine ⟨2 * ((n + 3 : ℕ) : ℝ) * 2 ^ (n + 3), by positivity, ?_⟩
  intro k T P D B _ hk hP hB htail hD
  have hR := hP.R_pos
  have hθ := hP.θ_pos
  have hθR : 0 < P.θ * P.R := mul_pos hθ hR
  set ε : ℝ≥0∞ := ENNReal.ofReal ((P.θ * P.R) ^ 2) with hε
  have hsub : P.S \ D.tubeSet P ⊆ {z | ε ≤ Metric.infEDist z D.rootModel ^ 2} := by
    rintro z ⟨hzS, hzt⟩
    have hlt : ENNReal.ofReal (P.θ * P.R) < Metric.infEDist z D.rootModel := by
      by_contra h
      exact hzt ⟨hzS, not_lt.1 h⟩
    show ε ≤ Metric.infEDist z D.rootModel ^ 2
    rw [hε, ENNReal.ofReal_pow hθR.le]
    exact pow_le_pow_left₀ zero_le hlt.le 2
  have hmeas : AEMeasurable (fun z => Metric.infEDist z D.rootModel ^ 2) P.ν :=
    ((ENNReal.continuous_pow 2).comp Metric.continuous_infEDist).measurable.aemeasurable
  have hcheb := mul_meas_ge_le_lintegral₀ hmeas ε
  have hglob := ConstructionData.rootError_le hP hB.le htail hD
  have hε0 : ε ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hθR 2)).ne'
  have hK : 2 * ((k + 2 : ℕ) : ℝ) * 2 ^ (k + 2) ≤ 2 * ((n + 3 : ℕ) : ℝ) * 2 ^ (n + 3) :=
    tailConst_le hk (by norm_num)
  calc P.ν (P.S \ D.tubeSet P) ≤ P.ν {z | ε ≤ Metric.infEDist z D.rootModel ^ 2} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (2 * ((k + 2 : ℕ) : ℝ) * 2 ^ (k + 2) * B * P.R ^ (k + 2)) / ε := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl ENNReal.ofReal_ne_top)]
        exact (mul_comm _ _).le.trans (hcheb.trans hglob)
    _ = ENNReal.ofReal (2 * ((k + 2 : ℕ) : ℝ) * 2 ^ (k + 2) * B * P.R ^ k / P.θ ^ 2) := by
        rw [hε, ← ENNReal.ofReal_div_of_pos (pow_pos hθR 2)]
        have hR0 : P.R ≠ 0 := hR.ne'
        have hθ0 : P.θ ≠ 0 := hθ.ne'
        congr 1
        field_simp
        ring
    _ ≤ ENNReal.ofReal (2 * ((n + 3 : ℕ) : ℝ) * 2 ^ (n + 3) * B * P.R ^ k / P.θ ^ 2) := by
        refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (sq_nonneg _))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hB.le)
          (pow_nonneg hR.le k)

/-- **`nodeBeta_le`**: every candidate has
`b_ν(g, 40 r_j) ≤ C B`, and the global error is `I_* ≤ C B R^{k+2}`. -/
theorem nodeBeta_le_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T)
      (B : ℝ), T.Available n k → k < n + 2 → P.IsAdmissible → 0 < B → P.TailBound k T B →
      D.IsSourceConstruction P →
      (∀ j, 1 ≤ j → ∀ i, i < D.candCount j →
        betaSq P.ν k T.toFamilyKind (D.cand j i) (40 * P.scale T j) ≤
          ENNReal.ofReal (C * B)) ∧
      ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν ≤ ENNReal.ofReal (C * B * P.R ^ (k + 2)) := by
  refine ⟨2 * ((n + 3 : ℕ) : ℝ) * 2 ^ (n + 3), by positivity, ?_⟩
  intro k T P D B _ hk hP hB htail hD
  have hK : 2 * ((k + 2 : ℕ) : ℝ) * 2 ^ (k + 2) ≤ 2 * ((n + 3 : ℕ) : ℝ) * 2 ^ (n + 3) :=
    tailConst_le hk (by norm_num)
  have hk2 : (1 : ℝ) ≤ 2 ^ (k + 2) := one_le_pow₀ (by norm_num)
  have hp0 : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨fun j hj i hi =>
    (ConstructionData.candBeta_le hP hB.le htail hD hj hi).trans ?_, ?_⟩
  · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hB.le)
    have h1 : 2 * ((k + 2 : ℕ) : ℝ) ≤ 2 * ((k + 2 : ℕ) : ℝ) * 2 ^ (k + 2) :=
      le_mul_of_one_le_right (by positivity) hk2
    exact h1.trans hK
  · refine (ConstructionData.rootError_le hP hB.le htail hD).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hB.le)
      (pow_nonneg hP.R_pos.le _)

/-- **`collapsedFit_le`**: a model of type `T` with
`fit_ν(g, 5 r_j) ≤ C B (5 r_j)^{k+2}`, from the fit on `P(g, 40 r_j)` at the cost
`8^{k+2}`. -/
theorem collapsedFit_le_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T)
      (B : ℝ), T.Available n k → k < n + 2 → P.IsAdmissible → 0 < B → P.TailBound k T B →
      D.IsSourceConstruction P → ∀ j, 1 ≤ j → ∀ i, i < D.candCount j →
      ∃ Pm : Models n k T.toFamilyKind,
        fit P.ν Pm (D.cand j i) (5 * P.scale T j) ≤
          ENNReal.ofReal (C * B * (5 * P.scale T j) ^ (k + 2)) := by
  refine ⟨2 * (2 * ((n + 3 : ℕ) : ℝ) * 8 ^ (n + 3)), by positivity, ?_⟩
  intro k T P D B _ hk hP hB htail hD j hj i hi
  have hr := P.scale_pos T hP.R_pos j
  have h5 : 0 < 5 * P.scale T j := by linarith
  set X : ℝ := 2 * ((k + 2 : ℕ) : ℝ) * B * (40 * P.scale T j) ^ (k + 2) with hX
  have hX0 : 0 < X := by rw [hX]; positivity
  have hinf : (⨅ L : Models n k T.toFamilyKind, fit P.ν L (D.cand j i) (5 * P.scale T j)) <
      ENNReal.ofReal (2 * X) := by
    calc (⨅ L : Models n k T.toFamilyKind, fit P.ν L (D.cand j i) (5 * P.scale T j))
        ≤ ⨅ L : Models n k T.toFamilyKind, fit P.ν L (D.cand j i) (40 * P.scale T j) :=
          iInf_mono fun L => fit_mono_radius _ _ _ (by linarith)
      _ ≤ ENNReal.ofReal X := ConstructionData.candFit_le hP hB.le htail hD hj hi
      _ < ENNReal.ofReal (2 * X) := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  obtain ⟨L, hL⟩ := iInf_lt_iff.1 hinf
  refine ⟨L, hL.le.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hK : 2 * ((k + 2 : ℕ) : ℝ) * 8 ^ (k + 2) ≤ 2 * ((n + 3 : ℕ) : ℝ) * 8 ^ (n + 3) :=
    tailConst_le hk (by norm_num)
  have h40 : (40 * P.scale T j) ^ (k + 2) = 8 ^ (k + 2) * (5 * P.scale T j) ^ (k + 2) := by
    rw [← mul_pow]
    ring
  have hpow : (0 : ℝ) ≤ (5 * P.scale T j) ^ (k + 2) := pow_nonneg h5.le _
  calc 2 * X = 2 * (2 * ((k + 2 : ℕ) : ℝ) * 8 ^ (k + 2)) * B * (5 * P.scale T j) ^ (k + 2) := by
        rw [hX, h40]
        ring
    _ ≤ 2 * (2 * ((n + 3 : ℕ) : ℝ) * 8 ^ (n + 3)) * B * (5 * P.scale T j) ^ (k + 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hB.le) hpow
        linarith

/-- **`errorSet_le`**, in implication form: the statement `nodeError_le`
(hypothesis `hnode`) implies the estimate for the error set; the initial-tube part is
`initialTube_error_le_proof`. -/
theorem errorSet_le_proof (n : ℕ)
    (hnode : ∃ C θ₁ A₁ : ℝ, 0 < C ∧ 0 < θ₁ ∧ 0 < A₁ ∧ ∀ {k : ℕ} {T : NeckType}
      (P : SourceSetup n) (D : ConstructionData n k T) (B : ℝ), T.Available n k →
      k < n + 2 → P.IsAdmissible → 0 < B → P.TailBound k T B → D.IsSourceConstruction P →
      P.θ ≤ θ₁ → A₁ * B ≤ P.a →
      P.ν (D.nodeErrorSet P) ≤ ENNReal.ofReal (C * B * P.R ^ k / P.θ ^ 2)) :
    ∃ C θ₁ A₁ : ℝ, 0 < C ∧ 0 < θ₁ ∧ 0 < A₁ ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
      (D : ConstructionData n k T) (B : ℝ), T.Available n k → k < n + 2 → P.IsAdmissible →
      0 < B → P.TailBound k T B → D.IsSourceConstruction P → P.θ ≤ θ₁ → A₁ * B ≤ P.a →
      ∀ L : ℝ, C ≤ L → P.ν (D.errorSet P) ≤ ENNReal.ofReal (L * B * P.R ^ k / P.θ ^ 2) := by
  obtain ⟨C₃, θ₁, A₁, hC₃, hθ₁, hA₁, h₃⟩ := hnode
  obtain ⟨C₂, hC₂, h₂⟩ := initialTube_error_le_proof n
  refine ⟨C₂ + C₃, θ₁, A₁, by linarith, hθ₁, hA₁, ?_⟩
  intro k T P D B hT hk hP hB htail hD hθ hA L hL
  have hR := hP.R_pos
  have hθpos := hP.θ_pos
  have hq : 0 ≤ B * P.R ^ k / P.θ ^ 2 := by positivity
  calc P.ν (D.errorSet P) ≤ P.ν (P.S \ D.tubeSet P) + P.ν (D.nodeErrorSet P) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₂ * B * P.R ^ k / P.θ ^ 2) +
          ENNReal.ofReal (C₃ * B * P.R ^ k / P.θ ^ 2) :=
        add_le_add (h₂ P D B hT hk hP hB htail hD) (h₃ P D B hT hk hP hB htail hD hθ hA)
    _ = ENNReal.ofReal ((C₂ + C₃) * (B * P.R ^ k / P.θ ^ 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (L * (B * P.R ^ k / P.θ ^ 2)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hL hq)
    _ = ENNReal.ofReal (L * B * P.R ^ k / P.θ ^ 2) := by
        congr 1
        ring

/-- **`measure_eq_of_construction`**, in implication form: the statement
`partitionFacts_of_construction` (hypothesis `hpart`) implies the measure identity. The source is carried by
`S`, which is the disjoint Borel union of the error, the core assignment and the
assignments of the countably many stopping centers. -/
theorem measure_eq_of_construction_proof (n : ℕ)
    (hpart : ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T),
      T.Available n k → k < n + 2 → P.IsAdmissible → D.IsSourceConstruction P →
      D.PartitionFacts P) :
    ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T),
      T.Available n k → k < n + 2 → P.IsAdmissible → D.IsSourceConstruction P →
      P.ν = P.ν.restrict (D.errorSet P) + P.ν.restrict (D.coreSet P) +
        Measure.sum (fun c : D.stopping P => P.ν.restrict (D.assignment P c)) := by
  intro k T P D hT hk hP hD
  have hF := hpart P D hT hk hP hD
  have : Countable (D.stopping P) := (D.stopping_countable P).to_subtype
  have hUm : MeasurableSet (⋃ c : D.stopping P, D.assignment P c) :=
    MeasurableSet.iUnion fun c => hF.measurableSet_assignment c c.2
  have hS : P.S = (D.errorSet P ∪ D.coreSet P) ∪ ⋃ c : D.stopping P, D.assignment P c := by
    apply Subset.antisymm
    · intro z hz
      rcases hF.cover hz with h | h
      · exact Or.inl h
      · obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.1 h
        exact Or.inr (mem_iUnion.2 ⟨⟨c, hc⟩, hzc⟩)
    · rintro z ((h | h) | h)
      · exact hF.errorSet_subset h
      · exact hF.coreSet_subset h
      · obtain ⟨c, hzc⟩ := mem_iUnion.1 h
        exact hF.assignment_subset c c.2 hzc
  have hdisj : Disjoint (D.errorSet P ∪ D.coreSet P) (⋃ c : D.stopping P, D.assignment P c) := by
    rw [disjoint_union_left, disjoint_iUnion_right, disjoint_iUnion_right]
    exact ⟨fun c => hF.disjoint_errorSet_assignment c c.2,
      fun c => hF.disjoint_coreSet_assignment c c.2⟩
  have hpair : Pairwise fun c c' : D.stopping P => Disjoint (D.assignment P c) (D.assignment P c') :=
    fun c c' hcc' => hF.disjoint_assignment c c.2 c' c'.2 fun h => hcc' (Subtype.ext h)
  have hae : ∀ᵐ w ∂P.ν, w ∈ P.S := ae_iff.2 hP.carried
  calc P.ν = P.ν.restrict P.S := (Measure.restrict_eq_self_of_ae_mem hae).symm
    _ = P.ν.restrict ((D.errorSet P ∪ D.coreSet P) ∪ ⋃ c : D.stopping P, D.assignment P c) := by
        rw [← hS]
    _ = _ := by
        rw [Measure.restrict_union hdisj hUm,
          Measure.restrict_union hF.disjoint_errorSet_coreSet hF.measurableSet_coreSet,
          Measure.restrict_iUnion hpair fun c => hF.measurableSet_assignment c c.2]

end ParabolicRectifiability
