import ParabolicRectifiability.Measure.Neck.RegionCore.CoreLower

/-!
# Core square and core own square

Proofs of two statements about the all-scale square bounds at the core:

* `core_square_of_construction_proof` (`core_square_of_construction`):
  for a core point `z` and `b > 0` choose a stage `j ≥ 1` with `r_j ≤ 2b` and a kept point
  `y ∈ S_j ⊆ S` with `d_P(z,y) < b`; then `f(y) < r_j ≤ 2b`, `P(z,r) ⊆ P(y,2r)` for `r > b`, and
  `∫_b^∞ b_ν(z,r) dr/r ≤ 2^{k+2} ∫_{2b}^∞ b_ν(y,s) ds/s ≤ 2^{k+2} B` by the invariance of
  `dr/r` under `r ↦ 2r` and the tail bound at `y`. Monotone convergence as `b ↓ 0` gives the
  all-scale bound, also at core points outside `S`. `C = 2^{n+3}`.
* `eta_square_of_construction_proof` (`eta_square_of_construction`): the domination
  `H^k_P ⌞ C₀ ≤ (C_17/a) ν` of `core_domination_of_construction_proof`, monotonicity of `β²` in the measure and its exact
  homogeneity under a finite positive scalar give `∫_0^∞ b_η(z,r) dr/r ≤ L B / a` with
  `C = C_17 C_18`, where `C_18` is the constant of the core square bound.

The scale-invariance lemmas are local copies (renamed with the prefix `ms4_`) of
`scaleMeasure_map_mul_left_aux` and `setLIntegral_scaleMeasure_comp_mul_left_aux` from the
trace extension development, so that this module imports no trace-extension file.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-! ## Scale invariance of `dr/r` (local copy) -/

/-- The scale measure `ds/s` is invariant under `s ↦ c s`, `c > 0`. -/
theorem ms4_scaleMeasure_map_mul_left {c : ℝ} (hc : 0 < c) :
    Measure.map (fun s => c * s) scaleMeasure = scaleMeasure := by
  ext A hA
  have hA' : MeasurableSet (A ∩ Ioi 0) := hA.inter measurableSet_Ioi
  have hpre : MeasurableSet ((fun s => c * s) ⁻¹' A) := measurable_const_mul c hA
  rw [Measure.map_apply (measurable_const_mul c) hA, scaleMeasure_apply _ hpre,
    scaleMeasure_apply _ hA]
  have hset : (fun s => c * s) ⁻¹' A ∩ Ioi 0 = (fun s => c * s) ⁻¹' (A ∩ Ioi 0) := by
    ext r
    simp only [mem_inter_iff, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, mul_pos hc h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, pos_of_mul_pos_right h2 hc.le⟩
  rw [hset, ← lintegral_indicator (measurable_const_mul c hA'), ← lintegral_indicator hA']
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ≥0∞,
      G = (A ∩ Ioi 0).indicator (fun t => ENNReal.ofReal (1 / t)) := ⟨_, rfl⟩
  rw [← hG]
  have hfun : ∀ r, ((fun s => c * s) ⁻¹' (A ∩ Ioi 0)).indicator
      (fun r => ENNReal.ofReal (1 / r)) r = ENNReal.ofReal c * G (c * r) := by
    intro r
    rw [hG]
    by_cases hr : c * r ∈ A ∩ Ioi 0
    · rw [indicator_of_mem (show r ∈ (fun s => c * s) ⁻¹' (A ∩ Ioi 0) from hr),
        indicator_of_mem hr, ← ENNReal.ofReal_mul hc.le, mul_one_div,
        div_mul_cancel_left₀ hc.ne', one_div]
    · rw [indicator_of_notMem (show r ∉ (fun s => c * s) ⁻¹' (A ∩ Ioi 0) from hr),
        indicator_of_notMem hr, mul_zero]
  have hmap : ∫⁻ r, G (c * r) = ENNReal.ofReal |c⁻¹| * ∫⁻ t, G t := by
    calc
      ∫⁻ r, G (c * r) = ∫⁻ t, G t ∂(Measure.map (fun s => c * s) volume) :=
        (lintegral_map_equiv G (MeasurableEquiv.mulLeft₀ c hc.ne')).symm
      _ = ∫⁻ t, G t ∂(ENNReal.ofReal |c⁻¹| • volume) := by
        rw [Real.map_volume_mul_left hc.ne']
      _ = ENNReal.ofReal |c⁻¹| * ∫⁻ t, G t := by
        rw [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_congr hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmap, ← mul_assoc,
    ← ENNReal.ofReal_mul hc.le, abs_of_pos (inv_pos.mpr hc), mul_inv_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]

/-- Change of scale `t = c s` for `ds/s`, valid for every function. -/
theorem ms4_setLIntegral_scaleMeasure_comp_mul_left {c : ℝ} (hc : 0 < c)
    (f : ℝ → ℝ≥0∞) (T : Set ℝ) :
    ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure = ∫⁻ t in T, f t ∂scaleMeasure := by
  set e := MeasurableEquiv.mulLeft₀ c hc.ne' with he_def
  have he : ⇑e = fun s => c * s := MeasurableEquiv.coe_mulLeft₀ hc.ne'
  symm
  calc
    ∫⁻ t in T, f t ∂scaleMeasure = ∫⁻ t in T, f t ∂(Measure.map e scaleMeasure) := by
      rw [he, ms4_scaleMeasure_map_mul_left hc]
    _ = ∫⁻ t, f t ∂((scaleMeasure.restrict (e ⁻¹' T)).map e) := by
      rw [e.measurableEmbedding.restrict_map]
    _ = ∫⁻ s, f (e s) ∂(scaleMeasure.restrict (e ⁻¹' T)) := lintegral_map_equiv f e
    _ = ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure := by
      rw [he]

/-- `∫_{r > b} g(2r) dr/r = ∫_{s > 2b} g(s) ds/s`. -/
theorem ms4_setLIntegral_Ioi_comp_two_mul (g : ℝ → ℝ≥0∞) (b : ℝ) :
    ∫⁻ r in Ioi b, g (2 * r) ∂scaleMeasure = ∫⁻ s in Ioi (2 * b), g s ∂scaleMeasure := by
  have hpre : (fun s : ℝ => 2 * s) ⁻¹' Ioi (2 * b) = Ioi b := by
    ext r
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [← ms4_setLIntegral_scaleMeasure_comp_mul_left (by norm_num : (0 : ℝ) < 2) g (Ioi (2 * b)),
    hpre]

/-- An all-scale integral is bounded once every tail `∫_{r > b}`, `b > 0`, is. -/
theorem ms4_lintegral_Ioi_zero_le_of_tails (g : ℝ → ℝ≥0∞) {X : ℝ≥0∞}
    (h : ∀ b : ℝ, 0 < b → ∫⁻ r in Ioi b, g r ∂scaleMeasure ≤ X) :
    ∫⁻ r in Ioi 0, g r ∂scaleMeasure ≤ X := by
  have hU : Ioi (0 : ℝ) = ⋃ m : ℕ, Ioi (1 / ((m : ℝ) + 1)) := by
    ext r
    simp only [mem_Ioi, mem_iUnion]
    constructor
    · intro hr
      exact exists_nat_one_div_lt hr
    · rintro ⟨m, hm⟩
      exact lt_trans (by positivity) hm
  have hmono : Monotone fun m : ℕ => Ioi (1 / ((m : ℝ) + 1)) := fun a b hab =>
    Ioi_subset_Ioi (one_div_le_one_div_of_le (by positivity) (by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith))
  rw [hU, setLIntegral_iUnion_of_directed _ hmono.directed_le]
  exact iSup_le fun m => h _ (by positivity)

/-! ## Energy comparisons for dominated measures -/

theorem ms4_allScaleEnergy_mono {n : ℕ} {μ ν : Measure (Space n)} (h : μ ≤ ν) (k : ℕ)
    (F : FamilyKind) (z : Space n) : allScaleEnergy μ k F z ≤ allScaleEnergy ν k F z :=
  lintegral_mono fun r => betaSq_mono_measure h k F z r

/-- `β²` of `c • μ` is at most `c β²(μ)` for a finite nonzero scalar (no availability needed). -/
theorem ms4_betaSq_smul_le {n : ℕ} (μ : Measure (Space n)) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ⊤) (k : ℕ) (F : FamilyKind) (z : Space n) (r : ℝ) :
    betaSq (c • μ) k F z r ≤ c * betaSq μ k F z r := by
  by_cases hr : 0 < r
  · rw [betaSq_of_pos _ _ _ _ hr, betaSq_of_pos _ _ _ _ hr]
    simp only [fit_smul]
    rw [← ENNReal.mul_iInf_of_ne hc0 hc]
    exact (mul_left_comm _ _ _).le
  · rw [betaSq_of_nonpos _ _ _ _ (not_lt.1 hr)]
    exact zero_le

theorem ms4_allScaleEnergy_smul_le {n : ℕ} (μ : Measure (Space n)) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ⊤) (k : ℕ) (F : FamilyKind) (z : Space n) :
    allScaleEnergy (c • μ) k F z ≤ c * allScaleEnergy μ k F z := by
  show ∫⁻ r in Ioi 0, betaSq (c • μ) k F z r ∂scaleMeasure ≤
    c * ∫⁻ r in Ioi 0, betaSq μ k F z r ∂scaleMeasure
  rw [← lintegral_const_mul' _ _ hc]
  exact lintegral_mono fun r => ms4_betaSq_smul_le μ hc0 hc k F z r

/-! ## Leaves 18 and 19 -/

/-- **`core_square_of_construction`**: all-scale square bound of the original source at
the core, with `C = 2^{n+3}`. -/
theorem core_square_of_construction_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T)
      (B : ℝ), T.Available n k → k < n + 2 → P.IsAdmissible → 0 < B → P.TailBound k T B →
      D.IsSourceConstruction P → ∀ L : ℝ, C ≤ L → ∀ z ∈ D.core P,
        allScaleEnergy P.ν k T.toFamilyKind z ≤ ENNReal.ofReal (L * B) := by
  refine ⟨2 ^ (n + 3), by positivity, ?_⟩
  intro k T P D B hT hk hP hB htail hD L hL z hz
  have hR := hP.R_pos
  have hz' : z ∈ D.coreLimit P := by
    rw [← ConstructionData.ms4_core_eq_coreLimit hD hR]
    exact hz
  have h2 : (2 : ℝ) ^ (k + 2) ≤ L :=
    (pow_le_pow_right₀ (by norm_num) (by omega : k + 2 ≤ n + 3)).trans hL
  have htails : ∀ b : ℝ, 0 < b →
      ∫⁻ r in Ioi b, betaSq P.ν k T.toFamilyKind z r ∂scaleMeasure ≤
        ENNReal.ofReal (2 ^ (k + 2) * B) := by
    intro b hb
    obtain ⟨m, hm⟩ := ((P.ms4_tendsto_scale T).eventually
      (gt_mem_nhds (show (0 : ℝ) < 2 * b by positivity))).exists
    obtain ⟨y, hy, hzy⟩ := Metric.mem_closure_iff.1 (mem_iInter.1 hz' (m + 1)) b hb
    have hyS : y ∈ P.S := D.ms4_kept_subset_S P (m + 1) hy
    have hfy : P.f y < P.scale T (m + 1) :=
      D.ms4_cutoff_lt_of_mem_kept P hD (Nat.le_add_left 1 m) hy
    have hpt : ∀ r ∈ Ioi b, betaSq P.ν k T.toFamilyKind z r ≤
        ENNReal.ofReal (2 ^ (k + 2)) * betaSq P.ν k T.toFamilyKind y (2 * r) := by
      intro r hr
      have hbr : b < r := hr
      have hr0 : 0 < r := hb.trans hbr
      have hsub : Metric.ball z r ⊆ Metric.ball y (2 * r) := by
        intro w hw
        rw [Metric.mem_ball] at hw ⊢
        have := dist_triangle w z y
        linarith
      have := betaSq_le_of_ball_subset P.ν k T.toFamilyKind hr0 (by linarith) hsub
      rwa [mul_div_cancel_right₀ (2 : ℝ) hr0.ne', ← ENNReal.ofReal_pow (show (0 : ℝ) ≤ 2 by norm_num)]
        at this
    calc ∫⁻ r in Ioi b, betaSq P.ν k T.toFamilyKind z r ∂scaleMeasure
        ≤ ∫⁻ r in Ioi b, ENNReal.ofReal (2 ^ (k + 2)) *
            betaSq P.ν k T.toFamilyKind y (2 * r) ∂scaleMeasure :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ = ENNReal.ofReal (2 ^ (k + 2)) *
            ∫⁻ r in Ioi b, betaSq P.ν k T.toFamilyKind y (2 * r) ∂scaleMeasure :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (2 ^ (k + 2)) *
            ∫⁻ s in Ioi (2 * b), betaSq P.ν k T.toFamilyKind y s ∂scaleMeasure := by
          rw [ms4_setLIntegral_Ioi_comp_two_mul (betaSq P.ν k T.toFamilyKind y) b]
      _ ≤ ENNReal.ofReal (2 ^ (k + 2)) * tailEnergy P.ν k T.toFamilyKind (P.f y) y :=
          mul_le_mul_right (lintegral_mono_set (Ioi_subset_Ioi (by linarith))) _
      _ ≤ ENNReal.ofReal (2 ^ (k + 2)) * ENNReal.ofReal B := mul_le_mul_right (htail y hyS) _
      _ = ENNReal.ofReal (2 ^ (k + 2) * B) := (ENNReal.ofReal_mul (by positivity)).symm
  calc allScaleEnergy P.ν k T.toFamilyKind z
      = ∫⁻ r in Ioi 0, betaSq P.ν k T.toFamilyKind z r ∂scaleMeasure := rfl
    _ ≤ ENNReal.ofReal (2 ^ (k + 2) * B) := ms4_lintegral_Ioi_zero_le_of_tails _ htails
    _ ≤ ENNReal.ofReal (L * B) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h2 hB.le)

/-- **`eta_square_of_construction`**: all-scale square bound of `η = H^k_P ⌞ C₀` at the
core, with `C = C_17 C_18`. -/
theorem eta_square_of_construction_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T)
      (B : ℝ), T.Available n k → k < n + 2 → P.IsAdmissible → 0 < B → P.TailBound k T B →
      D.IsSourceConstruction P → ∀ L : ℝ, C ≤ L → ∀ z ∈ D.core P,
        allScaleEnergy ((hausdorffP n k).restrict (D.core P)) k T.toFamilyKind z ≤
          ENNReal.ofReal (L * B / P.a) := by
  obtain ⟨C₁, hC₁, hdom⟩ := core_domination_of_construction_proof n
  obtain ⟨C₂, hC₂, hsq⟩ := core_square_of_construction_proof n
  refine ⟨C₁ * C₂, by positivity, ?_⟩
  intro k T P D B hT hk hP hB htail hD L hL z hz
  have ha := hP.a_pos
  have hle := hdom P D hT hk hP hD C₁ le_rfl
  have hsqz := hsq P D B hT hk hP hB htail hD C₂ le_rfl z hz
  have hc0 : ENNReal.ofReal (C₁ / P.a) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  calc allScaleEnergy ((hausdorffP n k).restrict (D.core P)) k T.toFamilyKind z
      ≤ allScaleEnergy (ENNReal.ofReal (C₁ / P.a) • P.ν) k T.toFamilyKind z :=
        ms4_allScaleEnergy_mono hle k _ z
    _ ≤ ENNReal.ofReal (C₁ / P.a) * allScaleEnergy P.ν k T.toFamilyKind z :=
        ms4_allScaleEnergy_smul_le P.ν hc0 ENNReal.ofReal_ne_top k _ z
    _ ≤ ENNReal.ofReal (C₁ / P.a) * ENNReal.ofReal (C₂ * B) := mul_le_mul_right hsqz _
    _ = ENNReal.ofReal (C₁ * C₂ * B / P.a) := by
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ C₁ / P.a by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (L * B / P.a) := by
        refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ ha.le)
        exact mul_le_mul_of_nonneg_right hL hB.le

end ParabolicRectifiability
