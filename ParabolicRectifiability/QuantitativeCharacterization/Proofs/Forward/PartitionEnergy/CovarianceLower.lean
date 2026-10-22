import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.TubeMass

/-! # Covariance lower bound with the horizontal small-error variant

Proof of `d1a_covarianceLower_proof : UpperRecenteringStatement → CovarianceLowerStatement`.

Constants (depending on `n, k, A` only; `C = d1atube_massConst n k`):
`δ = min (1/2) (A⁻¹/4 / (C A))`, `a₀ = min A⁻¹ (δ² A⁻¹/4 / n)`, `e₀ = δ² A⁻¹/4`.

* **Spatial rank zero** (vertical, `k = 2`): `ν(P(g,r)) = μ(P(g,r)) ≥ A⁻¹ r² ≥ a₀ r²` (lower ADR
  at the support point `g`, and `ν⌞P(g,r) = μ⌞P(g,r)`).
* **Positive rank `m = T.rank k`**: suppose `λ_m < a₀ r^{k+2}` for the source
  `S = SpatialSource.ofBall ν g r`. The top spectral plane `L` of rank `m - 1` has
  `I(L) = Σ_{i ≥ m-1} λ_i ≤ n λ_m < n a₀ r^{k+2}` (`topPlane_fittingError`, antitone eigenvalues),
  and `I(L) = ∫_{P(g,r)} ‖x - P_L x‖² dμ` since `S.measure = ν⌞P(g,r) = μ⌞P(g,r)`. Chebyshev
  leaves mass `≤ I(L) (δ r)^{-2}` outside the spatial `δ r`-tube of `L`. Horizontally, the full
  model `M` fitted on `P(g,2r)` with error `≤ e₀ r^{k+2}` (the genuine joint objective) gives
  `∫_{P(g,r)} |t - τ_M| dμ ≤ e₀ r^{k+2}`, and Chebyshev leaves mass `≤ e₀ δ^{-2} r^k` outside the
  time window `|t - τ_M| ≤ (δ r)²`. The rest of `P(g,r)` lies in the tube of the helper lemmas of
  `d1atube_gap_mass` (vertical: rank `k - 3`, `j = 1`; horizontal: rank `k - 1`, a point at `k = 1`,
  `j = 1`), of mass `≤ C A δ r^k`. Lower ADR then gives
  `A⁻¹ ≤ C A δ + (n a₀ + e₀) δ^{-2} ≤ (3/4) A⁻¹`, a contradiction.

The conclusion is the continuation hypothesis `hcont` of the base
`Measure.Neck.PlaneTime.ms3_core_comparison`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

/-! ## Spectral tail -/

/-- The top spectral plane of rank `m - 1` has fitting error at most `n λ_m`
(`I_{m-1} = Σ_{i ≥ m-1} λ_i`, each term at most `λ_m`). -/
theorem d1acov_topPlane_fittingError_le {n : ℕ} (S : SpatialSource n) {m : ℕ} (hm1 : 1 ≤ m)
    (hmn : m ≤ n) :
    S.fittingError (S.topPlane (m - 1) (by omega)) ≤ (n : ℝ) * S.rankEigenvalue m := by
  rw [S.topPlane_fittingError]
  have heig : S.rankEigenvalue m = S.eigenvalue ⟨m - 1, by omega⟩ := by
    unfold SpatialSource.rankEigenvalue
    split_ifs with h
    · rfl
    · exact absurd ⟨hm1, hmn⟩ h
  rw [heig]
  calc S.spectralTail (m - 1) ≤ ∑ _i : Fin n, S.eigenvalue ⟨m - 1, by omega⟩ := by
        unfold SpatialSource.spectralTail
        exact Finset.sum_le_sum fun i _ => by
          split_ifs with h
          · exact S.eigenvalue_antitone (Fin.le_iff_val_le_val.2 h)
          · exact S.eigenvalue_nonneg _
    _ = (n : ℝ) * S.eigenvalue ⟨m - 1, by omega⟩ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## The two Chebyshev estimates -/

/-- **Spatial Chebyshev.** For a finite `ν` agreeing with `μ` on `P(g, r)`, the `μ`-mass of the
points of `P(g, r)` at spatial distance `≥ s` from a plane `L` is at most `s^{-2}` times the
covariance fitting error of `L` for the source `ν⌞P(g, r)`. -/
theorem d1acov_residual_tail {n l : ℕ} (μ ν : Measure (Space n)) [IsFiniteMeasure ν]
    (g : Space n) {r : ℝ} (hr : 0 < r)
    (hν : ν.restrict (Metric.ball g r) = μ.restrict (Metric.ball g r))
    (L : AffineSpatialPlane n l) {s : ℝ} (hs : 0 ≤ s) :
    ENNReal.ofReal (s ^ 2) *
        μ ({z | s ≤ ‖z.1 - L.projection z.1‖} ∩ Metric.ball g r) ≤
      ENNReal.ofReal ((SpatialSource.ofBall ν g r hr).fittingError L) := by
  have hT := mul_meas_ge_le_lintegral₀ (μ := μ.restrict (Metric.ball g r))
    (ChargeCollapse.gm2_measurable_residual L).aemeasurable (ENNReal.ofReal (s ^ 2))
  rw [Measure.restrict_apply' measurableSet_ball] at hT
  rw [← ChargeCollapse.gm2_lintegral_residual ν g hr L, hν]
  refine le_trans ?_ hT
  apply mul_le_mul_right
  apply measure_mono
  intro z hz
  refine ⟨?_, hz.2⟩
  have h : s ≤ ‖z.1 - L.projection z.1‖ := hz.1
  show ENNReal.ofReal (s ^ 2) ≤ ENNReal.ofReal (‖z.1 - L.projection z.1‖ ^ 2)
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hs h 2)

/-- **Time Chebyshev** (horizontal joint objective). The `μ`-mass of the points of `P(g, r)`
outside the time window `|t - τ_M| ≤ s` of a horizontal model `M` is at most `s^{-1}` times the
fit of `M` on `P(g, 2r)`. -/
theorem d1acov_time_tail {n k : ℕ} (μ : Measure (Space n)) (M : HorizontalModel n k)
    (g : Space n) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    ENNReal.ofReal s * μ ({z | |z.2.val - M.time| ≤ s}ᶜ ∩ Metric.ball g r) ≤
      fit (T := .horizontal) μ M g (2 * r) := by
  have hm : Measurable (modelCost (T := .horizontal) M) :=
    Metric.continuous_infEDist.measurable.pow_const 2
  have hT := mul_meas_ge_le_lintegral₀ (μ := μ.restrict (Metric.ball g r)) hm.aemeasurable
    (ENNReal.ofReal s)
  rw [Measure.restrict_apply' measurableSet_ball] at hT
  unfold fit
  refine le_trans ?_ (hT.trans (lintegral_mono_set (Metric.ball_subset_ball (by linarith))))
  apply mul_le_mul_right
  apply measure_mono
  intro z hz
  refine ⟨?_, hz.2⟩
  have h : ¬ (|z.2.val - M.time| ≤ s) := hz.1
  show ENNReal.ofReal s ≤ modelCost (T := .horizontal) M z
  exact (ENNReal.ofReal_le_ofReal (not_le.1 h).le).trans
    (ChargeCollapse.gm2_time_le_cost_horizontal M z)

/-! ## Arithmetic and the generic contradiction -/

/-- `(δr)² C A δ r^k + F + e r^{k+2} < (δr)² A⁻¹ r^k` when `C A δ ≤ A⁻¹/4`,
`F ≤ (δ² A⁻¹/4) r^{k+2}` and `e ≤ δ² A⁻¹/4`. -/
theorem d1acov_arith {k : ℕ} {A δ r C F e : ℝ} (hA0 : 0 < A) (hδ : 0 < δ) (hr : 0 < r)
    (hCδ : C * A * δ ≤ A⁻¹ / 4) (hF : F ≤ δ ^ 2 * A⁻¹ / 4 * r ^ (k + 2))
    (he : e ≤ δ ^ 2 * A⁻¹ / 4) :
    (δ * r) ^ 2 * (C * A * δ ^ 1 * r ^ k) + F + e * r ^ (k + 2) <
      (δ * r) ^ 2 * (A⁻¹ * r ^ k) := by
  have hP : 0 < r ^ (k + 2) := pow_pos hr _
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = δ ^ 2 * A⁻¹ / 4 * r ^ (k + 2) := ⟨_, rfl⟩
  have hq0 : 0 < q := by
    rw [hq]
    exact mul_pos (div_pos (mul_pos (pow_pos hδ 2) (inv_pos.2 hA0)) (by norm_num)) hP
  have h1 : (δ * r) ^ 2 * (C * A * δ ^ 1 * r ^ k) ≤ q := by
    rw [hq]
    calc (δ * r) ^ 2 * (C * A * δ ^ 1 * r ^ k) = (δ ^ 2 * r ^ (k + 2)) * (C * A * δ) := by
          ring
      _ ≤ (δ ^ 2 * r ^ (k + 2)) * (A⁻¹ / 4) :=
          mul_le_mul_of_nonneg_left hCδ (mul_nonneg (sq_nonneg δ) hP.le)
      _ = δ ^ 2 * A⁻¹ / 4 * r ^ (k + 2) := by ring
  have h2 : (δ * r) ^ 2 * (A⁻¹ * r ^ k) = 4 * q := by
    rw [hq]
    ring
  have h3 : e * r ^ (k + 2) ≤ q := by
    rw [hq]
    exact mul_le_mul_of_nonneg_right he hP.le
  rw [← hq] at hF
  rw [h2]
  linarith

/-- **Generic contradiction.** Lower ADR on `P(g, r)`, the spatial Chebyshev bound outside the
`δ r`-tube of `L`, a Chebyshev bound outside a set `W` (the horizontal time window; `W = univ`
vertically), and the tube mass of the rest are incompatible with the choice of constants. -/
theorem d1acov_absurd {n k l : ℕ} {μ : Measure (Space n)} {A : ℝ} (hA0 : 0 < A)
    {g : Space n} {r : ℝ} (hr : 0 < r)
    (hlow : ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball g r))
    {C δ : ℝ} (hδ : 0 < δ) (hC0 : 0 ≤ C) (hCδ : C * A * δ ≤ A⁻¹ / 4)
    (L : AffineSpatialPlane n l) {F : ℝ} (hF0 : 0 ≤ F)
    (hres : ENNReal.ofReal ((δ * r) ^ 2) *
        μ ({z | δ * r ≤ ‖z.1 - L.projection z.1‖} ∩ Metric.ball g r) ≤ ENNReal.ofReal F)
    (hF : F ≤ δ ^ 2 * A⁻¹ / 4 * r ^ (k + 2))
    (W : Set (Space n)) (e : ℝ) (he0 : 0 ≤ e) (he : e ≤ δ ^ 2 * A⁻¹ / 4)
    (hW : ENNReal.ofReal ((δ * r) ^ 2) * μ (Wᶜ ∩ Metric.ball g r) ≤
      ENNReal.ofReal (e * r ^ (k + 2)))
    (htube : μ (Metric.ball g r ∩ {z | ‖z.1 - L.projection z.1‖ < δ * r ∧ z ∈ W}) ≤
      ENNReal.ofReal (C * A * δ ^ 1 * r ^ k)) : False := by
  have hcover : μ (Metric.ball g r) ≤
      μ (Metric.ball g r ∩ {z | ‖z.1 - L.projection z.1‖ < δ * r ∧ z ∈ W}) +
        μ ({z | δ * r ≤ ‖z.1 - L.projection z.1‖} ∩ Metric.ball g r) +
          μ (Wᶜ ∩ Metric.ball g r) := by
    refine (measure_mono ?_).trans ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl))
    intro z hz
    by_cases h1 : ‖z.1 - L.projection z.1‖ < δ * r
    · by_cases h2 : z ∈ W
      · exact Or.inl (Or.inl ⟨hz, h1, h2⟩)
      · exact Or.inr ⟨h2, hz⟩
    · exact Or.inl (Or.inr ⟨not_lt.1 h1, hz⟩)
  have hs : 0 ≤ (δ * r) ^ 2 := sq_nonneg _
  have hP : 0 < r ^ (k + 2) := pow_pos hr _
  have hxG : 0 ≤ C * A * δ ^ 1 * r ^ k :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 hA0.le) (pow_nonneg hδ.le _)) (pow_nonneg hr.le _)
  have hx₂ : 0 ≤ e * r ^ (k + 2) := mul_nonneg he0 hP.le
  have hY : 0 ≤ (δ * r) ^ 2 * (C * A * δ ^ 1 * r ^ k) + F + e * r ^ (k + 2) :=
    add_nonneg (add_nonneg (mul_nonneg hs hxG) hF0) hx₂
  have hmain : ENNReal.ofReal ((δ * r) ^ 2 * (A⁻¹ * r ^ k)) ≤
      ENNReal.ofReal ((δ * r) ^ 2 * (C * A * δ ^ 1 * r ^ k) + F + e * r ^ (k + 2)) := by
    calc ENNReal.ofReal ((δ * r) ^ 2 * (A⁻¹ * r ^ k))
        = ENNReal.ofReal ((δ * r) ^ 2) * ENNReal.ofReal (A⁻¹ * r ^ k) :=
          ENNReal.ofReal_mul hs
      _ ≤ ENNReal.ofReal ((δ * r) ^ 2) *
            (μ (Metric.ball g r ∩ {z | ‖z.1 - L.projection z.1‖ < δ * r ∧ z ∈ W}) +
              μ ({z | δ * r ≤ ‖z.1 - L.projection z.1‖} ∩ Metric.ball g r) +
                μ (Wᶜ ∩ Metric.ball g r)) :=
          mul_le_mul_right (hlow.trans hcover) _
      _ = ENNReal.ofReal ((δ * r) ^ 2) *
              μ (Metric.ball g r ∩ {z | ‖z.1 - L.projection z.1‖ < δ * r ∧ z ∈ W}) +
            ENNReal.ofReal ((δ * r) ^ 2) *
              μ ({z | δ * r ≤ ‖z.1 - L.projection z.1‖} ∩ Metric.ball g r) +
            ENNReal.ofReal ((δ * r) ^ 2) * μ (Wᶜ ∩ Metric.ball g r) := by
          rw [mul_add, mul_add]
      _ ≤ ENNReal.ofReal ((δ * r) ^ 2) * ENNReal.ofReal (C * A * δ ^ 1 * r ^ k) +
            ENNReal.ofReal F + ENNReal.ofReal (e * r ^ (k + 2)) :=
          add_le_add (add_le_add (mul_le_mul_right htube _) hres) hW
      _ = ENNReal.ofReal ((δ * r) ^ 2 * (C * A * δ ^ 1 * r ^ k) + F + e * r ^ (k + 2)) := by
          rw [← ENNReal.ofReal_mul hs, ← ENNReal.ofReal_add (mul_nonneg hs hxG) hF0,
            ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hs hxG) hF0) hx₂]
  have h := (ENNReal.ofReal_le_ofReal_iff hY).1 hmain
  have h' := d1acov_arith (k := k) hA0 hδ hr hCδ hF he
  exact (not_le.2 h') h

/-! ## The two positive-rank cases -/

/-- **Vertical positive rank** (`m = k - 2 ≥ 1`): the plane `L` of rank `l = k - 3` with small
fitting error contradicts lower ADR (tube mass with `l + 2 + 1 = k`). -/
theorem d1acov_vertical_absurd {n k l : ℕ} (hUR : UpperRecenteringStatement)
    {μ : Measure (Space n)} {A : ℝ} (hA0 : 0 < A) {a : Space n} {ρ : ℝ}
    (hADR : LocalADR μ k A a ρ) {g : Space n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball g (4 * r) ⊆ Metric.ball a ρ) (h4 : 4 * r ≤ ρ)
    (hlow : ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball g r))
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hCδ : d1atube_massConst n k * A * δ ≤ A⁻¹ / 4)
    (L : AffineSpatialPlane n l) (hl : l + 2 + 1 = k) {F : ℝ} (hF0 : 0 ≤ F)
    (hres : ENNReal.ofReal ((δ * r) ^ 2) *
        μ ({z | δ * r ≤ ‖z.1 - L.projection z.1‖} ∩ Metric.ball g r) ≤ ENNReal.ofReal F)
    (hF : F ≤ δ ^ 2 * A⁻¹ / 4 * r ^ (k + 2)) : False := by
  refine d1acov_absurd hA0 hr hlow hδ (d1atube_massConst_pos n k).le hCδ L hF0 hres hF
    Set.univ 0 le_rfl
    (div_nonneg (mul_nonneg (sq_nonneg δ) (inv_pos.2 hA0).le) (by norm_num)) (by simp) ?_
  exact d1atube_mass_vertical hUR hA0.le hADR hr hball h4 hδ hδ2 L hl _
    Set.inter_subset_left (fun z hz => hz.2.1)

/-- **Horizontal positive rank** (`m = k`): the plane `L` of rank `l = k - 1` (a point at
`k = 1`) with small fitting error, and the time window of the horizontal model `M` with small
fit on `P(g, 2r)`, contradict lower ADR (tube mass with `l + 1 = k`). -/
theorem d1acov_horizontal_absurd {n k l : ℕ} (hUR : UpperRecenteringStatement)
    {μ : Measure (Space n)} {A : ℝ} (hA0 : 0 < A) {a : Space n} {ρ : ℝ}
    (hADR : LocalADR μ k A a ρ) {g : Space n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball g (4 * r) ⊆ Metric.ball a ρ) (h4 : 4 * r ≤ ρ)
    (hlow : ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball g r))
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hCδ : d1atube_massConst n k * A * δ ≤ A⁻¹ / 4)
    (L : AffineSpatialPlane n l) (hl : l + 1 = k) {F : ℝ} (hF0 : 0 ≤ F)
    (hres : ENNReal.ofReal ((δ * r) ^ 2) *
        μ ({z | δ * r ≤ ‖z.1 - L.projection z.1‖} ∩ Metric.ball g r) ≤ ENNReal.ofReal F)
    (hF : F ≤ δ ^ 2 * A⁻¹ / 4 * r ^ (k + 2))
    (M : Models n k .horizontal) (e : ℝ) (he0 : 0 ≤ e) (he : e ≤ δ ^ 2 * A⁻¹ / 4)
    (hM : fit μ M g (2 * r) ≤ ENNReal.ofReal (e * r ^ (k + 2))) : False := by
  let M' : HorizontalModel n k := M
  refine d1acov_absurd hA0 hr hlow hδ (d1atube_massConst_pos n k).le hCδ L hF0 hres hF
    {z | |z.2.val - M'.time| ≤ (δ * r) ^ 2} e he0 he
    ((d1acov_time_tail μ M' g hr ((δ * r) ^ 2)).trans hM) ?_
  exact d1atube_mass_horizontal hUR hA0.le hADR hr hball h4 hδ hδ2 L M'.time hl _
    Set.inter_subset_left (fun z hz => hz.2)

/-! ## The statement -/

/-- **Covariance lower bound**, horizontal small-error variant included:
`UpperRecenteringStatement → CovarianceLowerStatement`. -/
theorem d1a_covarianceLower_proof : UpperRecenteringStatement → CovarianceLowerStatement := by
  intro hUR n hn k hk hkn A hA
  have hA0 : 0 < A := by linarith
  have hAi : 0 < A⁻¹ := inv_pos.2 hA0
  have hC := d1atube_massConst_pos n k
  have hCA : 0 < d1atube_massConst n k * A := mul_pos hC hA0
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (1 / 2) (A⁻¹ / 4 / (d1atube_massConst n k * A)) :=
    ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (by norm_num) (div_pos (div_pos hAi (by norm_num)) hCA)
  have hδ2 : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_left _ _
  have hCδ : d1atube_massConst n k * A * δ ≤ A⁻¹ / 4 := by
    calc d1atube_massConst n k * A * δ
        ≤ d1atube_massConst n k * A * (A⁻¹ / 4 / (d1atube_massConst n k * A)) :=
          mul_le_mul_of_nonneg_left (by rw [hδdef]; exact min_le_right _ _) hCA.le
      _ = A⁻¹ / 4 := mul_div_cancel₀ _ hCA.ne'
  obtain ⟨a₀, ha₀def⟩ : ∃ a₀ : ℝ, a₀ = min A⁻¹ (δ ^ 2 * A⁻¹ / 4 / n) := ⟨_, rfl⟩
  have ha₀pos : 0 < a₀ := by
    rw [ha₀def]
    exact lt_min hAi (div_pos (div_pos (mul_pos (pow_pos hδpos 2) hAi) (by norm_num)) hnpos)
  have ha₀A : a₀ ≤ A⁻¹ := by rw [ha₀def]; exact min_le_left _ _
  have ha₀n : (n : ℝ) * a₀ ≤ δ ^ 2 * A⁻¹ / 4 := by
    calc (n : ℝ) * a₀ ≤ (n : ℝ) * (δ ^ 2 * A⁻¹ / 4 / n) :=
          mul_le_mul_of_nonneg_left (by rw [ha₀def]; exact min_le_right _ _) hnpos.le
      _ = δ ^ 2 * A⁻¹ / 4 := mul_div_cancel₀ _ hnpos.ne'
  obtain ⟨e₀, he₀def⟩ : ∃ e₀ : ℝ, e₀ = δ ^ 2 * A⁻¹ / 4 := ⟨_, rfl⟩
  have he₀pos : 0 < e₀ := by
    rw [he₀def]
    exact div_pos (mul_pos (pow_pos hδpos 2) hAi) (by norm_num)
  refine ⟨a₀, ha₀pos, e₀, he₀pos, ?_⟩
  intro T hT μ a ρ hADR g hg r hr hball h4 hhor ν hνfin hν
  have hgmem : g ∈ μ.support ∩ Metric.ball a ρ :=
    ⟨hg, hball (Metric.mem_ball_self (by linarith))⟩
  have hlow : ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball g r) :=
    (hADR g hgmem r hr (by linarith)).1
  by_cases hm0 : T.rank k = 0
  · -- spatial rank zero: the mass alternative
    right
    refine ⟨hm0, ?_⟩
    have hk2 : k = 2 := by
      cases T <;> simp only [NeckType.rank, NeckType.Available] at hT hm0 <;> omega
    have hνB : ν (Metric.ball g r) = μ (Metric.ball g r) := by
      have h := congrArg (fun m : Measure (Space n) => m Set.univ) hν
      simp only [Measure.restrict_apply_univ] at h
      exact h
    rw [hνB]
    subst hk2
    exact le_trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right ha₀A (pow_nonneg hr.le 2))) hlow
  · -- positive rank: the eigenvalue alternative, by contradiction
    left
    have hm1 : 1 ≤ T.rank k := by omega
    have hmn : T.rank k ≤ n := by
      cases T <;> simp only [NeckType.rank, NeckType.Available] at hT ⊢ <;> omega
    refine ⟨by omega, hr, not_lt.1 fun hlt => ?_⟩
    have hfit : (SpatialSource.ofBall ν g r hr).fittingError
        ((SpatialSource.ofBall ν g r hr).topPlane (T.rank k - 1) (by omega)) ≤
          δ ^ 2 * A⁻¹ / 4 * r ^ (k + 2) := by
      calc _ ≤ (n : ℝ) * (SpatialSource.ofBall ν g r hr).rankEigenvalue (T.rank k) :=
            d1acov_topPlane_fittingError_le _ hm1 hmn
        _ ≤ (n : ℝ) * (a₀ * r ^ (k + 2)) := mul_le_mul_of_nonneg_left hlt.le hnpos.le
        _ = (n : ℝ) * a₀ * r ^ (k + 2) := by ring
        _ ≤ δ ^ 2 * A⁻¹ / 4 * r ^ (k + 2) :=
            mul_le_mul_of_nonneg_right ha₀n (pow_pos hr _).le
    obtain ⟨L, hL⟩ : ∃ L : AffineSpatialPlane n (T.rank k - 1),
        (SpatialSource.ofBall ν g r hr).fittingError L ≤ δ ^ 2 * A⁻¹ / 4 * r ^ (k + 2) :=
      ⟨_, hfit⟩
    have hres := d1acov_residual_tail μ ν g hr hν L (mul_pos hδpos hr).le
    have hF0 := (SpatialSource.ofBall ν g r hr).fittingError_nonneg L
    cases T with
    | horizontal =>
      obtain ⟨M, hM⟩ := hhor rfl
      exact d1acov_horizontal_absurd hUR hA0 hADR hr hball h4 hlow hδpos hδ2 hCδ L
        (by simp only [NeckType.rank] at hm1 ⊢; omega) hF0 hres hL M e₀ he₀pos.le he₀def.le hM
    | vertical =>
      exact d1acov_vertical_absurd hUR hA0 hADR hr hball h4 hlow hδpos hδ2 hCδ L
        (by simp only [NeckType.rank] at hm1 ⊢; omega) hF0 hres hL

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
