import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.LastWitness
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy
import ParabolicRectifiability.Measure.Neck.PlaneTime.PlaneComparison

/-! # The per-occurrence last-witness bound

Proof of `d1d_occurrenceBound_proof`, with type
`PartitionEnergy.PlaneComparisonStatement → OccurrenceBoundStatement`.

Route: each local
minimizer `M` (of the original-source fit on `P(g, 40 r_i)`) is compared separately with the
model `Π_Q` of the member `Q` on the occurrence's **own** noncollapsed source `P(g, 5 r_i)`; no
comparison source is centred at the last witness. Constants: `Λ₀ = 1`, `B = 1000`,
`C₁ = 2·206²·C_pc·(Λ·10^{12}/5)^{k+2}`, `b₀ = e₀ (5/(Λ·10^{12}))^{k+2}`, where `C_pc, e₀` are
the constants of the hypothesis.

Part (a) (forest localization, coefficient bound and cancellation, spatial-fit domination):
`d1docc_rootCell_subset`, `d1docc_dist_lt_of_inForest`, `d1docc_rootScale_le`,
`d1docc_source_subset`, `d1docc_modelCoeff_le`, `d1docc_fit_eq_mul_modelCoeff`,
`d1docc_coeffFit_le`, `d1docc_coeffFit_ne_top`, `d1docc_fit_le_coeffFit`,
`d1docc_spatialFit_le_fit`, `d1docc_smallError`.
Part (b) (comparison application and anchor change): `d1docc_comparison_constant`,
`d1docc_change_sq`, `d1docc_bound_of_comparison`, and the final statement `d1d_occurrenceBound_proof`.

Every fit is of the original `μ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Witness

variable {n : ℕ}

/-! ## Part (a): scales and forest localization -/

/-- Every partition side `ℓ_j = 10^{-j} ℓ₀` is positive. -/
theorem d1docc_scale_pos {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀) (j : ℕ) :
    0 < P.scale j := by
  show 0 < ℓ₀ / 10 ^ j
  exact div_pos P.scale_pos (pow_pos (by norm_num) j)

/-- The prescribed scales `r_i = 10^{-i} 48 ℓ_*` of a good region are positive. -/
theorem d1docc_radius_pos {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b) (i : ℕ) :
    0 < coherentScale (48 * 𝒢.rootScale) i := by
  show 0 < 48 * P.scale 𝒢.root.1 / 10 ^ i
  exact div_pos (mul_pos (by norm_num) (d1docc_scale_pos P 𝒢.root.1)) (pow_pos (by norm_num) i)

/-- **The root cell lies in the partitioned set**: `S = Q_* ⊆ E`; for `E = supp μ` every
point of `S` is a support point. -/
theorem d1docc_rootCell_subset {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b) :
    𝒢.rootCell ⊆ E := by
  intro x hx
  rw [← P.cell_cover 𝒢.root.1]
  exact Set.mem_biUnion (x := 𝒢.root.2) 𝒢.root_isCell hx

/-- **Forest localization**: if the root of `𝒢` is in the root forest of `P(a, R)`
for a partition from `ℓ₀ = R`, then every `g ∈ S` has `d_P(g, a) < 5 R`
(`S ⊆ cell 0 z₀ ⊆ P(z₀, 2R)` and the top cell meets `P(a, R)`). -/
theorem d1docc_dist_lt_of_inForest {E : Set (Space n)} {R : ℝ} {P : DirectPartition E R}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b) {a : Space n}
    (hF : P.InForest a R 𝒢.root) {g : Space n} (hg : g ∈ 𝒢.rootCell) : dist g a < 5 * R := by
  obtain ⟨z₀, hz₀, ⟨x, hx0, hxa⟩, hbelow⟩ := hF
  have hball := P.cell_subset_ball 0 z₀ hz₀
  have h0 : coherentScale R 0 = R := by simp [coherentScale]
  rw [h0] at hball
  have hgz : dist g z₀ < 2 * R := Metric.mem_ball.1 (hball (hbelow.2.2 hg))
  have hxz : dist x z₀ < 2 * R := Metric.mem_ball.1 (hball hx0)
  have hxa' : dist x a < R := Metric.mem_ball.1 hxa
  have htri := dist_triangle4 g z₀ x a
  rw [dist_comm z₀ x] at htri
  linarith

/-- The root side is at most the top scale: `ℓ_* ≤ R`. -/
theorem d1docc_rootScale_le {E : Set (Space n)} {R : ℝ} {P : DirectPartition E R}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b) :
    𝒢.rootScale ≤ R := by
  show R / 10 ^ 𝒢.root.1 ≤ R
  exact div_le_self P.scale_pos.le (one_le_pow₀ (by norm_num))

/-- **The ADR buffer of the comparison source** (`B = 1000` works at `i = 0`): for
`g ∈ S` in the root forest of `P(a, R)` and every level `i`, with `r = 5 r_i`,
`P(g, 4 r) ⊆ P(a, 1000 R)` and `4 r ≤ 1000 R` (`20 r_i ≤ 960 ℓ_* ≤ 960 R`). -/
theorem d1docc_source_subset {E : Set (Space n)} {R : ℝ} {P : DirectPartition E R}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b) {a : Space n}
    (hF : P.InForest a R 𝒢.root) {g : Space n} (hg : g ∈ 𝒢.rootCell) (i : ℕ) :
    Metric.ball g (4 * (5 * coherentScale (48 * 𝒢.rootScale) i)) ⊆ Metric.ball a (1000 * R) ∧
      4 * (5 * coherentScale (48 * 𝒢.rootScale) i) ≤ 1000 * R := by
  have hR : 0 < R := P.scale_pos
  have hga := d1docc_dist_lt_of_inForest 𝒢 hF hg
  have hroot := d1docc_rootScale_le 𝒢
  have hrs : 0 ≤ 𝒢.rootScale := (d1docc_scale_pos P 𝒢.root.1).le
  have hri : coherentScale (48 * 𝒢.rootScale) i ≤ 48 * R := by
    calc coherentScale (48 * 𝒢.rootScale) i = 48 * 𝒢.rootScale / 10 ^ i := rfl
      _ ≤ 48 * 𝒢.rootScale := div_le_self (mul_nonneg (by norm_num) hrs) (one_le_pow₀ (by norm_num))
      _ ≤ 48 * R := by linarith
  refine ⟨fun y hy => ?_, by linarith⟩
  rw [Metric.mem_ball] at hy ⊢
  have htri := dist_triangle y g a
  linarith

/-! ## Part (a): the coefficient bound and the cancellation -/

/-- **The coefficient of a member is paid by its own budget term**: `a_Q ≤ b`
(`Q` itself is a term of its chain budget; `ENNReal.le_tsum`). -/
theorem d1docc_modelCoeff_le {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b)
    {Q : ℕ × Space n} (hQ : Q ∈ 𝒢.members) :
    P.modelCoeff μ Λ (𝒢.model Q) Q ≤ ENNReal.ofReal b := by
  have hself : Q ∈ 𝒢.members ∧ P.IsBelow Q Q :=
    ⟨hQ, (𝒢.below_root Q hQ).1, le_rfl, Set.Subset.rfl⟩
  exact (ENNReal.le_tsum (f := fun Q' : {Q' : ℕ × Space n // Q' ∈ 𝒢.members ∧ P.IsBelow Q Q'} =>
    P.modelCoeff μ Λ (𝒢.model Q'.1) Q'.1) ⟨Q, hself⟩).trans (𝒢.budget Q hQ)

/-- **Coefficient cancellation**: for `L = Λ ℓ_Q > 0` and any model,
`∫_{P(z_Q, L)} d_P(·, M)² dμ = L^{k+2} · (L^{-k-2} ∫_{P(z_Q, L)} d_P(·, M)² dμ)`. -/
theorem d1docc_fit_eq_mul_modelCoeff {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (μ : Measure (Space n)) {k : ℕ} {T : FamilyKind} {Λ : ℝ} (L : Models n k T)
    (Q : ℕ × Space n) (hpos : 0 < Λ * P.scale Q.1) :
    fit μ L Q.2 (Λ * P.scale Q.1) =
      ENNReal.ofReal ((Λ * P.scale Q.1) ^ (k + 2)) * P.modelCoeff μ Λ L Q := by
  rw [ENNReal.ofReal_pow hpos.le, DirectPartition.modelCoeff, ← mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top, one_pow,
    one_mul]

/-- **The member's coefficient fit is bounded by the budget**:
`I_Q = ∫_{P(z_Q, Λ ℓ_Q)} d_P(·, Π_Q)² dμ ≤ (Λ ℓ_Q)^{k+2} b`. -/
theorem d1docc_coeffFit_le {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b) (hΛ : 0 < Λ)
    {Q : ℕ × Space n} (hQ : Q ∈ 𝒢.members) :
    fit μ (𝒢.model Q) Q.2 (Λ * P.scale Q.1) ≤
      ENNReal.ofReal ((Λ * P.scale Q.1) ^ (k + 2) * b) := by
  have hpos : 0 < Λ * P.scale Q.1 := mul_pos hΛ (d1docc_scale_pos P Q.1)
  rw [d1docc_fit_eq_mul_modelCoeff P μ (𝒢.model Q) Q hpos,
    ENNReal.ofReal_mul (pow_nonneg hpos.le _)]
  exact mul_le_mul_of_nonneg_left (d1docc_modelCoeff_le 𝒢 hQ) zero_le

/-- **The member's coefficient fit is finite.** -/
theorem d1docc_coeffFit_ne_top {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b) (hΛ : 0 < Λ)
    {Q : ℕ × Space n} (hQ : Q ∈ 𝒢.members) :
    fit μ (𝒢.model Q) Q.2 (Λ * P.scale Q.1) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (d1docc_coeffFit_le 𝒢 hΛ hQ)

/-! ## Part (a): spatial-fit domination -/

/-- **Minimality and ball inclusion** (step (2)): if `M` minimizes the fit on `P(g, ρ)` and
`P(g, ρ) ⊆ P(z_Q, Λ ℓ_Q)`, then `fit(M; g, ρ) ≤ fit(L; z_Q, Λ ℓ_Q)` for every model `L`. -/
theorem d1docc_fit_le_coeffFit {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {k : ℕ} {T : FamilyKind} {Λ : ℝ} {M : Models n k T} {g : Space n}
    {ρ : ℝ} (Q : ℕ × Space n) (L : Models n k T)
    (hmin : ∀ M' : Models n k T, fit μ M g ρ ≤ fit μ M' g ρ)
    (hball : Metric.ball g ρ ⊆ Metric.ball Q.2 (Λ * P.scale Q.1)) :
    fit μ M g ρ ≤ fit μ L Q.2 (Λ * P.scale Q.1) := by
  refine (hmin L).trans ?_
  unfold fit
  exact lintegral_mono_set hball

/-- **Spatial fitting integrals are dominated by model fits** (step (4)): for a model `M` of an
available type and any ball, `∫_{P(z,ρ)} |x - π_{L_M} x|² dμ ≤ ∫_{P(z,ρ)} d_P(·, M)² dμ`
(`ms3_ofReal_spatial_sq_le` with `NeckSelection.lowerModelSet_modelPlane`). -/
theorem d1docc_spatialFit_le_fit (μ : Measure (Space n)) {k : ℕ} (T : NeckType)
    (M : Models n k T.toFamilyKind) (z : Space n) (ρ : ℝ) :
    spatialFittingIntegral (μ.restrict (Metric.ball z ρ)) (NeckSelection.modelPlane T M) ≤
      fit μ M z ρ := by
  unfold spatialFittingIntegral fit
  refine lintegral_mono fun w => ?_
  have h := ms3_ofReal_spatial_sq_le T (NeckSelection.modelPlane T M)
    (NeckSelection.modelTime T M) w
  rw [NeckSelection.lowerModelSet_modelPlane] at h
  exact h

/-- **The horizontal small-error test** (step (3)): if `ℓ_Q ≤ 10^{12} r`,
`b ≤ e₀ (5/(Λ 10^{12}))^{k+2}` and `fit(M; g, 40 r) ≤ (Λ ℓ_Q)^{k+2} b`, then
`fit(M; g, 2·5r) ≤ e₀ (5 r)^{k+2}`. -/
theorem d1docc_smallError {k : ℕ} {T : FamilyKind} {μ : Measure (Space n)} {M : Models n k T}
    {g : Space n} {e₀ Λ r ℓ b : ℝ} (hΛ : 0 < Λ) (hr : 0 < r) (hℓ : 0 < ℓ)
    (hℓr : ℓ ≤ 10 ^ 12 * r) (hb : 0 ≤ b) (hb₀ : b ≤ e₀ * (5 / (Λ * 10 ^ 12)) ^ (k + 2))
    (hfit : fit μ M g (40 * r) ≤ ENNReal.ofReal ((Λ * ℓ) ^ (k + 2) * b)) :
    fit μ M g (2 * (5 * r)) ≤ ENNReal.ofReal (e₀ * (5 * r) ^ (k + 2)) := by
  have hmono : fit μ M g (2 * (5 * r)) ≤ fit μ M g (40 * r) := by
    unfold fit
    exact lintegral_mono_set (Metric.ball_subset_ball (by linarith))
  refine hmono.trans (hfit.trans (ENNReal.ofReal_le_ofReal ?_))
  have hc : Λ * 10 ^ 12 ≠ 0 := (mul_pos hΛ (by norm_num)).ne'
  have hΛℓ : Λ * ℓ ≤ Λ * 10 ^ 12 * r := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hℓr hΛ.le
  have h1 : (Λ * ℓ) ^ (k + 2) ≤ (Λ * 10 ^ 12 * r) ^ (k + 2) :=
    pow_le_pow_left₀ (mul_pos hΛ hℓ).le hΛℓ _
  have h2 : Λ * 10 ^ 12 * r * (5 / (Λ * 10 ^ 12)) = 5 * r := by
    rw [mul_div_assoc', div_eq_iff hc]
    ring
  have hpow0 : 0 ≤ (Λ * 10 ^ 12 * r) ^ (k + 2) :=
    pow_nonneg (mul_pos (mul_pos hΛ (by norm_num)) hr).le _
  calc (Λ * ℓ) ^ (k + 2) * b
      ≤ (Λ * 10 ^ 12 * r) ^ (k + 2) * (e₀ * (5 / (Λ * 10 ^ 12)) ^ (k + 2)) :=
        mul_le_mul h1 hb₀ hb hpow0
    _ = e₀ * (Λ * 10 ^ 12 * r * (5 / (Λ * 10 ^ 12))) ^ (k + 2) := by
        rw [mul_pow (Λ * 10 ^ 12 * r)]
        ring
    _ = e₀ * (5 * r) ^ (k + 2) := by rw [h2]

/-! ## Part (b): comparison application and anchor change -/

/-- **The comparison constant** (step (4)): for `0 < ℓ ≤ 10^{12} r`,
`C (5r)^{-(k+2)} ((Λ ℓ)^{k+2} + (Λ ℓ)^{k+2}) ≤ 2 C (Λ 10^{12}/5)^{k+2}`. -/
theorem d1docc_comparison_constant {k : ℕ} {C Λ r ℓ : ℝ} (hC : 0 < C) (hΛ : 0 < Λ)
    (hr : 0 < r) (hℓ : 0 < ℓ) (hℓr : ℓ ≤ 10 ^ 12 * r) :
    C / (5 * r) ^ (k + 2) * ((Λ * ℓ) ^ (k + 2) + (Λ * ℓ) ^ (k + 2)) ≤
      2 * C * (Λ * 10 ^ 12 / 5) ^ (k + 2) := by
  have h5r : 0 < 5 * r := by linarith
  have hq : Λ * ℓ / (5 * r) ≤ Λ * 10 ^ 12 / 5 := by
    rw [div_le_iff₀ h5r]
    calc Λ * ℓ ≤ Λ * (10 ^ 12 * r) := mul_le_mul_of_nonneg_left hℓr hΛ.le
      _ = Λ * 10 ^ 12 / 5 * (5 * r) := by ring
  have hq0 : 0 ≤ Λ * ℓ / (5 * r) := div_nonneg (mul_pos hΛ hℓ).le h5r.le
  have hpow := pow_le_pow_left₀ hq0 hq (k + 2)
  calc C / (5 * r) ^ (k + 2) * ((Λ * ℓ) ^ (k + 2) + (Λ * ℓ) ^ (k + 2))
      = 2 * C * (Λ * ℓ / (5 * r)) ^ (k + 2) := by
        rw [div_pow]
        ring
    _ ≤ 2 * C * (Λ * 10 ^ 12 / 5) ^ (k + 2) :=
        mul_le_mul_of_nonneg_left hpow (by linarith)

/-- **Anchor and radius change** (step (5)): for `‖y - x‖ ≤ 200 r = 40 · 5r` and `s ≥ r > 0`,
`d_{y,s}(L₁, L₂)² ≤ 206² d_{x,5r}(L₁, L₂)²` (`ms3_change_sq`, `1 + 41 · 5r/s ≤ 206`). -/
theorem d1docc_change_sq {m : ℕ} (L₁ L₂ : AffineSpatialPlane n m) (x y : Spatial n)
    {r s : ℝ} (hr : 0 < r) (hs : r ≤ s) (hxy : ‖y - x‖ ≤ 200 * r) :
    planeComparison y s L₁ L₂ ^ 2 ≤ 206 ^ 2 * planeComparison x (5 * r) L₁ L₂ ^ 2 := by
  have hs0 : 0 < s := hr.trans_le hs
  have h5 : 0 < 5 * r := by linarith
  have hxy' : ‖y - x‖ ≤ 40 * (5 * r) := by linarith
  have h := ms3_change_sq L₁ L₂ x y h5 hs0 (by norm_num : (0 : ℝ) ≤ 40) hxy'
  rw [ms3_planeComparison_eq, ms3_planeComparison_eq]
  refine h.trans ?_
  have h1 : (40 + 1) * (5 * r) / s ≤ 205 := by
    rw [div_le_iff₀ hs0]
    linarith
  have h0 : 0 ≤ (40 + 1) * (5 * r) / s := div_nonneg (by linarith) hs0.le
  have hfac : (1 + (40 + 1) * (5 * r) / s) ^ 2 ≤ 206 ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  exact mul_le_mul_of_nonneg_right hfac (sq_nonneg _)

/-- **Part (b), core:** given the comparison premise on the own source
`P(g, 5r)` (for all planes and all measures dominating `μ⌞P(g, 5r)`), the inclusion
`P(g, 40 r) ⊆ P(z, Λ ℓ)`, `fit(M; g, 40r) ≤ fit(N; z, Λ ℓ) = (Λ ℓ)^{k+2} a`, `ℓ ≤ 10^{12} r`,
`‖y - x_g‖ ≤ 200 r` and `s ≥ r`: `d_{y,s}(L_M, L_N)² ≤ 2·206²·C·(Λ 10^{12}/5)^{k+2} a`. -/
theorem d1docc_bound_of_comparison {k : ℕ} {T : NeckType} {μ : Measure (Space n)}
    {C Λ r ℓ s : ℝ} {g z : Space n} {y : Spatial n} {M N : Models n k T.toFamilyKind}
    {aQ : ℝ≥0∞} (hC : 0 < C) (hΛ : 0 < Λ) (hr : 0 < r) (hℓ : 0 < ℓ)
    (hℓr : ℓ ≤ 10 ^ 12 * r)
    (hcmp : ∀ (L₁ L₂ : AffineSpatialPlane n (T.rank k)) (μ₁ μ₂ : Measure (Space n)),
      μ.restrict (Metric.ball g (5 * r)) ≤ μ₁ → μ.restrict (Metric.ball g (5 * r)) ≤ μ₂ →
      ENNReal.ofReal (planeComparison g.1 (5 * r) L₁ L₂ ^ 2) ≤
        ENNReal.ofReal (C / (5 * r) ^ (k + 2)) *
          (spatialFittingIntegral μ₁ L₁ + spatialFittingIntegral μ₂ L₂))
    (hball : Metric.ball g (40 * r) ⊆ Metric.ball z (Λ * ℓ))
    (hM : fit μ M g (40 * r) ≤ fit μ N z (Λ * ℓ))
    (hN : fit μ N z (Λ * ℓ) = ENNReal.ofReal ((Λ * ℓ) ^ (k + 2)) * aQ)
    (hy : ‖y - g.1‖ ≤ 200 * r) (hs : r ≤ s) :
    ENNReal.ofReal (planeComparison y s (NeckSelection.modelPlane T M)
        (NeckSelection.modelPlane T N) ^ 2) ≤
      ENNReal.ofReal (2 * 206 ^ 2 * C * (Λ * 10 ^ 12 / 5) ^ (k + 2)) * aQ := by
  have h5r : 0 < 5 * r := by linarith
  have h40 : 5 * r ≤ 40 * r := by linarith
  have hsub : μ.restrict (Metric.ball g (5 * r)) ≤ μ.restrict (Metric.ball g (40 * r)) :=
    Measure.restrict_mono (Metric.ball_subset_ball h40) le_rfl
  have hsub' : μ.restrict (Metric.ball g (5 * r)) ≤ μ.restrict (Metric.ball z (Λ * ℓ)) :=
    Measure.restrict_mono ((Metric.ball_subset_ball h40).trans hball) le_rfl
  have key := hcmp (NeckSelection.modelPlane T M) (NeckSelection.modelPlane T N) _ _ hsub hsub'
  have hS₁ : spatialFittingIntegral (μ.restrict (Metric.ball g (40 * r)))
      (NeckSelection.modelPlane T M) ≤ ENNReal.ofReal ((Λ * ℓ) ^ (k + 2)) * aQ :=
    ((d1docc_spatialFit_le_fit μ T M g (40 * r)).trans hM).trans hN.le
  have hS₂ : spatialFittingIntegral (μ.restrict (Metric.ball z (Λ * ℓ)))
      (NeckSelection.modelPlane T N) ≤ ENNReal.ofReal ((Λ * ℓ) ^ (k + 2)) * aQ :=
    (d1docc_spatialFit_le_fit μ T N z (Λ * ℓ)).trans hN.le
  have hc0 : 0 ≤ C / (5 * r) ^ (k + 2) := div_nonneg hC.le (pow_nonneg h5r.le _)
  have hp0 : 0 ≤ (Λ * ℓ) ^ (k + 2) := pow_nonneg (mul_pos hΛ hℓ).le _
  have hreal := d1docc_comparison_constant (k := k) hC hΛ hr hℓ hℓr
  have hcomp : ENNReal.ofReal (planeComparison g.1 (5 * r) (NeckSelection.modelPlane T M)
        (NeckSelection.modelPlane T N) ^ 2) ≤
      ENNReal.ofReal (2 * C * (Λ * 10 ^ 12 / 5) ^ (k + 2)) * aQ := by
    calc ENNReal.ofReal (planeComparison g.1 (5 * r) (NeckSelection.modelPlane T M)
          (NeckSelection.modelPlane T N) ^ 2)
        ≤ ENNReal.ofReal (C / (5 * r) ^ (k + 2)) *
            (spatialFittingIntegral (μ.restrict (Metric.ball g (40 * r)))
                (NeckSelection.modelPlane T M) +
              spatialFittingIntegral (μ.restrict (Metric.ball z (Λ * ℓ)))
                (NeckSelection.modelPlane T N)) := key
      _ ≤ ENNReal.ofReal (C / (5 * r) ^ (k + 2)) *
            (ENNReal.ofReal ((Λ * ℓ) ^ (k + 2)) * aQ +
              ENNReal.ofReal ((Λ * ℓ) ^ (k + 2)) * aQ) :=
          mul_le_mul_of_nonneg_left (add_le_add hS₁ hS₂) zero_le
      _ = ENNReal.ofReal (C / (5 * r) ^ (k + 2) * ((Λ * ℓ) ^ (k + 2) + (Λ * ℓ) ^ (k + 2))) *
            aQ := by
          rw [← add_mul, ← ENNReal.ofReal_add hp0 hp0, ← mul_assoc, ← ENNReal.ofReal_mul hc0]
      _ ≤ ENNReal.ofReal (2 * C * (Λ * 10 ^ 12 / 5) ^ (k + 2)) * aQ :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hreal) zero_le
  have hchange := d1docc_change_sq (NeckSelection.modelPlane T M) (NeckSelection.modelPlane T N)
    g.1 y hr hs hy
  calc ENNReal.ofReal (planeComparison y s (NeckSelection.modelPlane T M)
        (NeckSelection.modelPlane T N) ^ 2)
      ≤ ENNReal.ofReal (206 ^ 2 * planeComparison g.1 (5 * r) (NeckSelection.modelPlane T M)
          (NeckSelection.modelPlane T N) ^ 2) :=
        ENNReal.ofReal_le_ofReal hchange
    _ = ENNReal.ofReal (206 ^ 2) * ENNReal.ofReal (planeComparison g.1 (5 * r)
          (NeckSelection.modelPlane T M) (NeckSelection.modelPlane T N) ^ 2) :=
        ENNReal.ofReal_mul (by norm_num)
    _ ≤ ENNReal.ofReal (206 ^ 2) *
          (ENNReal.ofReal (2 * C * (Λ * 10 ^ 12 / 5) ^ (k + 2)) * aQ) :=
        mul_le_mul_of_nonneg_left hcomp zero_le
    _ = ENNReal.ofReal (2 * 206 ^ 2 * C * (Λ * 10 ^ 12 / 5) ^ (k + 2)) * aQ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 206 ^ 2),
          show (206 : ℝ) ^ 2 * (2 * C * (Λ * 10 ^ 12 / 5) ^ (k + 2)) =
            2 * 206 ^ 2 * C * (Λ * 10 ^ 12 / 5) ^ (k + 2) by ring]

/-! ## The statement -/

/-- **The per-occurrence last-witness bound** (`OccurrenceBoundStatement`). Constants: `Λ₀ = 1`, `B = 1000`,
`C₁ = 2·206²·C_pc·(Λ·10^{12}/5)^{k+2}`, `b₀ = e₀ (5/(Λ·10^{12}))^{k+2}`, where `C_pc` and `e₀`
come from the premise `PlaneComparisonStatement` at `(n, k, A)`. Each local minimizer is
compared with `Π_Q` on its own source `P(g, 5 r_i)` (ADR buffer `P(g, 20 r_i) ⊆ P(a, 1000 R)`). -/
theorem d1d_occurrenceBound_proof :
    PartitionEnergy.PlaneComparisonStatement → OccurrenceBoundStatement := by
  intro hPC n hn k hk hkn A hA
  obtain ⟨C, hC, e₀, he₀, hcmp⟩ := hPC n hn k hk hkn A hA
  refine ⟨1, le_rfl, fun Λ hΛ => ?_⟩
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  have hC₁ : 0 ≤ 2 * 206 ^ 2 * C * (Λ * 10 ^ 12 / 5) ^ (k + 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hC.le)
      (pow_nonneg (div_nonneg (mul_nonneg hΛ0.le (by norm_num)) (by norm_num)) _)
  have hb₀ : 0 < e₀ * (5 / (Λ * 10 ^ 12)) ^ (k + 2) :=
    mul_pos he₀ (pow_pos (div_pos (by norm_num) (mul_pos hΛ0 (by norm_num))) _)
  refine ⟨1000, by norm_num, 2 * 206 ^ 2 * C * (Λ * 10 ^ 12 / 5) ^ (k + 2), hC₁,
    e₀ * (5 / (Λ * 10 ^ 12)) ^ (k + 2), hb₀, ?_⟩
  intro b hb hbb₀ μ _ _ a _ R _ hADR P 𝒢 hF i g M hg hmin Q hQ hball hscale y s hy hs _
  have hr := d1docc_radius_pos 𝒢 i
  have hℓ := d1docc_scale_pos P Q.1
  have hgS : g ∈ μ.support := d1docc_rootCell_subset 𝒢 hg
  obtain ⟨hsrc, hsrc'⟩ := d1docc_source_subset 𝒢 hF hg i
  have hM : fit μ M g (40 * coherentScale (48 * 𝒢.rootScale) i) ≤
      fit μ (𝒢.model Q) Q.2 (Λ * P.scale Q.1) :=
    d1docc_fit_le_coeffFit Q (𝒢.model Q) hmin hball
  have hN := d1docc_fit_eq_mul_modelCoeff P μ (𝒢.model Q) Q (mul_pos hΛ0 hℓ)
  have hsmall : 𝒢.type = .horizontal → ∃ M' : Models n k 𝒢.type.toFamilyKind,
      fit μ M' g (2 * (5 * coherentScale (48 * 𝒢.rootScale) i)) ≤
        ENNReal.ofReal (e₀ * (5 * coherentScale (48 * 𝒢.rootScale) i) ^ (k + 2)) :=
    fun _ => ⟨M, d1docc_smallError hΛ0 hr hℓ hscale hb.le hbb₀
      (hM.trans (d1docc_coeffFit_le 𝒢 hΛ0 hQ))⟩
  exact d1docc_bound_of_comparison hC hΛ0 hr hℓ hscale
    (hcmp 𝒢.type 𝒢.type_available μ a (1000 * R) hADR g hgS
      (5 * coherentScale (48 * 𝒢.rootScale) i) (by linarith) hsrc hsrc' hsmall)
    hball hM hN hy hs

end Witness

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
