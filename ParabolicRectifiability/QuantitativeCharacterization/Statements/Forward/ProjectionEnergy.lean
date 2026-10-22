import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion

/-! # Projection energy for the completion: data and named statements

Definitions and proposition definitions only. This module fixes the statements below
`d1e_hub_projectionEnergy`, the whole-map affine energy of the completed vertical map:

`d1e_DerivativeRecurrenceStatement → d1e_AffinePoincareStatement → d1e_ProjectionEnergyStatement`.

The three parts:
1. **path square/tail estimates and the discrete affine estimate**: the path square sum
   `∑_j d_j² ≤ E` (`d1e2_PathErrorSumStatement`), `b_0 = 0` (`d1e2_CurvatureZeroStatement`),
   the sequence lemma `∑_j b_j² ≤ 4C² ∑ d²` together with the tail sums
   (`d1e2_MajorantSumStatement`), the limit tail (`d1e2_TailStatement`), their assembly for the
   actual family (`d1e2_PathEstimatesStatement`) and the discrete affine estimate at the discrete radii
   (`d1e2_DiscreteAffineStatement`);
2. **measurable averaging-kernel integration, summation and interpolation between the discrete
   radii**: measurability of the explicit majorants (`d1e2_CurvatureContinuousStatement`,
   `d1e2_PathErrorMeasurableStatement`), interpolation (`d1e2_ScaleInterpolationStatement`),
   the averaging kernel (`d1e2_KernelIntegrationStatement`) and the summation for radii at most
   `r₀` (`d1e2_SmallRadiiStatement`);
3. **radii above `r₀` and the all-radius assembly** (`d1e2_AllRadiusStatement`): the zero fit
   with `|F⁰ - F₀|² ≤ C E r₀²` (from the tail at level `0`), `∫_{r₀}^{∞} (r₀/s)² ds/s = 1/2`,
   no bound on the support's diameter or number of root components.

The level majorant. With `h = 1/10`, `r_j = F.scale j`, `b_j = d1e_curvature` and
`d_j = d1e_pathError` of the actual stages, put
`T_j(p) = ∑_{ℓ ≥ 0} h^ℓ d_{j+ℓ}(p)²` (`d1e2_tailSum`) and `W_j(p) = b_j(p)² + T_j(p)`
(`d1e2_levelMajorant`). Then the discrete affine estimate reads
`a_{F⁰-F₀}(p, r_j)² ≤ C r_j^{-(m+2)} ∫_{P_b(p,r_j)} W_j` (unnormalized form of the averages:
`|P_b(p,r)| = 2ω_m r^{m+2}`), and `∑_j W_j ≤ C E` pointwise. Every majorant is explicit and
measurable; no measurability of an affine error is used.

Constants: the recurrence constant and the thresholds come from
`d1e_DerivativeRecurrenceStatement` and the base path bound, uniformly in `m`; the Poincaré,
volume, interpolation and kernel constants depend on `m` (`∀ m, ∃ C`). Since a
`CoherentFamily n m` has an actual rank-`m` plane, `m ≤ n`; the assembly takes the sum over
`0 ≤ m ≤ n` of the per-`m` constants, which dominates their maximum.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-! ## The tail sum and the level majorant -/

section Majorant

variable {n m : ℕ} {ι : Type*}

/-- The tail sum `T_j(p) = ∑_{ℓ ≥ 0} h^ℓ d_{j+ℓ}(p)²` of the path errors of the actual stages
(`|F⁰ - F_j|²/r_j² ≤ C ∑_{l ≥ j} h^{l-j} d_l²`), `h = 1/10`, at a point
`p = (u, t)` of the base `Space m`. -/
def d1e2_tailSum (F : CoherentFamily n m ι) (P : CoherentChart.InitialChart F) (j : ℕ)
    (p : Space m) : ℝ≥0∞ :=
  ∑' ℓ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ * d1e_pathError F P (j + ℓ) p.1 p.2.val ^ 2)

/-- The level-`j` majorant `W_j(p) = b_j(p)² + T_j(p)`: the squared
normalized derivative size of the actual stage `F_j` plus the tail sum. -/
def d1e2_levelMajorant (F : CoherentFamily n m ι) (P : CoherentChart.InitialChart F) (j : ℕ)
    (p : Space m) : ℝ≥0∞ :=
  ENNReal.ofReal (d1e_curvature F P j p.1 p.2.val ^ 2) + d1e2_tailSum F P j p

end Majorant

/-! ## Part 1: path square and tail estimates, and the discrete affine estimate -/

/-- **The path square sum** (from the finite path estimate
by monotone convergence). For `0 < σ` there is `δ₀ > 0`
such that for every coherent family with `0 ≤ δ ≤ δ₀` and vertical square bound `E`, every
initial chart and every parameter `(u, t)`, the path errors of the actual stages satisfy
`∑_j d_j(u,t)² ≤ E`. -/
def d1e2_PathErrorSumStatement : Prop :=
  ∀ n : ℕ, ∀ σ : ℝ, 0 < σ →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ {m : ℕ} {ι : Type} (F : CoherentFamily n m ι) (δ E : ℝ),
        0 ≤ δ → δ ≤ δ₀ → F.IsCoherent σ δ → F.VerticalSquareBound E →
        ∀ (P : CoherentChart.InitialChart F) (u : Spatial m) (t : ℝ),
          ∑' j, ENNReal.ofReal (d1e_pathError F P j u t ^ 2) ≤ ENNReal.ofReal E

/-- **`b_0 = 0`**: the initial stage `F_0(u,t) = x_* + U_* u` is affine in `u`
and independent of `t`, so its normalized derivative size vanishes. -/
def d1e2_CurvatureZeroStatement : Prop :=
  ∀ {n m : ℕ} {ι : Type} (F : CoherentFamily n m ι) (P : CoherentChart.InitialChart F)
    (u : Spatial m) (t : ℝ), d1e_curvature F P 0 u t = 0

/-- **The sequence lemma for the level majorants** (with the sum
`∑_{j ≤ l} h^{l-j} ≤ (1-h)^{-1}`): for real sequences with `b ≥ 0`,
`b_0 = 0`, `b_{j+1} ≤ b_j/2 + C d_j` (`C ≥ 0`) and `∑_j d_j² ≤ D`,
`∑_j (b_j² + ∑_ℓ h^ℓ d_{j+ℓ}²) ≤ (4C² + 2) D` (indeed `∑ b² ≤ 4C² D` and the double tail sum
is at most `D/(1-h) = 10 D/9`). -/
def d1e2_MajorantSumStatement : Prop :=
  ∀ (b d : ℕ → ℝ) (C D : ℝ), 0 ≤ C → (∀ j, 0 ≤ b j) → b 0 = 0 →
    (∀ j, b (j + 1) ≤ 1 / 2 * b j + C * d j) →
    ∑' j, ENNReal.ofReal (d j ^ 2) ≤ ENNReal.ofReal D →
    ∑' j, (ENNReal.ofReal (b j ^ 2) +
        ∑' ℓ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ * d (j + ℓ) ^ 2)) ≤
      ENNReal.ofReal ((4 * C ^ 2 + 2) * D)

/-- **The limit tail** (weighted Cauchy-Schwarz): a sequence
`f_j` in `ℝ^n` with steps `|f_{j+1} - f_j| ≤ c r_j d_j`, radii `r_{j+1} = h r_j`, `r_0 > 0`,
`d ≥ 0` and `∑ d_j² ≤ D` converges, and its limit (`limUnder`) satisfies
`|f - f_j|² ≤ 2 c² r_j² ∑_ℓ h^ℓ d_{j+ℓ}²` at every level and `|f - f_0|² ≤ 2 c² D r_0²`
(`|F⁰ - F₀| ≤ C √E r₀`). -/
def d1e2_TailStatement : Prop :=
  ∀ {n : ℕ} (f : ℕ → Spatial n) (r d : ℕ → ℝ) (c D : ℝ), 0 ≤ c → 0 < r 0 →
    (∀ j, r (j + 1) = CoherentChart.ratio * r j) → (∀ j, 0 ≤ d j) →
    ∑' j, ENNReal.ofReal (d j ^ 2) ≤ ENNReal.ofReal D →
    (∀ j, ‖f (j + 1) - f j‖ ≤ c * r j * d j) →
    (∀ j, ‖limUnder atTop f - f j‖ₑ ^ 2 ≤
        ENNReal.ofReal (2 * c ^ 2 * r j ^ 2) *
          ∑' ℓ, ENNReal.ofReal (CoherentChart.ratio ^ ℓ * d (j + ℓ) ^ 2)) ∧
      ‖limUnder atTop f - f 0‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * c ^ 2 * D * r 0 ^ 2)

/-- **The path estimates of the actual family**. Proved (`d1e2_pathEstimates`) from the derivative recurrence and the
four part-1 path statements. For `0 < σ ≤ 1` there are `C_W, C_T ≥ 0` and thresholds `δ₀, E₀` such
that for every coherent family with these smallness bounds and vertical square bound `E` and
every initial chart: `∑_j W_j ≤ C_W E` at every point, the tail
`|F⁰ - F_j|² ≤ C_T r_j² T_j` at every point and level, and `|F⁰ - F₀|² ≤ C_T E r_0²`. -/
def d1e2_PathEstimatesStatement : Prop :=
  ∀ n : ℕ, ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
    ∃ CW CT δ₀ E₀ : ℝ, 0 ≤ CW ∧ 0 ≤ CT ∧ 0 < δ₀ ∧ 0 < E₀ ∧
      ∀ {m : ℕ} {ι : Type} (F : CoherentFamily n m ι) (δ E : ℝ),
        0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → F.IsCoherent σ δ → F.VerticalSquareBound E →
        ∀ P : CoherentChart.InitialChart F,
          (∀ p : Space m, ∑' j, d1e2_levelMajorant F P j p ≤ ENNReal.ofReal (CW * E)) ∧
          (∀ (p : Space m) (j : ℕ),
            ‖d1e_projectionLimit F P p.1 p.2.val - CoherentChart.stage F P j p.1 p.2.val‖ₑ ^ 2 ≤
              ENNReal.ofReal (CT * F.scale j ^ 2) * d1e2_tailSum F P j p) ∧
          (∀ p : Space m,
            ‖d1e_projectionLimit F P p.1 p.2.val - (P.origin + P.isometry p.1)‖ₑ ^ 2 ≤
              ENNReal.ofReal (CT * E * F.scale 0 ^ 2))

/-- **The discrete affine estimate** (from the limit tail and the time Poincaré inequality). For every rank
`m` there is `C ≥ 0` (the Poincaré constant of rank `m`, up to a factor) such that for every
coherent family, initial chart and tail constant `C_T ≥ 0`: if the tail bound
`|F⁰ - F_j|² ≤ C_T r_j² T_j` holds at every point and level, then at every centre `y` and
every discrete radius `r_j`,
`a_{F⁰-F₀}(y, r_j)² ≤ 2 (C + C_T) r_j^{-(m+2)} ∫_{P_b(y,r_j)} W_j` (base `affineErrorSq`, the
normalization `r^{-m-4}`; the displacement is the function of `d1e_ProjectionEnergyStatement`).
No smallness is needed: the inequality is a consequence of Poincaré for the smooth stage and of
the tail bound. -/
def d1e2_DiscreteAffineStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ {n : ℕ} {ι : Type} (F : CoherentFamily n m ι) (P : CoherentChart.InitialChart F)
      (CT : ℝ), 0 ≤ CT →
      (∀ (p : Space m) (j : ℕ),
        ‖d1e_projectionLimit F P p.1 p.2.val - CoherentChart.stage F P j p.1 p.2.val‖ₑ ^ 2 ≤
          ENNReal.ofReal (CT * F.scale j ^ 2) * d1e2_tailSum F P j p) →
      ∀ (y : Space m) (j : ℕ),
        affineErrorSq (parabolicVolume m)
            (fun p : Space m => d1e_projectionLimit F P p.1 p.2.val - (P.origin + P.isometry p.1))
            y (F.scale j) ≤
          ENNReal.ofReal (2 * (C + CT)) * (ENNReal.ofReal (F.scale j))⁻¹ ^ (m + 2) *
            ∫⁻ q in Metric.ball y (F.scale j), d1e2_levelMajorant F P j q ∂parabolicVolume m

/-! ## Part 2: measurable majorants, interpolation, averaging kernel and summation -/

/-- **Continuity of the finite-stage derivative size** (the finite-stage
derivative quantities are continuous): for every level `j`, `(u, t) ↦ b_j(u, t)` is continuous
on the base `Space m`. -/
def d1e2_CurvatureContinuousStatement : Prop :=
  ∀ {n m : ℕ} {ι : Type} (F : CoherentFamily n m ι) (P : CoherentChart.InitialChart F) (j : ℕ),
    Continuous fun p : Space m => d1e_curvature F P j p.1 p.2.val

/-- **Borel measurability of the path errors** (the path errors are Borel finite
maxima with distance-incidence conditions): for every level `j`,
`(u, t) ↦ d_j(u, t) = e_j(F_j(u,t), t)` is measurable on the base `Space m`. -/
def d1e2_PathErrorMeasurableStatement : Prop :=
  ∀ {n m : ℕ} {ι : Type} (F : CoherentFamily n m ι) (P : CoherentChart.InitialChart F) (j : ℕ),
    Measurable fun p : Space m => d1e_pathError F P j p.1 p.2.val

/-- **Interpolation between the discrete radii** (the first discrete radius
above `R` enlarges its buffer by at most `h^{-1}`). For every rank `m` there is `C ≥ 0` such
that for every `f : Space m → ℝ^d`, radii `r_{j+1} = h r_j` with `r_0 > 0`, every centre `y` and
every `R`:
`∫_{(0,R) ∩ (0,r_0]} a_f(y,s)² ds/s ≤ C ∑_{j : r_{j+1} < R} a_f(y, r_j)²`
(on `(r_{j+1}, r_j]` the ball `P_b(y,s)` lies in `P_b(y,r_j)` and `r_j/s < 10`; the `dr/r`
mass of `(r_{j+1}, r_j]` is `log 10`). -/
def d1e2_ScaleInterpolationStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ {d : ℕ} (f : Space m → Spatial d) (r : ℕ → ℝ), 0 < r 0 →
      (∀ j, r (j + 1) = CoherentChart.ratio * r j) →
      ∀ (y : Space m) (R : ℝ),
        ∫⁻ s in Ioo 0 R ∩ Iic (r 0), affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure ≤
          ENNReal.ofReal C *
            ∑' j, if r (j + 1) < R then affineErrorSq (parabolicVolume m) f y (r j) else 0

/-- **The averaging kernel** (the averaging points lie in `P_b(p₀,2R)` and each
averaging kernel has integrated centre mass at most a dimensional constant; with the buffer
`r ≤ 10 R` of the interpolation the points lie in `P_b(z, 11R)`). For every rank `m` there is
`C ≥ 0` such that for every measurable `W ≥ 0` on `Space m`, centre `z` and radii
`0 < r ≤ 10 R`: `∫_{P_b(z,R)} r^{-(m+2)} ∫_{P_b(y,r)} W dq dy ≤ C ∫_{P_b(z,11R)} W`
(Tonelli and `|P_b(q,r)| = 2ω_m r^{m+2}`). -/
def d1e2_KernelIntegrationStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (W : Space m → ℝ≥0∞), Measurable W →
      ∀ (z : Space m) (R r : ℝ), 0 < r → r ≤ 10 * R →
        ∫⁻ y in Metric.ball z R,
            (ENNReal.ofReal r)⁻¹ ^ (m + 2) * ∫⁻ q in Metric.ball y r, W q ∂parabolicVolume m
          ∂parabolicVolume m ≤
          ENNReal.ofReal C * ∫⁻ q in Metric.ball z (11 * R), W q ∂parabolicVolume m

/-- **The integrated energy at radii at most `r₀`** (for the scale range
`(0, R) ∩ (0, r₀]`). For every rank `m` there is `C ≥ 0` such that for every `f : Space m → ℝ^d`,
radii `r_{j+1} = h r_j` with `r_0 > 0`, measurable majorants `W_j ≥ 0` with `∑_j W_j ≤ M`
pointwise, and the discrete estimate `a_f(y, r_j)² ≤ A r_j^{-(m+2)} ∫_{P_b(y,r_j)} W_j` at every
centre and level: `∫_{P_b(z,R)} ∫_{(0,R) ∩ (0,r_0]} a_f(y,s)² ds/s dy ≤ C A M R^{m+2}`. -/
def d1e2_SmallRadiiStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ {d : ℕ} (f : Space m → Spatial d) (r : ℕ → ℝ) (W : ℕ → Space m → ℝ≥0∞) (A M : ℝ),
      0 < r 0 → (∀ j, r (j + 1) = CoherentChart.ratio * r j) → 0 ≤ A → 0 ≤ M →
      (∀ j, Measurable (W j)) → (∀ q, ∑' j, W j q ≤ ENNReal.ofReal M) →
      (∀ (y : Space m) (j : ℕ), affineErrorSq (parabolicVolume m) f y (r j) ≤
        ENNReal.ofReal A * (ENNReal.ofReal (r j))⁻¹ ^ (m + 2) *
          ∫⁻ q in Metric.ball y (r j), W j q ∂parabolicVolume m) →
      ∀ (z : Space m) (R : ℝ), 0 < R →
        ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ Iic (r 0),
            affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure ∂parabolicVolume m ≤
          ENNReal.ofReal (C * A * M * R ^ (m + 2))

/-! ## Part 3: radii above `r₀` and the all-radius assembly -/

/-- **Radii above `r₀` and the all-radius assembly** (part 3). For
every rank `m` there is `C ≥ 0` such that for every `f : Space m → ℝ^d`, `r₀ > 0`, `A, M ≥ 0`:
if `|f|² ≤ M r₀²` everywhere and the integrated energy over the scales `(0, R) ∩ (0, r₀]` is at
most `A R^{m+2}` at every centre and radius, then `f` has the affine Carleson bound `A + C M`.
For `s > r₀` the zero fit gives `a_f(y,s)² ≤ 2ω_m M (r₀/s)²`, and
`∫_{r₀}^{∞} (r₀/s)² ds/s = 1/2`; no bound on the support of `f` is used. -/
def d1e2_AllRadiusStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ {d : ℕ} (f : Space m → Spatial d) (r₀ A M : ℝ), 0 < r₀ → 0 ≤ A → 0 ≤ M →
      (∀ p : Space m, ‖f p‖ₑ ^ 2 ≤ ENNReal.ofReal (M * r₀ ^ 2)) →
      (∀ (z : Space m) (R : ℝ), 0 < R →
        ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ Iic r₀,
            affineErrorSq (parabolicVolume m) f y s ∂scaleMeasure ∂parabolicVolume m ≤
          ENNReal.ofReal (A * R ^ (m + 2))) →
      HasAffineCarlesonBound (parabolicVolume m) f (A + C * M)

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
