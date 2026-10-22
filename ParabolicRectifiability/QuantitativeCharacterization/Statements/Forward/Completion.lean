import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ForwardCovering
import ParabolicRectifiability.Geometry.Chart.Construction
import ParabolicRectifiability.Geometry.Neck.Conclusions
import ParabolicRectifiability.Analysis.SmoothCutoff.ParabolicBump
import ParabolicRectifiability.Analysis.TraceExtension.AffineError

/-! # Completion of the forward covering: data and named statements

Definitions and proposition definitions only. This module fixes the statements below the
completion step of the forward covering `exists_local_forward_covering`,
`d1_hub_completion` (implication form of `ForwardCompletionStatement`).

The four branches and their named nodes:
* **actual projection chart and smooth attachments**: the projection limit
  `F⁰ = lim F_j` of the actual stage maps `F_{j+1} = σ_j(F_j, t)` (`d1e_projectionLimit`, built
  on the base `CoherentChart.stage`), the completion datum `d1e_VerticalCompletion` (initial
  chart and stopping preimages) and the completed map `F = F⁰ + G` with the smooth separated
  attachment `G = ∑_c φ_c v_c` (`d1e_VerticalCompletion.spatialMap`), whose bumps are the
  base `SmoothCutoff.parabolicBump`, never the metric tents of `exists_exact_attachment`;
* **derivative recurrence and whole-map affine energy**: `d1e_curvature`
  (`b_j`), `d1e_pathError` (`d_j`) and the affine Carleson bound of the displacement `F - F₀`
  of the **same** map;
* **standard-coordinate BMO bridge**: the coordinatewise half-time BMO bound on
  the standard base `Space m`, and invariance under adding the time-independent spatial affine
  `F₀`;
* **horizontal trace and plateau**: the compact quadratic trace of a horizontal
  neck, completed by the Whitney plateau statement.

Same-map contract. The map `F` is a *definition* from the datum `K`
(`K.spatialMap`), not a field; every analytic statement below is stated for `K.limitMap`,
`K.attachment`, `K.displacement` of an arbitrary datum `K`, and the assembly applies the chart,
attachment, energy and BMO statements to one and the same `K`.

Conventions: `m = NeckType.vertical.rank k = k - 2` is the spatial rank of a vertical neck; the
parameter space is `Space m` (`ℝ^m` with snowflaked time), its volume `parabolicVolume m`; the
time-preserving map of `G : ℝ^m → ℝ → ℝ^n` is the base `timePreservingMap G`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

open ParabolicRectifiability.Foundations

/-! ## The actual projection limit and the path quantities -/

section Projection

variable {n m : ℕ} {ι : Type*}

/-- **The projection limit** `F⁰(u,t) = lim_{j → ∞} F_j(u,t)` of the actual stage maps `F_j = CoherentChart.stage F P j`
of the coherent family `F` with initial chart `P` (`F₀(u,t) = x_* + U_* u`,
`F_{j+1} = σ_j(F_j(u,t), t)`, `σ_j = CoherentProjection.sigma` with the partition weights). The
limit is Mathlib's `limUnder`; under the chart smallness the sequence converges uniformly
(`|F_{j+1} - F_j| ≤ ε r_j`), so this is the genuine limit, not a choice. -/
def d1e_projectionLimit (F : CoherentFamily n m ι) (P : CoherentChart.InitialChart F)
    (u : Spatial m) (t : ℝ) : Spatial n :=
  limUnder atTop fun j => CoherentChart.stage F P j u t

/-- The normalized derivative size `b_j(u,t) = r_j (‖D_u² F_j(u,t)‖ + |∂_t F_j(u,t)|)` of the
actual stage map. -/
def d1e_curvature (F : CoherentFamily n m ι) (P : CoherentChart.InitialChart F) (j : ℕ)
    (u : Spatial m) (t : ℝ) : ℝ :=
  F.scale j * (‖fderiv ℝ (fun v => fderiv ℝ (fun w => CoherentChart.stage F P j w t) v) u‖ +
    ‖deriv (fun s => CoherentChart.stage F P j u s) t‖)

/-- The path error `d_j(u,t) = e_j(F_j(u,t), t)`: the base local
comparison coefficient `CoherentChart.localError` at the actual path point, as a real number
(it is a finite maximum of finite values). -/
def d1e_pathError (F : CoherentFamily n m ι) (P : CoherentChart.InitialChart F) (j : ℕ)
    (u : Spatial m) (t : ℝ) : ℝ :=
  (CoherentChart.localError F j (CoherentChart.pathPoint F P j u t)).toReal

end Projection

/-! ## The vertical smooth-completion datum and the completed map -/

section Completion

variable {n : ℕ} {ι : Type*}

/-- **The vertical smooth-completion datum** of a vertical neck `N` with bump ratio `χ` and
stopping-error ratio `ζ` (the attachment is
implemented by smooth bumps). Its data are an initial chart `chart` of the
neck's coherent family (this fixes the actual stages `F_j`, their limit
`F⁰ = d1e_projectionLimit N.family chart` and the initial affine map `F₀ = x_* + U_* u`) and
parameters `pre c = p_c` of the stopping centres. The fields are the facts the attachment and
its estimates use:
* `pre_time`: `p_c` is at the physical time of `c`;
* `stop_error`: `|F⁰(p_c) - x_c| ≤ 2 ζ d_c`;
* `ball_disjoint`: `d_b(p_c, p_{c'}) ≥ χ (d_c + d_{c'})` for distinct stopping centres. The separation field makes the open parameter balls `P_b(p_c, χ d_c)` pairwise
  disjoint. Their closed balls may touch. Each bump's closed support lies strictly inside its
  corresponding open ball (base `tsupport_parabolicBump_subset`,
  `point_mem_ball_of_mem_bumpSupportSet`), so the actual supports are disjoint;
* `core_avoid`: every parameter whose image under `Φ⁰ = (F⁰, t)` is a core point lies outside
  every bump ball.
The completed map `F = F⁰ + G` is *defined* from these data (`spatialMap`); it is not a field. -/
structure d1e_VerticalCompletion {k : ℕ} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
    (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ) (χ ζ : ℝ) where
  /-- The initial chart `(x_*, U_*)` of the neck's coherent family. -/
  chart : CoherentChart.InitialChart N.family
  /-- The parameter `p_c` of a stopping centre `c` (only stopping centres matter). -/
  pre : Space n → Space (NeckType.vertical.rank k)
  pre_time : ∀ c ∈ N.stopping, (pre c).2 = c.2
  stop_error : ∀ c ∈ N.stopping,
    ‖d1e_projectionLimit N.family chart (pre c).1 (pre c).2.val - c.1‖ ≤ 2 * ζ * N.radius c
  ball_disjoint : ∀ c ∈ N.stopping, ∀ c' ∈ N.stopping, c ≠ c' →
    χ * N.radius c + χ * N.radius c' ≤ dist (pre c) (pre c')
  core_avoid : ∀ c ∈ N.stopping, ∀ p : Space (NeckType.vertical.rank k),
    timePreservingMap (d1e_projectionLimit N.family chart) p ∈ N.core →
      χ * N.radius c ≤ dist p (pre c)

namespace d1e_VerticalCompletion

variable {k : ℕ} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
  {N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ} {χ ζ : ℝ}
  (K : d1e_VerticalCompletion N χ ζ)

/-- The projection limit `F⁰` as a function on the base `Space m`. -/
def limitMap (p : Space (NeckType.vertical.rank k)) : Spatial n :=
  d1e_projectionLimit N.family K.chart p.1 p.2.val

/-- The initial time-independent spatial affine map `F₀(u,t) = x_* + U_* u`. -/
def initialMap (p : Space (NeckType.vertical.rank k)) : Spatial n :=
  K.chart.origin + K.chart.isometry p.1

/-- One attachment term `g_c = φ_c v_c`: `v_c = x_c - F⁰(p_c)` and the
base bump `SmoothCutoff.parabolicBump` of radius `χ d_c / 3` at `p_c` (one on the parabolic
`2 χ d_c / 3`-ball, supported in the open `χ d_c`-ball, `C²` spatially and `C¹` in time with the
base bounds). -/
def bumpTerm (c : Space n) (p : Space (NeckType.vertical.rank k)) : Spatial n :=
  SmoothCutoff.parabolicBump (χ * N.radius c / 3) (K.pre c) (p.1, p.2.val) •
    (c.1 - K.limitMap (K.pre c))

/-- The smooth exact attachment `G = ∑_{c ∈ 𝒞₊} g_c`. The separation field
`ball_disjoint` makes the open parameter balls pairwise disjoint (their closed balls may touch);
each bump's closed support lies strictly inside its open ball, so the actual supports are
disjoint and at each parameter at most one term is nonzero. -/
def attachment (p : Space (NeckType.vertical.rank k)) : Spatial n :=
  ∑' c : N.stopping, K.bumpTerm (c : Space n) p

/-- **The completed spatial map** `F = F⁰ + G`. -/
def spatialMap (p : Space (NeckType.vertical.rank k)) : Spatial n :=
  K.limitMap p + K.attachment p

/-- The completed time-preserving map `Φ = (F, t)`; its form is that of
`VerticalReference.map`. -/
def map (p : Space (NeckType.vertical.rank k)) : Space n :=
  (K.spatialMap p, p.2)

/-- The displacement `F - F₀` from the initial affine map. -/
def displacement (p : Space (NeckType.vertical.rank k)) : Spatial n :=
  K.spatialMap p - K.initialMap p

end d1e_VerticalCompletion

end Completion

/-! ## the actual projection chart and the smooth attachments -/

/-- **Chart and smooth attachments for the actual limit**. For `0 < σ ≤ 1` there are thresholds `δ₀, E₀, κ₀` and a
constant `C` such that for every coherent family with these smallness bounds, every initial
chart `P` and the actual projection limit `F⁰ = d1e_projectionLimit F P`: `Φ⁰ = (F⁰, t)` has
metric bounds `0.8` and `1.1`, every level limit (hence every core point) lies in its image, and
every point with a stopping parent of tube tolerance `θ` and radius `d` has a parameter at its
own time with `|F⁰(u, t_c) - x_c| ≤ C (θ + δ) d`. -/
def d1e_ChartStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
    ∃ δ₀ E₀ κ₀ C : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < C ∧
      ∀ {m : ℕ} {ι : Type} (F : CoherentFamily n m ι) (δ E κ : ℝ),
        0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → 0 ≤ κ → κ ≤ κ₀ →
        F.IsCoherent σ δ → F.VerticalSquareBound E → F.HasCenterHeight κ →
        ∀ P : CoherentChart.InitialChart F,
          (∀ p p' : Space m,
            4 / 5 * dist p p' ≤ dist (timePreservingMap (d1e_projectionLimit F P) p)
                (timePreservingMap (d1e_projectionLimit F P) p') ∧
              dist (timePreservingMap (d1e_projectionLimit F P) p)
                (timePreservingMap (d1e_projectionLimit F P) p') ≤ 11 / 10 * dist p p') ∧
          (∀ z : Space n, F.IsLevelLimit z →
            z ∈ Set.range (timePreservingMap (d1e_projectionLimit F P))) ∧
          ∀ θ : ℝ, 0 ≤ θ → ∀ (c : Space n) (d : ℝ) (o : Option (ℕ × ι)),
            F.IsStoppingParent θ c d o →
              ∃ u : Spatial m, ‖d1e_projectionLimit F P u c.2.val - c.1‖ ≤ C * (θ + δ) * d

/-- **Compact displacement of the projection limit**. For
`0 < σ ≤ 1` there is `δ₀ > 0` such that for every coherent family with `δ ≤ δ₀` and every
initial chart, `F⁰ - F₀` is continuous on `Space m` and compactly supported: all centres lie in
a bounded set (finite root level, parents within `r_j`), and a parameter whose initial image
is far from them is never moved by a stage map. -/
def d1e_ProjectionDisplacementStatement : Prop :=
  ∀ n : ℕ, ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ {m : ℕ} {ι : Type} (F : CoherentFamily n m ι) (δ : ℝ), 0 ≤ δ → δ ≤ δ₀ →
        F.IsCoherent σ δ → ∀ P : CoherentChart.InitialChart F,
          Continuous (fun p : Space m =>
              d1e_projectionLimit F P p.1 p.2.val - (P.origin + P.isometry p.1)) ∧
            HasCompactSupport (fun p : Space m =>
              d1e_projectionLimit F P p.1 p.2.val - (P.origin + P.isometry p.1))

/-- **Existence of the completion datum**. If `Φ⁰` of the actual
limit for an initial chart `P` has the metric bounds `0.8`, `1.1` and every stopping centre has a
parameter at its own time within `2 ζ d_c` of it, then with `30 χ ≤ min(c₀,1)` and `24 ζ ≤ χ`
(with `χ = c_*/30`, `ζ = c_*/720`) these parameters form a completion datum with chart `P`:
separation of the stops and the core (`c₀`) and the upper metric bound
give the bump-ball separation and core avoidance. -/
def d1e_CompletionDatumStatement : Prop :=
  ∀ {n k : ℕ} {ι : Type} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
    (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ)
    (P : CoherentChart.InitialChart N.family) (χ ζ : ℝ),
    0 < χ → 0 ≤ ζ → 30 * χ ≤ min c₀ 1 → 24 * ζ ≤ χ →
    (∀ p p' : Space (NeckType.vertical.rank k),
      4 / 5 * dist p p' ≤ dist (timePreservingMap (d1e_projectionLimit N.family P) p)
          (timePreservingMap (d1e_projectionLimit N.family P) p') ∧
        dist (timePreservingMap (d1e_projectionLimit N.family P) p)
          (timePreservingMap (d1e_projectionLimit N.family P) p') ≤ 11 / 10 * dist p p') →
    (∀ c ∈ N.stopping, ∃ u : Spatial (NeckType.vertical.rank k),
      ‖d1e_projectionLimit N.family P u c.2.val - c.1‖ ≤ 2 * ζ * N.radius c) →
    ∃ K : d1e_VerticalCompletion N χ ζ, K.chart = P

/-- **The smooth separated attachments**. There is a margin
`c_A > 0`, depending only on `n, k` (through the base bump constants), such that for every
vertical neck, `χ > 0`, `ζ ≤ c_A χ` and every completion datum whose limit map `Φ⁰` has metric
bounds `0.8`, `1.1` and contains the core in its image: the completed map `Φ = (F⁰ + G, t)` is
`2`-bi-Lipschitz, attaches exactly (`Φ(p_c) = c` for stops, `G = 0` on core parameters), hence
contains every centre; `G` is continuous with compact support; and the displacement `F - F₀` is
`3`-Lipschitz. -/
def d1e_AttachmentStatement : Prop :=
  ∀ n k : ℕ, ∃ cA : ℝ, 0 < cA ∧
    ∀ {ι : Type} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
      (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ) (χ ζ : ℝ), 0 < χ →
      ζ ≤ cA * χ → ∀ K : d1e_VerticalCompletion N χ ζ,
        (∀ p p' : Space (NeckType.vertical.rank k),
          4 / 5 * dist p p' ≤ dist (timePreservingMap (d1e_projectionLimit N.family K.chart) p)
              (timePreservingMap (d1e_projectionLimit N.family K.chart) p') ∧
            dist (timePreservingMap (d1e_projectionLimit N.family K.chart) p)
              (timePreservingMap (d1e_projectionLimit N.family K.chart) p') ≤
                11 / 10 * dist p p') →
        (∀ z ∈ N.core, z ∈ Set.range (timePreservingMap (d1e_projectionLimit N.family K.chart))) →
        (∀ p p' : Space (NeckType.vertical.rank k),
            dist p p' ≤ 2 * dist (K.map p) (K.map p') ∧
              dist (K.map p) (K.map p') ≤ 2 * dist p p') ∧
          N.centers ⊆ Set.range K.map ∧
          Continuous K.attachment ∧ HasCompactSupport K.attachment ∧
          LipschitzWith 3 K.displacement

/-! ## the derivative recurrence and the whole-map affine energy -/

/-- **The derivative recurrence**. For `0 < σ ≤ 1`
there are `C ≥ 0` and thresholds `δ₀, E₀` such that for every coherent family with these
smallness bounds and vertical square bound `E`, every initial chart and every parameter `(u,t)`,
the actual stages satisfy, for every level `j`,
`b_{j+1} ≤ b_j / 2 + C d_j` and `|F_{j+1}(u,t) - F_j(u,t)| ≤ C r_j d_j`, with
`b_j = d1e_curvature`, `d_j = d1e_pathError`. -/
def d1e_DerivativeRecurrenceStatement : Prop :=
  ∀ n : ℕ, ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
    ∃ C δ₀ E₀ : ℝ, 0 ≤ C ∧ 0 < δ₀ ∧ 0 < E₀ ∧
      ∀ {m : ℕ} {ι : Type} (F : CoherentFamily n m ι) (δ E : ℝ),
        0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → F.IsCoherent σ δ → F.VerticalSquareBound E →
        ∀ (P : CoherentChart.InitialChart F) (u : Spatial m) (t : ℝ) (j : ℕ),
          d1e_curvature F P (j + 1) u t ≤
              1 / 2 * d1e_curvature F P j u t + C * d1e_pathError F P j u t ∧
            ‖CoherentChart.stage F P (j + 1) u t - CoherentChart.stage F P j u t‖ ≤
              C * F.scale j * d1e_pathError F P j u t

/-- **Second-order affine Poincaré on parabolic base balls**. For every
spatial rank `m` there is `C ≥ 0` such that every `C²` map `H : ℝ^m × ℝ → ℝ^d` has, on every
base ball `P_b(p,r)`,
`r^{-m-4} inf_{a,B} ∫_{P_b(p,r)} |H - a - B u|² ≤ C r^{-m} ∫_{P_b(p,r)} (‖D_u² H‖² + |∂_t H|²)`
(the left side is the base `affineErrorSq`). Rank zero is time Poincaré. The constant is chosen
before the target dimension `d`. Proved (`d1e_affine_poincare`) from the three
children below (no applicable `L²` Poincaré inequality exists in the base
or in Mathlib). -/
def d1e_AffinePoincareStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) (H : Spatial m → ℝ → Spatial d),
    ContDiff ℝ 2 (fun x : Spatial m × ℝ => H x.1 x.2) →
    ∀ (p : Space m) (r : ℝ), 0 < r →
      affineErrorSq (parabolicVolume m) (fun z : Space m => H z.1 z.2.val) p r ≤
        ENNReal.ofReal C * (ENNReal.ofReal r)⁻¹ ^ m *
          ∫⁻ z in Metric.ball p r,
            ENNReal.ofReal (‖fderiv ℝ (fun v => fderiv ℝ (fun w => H w z.2.val) v) z.1‖ ^ 2 +
              ‖deriv (fun s => H z.1 s) z.2.val‖ ^ 2) ∂parabolicVolume m

/-- **First-order time Poincaré on an interval** (child of `d1e_AffinePoincareStatement`). For every `C¹` curve `g : ℝ → ℝ^d`, every interval `(a, b)` and every base point
`s₀ ∈ [a, b]`: `∫_a^b |g(s) - g(s₀)|² ds ≤ (b - a)² ∫_a^b |g'(s)|² ds`. The constant `1` is
absolute, in particular independent of the target dimension. -/
def d1e_TimePoincareStatement : Prop :=
  ∀ (d : ℕ) (g : ℝ → Spatial d) (a b : ℝ), a < b → ContDiff ℝ 1 g →
    ∀ s₀ ∈ Set.Icc a b,
      ∫⁻ s in Set.Ioo a b, ‖g s - g s₀‖ₑ ^ 2 ≤
        ENNReal.ofReal ((b - a) ^ 2) * ∫⁻ s in Set.Ioo a b, ‖deriv g s‖ₑ ^ 2

/-- **First-order spatial Poincaré on a Euclidean ball, Banach-valued** (child of
`d1e_AffinePoincareStatement`). For every rank `m` there is `C ≥ 0`, chosen before the target
space, such that every `C¹` map `f : ℝ^m → Y` into a real Banach space has, on every ball
`B(u₀, r)`, a constant `c` with `∫_B |f - c|² ≤ C r² ∫_B ‖Df‖²`. Rank zero included (the ball is
the point and `f` is constant). The Banach target is needed because the second-order step applies
it to `Df : ℝ^m → (ℝ^m →L ℝ^d)` (operator norm). -/
def d1e_SpatialPoincareStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (f : Spatial m → Y),
      ContDiff ℝ 1 f → ∀ (u₀ : Spatial m) (r : ℝ), 0 < r →
        ∃ c : Y, ∫⁻ u in Metric.ball u₀ r, ‖f u - c‖ₑ ^ 2 ≤
          ENNReal.ofReal (C * r ^ 2) * ∫⁻ u in Metric.ball u₀ r, ‖fderiv ℝ f u‖ₑ ^ 2

/-- **Second-order spatial affine Poincaré on a Euclidean ball** (child of
`d1e_AffinePoincareStatement`). For every rank `m` there is `C ≥ 0`, chosen before the target
dimension, such that every `C²` map `f : ℝ^m → ℝ^d` has, on every ball `B(u₀, r)`, an affine
competitor `a + B u` with `∫_B |f - a - B u|² ≤ C r⁴ ∫_B ‖D²f‖²`. Rank zero included. -/
def d1e_SpatialSecondPoincareStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) (f : Spatial m → Spatial d), ContDiff ℝ 2 f →
    ∀ (u₀ : Spatial m) (r : ℝ), 0 < r →
      ∃ (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d),
        ∫⁻ u in Metric.ball u₀ r, ‖f u - (a + B u)‖ₑ ^ 2 ≤
          ENNReal.ofReal (C * r ^ 4) *
            ∫⁻ u in Metric.ball u₀ r, ‖fderiv ℝ (fun v => fderiv ℝ f v) u‖ₑ ^ 2

/-- **Affine energy of the projection limit**. For
`0 < σ ≤ 1` there are `C ≥ 0` and thresholds `δ₀, E₀` such that for every coherent family with
these smallness bounds and vertical square bound `E` and every initial chart, the displacement
`F⁰ - F₀` of the actual projection limit has the affine Carleson bound `C E` on `Space m`, at
every centre and every radius (radii above `r₀` included). -/
def d1e_ProjectionEnergyStatement : Prop :=
  ∀ n : ℕ, ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
    ∃ C δ₀ E₀ : ℝ, 0 ≤ C ∧ 0 < δ₀ ∧ 0 < E₀ ∧
      ∀ {m : ℕ} {ι : Type} (F : CoherentFamily n m ι) (δ E : ℝ),
        0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → F.IsCoherent σ δ → F.VerticalSquareBound E →
        ∀ P : CoherentChart.InitialChart F,
          HasAffineCarlesonBound (parabolicVolume m)
            (fun p : Space m => d1e_projectionLimit F P p.1 p.2.val - (P.origin + P.isometry p.1))
            (C * E)

/-- **Affine energy of the smooth attachment**. For
every `n, k` there is `C ≥ 0` (depending only on the rank `k - 2` through the base bump
constants) such that for every vertical neck, `χ > 0`, `a ≥ 0`, `ζ ≤ a χ` and every completion
datum, `G = K.attachment` has the affine Carleson bound `C a²` on `Space m`, including bumps
larger than the testing root. -/
def d1e_AttachmentEnergyStatement : Prop :=
  ∀ n k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ {ι : Type} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
      (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ) (χ ζ a : ℝ), 0 < χ → 0 ≤ a →
      ζ ≤ a * χ → ∀ K : d1e_VerticalCompletion N χ ζ,
        HasAffineCarlesonBound (parabolicVolume (NeckType.vertical.rank k)) K.attachment
          (C * a ^ 2)

/-- **Subadditivity of the affine Carleson bound** (combining with the discrete affine estimate): for
continuous `f, g : Space m → ℝ^d`, bounds `B₁, B₂` give `2 (B₁ + B₂)` for `f + g`. -/
def d1e_AffineCarlesonAddStatement : Prop :=
  ∀ (m d : ℕ) (f g : Space m → Spatial d) (B₁ B₂ : ℝ), Continuous f → Continuous g →
    HasAffineCarlesonBound (parabolicVolume m) f B₁ →
    HasAffineCarlesonBound (parabolicVolume m) g B₂ →
    HasAffineCarlesonBound (parabolicVolume m) (f + g) (2 * (B₁ + B₂))

/-- **Whole-map affine energy of the completed map**. For `0 < σ ≤ 1` there are `C ≥ 0` and thresholds `δ₀, E₀` such that for
every vertical neck with `δ ≤ δ₀`, `E ≤ E₀`, every `χ > 0`, `a ≥ 0`, `ζ ≤ a χ` and every completion
datum whose two displacement parts are continuous, the displacement `F - F₀` of the completed
map `F = F⁰ + G` has the affine Carleson bound `C (E + a²)` (that is, `C (E_neck + (ζ/χ)²)`). -/
def d1e_WholeAffineEnergyStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
    ∃ C δ₀ E₀ : ℝ, 0 ≤ C ∧ 0 < δ₀ ∧ 0 < E₀ ∧
      ∀ {ι : Type} {q : Space n} {R c₀ Cd Cs δ E κ θ γ : ℝ}
        (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ), δ ≤ δ₀ → E ≤ E₀ →
        ∀ (χ ζ a : ℝ), 0 < χ → 0 ≤ a → ζ ≤ a * χ → ∀ K : d1e_VerticalCompletion N χ ζ,
          Continuous (fun p => K.limitMap p - K.initialMap p) → Continuous K.attachment →
          HasAffineCarlesonBound (parabolicVolume (NeckType.vertical.rank k)) K.displacement
            (C * (E + a ^ 2))

/-! ## the standard-coordinate BMO bridge -/

/-- **Affine-to-BMO bound on the standard base, coordinatewise**. For every rank `m` there is `C > 0` such that
every compactly supported, `L`-Lipschitz `H : Space m → ℝ^d` with affine Carleson bound `B` on
`(Space m, parabolicVolume m)` has, in every Euclidean coordinate, the public half-time BMO bound
`C (L + √B)` (`HasHalfTimeBMOBound`: Lipschitz, and a representative of the standard
homogeneous half-time derivative with standard parabolic BMO bound). -/
def d1e_StandardAffineBMOStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (H : Space m → Spatial d) (L : ℝ≥0) (B : ℝ),
    HasCompactSupport H → LipschitzWith L H → HasAffineCarlesonBound (parabolicVolume m) H B →
    ∀ α : Fin d, HasHalfTimeBMOBound m (fun p => H p α) (C * ((L : ℝ) + Real.sqrt B))

/-- **Invariance under a time-independent spatial affine function**: the public half-time BMO bound of a real function on the standard base is
unchanged by adding `c + ℓ(u)` with `ℓ` linear (the pure-time half derivative annihilates it).
The statement `compactBridgeRepresentative_proof` covers only constants. -/
def d1e_AffineInvarianceStatement : Prop :=
  ∀ (m : ℕ) (H : Space m → ℝ) (B c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ),
    HasHalfTimeBMOBound m H B → HasHalfTimeBMOBound m (fun p => c + ℓ p.1 + H p) B

/-- **The standard-coordinate BMO bridge**: for every rank `m` there is
`C > 0` such that a map `F : Space m → ℝ^d` whose displacement `F - F₀` from a time-independent
spatial affine map `F₀(u) = x₀ + U u` (`U` a linear isometry) is `L`-Lipschitz, compactly
supported and has affine Carleson bound `B` satisfies `max_α [|D_t|^{1/2} F^α]_{BMO_P} ≤
C (L + √B)` in the public coordinate form of vertical references. -/
def d1e_BMOBridgeStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (F : Space m → Spatial d) (x₀ : Spatial d)
    (U : Spatial m →ₗᵢ[ℝ] Spatial d) (L : ℝ≥0) (B : ℝ),
    LipschitzWith L (fun p => F p - (x₀ + U p.1)) →
    HasCompactSupport (fun p => F p - (x₀ + U p.1)) →
    HasAffineCarlesonBound (parabolicVolume m) (fun p => F p - (x₀ + U p.1)) B →
    HasCoordinateHalfTimeBMOBound m d F (C * ((L : ℝ) + Real.sqrt B))

/-! ## the horizontal trace and plateau completion -/

/-- **The horizontal neck trace**. For
`c₀ > 0` and `0 < σ ≤ 1` there is `ε₀ > 0` such that every horizontal neck with tolerances at
most `ε₀` has a `2`-bi-Lipschitz spatial map `G : ℝ^k → ℝ^n`, a nonempty compact `D ⊆ ℝ^k` and a
time function `τ` with `|τ(u) - τ(v)| ≤ 2² |u - v|²` on `D` whose trace points `(G(u), τ(u))`,
`u ∈ D`, contain every centre (singleton trace when the centre set is empty). -/
def d1e_HorizontalTraceStatement : Prop :=
  ∀ n k : ℕ, ∀ c₀ σ : ℝ, 0 < c₀ → 0 < σ → σ ≤ 1 →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (ι : Type) (q : Space n) (R Cd Cs δ E κ θ γ : ℝ),
      δ ≤ ε₀ → E ≤ ε₀ → κ ≤ ε₀ → θ ≤ ε₀ → γ ≤ ε₀ →
      ∀ N : NeckRegion n k .horizontal ι q R c₀ Cd Cs σ δ E κ θ γ,
        ∃ G : Spatial k → Spatial n,
          (∀ u v : Spatial k, dist u v ≤ 2 * dist (G u) (G v) ∧ dist (G u) (G v) ≤ 2 * dist u v) ∧
          ∃ (D : Set (Spatial k)) (τ : Spatial k → ℝ), D.Nonempty ∧ IsCompact D ∧
            (∀ u ∈ D, ∀ v ∈ D, |τ u - τ v| ≤ 2 ^ 2 * dist u v ^ 2) ∧
            N.centers ⊆ (fun u => point (G u) (τ u)) '' D

/-- **The horizontal completed reference**: every small
horizontal neck has a horizontal `2`-reference whose carrier contains its centres. Proved
from the trace, the Whitney plateau completion and trace-point carrier membership. -/
def d1e_HorizontalCompletionStatement : Prop :=
  ∀ n k : ℕ, ∀ c₀ σ : ℝ, 0 < c₀ → 0 < σ → σ ≤ 1 →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (ι : Type) (q : Space n) (R Cd Cs δ E κ θ γ : ℝ),
      δ ≤ ε₀ → E ≤ ε₀ → κ ≤ ε₀ → θ ≤ ε₀ → γ ≤ ε₀ →
      ∀ N : NeckRegion n k .horizontal ι q R c₀ Cd Cs σ δ E κ θ γ,
        ∃ H : HorizontalReference n k 2, N.centers ⊆ H.carrier

/-! ## The vertical completed reference -/

/-- **The vertical completed reference**: for `n ≥ 1`, `k < n + 2`, `c₀ > 0`, `0 < σ ≤ 1` there are `L ≥ 2` and
`ε₀ > 0` such that every vertical neck with tolerances `δ, E, κ, θ ≤ ε₀` has a vertical
`L`-reference whose carrier contains its centres: the smooth completion `Φ = (F⁰ + G, t)` of the
actual projection limit. `L` depends only on `n, k, c₀, σ`. -/
def d1e_VerticalCompletionStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, k < n + 2 → ∀ c₀ σ : ℝ, 0 < c₀ → 0 < σ → σ ≤ 1 →
    ∃ L : ℝ, 2 ≤ L ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (ι : Type) (q : Space n) (R Cd Cs δ E κ θ γ : ℝ),
      δ ≤ ε₀ → E ≤ ε₀ → κ ≤ ε₀ → θ ≤ ε₀ →
      ∀ N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ,
        ∃ V : VerticalReference n k L, N.centers ⊆ V.carrier

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
