import ParabolicRectifiability.Geometry.Neck.Region
import ParabolicRectifiability.Metric.Hausdorff
import ParabolicRectifiability.Metric.Measure

/-!
# Conclusions supplied by the neck structure theorems

These predicates separate the geometric outputs from the coherent data in
`NeckRegion`: buffered reference measures, exact parametrizations, local and
total core/stopping content, and density of the core's own Hausdorff measure.
The public neck theorems proving these conclusions are `vertical_coherent_chart_proof` and its companions in `NeckHubTree`.

Vertical maps preserve time on a full parabolic base. Horizontal time maps
are defined on the compact parameter subset only. Core-density conclusions
refer to the restricted Hausdorff measure, not to an arbitrary source used
to construct the neck.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal

/-! ## Conclusion shapes -/

/-- The time-preserving map `Φ(u,t) = (F(u,t), t)` on the parameter space
`ℝ^m × ℝ`. The parameter space is `Space m`, whose metric is exactly
`d_b((u,t),(v,s)) = max{|u-v|, √|t-s|}`. -/
def timePreservingMap {n m : ℕ} (G : Spatial m → ℝ → Spatial n) (p : Space m) : Space n :=
  point (G p.1 p.2.val) p.2.val

namespace CoherentFamily

variable {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι)

/-- Buffered reference conclusion, vertical form, for the truncation through level `N`.
There are a time-preserving chart `Φ` with the bounds `0.8 d_b ≤ d_P∘Φ ≤ 1.1 d_b` and
a full base ball `D = P_b(p₀, C_r R)` such that every occurrence `(j,a)`, `j ≤ N`,
has a preimage `p` in `D` at the center's own time, with
`d_P(Φ(p), z_{j,a}) ≤ r_j/4` and `P_b(p, r_j/8) ⊆ D`; the finite measure
`ω_N = Φ_#(λ_b ⌞ D)` (base volume `λ_b` on `ℝ^m × ℝ`) has total mass at most
`C_m R^{m+2}` and mass at least `c_b r_j^{m+2}` on every `P(z_{j,a}, r_j)`. -/
def HasVerticalBufferedReference (R Cr Cm cb : ℝ) (N : ℕ) : Prop :=
  ∃ (G : Spatial m → ℝ → Spatial n) (p₀ : Space m),
    (∀ p p' : Space m,
      4 / 5 * dist p p' ≤ dist (timePreservingMap G p) (timePreservingMap G p') ∧
        dist (timePreservingMap G p) (timePreservingMap G p') ≤ 11 / 10 * dist p p') ∧
    (∀ j ≤ N, ∀ a ∈ F.index j, ∃ p ∈ Metric.ball p₀ (Cr * R),
      p.2.val = (F.center j a).2.val ∧
        dist (timePreservingMap G p) (F.center j a) ≤ F.scale j / 4 ∧
        Metric.ball p (F.scale j / 8) ⊆ Metric.ball p₀ (Cr * R)) ∧
    Measure.map (timePreservingMap G)
        ((parabolicVolume m).restrict (Metric.ball p₀ (Cr * R))) univ ≤
      ENNReal.ofReal (Cm * R ^ (m + 2)) ∧
    ∀ j ≤ N, ∀ a ∈ F.index j,
      ENNReal.ofReal (cb * F.scale j ^ (m + 2)) ≤
        Measure.map (timePreservingMap G)
          ((parabolicVolume m).restrict (Metric.ball p₀ (Cr * R)))
          (Metric.ball (F.center j a) (F.scale j))

/-- Buffered reference conclusion, horizontal form, for the truncation through level `N`.
The chart is a spatial map `F : ℝ^m → ℝ^n` with `0.8|u-v| ≤ |F u - F v| ≤ 1.1|u-v|`;
the base ball `D = B(u₀, C_r R)` is Euclidean; every occurrence `(j,a)`, `j ≤ N`,
has a preimage `u ∈ D` with `|F(u) - x_{j,a}| ≤ r_j/4` and `B(u, r_j/8) ⊆ D`. The
reference measure `F_#(volume ⌞ D)` is a measure on `ℝ^n`, with total mass at most
`C_m R^m` and mass at least `c_b r_j^m` on every spatial ball `B(x_{j,a}, r_j)`.
No physical time is attached to it. -/
def HasHorizontalBufferedReference (R Cr Cm cb : ℝ) (N : ℕ) : Prop :=
  ∃ (G : Spatial m → Spatial n) (u₀ : Spatial m),
    (∀ u v : Spatial m, 4 / 5 * ‖u - v‖ ≤ ‖G u - G v‖ ∧ ‖G u - G v‖ ≤ 11 / 10 * ‖u - v‖) ∧
    (∀ j ≤ N, ∀ a ∈ F.index j, ∃ u ∈ Metric.ball u₀ (Cr * R),
      ‖G u - (F.center j a).1‖ ≤ F.scale j / 4 ∧
        Metric.ball u (F.scale j / 8) ⊆ Metric.ball u₀ (Cr * R)) ∧
    Measure.map G ((volume : Measure (Spatial m)).restrict (Metric.ball u₀ (Cr * R))) univ ≤
      ENNReal.ofReal (Cm * R ^ m) ∧
    ∀ j ≤ N, ∀ a ∈ F.index j,
      ENNReal.ofReal (cb * F.scale j ^ m) ≤
        Measure.map G ((volume : Measure (Spatial m)).restrict (Metric.ball u₀ (Cr * R)))
          (Metric.ball (F.center j a).1 (F.scale j))

end CoherentFamily

namespace NeckRegion

variable {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n}
  {R c₀ Cd Cs σ δ E κ θ γ : ℝ}

/-- Vertical exact parametrization: the center set is the image of a
compact subset `A` of `ℝ^{k-2} × ℝ` under a full time-preserving map `Φ` which is
bi-Lipschitz on the whole parameter space with distortion at most `Λ`. -/
def HasVerticalParametrization (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ)
    (Λ : ℝ) : Prop :=
  ∃ (G : Spatial (k - 2) → ℝ → Spatial n) (A : Set (Space (k - 2))),
    (∀ p p' : Space (k - 2),
      Λ⁻¹ * dist p p' ≤ dist (timePreservingMap G p) (timePreservingMap G p') ∧
        dist (timePreservingMap G p) (timePreservingMap G p') ≤ Λ * dist p p') ∧
    IsCompact A ∧ timePreservingMap G '' A = N.centers

/-- Horizontal exact parametrization: a full spatial map
`F : ℝ^k → ℝ^n`, bi-Lipschitz with distortion at most `Λ`, a compact parameter set
`A ⊆ ℝ^k` and a physical time `τ` defined *only on `A`*, such that
`u ↦ (F(u), τ(u))` is bi-Lipschitz on `A` with distortion at most `Λ` and maps `A`
onto the center set. No extension of the time function to `ℝ^k` is asserted. -/
def HasHorizontalParametrization (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ)
    (Λ : ℝ) : Prop :=
  ∃ G : Spatial k → Spatial n,
    (∀ u v : Spatial k, Λ⁻¹ * ‖u - v‖ ≤ ‖G u - G v‖ ∧ ‖G u - G v‖ ≤ Λ * ‖u - v‖) ∧
    ∃ (A : Set (Spatial k)) (τ : A → ℝ), IsCompact A ∧
      (∀ u v : A,
        Λ⁻¹ * dist u v ≤ dist (point (G u) (τ u)) (point (G v) (τ v)) ∧
          dist (point (G u) (τ u)) (point (G v) (τ v)) ≤ Λ * dist u v) ∧
      Set.range (fun u : A => point (G u) (τ u)) = N.centers

/-- The local core and stopping content bound:
for every `z ∈ X` and `s > 0`,
`H^k_P(𝒞₀ ∩ P(z,s)) + ∑_{c ∈ 𝒞₊ ∩ P(z,s), d_c ≤ s} d_c^k ≤ C s^k`,
with the unnormalized parabolic Hausdorff measure `hausdorffP n k`. -/
def HasLocalContentBound (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ)
    (C : ℝ) : Prop :=
  ∀ (z : Space n) (s : ℝ), 0 < s →
    hausdorffP n k (N.core ∩ Metric.ball z s) +
        ∑' c : ↥(N.stopping ∩ Metric.ball z s ∩ {c | N.radius c ≤ s}),
          ENNReal.ofReal (N.radius c ^ k) ≤
      ENNReal.ofReal (C * s ^ k)

/-- The total core and stopping content bound
`H^k_P(𝒞₀) + ∑_{c ∈ 𝒞₊} d_c^k ≤ C' R^k`. -/
def HasTotalContentBound (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ)
    (C' : ℝ) : Prop :=
  hausdorffP n k N.core + ∑' c : ↥N.stopping, ENNReal.ofReal (N.radius c ^ k) ≤
    ENNReal.ofReal (C' * R ^ k)

/-- The core's own Hausdorff measure `η = H^k_P ⌞ 𝒞₀` has upper `k`-growth with
constant `C` at every center and radius, and positive lower `k`-density at
`η`-almost every point: `liminf_{r↓0} η(P(z,r))/r^k > 0`, written with explicit
eventual radius bounds. -/
def HasCoreDensity (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ) (C : ℝ) : Prop :=
  (∀ (z : Space n) (s : ℝ), 0 < s →
      (hausdorffP n k).restrict N.core (Metric.ball z s) ≤ ENNReal.ofReal (C * s ^ k)) ∧
    ∀ᵐ z ∂(hausdorffP n k).restrict N.core, ∃ a r₀ : ℝ, 0 < a ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        ENNReal.ofReal (a * r ^ k) ≤ (hausdorffP n k).restrict N.core (Metric.ball z r)

end NeckRegion

end ParabolicRectifiability
