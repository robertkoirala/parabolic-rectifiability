import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Foundations.SupportBounds
import ParabolicRectifiability.Measure.ScaleEnergy
import ParabolicRectifiability.Metric.Hausdorff
import ParabolicRectifiability.Metric.Measure

/-! # Statements: the independent ambient endpoint

One proposition per clause of the ambient case `k = n + 2`. These are proposition
definitions only; the corresponding theorems are `ambient_energy_zero`, `ambient_zero_graph_cover`,
`ambient_characterization`, `ambient_absolutely_continuous_density` and `ambient_local_core`.

Parts proved elsewhere are cited, not restated:
* "the full ambient space is the vertical model": every vertical model
  at `k = n + 2` is all of `X` (`ParabolicRectifiability.VerticalModel.ambient_toSet`),
  vertical models exist there (`VerticalModel.nonempty_iff`), and there is no horizontal
  model (`HorizontalModel.ambient_isEmpty`). Hence the available families at `n + 2` are
  exactly `.vertical` and `.mixed`.

The fifth clause, "the ambient core has zero remainder without an energy assumption",
is stated explicitly at every local scale `P(q,R)` by `AmbientLocalCoreStatement` below. The
theorem `ParabolicRectifiability.ambient_rectifiability : AmbientRectifiabilityStatement`
(from `ambient_retained_decomposition` and `ambientRetainedSets`) is the unit-ball case
`P(0,1)` only; it is a cross-reference and possible proof input, not the statement of the
clause.

The first clause has two forms: `AmbientEnergyZeroStatement`, for locally Radon sources, and
the separately named generalization `AmbientEnergyZeroArbitrarySourceStatement`, for an
arbitrary measure.

Conventions. The standing assumption `1 ≤ n` is
a hypothesis of every statement; the dimension is fixed to `k = n + 2`. "Locally Radon"
is `IsFiniteMeasureOnCompacts μ` together with `μ.InnerRegular`. Densities are
`lowerDensity`/`upperDensity`, `H_P^{n+2}` is `hausdorffP n (n + 2)`, `L^{n+1}` is
`parabolicVolume n`, and absolute continuity `≪` is evaluated on arbitrary sets (outer
measure). "μ-almost every" is `∀ᵐ z ∂μ`. The scale endpoint `T` is written
`R`, because `T` names the family.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- First clause, form for locally Radon sources: at `k = n + 2`, for
every locally Radon `μ` and every family available there (`Nonempty (Models n (n + 2) T)`,
i.e. `.vertical` or `.mixed`), the natural beta and the square function vanish
identically: `β²_{μ,T}(z,r) = 0` for every centre and radius `r > 0`, and
`S_{μ,T}^R(z) = 0` for every endpoint `R > 0` and centre.

The source is any nonnegative locally Radon measure. The beta conjunct says that every
available natural beta is identically zero. The availability guard is needed: for
`.horizontal` the empty infimum makes `β² = ⊤` at every positive radius. The
arbitrary-measure strengthening is the separate `AmbientEnergyZeroArbitrarySourceStatement`. -/
def AmbientEnergyZeroStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ T : FamilyKind, Nonempty (Models n (n + 2) T) →
    (∀ (z : Space n) (r : ℝ), 0 < r → betaSq μ (n + 2) T z r = 0) ∧
    (∀ R : ℝ, 0 < R → ∀ z : Space n, squareEnergy μ (n + 2) T R z = 0)

/-- Generalization of the first clause to an **arbitrary**
measure: the same conclusions as `AmbientEnergyZeroStatement`, with no hypothesis on `μ`.

This is a deliberate strengthening, kept under its
own name. It is true because the fitting cost to an
ambient vertical model is identically zero, so no regularity or finiteness of `μ` is
needed. It implies `AmbientEnergyZeroStatement` by discarding the two locally Radon
hypotheses. -/
def AmbientEnergyZeroArbitrarySourceStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ μ : Measure (Space n),
  ∀ T : FamilyKind, Nonempty (Models n (n + 2) T) →
    (∀ (z : Space n) (r : ℝ), 0 < r → betaSq μ (n + 2) T z r = 0) ∧
    (∀ R : ℝ, 0 < R → ∀ z : Space n, squareEnergy μ (n + 2) T R z = 0)

/-- Second clause: every set has the zero-graph cover.

At every positive tolerance `ε` there is a full general regular vertical graph of
dimension `n + 2` and norm at most `ε` whose function is identically zero and whose image
is all of `X`; consequently every set `E ⊆ X` is covered exactly by this one graph. In
particular every `E` is regularly `(n + 2)`-rectifiable of vertical type and of mixed
type (the typed covers of `IsRegularlyRectifiableSet`, modulo `H_P^{n+2}`). -/
def AmbientZeroGraphCoverStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ ε : ℝ, 0 < ε → ∃ G : GeneralRegularVerticalGraph n (n + 2) ε,
      (∀ p, G.function p = 0) ∧ G.image = Set.univ) ∧
    ∀ E : Set (Space n),
      IsRegularlyRectifiableSet .vertical (n + 2) E ∧
        IsRegularlyRectifiableSet .mixed (n + 2) E

/-- Third clause: for a
locally Radon `μ` on `X`, at `k = n + 2` the following are equivalent:
* regular `(n + 2)`-rectifiability of `μ`, of mixed type and, equally, of vertical type
  (`IsRegularlyRectifiableMeasure`: `μ ≪ H_P^{n+2}` and a countable carrier of typed
  graphs of finite norm);
* `μ ≪ H_P^{n+2}`;
* positive finite upper `(n + 2)`-density `μ`-almost everywhere:
  `0 < Θ^{n+2,*}(μ,z) < ∞` for `μ`-a.e. `z`.
Further equivalent forms (`μ ≪ L^{n+1}`; `Θ^{n+2,*} < ∞` a.e.;
`0 < Θ_* = Θ^* < ∞` a.e.) are not part of this statement. -/
def AmbientCharacterizationStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    (IsRegularlyRectifiableMeasure .mixed (n + 2) μ ↔ μ ≪ hausdorffP n (n + 2)) ∧
    (IsRegularlyRectifiableMeasure .vertical (n + 2) μ ↔ μ ≪ hausdorffP n (n + 2)) ∧
    (μ ≪ hausdorffP n (n + 2) ↔
      ∀ᵐ z ∂μ, 0 < upperDensity μ (n + 2) z ∧ upperDensity μ (n + 2) z < ⊤)

/-- Fourth clause:
differentiation with respect to volume. For a locally Radon source `μ ≪ L^{n+1}`
(the coordinate volume `parabolicVolume n`), at `μ`-almost every point both the lower and
the upper `(n + 2)`-density are positive and finite.

The identification of the common density value (`v_n f(z)` for `μ = f λ`) is
not part of this statement. -/
def AmbientAbsolutelyContinuousDensityStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    μ ≪ parabolicVolume n →
      ∀ᵐ z ∂μ, (0 < lowerDensity μ (n + 2) z ∧ lowerDensity μ (n + 2) z < ⊤) ∧
        (0 < upperDensity μ (n + 2) z ∧ upperDensity μ (n + 2) z < ⊤)

/-- Fifth clause: the ambient core
has zero remainder, without an energy assumption, on every cylinder `P(q,R)`.

There is a dimensional constant `C_n > 0` such that for every locally Radon `μ`, every
centre `q` and every radius `R > 0`, with `B = P(q,R)` (`Metric.ball q R`) and
`K = supp(μ⌊B)` (the actual support `(μ.restrict B).support`):
* `μ = μ⌊Bᶜ + μ⌊B`: the decomposition `μ⁺ = μ⌊Bᶜ`, `μ_V = μ⌊B`, `μ_H = 0`;
* `(μ⌊Bᶜ)(B) = 0`: zero remainder on `P(q,R)`;
* `HasRegularSupportBounds (n + 2) C_n q R ∅ K`: horizontal support `∅`, vertical support
  `K`, compact in `P̄(q,R)`, every-tolerance general regular vertical covers, and the
  global and local Hausdorff, separated-set, packing and tube bounds with constant `C_n`.

No energy hypothesis appears. The exact cover of `K` by the one zero-function full graph
`X` is `AmbientZeroGraphCoverStatement`. Sharper numerical constants
(`10^Q`, `3^Q`, `(2s)^Q`, `v_n (2R)^Q`) are absorbed into `C_n`. The theorem
`ParabolicRectifiability.ambient_rectifiability` concerns only the unit ball `P(0,1)`; it is a
cross-reference only. -/
def AmbientLocalCoreStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (q : Space n) (R : ℝ), 0 < R →
    μ = μ.restrict (Metric.ball q R)ᶜ + μ.restrict (Metric.ball q R) ∧
    (μ.restrict (Metric.ball q R)ᶜ) (Metric.ball q R) = 0 ∧
    HasRegularSupportBounds (n + 2) C q R ∅ (μ.restrict (Metric.ball q R)).support

end ParabolicRectifiability.Foundations
