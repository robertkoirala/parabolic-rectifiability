import ParabolicRectifiability.BetaP.Proofs.Counterexamples.Euclidean

/-! # The dispersed digit graph below the quadratic exponent

Definitions and proposition definitions only; the proofs are given separately.

Target: `BetaP.belowTwoDigitWitness_exists : ∃ E : Set Plane, IsBelowTwoDigitWitness E`.
The construction is a planar graph built from a dispersed digit expansion; its natural measure
has upper density in `[1/2, 2]` at every point of the set, the square functions `S_{p}` are
finite for `p < 2` and infinite for `p = 2`, and the lower density vanishes almost everywhere.

## The construction

Indices: `j ≥ 1` for `q_j, δ_j, h_j, M_j, N_j, ℓ_j, P_j`, with `ℓ_0 = h_0 = 1`.
The free choices are made explicit:
`h_j = 2^{-j-20} ℓ_{j-1}` and `M_j = 2^{j+30} = 2^{10} ℓ_{j-1}/h_j`, so that `N_j = (j+1) 2^{j+30}`,
`ℓ_j = ℓ_{j-1}/N_j`, `P_j = (j+1) ℓ_j = ℓ_{j-1}/M_j = 2^{-10} h_j` (all rational).

**Coding.** Instead of the digit-string space, every real `x` is coded by its greedy mixed-radix
digits: the `j`-th digit of `x ∈ [0,1)` is `⌊x/ℓ_j⌋ mod N_j`, and since `q_j ∣ N_j` it is marked
(`≡ 0 mod q_j`) exactly when `q_j ∣ ⌊x/ℓ_j⌋`. This defines the marked-digit indicator `b_j` on all
of `ℝ`, periodic with period `P_j` and with marked set `⋃_m [m P_j, m P_j + ℓ_j)`.
`T(x) = (x, Σ_{j≥1} h_j b_j(x))` with the right-continuous choice at the countable endpoint
set `D`.

**The set and the source.** `E = closure (T '' [0,1))`. It equals the set of points
`(x(d), y(d))` over digit strings `d`: `T(x) = (x(d), y(d))` for the greedy code `d` of
`x ∈ [0,1)`, greedy codes are dense in the compact digit space and `d ↦ (x(d), y(d))` is
continuous. The lemmas never use this identification. The source is `μ = T_#(L¹⌊[0,1))`
(`D` and `{1}` are null); it equals `H¹⌊E`.

## The statements

There are 21 statements, each proved from other statements in implication form, so that they
can be proved independently and assembled afterwards.
1. `E2sbGrid`: positivity, the nested grids, the scale identities.
2. `E2sbTails`: the numeric tail bounds.
3. `E2sbDigit`: coding and the separation property.
4. `E2sbPeriodic`: the periodic mass discrepancy.
5. `E2sbMeasurable`: Borel measurability of `b_j`, `y`, `T`.
6. `E2sbCover`: compactness and the cylinder cover `H¹(E) ≤ 1`.
7. `E2sbIdentify`: `μ = H¹⌊E` and `H¹(E) = 1`.
8. `E2sbDensity`: growth `μ(B(z,r)) ≤ 2r` and the upper density in `[1/2,2]`.
9. `E2PlanarLine`: affine lines of `ℝ²` as unit-normal equations; generic.
10. `E2sbBand`: the scale-band estimate.
11. `E2sbSpSmall`: finiteness of the square function on `(0,1/4)`.
12. `E2sbSpAll`: every positive finite endpoint.
13. `E2sbPrimitive`: the periodic integration by parts.
14. `E2Variance`: the two-height variance bound; generic.
15. `E2sbLineCost`: the cost of approximating by a line.
16. `E2sbBorelCantelli`: parent boundaries, almost everywhere.
17. `E2sbQuadBand`: the band lower bound `β_2^2 ≥ δ_j/1024`.
18. `E2sbQuadDiverge`: the divergent bands; generic in the measure.
19. `E2sbMarkedAE`: independence of the digits.
20. `E2sbLowerDensity`: the density estimate.
21. `E2sbFullSet`: the common full set in the plane from an a.e. statement in `x`.

The assembled statements are `E2sbMeasureHub`, `E2sbDensityBounds`, `E2sbSpAll`, `E2sbFullHub`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.BetaP (Plane)

/-! ## The scales -/

/-- `N_j = q_j M_j = (j+1) 2^{j+30}` (used for `j ≥ 1`). -/
def e2_sbN (j : ℕ) : ℕ := (j + 1) * 2 ^ (j + 30)

/-- `ℓ_0 = 1`, `ℓ_j = ℓ_{j-1}/N_j`: the width of the generation-`j` intervals. -/
def e2_sbEll : ℕ → ℝ
  | 0 => 1
  | j + 1 => e2_sbEll j / (e2_sbN (j + 1) : ℝ)

/-- `h_0 = 1`, `h_j = 2^{-j-20} ℓ_{j-1}` for `j ≥ 1`: the lift heights. -/
def e2_sbH : ℕ → ℝ
  | 0 => 1
  | j + 1 => e2_sbEll j / 2 ^ (j + 21)

/-- `δ_j = q_j^{-1} = (j+1)^{-1}`: the marked proportion. -/
def e2_sbDelta (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

/-- `P_j = q_j ℓ_j`: the period of the marked children. -/
def e2_sbPeriod (j : ℕ) : ℝ := ((j : ℝ) + 1) * e2_sbEll j

/-- `η_j = Σ_{i>j} h_i`: the future-height tail. -/
def e2_sbTail (j : ℕ) : ℝ := ∑' i : ℕ, e2_sbH (j + 1 + i)

/-! ## Digits, heights and the set -/

/-- The marked set of generation `j`: `b_j(x) = 1` iff `q_j = j+1` divides `⌊x/ℓ_j⌋`. -/
def e2_sbMarked (j : ℕ) : Set ℝ := {x | ((j + 1 : ℕ) : ℤ) ∣ ⌊x / e2_sbEll j⌋}

/-- The marked-digit indicator `b_j(x) ∈ {0,1}` (a real number). -/
def e2_sbBit (j : ℕ) (x : ℝ) : ℝ := (e2_sbMarked j).indicator (fun _ => (1 : ℝ)) x

/-- The height `y(x) = Σ_{j≥1} h_j b_j(x)`. -/
def e2_sbHeight (x : ℝ) : ℝ := ∑' i : ℕ, e2_sbH (i + 1) * e2_sbBit (i + 1) x

/-- The old-bit height `Y_j(x) = Σ_{1≤i≤j} h_i b_i(x)` (`Y_0 = 0`). -/
def e2_sbOldHeight (j : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range j, e2_sbH (i + 1) * e2_sbBit (i + 1) x

/-- The graph map `T(x) = (x, y(x))`. -/
def e2_sbGraph (x : ℝ) : Plane := !₂[x, e2_sbHeight x]

/-- The dispersed digit graph `E = closure (T '' [0,1))`. -/
def e2_sbSet : Set Plane := closure (e2_sbGraph '' Ico 0 1)

/-- The source `μ = T_#(L¹⌊[0,1))`. -/
def e2_sbSource : Measure Plane := (volume.restrict (Ico (0 : ℝ) 1)).map e2_sbGraph

/-! ## Statements: scales, coding, periodicity, measurability -/

/-- **Scales (`E2sbGrid`).** Positivity; `ℓ_j ≤ 1`; the nested grids
(`ℓ_i` is an integer multiple of `ℓ_j` for `i ≤ j`, and `1/ℓ_j` is an integer); for `j ≥ 1`:
`h_j = ℓ_{j-1}/2^{j+20}`, `h_j = 2^{10} P_j` (so `P_j ≤ 2^{-10} h_j`), `ℓ_{j-1} = M_j P_j` with
`M_j = 2^{j+30}`, and `0 < δ_j ≤ 1/2`. -/
def E2sbGrid : Prop :=
  (∀ j, 0 < e2_sbEll j) ∧ (∀ j, 0 < e2_sbH j) ∧ (∀ j, e2_sbEll j ≤ 1) ∧
    (∀ i j : ℕ, i ≤ j → ∃ c : ℕ, e2_sbEll i = (c : ℝ) * e2_sbEll j) ∧
    (∀ j, ∃ c : ℕ, (c : ℝ) * e2_sbEll j = 1) ∧
    (∀ j, 1 ≤ j → e2_sbH j = e2_sbEll (j - 1) / 2 ^ (j + 20)) ∧
    (∀ j, 1 ≤ j → e2_sbH j = 2 ^ 10 * e2_sbPeriod j) ∧
    (∀ j, 1 ≤ j → e2_sbEll (j - 1) = 2 ^ (j + 30) * e2_sbPeriod j) ∧
    (∀ j, 1 ≤ j → 0 < e2_sbDelta j ∧ e2_sbDelta j ≤ 1 / 2)

/-- **Tails (`E2sbTails`).** `Σ h_j < ∞`; for `j ≥ 1`:
`h_{j+1} ≤ 2^{-j-31} δ_j h_j`, `0 ≤ η_j ≤ 2 h_{j+1}`, `η_j ≤ 2^{-j-20} ℓ_j`,
`η_j ≤ 2^{-j-30} δ_j h_j`, `η_j^2 ≤ δ_j h_j^2/32`; `h` is strictly decreasing to `0`. -/
def E2sbTails : Prop :=
  Summable e2_sbH ∧
    (∀ j, 1 ≤ j → e2_sbH (j + 1) ≤ e2_sbDelta j * e2_sbH j / 2 ^ (j + 31)) ∧
    (∀ j, 0 ≤ e2_sbTail j) ∧
    (∀ j, 1 ≤ j → e2_sbTail j ≤ 2 * e2_sbH (j + 1)) ∧
    (∀ j, 1 ≤ j → e2_sbTail j ≤ e2_sbEll j / 2 ^ (j + 20)) ∧
    (∀ j, 1 ≤ j → e2_sbTail j ≤ e2_sbDelta j * e2_sbH j / 2 ^ (j + 30)) ∧
    (∀ j, 1 ≤ j → e2_sbTail j ^ 2 ≤ e2_sbDelta j * e2_sbH j ^ 2 / 32) ∧
    StrictAnti e2_sbH ∧ Tendsto e2_sbH atTop (𝓝 0)

/-- **Coding and separation (`E2sbDigit`).** (a) The bits `b_1, …, b_j` are constant on every generation-`j` interval
`[k ℓ_j, (k+1) ℓ_j)`, `k ∈ ℤ`. (b) `0 ≤ y(x) - Y_j(x) ≤ η_j`. (c) Separation: if
`|y(x) - y(x')| < h_j/2`, then `x` and `x'` have the same bits `b_1, …, b_j`. -/
def E2sbDigit : Prop :=
  (∀ j i : ℕ, 1 ≤ i → i ≤ j → ∀ (k : ℤ) (x y : ℝ),
      x ∈ Ico ((k : ℝ) * e2_sbEll j) (((k : ℝ) + 1) * e2_sbEll j) →
      y ∈ Ico ((k : ℝ) * e2_sbEll j) (((k : ℝ) + 1) * e2_sbEll j) →
      e2_sbBit i x = e2_sbBit i y) ∧
    (∀ (j : ℕ) (x : ℝ), 0 ≤ e2_sbHeight x - e2_sbOldHeight j x ∧
      e2_sbHeight x - e2_sbOldHeight j x ≤ e2_sbTail j) ∧
    (∀ (j : ℕ) (x y : ℝ), |e2_sbHeight x - e2_sbHeight y| < e2_sbH j / 2 →
      ∀ i : ℕ, 1 ≤ i → i ≤ j → e2_sbBit i x = e2_sbBit i y)

/-- **Periodicity (`E2sbPeriodic`).** For `j ≥ 1`: the discrepancy
`|∫_a^b b_j - δ_j (b - a)| ≤ 2 δ_j P_j` on every bounded interval (the mass discrepancy), and
`L¹{x : |x - x₀| < r, b_j(x) = 1} ≤ 3 δ_j r` for `r ≥ h_j/4` and every real `x₀`. -/
def E2sbPeriodic : Prop :=
  (∀ j, 1 ≤ j → ∀ a b : ℝ, a ≤ b →
      |(∫ x in a..b, e2_sbBit j x) - e2_sbDelta j * (b - a)| ≤
        2 * e2_sbDelta j * e2_sbPeriod j) ∧
    ∀ j, 1 ≤ j → ∀ x₀ r : ℝ, e2_sbH j / 4 ≤ r →
      volume (Ioo (x₀ - r) (x₀ + r) ∩ e2_sbMarked j) ≤ ENNReal.ofReal (3 * e2_sbDelta j * r)

/-- **Measurability (`E2sbMeasurable`).** The marked sets are Borel, and `y` and `T`
are Borel measurable. -/
def E2sbMeasurable : Prop :=
  (∀ j, MeasurableSet (e2_sbMarked j)) ∧ Measurable e2_sbHeight ∧ Measurable e2_sbGraph

/-! ## Statements: the natural measure and the density -/

/-- **Cylinder cover (`E2sbCover`).** `E` is compact and
`H¹(E) ≤ 1` (the generation-`j` cylinder rectangles `I_w × [Y_w, Y_w + η_j]` cover `E`, there are
`1/ℓ_j` of them, each of diameter `√(ℓ_j^2 + η_j^2)`, and `η_j/ℓ_j → 0`). -/
def E2sbCover : Prop :=
  IsCompact e2_sbSet ∧ μH[1] e2_sbSet ≤ 1

/-- **The natural measure (`E2sbIdentify`).** `μ = H¹⌊E` and
`H¹(E) = 1` (projection is one-Lipschitz and `π₁ ∘ T = id`, so `μ ≤ H¹⌊E` on Borel sets; both
have total mass at most one and `μ` is a probability). -/
def E2sbIdentify : Prop :=
  μH[1].restrict e2_sbSet = e2_sbSource ∧ μH[1] e2_sbSet = 1

/-- **Density bounds (`E2sbDensityBounds`).** At every point of `E` the planar upper
one-density of `μ` lies in `[1/2, 2]`. -/
def E2sbDensityBounds : Prop :=
  ∀ z ∈ e2_sbSet, (2 : ℝ≥0∞)⁻¹ ≤ BetaP.planarUpperDensity e2_sbSource z ∧
    BetaP.planarUpperDensity e2_sbSource z ≤ 2

/-- **Growth and density (`E2sbDensity`).** The global growth bound
`μ(B(z,r)) ≤ 2r` for every `z ∈ ℝ²` and `r > 0`, and the density bounds. -/
def E2sbDensity : Prop :=
  (∀ (z : Plane) (r : ℝ), 0 < r → e2_sbSource (Metric.ball z r) ≤ ENNReal.ofReal (2 * r)) ∧
    E2sbDensityBounds

/-- **The set and its measure (`E2sbMeasureHub`).** `E` is compact, `H¹(E) = 1` and `H¹⌊E = μ`. -/
def E2sbMeasureHub : Prop :=
  IsCompact e2_sbSet ∧ μH[1] e2_sbSet = 1 ∧ μH[1].restrict e2_sbSet = e2_sbSource

/-! ## Statements: finiteness of every subquadratic square function -/

/-- **Planar lines (`E2PlanarLine`, generic).** The affine lines of `ℝ²` (`AffineSpatialPlane 2 1`)
are exactly the sets `{a w₀ + b w₁ = c}` with `a^2 + b^2 = 1`, with
`dist(w, L) = |a w₀ + b w₁ - c|` (as `Metric.infEDist`). -/
def E2PlanarLine : Prop :=
  (∀ L : AffineSpatialPlane 2 1, ∃ a b c : ℝ, a ^ 2 + b ^ 2 = 1 ∧
      ∀ w : Plane, Metric.infEDist w L.toSet = ENNReal.ofReal |a * w 0 + b * w 1 - c|) ∧
    ∀ a b c : ℝ, a ^ 2 + b ^ 2 = 1 → ∃ L : AffineSpatialPlane 2 1,
      ∀ w : Plane, Metric.infEDist w L.toSet = ENNReal.ofReal |a * w 0 + b * w 1 - c|

/-- **Band estimate (`E2sbBand`).** For every `p > 0` there
is `C_p ≥ 0` with, for every `z ∈ E`, `j ≥ 1` and `h_j/4 ≤ r < h_{j-1}/4`,
`β_{p,μ}(z,r)^2 ≤ C_p [δ_j^{2/p} (h_j/r)^2 + (η_j/r)^2]`. -/
def E2sbBand : Prop :=
  ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ e2_sbSet, ∀ j : ℕ, 1 ≤ j → ∀ r : ℝ,
    e2_sbH j / 4 ≤ r → r < e2_sbH (j - 1) / 4 →
      euclideanBetaPow e2_sbSource 1 p z r ^ (2 / p) ≤
        ENNReal.ofReal (C * (e2_sbDelta j ^ (2 / p) * (e2_sbH j / r) ^ 2 + (e2_sbTail j / r) ^ 2))

/-- **Small scales (`E2sbSpSmall`).** For `0 < p < 2`, `S_{p,μ}^{1/4}`
is bounded on `E` by a constant depending on `p` only. -/
def E2sbSpSmall : Prop :=
  ∀ p : ℝ, 0 < p → p < 2 → ∃ B : ℝ, ∀ z ∈ e2_sbSet,
    euclideanEnergyS e2_sbSource 1 p (1 / 4) z ≤ ENNReal.ofReal B

/-- **All finite endpoints (`E2sbSpAll`).** For `0 < p < 2` and
every finite `a > 0`, `S_{p,μ}^a` is bounded on `E` by a constant depending on `p` and `a` only
(the bounded annulus `[1/4, a)` uses a line through the centre). -/
def E2sbSpAll : Prop :=
  ∀ p : ℝ, 0 < p → p < 2 → ∀ a : ℝ, 0 < a → ∃ B : ℝ, ∀ z ∈ e2_sbSet,
    euclideanEnergyS e2_sbSource 1 p a z ≤ ENNReal.ofReal B

/-! ## Statements: quadratic divergence -/

/-- **Periodic primitive (`E2sbPrimitive`).** For `j ≥ 1`, every centre
`x₀` and `h > 0`: `|∫_{-h}^{h} X (b_j(x₀+X) - δ_j) dX| ≤ 4 δ_j P_j h` (integration by parts
against the periodic primitive `F` of `b_j - δ_j`, `0 ≤ F ≤ δ_j P_j`). -/
def E2sbPrimitive : Prop :=
  ∀ j, 1 ≤ j → ∀ x₀ h : ℝ, 0 < h →
    |∫ X in (-h)..h, X * (e2_sbBit j (x₀ + X) - e2_sbDelta j)| ≤
      4 * e2_sbDelta j * e2_sbPeriod j * h

/-- **Two-height variance (`E2Variance`, generic).** Let `h > 0`,
`0 < δ ≤ 1/2`, `0 < P ≤ 2^{-10} h`, and `β` a Borel `{0,1}`-valued function with mean
discrepancy `|∫_{-h}^{h} β - 2hδ| ≤ 2δP` and covariance `|∫_{-h}^{h} X(β(X) - δ)| ≤ 4δPh`. Then
for every unit `(a,b)` and every `c`, `∫_{-h}^{h} (aX + bhβ(X) - c)^2 dX ≥ δh^3/4`. -/
def E2Variance : Prop :=
  ∀ (h δ P : ℝ) (β : ℝ → ℝ), 0 < h → 0 < δ → δ ≤ 1 / 2 → 0 < P → 2 ^ 10 * P ≤ h →
    Measurable β → (∀ X, β X = 0 ∨ β X = 1) →
    |(∫ X in (-h)..h, β X) - 2 * h * δ| ≤ 2 * δ * P →
    |∫ X in (-h)..h, X * (β X - δ)| ≤ 4 * δ * P * h →
    ∀ a b c : ℝ, a ^ 2 + b ^ 2 = 1 →
      δ * h ^ 3 / 4 ≤ ∫ X in (-h)..h, (a * X + b * h * β X - c) ^ 2

/-- **Line cost (`E2sbLineCost`).** For `j ≥ 1` and
`J = (x₀ - h_j, x₀ + h_j)` inside one generation-`(j-1)` interval `[kℓ_{j-1}, (k+1)ℓ_{j-1}]`
(`k ∈ ℤ`), every affine line `L` has `∫_J dist(T(x), L)^2 dx ≥ δ_j h_j^3/16`. -/
def E2sbLineCost : Prop :=
  ∀ j, 1 ≤ j → ∀ (k : ℤ) (x₀ : ℝ), (k : ℝ) * e2_sbEll (j - 1) ≤ x₀ - e2_sbH j →
    x₀ + e2_sbH j ≤ ((k : ℝ) + 1) * e2_sbEll (j - 1) →
    ∀ L : AffineSpatialPlane 2 1,
      ENNReal.ofReal (e2_sbDelta j * e2_sbH j ^ 3 / 16) ≤
        ∫⁻ x in Ioo (x₀ - e2_sbH j) (x₀ + e2_sbH j),
          Metric.infEDist (e2_sbGraph x) L.toSet ^ (2 : ℝ)

/-- **Parent boundaries (`E2sbBorelCantelli`).** For `L¹`-a.e. `x ∈ [0,1)`,
for all large `j`, `[x - h_j, x + h_j]` lies in one generation-`(j-1)` interval. -/
def E2sbBorelCantelli : Prop :=
  ∀ᵐ x ∂(volume.restrict (Ico (0 : ℝ) 1)), ∀ᶠ j in atTop, ∃ k : ℤ,
    (k : ℝ) * e2_sbEll (j - 1) ≤ x - e2_sbH j ∧ x + e2_sbH j ≤ ((k : ℝ) + 1) * e2_sbEll (j - 1)

/-- **Quadratic band bound (`E2sbQuadBand`).** For `j ≥ 1`, `x₀ ∈ [0,1)` with
`[x₀ - h_j, x₀ + h_j]` inside a generation-`(j-1)` interval, and `3h_j ≤ r ≤ 4h_j`:
`β_{2,μ}(T(x₀), r)^2 ≥ δ_j/1024`. -/
def E2sbQuadBand : Prop :=
  ∀ j, 1 ≤ j → ∀ (k : ℤ) (x₀ : ℝ), x₀ ∈ Ico (0 : ℝ) 1 →
    (k : ℝ) * e2_sbEll (j - 1) ≤ x₀ - e2_sbH j → x₀ + e2_sbH j ≤ ((k : ℝ) + 1) * e2_sbEll (j - 1) →
    ∀ r : ℝ, 3 * e2_sbH j ≤ r → r ≤ 4 * e2_sbH j →
      ENNReal.ofReal (e2_sbDelta j / 1024) ≤ euclideanBetaPow e2_sbSource 1 2 (e2_sbGraph x₀) r

/-- **Divergent bands (`E2sbQuadDiverge`, generic in the measure).** If for
all large `j` the band bound `β_{2,ν}(z,r)^2 ≥ δ_j/1024` holds on `[3h_j, 4h_j]`, then
`S_{2,ν}^a(z) = ∞` for every `a > 0` (the bands are disjoint, each has `dr/r`-length `log(4/3)`,
and `Σ δ_j = ∞`). -/
def E2sbQuadDiverge : Prop :=
  ∀ (ν : Measure Plane) (z : Plane),
    (∀ᶠ j in atTop, ∀ r : ℝ, 3 * e2_sbH j ≤ r → r ≤ 4 * e2_sbH j →
      ENNReal.ofReal (e2_sbDelta j / 1024) ≤ euclideanBetaPow ν 1 2 z r) →
    ∀ a : ℝ, 0 < a → euclideanEnergyS ν 1 2 a z = ⊤

/-! ## Statements: vanishing lower density and the full set -/

/-- **Marked digits (`E2sbMarkedAE`).** `L¹`-a.e. `x ∈ [0,1)` has
infinitely many marked digits (`L¹{b_m = … = b_N = 0} = m/(N+1)` on `[0,1)`). -/
def E2sbMarkedAE : Prop :=
  ∀ᵐ x ∂(volume.restrict (Ico (0 : ℝ) 1)), ∃ᶠ j in atTop, x ∈ e2_sbMarked j

/-- **Lower density (`E2sbLowerDensity`).** If `x₀` has infinitely
many marked digits, the planar lower one-density of `μ` at `T(x₀)` is zero (along `r = h_j/4`
with `b_j(x₀) = 1`, `μ(B(T(x₀), r))/r ≤ 3δ_j`). -/
def E2sbLowerDensity : Prop :=
  ∀ x₀ : ℝ, (∃ᶠ j in atTop, x₀ ∈ e2_sbMarked j) →
    BetaP.planarLowerDensity e2_sbSource (e2_sbGraph x₀) = 0

/-- **Common full set (`E2sbFullSet`).** A property that
holds at `T(x)` for `L¹`-a.e. `x ∈ [0,1)` holds on a set `G ⊆ ℝ²` of full `μ`-measure. -/
def E2sbFullSet : Prop :=
  ∀ P : Plane → Prop, (∀ᵐ x ∂(volume.restrict (Ico (0 : ℝ) 1)), P (e2_sbGraph x)) →
    ∃ G : Set Plane, e2_sbSource Gᶜ = 0 ∧ ∀ z ∈ G, P z

/-- **Divergence and vanishing lower density (`E2sbFullHub`).** On one common set of full `μ`-measure,
`S_{2,μ}^a = ∞` for every `a > 0` and the planar lower one-density of `μ` vanishes. -/
def E2sbFullHub : Prop :=
  ∃ G : Set Plane, e2_sbSource Gᶜ = 0 ∧ ∀ z ∈ G,
    (∀ a : ℝ, 0 < a → euclideanEnergyS e2_sbSource 1 2 a z = ⊤) ∧
      BetaP.planarLowerDensity e2_sbSource z = 0

end ParabolicRectifiability.Examples
