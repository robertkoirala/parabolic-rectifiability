import ParabolicRectifiability.Examples.Lacunary
import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements
import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiabilityStatements

/-! # The decorated-segment witness above the quadratic exponent

Definitions and intermediate statements (as `Prop`s) for the planar witness `E₊` used to prove
`BetaP.DirectWitnessPlusStatement`: a countable union of horizontal segments in the plane with
`1 ≤ H¹(E₊) ≤ 100/99`, density `2` almost everywhere, a divergent Euclidean square energy
`S^{a}_{p} = ∞` off a countable endpoint set for every `p > 2`, and whose time slice is covered by
countably many horizontal graphs of slope zero. Nothing is proved here; the proofs are assembled
in `AboveTwoSegmentLeaves` and `AboveTwoSegmentGlue`.

## The construction

A labelled segment is a triple `(a, L, b)` standing for `[a, a+L] × {b}`. For `j ≥ 1` and
`0 ≤ m < N_j = 8^{j+1}`, with `h = L/N_j`, its child `J_{j,m}` is
`[a + (m+1/2)h - δ_j h/2, a + (m+1/2)h + δ_j h/2] × {b + h}`, i.e. the triple
`(a + (m+1/2)h - δ_j h/2, δ_j h, b + h)`. A label is a list of pairs `(j,m)`, newest first; the
empty label is the root `[0,1] × {0}` and `(j,m) :: l` is the child `J_{j,m}` of the segment
of `l`. A label is valid when every pair has `j ≥ 1` and `m < N_j`. Labels are coded by natural
numbers through `Denumerable (List (ℕ × ℕ))`; `e2_sapIndex ⊆ ℕ` is the set of codes of valid
labels, so `E = e2_sapSet` is literally the union `⋃_{i ∈ I} [u_i, v_i] × {b_i}` required by
`DirectWitnessPlusStatement` (labels are kept; coinciding segments are not merged). The
closure of `E` is not taken.

## Intermediate statements

Weights: `E2sapWeights`, `E2sapWeightsDiverge`.
The fitting lemma: `E2sapFitTilted`, `E2sapFit`.
Segments as intervals: `E2sapLevelMeasureStatement`, `E2sapSegment`.
Band lower bound for the beta numbers: `E2sapPairCost`, `E2sapBallContain`, `E2sapBandBeta`.
Divergence of the energy: `E2sapCell`, `E2sapBandEnergy`, `E2sapDivergenceOff`.
Mass: `E2sapLabelBounds`, `E2sapSetBasic`, `E2sapGeneration`, `E2sapTreeLength`, `E2sapMass`.
Density: `E2sapLevels`, `E2sapLevelPoint`, `E2sapLevelAE`, `E2sapDensity`.
Zero-slope cover: `E2sapCover`.
Two further inputs are shared with the witnesses below the quadratic exponent: `E2PlanarLine`
(proved by `e2_planarLine`) and `E2sbSlopeGraph` (proved by `e2_sb_slopeGraph`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.BetaP (Plane horizontalSegment timeSlice planarDensityRatio)

/-! ## The weights and the scales -/

/-- `δ_j = 1/(100 (j+1) (1 + log(j+1))^2)`. Defined for every `j`; the construction
uses `j ≥ 1`. -/
def e2_sapDelta (j : ℕ) : ℝ :=
  1 / (100 * ((j : ℝ) + 1) * (1 + Real.log ((j : ℝ) + 1)) ^ 2)

/-- `N_j = 8^{j+1}`. -/
def e2_sapN (j : ℕ) : ℕ := 8 ^ (j + 1)

/-! ## The labelled tree of segments -/

/-- The child `J_{j,m}` of the labelled segment `s = (a, L, b)`, i.e. of `[a, a+L] × {b}`:
with `h = L/N_j`, the triple `(a + (m+1/2)h - δ_j h/2, δ_j h, b + h)`. -/
def e2_sapChild (s : ℝ × ℝ × ℝ) (j m : ℕ) : ℝ × ℝ × ℝ :=
  (s.1 + ((m : ℝ) + 1 / 2) * (s.2.1 / (e2_sapN j : ℝ)) -
      e2_sapDelta j * (s.2.1 / (e2_sapN j : ℝ)) / 2,
    e2_sapDelta j * (s.2.1 / (e2_sapN j : ℝ)),
    s.2.2 + s.2.1 / (e2_sapN j : ℝ))

/-- The labelled segment of a label (newest pair first): the root `(0, 1, 0)` for the empty
label, and the child `J_{j,m}` of the segment of `l` for `(j,m) :: l`. -/
def e2_sapSeg : List (ℕ × ℕ) → ℝ × ℝ × ℝ
  | [] => (0, 1, 0)
  | q :: l => e2_sapChild (e2_sapSeg l) q.1 q.2

/-- A label is valid when every pair `(j,m)` has `j ≥ 1` and `m < N_j`. -/
def e2_sapValid (l : List (ℕ × ℕ)) : Prop :=
  ∀ q ∈ l, 1 ≤ q.1 ∧ q.2 < e2_sapN q.1

/-- The label coded by `n` (`Denumerable (List (ℕ × ℕ))`). -/
def e2_sapLabel (n : ℕ) : List (ℕ × ℕ) :=
  Denumerable.ofNat (List (ℕ × ℕ)) n

/-- The index set `I ⊆ ℕ`: the codes of valid labels. -/
def e2_sapIndex : Set ℕ :=
  {n | e2_sapValid (e2_sapLabel n)}

/-- Left end `a` of the segment with code `n`. -/
def e2_sapLeft (n : ℕ) : ℝ := (e2_sapSeg (e2_sapLabel n)).1

/-- Length `L` of the segment with code `n`. -/
def e2_sapLength (n : ℕ) : ℝ := (e2_sapSeg (e2_sapLabel n)).2.1

/-- Right end `a + L` of the segment with code `n`. -/
def e2_sapRight (n : ℕ) : ℝ := e2_sapLeft n + e2_sapLength n

/-- Height `b` of the segment with code `n`. -/
def e2_sapHeight (n : ℕ) : ℝ := (e2_sapSeg (e2_sapLabel n)).2.2

/-- The witness `E₊ = ⋃_{i ∈ I} [a_i, a_i + L_i] × {b_i}`: the union of all generations, root
included, without closure. -/
def e2_sapSet : Set Plane :=
  ⋃ i : e2_sapIndex, horizontalSegment (e2_sapLeft i) (e2_sapRight i) (e2_sapHeight i)

/-- The planar point `(s, c)`. -/
def e2_sapPt (s c : ℝ) : Plane := !₂[s, c]

/-- The exceptional set `Z` of the divergence statement: the endpoints of all labelled
segments. -/
def e2_sapEndpoints : Set Plane :=
  ⋃ i : e2_sapIndex,
    {e2_sapPt (e2_sapLeft i) (e2_sapHeight i), e2_sapPt (e2_sapRight i) (e2_sapHeight i)}

/-- The constant `c_p = 4^{-p} min{1, 2/(p+1)}` of the fitting lemma `E2sapFit`. -/
def e2_sapFitConst (p : ℝ) : ℝ := (4 : ℝ) ^ (-p) * min 1 (2 / (p + 1))

/-! ## Levels -/

/-- The level measure `Σ_k (s ↦ (s, c_k))_# (L¹⌊A_k)`. -/
def e2_sapLevelMeasure (c : ℕ → ℝ) (A : ℕ → Set ℝ) : Measure Plane :=
  Measure.sum fun k => (volume.restrict (A k)).map (fun s => e2_sapPt s (c k))

/-- The tail `g_N = Σ_{k > N} 1_{A_k}`, with values in `ℝ≥0∞`. -/
def e2_sapTail (A : ℕ → Set ℝ) (N : ℕ) (u : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, (A (N + 1 + k)).indicator (fun _ => (1 : ℝ≥0∞)) u

/-! ## The weights: intermediate statements -/

/-- **The weights.** `0 < δ_j < 1/4` for every
`j`, and `D = Σ_{j ≥ 1} δ_j` converges with `D ≤ 1/100`. -/
def E2sapWeights : Prop :=
  (∀ j : ℕ, 0 < e2_sapDelta j ∧ e2_sapDelta j < 1 / 4) ∧
    Summable (fun j : ℕ => e2_sapDelta (j + 1)) ∧ ∑' j : ℕ, e2_sapDelta (j + 1) ≤ 1 / 100

/-- **Divergence of the powered weights.** `Σ_j δ_j^q = ∞` for every
`0 < q < 1` (the sum over all `j ≥ 0`; one extra finite term does not change divergence). -/
def E2sapWeightsDiverge : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 → ∑' j : ℕ, ENNReal.ofReal (e2_sapDelta j ^ q) = ⊤

/-! ## The fitting lemma -/

/-- **The fitting lemma, tilted lines.** For `p ≥ 1`, `h > 0`
and a tilted line (`|α| ≥ 1/4`), `∫_{-h}^{h} |αs - c|^p ds ≥ 2·4^{-p} h^{p+1}/(p+1)`. -/
def E2sapFitTilted : Prop :=
  ∀ p : ℝ, 1 ≤ p → ∀ h : ℝ, 0 < h → ∀ α c : ℝ, 1 / 4 ≤ |α| →
    ENNReal.ofReal (2 * (4 : ℝ) ^ (-p) / (p + 1) * h ^ (p + 1)) ≤
      ∫⁻ s in Icc (-h) h, ENNReal.ofReal |α * s - c| ^ p

/-- **The fitting lemma, in parameter form.** For `p > 2`,
`h > 0`, `0 < δ ≤ 1/4`, `|ξ| ≤ h/2`, and every unit normal `(α, β)` and offset `c` (the line
`{αu + βv = c}`): the baseline `[-h,h] × {0}` and the satellite
`[ξ - δh/2, ξ + δh/2] × {h}` together cost at least `c_p δ h^{p+1}`. -/
def E2sapFit : Prop :=
  ∀ p : ℝ, 2 < p → ∀ h δ ξ : ℝ, 0 < h → 0 < δ → δ ≤ 1 / 4 → |ξ| ≤ h / 2 →
    ∀ α β c : ℝ, α ^ 2 + β ^ 2 = 1 →
      ENNReal.ofReal (e2_sapFitConst p * δ * h ^ (p + 1)) ≤
        (∫⁻ s in Icc (-h) h, ENNReal.ofReal |α * s - c| ^ p) +
          ∫⁻ s in Icc (ξ - δ * h / 2) (ξ + δ * h / 2), ENNReal.ofReal |α * s + β * h - c| ^ p

/-! ## Horizontal segments are intervals -/

/-- **Arclength on one level.** For every height `c`
and Borel `A ⊆ ℝ`, `H¹⌊((s ↦ (s,c))(A)) = (s ↦ (s,c))_# (L¹⌊A)`. -/
def E2sapLevelMeasureStatement : Prop :=
  ∀ (c : ℝ) (A : Set ℝ), MeasurableSet A →
    μH[1].restrict ((fun s => e2_sapPt s c) '' A) =
      (volume.restrict A).map (fun s => e2_sapPt s c)

/-- **The arclength value of `H¹` on a segment.** For
`u ≤ v`: `[u,v] × {b}` is the image of `[u,v]` under `s ↦ (s,b)`, has `H¹` equal to `v - u`, and
every `H¹`-integral over it is the parameter integral. -/
def E2sapSegment : Prop :=
  ∀ u v b : ℝ, u ≤ v →
    horizontalSegment u v b = (fun s => e2_sapPt s b) '' Icc u v ∧
      μH[1] (horizontalSegment u v b) = ENNReal.ofReal (v - u) ∧
      ∀ f : Plane → ℝ≥0∞,
        ∫⁻ w in horizontalSegment u v b, f w ∂μH[1] = ∫⁻ s in Icc u v, f (e2_sapPt s b)

/-! ## The band lower bound -/

/-- **The fitting lemma translated by `z = (x,y)`.** For
`p > 2`, `h > 0`, `0 < δ ≤ 1/4`, `|ξ| ≤ h/2`, the baseline `[x-h, x+h] × {y}` and the satellite
`[x+ξ-δh/2, x+ξ+δh/2] × {y+h}` cost, against every affine line `U`, at least `c_p δ h^{p+1}`
for `H¹`. -/
def E2sapPairCost : Prop :=
  ∀ p : ℝ, 2 < p → ∀ x y h δ ξ : ℝ, 0 < h → 0 < δ → δ ≤ 1 / 4 → |ξ| ≤ h / 2 →
    ∀ U : AffineSpatialPlane 2 1,
      ENNReal.ofReal (e2_sapFitConst p * δ * h ^ (p + 1)) ≤
        (∫⁻ w in horizontalSegment (x - h) (x + h) y, Metric.infEDist w U.toSet ^ p ∂μH[1]) +
          ∫⁻ w in horizontalSegment (x + ξ - δ * h / 2) (x + ξ + δ * h / 2) (y + h),
            Metric.infEDist w U.toSet ^ p ∂μH[1]

/-- **Both segments lie in the ball.** For `h > 0`, `0 ≤ δ ≤ 1/4`,
`|ξ| ≤ h/2` and `r ≥ 2h`, the baseline and the satellite lie in the open ball `B((x,y), r)`. -/
def E2sapBallContain : Prop :=
  ∀ x y h δ ξ r : ℝ, 0 < h → 0 ≤ δ → δ ≤ 1 / 4 → |ξ| ≤ h / 2 → 2 * h ≤ r →
    horizontalSegment (x - h) (x + h) y ⊆ Metric.ball (e2_sapPt x y) r ∧
      horizontalSegment (x + ξ - δ * h / 2) (x + ξ + δ * h / 2) (y + h) ⊆
        Metric.ball (e2_sapPt x y) r

/-- **The band lower bound for the beta numbers.** For any set
`E ⊇` baseline `∪` satellite (with the hypotheses of `E2sapPairCost`), at every radius
`2h ≤ r ≤ 4h`: `β^E_{p,H¹⌊E}((x,y), r)^p ≥ A_p δ` with `A_p = c_p 4^{-p-1}`. -/
def E2sapBandBeta : Prop :=
  ∀ (E : Set Plane) (p : ℝ), 2 < p → ∀ x y h δ ξ : ℝ, 0 < h → 0 < δ → δ ≤ 1 / 4 →
    |ξ| ≤ h / 2 →
    horizontalSegment (x - h) (x + h) y ⊆ E →
    horizontalSegment (x + ξ - δ * h / 2) (x + ξ + δ * h / 2) (y + h) ⊆ E →
    ∀ r : ℝ, 2 * h ≤ r → r ≤ 4 * h →
      ENNReal.ofReal (e2_sapFitConst p * (4 : ℝ) ^ (-p - 1) * δ) ≤
        euclideanBetaPow (μH[1].restrict E) 1 p (e2_sapPt x y) r

/-! ## The divergence -/

/-- **Nearest cell midpoint.** For `L > 0`, `a ≤ x < a + L` and
every `j`, one of the `N_j` cell midpoints `a + (m+1/2) L/N_j` is within `(L/N_j)/2` of `x`. -/
def E2sapCell : Prop :=
  ∀ (a L x : ℝ) (j : ℕ), 0 < L → a ≤ x → x < a + L →
    ∃ m : ℕ, m < e2_sapN j ∧
      |a + ((m : ℝ) + 1 / 2) * (L / (e2_sapN j : ℝ)) - x| ≤ L / (e2_sapN j : ℝ) / 2

/-- **Divergence on disjoint bands (generic).** Let `H > 0`,
`A > 0`, `p > 2`, `a > 0`, `d ≥ 0` with `Σ_j d_j^{2/p} = ∞`. If `f(r) ≥ A d_j` on the band
`[2H/N_j, 4H/N_j]` for every `j ≥ j₀`, then `∫_0^a f^{2/p} dr/r = ∞` (the bands are disjoint,
each has `dr/r`-length `log 2`, and all but finitely many lie in `(0,a)`). -/
def E2sapBandEnergy : Prop :=
  ∀ (f : ℝ → ℝ≥0∞) (d : ℕ → ℝ) (H A p a : ℝ) (j₀ : ℕ), 0 < H → 0 < A → 2 < p → 0 < a →
    (∀ j, 0 ≤ d j) → ∑' j : ℕ, ENNReal.ofReal (d j ^ (2 / p)) = ⊤ →
    (∀ j : ℕ, j₀ ≤ j → ∀ r : ℝ, 2 * (H / (e2_sapN j : ℝ)) ≤ r → r ≤ 4 * (H / (e2_sapN j : ℝ)) →
      ENNReal.ofReal (A * d j) ≤ f r) →
    ∫⁻ r in Ioo 0 a, f r ^ (2 / p) ∂scaleMeasure = ⊤

/-! ## The mass -/

/-- **Bounds of the labelled segments.** Every labelled segment is
nondegenerate, lies above `[0,1]`, and has height in `[0,1]`. -/
def E2sapLabelBounds : Prop :=
  ∀ n ∈ e2_sapIndex, e2_sapLeft n < e2_sapRight n ∧ 0 ≤ e2_sapLeft n ∧ e2_sapRight n ≤ 1 ∧
    0 ≤ e2_sapHeight n ∧ e2_sapHeight n ≤ 1

/-- `E` is Borel and
bounded. -/
def E2sapSetBasic : Prop :=
  MeasurableSet e2_sapSet ∧ Bornology.IsBounded e2_sapSet

/-- **Generation lengths.** The total labelled length of
generation `g` is `D^g`, with `D = Σ_{j≥1} δ_j` (in `ℝ≥0∞`). -/
def E2sapGeneration : Prop :=
  ∀ g : ℕ, ∑' l : {l : List (ℕ × ℕ) // e2_sapValid l ∧ l.length = g},
      ENNReal.ofReal (e2_sapSeg l.1).2.1 = (∑' j : ℕ, ENNReal.ofReal (e2_sapDelta (j + 1))) ^ g

/-- **Total labelled length.** The total labelled length of
all generations is at most `Σ_g D^g = 1/(1-D) ≤ 100/99`. -/
def E2sapTreeLength : Prop :=
  ∑' i : e2_sapIndex, ENNReal.ofReal (e2_sapLength i) ≤ ENNReal.ofReal (100 / 99)

/-- **The mass.** `1 ≤ H¹(E) ≤ 100/99`. -/
def E2sapMass : Prop :=
  1 ≤ μH[1] e2_sapSet ∧ μH[1] e2_sapSet ≤ ENNReal.ofReal (100 / 99)

/-- **Divergence of the energy.** Outside the endpoint
set `Z`, every point of `E` has `S^{a,E}_{p,H¹⌊E} = ∞` for every `p > 2` and every `a > 0`. -/
def E2sapDivergenceOff : Prop :=
  ∀ z ∈ e2_sapSet \ e2_sapEndpoints, ∀ p : ℝ, 2 < p → ∀ a : ℝ, 0 < a →
    euclideanEnergyS (μH[1].restrict e2_sapSet) 1 p a z = ⊤

/-! ## The density -/

/-- **Decomposition into levels.** For every countable family of
horizontal segments with union `F`, there are pairwise distinct heights `c_k` and Borel sets
`A_k ⊆ ℝ` with `H¹⌊F = Σ_k (s ↦ (s, c_k))_# (L¹⌊A_k)`. -/
def E2sapLevels : Prop :=
  ∀ (I : Set ℕ) (u v b : I → ℝ),
    ∃ (c : ℕ → ℝ) (A : ℕ → Set ℝ), Function.Injective c ∧ (∀ k, MeasurableSet (A k)) ∧
      μH[1].restrict (⋃ i, horizontalSegment (u i) (v i) (b i)) = e2_sapLevelMeasure c A

/-- **Density at a good point.** For distinct
heights and Borel levels, if `s` is a Lebesgue density point of `A_m`, a Lebesgue point of every
tail `g_N`, and `g_N(s) → 0`, then `ν(B((s, c_m), r))/r → 2` for the level measure `ν`. -/
def E2sapLevelPoint : Prop :=
  ∀ (c : ℕ → ℝ) (A : ℕ → Set ℝ), Function.Injective c → (∀ k, MeasurableSet (A k)) →
    ∀ (m : ℕ) (s : ℝ), IsLebesgueDensityPoint (A m) s →
    (∀ N : ℕ, Tendsto (fun r => (∫⁻ u in Metric.closedBall s r, e2_sapTail A N u) /
        volume (Metric.closedBall s r)) (𝓝[>] 0) (𝓝 (e2_sapTail A N s))) →
    Tendsto (fun N => e2_sapTail A N s) atTop (𝓝 0) →
    Tendsto (planarDensityRatio (e2_sapLevelMeasure c A) (e2_sapPt s (c m))) (𝓝[>] 0) (𝓝 2)

/-- **One-dimensional Lebesgue differentiation on the levels.** If `Σ_k |A_k| < ∞`, then for every `m`, `L¹`-a.e. `s ∈ A_m` is a Lebesgue
density point of `A_m` and a Lebesgue point of every tail `g_N`, and `g_N(s) → 0`. -/
def E2sapLevelAE : Prop :=
  ∀ A : ℕ → Set ℝ, (∀ k, MeasurableSet (A k)) → ∑' k, volume (A k) ≠ ⊤ → ∀ m : ℕ,
    ∀ᵐ s ∂(volume.restrict (A m)), IsLebesgueDensityPoint (A m) s ∧
      (∀ N : ℕ, Tendsto (fun r => (∫⁻ u in Metric.closedBall s r, e2_sapTail A N u) /
        volume (Metric.closedBall s r)) (𝓝[>] 0) (𝓝 (e2_sapTail A N s))) ∧
      Tendsto (fun N => e2_sapTail A N s) atTop (𝓝 0)

/-- **Density of countable unions of horizontal segments.** For a countable
union `F` of horizontal segments with `H¹(F) < ∞`, `H¹⌊F(B(z,r))/r → 2` for `H¹⌊F`-a.e. `z`. -/
def E2sapDensity : Prop :=
  ∀ (I : Set ℕ) (u v b : I → ℝ),
    μH[1] (⋃ i, horizontalSegment (u i) (v i) (b i)) ≠ ⊤ →
    ∀ᵐ z ∂(μH[1].restrict (⋃ i, horizontalSegment (u i) (v i) (b i))),
      Tendsto (planarDensityRatio (μH[1].restrict (⋃ i, horizontalSegment (u i) (v i) (b i))) z)
        (𝓝[>] 0) (𝓝 2)

/-! ## The zero-slope cover -/

/-- **The zero-slope cover.** At `n = 2`, `k = 1`, `ι(E)` is
covered exactly by countably many horizontal graphs of slope zero (one per labelled segment). -/
def E2sapCover : Prop :=
  ∃ (I : Set ℕ) (G : I → HorizontalGraph 2 1 0), timeSlice '' e2_sapSet ⊆ ⋃ i, (G i).image

end ParabolicRectifiability.Examples
