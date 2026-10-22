import ParabolicRectifiability.Examples.Proofs.DigitGraph.Grid
import ParabolicRectifiability.Examples.Proofs.DigitGraph.Tails
import ParabolicRectifiability.Examples.Proofs.DigitGraph.Digit
import ParabolicRectifiability.Examples.Proofs.DigitGraph.Periodic
import ParabolicRectifiability.Examples.Proofs.DigitGraph.Measurable
import ParabolicRectifiability.Examples.Proofs.DigitGraph.Cover
import ParabolicRectifiability.Examples.Proofs.DigitGraph.Identify
import ParabolicRectifiability.Examples.Proofs.DigitGraph.Density
import ParabolicRectifiability.Examples.Proofs.PlanarSlices.PlanarLine
import ParabolicRectifiability.Examples.Proofs.DigitGraph.Band
import ParabolicRectifiability.Examples.Proofs.DigitGraph.SmallEnergy
import ParabolicRectifiability.Examples.Proofs.DigitGraph.AllEnergy
import ParabolicRectifiability.Examples.Proofs.DigitGraph.Primitive
import ParabolicRectifiability.Examples.Proofs.DigitGraph.LineCost
import ParabolicRectifiability.Examples.Proofs.DigitGraph.Variance
import ParabolicRectifiability.Examples.Proofs.DigitGraph.BorelCantelli
import ParabolicRectifiability.Examples.Proofs.DigitGraph.QuadBand
import ParabolicRectifiability.Examples.Proofs.DigitGraph.QuadDiverge
import ParabolicRectifiability.Examples.Proofs.DigitGraph.LowerDensity
import ParabolicRectifiability.Examples.Proofs.DigitGraph.MarkedAE
import ParabolicRectifiability.Examples.Proofs.DigitGraph.FullSet
import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements

/-! # The dispersed digit graph below the quadratic exponent: composed lemmas

The theorems here delegate to their corresponding proofs `<name>_proof`, which have exactly the
displayed type (their hypotheses are other statements `E2sb…`, in implication form) and are
proved in separate modules (prefix `e2_`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

/-- **The grid of scales.** Route: closed forms
`ℓ_j = 1/∏_{i=1}^{j} N_i` (`Nat` products, `Finset.prod_range_succ`), `N_j = (j+1) 2^{j+30}`;
the integer multiples are partial products; `h_j = 2^{10} P_j` and `ℓ_{j-1} = 2^{j+30} P_j` by
`field_simp` from the definitions. -/
theorem e2_sb_grid : E2sbGrid := by
  exact @e2_sb_grid_proof

/-- **The tail bounds.** Route: `h_{j+1} = δ_j h_j/2^{j+31}` exactly from the closed forms; hence
`h_{j+1+i} ≤ 2^{-32 i} h_{j+1}`, a geometric majorant (`summable_geometric_of_lt_one`,
`tsum_le_tsum`) giving `Σ h < ∞` and `η_j ≤ 2 h_{j+1}`; the other bounds follow; strict
antitonicity from `h_1 = 2^{-21} < 1 = h_0` and the ratio bound. -/
theorem e2_sb_tails (hG : E2sbGrid) : E2sbTails := by
  exact @e2_sb_tails_proof hG

/-- **Coding and separation.** Route: (a) for
`i ≤ j`, `ℓ_i = c ℓ_j` with `c ∈ ℕ` (grid), and `⌊u/c⌋ = ⌊⌊u⌋/c⌋` (`Int.floor_div…`) makes
`⌊x/ℓ_i⌋` constant on `[kℓ_j, (k+1)ℓ_j)`. (b) `sum_add_tsum_nat_add` splits `y = Y_j + tail` and
`0 ≤ tail ≤ η_j` termwise. (c) take the first differing bit `i ≤ j`: the difference is
`±h_i` plus a term of size `≤ η_i < h_i/2` (tails), so `|Δy| > h_i/2 ≥ h_j/2`. -/
theorem e2_sb_digit (hG : E2sbGrid) (hT : E2sbTails) : E2sbDigit := by
  exact @e2_sb_digit_proof hG hT

/-- **Periodic mass discrepancy.**
Route: `b_j(x + P_j) = b_j(x)` (`Int.floor_add_int`) and `b_j = 1` exactly on
`[mP_j, mP_j + ℓ_j)`; the integral over any interval of length `P_j` is `ℓ_j = δ_j P_j`; remove
whole periods (`intervalIntegral.integral_comp_add_right`, periodicity) and bound the partial
period by `δ_j P_j`. The mass bound applies the discrepancy to `(x₀ - r, x₀ + r)`
(`volume` of the marked part `= ∫ b_j`, `integral_indicator`) with `2P_j ≤ r` (`h_j = 2^{10}P_j`). -/
theorem e2_sb_periodic (hG : E2sbGrid) : E2sbPeriodic := by
  exact @e2_sb_periodic_proof hG

/-- **Borel measurability.** Route:
`Int.measurable_floor`/`measurable_floor` composed with `x ↦ x/ℓ_j` gives Borel marked sets;
`y` is a pointwise limit of finite sums (`measurable_of_tendsto_metrizable`, or
`Measurable.ennreal_tsum` after `ofReal`), and `T` by `measurable_pi_iff`/`WithLp` coordinates. -/
theorem e2_sb_measurable : E2sbMeasurable := by
  exact @e2_sb_measurable_proof

/-- **Compactness and the cylinder cover.** Route: `T([kℓ_j,(k+1)ℓ_j)) ⊆ [kℓ_j,(k+1)ℓ_j] × [Y_k, Y_k + η_j]` (digit (a), (b)),
`0 ≤ k < 1/ℓ_j`; the finite union is closed, so it contains `E`; `E` is closed and bounded
(`Metric.isCompact_of_isClosed_isBounded`). `hausdorffMeasure_le_liminf_sum` with `d = 1`, the
`1/ℓ_j` rectangles of diameter `√(ℓ_j^2+η_j^2)` and `η_j/ℓ_j ≤ 2^{-j-20} → 0`. -/
theorem e2_sb_cover (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit) : E2sbCover := by
  exact @e2_sb_cover_proof hG hT hD

/-- **The natural measure.** Route: for
Borel `A`, `T⁻¹A ∩ [0,1) ⊆ π₁(A ∩ E)` since `π₁ ∘ T = id` and `T([0,1)) ⊆ E`; then
`μ(A) ≤ L¹(π₁(A ∩ E)) = μH[1](π₁(A ∩ E)) ≤ μH[1](A ∩ E)` (`hausdorffMeasure_real`,
`LipschitzWith.hausdorffMeasure_image_le` for the one-Lipschitz projection). With
`μ(ℝ²) = 1` and `H¹(E) ≤ 1` (cover), complements give equality on Borel sets
(`Measure.ext`), and `H¹(E) = 1`. -/
theorem e2_sb_identify (hM : E2sbMeasurable) (hC : E2sbCover) : E2sbIdentify := by
  exact @e2_sb_identify_proof hM hC

/-- **Growth and upper density.**
Route: `μ(B(z,r)) = L¹{x ∈ [0,1) : T x ∈ B(z,r)} ≤ L¹(z₀ - r, z₀ + r) = 2r`
(`Measure.map_apply`, `|x - z₀| ≤ ‖T x - z‖`), hence the ratio is `≤ 2` (`limsup_le_of_le`).
Lower bound at every `z ∈ E` (closure points included): choose a graph approximant
`x ∈ [0,1)` with `‖T x - z‖ < 2ℓ_j - √(ℓ_j^2+η_j^2)` (positive since `η_j < ℓ_j`); its whole
generation-`j` interval `I ⊆ [0,1)` has `T(I) ⊆ B(z, 2ℓ_j)` (digit (a), (b)), so
`μ(B(z,2ℓ_j)) ≥ L¹(I) = ℓ_j`; radii `2ℓ_j → 0` give `limsup ≥ 1/2`
(`le_limsup_of_frequently_le`). -/
theorem e2_sb_density (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit) (hM : E2sbMeasurable) :
    E2sbDensity := by
  exact @e2_sb_density_proof hG hT hD hM

/-- **Affine lines of the plane** (generic; used for the band estimate and the line cost). Route: `L.directionᗮ` has `finrank 1` (`Submodule.finrank_add_finrank_orthogonal`);
a unit `n = (a,b)` spans it; `infEDist w L = ofReal ‖(w - L.projection w)‖` (`AffineSpatialPlane.nearest`,
`Metric.infEDist` of a closed nonempty set attained) `= |⟪w - anchor, n⟫|`, `c = ⟪anchor, n⟫`.
Converse: `AffineSpatialPlane.ofTranslate (span {(-b, a)}) _ (c • n)`. -/
theorem e2_planarLine : E2PlanarLine := by
  exact @e2_planarLine_proof

/-- **The uniform scale-band estimate.** Route: approximate `z ∈ E` by `T(x₀)`, `x₀ ∈ [0,1)`, `‖T x₀ - z‖ < h_{j-1}/4`; for `T(x) ∈ B(z,r)`, `|y(x) - y(x₀)| < r + h_{j-1}/4 < h_{j-1}/2`, so separation gives the same first `j-1` bits and
`y(x) = Y + h_j b_j(x) + e(x)`, `0 ≤ e ≤ η_j`, `Y = Y_{j-1}(x₀)`. Competitor: the horizontal line
`{w₁ = Y}` (planar line, converse). `(u+v)^p ≤ c_p(u^p + v^p)`, periodic mass `≤ 3δ_j r`
(`|x - z₀| < r`), growth `μ(B) ≤ 2r`: `β^p ≤ c_p[3δ_j(h_j/r)^p + 2(η_j/r)^p]`; then
`(u+v)^{2/p} ≤ max(1, 2^{2/p-1})(u^{2/p}+v^{2/p})`. -/
theorem e2_sb_band (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit) (hP : E2sbPeriodic)
    (hM : E2sbMeasurable) (hDen : E2sbDensity) (hL : E2PlanarLine) : E2sbBand := by
  exact @e2_sb_band_proof hG hT hD hP hM hDen hL

/-- **Summation over the bands.**
Route: `(0,1/4) = ⋃_{j≥1} [h_j/4, h_{j-1}/4)` (tails: `h` strictly decreasing to `0`,
`h_0 = 1`), disjoint (`lintegral_iUnion`); on each band integrate the band bound against `dr/r`
(`setLIntegral_scaleMeasure`): `∫(h_j/r)^2 dr/r ≤ 8`, `∫(η_j/r)^2 dr/r ≤ 8(η_j/h_j)^2`; the sum
`Σ_j [δ_j^{2/p} + (η_j/h_j)^2]` converges (`Real.summable_one_div_nat_rpow`, `2/p > 1`;
`η_j/h_j ≤ 2^{-j-30}`). -/
theorem e2_sb_spSmall (hG : E2sbGrid) (hT : E2sbTails) (hB : E2sbBand) : E2sbSpSmall := by
  exact @e2_sb_spSmall_proof hG hT hB

/-- **Every positive finite endpoint.** Route: for `a ≤ 1/4`, monotonicity in the endpoint (`lintegral_mono_set`); for
`a > 1/4` split `(0,a) = (0,1/4) ∪ [1/4,a)`; on `[1/4, a)` a line through `z` (planar line,
converse) gives `dist(w,L) < r` on `B(z,r)`, `μ(ℝ²) = 1` (measurable `T`), so
`β_p^p ≤ r^{-1}` and `β_p^2 ≤ 4^{2/p}`, integrated against `dr/r` over `[1/4, a)`. -/
theorem e2_sb_spAll (hM : E2sbMeasurable) (hL : E2PlanarLine) (hS : E2sbSpSmall) :
    E2sbSpAll := by
  exact @e2_sb_spAll_proof hM hL hS

/-- **The periodic primitive.**
Route: `F(x) = ∫_0^x (b_j - δ_j)` is `P_j`-periodic with `0 ≤ F ≤ δ_j P_j` (explicit on
`[0, P_j)`: `min(x, ℓ_j) - δ_j x`); integration by parts for the absolutely continuous `F`
(`intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt` or the countable-
exception version: `F` has derivative `b_j - δ_j` off the countable jump set):
`∫_{-h}^{h} X g(x₀+X) = h F(x₀+h) + h F(x₀-h) - ∫_{-h}^{h} F(x₀+X)`, each part `≤ hδP`, `≤ 2hδP`.
Input: grid only (the marked set is explicit). -/
theorem e2_sb_primitive (hG : E2sbGrid) : E2sbPrimitive := by
  exact @e2_sb_primitive_proof hG

/-- **The two-height variance bound** (generic). Route: with `m = (2h)^{-1}∫β`, `|m - δ| ≤ δP/h`, hence
`m(1-m) ≥ δ/4`; `∫(Z - c)^2 ≥ ∫(Z - Z̄)^2` for `Z = aX + bhβ`, and `∫(Z - Z̄)^2 =
a^2(2h^3/3) + 2abh∫X(β - δ) + b^2 h^2 · 2hm(1-m)` (`β^2 = β`, `∫X = 0`); AM-GM
`4|ab|δPh ≤ a^2h^2/6 + 24b^2δ^2P^2` and `P ≤ 2^{-10}h` give `≥ 2h · δh^2/8 = δh^3/4`. -/
theorem e2_variance : E2Variance := by
  exact @e2_variance_proof

/-- **The line cost.** Route: write `L` as `{a w₀ + b w₁ = c}` (planar line); on `J` the old bits are
constant (digit (a) at generation `j-1`), `y(x) = Y + h_j b_j(x) + e(x)`, `0 ≤ e ≤ η_j`
(digit (b)); translate `X = x - x₀`; the mean input from the discrepancy (periodic) and the
covariance input from the primitive feed the variance bound (`β(X) = b_j(x₀+X)`, `P = P_j`,
`δ = δ_j`) giving `δh^3/4` for the ideal points; `|u+v|^2 ≥ u^2/2 - v^2` with `|b e| ≤ η_j`
and `η_j^2 ≤ δ_j h_j^2/32` (tails) give `δ_j h_j^3/16`; convert to the lower Lebesgue integral
(`ofReal_integral_eq_lintegral_ofReal`, measurable `T`). -/
theorem e2_sb_lineCost (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit) (hP : E2sbPeriodic)
    (hM : E2sbMeasurable) (hPr : E2sbPrimitive) (hV : E2Variance) (hL : E2PlanarLine) :
    E2sbLineCost := by
  exact @e2_sb_lineCost_proof hG hT hD hP hM hPr hV hL

/-- **Borel-Cantelli for the parent boundaries.** Route: the bad set of index `j` in `[0,1)` is the set of `x` within
`h_j` of a generation-`(j-1)` boundary, of measure `≤ 2h_j/ℓ_{j-1} = 2^{-j-19}` (grid); the series
converges and `measure_limsup_atTop_eq_zero` gives a.e. eventual goodness; take
`k = ⌊x/ℓ_{j-1}⌋`. -/
theorem e2_sb_borelCantelli (hG : E2sbGrid) (hT : E2sbTails) : E2sbBorelCantelli := by
  exact @e2_sb_borelCantelli_proof hG hT

/-- **The quadratic band lower bound.** Route: `J = (x₀ - h_j, x₀ + h_j) ⊆ [0,1)` (`x₀ ∈ [0,1)`, `1/ℓ_{j-1} ∈ ℕ`); on `J`
the old bits agree with `x₀`'s (digit (a)), so `|y(x) - y(x₀)| ≤ h_j + η_j < 2h_j` and
`T(J) ⊆ B(T(x₀), 3h_j) ⊆ B(T(x₀), r)`; `∫_{B} dist^2 dμ ≥ ∫_J dist(T x, L)^2 dx`
(`lintegral_map`, `setLIntegral_mono_set`) for every line; the line cost gives
`β_2^2 ≥ r^{-3} δ_j h_j^3/16 ≥ δ_j/1024` for `r ≤ 4h_j`. -/
theorem e2_sb_quadBand (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit) (hM : E2sbMeasurable)
    (hLC : E2sbLineCost) : E2sbQuadBand := by
  exact @e2_sb_quadBand_proof hG hT hD hM hLC

/-- **Divergent quadratic bands** (generic in the measure). Route: for `j ≥ j₁` the bands `[3h_j, 4h_j]` lie in `(0,a)` and are
pairwise disjoint (`4h_{j+1} < 3h_j`, tails); `lintegral_iUnion` (no measurability of the
integrand is needed) and `setLIntegral_const` give
`S_2^a ≥ Σ_{j≥j₁} (δ_j/1024) log(4/3) = ∞` (`Real.not_summable_one_div_natCast`,
`ENNReal.tsum_eq_top…`); at `p = 2` the exponent `2/2 = 1`. -/
theorem e2_sb_quadDiverge (hG : E2sbGrid) (hT : E2sbTails) : E2sbQuadDiverge := by
  exact @e2_sb_quadDiverge_proof hG hT

/-- **Infinitely many marked digits.** Route: on `[0,1)` the set `{b_m = … = b_N = 0}` is a union of generation-`N`
intervals; the bits `b_m, …, b_{N-1}` are constant on generation-`(N-1)` intervals (input digit
(a)), and each generation-`(N-1)` interval
contains exactly `M_N = 2^{N+30}` marked children of its `N_N` children (`q_N ∣ N_N`), so the measure is `∏_{j=m}^{N}(1 - δ_j) = m/(N+1)` (induction
on `N`); `→ 0`, so `{∀ j ≥ m, b_j = 0}` is null; union over `m`
(`measure_iUnion_null`), `Filter.frequently_atTop`. The proof goes through the
exact finite avoidance formula `L¹({b_m = … = b_N = 0} ∩ [0,1)) = m/(N+1)` for `1 ≤ m ≤ N`,
then its a.e. consequence. -/
theorem e2_sb_markedAE (hG : E2sbGrid) (hD : E2sbDigit) (hM : E2sbMeasurable) :
    E2sbMarkedAE := by
  exact @e2_sb_markedAE_proof hG hD hM

/-- **Vanishing lower density.** Route: if `b_j(x₀) = 1` and `T(x) ∈ B(T(x₀), h_j/4)`, then
`|y(x) - y(x₀)| < h_j/4 ≤ h_{j-1}/2`, so the first `j-1` bits agree (separation), and
`b_j(x) = 0` would give `|Δy| ≥ h_j - η_j > h_j/4` (digit (b), tails); so
`μ(B(T(x₀), h_j/4)) ≤ L¹{|x - x₀| < h_j/4, b_j = 1} ≤ 3δ_j h_j/4` (periodic); the ratio
`≤ 3δ_j → 0` along `r = h_j/4 → 0` gives `liminf = 0` (`liminf_le_of_frequently_le`). -/
theorem e2_sb_lowerDensity (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit) (hP : E2sbPeriodic)
    (hM : E2sbMeasurable) : E2sbLowerDensity := by
  exact @e2_sb_lowerDensity_proof hG hT hD hP hM

/-- **The common full set.** Route: choose a Borel null `N ⊇ {x ∈ [0,1) : ¬P(T x)}`
(`exists_measurable_superset_of_null`) and put `G = {z | z 0 ∈ Ico 0 1 \ N ∧ T (z 0) = z}` (the
source-domain condition `z 0 ∈ [0,1)` is required: without it `G` would contain `T(2)`, where `P`
need not hold); `G` is Borel (`measurableSet_eq_fun`, measurable `T`, coordinate). Since
`(T x) 0 = x`, `[0,1) ∩ T⁻¹(Gᶜ) ⊆ N`, so `μ(Gᶜ) = L¹([0,1) ∩ T⁻¹ Gᶜ) = 0`
(`Measure.map_apply`, `Measure.restrict_apply`), and `z ∈ G` is `T(x)` with `x ∈ [0,1) \ N`,
hence `P z`. `G ⊆ T([0,1)) ⊆ E`. -/
theorem e2_sb_fullSet (hM : E2sbMeasurable) : E2sbFullSet := by
  exact @e2_sb_fullSet_proof hM

end ParabolicRectifiability.Examples
