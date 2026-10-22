import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Data

/-! # Source allocation data for the Whitney nodes

Definitions for the simultaneous allocation of a diffuse source to all Whitney
holes (`WhitneySourceAllocation`). For each cell `Q_i` there are
an anchor `a_i ∈ F₀` nearest to the center `p_i`, reservoir sets
`S_{i,0}, …, S_{i,m}` in `P(a_i, C_B r_i)` and densities `h_{i,l}` carried by them,
with `∫ h_{i,l} dσ = |Q_i|` and the simultaneous total bound `Σ h_{i,l} ≤ A`
σ-almost everywhere. The allocated probability barycenters `b_{i,l}` keep the
robust spatial simplex lower bound `σ_min[b_{i,1}-b_{i,0} ⋯ b_{i,m}-b_{i,0}] ≥ c₂ r_i`.

From these data: the averages `|Q_i|⁻¹ ∫ f h_{i,l} dσ`, the signed node values
`g(p_i) = Σ_l c_{i,l} |Q_i|⁻¹ ∫ f h_{i,l} dσ` for coefficients with the moment
identities `Σ_l c_{i,l} = 1`, `Σ_l c_{i,l} b_{i,l} = u_i`, `Σ_l |c_{i,l}| ≤ C`
(`IsMomentCoefficients`), and the node function equal to `f` off the centers. The
coefficients may have signs; only the densities are nonnegative.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-- Allocation of the source `σ` to every Whitney cell, with total density bound
`A`, reservoir radius factor `C_B` and simplex constant `c₂`. -/
structure WhitneySourceAllocation {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a : ℝ}
    (W : WhitneyData m ι F₀ D a) (σ : Measure (Space m)) (A C_B c₂ : ℝ) where
  anchor : ι → Space m
  anchor_mem : ∀ i, anchor i ∈ F₀
  dist_anchor : ∀ i, dist (W.center i) (anchor i) = Metric.infDist (W.center i) F₀
  reservoir : ι → Fin (m + 1) → Set (Space m)
  measurableSet_reservoir : ∀ i l, MeasurableSet (reservoir i l)
  reservoir_subset : ∀ i l, reservoir i l ⊆ Metric.ball (anchor i) (C_B * W.radius i)
  density : ι → Fin (m + 1) → Space m → ℝ≥0∞
  measurable_density : ∀ i l, Measurable (density i l)
  density_eq_zero : ∀ i l, ∀ x ∉ reservoir i l, density i l x = 0
  lintegral_density : ∀ i l, ∫⁻ x, density i l x ∂σ = ENNReal.ofReal (W.radius i ^ (m + 2))
  sum_density_le : ∀ᵐ x ∂σ, ∑' p : ι × Fin (m + 1), density p.1 p.2 x ≤ ENNReal.ofReal A
  simplex : ∀ i (v : Fin m → ℝ), c₂ * W.radius i * ‖WithLp.toLp 2 v‖ ≤
    ‖∑ l : Fin m, v l • ((W.radius i ^ (m + 2))⁻¹ • ∫ x, (density i l.succ x).toReal • x.1 ∂σ -
      (W.radius i ^ (m + 2))⁻¹ • ∫ x, (density i 0 x).toReal • x.1 ∂σ)‖

namespace WhitneySourceAllocation

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a : ℝ} {W : WhitneyData m ι F₀ D a}
  {σ : Measure (Space m)} {A C_B c₂ : ℝ}

/-- The spatial barycenter `b_{i,l} = |Q_i|⁻¹ ∫ u h_{i,l} dσ`. -/
def barycenter (S : WhitneySourceAllocation W σ A C_B c₂) (i : ι) (l : Fin (m + 1)) :
    Spatial m :=
  (W.radius i ^ (m + 2))⁻¹ • ∫ x, (S.density i l x).toReal • x.1 ∂σ

/-- The allocated average `|Q_i|⁻¹ ∫ f h_{i,l} dσ`. -/
def average (S : WhitneySourceAllocation W σ A C_B c₂) {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (f : Space m → Y) (i : ι) (l : Fin (m + 1)) : Y :=
  (W.radius i ^ (m + 2))⁻¹ • ∫ x, (S.density i l x).toReal • f x ∂σ

/-- The signed node value `g(p_i) = Σ_l c_{i,l} |Q_i|⁻¹ ∫ f h_{i,l} dσ`. -/
def nodeValue (S : WhitneySourceAllocation W σ A C_B c₂) (c : ι → Fin (m + 1) → ℝ)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : Space m → Y) (i : ι) : Y :=
  ∑ l, c i l • S.average f i l

open Classical in
/-- The node function: the node value at a center, and `f` elsewhere (in particular
on `F₀`, which contains no center). -/
def nodeFunction (S : WhitneySourceAllocation W σ A C_B c₂) (c : ι → Fin (m + 1) → ℝ)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : Space m → Y) (q : Space m) :
    Y :=
  if h : ∃ i, W.center i = q then S.nodeValue c f h.choose else f q

/-- The moment identities `Σ_l c_{i,l} = 1`, `Σ_l c_{i,l} b_{i,l} = u_i` and the
coefficient bound `Σ_l |c_{i,l}| ≤ C`. -/
structure IsMomentCoefficients (S : WhitneySourceAllocation W σ A C_B c₂)
    (c : ι → Fin (m + 1) → ℝ) (C : ℝ) : Prop where
  sum_eq_one : ∀ i, ∑ l, c i l = 1
  sum_smul_barycenter : ∀ i, ∑ l, c i l • S.barycenter i l = (W.center i).1
  sum_abs_le : ∀ i, ∑ l, |c i l| ≤ C

end WhitneySourceAllocation

end ParabolicRectifiability
