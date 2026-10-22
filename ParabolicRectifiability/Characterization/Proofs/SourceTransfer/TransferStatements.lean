import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import Mathlib.Probability.Kernel.Defs

/-! # Named statements for the transfer of square finiteness from an ADR measure

Definitions and proposition definitions only. The component estimates are proved in the
corresponding proof modules and exposed as `b3_couplingEnergy`, …;
`adr_source_transfer_of_leaves` assembles them into `SourceTransferStatement`. The transfer has the
following steps: on-carrier displacement, off-carrier probability kernel, integrated errors,
exceptional-set removal; plane infima are taken after the fixed-plane comparison.

**Couplings.** Both displacement steps are written with one device. A *coupling* of
`μ` and `ν` is a measure `π` on `X × X` with `π.fst = μ` and `π.snd = ν`; mass at `y` is moved
to `v` along `π`. The on-carrier replacement (mass of `E_i` spread uniformly over
`B_i`, the good part kept in place) and the off-carrier kernel (mass at `y ∉ Γ`
spread by a probability kernel over a reference ball near `y`) are couplings. One fixed-plane
inequality (`CouplingEnergyStatement`) then gives both the on-carrier and the off-carrier
transfer at the energy level, with the plane infimum taken **after** the
fixed-plane comparison. Its error term is `couplingError`.

The two error estimates are stated through one measurability/Tonelli bridge
(`CouplingErrorTonelliStatement`) and a geometric estimate in Tonelli form
(`OnCarrierErrorEstimateStatement`, `OffCarrierErrorEstimateStatement`); the off-carrier
coupling is stated through a normalized Borel probability kernel (`OffCarrierKernelStatement`)
and the coupling it induces (`KernelCouplingStatement`). `b3_onCarrierError_of_parts` etc. prove
`OnCarrierErrorStatement`, `OffCarrierErrorStatement` and `OffCarrierCouplingStatement` from
these parts.

Conventions: `P(z,r)` is `Metric.ball z r`; `Ω_A = Γ \ G_A` with `G_A = adrGoodSet Γ ν k A`;
the relative ball `B_i = Γ ∩ P(z_i, r_i)`; `Ξ_A = ⋃_i P(z_i, 20 r_i)` (the excluded
centres). Real constants are compared through `ENNReal.ofReal`.
-/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.SourceTransferTree

open ParabolicRectifiability.Foundations

/-! ## Definitions -/

/-- The integrated displacement error of a coupling `π` at the centre `z` up to the scale `R`:
`∫_0^R r^{-k-2} ∫_{p.1 ∈ P(z,r)} d_P(p.1,p.2)^2 dπ(p) dr/r`, in `[0,∞]`.

With the factor `2` of `CouplingEnergyStatement` this is the integrated error term of
the on-carrier transfer (bounded by `72 r^{-k-2} Σ m_i r_i^2`) and of
the off-carrier transfer (bounded by `18 r^{-k-2} ∫ d(y)^2 dμ`). -/
def b3_couplingError {n : ℕ} (k : ℕ) (π : Measure (Space n × Space n)) (z : Space n)
    (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioo 0 R, (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
    ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, edist p.1 p.2 ^ 2 ∂π ∂scaleMeasure

/-- The replaced source `ν_A = ν⌊G_A + Σ_i (m_i / σ(B_i)) σ⌊B_i` with `m_i = ν(E_i)` and `B_i = Γ ∩ P(z_i, r_i)`. This is the measure `νA` of
`ReplacementStatement`. -/
def b3_replacedSource {n : ℕ} (k : ℕ) (Γ : Set (Space n)) (σ ν : Measure (Space n)) (A : ℝ)
    (I : Set ℕ) (z : I → Space n) (r : I → ℝ) (E : I → Set (Space n)) : Measure (Space n) :=
  ν.restrict (adrGoodSet Γ ν k A) +
    Measure.sum (fun i : I =>
      (ν (E i) / σ (Γ ∩ Metric.ball (z i) (r i))) •
        σ.restrict (Γ ∩ Metric.ball (z i) (r i)))

/-- The data `(I, z_i, r_i, E_i)` satisfy all conclusions of `ReplacementStatement`
for the constants `C₀, C₁`, the reference `(Γ, σ)`, the source `ν` and the level `A`.

This is the body of `ReplacementStatement` after its existential quantifiers (the
last conjunct names the measure `νA` through `b3_replacedSource`, which unfolds to the same
`let` body); the output of `ReplacementStatement` is passed to the component estimates through
this predicate by definitional unfolding. -/
def b3_IsReplacementData {n : ℕ} (k : ℕ) (C₀ C₁ : ℝ) (Γ : Set (Space n))
    (σ ν : Measure (Space n)) (A : ℝ)
    (I : Set ℕ) (z : I → Space n) (r : I → ℝ) (E : I → Set (Space n)) : Prop :=
  (∀ i, z i ∈ Γ ∧ 0 < r i) ∧
  Pairwise (Disjoint on fun i => Γ ∩ Metric.ball (z i) (r i)) ∧
  (∀ i, Γ ∩ Metric.ball (z i) (r i) ⊆ Γ \ adrGoodSet Γ ν k A) ∧
  (∀ i, MeasurableSet (E i)) ∧
  (∀ i, E i ⊆ Γ ∩ Metric.ball (z i) (5 * r i)) ∧
  Pairwise (Disjoint on E) ∧
  (⋃ i, E i) = Γ \ adrGoodSet Γ ν k A ∧
  σ (Γ \ adrGoodSet Γ ν k A) ≤ ENNReal.ofReal (C₀ / A) * ν Γ ∧
  (∀ i, ν (E i) ≤ ENNReal.ofReal (205 ^ k * A * r i ^ k)) ∧
  (b3_replacedSource k Γ σ ν A I z r E ≤ ENNReal.ofReal (C₁ * A) • σ ∧
    b3_replacedSource k Γ σ ν A I z r E Γ = ν Γ)

/-! ## Named statements -/

/-- **Fixed-plane coupling inequality at the energy level** (the on-carrier and
off-carrier displacement estimates, integrated in scale).

Let `π` be a finite coupling of `μ = π.fst` and `ν = π.snd`, `z` a centre, `0 < R` and
`a ≥ 1`, and suppose that for every `0 < r < R`, `π`-a.e. pair `(y,v)` with `y ∈ P(z,r)` has
`v ∈ P(z, a r)`. Then
`S^R_{μ,T}(z) ≤ 2 a^{k+2} S^{aR}_{ν,T}(z) + 2 couplingError(π, z, R)`.

Proof route: for a fixed model `L`, `d(y,L)^2 ≤ 2 d(v,L)^2 + 2 d(y,v)^2`, integrate against
`π` over `{y ∈ P(z,r)}` and use the localization: `fit_μ(L;z,r) ≤ 2 fit_ν(L;z,ar) + 2 e(r)`.
Only then take the infimum over `L` (`iInf_add`), multiply by `r^{-k-2}` (with
`r^{-k-2} = a^{k+2} (ar)^{-k-2}`), and integrate over `(0,R)` against `dr/r`, using the
dilation invariance of `dr/r` to identify `∫_0^R β_ν(z,ar) dr/r = S^{aR}_ν(z)`. An
unavailable family is allowed (both infima are `⊤`). Measurability in `r` of the two terms:
`measurable_betaSq` (finite `ν`) for the model term; for the error term, for fixed `z` the
unweighted cumulative displacement integral `r ↦ ∫_{p.1 ∈ P(z,r)} d_P(p.1,p.2)^2 dπ` is
monotone in `r` and hence measurable, and multiplication by the measurable radius weight
`r^{-k-2}` preserves measurability. The weighted integrand itself need not be monotone (a
displaced atom whose first coordinate is at distance `1` from `z` gives a positive multiple
of `1_{r>1} r^{-k-2}`). Only the model term needs measurability for `lintegral_add_left`;
put the error term second. The dilation of `dr/r` is already in the project:
`map_const_mul_scaleMeasure` and `setLIntegral_scaleMeasure_comp_const_mul`
are the lemmas used for this. The hypothesis `1 ≤ a` is not needed by the proof
(any `a > 0` works). -/
def CouplingEnergyStatement : Prop :=
  ∀ (n k : ℕ) (T : FamilyKind) (π : Measure (Space n × Space n)), IsFiniteMeasure π →
  ∀ (z : Space n) (R a : ℝ), 0 < R → 1 ≤ a →
    (∀ r : ℝ, 0 < r → r < R →
      ∀ᵐ p ∂π, p.1 ∈ Metric.ball z r → p.2 ∈ Metric.ball z (a * r)) →
    squareEnergy π.fst k T R z ≤
      ENNReal.ofReal (2 * a ^ (k + 2)) * squareEnergy π.snd k T (a * R) z +
        2 * b3_couplingError k π z R

/-- **Exceptional centres**: for replacement data, the
excluded centres `Ξ_A = ⋃_i P(z_i, 20 r_i)` satisfy
`σ(Ξ_A) ≤ (C 20^k / c) σ(Ω_A)`.

Proof route: upper ADR at `z_i ∈ Γ` gives `σ(P(z_i,20 r_i)) ≤ C 20^k r_i^k`; lower ADR and
`σ(Γᶜ) = 0` (`Measure.measure_compl_support`, `support_eq`) give `c r_i^k ≤ σ(B_i)`; the
`B_i` are disjoint Borel subsets of `Ω_A`, so `Σ_i σ(B_i) ≤ σ(Ω_A)`. No source estimate is
used; with the bad-mass bound of the data this gives `σ(Ξ_A) ≤ C₃ ν(Γ)/A`. -/
def ExceptionalMassStatement : Prop :=
  ∀ (n k : ℕ) (c C C₀ C₁ : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
  ∀ (ν : Measure (Space n)) (A : ℝ) (I : Set ℕ) (z : I → Space n) (r : I → ℝ)
    (E : I → Set (Space n)), b3_IsReplacementData k C₀ C₁ Γ σ ν A I z r E →
    σ (⋃ i, Metric.ball (z i) (20 * r i)) ≤
      ENNReal.ofReal (C * 20 ^ k / c) * σ (Γ \ adrGoodSet Γ ν k A)

/-- **On-carrier coupling**: for a finite source `ν` carried by `Γ`, a level
`A > 0` and replacement data, the measure
`π_A = (ν⌊G_A) ∘ (y ↦ (y,y))⁻¹ + Σ_i (ν⌊E_i) ⊗ (σ⌊B_i / σ(B_i))`
is a finite coupling of `ν` and the replaced source `ν_A`; `π_A`-a.e. pair either stays in
place in `G_A` or moves from `E_i` into `B_i`; and at a centre `x ∈ Γ` outside the excluded
balls (`d(x, z_i) ≥ 20 r_i` for every `i`) a pair starting in `P(x,s)` ends in `P(x,2s)`.

Proof route: `0 < c r_i^k ≤ σ(B_i) ≤ C r_i^k < ∞` (ADR and `σ(Γᶜ) = 0`), so each product has
first marginal `ν⌊E_i`; `G_A = Γ \ ⋃ E_i` is Borel and `ν = ν⌊G_A + Σ ν⌊E_i` (exact
allocation, `ν Γᶜ = 0`). The good set is Borel **only through the exact allocation**:
`adrGoodSet ⊆ Γ` by definition, so `G_A = Γ \ ⋃ E_i`, which is needed both for the diagonal
part and for `ν = ν⌊G_A + Σ ν⌊E_i`. The second marginals sum to `b3_replacedSource` exactly
(`Measure.fst_sum`, `Measure.snd_sum`, `Measure.fst_prod`, `Measure.snd_prod`; rewrite
`(a/b) • m = a • (b⁻¹ • m)`). Localization:
`y ∈ E_i ∩ P(x,s)` and `d(x,z_i) ≥ 20 r_i` give `s > 15 r_i`, hence
`d(x,v) < s + 6 r_i < 2s` for `v ∈ B_i`. -/
def OnCarrierCouplingStatement : Prop :=
  ∀ (n k : ℕ) (c C C₀ C₁ : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
  ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν Γᶜ = 0 → ∀ A : ℝ, 0 < A →
  ∀ (I : Set ℕ) (z : I → Space n) (r : I → ℝ) (E : I → Set (Space n)),
    b3_IsReplacementData k C₀ C₁ Γ σ ν A I z r E →
    ∃ π : Measure (Space n × Space n), IsFiniteMeasure π ∧ π.fst = ν ∧
      π.snd = b3_replacedSource k Γ σ ν A I z r E ∧
      (∀ᵐ p ∂π, (p.2 = p.1 ∧ p.1 ∈ adrGoodSet Γ ν k A) ∨
        ∃ i, p.1 ∈ E i ∧ p.2 ∈ Γ ∩ Metric.ball (z i) (r i)) ∧
      ∀ x ∈ Γ, (∀ i, x ∉ Metric.ball (z i) (20 * r i)) → ∀ s : ℝ, 0 < s →
        ∀ᵐ p ∂π, p.1 ∈ Metric.ball x s → p.2 ∈ Metric.ball x (2 * s)

/-- **On-carrier integrated error**: for a finite coupling `π`
of `ν` supported as in `OnCarrierCouplingStatement`, the error is Borel in the centre and
`∫_{Γ \ Ξ_A} couplingError(π, x, R) dσ(x) ≤ C 2^k ν(Γ)` for every `R`.

Proof route: `π`-a.e., `d(y,v)^2 · 1_{P(x,s)}(y) ≤ Σ_i 36 r_i^2 1_{E_i ∩ P(x,s)}(y)` (points
of `G_A` do not move; `y ∈ E_i ⊆ P(z_i,5r_i)`, `v ∈ P(z_i,r_i)`). The hit condition
`dist(x, E_i) < s` is Borel (`infEDist`, empty set at infinity). For `x ∈ Γ \ Ξ_A` a hit
forces `s > 15 r_i` and `x ∈ P(z_i, 2s)`. Tonelli and upper ADR at `z_i`:
`Σ_i 36 r_i^2 m_i ∫_{15 r_i}^∞ s^{-k-3} C (2s)^k ds = (36 C 2^k / 450) Σ_i m_i ≤ C 2^k ν(Γ)`
(the cancellation `m_i r_i^2 ∫_{15r_i}^∞ s^{-3} ds = m_i/450`). Joint
measurability of `(x,s) ↦ ∫ 1_{P(x,s)}(p.1) d(p)^2 dπ` from the open set
`{(x,s,p) : d(p.1,x) < s}` (`Measurable.lintegral_prod_right'`). -/
def OnCarrierErrorStatement : Prop :=
  ∀ (n k : ℕ) (c C C₀ C₁ : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
  ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν Γᶜ = 0 → ∀ A : ℝ, 0 < A →
  ∀ (I : Set ℕ) (z : I → Space n) (r : I → ℝ) (E : I → Set (Space n)),
    b3_IsReplacementData k C₀ C₁ Γ σ ν A I z r E →
  ∀ π : Measure (Space n × Space n), IsFiniteMeasure π → π.fst = ν →
    (∀ᵐ p ∂π, (p.2 = p.1 ∧ p.1 ∈ adrGoodSet Γ ν k A) ∨
      ∃ i, p.1 ∈ E i ∧ p.2 ∈ Γ ∩ Metric.ball (z i) (r i)) →
  ∀ R : ℝ, Measurable (fun x => b3_couplingError k π x R) ∧
    ∫⁻ x in Γ \ ⋃ i, Metric.ball (z i) (20 * r i), b3_couplingError k π x R ∂σ ≤
      ENNReal.ofReal (C * 2 ^ k) * ν Γ

/-- **Off-carrier probability kernel**: every finite ambient source `μ` is the
first marginal of a finite coupling `π` whose second marginal is carried by `Γ`, which moves
each point at most three times its distance to `Γ`, and which keeps pairs starting in
`P(x,s)`, `x ∈ Γ`, inside `P(x,4s)`.

Proof route (selection-free kernel): `π = μ ⊗ₘ K` with
`K_y = δ_y` for `y ∈ Γ` and, for `y ∉ Γ` with `d(y) = dist(y,Γ) > 0`, `K_y` the normalized
`σ` on a reference ball of radius comparable to `d(y)` within `2 d(y)` of `y`: the ball `P(y, 2 d(y))` centred at `y` itself (its mass is between
`c (d/2)^k` and `C (4d)^k` by ADR at a point of `Γ` within `3d/2` of `y`); alternatively the
ball `P(a(y), d(y))` with `a(y)` the first point of a countable dense subset of `Γ` with
`d(y, a(y)) < 2 d(y)`. Measurability of
`y ↦ K_y(s)`: `Kernel.piecewise` on the closed set `Γ`, parameter integration of the
measurable set `{(y,w) : w ∈ ball}` (`measurable_measure_prodMk_left`). Marginals:
`Measure.fst_compProd`; `π.snd Γᶜ = 0` from `σ(Γᶜ) = 0`. Displacement:
`d(y,v) < 3 d(y)`; for `y ∈ Γ`, `v = y`. Localization: `d(y) ≤ d(y,x) < s`, so
`d(x,v) < s + 3s`.

This statement is true **only because `IsADRCarrier` contains `nonempty`**: for `Γ = ∅` and
`μ ≠ 0`, `π.snd Γᶜ = 0` forces `π = 0`, contradicting `π.fst = μ`. The localization conjunct
follows from the displacement conjunct (`infEDist y Γ ≤ edist y x` for `x ∈ Γ`); it is
derived in `b3_mem_ball_of_displacement`, and the statement is proved by
`b3_offCarrierCoupling_of_parts` from `OffCarrierKernelStatement` and
`KernelCouplingStatement`. -/
def OffCarrierCouplingStatement : Prop :=
  ∀ (n k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
  ∀ μ : Measure (Space n), IsFiniteMeasure μ →
    ∃ π : Measure (Space n × Space n), IsFiniteMeasure π ∧ π.fst = μ ∧ π.snd Γᶜ = 0 ∧
      (∀ᵐ p ∂π, edist p.1 p.2 ≤ 3 * Metric.infEDist p.1 Γ) ∧
      ∀ x ∈ Γ, ∀ s : ℝ, 0 < s →
        ∀ᵐ p ∂π, p.1 ∈ Metric.ball x s → p.2 ∈ Metric.ball x (4 * s)

/-- **Off-carrier integrated error**: for a finite coupling `π` which moves each
point at most three times its distance to `Γ`, the error is Borel in the centre and
`∫_Γ couplingError(π, x, R) dσ(x) ≤ 9 C 2^k π.fst(Γᶜ)` for every `R`.

Proof route: `π`-a.e. `d(y,v)^2 ≤ 9 d(y)^2`, and pairs with `y ∈ Γ` do not move. For
`y ∉ Γ`, `x ∈ Γ ∩ P(y,s)` forces `s > d(y)`, and recentering at a point of `Γ ∩ P(y,s)`
gives `σ(Γ ∩ P(y,s)) ≤ C (2s)^k`. Tonelli:
`∫ 9 d(y)^2 C 2^k ∫_{d(y)}^∞ s^{-3} ds dπ = (9 C 2^k / 2) π.fst(Γᶜ)`. -/
def OffCarrierErrorStatement : Prop :=
  ∀ (n k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
  ∀ π : Measure (Space n × Space n), IsFiniteMeasure π →
    (∀ᵐ p ∂π, edist p.1 p.2 ≤ 3 * Metric.infEDist p.1 Γ) →
  ∀ R : ℝ, Measurable (fun x => b3_couplingError k π x R) ∧
    ∫⁻ x in Γ, b3_couplingError k π x R ∂σ ≤ ENNReal.ofReal (9 * C * 2 ^ k) * π.fst Γᶜ

/-! ## The error bridge, the error estimates and the kernel -/

/-- The scale weight of a moving reference ball:
`w_{σ,D}(y,R) = ∫_0^R r^{-k-2} σ(D ∩ P(y,r)) dr/r`, in `[0,∞]`.

By Tonelli (`CouplingErrorTonelliStatement`),
`∫_D couplingError(π,x,R) dσ(x) = ∫ d_P(y,v)^2 w_{σ,D}(y,R) dπ(y,v)`. -/
def b3_errorWeight {n : ℕ} (k : ℕ) (σ : Measure (Space n)) (D : Set (Space n)) (y : Space n)
    (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioo 0 R, (ENNReal.ofReal r)⁻¹ ^ (k + 2) * σ (D ∩ Metric.ball y r) ∂scaleMeasure

/-- **Measurability/Tonelli bridge for the coupling error** (used by
both the on-carrier and the off-carrier error estimates).

For a measure `σ` finite on compacts, a finite measure `π` on `X × X`, a Borel set `D` and
every real `R`: the centre map `x ↦ couplingError(π,x,R)` is Borel, and
`∫_D couplingError(π,x,R) dσ(x) = ∫ d_P(y,v)^2 [∫_0^R r^{-k-2} σ(D ∩ P(y,r)) dr/r] dπ(y,v)`.

Proof route: `σ` is sigma-finite (finite on compacts in the proper, sigma-compact `Space n`);
`π` is finite and `scaleMeasure` is s-finite. The set `{(x, r, p) : dist p.1 x < r}` is open,
hence Borel in `Space n × ℝ × (Space n × Space n)` (second countable), so the integrand
`1_D(x) 1_{(0,R)}(r) r^{-k-2} 1_{P(x,r)}(p.1) d_P(p.1,p.2)^2` is jointly measurable
(`Measurable.lintegral_prod_right'` gives the measurability in `x`). Swap the three integrals
(`lintegral_lintegral_swap`, twice) and use `p.1 ∈ P(x,r) ↔ x ∈ P(p.1,r)` (`dist_comm`), so
`∫_x 1_D(x) 1_{P(x,r)}(p.1) dσ = σ(D ∩ P(p.1,r))`. For `R ≤ 0` both sides vanish
(`Ioo 0 R = ∅`). -/
def CouplingErrorTonelliStatement : Prop :=
  ∀ (n k : ℕ) (σ : Measure (Space n)), IsFiniteMeasureOnCompacts σ →
  ∀ π : Measure (Space n × Space n), IsFiniteMeasure π →
  ∀ D : Set (Space n), MeasurableSet D → ∀ R : ℝ,
    Measurable (fun x => b3_couplingError k π x R) ∧
    ∫⁻ x in D, b3_couplingError k π x R ∂σ =
      ∫⁻ p, edist p.1 p.2 ^ 2 * b3_errorWeight k σ D p.1 R ∂π

/-- **On-carrier error, geometric estimate in Tonelli form.** Hypotheses as in `OnCarrierErrorStatement`; for every `R`,
`∫ d_P(y,v)^2 w_{σ, Γ \ Ξ_A}(y,R) dπ(y,v) ≤ C 2^k ν(Γ)`, with
`Ξ_A = ⋃_i P(z_i, 20 r_i)`.

Proof route: `π`-a.e. a pair either stays in place (`d = 0`; note `0 · ⊤ = 0`) or has
`y ∈ E_i ⊆ P(z_i,5r_i)`, `v ∈ P(z_i,r_i)`, hence `d(y,v)^2 < 36 r_i^2`. For such `y`, a point
`x ∈ (Γ \ Ξ_A) ∩ P(y,r)` has `20 r_i ≤ d(x,z_i) < r + 5 r_i`, so `r > 15 r_i` and
`x ∈ P(z_i, 2r)`; upper ADR at `z_i` gives `σ((Γ \ Ξ_A) ∩ P(y,r)) ≤ C (2r)^k 1_{r > 15 r_i}`.
Then `w ≤ C 2^k ∫_{(15 r_i,∞)} r^{-2} dr/r = C 2^k / (450 r_i^2)` by
`lintegral_inv_pow_Ioi_scaleMeasure` with **exponent `2`** (the measure already contributes
`dr/r`). Hence the integrand is at most `Σ_i (36/450) C 2^k 1_{E_i}(y)`, and
`∫ ≤ (36 C 2^k / 450) Σ_i ν(E_i) ≤ (36 C 2^k / 450) ν(Γ) ≤ C 2^k ν(Γ)` (`π.fst = ν`; the
`E_i` are disjoint Borel subsets of `Γ`). Keep this raw constant `36 C 2^k ν(Γ) / 450`
separate from the factor `2` of `CouplingEnergyStatement` (together: `72/450`). -/
def OnCarrierErrorEstimateStatement : Prop :=
  ∀ (n k : ℕ) (c C C₀ C₁ : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
  ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν Γᶜ = 0 → ∀ A : ℝ, 0 < A →
  ∀ (I : Set ℕ) (z : I → Space n) (r : I → ℝ) (E : I → Set (Space n)),
    b3_IsReplacementData k C₀ C₁ Γ σ ν A I z r E →
  ∀ π : Measure (Space n × Space n), IsFiniteMeasure π → π.fst = ν →
    (∀ᵐ p ∂π, (p.2 = p.1 ∧ p.1 ∈ adrGoodSet Γ ν k A) ∨
      ∃ i, p.1 ∈ E i ∧ p.2 ∈ Γ ∩ Metric.ball (z i) (r i)) →
  ∀ R : ℝ,
    ∫⁻ p, edist p.1 p.2 ^ 2 *
        b3_errorWeight k σ (Γ \ ⋃ i, Metric.ball (z i) (20 * r i)) p.1 R ∂π ≤
      ENNReal.ofReal (C * 2 ^ k) * ν Γ

/-- **Off-carrier error, geometric estimate in Tonelli form.** Hypotheses as in
`OffCarrierErrorStatement`; for every `R`,
`∫ d_P(y,v)^2 w_{σ,Γ}(y,R) dπ(y,v) ≤ 9 C 2^k π.fst(Γᶜ)`.

Proof route: write `d(y) = infEDist y Γ`. For `y ∈ Γ`, `d(y) = 0` forces `v = y` and the
integrand vanishes (`0 · ⊤ = 0`). For `y ∉ Γ`, `0 < d(y) < ∞` (`Γ` closed and nonempty);
`σ(Γ ∩ P(y,r)) = 0` for `r ≤ d(y)`, and recentering at a point `γ ∈ Γ ∩ P(y,r)`
(`P(y,r) ⊆ P(γ,2r)`) gives `σ(Γ ∩ P(y,r)) ≤ C (2r)^k`. Then
`w ≤ C 2^k ∫_{(d(y),∞)} r^{-2} dr/r = C 2^k / (2 d(y)^2)` (`lintegral_inv_pow_Ioi_scaleMeasure`, exponent `2`), and `d(y,v)^2 ≤ 9 d(y)^2`, so the
integrand is at most `(9 C 2^k / 2) 1_{Γᶜ}(y)` and `∫ ≤ (9 C 2^k / 2) π.fst(Γᶜ)`. Keep this raw
constant separate from the factor `2` of `CouplingEnergyStatement` (together: `18 C 2^k`). -/
def OffCarrierErrorEstimateStatement : Prop :=
  ∀ (n k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
  ∀ π : Measure (Space n × Space n), IsFiniteMeasure π →
    (∀ᵐ p ∂π, edist p.1 p.2 ≤ 3 * Metric.infEDist p.1 Γ) →
  ∀ R : ℝ,
    ∫⁻ p, edist p.1 p.2 ^ 2 * b3_errorWeight k σ Γ p.1 R ∂π ≤
      ENNReal.ofReal (9 * C * 2 ^ k) * π.fst Γᶜ

/-- **The normalized moving-ball probability kernel.**

Under the reference hypotheses there is a Markov (probability) kernel `K` on `Space n`,
carried by `Γ`, which moves each point at most three times its distance to `Γ`.

Proof route (selection-free): `K_y = δ_y` for `y ∈ Γ`, and for `y ∉ Γ`, with
`d(y) = dist(y,Γ)`, `K_y = σ⌊P(y,2d(y)) / σ(P(y,2d(y)))`. Checkpoints:
* `σ` is sigma-finite (finite on compacts in the proper `Space n`) and `σ(Γᶜ) = 0`
  (`Measure.measure_compl_support`, `support_eq`, `Γ` closed);
* off `Γ`, `0 < d(y) < ∞` (`Γ` closed and **nonempty**, `IsADRCarrier.nonempty`). Choose,
  non-measurably and only for the bounds, `γ ∈ Γ` with `d(y,γ) < 3 d(y)/2`; then
  `P(γ, d(y)/2) ⊆ P(y,2d(y)) ⊆ P(γ,4d(y))`, so
  `0 < c (d(y)/2)^k ≤ σ(P(y,2d(y))) ≤ C (4d(y))^k < ∞`: positive finite denominators;
* Borel measurability of `y ↦ K_y(S)`: the moving-ball indicator `{(y,w) : dist w y < 2 d(y)}`
  is jointly Borel (`d` is continuous), parameter integration against the sigma-finite `σ`
  (`measurable_measure_prodMk_left`), division by the measurable positive finite
  denominator, and the piecewise definition on the closed set `Γ` (`Kernel.piecewise`,
  `Kernel.deterministic` for `δ_y`);
* `K_y(Γᶜ) = 0` from `σ(Γᶜ) = 0`, and from `y ∈ Γ` for `δ_y`;
* displacement: off `Γ`, `K_y`-a.e. `d(y,v) < 2 d(y) ≤ 3 d(y)`; on `Γ`, `v = y`.
No measurable selection is needed. -/
def OffCarrierKernelStatement : Prop :=
  ∀ (n k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
    ∃ K : ProbabilityTheory.Kernel (Space n) (Space n), ProbabilityTheory.IsMarkovKernel K ∧
      (∀ y, K y Γᶜ = 0) ∧
      ∀ y, ∀ᵐ v ∂(K y), edist y v ≤ 3 * Metric.infEDist y Γ

/-- **The coupling of a Markov kernel: marginals and displacement.**

For a Borel set `Γ`, a Markov kernel `K` carried by `Γ` which moves each point at most three
times its distance to `Γ`, and a finite measure `μ`, the measure `π = μ ⊗ₘ K` is a finite
coupling with `π.fst = μ`, `π.snd Γᶜ = 0`, and `π`-a.e. `d(p.1,p.2) ≤ 3 dist(p.1,Γ)`.

Proof route: `Measure.compProd` (`μ ⊗ₘ K`); finiteness and `Measure.fst_compProd`
(Markov); `π.snd Γᶜ = ∫ K_y(Γᶜ) dμ(y) = 0` (`Measure.snd_compProd` or
`Measure.compProd_apply` with the measurable `Γᶜ`); the displacement set is Borel
(`edist` and `infEDist` are continuous), so `Measure.ae_compProd_iff` applies. The
localization conjunct of `OffCarrierCouplingStatement` is derived from the displacement in
`b3_mem_ball_of_displacement`. -/
def KernelCouplingStatement : Prop :=
  ∀ (n : ℕ) (Γ : Set (Space n)), MeasurableSet Γ →
  ∀ K : ProbabilityTheory.Kernel (Space n) (Space n), ProbabilityTheory.IsMarkovKernel K →
    (∀ y, K y Γᶜ = 0) → (∀ y, ∀ᵐ v ∂(K y), edist y v ≤ 3 * Metric.infEDist y Γ) →
  ∀ μ : Measure (Space n), IsFiniteMeasure μ →
    ∃ π : Measure (Space n × Space n), IsFiniteMeasure π ∧ π.fst = μ ∧ π.snd Γᶜ = 0 ∧
      ∀ᵐ p ∂π, edist p.1 p.2 ≤ 3 * Metric.infEDist p.1 Γ

end ParabolicRectifiability.Characterization.SourceTransferTree
