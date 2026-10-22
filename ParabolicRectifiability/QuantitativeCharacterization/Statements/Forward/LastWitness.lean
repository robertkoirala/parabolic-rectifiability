import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ForwardCovering

/-! # Last-witness square estimate for the forward covering: definitions and named statements

Definitions and proposition definitions only. This module fixes the statements below
`LastWitnessStatement`: the last-witness comparison square estimate of a terminal construction.

The argument uses only the exported `TerminalNeck` fields `initialPlane_fit`, `level_zero_plane`,
`genuine_mem`, `genuine_scale`, `genuine_fit`, `timeCompatible`, together with the finite
occurrence sets and the prescribed scales (`initialRadius_eq`: `r_j = 10^{-j} 48 ℓ_*`), the good
region's optimal models and chain budget, and three inputs from the neighbouring steps: the
`OwnerStatement` and `AncestorStatement` of the terminal construction and the
`PlaneComparisonStatement` of the partition-energy step.

Fixed constants: `J_lag = 8`, `m₀ = 2`, so the charged depth of comparison index
`j` is `t(j) = max(0, j - 1 - J_lag - m₀) = j - 11` (natural subtraction). Statements index a
comparison by `j + 1` (levels `j` and `j + 1`, scale `r_j`), whose charged ancestor lies at the
absolute level `𝒢.root.1 + (j + 1 - 11)`. The horizontal tolerance cap is `γ ≤ 1`: it converts spatial incidence into parabolic incidence without any inverse
power of a tolerance. Every constant depends only on `n, k, A, Λ` and these fixed numbers.

The route, for fixed `w` and truncation `N`:
1. `WitnessSelectionStatement`: the last nonzero comparison index `j₀ + 1 ≤ N` and a finest
   genuine occurrence `g_*` (level `i ∈ {j₀, j₀ + 1}`, `i ≥ 1`) incident to `w`.
2. `IncidenceStatement`: horizontal recorded-time compatibility with `γ ≤ 1` turns spatial
   incidence into parabolic incidence (vertically it is the triangle inequality).
3. the owner `O_* = O(g_*, i)` (input `OwnerStatement`) and its member ancestors (input).
4. `AncestorInclusionStatement`: every fitting ball `P(g, 40 r_j)` of a genuine occurrence
   incident to the comparison lies in the coefficient ball of the ancestor at depth `t(j + 1)`
   (unclamped `t > 0` and clamped `t = 0`).
5. `OccurrenceBoundStatement`: each genuine fitted plane, tested against the
   ancestor's model on its own source `P(g, 5 r_i)`, is within `C₁ a_A` of the ancestor's plane
   (squared plane comparison at every advertised anchor and radius).
6. `PairBoundStatement`: the triangle inequality through the ancestor's plane bounds every
   same-level and adjacent term, hence `E_{j+1}(w)² ≤ 4 C₁ a_A`.
7. `LevelEstimateStatement`: steps 2-6 assembled at one comparison index.
8. `ChargingStatement`: the root is charged at most
   `J_lag + 3 = 11` times, every positive-depth ancestor once; the budget of `O_*` pays.
9. `SquareUpToStatement`: the finite bound `∑_{j ≤ N} E_j(w)² ≤ 44 C₁ b`, uniformly in `w, N`;
   the passage to the infinite sum is by monotone convergence.

Conventions: every fit and plane comparison uses the original `μ` on its stated ball; nothing
here mentions the assigned measure `μ⌞S`. The square bound is never assumed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Witness

section Defs

variable {n : ℕ}

/-- **The comparison square bound of the neck's type through level `N`**: the finite truncation
of `NeckType.SquareBound` (base), vertical functions on `X`
or horizontal functions on `ℝ^n`, `sup_w ∑_{j ≤ N} E_j(w)² ≤ E`. -/
def TypeSquareBoundUpTo {m : ℕ} {ι : Type*} :
    NeckType → CoherentFamily n m ι → ℝ → ℕ → Prop
  | .horizontal, F, E, N => F.HorizontalSquareBoundUpTo E N
  | .vertical, F, E, N => F.VerticalSquareBoundUpTo E N

variable {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- **The per-occurrence last-witness bound** of a good region with
constant `C₁`: let `g ∈ S` and let `M` be a `T`-model minimizing the original-source fit
`∫_{P(g, 40 r_i)} d_P(·, M)² dμ` (`r_i = 10^{-i} 48 ℓ_*`). For every member `Q` whose coefficient
ball contains that fitting ball, with `ℓ_Q ≤ 10^{12} r_i`, every anchor `y` with
`|y - x_g| ≤ 200 r_i` and every radius `s ∈ [r_i, 10 r_i]`,
`d_{y,s}(L_M, L_{Π_Q})² ≤ C₁ a_Q`, `a_Q = (Λ ℓ_Q)^{-k-2} ∫_{P(z_Q, Λ ℓ_Q)} d_P(·, Π_Q)² dμ`.
The anchors and radii are exactly those of the same-level (`i = j`) and adjacent (`i = j + 1`)
comparison terms at scale `r_j`. -/
def OccurrenceBound (𝒢 : GoodRegion P μ k Λ b) (C₁ : ℝ) : Prop :=
  ∀ (i : ℕ) (g : Space n) (M : Models n k 𝒢.type.toFamilyKind), g ∈ 𝒢.rootCell →
    (∀ M' : Models n k 𝒢.type.toFamilyKind,
      fit μ M g (40 * coherentScale (48 * 𝒢.rootScale) i) ≤
        fit μ M' g (40 * coherentScale (48 * 𝒢.rootScale) i)) →
    ∀ Q ∈ 𝒢.members,
      Metric.ball g (40 * coherentScale (48 * 𝒢.rootScale) i) ⊆
        Metric.ball Q.2 (Λ * P.scale Q.1) →
      P.scale Q.1 ≤ 10 ^ 12 * coherentScale (48 * 𝒢.rootScale) i →
    ∀ (y : Spatial n) (s : ℝ), ‖y - g.1‖ ≤ 200 * coherentScale (48 * 𝒢.rootScale) i →
      coherentScale (48 * 𝒢.rootScale) i ≤ s → s ≤ 10 * coherentScale (48 * 𝒢.rootScale) i →
      ENNReal.ofReal (planeComparison y s (NeckSelection.modelPlane 𝒢.type M)
          (NeckSelection.modelPlane 𝒢.type (𝒢.model Q)) ^ 2) ≤
        ENNReal.ofReal C₁ * P.modelCoeff μ Λ (𝒢.model Q) Q

end Defs

/-! ## Generic coherent-family statements (no good region) -/

/-- **Incidence**: under horizontal recorded-time
compatibility with tolerance `γ ≤ 1`, two occurrences whose recorded scales are at most `ρ` and
whose spatial centres are within `ρ` are within `ρ` in `d_P`. (No inverse power of `γ`.) -/
def IncidenceStatement : Prop :=
  ∀ (n m : ℕ) (ι : Type) (F : CoherentFamily n m ι) (C : Set (Space n)) (d : Space n → ℝ)
    (γ : ℝ), γ ≤ 1 → RecordsTimeCompatible F C d γ →
    ∀ (i i' : ℕ) (a a' : ι), a ∈ F.index i → a' ∈ F.index i' → ∀ ρ : ℝ,
      F.scale i ≤ ρ → F.scale i' ≤ ρ → ‖(F.center i a).1 - (F.center i' a').1‖ ≤ ρ →
        dist (F.center i a) (F.center i' a') ≤ ρ

/-- **The last witness** (the finite deepest-witness selection pattern of the base
`ChargeCollapse.incidentWitness_sum_le`, not its conclusion). For a coherent
family whose level-zero planes are its initial plane, any distance map `pos`, any reference
point `w` and truncation `N`: `E_0(w) = 0`, and either every `E_j(w)`, `j ≤ N`, vanishes, or
there is a last nonzero index `j₀ + 1 ≤ N` and an occurrence `(i, a)` of level `i ∈ {j₀, j₀ + 1}`,
`i ≥ 1` (a genuine occurrence: the root/child pair yields the child), incident to `w` at scale
`r_{j₀}`. -/
def WitnessSelectionStatement : Prop :=
  ∀ (n m : ℕ) (ι : Type) (W : Type) [PseudoMetricSpace W] (pos : Space n → W)
    (F : CoherentFamily n m ι) (w : W) (N : ℕ),
    (∀ a ∈ F.index 0, F.plane 0 a = F.initialPlane) →
    F.comparisonEnergy pos 0 w = 0 ∧
    ((∀ j ≤ N, F.comparisonEnergy pos j w = 0) ∨
      ∃ j₀ : ℕ, j₀ + 1 ≤ N ∧
        (∀ j : ℕ, j₀ + 1 < j → j ≤ N → F.comparisonEnergy pos j w = 0) ∧
        ∃ (i : ℕ) (a : ι), 1 ≤ i ∧ j₀ ≤ i ∧ i ≤ j₀ + 1 ∧ a ∈ F.index i ∧
          dist (pos (F.center i a)) w ≤ 12 * F.scale j₀)

/-- **The pair bound** (the triangle inequality through a test plane): if a spatial
distance map `pos` dominates spatial distances and every occurrence of level `j` or `j + 1`
incident to `w` at scale `r_j` has `d_{y, r_j}(L_{i,a}, L)² ≤ D` at every anchor `y` within
`20 r_j` of its spatial centre, then `E_{j+1}(w)² ≤ 4 D` (every same-level and adjacent term is
at most `2 √D`). -/
def PairBoundStatement : Prop :=
  ∀ (n m : ℕ) (ι : Type) (W : Type) [PseudoMetricSpace W] (pos : Space n → W)
    (F : CoherentFamily n m ι) (L : AffineSpatialPlane n m) (D : ℝ) (j : ℕ) (w : W),
    (∀ z z' : Space n, ‖z.1 - z'.1‖ ≤ dist (pos z) (pos z')) →
    (∀ i : ℕ, (i = j ∨ i = j + 1) → ∀ a ∈ F.index i,
      dist (pos (F.center i a)) w ≤ 12 * F.scale j →
      ∀ y : Spatial n, ‖y - (F.center i a).1‖ ≤ 20 * F.scale j →
        ENNReal.ofReal (planeComparison y (F.scale j) (F.plane i a) L ^ 2) ≤
          ENNReal.ofReal D) →
    F.comparisonEnergy pos (j + 1) w ^ 2 ≤ ENNReal.ofReal (4 * D)

/-! ## Good-region statements -/

/-- **Ancestor inclusion**, unclamped and clamped. Let `g` have an
owner-type cell `O` at level `i` (`d_P(g, z_O) ≤ 2000 r_i + 2 ℓ_O`, depth
`O.1 - root.1 ≥ i - 8`), let `j ≤ i`, and let `A` be the member ancestor of `O` at absolute level
`root.1 + (j + 1 - 11)`. For `Λ ≥ 4000`, every `z ∈ S` within `24 r_j` of `g` has its fitting
ball `P(z, 40 r_j)` inside the coefficient ball `P(z_A, Λ ℓ_A)`, and `ℓ_A ≤ 10^{12} r_{j+1}`.
(Unclamped, `j ≥ 10`: `ℓ_A = 10^{10} r_j / 48`; clamped, `j ≤ 10`: `A` is at the root level and
`z ∈ S ⊆ P(q, 2 ℓ_*)`, `40 r_j ≤ 1920 ℓ_*`.) -/
def AncestorInclusionStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (i : ℕ) (g : Space n) (O : ℕ × Space n)
    (j : ℕ) (A : ℕ × Space n) (z : Space n),
    4000 ≤ Λ → O ∈ 𝒢.members →
    dist g O.2 ≤ 2000 * coherentScale (48 * 𝒢.rootScale) i + 2 * P.scale O.1 →
    i + 𝒢.root.1 ≤ O.1 + 8 → j ≤ i →
    A ∈ 𝒢.members → A.1 = 𝒢.root.1 + (j + 1 - 11) → P.cellOf O ⊆ P.cellOf A →
    z ∈ 𝒢.rootCell → dist z g ≤ 24 * coherentScale (48 * 𝒢.rootScale) j →
      Metric.ball z (40 * coherentScale (48 * 𝒢.rootScale) j) ⊆
          Metric.ball A.2 (Λ * P.scale A.1) ∧
        P.scale A.1 ≤ 10 ^ 12 * coherentScale (48 * 𝒢.rootScale) (j + 1)

/-- **The per-occurrence bound holds**: for
`1 ≤ k < n + 2`, `A ≥ 1` there is `Λ₀` such that for every `Λ ≥ Λ₀` there are a buffer `B ≥ 1`,
`C₁ ≥ 0` and `b₀ > 0` with: for `0 < b ≤ b₀`, local ADR in `P(a, B R)` at a support-centred root,
every good region of a direct partition from `ℓ₀ = R` whose root is in the root forest satisfies
`OccurrenceBound 𝒢 C₁`. The comparison is applied on `P(g, 5 r_i)` with ADR buffer `P(g, 20 r_i)`
and the horizontal small-error test on `P(g, 10 r_i) ⊆ P(g, 40 r_i)`; `C₁` absorbs `5^{k+2}`,
`(Λ 10^{12})^{k+2}` and the anchor/radius change. -/
def OccurrenceBoundStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ B : ℝ, 1 ≤ B ∧ ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → LocalADR μ k A a (B * R) →
    ∀ (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b),
      P.InForest a R 𝒢.root → OccurrenceBound 𝒢 C₁

/-- **The ancestor-chain charging lemma** (not the
all-scale-tail `incidentWitness_sum_le`). Let `O` be a member and `J + root.1 ≤ O.1 + 11`. If
`e₀ = 0` and each `e_{j+1}`, `j + 1 ≤ J`, is at most `c a_A` for the member ancestor `A ⊇ O` at
absolute level `root.1 + (j + 1 - 11)`, then `∑_{j ≤ J} e_j ≤ 11 c b`: the root is charged at
most `J_lag + 3 = 11` times, every positive-depth ancestor once, and the chain budget of `O`
pays the whole chain. -/
def ChargingStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (O : ℕ × Space n) (J : ℕ)
    (e : ℕ → ℝ≥0∞) (c : ℝ≥0∞),
    O ∈ 𝒢.members → J + 𝒢.root.1 ≤ O.1 + 11 → e 0 = 0 →
    (∀ j : ℕ, j + 1 ≤ J → ∀ A ∈ 𝒢.members, A.1 = 𝒢.root.1 + (j + 1 - 11) →
      P.cellOf O ⊆ P.cellOf A → e (j + 1) ≤ c * P.modelCoeff μ Λ (𝒢.model A) A) →
    ∑ j ∈ Finset.range (J + 1), e j ≤ 11 * c * ENNReal.ofReal b

/-- **The level estimate at one comparison index**: for a terminal construction,
`Λ ≥ 4000`, the per-occurrence bound with `C₁ ≥ 0`, a spatial distance map `pos` dominating
spatial distances and turning `pos`-incidence of occurrences into parabolic incidence, a witness
occurrence `(i, a)` (`i ≥ 1`, `j₀ ≤ i`) incident to `w` at scale `r_{j₀}`, an owner-type cell `O`
of the witness, and for `j ≤ j₀` the member ancestor `Q ⊇ O` at absolute level
`root.1 + (j + 1 - 11)`: `E_{j+1}(w)² ≤ 4 C₁ a_Q`. At `j = 0` the level-zero occurrences carry
`L_*`, the plane of `Q = Q_*` itself. -/
def LevelEstimateStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (δ κ θ γ : ℝ) (TN : TerminalNeck 𝒢 δ κ θ γ)
    (C₁ : ℝ) (W : Type) [PseudoMetricSpace W] (pos : Space n → W),
    4000 ≤ Λ → 0 ≤ C₁ → OccurrenceBound 𝒢 C₁ →
    (∀ z z' : Space n, ‖z.1 - z'.1‖ ≤ dist (pos z) (pos z')) →
    (∀ (i i' : ℕ) (a a' : Space n), a ∈ TN.family.index i → a' ∈ TN.family.index i' →
      ∀ ρ : ℝ, TN.family.scale i ≤ ρ → TN.family.scale i' ≤ ρ →
        dist (pos (TN.family.center i a)) (pos (TN.family.center i' a')) ≤ ρ →
          dist (TN.family.center i a) (TN.family.center i' a') ≤ ρ) →
    ∀ (w : W) (j₀ i : ℕ) (a : Space n), 1 ≤ i → j₀ ≤ i → a ∈ TN.family.index i →
      dist (pos (TN.family.center i a)) w ≤ 12 * TN.family.scale j₀ →
    ∀ O ∈ 𝒢.members,
      dist (TN.family.center i a) O.2 ≤
        2000 * coherentScale (48 * 𝒢.rootScale) i + 2 * P.scale O.1 →
      i + 𝒢.root.1 ≤ O.1 + 8 →
    ∀ j : ℕ, j ≤ j₀ → ∀ Q ∈ 𝒢.members, Q.1 = 𝒢.root.1 + (j + 1 - 11) →
      P.cellOf O ⊆ P.cellOf Q →
        TN.family.comparisonEnergy pos (j + 1) w ^ 2 ≤
          ENNReal.ofReal (4 * C₁) * P.modelCoeff μ Λ (𝒢.model Q) Q

/-- **The finite square sum**: for a terminal construction with
horizontal tolerance `γ ≤ 1`, `Λ ≥ 4000` and the per-occurrence bound with `C₁ ≥ 0`, every
truncation satisfies the comparison square bound of the region's type with `E = 44 C₁ b`
(`4 C₁` per level, `11` charges of one chain budget `b`), uniformly in the truncation and the
witness. -/
def SquareUpToStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (δ κ θ γ : ℝ) (TN : TerminalNeck 𝒢 δ κ θ γ)
    (C₁ : ℝ), 4000 ≤ Λ → γ ≤ 1 → 0 ≤ C₁ → OccurrenceBound 𝒢 C₁ →
    ∀ N : ℕ, TypeSquareBoundUpTo 𝒢.type TN.family (44 * C₁ * b) N

end Witness

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
