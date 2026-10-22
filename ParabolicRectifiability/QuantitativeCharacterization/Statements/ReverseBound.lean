import ParabolicRectifiability.QuantitativeCharacterization.Coverings
import Mathlib.Probability.Kernel.Defs

/-! # The reverse bound: definitions and named statements

Definitions and proposition definitions only. The reverse proofs are in the
proof modules for the reverse bound, which assemble the local
estimate `exists_local_reverse_bound` from the named statements below.

**Shape of the proof.** For one model ball `P_i = P(c,ρ)` of the covering, with typed
`L`-reference `(Γ,σ)` meeting it, the transfer bound (`ModelTransferStatement`, with the
recentring) is
`∫∫_{z ∈ P(c,ρ), L⁻¹ d(z) ≤ r < ρ} β_{μ,T}(z,r)² dμ dr/r ≤ C₁ ρ^k`. It is assembled from

* the buffered Hall allocation in **kernel form** (`CouplingStatement`): a
  Markov kernel `κ` moving every point `y` at most `C_disp · d(y)`, `d = dist(·,Γ)`, whose
  transport of `μ⌊P(c,2ρ)` is at most `D₀ σ`. A kernel is the disintegrated coupling; the
  construction produces it directly (cells `λ_j = μ⌊Q_j` sent to `ν_j/m_j`, identity on `Γ`), so
  no disintegration theorem is needed. Its parts are the Whitney cells
  (`WhitneyCellsStatement`), the on-carrier comparison `μ⌊Γ ≤ D σ` (`OnCarrierStatement`), the
  capacitated Hall inequality (`HallInequalityStatement`), and a kernel built on a
  countable Borel partition (`KernelOfPartitionStatement`); the finite flow and the countable
  limit are the base theorem
  `HallAllocation.exists_countable_hall_allocation_proof` (weak `L¹` compactness of densities,
  no weak limit of measures);
* the pointwise comparison for each fixed fitting model, integrated before the infimum
  (`ComparisonStatement`);
* the Tonelli error bound (`ErrorIntegralStatement`);
* the main term: averaging over the transported testing centres (second factor `D₀`), the
  dilation of `dr/r` and the recentring at a nearby reference point (`MainTermStatement`).

The covering assembly is `CoveringAssemblyStatement`.

**Constants.** `B_rev(n,k,L)` is fixed before `A`: the allocation buffer `Bal` and the
displacement constant `C_disp` depend on `(n,k)` and the reference ADR constant `A_ref(n,k,L)`
only; the source growth `A` enters only through the capacities `D₀`.

Conventions: `P(z,r)` is `Metric.ball z r`; `d(y) = Metric.infDist y Γ` (real); real constants
are compared through `ENNReal.ofReal`; energies are extended nonnegative; `dμ dr/r` is
`pointScaleMeasure μ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization.ReverseTree

open ParabolicRectifiability.Foundations

/-! ## Definitions -/

/-- The covered point–scale pairs of one model ball `P(c,ρ)` with reference carrier `Γ`
(left side):
`{(z,r) : z ∈ P(c,ρ), L⁻¹ dist(z,Γ) ≤ r < ρ}`. Every scale set `𝓤_i` of a regular mixed
covering lies in the set of its model (`RegularMixedCovering.scaleSet_cover`). -/
def d2_modelPairs {n : ℕ} (L : ℝ) (Γ : Set (Space n)) (c : Space n) (ρ : ℝ) :
    Set (Space n × ℝ) :=
  {p | p.1 ∈ Metric.ball c ρ ∧ L⁻¹ * Metric.infDist p.1 Γ ≤ p.2 ∧ p.2 < ρ}

/-- The transport error at the testing pair `(z,r)`:
`r^{-k-2} ∫_{P(z,r)} h(y)² dμ(y)` with the displacement bound `h(y) = C_disp · dist(y,Γ)`,
in `[0,∞]`. -/
def d2_transportError {n : ℕ} (k : ℕ) (Cdisp : ℝ) (Γ : Set (Space n))
    (μ : Measure (Space n)) (z : Space n) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
    ∫⁻ y in Metric.ball z r, ENNReal.ofReal (Cdisp * Metric.infDist y Γ) ^ 2 ∂μ

/-! ## Named statements: the allocation -/

/-- **Whitney cells of the complement of a closed set** (the "distance layers and small net
cells" decomposition).

For every `n` there is `C₀ ≥ 1` such that the complement of every closed nonempty `Γ` is the
disjoint union of countably many Borel cells `Q_j`, each with an anchor `g_j ∈ Γ` and a scale
`s_j > 0`, such that `Q_j ⊆ P(g_j, C₀ s_j)` and `s_j ≤ dist(y,Γ)` for every `y ∈ Q_j`. Cells may
be empty (padding). -/
def WhitneyCellsStatement : Prop :=
  ∀ n : ℕ, ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ Γ : Set (Space n), IsClosed Γ → Γ.Nonempty →
    ∃ (Q : ℕ → Set (Space n)) (g : ℕ → Space n) (s : ℕ → ℝ),
      (∀ j, MeasurableSet (Q j)) ∧ (Pairwise fun i j => Disjoint (Q i) (Q j)) ∧
      (⋃ j, Q j) = Γᶜ ∧ (∀ j, g j ∈ Γ) ∧ (∀ j, 0 < s j) ∧
      (∀ j, Q j ⊆ Metric.ball (g j) (C₀ * s j)) ∧
      (∀ j, ∀ y ∈ Q j, s j ≤ Metric.infDist y Γ)

/-- **On-carrier comparison** `μ⌊Γ ≤ D σ` ("`λ|_Γ` … is at most `Cσ` by upper growth,
lower reference ADR, and the fivefold covering argument").

For `A ≥ 1` and `A_ref ≥ 1` there is `D` such that, for a locally Radon `μ` with upper growth
`μ(P(b,s)) ≤ A s^k` at `b ∈ supp μ ∩ P(c,ρ)`, `0 < s ≤ ρ`, and a measure `σ` with support `Γ`
that is `A_ref`-ADR, the part of `μ` on `Γ ∩ P(c,ρ)` is at most `D σ`. -/
def OnCarrierStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ Aref : ℝ, 1 ≤ Aref → ∀ A : ℝ, 1 ≤ A →
  ∃ D : ℝ, 0 < D ∧
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsFiniteMeasureOnCompacts σ → σ.support = Γ → IsADR Aref k σ →
  ∀ (c : Space n) (ρ : ℝ), 0 < ρ →
    (∀ b ∈ μ.support ∩ Metric.ball c ρ, ∀ s : ℝ, 0 < s → s ≤ ρ →
      μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k)) →
    μ.restrict (Γ ∩ Metric.ball c ρ) ≤ ENNReal.ofReal D • σ

/-- **The capacitated Hall inequality.**

For `A_ref ≥ 1` and a cell constant `C₀ ≥ 1` there is a growth radius factor `Ch ≥ 1` (before
`A`) and, for `A ≥ 1`, a capacity `D₁`, such that: for disjoint Borel cells `Q_j` with anchors
`g_j ∈ Γ = supp σ`, scales `s_j > 0` and `Q_j ⊆ P(g_j, C₀ s_j)`, and upper growth of `μ` on
`supp μ ∩ P(g_j, Ch s_j)` up to radius `Ch s_j`, every finite demand set `I` satisfies
`Σ_{j ∈ I} μ(Q_j) ≤ D₁ σ(⋃_{j ∈ I} Γ ∩ P̄(g_j, s_j))`. -/
def HallInequalityStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ Aref : ℝ, 1 ≤ Aref →
  ∀ C₀ : ℝ, 1 ≤ C₀ →
  ∃ Ch : ℝ, 1 ≤ Ch ∧ ∀ A : ℝ, 1 ≤ A → ∃ D₁ : ℝ, 0 < D₁ ∧
  ∀ (μ σ : Measure (Space n)) (Γ : Set (Space n)), σ.support = Γ → IsADR Aref k σ →
  ∀ (ι : Type) (Q : ι → Set (Space n)) (g : ι → Space n) (s : ι → ℝ),
    (∀ j, MeasurableSet (Q j)) → (Pairwise fun i j => Disjoint (Q i) (Q j)) →
    (∀ j, g j ∈ Γ) → (∀ j, 0 < s j) → (∀ j, Q j ⊆ Metric.ball (g j) (C₀ * s j)) →
    (∀ j, ∀ b ∈ μ.support ∩ Metric.ball (g j) (Ch * s j), ∀ t : ℝ, 0 < t → t ≤ Ch * s j →
      μ (Metric.ball b t) ≤ ENNReal.ofReal (A * t ^ k)) →
    ∀ I : Finset ι, ∑ j ∈ I, μ (Q j) ≤
      ENNReal.ofReal D₁ * σ (⋃ j ∈ I, Γ ∩ Metric.closedBall (g j) (s j))

/-- **A Markov kernel on a countable Borel partition** (the product couplings
`m_i⁻¹ λ_i ⊗ ν_i` together with the core identity coupling,  written as a kernel).

For countably many disjoint Borel sets `P_j` and probability measures `τ_j` there is a Markov
kernel `κ` with `κ y = τ_j` on `P_j` and `κ y = δ_y` off `⋃_j P_j`. -/
def KernelOfPartitionStatement : Prop :=
  ∀ (n : ℕ) (ι : Type) [Countable ι] (P : ι → Set (Space n)) (τ : ι → Measure (Space n)),
    (∀ j, MeasurableSet (P j)) → (Pairwise fun i j => Disjoint (P i) (P j)) →
    (∀ j, IsProbabilityMeasure (τ j)) →
    ∃ κ : ProbabilityTheory.Kernel (Space n) (Space n), ProbabilityTheory.IsMarkovKernel κ ∧
      (∀ j, ∀ y ∈ P j, κ y = τ j) ∧ (∀ y, (∀ j, y ∉ P j) → κ y = Measure.dirac y)

/-- **The buffered allocation in kernel form.**

For `A_ref ≥ 1` there are a displacement constant `C_disp ≥ 1` and a buffer `Bal ≥ 1` (both
before `A`) and, for `A ≥ 1`, a density bound `D₀`, such that: for a locally Radon `μ`, a
closed `A_ref`-ADR reference `σ` with support `Γ` meeting `P(c,ρ)`, and upper growth of `μ` on
`supp μ ∩ P(c, Bal ρ)` up to radius `Bal ρ`, there is a Markov kernel `κ` which moves every point
`y` at most `C_disp · dist(y,Γ)` (`κ y`-a.e.) and transports `μ⌊P(c,2ρ)` to a measure at most
`D₀ σ`: `∫_{P(c,2ρ)} κ_y dμ(y) ≤ D₀ σ`. This is the coupling `π(dy,dv) = λ(dy) κ_y(dv)` of
`λ = μ⌊P(c,2ρ)` with `pr₁ π = λ`, `pr₂ π ≤ D₀ σ`, `d(y,v) ≤ C d(y)` `π`-a.e. -/
def CouplingStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ Aref : ℝ, 1 ≤ Aref →
  ∃ Cdisp : ℝ, 1 ≤ Cdisp ∧ ∃ Bal : ℝ, 1 ≤ Bal ∧ ∀ A : ℝ, 1 ≤ A → ∃ D₀ : ℝ, 0 < D₀ ∧
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsFiniteMeasureOnCompacts σ → σ.support = Γ → IsADR Aref k σ →
  ∀ (c : Space n) (ρ : ℝ), 0 < ρ → (Metric.ball c ρ ∩ Γ).Nonempty →
    (∀ b ∈ μ.support ∩ Metric.ball c (Bal * ρ), ∀ s : ℝ, 0 < s → s ≤ Bal * ρ →
      μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k)) →
    ∃ κ : ProbabilityTheory.Kernel (Space n) (Space n), ProbabilityTheory.IsMarkovKernel κ ∧
      (∀ y, ∀ᵐ v ∂(κ y), dist y v ≤ Cdisp * Metric.infDist y Γ) ∧
      (μ.restrict (Metric.ball c (2 * ρ))).bind κ ≤ ENNReal.ofReal D₀ • σ

/-! ## Named statements: the integrated transfer -/

/-- **The pointwise comparison**, for each fixed fitting model before the
infimum.

Let `κ` be a Markov kernel moving every `y` at most `h(y) = C_disp · dist(y,Γ)` and transporting
`μ⌊P(c,2ρ)` below `D₀ σ`. Put `θ = C_disp (1 + L)` and `Λ = 1 + 2θ`. For `z ∈ P(c,ρ)`,
`0 < r < ρ` with `L⁻¹ dist(z,Γ) ≤ r`, and every transported centre `v` with
`dist(z,v) ≤ h(z)`:
`β_{μ,T}(z,r)² ≤ 2 D₀ Λ^{k+2} β_{σ,T}(v,Λr)² + 2 r^{-k-2} ∫_{P(z,r)} h² dμ`. -/
def ComparisonStatement : Prop :=
  ∀ (n k : ℕ) (T : FamilyKind) (L Cdisp D₀ : ℝ), 1 ≤ L → 1 ≤ Cdisp → 0 < D₀ →
  ∀ (μ σ : Measure (Space n)) (Γ : Set (Space n))
    (κ : ProbabilityTheory.Kernel (Space n) (Space n)), ProbabilityTheory.IsMarkovKernel κ →
    (∀ y, ∀ᵐ v ∂(κ y), dist y v ≤ Cdisp * Metric.infDist y Γ) →
  ∀ (c : Space n) (ρ : ℝ),
    (μ.restrict (Metric.ball c (2 * ρ))).bind κ ≤ ENNReal.ofReal D₀ • σ →
  ∀ (z : Space n) (r : ℝ), z ∈ Metric.ball c ρ → 0 < r → r < ρ →
    L⁻¹ * Metric.infDist z Γ ≤ r →
  ∀ v : Space n, dist z v ≤ Cdisp * Metric.infDist z Γ →
    betaSq μ k T z r ≤
      ENNReal.ofReal (2 * D₀ * (1 + 2 * Cdisp * (1 + L)) ^ (k + 2)) *
          betaSq σ k T v ((1 + 2 * Cdisp * (1 + L)) * r) +
        2 * d2_transportError k Cdisp Γ μ z r

/-- **The transport error integral.**

For `L, C_disp ≥ 1` there is a buffer `Be ≥ 1` (before `A`) and, for `A ≥ 1`, a constant `Ce`
such that, for a locally Radon `μ` with `c ∈ supp μ` and upper growth on `supp μ ∩ P(c, Be ρ)` up
to radius `Be ρ`, and any set `Γ`:
`∫∫_{z ∈ P(c,ρ), L⁻¹ d(z) ≤ r < ρ} r^{-k-2} ∫_{P(z,r)} h² dμ dμ dr/r ≤ Ce ρ^k`. -/
def ErrorIntegralStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ (L Cdisp : ℝ), 1 ≤ L → 1 ≤ Cdisp →
  ∃ Be : ℝ, 1 ≤ Be ∧ ∀ A : ℝ, 1 ≤ A → ∃ Ce : ℝ, 0 < Ce ∧
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (Γ : Set (Space n)) (c : Space n), c ∈ μ.support → ∀ ρ : ℝ, 0 < ρ →
    (∀ b ∈ μ.support ∩ Metric.ball c (Be * ρ), ∀ s : ℝ, 0 < s → s ≤ Be * ρ →
      μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k)) →
    ∫⁻ p in d2_modelPairs L Γ c ρ, d2_transportError k Cdisp Γ μ p.1 p.2
        ∂(pointScaleMeasure μ) ≤ ENNReal.ofReal (Ce * ρ ^ k)

/-- **The main term**: averaging over the transported testing centres (the second
factor `D₀`), the dilation of `dr/r`, and the recentring of the enlarged reference ball
at a nearby reference point.

For `C_disp ≥ 1`, `D₀ > 0`, `Λ ≥ 1`, `C_ref > 0` there is `Cm` such that: if `σ` has own-type
Carleson energy at most `C_ref` (as a root supremum over `Γ`), `κ` is a Markov kernel moving
every `y` at most `C_disp · dist(y,Γ)` and transporting `μ⌊P(c,2ρ)` below `D₀ σ`, and `Γ` meets
`P(c,ρ)`, then
`∫_{P(c,ρ)} ∫_0^ρ ∫ β_{σ,T}(v,Λr)² dκ_z(v) dr/r dμ(z) ≤ Cm ρ^k`. -/
def MainTermStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ (Cdisp D₀ Λ Cref : ℝ),
    1 ≤ Cdisp → 0 < D₀ → 1 ≤ Λ → 0 < Cref →
  ∃ Cm : ℝ, 0 < Cm ∧
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (T : FamilyKind) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsFiniteMeasureOnCompacts σ →
    rootCarlesonSup Γ σ k (fun R z => squareEnergy σ k T R z) ≤ ENNReal.ofReal Cref →
  ∀ κ : ProbabilityTheory.Kernel (Space n) (Space n), ProbabilityTheory.IsMarkovKernel κ →
    (∀ y, ∀ᵐ v ∂(κ y), dist y v ≤ Cdisp * Metric.infDist y Γ) →
  ∀ (c : Space n) (ρ : ℝ), 0 < ρ → (Metric.ball c ρ ∩ Γ).Nonempty →
    (μ.restrict (Metric.ball c (2 * ρ))).bind κ ≤ ENNReal.ofReal D₀ • σ →
    ∫⁻ p in Metric.ball c ρ ×ˢ Ioo 0 ρ, ∫⁻ v, betaSq σ k T v (Λ * p.2) ∂(κ p.1)
        ∂(pointScaleMeasure μ) ≤ ENNReal.ofReal (Cm * ρ ^ k)

/-- **Transfer to one reference** with the recentring.

For `n ≥ 1`, `1 ≤ k ≤ n + 2`, `L ≥ 1` and reference constants `A_ref ≥ 1`, `C_ref > 0` there is a
buffer `Bm ≥ 1` (before `A`) and, for `A ≥ 1`, a constant `C₁`, such that: for a locally Radon
`μ`, a family `T` and a measure `σ` with support `Γ`, finite on compacts, `A_ref`-ADR, with
own-type Carleson energy at most `C_ref`; a model ball `P(c,ρ)`, `c ∈ supp μ`, `ρ > 0`, meeting
`Γ`; and upper growth `μ(P(b,s)) ≤ A s^k` for `b ∈ supp μ ∩ P(c, Bm ρ)`, `0 < s ≤ Bm ρ`:
`∫∫_{z ∈ P(c,ρ), L⁻¹ dist(z,Γ) ≤ r < ρ} β_{μ,T}(z,r)² dμ dr/r ≤ C₁ ρ^k`.
Every beta uses the whole original `μ`. -/
def ModelTransferStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ L : ℝ, 1 ≤ L →
  ∀ Aref : ℝ, 1 ≤ Aref → ∀ Cref : ℝ, 0 < Cref →
  ∃ Bm : ℝ, 1 ≤ Bm ∧ ∀ A : ℝ, 1 ≤ A → ∃ C₁ : ℝ, 0 < C₁ ∧
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (T : FamilyKind) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsFiniteMeasureOnCompacts σ → σ.support = Γ → IsADR Aref k σ →
    rootCarlesonSup Γ σ k (fun R z => squareEnergy σ k T R z) ≤ ENNReal.ofReal Cref →
  ∀ c ∈ μ.support, ∀ ρ : ℝ, 0 < ρ → (Metric.ball c ρ ∩ Γ).Nonempty →
    (∀ b ∈ μ.support ∩ Metric.ball c (Bm * ρ), ∀ s : ℝ, 0 < s → s ≤ Bm * ρ →
      μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k)) →
    ∫⁻ p in d2_modelPairs L Γ c ρ, betaSq μ k T p.1 p.2 ∂(pointScaleMeasure μ) ≤
      ENNReal.ofReal (C₁ * ρ ^ k)

/-! ## Named statement: the covering assembly -/

/-- **Covering assembly**  at one root, for a given covering.

For a `(K,L)`-regular mixed covering of `P(a,R)`, upper growth `μ(P(b,s)) ≤ A s^k` for
`b ∈ supp μ ∩ P(a,R)`, `0 < s ≤ R`, and the per-model bound
`∫∫_{z ∈ P_i, L⁻¹ dist(z,Γ_i) ≤ r < R_i} β_{μ,T_i}² dμ dr/r ≤ C₁ R_i^k` for every model,
`∫_{P(a,R)} S^R_{μ,𝒜_k} dμ ≤ (A + C₁) K R^k`. Bad pairs are paid by `β_μ² ≤ A` (a model through
the centre and upper growth) and `∬_𝓑 dμ dr/r ≤ K R^k`; good pairs by the per-model bound, the
mixed beta being at most the fixed-type beta, and root packing `Σ_i R_i^k ≤ K R^k`. Local
packing is not used. -/
def CoveringAssemblyStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ (L K A C₁ : ℝ),
    1 ≤ L → 1 ≤ K → 1 ≤ A → 0 < C₁ →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ 𝒞 : RegularMixedCovering k K L μ a R,
    (∀ b ∈ μ.support ∩ Metric.ball a R, ∀ s : ℝ, 0 < s → s ≤ R →
      μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k)) →
    (∀ i : 𝒞.index,
      ∫⁻ p in d2_modelPairs L (𝒞.reference i).carrier (𝒞.center i) (𝒞.radius i),
          betaSq μ k (𝒞.reference i).kind p.1 p.2 ∂(pointScaleMeasure μ) ≤
        ENNReal.ofReal (C₁ * 𝒞.radius i ^ k)) →
    ∫⁻ z in Metric.ball a R, squareEnergy μ k .mixed R z ∂μ ≤
      ENNReal.ofReal ((A + C₁) * K * R ^ k)

end ParabolicRectifiability.QuantitativeCharacterization.ReverseTree
