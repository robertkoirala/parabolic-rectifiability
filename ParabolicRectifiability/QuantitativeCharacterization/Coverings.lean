import ParabolicRectifiability.QuantitativeCharacterization.References
import ParabolicRectifiability.Foundations.ADR
import ParabolicRectifiability.Foundations.BetaPow
import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Metric.Hausdorff

/-! # Carleson energies, regular mixed coverings and approximants

Definitions only, for the quantitative characterization: the Carleson energy `M_β` (the ADR
condition `IsADR` is the shared `ParabolicRectifiability.Foundations.IsADR`), regular mixed
coverings and the `(K,L)` property, the approximants of a covering, and the beta-`p` root
energies.

Conventions.
* Balls are open parabolic balls `Metric.ball`; `E = supp μ` is `μ.support`.
* Every beta and energy uses the whole original `μ` and the mixed family `.mixed`; there is
  no division by ball mass. Energies are `ℝ≥0∞`, with `R^{-k} = (ofReal R)⁻¹ ^ k`.
* "Modulo `dμ dr/r`" uses the product `μ.prod scaleMeasure` on `X × ℝ`, where `scaleMeasure`
  is `dr/r` on positive radii. The bad set and the scale sets are Borel subsets of `(P₀ ∩ E) × (0,R)`, their pairwise
  intersections are null, and their union misses a null part of `(P₀ ∩ E) × (0,R)`.
* Families are indexed by a subset `I` of `ℕ`, so finite, countable and empty families need
  no padding.
* The numerical constants `K, L` are real; the guards `1 ≤ K`, `1 ≤ L` are hypotheses of the
  statements.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

variable {n : ℕ}

/-- The normalized root supremum `sup_{a ∈ S, R > 0} R^{-k} ∫_{P(a,R)} f(R,z) dμ(z)` of a
scale-dependent energy `f(R,·)`, in `ℝ≥0∞`. An empty centre set gives `0`. -/
def rootCarlesonSup (S : Set (Space n)) (μ : Measure (Space n)) (k : ℕ)
    (f : ℝ → Space n → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (a : Space n) (_ : a ∈ S) (R : ℝ) (_ : 0 < R),
    (ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball a R, f R z ∂μ

/-- The Carleson energy
`M_β(μ) = sup_{a ∈ E, R > 0} R^{-k} ∫_{P(a,R)} ∫_0^R β_μ(z,r)² dr/r dμ(z)`,
with the natural mixed-family beta of the whole original source. -/
def carlesonEnergy (μ : Measure (Space n)) (k : ℕ) : ℝ≥0∞ :=
  rootCarlesonSup μ.support μ k (fun R z => squareEnergy μ k .mixed R z)

/-- `M_{S_p} = sup_{a ∈ E, R > 0} R^{-k} ∫_{P(a,R)} S^R_{p,μ} dμ`, with the Foundations energy `energyS` of the
mixed family. -/
def carlesonEnergyS (μ : Measure (Space n)) (k : ℕ) (p : ℝ) : ℝ≥0∞ :=
  rootCarlesonSup μ.support μ k (fun R z => energyS μ k .mixed p R z)

/-- `M_{T_p} = sup_{a ∈ E, R > 0} R^{-k} ∫_{P(a,R)} T^R_{p,μ} dμ`, with the Foundations energy `energyT` of the
mixed family. -/
def carlesonEnergyT (μ : Measure (Space n)) (k : ℕ) (p : ℝ) : ℝ≥0∞ :=
  rootCarlesonSup μ.support μ k (fun R z => energyT μ k .mixed p R z)

/-- The own-type Carleson energy of a reference:
`sup_{a ∈ Γ, R > 0} R^{-k} ∫_{P(a,R)} ∫_0^R β_{σ,T}(z,r)² dr/r dσ(z)`, with `T` the type of
the reference. -/
def referenceEnergy {k : ℕ} {L : ℝ} (ρ : Reference n k L) : ℝ≥0∞ :=
  rootCarlesonSup ρ.carrier ρ.measure k (fun R z => squareEnergy ρ.measure k ρ.kind R z)

/-- The point–scale measure `dμ dr/r` on `X × ℝ`. -/
def pointScaleMeasure (μ : Measure (Space n)) : Measure (Space n × ℝ) :=
  μ.prod scaleMeasure

/-- The tested point–scale pairs `(P₀ ∩ E) × (0,R)` of the root `P₀ = P(a,R)`. -/
def rootPairs (μ : Measure (Space n)) (a : Space n) (R : ℝ) : Set (Space n × ℝ) :=
  (Metric.ball a R ∩ μ.support) ×ˢ Ioo 0 R

open scoped Classical in
/-- A `(K,L)`-regular mixed parabolic covering of `μ` on `P₀ = P(a,R)`.
The data are a countable family of typed `L`-references `(Γ_i, σ_i)`, balls
`P_i = P(a_i,R_i)`, a bad set `𝓑` and scale sets `𝓤_i`. The fields are the root packing,
local packing and scale-cover conditions. The indicator in the local packing sum uses
classical decidability. -/
structure RegularMixedCovering (k : ℕ) (K L : ℝ) (μ : Measure (Space n)) (a : Space n)
    (R : ℝ) where
  /-- The finite or countable index set. -/
  index : Set ℕ
  /-- The typed `L`-references `(Γ_i, σ_i)`. -/
  reference : index → Reference n k L
  /-- Ball centres `a_i` and radii `R_i`. -/
  center : index → Space n
  radius : index → ℝ
  /-- The bad set `𝓑` and the scale sets `𝓤_i`. -/
  badSet : Set (Space n × ℝ)
  scaleSet : index → Set (Space n × ℝ)
  /-- Root packing: `a_i ∈ E`, `R_i > 0`,
  `P_i ⊂ P(a,LR)`, `P_i ∩ Γ_i ≠ ∅`, `Σ_i R_i^k ≤ K R^k`. -/
  center_mem_support : ∀ i, center i ∈ μ.support
  radius_pos : ∀ i, 0 < radius i
  ball_subset : ∀ i, Metric.ball (center i) (radius i) ⊆ Metric.ball a (L * R)
  ball_meets_carrier : ∀ i, (Metric.ball (center i) (radius i) ∩ (reference i).carrier).Nonempty
  root_packing : ∑' i, ENNReal.ofReal (radius i) ^ k ≤ ENNReal.ofReal (K * R ^ k)
  /-- Local packing of the same family: for every
  `b ∈ X` and `s > 0`, `Σ_{a_i ∈ P(b,s), R_i ≤ s} R_i^k ≤ K s^k`. -/
  local_packing : ∀ (b : Space n) (s : ℝ), 0 < s →
    (∑' i, if center i ∈ Metric.ball b s ∧ radius i ≤ s then
        ENNReal.ofReal (radius i) ^ k else 0) ≤ ENNReal.ofReal (K * s ^ k)
  /-- `𝓑` and the `𝓤_i` are Borel subsets of `(P₀ ∩ E) × (0,R)`. -/
  measurable_badSet : MeasurableSet badSet
  measurable_scaleSet : ∀ i, MeasurableSet (scaleSet i)
  badSet_subset : badSet ⊆ rootPairs μ a R
  scaleSet_subset : ∀ i, scaleSet i ⊆ rootPairs μ a R
  /-- They partition `(P₀ ∩ E) × (0,R)` modulo `dμ dr/r`: pairwise intersections are null
  and their union misses only a null set. -/
  bad_inter_scale_null : ∀ i, pointScaleMeasure μ (badSet ∩ scaleSet i) = 0
  scale_inter_scale_null : ∀ i j, i ≠ j → pointScaleMeasure μ (scaleSet i ∩ scaleSet j) = 0
  cover_null : pointScaleMeasure μ (rootPairs μ a R \ (badSet ∪ ⋃ i, scaleSet i)) = 0
  /-- Scale cover:
  `𝓤_i ⊂ {(z,r) : z ∈ P₀ ∩ P_i, L⁻¹ dist(z,Γ_i) ≤ r < R_i}`. -/
  scaleSet_cover : ∀ i, scaleSet i ⊆
    {p : Space n × ℝ | p.1 ∈ Metric.ball a R ∩ Metric.ball (center i) (radius i) ∧
      L⁻¹ * Metric.infDist p.1 (reference i).carrier ≤ p.2 ∧ p.2 < radius i}
  /-- Bad logarithmic mass: `∬_𝓑 dμ dr/r ≤ K R^k`. -/
  bad_bound : pointScaleMeasure μ badSet ≤ ENNReal.ofReal (K * R ^ k)

namespace RegularMixedCovering

variable {k : ℕ} {K L : ℝ} {μ : Measure (Space n)} {a : Space n} {R : ℝ}
variable (𝒞 : RegularMixedCovering k K L μ a R)

/-- The model ball `P_i = P(a_i, R_i)`. -/
def ball (i : 𝒞.index) : Set (Space n) :=
  Metric.ball (𝒞.center i) (𝒞.radius i)

/-- The multiplicity `m(z) = Σ_i 1_{P_i}(z) ∈ ℕ∞`, the number of model balls containing `z`. -/
def multiplicity (z : Space n) : ℕ∞ :=
  {i : 𝒞.index | z ∈ 𝒞.ball i}.encard

/-- The union of the typed traces `P_i ∩ Γ_i` over the references of type `T`. -/
def typedTrace (T : FamilyKind) : Set (Space n) :=
  ⋃ (i : 𝒞.index) (_ : (𝒞.reference i).kind = T), 𝒞.ball i ∩ (𝒞.reference i).carrier

/-- The retained approximant `μ^N_{T,P₀} = μ ⌊ (F_T ∩ {m ≤ N})`, for a given typed set `F = F_T`. -/
def approximant (F : Set (Space n)) (N : ℕ) : Measure (Space n) :=
  μ.restrict (F ∩ {z | 𝒞.multiplicity z ≤ (N : ℕ∞)})

/-- The residual `e^N_{P₀} = μ ⌊ (P₀ ∩ {m > N})`. -/
def residual (N : ℕ) : Measure (Space n) :=
  μ.restrict (Metric.ball a R ∩ {z | (N : ℕ∞) < 𝒞.multiplicity z})

/-- The typed split of the root: disjoint Borel
`F_H, F_V ⊂ P₀`, each inside the union of the typed traces of its type, carrying `μ ⌊ P₀`. -/
structure IsTypedTraceSplit (FH FV : Set (Space n)) : Prop where
  measurable_horizontal : MeasurableSet FH
  measurable_vertical : MeasurableSet FV
  disjoint : Disjoint FH FV
  horizontal_subset_root : FH ⊆ Metric.ball a R
  vertical_subset_root : FV ⊆ Metric.ball a R
  horizontal_subset_trace : FH ⊆ 𝒞.typedTrace .horizontal
  vertical_subset_trace : FV ⊆ 𝒞.typedTrace .vertical
  null_remainder : μ (Metric.ball a R \ (FH ∪ FV)) = 0

/-- The measure identity at every level:
`μ ⌊ P₀ = μ^N_H + μ^N_V + e^N` for every `N ≥ 0`. -/
def MeasureIdentity (FH FV : Set (Space n)) : Prop :=
  ∀ N : ℕ, μ.restrict (Metric.ball a R) = 𝒞.approximant FH N + 𝒞.approximant FV N + 𝒞.residual N

/-- The relative residual tail at every level, with tail constant `C_tail` and the
covering constant `K`:
`e^N(P₀) ≤ 2 exp(-N / (C_tail K)) μ(P₀)` for every `N ≥ 0`. -/
def RelativeTail (Ctail : ℝ) : Prop :=
  ∀ N : ℕ, 𝒞.residual N (Metric.ball a R) ≤
    ENNReal.ofReal (2 * Real.exp (-(N : ℝ) / (Ctail * K))) * μ (Metric.ball a R)

/-- The canonical conclusions of the approximants
for a typed split: every `μ^N_H` is horizontally rectifiable and every `μ^N_V` regularly
vertically rectifiable (`IsRegularlyRectifiableMeasure` of that type); the retained measures
increase and converge on every Borel set to the canonical parts `μ_H ⌊ P₀`, `μ_V ⌊ P₀`, where
`μ_T = μ ⌊ {S^1_{μ,T} < ∞}` (at the endpoint `1`; the canonical measures do not
depend on the endpoint); the residual decreases and its total mass, which is its total
variation, tends to zero. -/
structure HasCanonicalLimits (FH FV : Set (Space n)) : Prop where
  horizontal_rectifiable : ∀ N : ℕ,
    IsRegularlyRectifiableMeasure .horizontal k (𝒞.approximant FH N)
  vertical_rectifiable : ∀ N : ℕ,
    IsRegularlyRectifiableMeasure .vertical k (𝒞.approximant FV N)
  horizontal_monotone : Monotone (fun N : ℕ => 𝒞.approximant FH N)
  vertical_monotone : Monotone (fun N : ℕ => 𝒞.approximant FV N)
  horizontal_tendsto : ∀ S : Set (Space n), MeasurableSet S →
    Filter.Tendsto (fun N : ℕ => 𝒞.approximant FH N S) Filter.atTop
      (nhds ((μ.restrict {z | squareEnergy μ k .horizontal 1 z < ⊤}).restrict
        (Metric.ball a R) S))
  vertical_tendsto : ∀ S : Set (Space n), MeasurableSet S →
    Filter.Tendsto (fun N : ℕ => 𝒞.approximant FV N S) Filter.atTop
      (nhds ((μ.restrict {z | squareEnergy μ k .vertical 1 z < ⊤}).restrict
        (Metric.ball a R) S))
  residual_antitone : Antitone (fun N : ℕ => 𝒞.residual N)
  residual_tendsto_zero :
    Filter.Tendsto (fun N : ℕ => 𝒞.residual N Set.univ) Filter.atTop (nhds 0)

end RegularMixedCovering

/-- `(K,L)`-quantitative mixed parabolic rectifiability: `μ ≪ H_P^k` and every
support-centred root `P(a,R)`, `a ∈ supp μ`, `R > 0`, has a `(K,L)`-regular mixed parabolic
covering. The covering may depend on the root; the constants do not. -/
def IsQuantitativelyMixedRectifiable (k : ℕ) (K L : ℝ) (μ : Measure (Space n)) : Prop :=
  μ ≪ hausdorffP n k ∧
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → Nonempty (RegularMixedCovering k K L μ a R)

end ParabolicRectifiability.QuantitativeCharacterization
