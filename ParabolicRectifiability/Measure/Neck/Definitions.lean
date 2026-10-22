import ParabolicRectifiability.Geometry.Neck.Region
import ParabolicRectifiability.Decomposition.Interfaces
import ParabolicRectifiability.Measure.BetaTail

/-!
# Source-side definitions for the measure neck construction

Definitions, together with a few elementary lemmas, for the decomposition of a
measure into neck regions: from a single neck built on a source, through one
contracting step and the countable neck decomposition, to the density carrier.
Nothing in this file assumes a neck theorem, a packing estimate or a graph cover.

* `tailEnergy`: the scale integral of the natural beta square above a cutoff.
* `IsSourceCutoff`: a Borel cutoff `f : S → [0,R]` whose positive values are
  locally finite in `(0,R]`.
* `firstSwitchCutoff`: the dyadic first change of preferred type.
* `NeckSourcePartition`: the exact Borel source assignments of a neck.
* `CollapsedAssignmentBound`: the estimate for collapsed assignments.
* `ContractingStep`: the data of one contracting step.
* `NeckDecomposition`: the countable rooted tree, its compact carrier and its
  global estimates.
* `densityCarrier`: the all-radius lower-mass carrier `K_a`.
* `truncatedAtomicSource`: the scale-truncated atomic source of a finite family of balls.

All sources are restrictions of the original measure to Borel sets; no
measure is formed by subtracting possibly infinite masses. The vertices of the
countable tree are finite sequences of child indices.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-! ## Energies -/

/-- The tail energy `∫_{s}^{∞} β_{ν,F,k}(z,r)^2 dr/r` of the natural beta square for
the unchanged source `ν`, with the scale measure `dr/r`. The value may be infinite.
At `s = 0` it is the all-scale energy. -/
def tailEnergy {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (F : FamilyKind) (s : ℝ)
    (z : Space n) : ℝ≥0∞ :=
  ∫⁻ r in Ioi s, betaSq ν k F z r ∂scaleMeasure

theorem tailEnergy_zero {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (F : FamilyKind)
    (z : Space n) : tailEnergy ν k F 0 z = allScaleEnergy ν k F z := rfl

/-- The all-scale energy is a Borel function of the reference point. -/
theorem measurable_allScaleEnergy {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ) (T : FamilyKind) : Measurable (allScaleEnergy μ k T) :=
  (measurable_betaSq μ k T).lintegral_prod_right (ν := scaleMeasure.restrict (Ioi 0))

/-- Restricting the source to a Borel set decreases the all-scale energy at every point
(the restriction monotonicity of `betaSq`). This is why every child of a contracting
step inherits the *original* bound, not an inflated fixed-family bound. -/
theorem allScaleEnergy_restrict_le_original {n : ℕ} (μ : Measure (Space n))
    (G : Set (Space n)) (k : ℕ) (T : FamilyKind) (z : Space n) :
    allScaleEnergy (μ.restrict G) k T z ≤ allScaleEnergy μ k T z :=
  lintegral_mono fun r => betaSq_restrict_le μ G k T z r

/-! ## Cutoffs -/

/-- A cutoff for the source set `S ⊆ P(q,R)`: a Borel
function with values in `[0,R]` on `S` whose positive values are locally finite in
`(0,R]`, i.e. above every positive level only finitely many values occur. Global
measurability is no restriction: on a Borel `S` any Borel function on `S` extends by
zero. -/
structure IsSourceCutoff {n : ℕ} (S : Set (Space n)) (R : ℝ) (f : Space n → ℝ) : Prop where
  measurable : Measurable f
  nonneg : ∀ z ∈ S, 0 ≤ f z
  le_radius : ∀ z ∈ S, f z ≤ R
  finite_values : ∀ b : ℝ, 0 < b → (f '' S ∩ Ici b).Finite

/-- The zero cutoff, used in a contracting step for a fixed family or when only one
type is available. -/
theorem isSourceCutoff_zero {n : ℕ} (S : Set (Space n)) {R : ℝ} (hR : 0 ≤ R) :
    IsSourceCutoff S R (fun _ => 0) where
  measurable := measurable_const
  nonneg := fun _ _ => le_rfl
  le_radius := fun _ _ => hR
  finite_values := fun _ _ => (Set.finite_singleton (0 : ℝ)).subset fun x hx => by
    obtain ⟨⟨z, -, rfl⟩, -⟩ := hx
    exact Set.mem_singleton _

namespace NeckType

/-- The other neck type. -/
def other : NeckType → NeckType
  | horizontal => vertical
  | vertical => horizontal

/-- The separation constant of the candidate nets in the source construction:
`1/4` for horizontal and `1` for vertical necks. -/
def sourceSeparation : NeckType → ℝ
  | horizontal => 1 / 4
  | vertical => 1

/-- The represented set of a model of the given type with spatial plane `L` (of any
rank) and, in the horizontal case, time level `τ`. Used for the lower-rank models of
collapsed assignments (`CollapsedAssignmentBound`): horizontal `L × {τ}`, vertical `L × ℝ`. -/
def lowerModelSet {n m : ℕ} : NeckType → AffineSpatialPlane n m → ℝ → Set (Space n)
  | horizontal, L, τ => {z | z.1 ∈ L.toSet ∧ z.2.val = τ}
  | vertical, L, _ => {z | z.1 ∈ L.toSet}

end NeckType

/-- The unnormalized fitting error `I_F(x,r) = inf_L ∫_{P(x,r)} d_P(z,L)^2 dν(z)` of the
family `F`; for `r > 0` one has `I_F(x,r) = r^(k+2) β²_{ν,F,k}(x,r)`. -/
def typeFittingError {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (F : FamilyKind) (x : Space n)
    (r : ℝ) : ℝ≥0∞ :=
  ⨅ L : Models n k F, fit ν L x r

/-- At `x` and radius `r` the other type has strictly smaller fitting error than `T`. -/
def PrefersOtherType {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (T : NeckType) (x : Space n)
    (r : ℝ) : Prop :=
  typeFittingError ν k T.other.toFamilyKind x r < typeFittingError ν k T.toFamilyKind x r

open Classical in
/-- The first-switch cutoff: the largest radius
`R 2^{-j}`, `j ≥ 0`, at which the other type has strictly smaller error, and `0` if
there is none. -/
def firstSwitchCutoff {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (T : NeckType) (R : ℝ)
    (x : Space n) : ℝ :=
  if h : ∃ j : ℕ, PrefersOtherType ν k T x (R / 2 ^ j) then R / 2 ^ Nat.find h else 0

/-! ## The source partition of one neck -/

/-- The exact source assignments of a neck `N` constructed from a source carried by `S`
with cutoff `f`.

* `errorSet`: the discarded source `e`;
* `coreSet`: the core assignment `S_∞`, carried by `S ∩ {f = 0}` and contained in the
  closed core `C₀` (so the core restriction is supported on `C₀`);
* `assignment c`: the assignment of the stopping center `c`, inside the open hole
  `P(c, d_c)`;
* `terminal`: the terminal stopping centers, with `d_c = f(c)` and `f ≤ d_c` on their
  assignments; every other stopping center is collapsed, with `d_c = 5 r_j` at a stage
  `j ≥ 1` and `f < r_j` on its assignment.

The sets are Borel subsets of `S`, pairwise disjoint, and cover `S`. -/
structure NeckSourcePartition {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n}
    {R c₀ Cd Cs σ δ E κ θ γ : ℝ} (S : Set (Space n)) (f : Space n → ℝ)
    (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ) where
  errorSet : Set (Space n)
  coreSet : Set (Space n)
  assignment : Space n → Set (Space n)
  terminal : Set (Space n)
  measurableSet_errorSet : MeasurableSet errorSet
  measurableSet_coreSet : MeasurableSet coreSet
  measurableSet_assignment : ∀ c ∈ N.stopping, MeasurableSet (assignment c)
  errorSet_subset : errorSet ⊆ S
  coreSet_subset : coreSet ⊆ S
  assignment_subset : ∀ c ∈ N.stopping, assignment c ⊆ S
  cover : S ⊆ errorSet ∪ coreSet ∪ ⋃ c ∈ N.stopping, assignment c
  disjoint_errorSet_coreSet : Disjoint errorSet coreSet
  disjoint_errorSet_assignment : ∀ c ∈ N.stopping, Disjoint errorSet (assignment c)
  disjoint_coreSet_assignment : ∀ c ∈ N.stopping, Disjoint coreSet (assignment c)
  disjoint_assignment : ∀ c ∈ N.stopping, ∀ c' ∈ N.stopping, c ≠ c' →
    Disjoint (assignment c) (assignment c')
  cutoff_coreSet : ∀ z ∈ coreSet, f z = 0
  coreSet_subset_core : coreSet ⊆ N.core
  assignment_subset_ball : ∀ c ∈ N.stopping, assignment c ⊆ Metric.ball c (N.radius c)
  terminal_subset : terminal ⊆ N.stopping
  terminal_radius : ∀ c ∈ terminal, c ∈ S ∧ N.radius c = f c
  terminal_cutoff : ∀ c ∈ terminal, ∀ z ∈ assignment c, f z ≤ N.radius c
  collapsed_radius : ∀ c ∈ N.stopping, c ∉ terminal → ∃ j : ℕ, 1 ≤ j ∧
    N.radius c = 5 * N.family.scale j ∧ ∀ z ∈ assignment c, f z < N.family.scale j

/-- The collapsed-assignment estimate for an
assignment `A` with radius `d`: at positive spatial rank a model of the same type and
one smaller spatial rank fits `ν|A` with error at most `C (a + B) d^{k+2}`; at vertical
rank zero the mass of `A` is less than `a d^2`. -/
def CollapsedAssignmentBound {n : ℕ} (T : NeckType) (k : ℕ) (ν : Measure (Space n))
    (A : Set (Space n)) (d a B C : ℝ) : Prop :=
  (0 < T.rank k → ∃ (L : AffineSpatialPlane n (T.rank k - 1)) (τ : ℝ),
      ∫⁻ z in A, Metric.infEDist z (T.lowerModelSet L τ) ^ 2 ∂ν ≤
        ENNReal.ofReal (C * (a + B) * d ^ (k + 2))) ∧
    (T.rank k = 0 → ν A < ENNReal.ofReal (a * d ^ 2))

/-! ## One contracting step -/

/-- The data of one contracting decomposition step for
a source carried by `S ⊆ P(q,R)`, built on the neck `N`. Every child comes from one
stopping hole `P(c, d_c)` of `N` (its *parent* stopping center `c`), lies in that hole,
and has radius exactly `3ρ d_c` (covariance failure) or `2ε d_c` (change of type); each
hole has finitely many children. The child sources are Borel subsets of `S`; the child
measures are the restrictions of the parent source to them (see
`ContractingStep.childSource_energy_le`). -/
structure ContractingStep {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n}
    {R c₀ Cd Cs σ δ E κ θ γ : ℝ} (ν : Measure (Space n)) (S : Set (Space n))
    (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ) (B Eerr ρ ε : ℝ) where
  errorSet : Set (Space n)
  coreSet : Set (Space n)
  childIndex : Set ℕ
  childSource : ℕ → Set (Space n)
  childCenter : ℕ → Space n
  childRadius : ℕ → ℝ
  childParent : ℕ → Space n
  measurableSet_errorSet : MeasurableSet errorSet
  measurableSet_coreSet : MeasurableSet coreSet
  measurableSet_childSource : ∀ w ∈ childIndex, MeasurableSet (childSource w)
  errorSet_subset : errorSet ⊆ S
  coreSet_subset : coreSet ⊆ S
  childSource_subset : ∀ w ∈ childIndex, childSource w ⊆ S
  cover : S ⊆ errorSet ∪ coreSet ∪ ⋃ w ∈ childIndex, childSource w
  disjoint_errorSet_coreSet : Disjoint errorSet coreSet
  disjoint_errorSet_child : ∀ w ∈ childIndex, Disjoint errorSet (childSource w)
  disjoint_coreSet_child : ∀ w ∈ childIndex, Disjoint coreSet (childSource w)
  disjoint_children : ∀ w ∈ childIndex, ∀ w' ∈ childIndex, w ≠ w' →
    Disjoint (childSource w) (childSource w')
  coreSet_subset_core : coreSet ⊆ N.core
  errorSet_le : ν errorSet ≤ ENNReal.ofReal (Eerr * B * R ^ k)
  childParent_mem : ∀ w ∈ childIndex, childParent w ∈ N.stopping
  childSource_subset_hole : ∀ w ∈ childIndex,
    childSource w ⊆ Metric.ball (childParent w) (N.radius (childParent w))
  childSource_subset_ball : ∀ w ∈ childIndex,
    childSource w ⊆ Metric.ball (childCenter w) (childRadius w)
  childRadius_eq : ∀ w ∈ childIndex,
    childRadius w = 3 * ρ * N.radius (childParent w) ∨
      childRadius w = 2 * ε * N.radius (childParent w)
  finite_children : ∀ c : Space n, {w | w ∈ childIndex ∧ childParent w = c}.Finite
  childRadius_le : ∀ w ∈ childIndex, childRadius w ≤ R / 2
  child_content_le : ∑' w : childIndex, ENNReal.ofReal (childRadius w ^ k) ≤
    ENNReal.ofReal (R ^ k / 2)

/-- Children inherit the original bound: if the parent source has all-scale energy at
most `B` at every point of `S` (for the family `F`), then each child restriction has
all-scale energy at most `B` at every point of its own source set. No inflated
fixed-family bound is used. -/
theorem ContractingStep.childSource_energy_le {n k : ℕ} {T : NeckType} {ι : Type*}
    {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ} {ν : Measure (Space n)} {S : Set (Space n)}
    {N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ} {B Eerr ρ ε : ℝ}
    (D : ContractingStep ν S N B Eerr ρ ε) (F : FamilyKind)
    (hB : ∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B) {w : ℕ}
    (hw : w ∈ D.childIndex) :
    ∀ z ∈ D.childSource w,
      allScaleEnergy (ν.restrict (D.childSource w)) k F z ≤ ENNReal.ofReal B :=
  fun z hz => (allScaleEnergy_restrict_le_original ν _ k F z).trans
    (hB z (D.childSource_subset w hw hz))

/-! ## The countable decomposition -/

/-- The infinite-path residual set `A_∞ = ⋂_j ⋃_{depth v = j} S_v` of a tree of
source sets. -/
def treeResidual {X : Type*} (V : Set (List ℕ)) (s : List ℕ → Set X) : Set X :=
  ⋂ j : ℕ, ⋃ v ∈ V, ⋃ (_ : v.length = j), s v

/-- The countable neck decomposition of the original source `ν`, carried by `S ⊆ P(q,R)`,
for the testing family `F`.

Vertices are finite sequences of child indices; the root is `[]` with source `S` and
container `P(q,R)`. At each vertex `v` the source `S_v` is partitioned into Borel sets:
the error assignment `e_v`, the core assignment (contained in the compact core `C_v`)
and the child sources. Local estimates: `e_v(X) ≤ E B R_v^k`, `R_w ≤ R_v/2`,
`∑_{children} R_w^k ≤ R_v^k / 2`.

Global outputs: the identity `ν = e + ∑_v ν|core assignment + ν_res` with
`e(X) ≤ C B R^k`; `∑_v R_v^k ≤ 2 R^k`; a compact carrier `K ⊆ closure P(q,R)` carrying
every nonerror term, so `ν(X \ K) ≤ C B R^k`; `H^k_P(K \ ⋃_v C_v) = 0`; the residual
`ν_res = ν|A_∞` is retained, and `A_∞` is Hausdorff-null although `ν(A_∞)` may be
positive; the variable-radius packing `∑ r_i^k ≤ C R^k` for every finite or countable
disjoint family of open balls centered on `K` with `0 < r_i ≤ R`; and its consequences
for separated sets and neighborhoods. Every core type is available and respects the
testing family. -/
structure NeckDecomposition {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (F : FamilyKind)
    (S : Set (Space n)) (q : Space n) (R B E C : ℝ) where
  vertices : Set (List ℕ)
  root_mem : [] ∈ vertices
  parent_mem : ∀ v i, v ++ [i] ∈ vertices → v ∈ vertices
  source : List ℕ → Set (Space n)
  center : List ℕ → Space n
  radius : List ℕ → ℝ
  errorSet : List ℕ → Set (Space n)
  coreSet : List ℕ → Set (Space n)
  core : List ℕ → Set (Space n)
  coreType : List ℕ → NeckType
  source_root : source [] = S
  center_root : center [] = q
  radius_root : radius [] = R
  measurableSet_source : ∀ v ∈ vertices, MeasurableSet (source v)
  measurableSet_errorSet : ∀ v ∈ vertices, MeasurableSet (errorSet v)
  measurableSet_coreSet : ∀ v ∈ vertices, MeasurableSet (coreSet v)
  radius_pos : ∀ v ∈ vertices, 0 < radius v
  source_subset_ball : ∀ v ∈ vertices, source v ⊆ Metric.ball (center v) (radius v)
  errorSet_subset : ∀ v ∈ vertices, errorSet v ⊆ source v
  coreSet_subset : ∀ v ∈ vertices, coreSet v ⊆ source v
  child_subset : ∀ v i, v ++ [i] ∈ vertices → source (v ++ [i]) ⊆ source v
  cover : ∀ v ∈ vertices, source v ⊆
    errorSet v ∪ coreSet v ∪ ⋃ (i : ℕ) (_ : v ++ [i] ∈ vertices), source (v ++ [i])
  disjoint_errorSet_coreSet : ∀ v ∈ vertices, Disjoint (errorSet v) (coreSet v)
  disjoint_errorSet_child : ∀ v i, v ++ [i] ∈ vertices →
    Disjoint (errorSet v) (source (v ++ [i]))
  disjoint_coreSet_child : ∀ v i, v ++ [i] ∈ vertices →
    Disjoint (coreSet v) (source (v ++ [i]))
  disjoint_children : ∀ v i j, v ++ [i] ∈ vertices → v ++ [j] ∈ vertices → i ≠ j →
    Disjoint (source (v ++ [i])) (source (v ++ [j]))
  errorSet_le : ∀ v ∈ vertices, ν (errorSet v) ≤ ENNReal.ofReal (E * B * radius v ^ k)
  child_radius_le : ∀ v i, v ++ [i] ∈ vertices → radius (v ++ [i]) ≤ radius v / 2
  child_content_le : ∀ v ∈ vertices,
    ∑' i : {i : ℕ // v ++ [i] ∈ vertices}, ENNReal.ofReal (radius (v ++ [i.1]) ^ k) ≤
      ENNReal.ofReal (radius v ^ k / 2)
  coreSet_subset_core : ∀ v ∈ vertices, coreSet v ⊆ core v
  coreType_available : ∀ v ∈ vertices, (coreType v).Available n k
  coreType_family : ∀ v ∈ vertices, F = .mixed ∨ F = (coreType v).toFamilyKind
  measure_eq : ν = Measure.sum (fun v : vertices => ν.restrict (errorSet v)) +
    Measure.sum (fun v : vertices => ν.restrict (coreSet v)) +
    ν.restrict (treeResidual vertices source)
  error_total : Measure.sum (fun v : vertices => ν.restrict (errorSet v)) univ ≤
    ENNReal.ofReal (C * B * R ^ k)
  radius_total : ∑' v : vertices, ENNReal.ofReal (radius v ^ k) ≤ ENNReal.ofReal (2 * R ^ k)
  carrier : Set (Space n)
  isCompact_carrier : IsCompact carrier
  carrier_subset : carrier ⊆ Metric.closedBall q R
  core_subset_carrier : ∀ v ∈ vertices, core v ⊆ carrier
  residual_subset_carrier : treeResidual vertices source ⊆ carrier
  measure_compl_carrier_le : ν carrierᶜ ≤ ENNReal.ofReal (C * B * R ^ k)
  null_remainder : hausdorffP n k (carrier \ ⋃ v ∈ vertices, core v) = 0
  residual_null : hausdorffP n k (treeResidual vertices source) = 0
  packing : ∀ (I : Type) [Countable I] (z : I → Space n) (r : I → ℝ),
    (∀ i, z i ∈ carrier) → (∀ i, 0 < r i ∧ r i ≤ R) →
    (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
    ∑' i, ENNReal.ofReal (r i) ^ k ≤ ENNReal.ofReal (C * R ^ k)
  separated : ∀ r : ℝ, 0 < r → r ≤ R → ∀ P : Finset (Space n),
    (↑P : Set (Space n)) ⊆ carrier → (∀ x ∈ P, ∀ y ∈ P, x ≠ y → r ≤ dist x y) →
    (P.card : ℝ) ≤ C * (R / r) ^ k
  minkowski : ∀ r : ℝ, 0 < r → r ≤ R →
    parabolicVolume n {z | Metric.infEDist z carrier < ENNReal.ofReal r} ≤
      ENNReal.ofReal (C * R ^ k * r ^ (n + 2 - k))

namespace NeckDecomposition

variable {n k : ℕ} {ν : Measure (Space n)} {F : FamilyKind} {S : Set (Space n)}
  {q : Space n} {R B E C : ℝ}

/-- The natural-number codes of the vertices whose core has type `T`
(vertices are decoded by `Denumerable.ofNat (List ℕ)`). -/
def typeIndex (D : NeckDecomposition ν k F S q R B E C) (T : NeckType) : Set ℕ :=
  {m | Denumerable.ofNat (List ℕ) m ∈ D.vertices ∧
    D.coreType (Denumerable.ofNat (List ℕ) m) = T}

theorem mem_typeIndex (D : NeckDecomposition ν k F S q R B E C) {T : NeckType} {m : ℕ} :
    m ∈ D.typeIndex T ↔ Denumerable.ofNat (List ℕ) m ∈ D.vertices ∧
      D.coreType (Denumerable.ofNat (List ℕ) m) = T := Iff.rfl

/-- Every vertex core is one of the cores indexed by type. -/
theorem iUnion_core_subset (D : NeckDecomposition ν k F S q R B E C) :
    (⋃ v ∈ D.vertices, D.core v) ⊆
      (⋃ i : D.typeIndex .horizontal, D.core (Denumerable.ofNat (List ℕ) i)) ∪
        ⋃ i : D.typeIndex .vertical, D.core (Denumerable.ofNat (List ℕ) i) := by
  intro z hz
  simp only [mem_iUnion] at hz
  obtain ⟨v, hv, hzv⟩ := hz
  have henc : Denumerable.ofNat (List ℕ) (Encodable.encode v) = v :=
    Denumerable.ofNat_encode v
  cases hty : D.coreType v with
  | horizontal =>
    refine mem_union_left _ (mem_iUnion.mpr ⟨⟨Encodable.encode v, ?_⟩, ?_⟩)
    · rw [mem_typeIndex, henc]
      exact ⟨hv, hty⟩
    · show z ∈ D.core (Denumerable.ofNat (List ℕ) (Encodable.encode v))
      rw [henc]
      exact hzv
  | vertical =>
    refine mem_union_right _ (mem_iUnion.mpr ⟨⟨Encodable.encode v, ?_⟩, ?_⟩)
    · rw [mem_typeIndex, henc]
      exact ⟨hv, hty⟩
    · show z ∈ D.core (Denumerable.ofNat (List ℕ) (Encodable.encode v))
      rw [henc]
      exact hzv

/-- No horizontal core occurs for a vertical testing family or an unavailable
horizontal type. -/
theorem typeIndex_horizontal_eq_empty (D : NeckDecomposition ν k F S q R B E C)
    (h : F = .vertical ∨ ¬ (1 ≤ k ∧ k ≤ n)) : D.typeIndex .horizontal = ∅ := by
  ext m
  simp only [mem_empty_iff_false, iff_false]
  intro hm
  obtain ⟨hv, hty⟩ := D.mem_typeIndex.mp hm
  have hav := D.coreType_available _ hv
  have hfam := D.coreType_family _ hv
  rw [hty] at hav hfam
  rcases h with h | h
  · subst h
    rcases hfam with h' | h' <;> cases h'
  · exact h hav

/-- No vertical core occurs for a horizontal testing family or an unavailable
vertical type. -/
theorem typeIndex_vertical_eq_empty (D : NeckDecomposition ν k F S q R B E C)
    (h : F = .horizontal ∨ ¬ (2 ≤ k ∧ k ≤ n + 2)) : D.typeIndex .vertical = ∅ := by
  ext m
  simp only [mem_empty_iff_false, iff_false]
  intro hm
  obtain ⟨hv, hty⟩ := D.mem_typeIndex.mp hm
  have hav := D.coreType_available _ hv
  have hfam := D.coreType_family _ hv
  rw [hty] at hav hfam
  rcases h with h | h
  · subst h
    rcases hfam with h' | h' <;> cases h'
  · exact h hav

end NeckDecomposition

/-! ## Density carrier and discrete sources -/

/-- The all-radius lower-mass carrier:
`K_a = {z ∈ supp ν : ν(closure P(z,r)) ≥ a r^k for every 0 < r ≤ 1}`. -/
def densityCarrier {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (a : ℝ) : Set (Space n) :=
  {z | z ∈ ν.support ∧
    ∀ r : ℝ, 0 < r → r ≤ 1 → ENNReal.ofReal (a * r ^ k) ≤ ν (Metric.closedBall z r)}

/-- The scale-truncated atomic source:
`σ_s = ∑_{r_j ≤ s} b_j r_j^k δ_{z_j}` for the finite family `(z_j, r_j)` with weights
`b_j = w j`. -/
def truncatedAtomicSource {n l : ℕ} (k : ℕ) (z : Fin l → Space n) (r w : Fin l → ℝ)
    (s : ℝ) : Measure (Space n) :=
  ∑ j ∈ Finset.univ.filter (fun j => r j ≤ s),
    ENNReal.ofReal (w j * r j ^ k) • Measure.dirac (z j)

end ParabolicRectifiability
