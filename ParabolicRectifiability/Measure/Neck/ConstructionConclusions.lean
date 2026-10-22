import ParabolicRectifiability.Measure.Neck.Construction
import ParabolicRectifiability.Geometry.Neck.ChargingConclusions

/-!
# Intermediate conclusions of the neck construction

Definitions naming the intermediate conclusions of the source neck construction, the
contracting step and the step tree, together with two short lemmas about coherent
families:

* `SourceSetup.IsRootChoice`, `ConstructionData.IsStageChoice`: the root and stage
  selection rules;
* `ConstructionData.NodeChargeData`: the data charging the node errors;
* `ConstructionData.StageInvariants`: invariants of the stage sets;
* `ConstructionData.SeparationFacts`: separation and bounds of the centers;
* `ConstructionData.IsGenuineRecord`, `ConstructionData.FittedTimeComparison`,
  `ConstructionData.GenuineTimeCompatible`: time compatibility of the records;
* `StepChildren`: the countable child indexing of a contracting step;
* `StepTree.subtreeSet`: the subtree set of a vertex;
* `CoherentFamily.squareBound_of_upTo` and `CoherentFamily.horizontal_occurrence_witness`.

The origin map of `StepChildren` is defined on the active children `childIndex` only, so
that the structure is inhabited also for an empty neck and when every hole discards all
of its source.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-! ## Intermediate conclusions

The definitions name the intermediate conclusions passed from one step of the
construction to the next. -/

/-- The root rules of `ConstructionData.IsSourceConstruction` for a root choice `(L, τ, z)`:
the model set `T.lowerModelSet L τ` minimizes the global error of the original
source among all models of type `T`, and the artificial root `z` lies on `L` (at time `τ`
in the horizontal case) within `R` of `q`. -/
def SourceSetup.IsRootChoice {n : ℕ} (P : SourceSetup n) (k : ℕ) (T : NeckType)
    (L : AffineSpatialPlane n (T.rank k)) (τ : ℝ) (z : Space n) : Prop :=
  (∀ M : Models n k T.toFamilyKind,
      ∫⁻ y, Metric.infEDist y (T.lowerModelSet L τ) ^ 2 ∂P.ν ≤ ∫⁻ y, modelCost M y ∂P.ν) ∧
    z.1 ∈ L.toSet ∧ (T = .horizontal → z.2.val = τ) ∧ dist z P.q ≤ P.R

/-- The stage-`j` selection rules of `ConstructionData.IsSourceConstruction` for an
entering set `E`, stated for the stage-`j` fields of `D` only: decreasing
terminal selection from `E` with `f ≥ r_j`, the end of the terminal phase, a maximal
`κ r_j`-separated net of the remainder, and attained original-source fits on
`P(g, 40 r_j)`. -/
structure ConstructionData.IsStageChoice {n k : ℕ} {T : NeckType} (D : ConstructionData n k T)
    (P : SourceSetup n) (j : ℕ) (E : Set (Space n)) : Prop where
  term_mem : ∀ i, i < D.termCount j →
    D.term j i ∈ E \ ⋃ (l : ℕ) (_ : l < i), Metric.ball (D.term j l) (P.f (D.term j l))
  term_large : ∀ i, i < D.termCount j → P.scale T j ≤ P.f (D.term j i)
  term_max : ∀ i, i < D.termCount j →
    ∀ z ∈ E \ ⋃ (l : ℕ) (_ : l < i), Metric.ball (D.term j l) (P.f (D.term j l)),
      P.f z ≤ P.f (D.term j i)
  term_done : ∀ z ∈ D.afterTerm P j E, P.f z < P.scale T j
  cand_mem : ∀ i, i < D.candCount j → D.cand j i ∈ D.afterTerm P j E
  cand_separated : ∀ i, i < D.candCount j → ∀ l, l < D.candCount j → i ≠ l →
    T.sourceSeparation * P.scale T j ≤ dist (D.cand j i) (D.cand j l)
  cand_cover : D.afterTerm P j E ⊆
    ⋃ (i : ℕ) (_ : i < D.candCount j),
      Metric.ball (D.cand j i) (T.sourceSeparation * P.scale T j)
  fit_minimal : ∀ i, i < D.candCount j →
    ∫⁻ z in Metric.ball (D.cand j i) (40 * P.scale T j),
        Metric.infEDist z (D.modelSet j i) ^ 2 ∂P.ν ≤
      typeFittingError P.ν k T.toFamilyKind (D.cand j i) (40 * P.scale T j)

/-- Stage invariants and stopping-stage uniqueness of the construction: the
kept sets are Borel, decreasing and inside `S`; the continuing `κ r_j`-balls cover what
the collapsed phase leaves, so every point of an entering set lies in a terminal,
collapsed or parent piece; a terminal center or noncontinuing candidate occurs at one
stage and index only, the two kinds never coincide, and each is removed at its own
stage. -/
structure ConstructionData.StageInvariants {n k : ℕ} {T : NeckType}
    (D : ConstructionData n k T) (P : SourceSetup n) : Prop where
  measurableSet_kept : ∀ j, MeasurableSet (D.kept P j)
  kept_subset : ∀ j, D.kept P j ⊆ P.S
  kept_succ_subset : ∀ j, D.kept P (j + 1) ⊆ D.kept P j
  afterColl_subset : ∀ j, 1 ≤ j → D.afterColl P j (D.entering P j) ⊆
    ⋃ (i : ℕ) (_ : i < D.candCount j ∧ D.IsContinuing P j i),
      Metric.ball (D.cand j i) (T.sourceSeparation * P.scale T j)
  term_unique : ∀ j j' i i', 1 ≤ j → 1 ≤ j' → i < D.termCount j → i' < D.termCount j' →
    D.term j i = D.term j' i' → j = j' ∧ i = i'
  coll_unique : ∀ j j' i i', 1 ≤ j → 1 ≤ j' → i < D.candCount j → i' < D.candCount j' →
    ¬ D.IsContinuing P j i → ¬ D.IsContinuing P j' i' → D.cand j i = D.cand j' i' →
    j = j' ∧ i = i'
  term_ne_coll : ∀ j j' i i', 1 ≤ j → 1 ≤ j' → i < D.termCount j → i' < D.candCount j' →
    ¬ D.IsContinuing P j' i' → D.term j i ≠ D.cand j' i'
  term_not_kept : ∀ j i, 1 ≤ j → i < D.termCount j → D.term j i ∉ D.kept P j
  coll_not_kept : ∀ j i, 1 ≤ j → i < D.candCount j → ¬ D.IsContinuing P j i →
    D.cand j i ∉ D.kept P j

/-- The separation and bound fields of `ConstructionData.RegionFacts`: all
fields except compactness of the centers, the core limits and compactness of the core. -/
structure ConstructionData.SeparationFacts {n k : ℕ} {T : NeckType}
    (D : ConstructionData n k T) (P : SourceSetup n) (hR : 0 < P.R) (Cs : ℝ) : Prop where
  centers_subset : D.centers P ⊆ Metric.closedBall P.q P.R
  radius_nonneg : ∀ c ∈ D.centers P, 0 ≤ D.radius P c
  radius_le : ∀ c ∈ D.centers P, D.radius P c ≤ 4 * P.R
  stop_separation : ∀ c ∈ D.centers P, ∀ c' ∈ D.centers P, 0 < D.radius P c →
    0 < D.radius P c' → c ≠ c' → 1 / 20 * max (D.radius P c) (D.radius P c') ≤ dist c c'
  core_separation : ∀ c ∈ D.centers P, 0 < D.radius P c → ∀ z ∈ D.centers P,
    D.radius P z = 0 → D.radius P c ≤ dist c z
  initialRadius_le : T.rootRadius P.R ≤ Cs * P.R
  initialPoint_mem : D.rootCenter.1 ∈ D.rootPlane.toSet
  initialPoint_near : ‖D.rootCenter.1 - P.q.1‖ ≤ Cs * P.R
  center_mem : ∀ j, ∀ a ∈ (D.family P hR).index j,
    (D.family P hR).center j a ∈ Metric.ball P.q (Cs * P.R)

open Classical in
/-- The charging data of the node errors of a construction, exactly the
hypotheses of the charging bound `ChargeCollapse.nodeErrorMass_iUnion_le` for
the original source, the stage scales `r_j = coherentScale (T.rootRadius R) j`, the tube
tolerance `θ` and the constants `F, A, C_ω, c₁, N₀`: Borel incidence sets in a measurable
reference space `X`, charged nodes `I j` in `S` (none at level `0`: the artificial root is
not charged) with cutoff `f(g) ≤ F r_j`, same-level multiplicity at most `N₀`, the
incident-witness comparison with constant `A`, reference measures `ω N` (one per
truncation) of total mass `≤ C_ω R^k` and lower patch masses `≥ c₁ r_j^k`, attained fits,
and Borel stage-error pieces in `P(g, r_j)` outside the `θ r_j`-tube covering the node
error set. -/
def ConstructionData.NodeChargeData {n k : ℕ} {T : NeckType} (D : ConstructionData n k T)
    (P : SourceSetup n) (Fc A Cω c₁ : ℝ) (N₀ : ℕ) : Prop :=
  ∃ (X : Type) (_ : MeasurableSpace X) (I : ℕ → Finset (Space n)) (E : ℕ → Space n → Set X)
    (ω : ℕ → Measure X) (Pm : ℕ → Space n → Models n k T.toFamilyKind)
    (e : ℕ → Space n → Set (Space n)),
    I 0 = ∅ ∧
    (∀ j, ∀ g ∈ I j, g ∈ P.S) ∧
    (∀ j, ∀ g ∈ I j, P.f g ≤ Fc * coherentScale (T.rootRadius P.R) j) ∧
    (∀ j, ∀ g ∈ I j, MeasurableSet (E j g)) ∧
    (∀ (x : X) (j : ℕ), ((I j).filter fun g => x ∈ E j g).card ≤ N₀) ∧
    (∀ (x : X) (j : ℕ), ∀ g ∈ I j, x ∈ E j g → ∀ j', j ≤ j' →
      ∀ y ∈ I j', x ∈ E j' y → dist g y ≤ A * coherentScale (T.rootRadius P.R) j) ∧
    (∀ N, ω N univ ≤ ENNReal.ofReal (Cω * P.R ^ k)) ∧
    (∀ N, ∀ j ≤ N, ∀ g ∈ I j,
      ENNReal.ofReal (c₁ * coherentScale (T.rootRadius P.R) j ^ k) ≤ ω N (E j g)) ∧
    (∀ j, ∀ g ∈ I j, fit P.ν (Pm j g) g (40 * coherentScale (T.rootRadius P.R) j) ≤
      ENNReal.ofReal ((40 * coherentScale (T.rootRadius P.R) j) ^ (k + 2)) *
        betaSq P.ν k T.toFamilyKind g (40 * coherentScale (T.rootRadius P.R) j)) ∧
    (∀ j, ∀ g ∈ I j, MeasurableSet (e j g)) ∧
    (∀ j, ∀ g ∈ I j, e j g ⊆ Metric.ball g (coherentScale (T.rootRadius P.R) j)) ∧
    (∀ j, ∀ g ∈ I j, ∀ z ∈ e j g,
      ENNReal.ofReal ((P.θ * coherentScale (T.rootRadius P.R) j) ^ 2) <
        modelCost (Pm j g) z) ∧
    D.nodeErrorSet P ⊆ ⋃ j, ⋃ g ∈ I j, e j g

/-- The genuine records of the construction: occurrences of positive levels and
stopping centers; not the artificial root and not the core points. -/
def ConstructionData.IsGenuineRecord {n k : ℕ} {T : NeckType} (D : ConstructionData n k T)
    (P : SourceSetup n) : NeckRecord n ℕ → Prop
  | .inl (j, _) => 1 ≤ j
  | .inr c => c ∈ D.stopping P

/-- The fitted-time comparison: fitted times of continuing candidates at the
same level within `20 r_j`, or at adjacent levels within `20 r_j`, differ by at most
`K r_j²`. -/
def ConstructionData.FittedTimeComparison {n k : ℕ} {T : NeckType}
    (D : ConstructionData n k T) (P : SourceSetup n) (K : ℝ) : Prop :=
  (∀ j, 1 ≤ j → ∀ i ∈ D.contIndex P j, ∀ l ∈ D.contIndex P j,
      dist (D.cand j i) (D.cand j l) ≤ 20 * P.scale T j →
      |D.time j i - D.time j l| ≤ K * P.scale T j ^ 2) ∧
    ∀ j, 1 ≤ j → ∀ i ∈ D.contIndex P (j + 1), ∀ l ∈ D.contIndex P j,
      dist (D.cand (j + 1) i) (D.cand j l) ≤ 20 * P.scale T j →
      |D.time (j + 1) i - D.time j l| ≤ K * P.scale T j ^ 2

/-- Time compatibility of the genuine records: the inequality of
`RecordsTimeCompatible` for every pair of genuine records. -/
def ConstructionData.GenuineTimeCompatible {n k : ℕ} {T : NeckType}
    (D : ConstructionData n k T) (P : SourceSetup n) (hR : 0 < P.R) (γ : ℝ) : Prop :=
  ∀ z w : NeckRecord n ℕ, NeckRecord.IsRecord (D.family P hR) (D.centers P) z →
    NeckRecord.IsRecord (D.family P hR) (D.centers P) w →
    D.IsGenuineRecord P z → D.IsGenuineRecord P w →
    |(NeckRecord.position (D.family P hR) z).2.val -
        (NeckRecord.position (D.family P hR) w).2.val| ≤
      γ * max (‖(NeckRecord.position (D.family P hR) z).1 -
          (NeckRecord.position (D.family P hR) w).1‖ ^ 2)
        (max (NeckRecord.scale (D.family P hR) (D.radius P) z ^ 2)
          (NeckRecord.scale (D.family P hR) (D.radius P) w ^ 2))

/-- The countable child indexing and Borel partition of a contracting step built from the
hole children `H` of the stopping centers: every field of `ContractingStep`
except its three estimates (`errorSet_le`, `childRadius_le`, `child_content_le`),
together with the step identity, the exact collapsed radius, and the origin data used by
the estimates: the error set lies in `e ∪ ⋃_c discard_c`, and every active child
`w : childIndex` comes from one hole child (`childOrigin`, injective) with the parent and
radius of that hole. The origin map is defined on the active index set only, so no
stopping center and no hole child has to exist: the empty neck and the
case where every hole discards all of its source are allowed. -/
structure StepChildren {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n}
    {R c₀ Cd Cs σ δ E κ θ γ : ℝ} {N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ}
    {ν : Measure (Space n)} {S : Set (Space n)} {f : Space n → ℝ}
    (Pa : NeckSourcePartition S f N) (ρ ε : ℝ) (rad : N.stopping → ℝ)
    (H : ∀ c : N.stopping, HoleChildren ν (Pa.assignment c) (rad c)) where
  errorSet : Set (Space n)
  coreSet : Set (Space n)
  childIndex : Set ℕ
  childSource : ℕ → Set (Space n)
  childCenter : ℕ → Space n
  childRadius : ℕ → ℝ
  childParent : ℕ → Space n
  childOrigin : childIndex → Σ c : N.stopping, Fin (H c).count
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
  childParent_mem : ∀ w ∈ childIndex, childParent w ∈ N.stopping
  childSource_subset_hole : ∀ w ∈ childIndex,
    childSource w ⊆ Metric.ball (childParent w) (N.radius (childParent w))
  childSource_subset_ball : ∀ w ∈ childIndex,
    childSource w ⊆ Metric.ball (childCenter w) (childRadius w)
  childRadius_eq : ∀ w ∈ childIndex,
    childRadius w = 3 * ρ * N.radius (childParent w) ∨
      childRadius w = 2 * ε * N.radius (childParent w)
  finite_children : ∀ c : Space n, {w | w ∈ childIndex ∧ childParent w = c}.Finite
  errorSet_subset_discard : errorSet ⊆ Pa.errorSet ∪ ⋃ c : N.stopping, (H c).discard
  childOrigin_injective : Function.Injective childOrigin
  childParent_origin : ∀ w : childIndex, childParent w = ((childOrigin w).1 : Space n)
  childRadius_origin : ∀ w : childIndex, childRadius w = rad (childOrigin w).1
  childRadius_collapsed : ∀ w ∈ childIndex, childParent w ∉ Pa.terminal →
    childRadius w = 3 * ρ * N.radius (childParent w)
  measure_eq : ν = ν.restrict errorSet + ν.restrict coreSet +
    Measure.sum (fun w : childIndex => ν.restrict (childSource w))

/-- The subtree set `D_v` of a vertex: the cores of all vertices `u`
having `v` as a prefix, and the infinite-path residual inside the source `S_v`. Its
closure is `K_v`; the carrier is the closure of `D_[]`. -/
def StepTree.subtreeSet {n k : ℕ} {F : FamilyKind} {S : Set (Space n)} {q : Space n}
    {R B Eerr ρ ε : ℝ} {ν : Measure (Space n)} (Tr : StepTree ν k F S q R B Eerr ρ ε)
    (v : List ℕ) : Set (Space n) :=
  (⋃ u ∈ Tr.vertices, ⋃ (_ : v <+: u), (Tr.vneck u).neck.core) ∪
    (treeResidual Tr.vertices Tr.source ∩ Tr.source v)

/-- The comparison square bound over all
levels follows from the bounds for every finite truncation: the series is the supremum of
its partial sums. -/
theorem CoherentFamily.squareBound_of_upTo {n m : ℕ} {ι : Type*} {W : Type*}
    [PseudoMetricSpace W] (pos : Space n → W) (F : CoherentFamily n m ι) (E : ℝ)
    (h : ∀ N : ℕ, F.SquareBoundUpTo pos E N) : F.SquareBound pos E := by
  intro w
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => le_trans ?_ (h N w)
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.le_succ N))

/-- Pairwise witness bound for horizontal spatial incidence. Two occurrences `(j, a)` and `(J, b)`, `j ≤ J`, of a family whose records are
time compatible with constant `γ`, both spatially incident to one spatial reference point
`x` (`|x - x_{j,a}| < A₀ r_j`, `|x - x_{J,b}| < A₀ r_J`), satisfy
`d_P(z_{j,a}, z_{J,b}) ≤ max{2A₀, √γ max(2A₀, 1)} r_j` (by
`ChargeCollapse.horizontal_witness_dist` applied with the record inequality of the two occurrences). -/
theorem CoherentFamily.horizontal_occurrence_witness {n m : ℕ} {ι : Type*}
    (F : CoherentFamily n m ι) {C : Set (Space n)} {d : Space n → ℝ} {γ A₀ : ℝ}
    (hγ : 0 ≤ γ) (hA₀ : 0 ≤ A₀) (htime : RecordsTimeCompatible F C d γ) {j J : ℕ}
    (hjJ : j ≤ J) {a b : ι} (ha : a ∈ F.index j) (hb : b ∈ F.index J) {x : Spatial n}
    (hxa : dist x (F.center j a).1 < A₀ * F.scale j)
    (hxb : dist x (F.center J b).1 < A₀ * F.scale J) :
    dist (F.center j a) (F.center J b) ≤
      max (2 * A₀) (Real.sqrt γ * max (2 * A₀) 1) * F.scale j :=
  ChargeCollapse.horizontal_witness_dist hγ hA₀
    (Charging.coherentScale_pos F.initialRadius_pos J)
    (ChargeCollapse.coherentScale_anti F.initialRadius_pos hjJ) hxa hxb
    (htime (Sum.inl (j, a)) (Sum.inl (J, b)) ha hb)

end ParabolicRectifiability
