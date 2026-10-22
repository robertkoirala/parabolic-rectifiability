import ParabolicRectifiability.Measure.Neck.Definitions
import ParabolicRectifiability.Geometry.Neck.Collapse
import ParabolicRectifiability.Geometry.Neck.Conclusions

/-!
# The recursive source construction and the private decomposition tree

Definitions, with a few elementary lemmas, describing the recursive construction of a
neck from a Radon source, one contracting step, and the decomposition tree: finite
ordered assignment sets, stored parents and covariance tests for the original source;
and tree data retaining at each vertex its neck, contracting step, parent-hole
assignment, exact child-radius relation and a uniform parametrization constant.

* `SourceSetup`: the data `(ν, S, f, q, R, θ, a)` of the neck construction, with
  `SourceSetup.IsAdmissible` (the standing hypotheses) and `SourceSetup.TailBound`.
* `ConstructionData`: the raw choices of the construction:
  the global minimizing model and the artificial root; at each stage
  `j ≥ 1` the ordered terminal centers, the ordered net candidates and their fitted
  models. Everything else is *defined* from these choices: the initial tube, the
  original-source covariance test `IsContinuing`, the ordered first-ball assignments,
  the kept sets `S_j`, the core limit, the stopping centers and radii, the stored
  parents, the coherent family, and the source partition.
* `ConstructionData.IsSourceConstruction`: the selection rules of the construction
  (global minimality, decreasing terminal selection, maximal separated nets,
  attained fits).
* `ConstructionData.RegionFacts`, `NeckFacts`, `PartitionFacts`: the neck-region and
  partition facts of the construction, and their packaging
  `toNeckRegion`, `toSourcePartition`.
* `HoleFacts`, `HoleChildren.discardAll`: the per-hole data of a contracting step.
* `VertexNeck`, `StepTree`: the tree data of the countable decomposition, and
  `StepTree.carrier`.
* Monotonicity of the geometric conclusion shapes in their constants.

All assignment sets are Borel restrictions of the original source; the covariance
test always uses the original source `ν` on `P(g, 5 r_j)`, never a surviving part.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal

/-! ## Monotonicity of the geometric conclusion shapes -/

namespace NeckRegion

variable {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n}
  {R c₀ Cd Cs σ δ E κ θ γ : ℝ} {N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ}

theorem HasVerticalParametrization.mono {Λ Λ' : ℝ} (h : N.HasVerticalParametrization Λ)
    (hΛ : 0 < Λ) (hΛΛ' : Λ ≤ Λ') : N.HasVerticalParametrization Λ' := by
  obtain ⟨G, A, hG, hA, himg⟩ := h
  refine ⟨G, A, fun p p' => ⟨?_, ?_⟩, hA, himg⟩
  · exact le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hΛ hΛΛ') dist_nonneg) (hG p p').1
  · exact le_trans (hG p p').2 (mul_le_mul_of_nonneg_right hΛΛ' dist_nonneg)

theorem HasHorizontalParametrization.mono {Λ Λ' : ℝ} (h : N.HasHorizontalParametrization Λ)
    (hΛ : 0 < Λ) (hΛΛ' : Λ ≤ Λ') : N.HasHorizontalParametrization Λ' := by
  obtain ⟨G, hG, A, τ, hA, hφ, himg⟩ := h
  refine ⟨G, fun u v => ⟨?_, ?_⟩, A, τ, hA, fun u v => ⟨?_, ?_⟩, himg⟩
  · exact le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hΛ hΛΛ') (norm_nonneg _)) (hG u v).1
  · exact le_trans (hG u v).2 (mul_le_mul_of_nonneg_right hΛΛ' (norm_nonneg _))
  · exact le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hΛ hΛΛ') dist_nonneg) (hφ u v).1
  · exact le_trans (hφ u v).2 (mul_le_mul_of_nonneg_right hΛΛ' dist_nonneg)

theorem HasLocalContentBound.mono {C C' : ℝ} (h : N.HasLocalContentBound C) (hC : C ≤ C') :
    N.HasLocalContentBound C' := by
  intro z s hs
  exact le_trans (h z s hs)
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hs.le k)))

theorem HasTotalContentBound.mono {C C' : ℝ} (h : N.HasTotalContentBound C) (hC : C ≤ C')
    (hR : 0 ≤ R) : N.HasTotalContentBound C' :=
  le_trans h (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hR k)))

theorem HasCoreDensity.mono {C C' : ℝ} (h : N.HasCoreDensity C) (hC : C ≤ C') :
    N.HasCoreDensity C' := by
  obtain ⟨hup, hlow⟩ := h
  refine ⟨fun z s hs => le_trans (hup z s hs) ?_, hlow⟩
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hs.le k))

end NeckRegion

/-! ## Neck types: root radius and separation -/

namespace NeckType

/-- The initial radius `r_0` of the source construction: `8R` (horizontal)
and `4R` (vertical). -/
def rootRadius : NeckType → ℝ → ℝ
  | horizontal, R => 8 * R
  | vertical, R => 4 * R

theorem rootRadius_pos (T : NeckType) {R : ℝ} (hR : 0 < R) : 0 < T.rootRadius R := by
  cases T
  · show (0 : ℝ) < 8 * R
    linarith
  · show (0 : ℝ) < 4 * R
    linarith

theorem sourceSeparation_pos (T : NeckType) : 0 < T.sourceSeparation := by
  cases T
  · show (0 : ℝ) < 1 / 4
    norm_num
  · show (0 : ℝ) < 1
    norm_num

theorem sourceSeparation_le_one (T : NeckType) : T.sourceSeparation ≤ 1 := by
  cases T
  · show (1 / 4 : ℝ) ≤ 1
    norm_num
  · show (1 : ℝ) ≤ 1
    norm_num

/-- The collapse model set `NeckType.collapseModelSet` and the lower model set are the
same set. -/
theorem collapseModelSet_eq_lowerModelSet {n m : ℕ} (T : NeckType)
    (L : AffineSpatialPlane n m) (τ : ℝ) : T.collapseModelSet L τ = T.lowerModelSet L τ := by
  cases T <;> rfl

end NeckType

/-! ## First-ball assignments -/

/-- First-ball assignment of an ordered family of balls: the `i`-th
piece is the part of `A` in the `i`-th ball and in no earlier ball of the subfamily
selected by `P`. -/
def firstBallPiece {X : Type*} [PseudoMetricSpace X] (A : Set X) (P : ℕ → Prop) (c : ℕ → X)
    (r : ℕ → ℝ) (i : ℕ) : Set X :=
  A ∩ (Metric.ball (c i) (r i) \ ⋃ (l : ℕ) (_ : l < i ∧ P l), Metric.ball (c l) (r l))

/-! ## The source setup of the neck construction -/

/-- The data of the neck construction: the original source `ν` (finite),
the source set `S`, the cutoff `f`, the container `P(q,R)`, the tube tolerance `θ` and
the noncollapse level `a`. -/
structure SourceSetup (n : ℕ) where
  ν : Measure (Space n)
  finite : IsFiniteMeasure ν
  S : Set (Space n)
  f : Space n → ℝ
  q : Space n
  R : ℝ
  θ : ℝ
  a : ℝ

namespace SourceSetup

variable {n : ℕ}

/-- The standing hypotheses of the neck construction other than the tail bound. -/
structure IsAdmissible (P : SourceSetup n) : Prop where
  R_pos : 0 < P.R
  measurableSet_S : MeasurableSet P.S
  S_subset : P.S ⊆ Metric.ball P.q P.R
  carried : P.ν P.Sᶜ = 0
  cutoff : IsSourceCutoff P.S P.R P.f
  θ_pos : 0 < P.θ
  a_pos : 0 < P.a

/-- The fixed-type tail bound `∫_{f(z)}^∞ b_ν(z,r) dr/r ≤ B` on `S`. -/
def TailBound (P : SourceSetup n) (k : ℕ) (T : NeckType) (B : ℝ) : Prop :=
  ∀ z ∈ P.S, tailEnergy P.ν k T.toFamilyKind (P.f z) z ≤ ENNReal.ofReal B

/-- The stage scales `r_j = 10^{-j} r_0`. -/
def scale (P : SourceSetup n) (T : NeckType) (j : ℕ) : ℝ := coherentScale (T.rootRadius P.R) j

theorem scale_pos (P : SourceSetup n) (T : NeckType) (hR : 0 < P.R) (j : ℕ) :
    0 < P.scale T j :=
  div_pos (T.rootRadius_pos hR) (pow_pos (by norm_num) j)

end SourceSetup

/-! ## The raw choices of the construction -/

/-- The raw choices of the source construction.

* `rootPlane`, `rootTime`: the spatial plane `L_*` and (horizontal case) time `τ_*` of
  the global minimizing model `Π_*`; `rootCenter` is the artificial root;
* at stage `j ≥ 1`: the terminal centers `term j 0, …, term j (termCount j - 1)` in
  their selection order; the net candidates `cand j 0, …, cand j (candCount j - 1)` in
  the fixed processing order; the fitted model `plane j i × {time j i}` (horizontal) or
  `plane j i × ℝ` (vertical) of candidate `i` on `P(cand j i, 40 r_j)`.

Values at stage `0` and at indices beyond the counts are never used. -/
structure ConstructionData (n k : ℕ) (T : NeckType) where
  rootPlane : AffineSpatialPlane n (T.rank k)
  rootTime : ℝ
  rootCenter : Space n
  termCount : ℕ → ℕ
  term : ℕ → ℕ → Space n
  candCount : ℕ → ℕ
  cand : ℕ → ℕ → Space n
  plane : ℕ → ℕ → AffineSpatialPlane n (T.rank k)
  time : ℕ → ℕ → ℝ

namespace ConstructionData

variable {n k : ℕ} {T : NeckType}

/-- The global minimizing model set `Π_*`. -/
def rootModel (D : ConstructionData n k T) : Set (Space n) :=
  T.lowerModelSet D.rootPlane D.rootTime

/-- The fitted model set `Π_g` of candidate `i` at stage `j`. -/
def modelSet (D : ConstructionData n k T) (j i : ℕ) : Set (Space n) :=
  T.lowerModelSet (D.plane j i) (D.time j i)

/-- The initial tube `S_0 = S ∩ {d_P(z, Π_*) ≤ θ R}`. -/
def tubeSet (D : ConstructionData n k T) (P : SourceSetup n) : Set (Space n) :=
  P.S ∩ {z | Metric.infEDist z D.rootModel ≤ ENNReal.ofReal (P.θ * P.R)}

/-- The covariance test of candidate `i` at stage `j`, always for the
original source: at positive spatial rank `d`, `λ_d(Q_g) ≥ a (5 r_j)^{k+2}` for the
covariance of `ν ⌞ P(g, 5 r_j)`; at vertical rank zero, `ν(P(g, 5 r_j)) ≥ a (5 r_j)^2`. -/
def IsContinuing (D : ConstructionData n k T) (P : SourceSetup n) (j i : ℕ) : Prop :=
  (0 < T.rank k ∧ ∃ h : 0 < 5 * P.scale T j,
      P.a * (5 * P.scale T j) ^ (k + 2) ≤
        (@SpatialSource.ofBall n P.ν P.finite (D.cand j i) (5 * P.scale T j) h).rankEigenvalue
          (T.rank k)) ∨
    (T.rank k = 0 ∧
      ENNReal.ofReal (P.a * (5 * P.scale T j) ^ 2) ≤
        P.ν (Metric.ball (D.cand j i) (5 * P.scale T j)))

/-- Terminal assignment of the `i`-th terminal center at stage `j` from the entering
set `E` (first-ball order, radius `f(c)`). -/
def termPiece (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) (E : Set (Space n))
    (i : ℕ) : Set (Space n) :=
  firstBallPiece E (fun _ => True) (D.term j) (fun l => P.f (D.term j l)) i

/-- The part of `E` left after the terminal phase of stage `j`. -/
def afterTerm (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) (E : Set (Space n)) :
    Set (Space n) :=
  E \ ⋃ (i : ℕ) (_ : i < D.termCount j), Metric.ball (D.term j i) (P.f (D.term j i))

/-- Collapsed assignment of a noncontinuing candidate (first-ball order among the
noncontinuing candidates, radius `5 r_j`). -/
def collPiece (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) (E : Set (Space n))
    (i : ℕ) : Set (Space n) :=
  firstBallPiece (D.afterTerm P j E) (fun l => ¬ D.IsContinuing P j l) (D.cand j)
    (fun _ => 5 * P.scale T j) i

/-- The part left after the collapsed assignments of stage `j`. -/
def afterColl (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) (E : Set (Space n)) :
    Set (Space n) :=
  D.afterTerm P j E \ ⋃ (i : ℕ) (_ : i < D.candCount j ∧ ¬ D.IsContinuing P j i),
    Metric.ball (D.cand j i) (5 * P.scale T j)

/-- Parent assignment `U_i` of a continuing candidate (first-ball order among the
continuing candidates, radius `κ r_j`). -/
def parentPiece (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) (E : Set (Space n))
    (i : ℕ) : Set (Space n) :=
  firstBallPiece (D.afterColl P j E) (fun l => D.IsContinuing P j l) (D.cand j)
    (fun _ => T.sourceSeparation * P.scale T j) i

/-- The kept part of `U_i`: within `θ r_j` of the fitted model `Π_g`. -/
def keptPiece (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) (E : Set (Space n))
    (i : ℕ) : Set (Space n) :=
  D.parentPiece P j E i ∩
    {z | Metric.infEDist z (D.modelSet j i) ≤ ENNReal.ofReal (P.θ * P.scale T j)}

/-- The stage error of `U_i`: outside the `θ r_j`-tube of its fitted model. -/
def errorPiece (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) (E : Set (Space n))
    (i : ℕ) : Set (Space n) :=
  D.parentPiece P j E i \ D.keptPiece P j E i

/-- The kept set produced by stage `j` from the entering set `E`. -/
def stageKept (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) (E : Set (Space n)) :
    Set (Space n) :=
  ⋃ (i : ℕ) (_ : i < D.candCount j ∧ D.IsContinuing P j i), D.keptPiece P j E i

/-- The kept sets `S_0 = tube`, `S_j = stageKept j S_{j-1}`. -/
def kept (D : ConstructionData n k T) (P : SourceSetup n) : ℕ → Set (Space n)
  | 0 => D.tubeSet P
  | j + 1 => D.stageKept P (j + 1) (kept D P j)

/-- The set entering stage `j ≥ 1`, namely `S_{j-1}`. -/
def entering (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) : Set (Space n) :=
  D.kept P (j - 1)

open Classical in
/-- The continuing candidates of stage `j`. -/
def contIndex (D : ConstructionData n k T) (P : SourceSetup n) (j : ℕ) : Finset ℕ :=
  (Finset.range (D.candCount j)).filter (fun i => D.IsContinuing P j i)

open Classical in
/-- The stored preceding parent of candidate `a` of stage `j + 1`: the continuing
candidate `i` of stage `j` whose kept piece contains it. -/
def parentIndex (D : ConstructionData n k T) (P : SourceSetup n) (j a : ℕ) : ℕ :=
  if h : ∃ i, i < D.candCount j ∧ D.IsContinuing P j i ∧
      D.cand (j + 1) a ∈ D.keptPiece P j (D.entering P j) i then Nat.find h else 0

/-- The coherent family of the construction: level `0` is the
singleton artificial root with plane `L_*`; level `j ≥ 1` consists of the continuing
candidates of stage `j` with their fitted spatial planes; parents are the stored
preceding parents (the root for level `1`). -/
def family (D : ConstructionData n k T) (P : SourceSetup n) (hR : 0 < P.R) :
    CoherentFamily n (T.rank k) ℕ where
  initialRadius := T.rootRadius P.R
  initialRadius_pos := T.rootRadius_pos hR
  index := fun j => if j = 0 then {0} else D.contIndex P j
  center := fun j i => if j = 0 then D.rootCenter else D.cand j i
  plane := fun j i => if j = 0 then D.rootPlane else D.plane j i
  parent := fun j a => if j ≤ 1 then 0 else D.parentIndex P (j - 1) a
  initialPlane := D.rootPlane

/-- `c` is a terminal center of some stage. -/
def IsTermCenter (D : ConstructionData n k T) (c : Space n) : Prop :=
  ∃ j, 1 ≤ j ∧ ∃ i, i < D.termCount j ∧ D.term j i = c

/-- `c` is a collapsed center of some stage (a noncontinuing candidate with a nonempty
assignment). -/
def IsCollCenter (D : ConstructionData n k T) (P : SourceSetup n) (c : Space n) : Prop :=
  ∃ j, 1 ≤ j ∧ ∃ i, i < D.candCount j ∧ ¬ D.IsContinuing P j i ∧ D.cand j i = c ∧
    (D.collPiece P j (D.entering P j) i).Nonempty

/-- The core `C₀ = ⋂_j closure(S_j)`. -/
def coreLimit (D : ConstructionData n k T) (P : SourceSetup n) : Set (Space n) :=
  ⋂ j : ℕ, closure (D.kept P j)

open Classical in
/-- The stage of a collapsed center. -/
def collStage (D : ConstructionData n k T) (P : SourceSetup n) (c : Space n) : ℕ :=
  if h : D.IsCollCenter P c then Classical.choose h else 0

open Classical in
/-- The radius function: `f(c)` at a terminal center, `5 r_j` at a collapsed center of
stage `j`, and `0` elsewhere (in particular on the core). -/
def radius (D : ConstructionData n k T) (P : SourceSetup n) (c : Space n) : ℝ :=
  if D.IsTermCenter c then P.f c
  else if D.IsCollCenter P c then 5 * P.scale T (D.collStage P c) else 0

/-- The actual center set `𝒞 = C₀ ∪ {stopping centers}`. -/
def centers (D : ConstructionData n k T) (P : SourceSetup n) : Set (Space n) :=
  D.coreLimit P ∪ {c | D.IsTermCenter c ∨ D.IsCollCenter P c}

/-- The core `{c ∈ 𝒞 : d_c = 0}`, as in `NeckRegion.core`. -/
def core (D : ConstructionData n k T) (P : SourceSetup n) : Set (Space n) :=
  {c | c ∈ D.centers P ∧ D.radius P c = 0}

/-- The stopping centers `{c ∈ 𝒞 : d_c > 0}`, as in `NeckRegion.stopping`. -/
def stopping (D : ConstructionData n k T) (P : SourceSetup n) : Set (Space n) :=
  {c | c ∈ D.centers P ∧ 0 < D.radius P c}

/-- The terminal centers. -/
def terminal (D : ConstructionData n k T) : Set (Space n) :=
  {c | D.IsTermCenter c}

open Classical in
/-- The stage of a stopping center. -/
def stopStage (D : ConstructionData n k T) (P : SourceSetup n) (c : Space n) : ℕ :=
  if h : D.IsTermCenter c then Classical.choose h else D.collStage P c

open Classical in
/-- The stopping parent: for a center of stage `j ≥ 2`, its preceding
parent, i.e. the continuing candidate of stage `j - 1` whose kept piece contains it;
for a center of stage `1`, the initial plane (`none`). -/
def stoppingParent (D : ConstructionData n k T) (P : SourceSetup n) (c : Space n) :
    Option (ℕ × ℕ) :=
  if h : 2 ≤ D.stopStage P c ∧ ∃ i, i < D.candCount (D.stopStage P c - 1) ∧
      D.IsContinuing P (D.stopStage P c - 1) i ∧
      c ∈ D.keptPiece P (D.stopStage P c - 1) (D.entering P (D.stopStage P c - 1)) i
  then some (D.stopStage P c - 1, Nat.find h.2) else none

/-- The union of the stage errors of all continuing candidates. -/
def nodeErrorSet (D : ConstructionData n k T) (P : SourceSetup n) : Set (Space n) :=
  ⋃ (j : ℕ) (_ : 1 ≤ j) (i : ℕ) (_ : i < D.candCount j ∧ D.IsContinuing P j i),
    D.errorPiece P j (D.entering P j) i

/-- The discarded source `e`: the initial-tube error and the stage errors. -/
def errorSet (D : ConstructionData n k T) (P : SourceSetup n) : Set (Space n) :=
  (P.S \ D.tubeSet P) ∪ D.nodeErrorSet P

/-- The core assignment `S_∞ = ⋂_j S_j`. -/
def coreSet (D : ConstructionData n k T) (P : SourceSetup n) : Set (Space n) :=
  ⋂ j : ℕ, D.kept P j

/-- The assignment of a stopping center: its terminal or collapsed pieces. -/
def assignment (D : ConstructionData n k T) (P : SourceSetup n) (c : Space n) :
    Set (Space n) :=
  (⋃ (j : ℕ) (_ : 1 ≤ j) (i : ℕ) (_ : i < D.termCount j ∧ D.term j i = c),
      D.termPiece P j (D.entering P j) i) ∪
    ⋃ (j : ℕ) (_ : 1 ≤ j) (i : ℕ)
      (_ : i < D.candCount j ∧ ¬ D.IsContinuing P j i ∧ D.cand j i = c),
      D.collPiece P j (D.entering P j) i

/-- The selection rules of the source construction:
* `Π_*` minimizes the global error among all models of type `T`; the artificial root
  lies on `L_*` (at time `τ_*` in the horizontal case) and within `R` of `q`;
* terminal centers are selected from the entering set in decreasing order of the
  cutoff, each outside the earlier terminal balls, with `f ≥ r_j`; afterwards `f < r_j`;
* the candidates form a maximal `κ r_j`-separated subset of what remains (`κ` the
  source separation);
* each fitted model attains the original-source fitting infimum on `P(g, 40 r_j)`. -/
structure IsSourceConstruction (D : ConstructionData n k T) (P : SourceSetup n) : Prop where
  root_minimal : ∀ L : Models n k T.toFamilyKind,
    ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν ≤ ∫⁻ z, modelCost L z ∂P.ν
  root_mem : D.rootCenter.1 ∈ D.rootPlane.toSet
  root_time : T = .horizontal → D.rootCenter.2.val = D.rootTime
  root_dist : dist D.rootCenter P.q ≤ P.R
  term_mem : ∀ j, 1 ≤ j → ∀ i, i < D.termCount j →
    D.term j i ∈ D.entering P j \
      ⋃ (l : ℕ) (_ : l < i), Metric.ball (D.term j l) (P.f (D.term j l))
  term_large : ∀ j, 1 ≤ j → ∀ i, i < D.termCount j → P.scale T j ≤ P.f (D.term j i)
  term_max : ∀ j, 1 ≤ j → ∀ i, i < D.termCount j →
    ∀ z ∈ D.entering P j \ ⋃ (l : ℕ) (_ : l < i), Metric.ball (D.term j l) (P.f (D.term j l)),
      P.f z ≤ P.f (D.term j i)
  term_done : ∀ j, 1 ≤ j → ∀ z ∈ D.afterTerm P j (D.entering P j), P.f z < P.scale T j
  cand_mem : ∀ j, 1 ≤ j → ∀ i, i < D.candCount j →
    D.cand j i ∈ D.afterTerm P j (D.entering P j)
  cand_separated : ∀ j, 1 ≤ j → ∀ i, i < D.candCount j → ∀ l, l < D.candCount j → i ≠ l →
    T.sourceSeparation * P.scale T j ≤ dist (D.cand j i) (D.cand j l)
  cand_cover : ∀ j, 1 ≤ j → D.afterTerm P j (D.entering P j) ⊆
    ⋃ (i : ℕ) (_ : i < D.candCount j),
      Metric.ball (D.cand j i) (T.sourceSeparation * P.scale T j)
  fit_minimal : ∀ j, 1 ≤ j → ∀ i, i < D.candCount j →
    ∫⁻ z in Metric.ball (D.cand j i) (40 * P.scale T j),
        Metric.infEDist z (D.modelSet j i) ^ 2 ∂P.ν ≤
      typeFittingError P.ν k T.toFamilyKind (D.cand j i) (40 * P.scale T j)

/-- The neck-region facts of the constructed data that do not involve the energies:
compact center set inside `closure P(q,R)`, radii in `[0, 4R]`, stopping separation
`1/20`, core separation, buffers `C_*`, core limits, compact core. -/
structure RegionFacts (D : ConstructionData n k T) (P : SourceSetup n) (hR : 0 < P.R)
    (Cs : ℝ) : Prop where
  isCompact_centers : IsCompact (D.centers P)
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
  core_limit : ∀ z ∈ D.centers P, D.radius P z = 0 → (D.family P hR).IsLevelLimit z
  isCompact_core : IsCompact (D.core P)

/-- All propositional fields of a `NeckRegion` for the constructed data, with stopping
separation `1/20`, radius bound `4R`, net separation `T.sourceSeparation`, and
parameters `δ, E, κ, θ, γ`. -/
structure NeckFacts (D : ConstructionData n k T) (P : SourceSetup n) (hR : 0 < P.R)
    (Cs δ E κ γ : ℝ) : Prop where
  available : T.Available n k
  parameters : NeckParameters T P.R (1 / 20) 4 Cs T.sourceSeparation δ E κ P.θ γ
  region : D.RegionFacts P hR Cs
  coherent : ∀ N : ℕ, (D.family P hR).IsCoherentUpTo T.sourceSeparation δ N
  centerHeight : (D.family P hR).HasCenterHeight κ
  squareBound : T.SquareBound (D.family P hR) E
  stoppingParent_spec : ∀ c ∈ D.centers P, 0 < D.radius P c →
    (D.family P hR).IsStoppingParent P.θ c (D.radius P c) (D.stoppingParent P c)
  timeCompatible : T = .horizontal →
    RecordsTimeCompatible (D.family P hR) (D.centers P) (D.radius P) γ

/-- The actual neck region of the construction (a packaging of `NeckFacts`). -/
def toNeckRegion (D : ConstructionData n k T) (P : SourceSetup n) (hR : 0 < P.R)
    {Cs δ E κ γ : ℝ} (h : D.NeckFacts P hR Cs δ E κ γ) :
    NeckRegion n k T ℕ P.q P.R (1 / 20) 4 Cs T.sourceSeparation δ E κ P.θ γ where
  available := h.available
  parameters := h.parameters
  centers := D.centers P
  isCompact_centers := h.region.isCompact_centers
  centers_subset := h.region.centers_subset
  radius := D.radius P
  radius_nonneg := h.region.radius_nonneg
  radius_le := h.region.radius_le
  stop_separation := h.region.stop_separation
  core_separation := h.region.core_separation
  family := D.family P hR
  initialRadius_le := h.region.initialRadius_le
  initialPoint := D.rootCenter.1
  initialPoint_mem := h.region.initialPoint_mem
  initialPoint_near := h.region.initialPoint_near
  center_mem := h.region.center_mem
  coherent := h.coherent
  centerHeight := h.centerHeight
  squareBound := h.squareBound
  core_limit := h.region.core_limit
  stoppingParent := D.stoppingParent P
  stoppingParent_spec := h.stoppingParent_spec
  timeCompatible := h.timeCompatible

/-- The exact source partition facts of the construction, stated for the constructed
sets. -/
structure PartitionFacts (D : ConstructionData n k T) (P : SourceSetup n) : Prop where
  measurableSet_errorSet : MeasurableSet (D.errorSet P)
  measurableSet_coreSet : MeasurableSet (D.coreSet P)
  measurableSet_assignment : ∀ c ∈ D.stopping P, MeasurableSet (D.assignment P c)
  errorSet_subset : D.errorSet P ⊆ P.S
  coreSet_subset : D.coreSet P ⊆ P.S
  assignment_subset : ∀ c ∈ D.stopping P, D.assignment P c ⊆ P.S
  cover : P.S ⊆ D.errorSet P ∪ D.coreSet P ∪ ⋃ c ∈ D.stopping P, D.assignment P c
  disjoint_errorSet_coreSet : Disjoint (D.errorSet P) (D.coreSet P)
  disjoint_errorSet_assignment : ∀ c ∈ D.stopping P, Disjoint (D.errorSet P) (D.assignment P c)
  disjoint_coreSet_assignment : ∀ c ∈ D.stopping P, Disjoint (D.coreSet P) (D.assignment P c)
  disjoint_assignment : ∀ c ∈ D.stopping P, ∀ c' ∈ D.stopping P, c ≠ c' →
    Disjoint (D.assignment P c) (D.assignment P c')
  cutoff_coreSet : ∀ z ∈ D.coreSet P, P.f z = 0
  coreSet_subset_core : D.coreSet P ⊆ D.core P
  assignment_subset_ball : ∀ c ∈ D.stopping P, D.assignment P c ⊆ Metric.ball c (D.radius P c)
  terminal_subset : D.terminal ⊆ D.stopping P
  terminal_radius : ∀ c ∈ D.terminal, c ∈ P.S ∧ D.radius P c = P.f c
  terminal_cutoff : ∀ c ∈ D.terminal, ∀ z ∈ D.assignment P c, P.f z ≤ D.radius P c
  collapsed_radius : ∀ c ∈ D.stopping P, c ∉ D.terminal → ∃ j : ℕ, 1 ≤ j ∧
    D.radius P c = 5 * P.scale T j ∧ ∀ z ∈ D.assignment P c, P.f z < P.scale T j

/-- The source partition of the constructed neck (a packaging of `PartitionFacts`). -/
def toSourcePartition (D : ConstructionData n k T) (P : SourceSetup n) (hR : 0 < P.R)
    {Cs δ E κ γ : ℝ} (h : D.NeckFacts P hR Cs δ E κ γ) (hp : D.PartitionFacts P) :
    NeckSourcePartition P.S P.f (D.toNeckRegion P hR h) where
  errorSet := D.errorSet P
  coreSet := D.coreSet P
  assignment := D.assignment P
  terminal := D.terminal
  measurableSet_errorSet := hp.measurableSet_errorSet
  measurableSet_coreSet := hp.measurableSet_coreSet
  measurableSet_assignment := hp.measurableSet_assignment
  errorSet_subset := hp.errorSet_subset
  coreSet_subset := hp.coreSet_subset
  assignment_subset := hp.assignment_subset
  cover := hp.cover
  disjoint_errorSet_coreSet := hp.disjoint_errorSet_coreSet
  disjoint_errorSet_assignment := hp.disjoint_errorSet_assignment
  disjoint_coreSet_assignment := hp.disjoint_coreSet_assignment
  disjoint_assignment := hp.disjoint_assignment
  cutoff_coreSet := hp.cutoff_coreSet
  coreSet_subset_core := hp.coreSet_subset_core
  assignment_subset_ball := hp.assignment_subset_ball
  terminal_subset := hp.terminal_subset
  terminal_radius := hp.terminal_radius
  terminal_cutoff := hp.terminal_cutoff
  collapsed_radius := hp.collapsed_radius

end ConstructionData

/-! ## Children of one stopping hole -/

/-- The rank-zero discard: the whole assignment is discarded and no child is
created. -/
def HoleChildren.discardAll {n : ℕ} (ν : Measure (Space n)) (A : Set (Space n))
    (hA : MeasurableSet A) (r : ℝ) : HoleChildren ν A r where
  count := 0
  discard := A
  center := fun i => i.elim0
  childSet := fun i => i.elim0
  measurableSet_discard := hA
  measurableSet_childSet := fun i => i.elim0
  discard_subset := subset_rfl
  childSet_subset := fun i => i.elim0
  center_mem := fun i => i.elim0
  childSet_subset_ball := fun i => i.elim0
  cover := subset_union_left
  disjoint_discard := fun i => i.elim0
  disjoint_childSet := fun i => i.elim0

/-- The per-hole facts used by the contracting step for the stopping
center `c` with radius `d = N.radius c`, hole children `Hc` of radius `r`:
* terminal center: `r = 2 ε d`, `d ≤ R`, `2 ≤ k`, discard at most `2 (C₂ B) d^k / ε²`,
  child count `m` with `m ε^{k-2} ≤ C_ter` (from the two-tubes lemma);
* collapsed center: `r = 3 ρ d`, and either positive rank with discard at most
  `4 (C₁ (a + B')) d^k / ρ²` and `m ρ^{k-1} ≤ C_col` (from `CollapsedAssignmentBound`), or
  vertical rank zero with no child and discarded mass `< a d²`. -/
def HoleFacts {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
    {N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ} {ν : Measure (Space n)}
    {S : Set (Space n)} {f : Space n → ℝ} (Pa : NeckSourcePartition S f N)
    (B B' a C₁ C₂ Ccol Cter ρ ε : ℝ) (c : N.stopping) (r : ℝ)
    (Hc : HoleChildren ν (Pa.assignment c) r) : Prop :=
  ((c : Space n) ∈ Pa.terminal → r = 2 * ε * N.radius c ∧ N.radius c ≤ R ∧ 2 ≤ k ∧
      ν Hc.discard ≤ ENNReal.ofReal (2 * (C₂ * B) * N.radius c ^ k / ε ^ 2) ∧
      (Hc.count : ℝ) * ε ^ (k - 2) ≤ Cter) ∧
    ((c : Space n) ∉ Pa.terminal → r = 3 * ρ * N.radius c ∧
      ((0 < T.rank k ∧
          ν Hc.discard ≤ ENNReal.ofReal (4 * (C₁ * (a + B')) * N.radius c ^ k / ρ ^ 2) ∧
          (Hc.count : ℝ) * ρ ^ (k - 1) ≤ Ccol) ∨
        (T.rank k = 0 ∧ Hc.count = 0 ∧ ν Hc.discard < ENNReal.ofReal (a * N.radius c ^ 2))))

/-! ## The tree of the countable decomposition -/

/-- A neck region over the container `P(q,R)` with stopping separation `1/20`, together
with its type and parameters (the neck retained at one vertex). -/
structure VertexNeck (n k : ℕ) (q : Space n) (R : ℝ) where
  type : NeckType
  ι : Type
  Cd : ℝ
  Cs : ℝ
  σ : ℝ
  δ : ℝ
  E : ℝ
  κ : ℝ
  θ : ℝ
  γ : ℝ
  neck : NeckRegion n k type ι q R (1 / 20) Cd Cs σ δ E κ θ γ

/-- The tree data of the countable neck decomposition: the countable
rooted tree of vertices `v ∈ List ℕ`, the source `S_v`, container `P(q_v, R_v)`, the
retained neck and contracting step at every vertex (for the vertex source `ν|S_v`), the
correspondence between tree children and step children (same source, center and exact
radius `3ρ d_c` or `2ε d_c` of the parent stopping center), the inherited original
bound `B`, and the local identities in tree indexing. Packing, compactness and the
global identities are *not* fields: they are proved from these data. -/
structure StepTree {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (F : FamilyKind)
    (S : Set (Space n)) (q : Space n) (R B Eerr ρ ε : ℝ) where
  vertices : Set (List ℕ)
  root_mem : [] ∈ vertices
  parent_mem : ∀ v i, v ++ [i] ∈ vertices → v ∈ vertices
  source : List ℕ → Set (Space n)
  center : List ℕ → Space n
  radius : List ℕ → ℝ
  vneck : ∀ v : List ℕ, VertexNeck n k (center v) (radius v)
  step : ∀ v : List ℕ,
    ContractingStep (ν.restrict (source v)) (source v) (vneck v).neck B Eerr ρ ε
  source_root : source [] = S
  center_root : center [] = q
  radius_root : radius [] = R
  measurableSet_source : ∀ v ∈ vertices, MeasurableSet (source v)
  radius_pos : ∀ v ∈ vertices, 0 < radius v
  source_subset_ball : ∀ v ∈ vertices, source v ⊆ Metric.ball (center v) (radius v)
  energy_le : ∀ v ∈ vertices, ∀ z ∈ source v,
    allScaleEnergy (ν.restrict (source v)) k F z ≤ ENNReal.ofReal B
  family : ∀ v ∈ vertices, F = .mixed ∨ F = (vneck v).type.toFamilyKind
  step_measure_eq : ∀ v ∈ vertices, ν.restrict (source v) =
    (ν.restrict (source v)).restrict (step v).errorSet +
      (ν.restrict (source v)).restrict (step v).coreSet +
      Measure.sum (fun w : (step v).childIndex =>
        (ν.restrict (source v)).restrict ((step v).childSource w))
  child_mem_iff : ∀ v ∈ vertices, ∀ i : ℕ, v ++ [i] ∈ vertices ↔ i ∈ (step v).childIndex
  child_source : ∀ v ∈ vertices, ∀ i ∈ (step v).childIndex,
    source (v ++ [i]) = (step v).childSource i
  child_center : ∀ v ∈ vertices, ∀ i ∈ (step v).childIndex,
    center (v ++ [i]) = (step v).childCenter i
  child_radius : ∀ v ∈ vertices, ∀ i ∈ (step v).childIndex,
    radius (v ++ [i]) = (step v).childRadius i
  child_subset : ∀ v i, v ++ [i] ∈ vertices → source (v ++ [i]) ⊆ source v
  cover : ∀ v ∈ vertices, source v ⊆
    (step v).errorSet ∪ (step v).coreSet ∪ ⋃ (i : ℕ) (_ : v ++ [i] ∈ vertices), source (v ++ [i])
  disjoint_errorSet_child : ∀ v i, v ++ [i] ∈ vertices →
    Disjoint (step v).errorSet (source (v ++ [i]))
  disjoint_coreSet_child : ∀ v i, v ++ [i] ∈ vertices →
    Disjoint (step v).coreSet (source (v ++ [i]))
  disjoint_children : ∀ v i j, v ++ [i] ∈ vertices → v ++ [j] ∈ vertices → i ≠ j →
    Disjoint (source (v ++ [i])) (source (v ++ [j]))
  errorSet_le : ∀ v ∈ vertices, ν (step v).errorSet ≤ ENNReal.ofReal (Eerr * B * radius v ^ k)
  child_radius_le : ∀ v i, v ++ [i] ∈ vertices → radius (v ++ [i]) ≤ radius v / 2
  child_content_le : ∀ v ∈ vertices,
    ∑' i : {i : ℕ // v ++ [i] ∈ vertices}, ENNReal.ofReal (radius (v ++ [i.1]) ^ k) ≤
      ENNReal.ofReal (radius v ^ k / 2)

namespace StepTree

variable {n k : ℕ} {F : FamilyKind} {S : Set (Space n)} {q : Space n} {R B Eerr ρ ε : ℝ}
  {ν : Measure (Space n)}

/-- The compact carrier `K = closure(D_root)`: the closure of all
vertex cores and of the infinite-path residual set. -/
def carrier (Tr : StepTree ν k F S q R B Eerr ρ ε) : Set (Space n) :=
  closure ((⋃ v ∈ Tr.vertices, (Tr.vneck v).neck.core) ∪ treeResidual Tr.vertices Tr.source)

theorem core_subset_carrier (Tr : StepTree ν k F S q R B Eerr ρ ε) {v : List ℕ}
    (hv : v ∈ Tr.vertices) : (Tr.vneck v).neck.core ⊆ Tr.carrier := fun _ hz =>
  subset_closure (mem_union_left _ (mem_iUnion₂.mpr ⟨v, hv, hz⟩))

theorem residual_subset_carrier (Tr : StepTree ν k F S q R B Eerr ρ ε) :
    treeResidual Tr.vertices Tr.source ⊆ Tr.carrier := fun _ hz =>
  subset_closure (mem_union_right _ hz)

end StepTree

end ParabolicRectifiability
