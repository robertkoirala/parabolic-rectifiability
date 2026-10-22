import ParabolicRectifiability.BetaP.Statements.Main

/-! # Variants of active-radius packing: intermediate statements

Definitions and proposition definitions used to prove `activeRadiusPacking_variants`: from the
all-scale active-radius bound with constant `C` (`ActiveRadiusPackingBound`), produce one
constant `C'` for the unit-parent bound with endpoint two, the exceptional bound and the
unit-parent exceptional bound. The argument uses the exact `p`-tail.

**Route (a simplification of the argument by ambient volume).** The usual argument
removes the radii `r_i ≥ 1/100` by ambient disjoint volume, partitions the rest into cells of
diameter `≤ 1/100`, and applies the all-scale bound to each cell inside a radius-`2/100` parent.
Here the large radii are not removed: every packing ball of the unit parent has `r_i ≤ 1`
(`radius_le_of_ball_subset`), which is all the exact-tail step needs (`(1,2) ⊆ (r_i,2)`); the centres are partitioned into a
dimensional number `M(n)` of cells of centre distance `< 1` (statement 2); each cell family is
again a weighted packing of the **same** parent `P(q,1)` (statement 3), so the all-scale bound
applies to it with `R = 1`; and inside a cell the exact tail turns the endpoint-two tail into an
all-scale tail with factor `2` (statement 4). Summing the cells gives
`C' = (M+1) 2^{p/2} C`. Exceptional indices are deleted by passing to the complementary
subfamily (statement 3) and monotonicity of `B_p` in the source
(`cpk2_betaPow_mono_measure`); they cost exactly their weight `Γ`.

For a finite family `(z_i, r_i, w_i)` (`Fin N`-indexed, as in `IsWeightedPacking`) and a finite
index set `I`, `c2_sub f I` is the subfamily of `f` indexed by `I`, enumerated along
`I.equivFin`.

The three statements (statement 1, the radius bound, is `radius_le_of_ball_subset`):
2. `c2_CellPartitionStatement`: centres in `P(q,1)` split into `M(n)` cells of centre distance
   `< 1`.
3. `c2_SubfamilyStatement`: subfamily reindexing; domination of atomic sources; atomic masses;
   a subfamily of a weighted packing is a weighted packing of the same parent.
4. `c2_CellTailStatement`: for an atomic source all of whose atoms lie within distance `< 1` of
   the centre `z_i`, and `r_i ≤ 1`, the all-scale tail `∫_{r_i}^∞` is at most twice the
   endpoint-two tail `∫_{r_i}^2` (exact `p`-tail).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## Subfamilies -/

/-- The subfamily of a finite family `f : Fin N → α` indexed by `I : Finset (Fin N)`,
enumerated along `I.equivFin` (so `c2_sub f I m = f i` for the `m`-th element `i` of `I`). -/
def c2_sub {α : Type*} {N : ℕ} (f : Fin N → α) (I : Finset (Fin N)) : Fin I.card → α :=
  fun m => f (I.equivFin.symm m).1

/-! ## The three statements -/

/-- `M` cells suffice in dimension `n`: any finitely many points of a unit ball `P(q,1)` carry a
labelling by `Fin M` whose equally labelled points are at distance `< 1`. -/
def c2_CellLabelling (n M : ℕ) : Prop :=
  ∀ (q : Space n) {N : ℕ} (z : Fin N → Space n), (∀ i, z i ∈ Metric.ball q 1) →
    ∃ κ : Fin N → Fin M, ∀ i j, κ i = κ j → dist (z i) (z j) < 1

/-- **Cell partition** ("partition the remaining centers into finitely many Borel cells"). For each `n` there is a number `M` of cells such that any finitely
many points of the unit ball `P(q,1)` carry a labelling by `Fin M` whose equally labelled points
are at distance `< 1` (`c2_CellLabelling n M`). (Maximal `1/2`-separated subset of the points,
`exists_maximal_separated_finset`, of cardinality `≤ 5^{n+2}` by
`card_le_of_separated_subset_closedBall`; label each point by a net point within `1/2`.) -/
def c2_CellPartitionStatement : Prop :=
  ∀ n : ℕ, ∃ M : ℕ, c2_CellLabelling n M

/-- **Subfamilies** (restricted cell sources and deleted exceptional indices). For a finite family and an index set `I`:
* the subfamily's atomic source is dominated by the full atomic source (the labelled summands of
  the subfamily are among those of the family, `I.equivFin` being a bijection onto `I`);
* the subfamily's total mass is `Σ_{i ∈ I} b_i r_i^k` (in `ℝ≥0∞`, termwise `ofReal`);
* the family's total mass is `Σ_i b_i r_i^k` (the same form for the whole family);
* a subfamily of a weighted packing of `P(q,R)` with weight bound `b` is a weighted packing of
  the same parent with the same weight bound. -/
def c2_SubfamilyStatement : Prop :=
  ∀ {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ) (I : Finset (Fin N)),
    atomicSource k (c2_sub z I) (c2_sub r I) (c2_sub w I) ≤ atomicSource k z r w ∧
    atomicSource k (c2_sub z I) (c2_sub r I) (c2_sub w I) univ =
      ∑ i ∈ I, ENNReal.ofReal (w i * r i ^ k) ∧
    atomicSource k z r w univ = ∑ i, ENNReal.ofReal (w i * r i ^ k) ∧
    ∀ (q : Space n) (R b : ℝ), IsWeightedPacking q R z r w b →
      IsWeightedPacking q R (c2_sub z I) (c2_sub r I) (c2_sub w I) b

/-- **Cell tail** (the exact `p`-tail, as used for packing). Let `λ = Σ_j b_j r_j^k δ_{z_j}` be an atomic source with positive radii
and weights whose centres are pairwise at distance `< 1`, and let `r_i ≤ 1`. Its support is the
finite set of centres: compact, of diameter `< 1`, containing `z_i`. For `s ≥ 1` the testing ball
`P(z_i,s)` contains the support, so `B_p(λ;z_i,s) = s^{-k-p} I_p` with the global fit
`I_p = inf_L ∫ d_P(w,L)^p dλ ∈ [0,∞]`, and (`cloc_pTail_proof`) `∫_2^∞ B_p^{2/p} ds/s =
(2^{q}-1)^{-1} ∫_1^2 B_p^{2/p} ds/s ≤ ∫_1^2 B_p^{2/p} ds/s` with `q = 2 + 2k/p ≥ 2`
(`clocp_tailFactor_le_one`). Since `(1,2) ⊆ (r_i,2)` and the point `2` is `scaleMeasure`-null,
the all-scale tail is at most twice the endpoint-two tail. Every `p > 0` and every family
(`I_p = ⊤` for an unavailable family). -/
def c2_CellTailStatement : Prop :=
  ∀ {n N : ℕ} (k : ℕ) (T : FamilyKind) (p : ℝ), 0 < p →
  ∀ (z : Fin N → Space n) (r w : Fin N → ℝ), (∀ j, 0 < r j) → (∀ j, 0 < w j) →
    (∀ j j', dist (z j) (z j') < 1) →
    ∀ i : Fin N, r i ≤ 1 →
    (∫⁻ s in Ioi (r i),
        betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure) ≤
      2 * ∫⁻ s in Ioo (r i) 2,
        betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p) ∂scaleMeasure

end ParabolicRectifiability.BetaP
