import ParabolicRectifiability.Geometry.Covariance
import ParabolicRectifiability.Geometry.Neck.Region

/-!
# Covariance collapse and contracting children

Definitions and elementary facts for the collapse step of the Radon neck construction
(with the covariance identity `SpatialSource.minimumError_step`) and for the contracting
children of one step of the construction.

* `SpatialSource.ofBall`: the source `ν ⌞ P(g,ρ)` of the covariance test, carried by
  the closed ball.
* `SpatialSource.rankEigenvalue S d`: the eigenvalue `λ_d(Q)` (one-based, `d`-th
  largest), and `0` outside `1 ≤ d ≤ n`.
* `NeckType.collapseModelSet`: the lower-rank model set `L × {τ}` (horizontal) or
  `L × ℝ` (vertical). It is the model set used for
  `NeckType.lowerModelSet`.
* `HoleChildren ν A R`: a Borel decomposition of one stopping assignment `A` into a
  discarded part and finitely many children of radius `R`, centered at points of `A`
  (only `center i ∈ A` is asserted; see its docstring).

Also proved here: the noncollapse mass bound, the per-hole content of collapsed and
terminal children, the child-radius contraction, and the total content contraction of one
step.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal

namespace SpatialSource

variable {n : ℕ}

/-- The source `ν ⌞ P(g, ρ)` (open parabolic ball), carried by the closed ball. This is
the covariance source `λ|P(g, 5 r_j)` of the continuation test, always formed from the original source. -/
def ofBall (ν : Measure (Space n)) [IsFiniteMeasure ν] (g : Space n) (ρ : ℝ) (hρ : 0 < ρ) :
    SpatialSource n where
  measure := ν.restrict (Metric.ball g ρ)
  finite := inferInstance
  center := g
  radius := ρ
  radius_pos := hρ
  carried := (ae_restrict_mem measurableSet_ball).mono fun _ hz => Metric.ball_subset_closedBall hz

/-- The eigenvalue `λ_d(Q)` of the covariance, `d`-th largest with one-based `d`; zero
outside `1 ≤ d ≤ n`. -/
def rankEigenvalue (S : SpatialSource n) (d : ℕ) : ℝ :=
  if h : 1 ≤ d ∧ d ≤ n then S.eigenvalue ⟨d - 1, by omega⟩ else 0

/-- `λ_d(Q) ≤ tr Q`. -/
theorem rankEigenvalue_le_trace (S : SpatialSource n) (d : ℕ) :
    S.rankEigenvalue d ≤ spatialTrace S.covariance := by
  rw [S.trace_covariance_eq_sum]
  unfold rankEigenvalue
  split_ifs with hd
  · exact Finset.single_le_sum (fun i _ => S.eigenvalue_nonneg i) (Finset.mem_univ _)
  · exact Finset.sum_nonneg fun i _ => S.eigenvalue_nonneg i

/-- **Noncollapse gives mass.** If
`λ_d(Q) ≥ a r^{k+2}` for the source radius `r`, then the mass is at least `a r^k`. -/
theorem mul_radius_pow_le_mass (S : SpatialSource n) {d k : ℕ} {a : ℝ}
    (h : a * S.radius ^ (k + 2) ≤ S.rankEigenvalue d) : a * S.radius ^ k ≤ S.mass := by
  have hr2 : 0 < S.radius ^ 2 := pow_pos S.radius_pos 2
  have hle : a * S.radius ^ k * S.radius ^ 2 ≤ S.mass * S.radius ^ 2 := by
    calc a * S.radius ^ k * S.radius ^ 2 = a * S.radius ^ (k + 2) := by ring
      _ ≤ S.mass * S.radius ^ 2 :=
        h.trans ((S.rankEigenvalue_le_trace d).trans S.trace_covariance_le)
  exact le_of_mul_le_mul_right hle hr2

/-- **Mass lower bound at a continuing center.** A continuing center at radius `ρ`
(`λ_d(Q) ≥ a ρ^{k+2}` for the original source on `P(g,ρ)`) has
`ν(P(g,ρ)) ≥ a ρ^k`. -/
theorem measure_ball_ge_of_rankEigenvalue (ν : Measure (Space n)) [IsFiniteMeasure ν]
    (g : Space n) {ρ : ℝ} (hρ : 0 < ρ) {d k : ℕ} {a : ℝ}
    (h : a * ρ ^ (k + 2) ≤ (ofBall ν g ρ hρ).rankEigenvalue d) :
    ENNReal.ofReal (a * ρ ^ k) ≤ ν (Metric.ball g ρ) := by
  have hm : a * ρ ^ k ≤ (ofBall ν g ρ hρ).mass := (ofBall ν g ρ hρ).mul_radius_pow_le_mass h
  have hmass : ENNReal.ofReal (ofBall ν g ρ hρ).mass = ν (Metric.ball g ρ) := by
    simp only [mass, ofBall, measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.ofReal_toReal (measure_ne_top ν _)
  exact (ENNReal.ofReal_le_ofReal hm).trans_eq hmass

end SpatialSource

namespace NeckType

/-- The lower-rank model set of a collapsed assignment : horizontal
`L × {τ}`, vertical `L × ℝ`. -/
def collapseModelSet {n m : ℕ} : NeckType → AffineSpatialPlane n m → ℝ → Set (Space n)
  | horizontal, L, τ => {z | z.1 ∈ L.toSet ∧ z.2.val = τ}
  | vertical, L, _ => {z | z.1 ∈ L.toSet}

end NeckType

/-- Children of one stopping assignment `A` of one step: a Borel
discarded part and finitely many Borel child sets, pairwise disjoint and covering `A`,
each inside an open ball of the common radius `R` about a center `center i`.

What the fields guarantee, and no more:
* the centers satisfy only `center i ∈ A` (`center_mem`). A center is **not** asserted to
  lie in the retained part `A \ discard`, nor in its own child set `childSet i`. Recentering
  each nonempty cell at one retained source point is a choice available in the
  construction, not a consequence of these fields;
* `discard` is only a Borel subset of `A`, disjoint from the children, with the cover
  `A ⊆ discard ∪ ⋃ i, childSet i`. It is **not** asserted to equal the tube complement
  named in the docstrings of `collapsed_children` and `terminal_children`; those statements
  assert only the stated bound on `ν discard`.

These fields suffice for the contracting step of the construction: its child fields require Borel child sources inside
the parent hole, pairwise disjointness, the cover, inclusion in the ball of the child
center and radius, finitely many children per hole and the content bound. None of them
requires the child center to lie in the retained set or in its child. The child sources
are restrictions of the original source to the child sets, so they inherit the original
square bound. -/
structure HoleChildren {n : ℕ} (ν : Measure (Space n)) (A : Set (Space n)) (R : ℝ) where
  count : ℕ
  discard : Set (Space n)
  center : Fin count → Space n
  childSet : Fin count → Set (Space n)
  measurableSet_discard : MeasurableSet discard
  measurableSet_childSet : ∀ i, MeasurableSet (childSet i)
  discard_subset : discard ⊆ A
  childSet_subset : ∀ i, childSet i ⊆ A
  center_mem : ∀ i, center i ∈ A
  childSet_subset_ball : ∀ i, childSet i ⊆ Metric.ball (center i) R
  cover : A ⊆ discard ∪ ⋃ i, childSet i
  disjoint_discard : ∀ i, Disjoint discard (childSet i)
  disjoint_childSet : ∀ i j, i ≠ j → Disjoint (childSet i) (childSet j)

namespace Contraction

/-- **Content of collapsed children.** If a hole of radius `d` has `m` children
of radius `3ρd` with `m ρ^{k-1} ≤ C` (the bound `C ρ^{-(k-1)}` on the number of cells),
then `m (3ρd)^k ≤ 3^k C ρ d^k`. -/
theorem collapsed_hole_content {k m : ℕ} (hk : 1 ≤ k) {ρ d C : ℝ} (hρ : 0 < ρ) (hd : 0 ≤ d)
    (hm : (m : ℝ) * ρ ^ (k - 1) ≤ C) :
    (m : ℝ) * (3 * ρ * d) ^ k ≤ 3 ^ k * C * ρ * d ^ k := by
  have hpow : ρ ^ k = ρ ^ (k - 1) * ρ := by
    rw [← pow_succ]
    congr 1
    omega
  have hnn : 0 ≤ 3 ^ k * ρ * d ^ k :=
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) k) hρ.le) (pow_nonneg hd k)
  calc (m : ℝ) * (3 * ρ * d) ^ k = ((m : ℝ) * ρ ^ (k - 1)) * (3 ^ k * ρ * d ^ k) := by
        rw [mul_pow, mul_pow, hpow]
        ring
    _ ≤ C * (3 ^ k * ρ * d ^ k) := mul_le_mul_of_nonneg_right hm hnn
    _ = 3 ^ k * C * ρ * d ^ k := by ring

/-- **Content of terminal children.** If a hole of radius `d` has `m` children
of radius `2εd` with `m ε^{k-2} ≤ C`, then `m (2εd)^k ≤ 2^k C ε² d^k`. -/
theorem terminal_hole_content {k m : ℕ} (hk : 2 ≤ k) {ε d C : ℝ} (hε : 0 < ε) (hd : 0 ≤ d)
    (hm : (m : ℝ) * ε ^ (k - 2) ≤ C) :
    (m : ℝ) * (2 * ε * d) ^ k ≤ 2 ^ k * C * ε ^ 2 * d ^ k := by
  have hpow : ε ^ k = ε ^ (k - 2) * ε ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hnn : 0 ≤ 2 ^ k * ε ^ 2 * d ^ k :=
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) k) (pow_nonneg hε.le 2)) (pow_nonneg hd k)
  calc (m : ℝ) * (2 * ε * d) ^ k = ((m : ℝ) * ε ^ (k - 2)) * (2 ^ k * ε ^ 2 * d ^ k) := by
        rw [mul_pow, mul_pow, hpow]
        ring
    _ ≤ C * (2 ^ k * ε ^ 2 * d ^ k) := mul_le_mul_of_nonneg_right hm hnn
    _ = 2 ^ k * C * ε ^ 2 * d ^ k := by ring

/-- **Radius contraction.** With `12ρ ≤ 1/2` and `2ε ≤ 1/2`,
a child of a collapsed hole (`r = 3ρd`, `d ≤ 4R`) or of a terminal hole (`r = 2εd`,
`d ≤ R`) has radius at most `R/2`. -/
theorem child_radius_le_half {R d ρ ε r : ℝ} (hρ : 0 ≤ ρ) (hε : 0 ≤ ε)
    (hρ' : 12 * ρ ≤ 1 / 2) (hε' : 2 * ε ≤ 1 / 2)
    (h : (r = 3 * ρ * d ∧ 0 ≤ d ∧ d ≤ 4 * R) ∨ (r = 2 * ε * d ∧ 0 ≤ d ∧ d ≤ R)) :
    r ≤ R / 2 := by
  rcases h with ⟨rfl, hd0, hd⟩ | ⟨rfl, hd0, hd⟩
  · have hR : 0 ≤ R := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ') hR, mul_nonneg hρ (sub_nonneg.mpr hd)]
  · have hR : 0 ≤ R := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hε') hR, mul_nonneg hε (sub_nonneg.mpr hd)]

/-- **Content contraction of one step.** Suppose the holes
`c` have radii `d c ≥ 0` with joint content `∑_c d_c^k ≤ C_g R^k`, and each hole has `m c`
children of radius `rad c` with `m_c · rad_c^k ≤ K d_c^k`, where
`K = 3^k C_col ρ + 2^k C_ter ε²` covers both kinds of holes. If `C_g K ≤ 1/2`, the total
child content is at most `R^k/2`. -/
theorem children_content_le_half {ι : Type*} {k : ℕ} {R Cg K : ℝ} (hR : 0 ≤ R) (hK : 0 ≤ K)
    (d : ι → ℝ) (hcontent : ∑' c, ENNReal.ofReal (d c ^ k) ≤ ENNReal.ofReal (Cg * R ^ k))
    (m : ι → ℕ) (rad : ι → ℝ) (hhole : ∀ c, (m c : ℝ) * rad c ^ k ≤ K * d c ^ k)
    (hsmall : Cg * K ≤ 1 / 2) :
    ∑' c, ENNReal.ofReal ((m c : ℝ) * rad c ^ k) ≤ ENNReal.ofReal (R ^ k / 2) := by
  have hRk : 0 ≤ R ^ k := pow_nonneg hR k
  calc ∑' c, ENNReal.ofReal ((m c : ℝ) * rad c ^ k)
      ≤ ∑' c, ENNReal.ofReal K * ENNReal.ofReal (d c ^ k) :=
        ENNReal.tsum_le_tsum fun c => by
          rw [← ENNReal.ofReal_mul hK]
          exact ENNReal.ofReal_le_ofReal (hhole c)
    _ = ENNReal.ofReal K * ∑' c, ENNReal.ofReal (d c ^ k) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (Cg * R ^ k) := mul_le_mul_right hcontent _
    _ = ENNReal.ofReal (K * (Cg * R ^ k)) := (ENNReal.ofReal_mul hK).symm
    _ ≤ ENNReal.ofReal (R ^ k / 2) := ENNReal.ofReal_le_ofReal (by nlinarith)

end Contraction

end ParabolicRectifiability
