import ParabolicRectifiability.Geometry.Neck.Charging
import ParabolicRectifiability.Geometry.Neck.LastWitness
import ParabolicRectifiability.Geometry.Neck.CollapseLowerModel
import ParabolicRectifiability.Geometry.Neck.CollapsedChildren
import ParabolicRectifiability.Geometry.Neck.TerminalChildren
import ParabolicRectifiability.Geometry.Neck.Collapse
import ParabolicRectifiability.Measure.ScaleEnergy

/-!
# Charging and collapse contracts

Statements for the charging of node errors and for the collapse of assignments, together
with the finite charge and error bounds that assemble them with the lemmas of
the `Charging` and `ChargeCollapse` developments.

All sources are the original measure or its restrictions to Borel sets; no measure is
formed by subtraction. Tail hypotheses are written out as
`∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ B`, which is definitionally
`tailEnergy μ k F (f y) y ≤ B`.

**Charging.**
* `lastWitness_sum` (the last-witness bound), and its two forms `lastWitness_commonCenter`
  and `lastWitness_movingPoint`;
* `nodeErrorMass_le` (Chebyshev for one node's error assignment);
* `totalNodeCharge_le` (finite, parabolic-incidence, `c₁`-weighted total node charge) and
  `nodeErrorMass_sum_le` (finite weighted node part of the neck error). The horizontal
  (spatial-incidence), `c₁ > 0` and infinite-sum endpoints are proved separately (`incidentWitness_sum_le`, `nodeCharge_tsum_le`, `horizontalNodeCharge_le`).

**Collapse and contracting children.**
* `collapsed_lowerModel_error` (the covariance identity applied to a failed
  continuation test);
* `collapsed_children` and `terminal_children` (the tube covers of one step of the
  construction);
* `collapsedAssignmentBound_of_failure`: the collapsed-assignment error bound when the
  continuation test fails.
-/

noncomputable section

namespace ParabolicRectifiability

namespace ChargeCollapse

open MeasureTheory Set
open scoped ENNReal

/-! ## The last witness -/

/-- **Last-witness bound.**
Let `μ` be a finite measure, `S` a set, and `f` a cutoff with the tail bound
`∫_{f(y)}^∞ b_μ(y,s) ds/s ≤ B` at every `y ∈ S`. Let `r_j = 10^{-j} r_0`, `0 ≤ j ≤ N`, and
let finite sets `I_j` have at most `N₀` elements. Suppose `J ≤ N` is the deepest nonempty
level (`I_j = ∅` for `J < j ≤ N`) and the witness `y ∈ I_J ∩ S` satisfies
`f(y) ≤ F r_J` and `d_P(g, y) ≤ A r_j` for every `j ≤ J`, `g ∈ I_j`. Then for every
`c > 0` and `H ≥ max{F, A + c}`
`∑_{j ≤ N} ∑_{g ∈ I_j} b_μ(g, c r_j) ≤ (N₀ / log 2) (2H/c)^{k+2} B`.
The witness is chosen once for the finite collection; no measurable choice is used. -/
theorem lastWitness_sum {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ)
    (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n)) (N₀ : ℕ)
    (hcard : ∀ j ≤ N, (I j).card ≤ N₀) (J : ℕ) (hJ : J ≤ N)
    (hdeep : ∀ j, J < j → j ≤ N → I j = ∅) (y : Space n) (hyI : y ∈ I J) (hyS : y ∈ S)
    (Fc : ℝ) (hfy : f y ≤ Fc * coherentScale r₀ J) (A : ℝ)
    (hA : ∀ j ≤ J, ∀ g ∈ I j, dist g y ≤ A * coherentScale r₀ j)
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : A + c ≤ H) :
    ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) := by
  exact lastWitness_sum_proof μ k F S f B htail r₀ hr₀ N I N₀ hcard J hJ hdeep y hyI hyS Fc hfy A hA c H hc hH₁ hH₂

/-- **Last witness, common center.** If every
center at every level `j ≤ N` lies within `A₀ r_j` of one point `w`, all centers lie in
`S` and have cutoff at most `F r_j`, then the last-witness bound holds with
`H ≥ max{F, 2 A₀ + c}`. The proof selects the deepest nonempty level and one center
on it as witness (`d_P(g,y) ≤ A₀ r_j + A₀ r_J ≤ 2 A₀ r_j`) and applies the last-witness bound; an
empty collection has sum zero. -/
theorem lastWitness_commonCenter {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ]
    (k : ℕ) (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n)) (N₀ : ℕ)
    (hcard : ∀ j ≤ N, (I j).card ≤ N₀) (hS : ∀ j ≤ N, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j ≤ N, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (w : Space n) (A₀ : ℝ)
    (hw : ∀ j ≤ N, ∀ g ∈ I j, dist g w ≤ A₀ * coherentScale r₀ j)
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : 2 * A₀ + c ≤ H) :
    ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) := by
  exact lastWitness_commonCenter_proof μ k F S f B htail r₀ hr₀ N I N₀ hcard hS Fc hf w A₀ hw c H hc hH₁ hH₂

/-- **Last witness, moving point.** If `q_j` is a
moving point with `d_P(q_{j+1}, q_j) ≤ D₀ r_j` (`D₀ ≥ 0`) and every center at level `j`
lies within `A₀ r_j` of `q_j`, then `d_P(g,y) ≤ (2A₀ + D₀/(1 - 1/10)) r_j` for the deepest
witness, and the last-witness bound holds with `H ≥ max{F, 2A₀ + (10/9) D₀ + c}`. -/
theorem lastWitness_movingPoint {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ]
    (k : ℕ) (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n)) (N₀ : ℕ)
    (hcard : ∀ j ≤ N, (I j).card ≤ N₀) (hS : ∀ j ≤ N, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j ≤ N, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (q : ℕ → Space n) (A₀ D₀ : ℝ)
    (hD₀ : 0 ≤ D₀) (hq : ∀ j < N, dist (q (j + 1)) (q j) ≤ D₀ * coherentScale r₀ j)
    (hw : ∀ j ≤ N, ∀ g ∈ I j, dist g (q j) ≤ A₀ * coherentScale r₀ j)
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : 2 * A₀ + 10 / 9 * D₀ + c ≤ H) :
    ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) := by
  exact lastWitness_movingPoint_proof μ k F S f B htail r₀ hr₀ N I N₀ hcard hS Fc hf q A₀ D₀ hD₀ hq hw c H hc hH₁ hH₂

/-! ## Node errors -/

/-- **Node error by Chebyshev.** Let the model `Pm` attain the
fit of the original source at `g` and radius `40 r`, i.e.
`∫_{P(g,40r)} d_P(z,Pm)^2 dμ ≤ (40r)^{k+2} b_μ(g, 40r)`. If a Borel set `e ⊆ P(g, r)`
lies outside the `θ r`-tube of `Pm` (`d_P(z, Pm)^2 > (θ r)^2` on `e`), then
`θ² μ(e) ≤ 40^{k+2} r^k b_μ(g, 40 r)`. -/
theorem nodeErrorMass_le {n k : ℕ} {F : FamilyKind} (μ : Measure (Space n)) (g : Space n)
    {r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ) (Pm : Models n k F)
    (hfit : fit μ Pm g (40 * r) ≤ ENNReal.ofReal ((40 * r) ^ (k + 2)) * betaSq μ k F g (40 * r))
    (e : Set (Space n)) (hem : MeasurableSet e) (he : e ⊆ Metric.ball g r)
    (htube : ∀ z ∈ e, ENNReal.ofReal ((θ * r) ^ 2) < modelCost Pm z) :
    ENNReal.ofReal (θ ^ 2) * μ e ≤
      ENNReal.ofReal (40 ^ (k + 2)) * ENNReal.ofReal (r ^ k) * betaSq μ k F g (40 * r) := by
  exact nodeErrorMass_le_proof μ g hr hθ Pm hfit e hem he htube

/-- **Total node charge.** Finitely many levels of
nodes `g ∈ I_j ⊆ S` (`j ≤ N`) with cutoff `f(g) ≤ F r_j`, incidence balls `P(g, A₀ r_j)`
of same-level multiplicity at most `N₀`, and a finite reference measure `ω` with
`ω(X) ≤ C₁ R^k` and `ω(P(g, A₀ r_j)) ≥ c₁ r_j^k` give
`∑_{j ≤ N} ∑_{g ∈ I_j} b_μ(g, c r_j) · c₁ r_j^k ≤ (N₀/log 2)(2H/c)^{k+2} B · C₁ R^k`
for `H ≥ max{F, 2A₀ + c}`. Proof: at each point the incident nodes lie within `A₀ r_j`
of it, so `lastWitness_commonCenter` bounds the pointwise incidence sum; then
`Charging.referenceCharge_sum` integrates against `ω`. -/
theorem totalNodeCharge_le {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ)
    (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n))
    (hS : ∀ j ≤ N, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j ≤ N, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (A₀ : ℝ) (N₀ : ℕ)
    (hmult : ∀ (w : Space n), ∀ j ≤ N,
      ((I j).filter fun g => dist w g < A₀ * coherentScale r₀ j).card ≤ N₀)
    (ω : Measure (Space n)) (C₁ c₁ R : ℝ) (hω : ω univ ≤ ENNReal.ofReal (C₁ * R ^ k))
    (hlow : ∀ j ≤ N, ∀ g ∈ I j, ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤
      ω (Metric.ball g (A₀ * coherentScale r₀ j)))
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : 2 * A₀ + c ≤ H) :
    ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j,
        betaSq μ k F g (c * coherentScale r₀ j) * ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) *
        ENNReal.ofReal (C₁ * R ^ k) := by
  have hpt : ∀ x, ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j,
      (Metric.ball g (A₀ * coherentScale r₀ j)).indicator
        (fun _ => betaSq μ k F g (c * coherentScale r₀ j)) x ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) := by
    intro x
    have heq : ∀ j, ∑ g ∈ I j, (Metric.ball g (A₀ * coherentScale r₀ j)).indicator
          (fun _ => betaSq μ k F g (c * coherentScale r₀ j)) x =
        ∑ g ∈ (I j).filter (fun g => dist x g < A₀ * coherentScale r₀ j),
          betaSq μ k F g (c * coherentScale r₀ j) := by
      intro j
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases h : dist x g < A₀ * coherentScale r₀ j
      · rw [Set.indicator_of_mem (Metric.mem_ball.mpr h), ite_eq_left h]
      · rw [Set.indicator_of_notMem (fun hm => h (Metric.mem_ball.mp hm)), ite_eq_right h]
    simp only [heq]
    exact lastWitness_commonCenter μ k F S f B htail r₀ hr₀ N
      (fun j => (I j).filter fun g => dist x g < A₀ * coherentScale r₀ j) N₀
      (fun j hj => hmult x j hj)
      (fun j hj g hg => hS j hj g (Finset.mem_filter.mp hg).1) Fc
      (fun j hj g hg => hf j hj g (Finset.mem_filter.mp hg).1) x A₀
      (fun j _ g hg => by rw [dist_comm]; exact (Finset.mem_filter.mp hg).2.le)
      c H hc hH₁ hH₂
  calc ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j,
        betaSq μ k F g (c * coherentScale r₀ j) * ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k)
      ≤ ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) * ω univ :=
        Charging.referenceCharge_sum ω (Finset.range (N + 1)) I
          (fun j g => Metric.ball g (A₀ * coherentScale r₀ j)) (fun _ _ _ _ => measurableSet_ball)
          (fun j g => betaSq μ k F g (c * coherentScale r₀ j))
          (fun j _ => ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k))
          (fun j hj g hg => hlow j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) g hg) _ hpt
    _ ≤ ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) *
          ENNReal.ofReal (C₁ * R ^ k) := mul_le_mul_right hω _

/-- **Node part of the neck error.** Under the hypotheses
of `totalNodeCharge_le` with testing radius `c = 40`, suppose each node `g ∈ I_j` has a
model `Pm j g` attaining its fit on `P(g, 40 r_j)` and a Borel error assignment
`e j g ⊆ P(g, r_j)` outside the `θ r_j`-tube of that model. Then
`c₁ θ² ∑_{j,g} μ(e_{j,g}) ≤ 40^{k+2} (N₀/log 2)(2H/40)^{k+2} B · C₁ R^k`,
i.e. the summed node error is at most `C θ^{-2} B R^k`. -/
theorem nodeErrorMass_sum_le {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ)
    (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n))
    (hS : ∀ j ≤ N, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j ≤ N, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (A₀ : ℝ) (N₀ : ℕ)
    (hmult : ∀ (w : Space n), ∀ j ≤ N,
      ((I j).filter fun g => dist w g < A₀ * coherentScale r₀ j).card ≤ N₀)
    (ω : Measure (Space n)) (C₁ c₁ R : ℝ) (hc₁ : 0 ≤ c₁)
    (hω : ω univ ≤ ENNReal.ofReal (C₁ * R ^ k))
    (hlow : ∀ j ≤ N, ∀ g ∈ I j, ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤
      ω (Metric.ball g (A₀ * coherentScale r₀ j)))
    (H : ℝ) (hH₁ : Fc ≤ H) (hH₂ : 2 * A₀ + 40 ≤ H)
    (θ : ℝ) (hθ : 0 < θ) (Pm : ℕ → Space n → Models n k F) (e : ℕ → Space n → Set (Space n))
    (hfit : ∀ j ≤ N, ∀ g ∈ I j, fit μ (Pm j g) g (40 * coherentScale r₀ j) ≤
      ENNReal.ofReal ((40 * coherentScale r₀ j) ^ (k + 2)) *
        betaSq μ k F g (40 * coherentScale r₀ j))
    (hem : ∀ j ≤ N, ∀ g ∈ I j, MeasurableSet (e j g))
    (he : ∀ j ≤ N, ∀ g ∈ I j, e j g ⊆ Metric.ball g (coherentScale r₀ j))
    (htube : ∀ j ≤ N, ∀ g ∈ I j, ∀ z ∈ e j g,
      ENNReal.ofReal ((θ * coherentScale r₀ j) ^ 2) < modelCost (Pm j g) z) :
    ENNReal.ofReal c₁ *
        (ENNReal.ofReal (θ ^ 2) * ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, μ (e j g)) ≤
      ENNReal.ofReal (40 ^ (k + 2)) *
        (ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / 40) ^ (k + 2) * B) *
          ENNReal.ofReal (C₁ * R ^ k)) := by
  have hcharge := totalNodeCharge_le μ k F S f B htail r₀ hr₀ N I hS Fc hf A₀ N₀ hmult ω C₁ c₁ R
    hω hlow 40 H (by norm_num) hH₁ hH₂
  have hnode : ∀ j ∈ Finset.range (N + 1), ∀ g ∈ I j,
      ENNReal.ofReal c₁ * (ENNReal.ofReal (θ ^ 2) * μ (e j g)) ≤
        ENNReal.ofReal (40 ^ (k + 2)) *
          (betaSq μ k F g (40 * coherentScale r₀ j) *
            ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k)) := by
    intro j hj g hg
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h := nodeErrorMass_le μ g (Charging.coherentScale_pos hr₀ j) hθ (Pm j g)
      (hfit j hjN g hg) (e j g) (hem j hjN g hg) (he j hjN g hg) (htube j hjN g hg)
    calc ENNReal.ofReal c₁ * (ENNReal.ofReal (θ ^ 2) * μ (e j g))
        ≤ ENNReal.ofReal c₁ * (ENNReal.ofReal (40 ^ (k + 2)) *
            ENNReal.ofReal (coherentScale r₀ j ^ k) * betaSq μ k F g (40 * coherentScale r₀ j)) :=
          mul_le_mul_right h _
      _ = ENNReal.ofReal (40 ^ (k + 2)) *
            (betaSq μ k F g (40 * coherentScale r₀ j) *
              ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k)) := by
          rw [ENNReal.ofReal_mul hc₁]
          ring
  calc ENNReal.ofReal c₁ *
        (ENNReal.ofReal (θ ^ 2) * ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, μ (e j g))
      = ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j,
          ENNReal.ofReal c₁ * (ENNReal.ofReal (θ ^ 2) * μ (e j g)) := by
        simp only [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, ENNReal.ofReal (40 ^ (k + 2)) *
          (betaSq μ k F g (40 * coherentScale r₀ j) *
            ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k)) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun g hg => hnode j hj g hg
    _ = ENNReal.ofReal (40 ^ (k + 2)) * ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j,
          betaSq μ k F g (40 * coherentScale r₀ j) *
            ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) := by
        simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_right hcharge _

/-! ## Collapse -/

/-- **The covariance identity at a failed continuation test.** Let `T` be available with positive spatial rank `d = T.rank k`, and
let the covariance of the original source on `P(g, ρ)` have `λ_d(Q) < a ρ^{k+2}`. Then for
every model `Pm` of type `T` there are a spatial plane `L⁻` of rank `d - 1` and a time `τ`
with `∫_{P(g,ρ)} d_P(z, L⁻-model)^2 dμ ≤ a ρ^{k+2} + 2 ∫_{P(g,ρ)} d_P(z, Pm)^2 dμ`.
Proof route: `I_{d-1} = λ_d(Q) + I_d` (`SpatialSource.minimumError_step`),
`I_d ≤` the spatial part of the fit of `Pm`, the minimizer of `I_{d-1}` is attained; in the
horizontal case keep the time `τ` of `Pm` and use `max{u,v} ≤ u + v` (one more copy of the
fit). -/
theorem collapsed_lowerModel_error {n k : ℕ} {T : NeckType} (hT : T.Available n k)
    (hrank : 1 ≤ T.rank k) (μ : Measure (Space n)) [IsFiniteMeasure μ] (g : Space n)
    {ρ : ℝ} (hρ : 0 < ρ) (a : ℝ)
    (hsmall : (SpatialSource.ofBall μ g ρ hρ).rankEigenvalue (T.rank k) < a * ρ ^ (k + 2))
    (Pm : Models n k T.toFamilyKind) :
    ∃ (L : AffineSpatialPlane n (T.rank k - 1)) (τ : ℝ),
      ∫⁻ z in Metric.ball g ρ, Metric.infEDist z (T.collapseModelSet L τ) ^ 2 ∂μ ≤
        ENNReal.ofReal (a * ρ ^ (k + 2)) + 2 * fit μ Pm g ρ := by
  exact collapsed_lowerModel_error_proof hT hrank μ g hρ a hsmall Pm

/-- **Collapsed-assignment error bound.** Let `A` be a
collapsed assignment inside `P(g, ρ)`, `ρ = 5 r_j`. At positive rank, suppose the
continuation test failed (`λ_d(Q) < a ρ^{k+2}` for the original source on `P(g,ρ)`) and
some model of type `T` has `∫_{P(g,ρ)} d_P(z,Pm)^2 dμ ≤ C_B B ρ^{k+2}` (from the node beta bound
and the fit at `40 r_j`); at rank zero suppose the mass test failed
(`μ(P(g,ρ)) < a ρ²`). Then the conclusion is
`CollapsedAssignmentBound T k μ A ρ a B (1 + 2 C_B)` (with `collapseModelSet` for
`lowerModelSet`). -/
theorem collapsedAssignmentBound_of_failure {n k : ℕ} {T : NeckType} (hT : T.Available n k)
    (μ : Measure (Space n)) [IsFiniteMeasure μ] (g : Space n) {ρ : ℝ} (hρ : 0 < ρ)
    (A : Set (Space n)) (hA : A ⊆ Metric.ball g ρ) {a B CB : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hCB : 0 ≤ CB)
    (hpos : 0 < T.rank k →
      (SpatialSource.ofBall μ g ρ hρ).rankEigenvalue (T.rank k) < a * ρ ^ (k + 2) ∧
        ∃ Pm : Models n k T.toFamilyKind,
          fit μ Pm g ρ ≤ ENNReal.ofReal (CB * B * ρ ^ (k + 2)))
    (hzero : T.rank k = 0 → μ (Metric.ball g ρ) < ENNReal.ofReal (a * ρ ^ 2)) :
    (0 < T.rank k → ∃ (L : AffineSpatialPlane n (T.rank k - 1)) (τ : ℝ),
        ∫⁻ z in A, Metric.infEDist z (T.collapseModelSet L τ) ^ 2 ∂μ ≤
          ENNReal.ofReal ((1 + 2 * CB) * (a + B) * ρ ^ (k + 2))) ∧
      (T.rank k = 0 → μ A < ENNReal.ofReal (a * ρ ^ 2)) := by
  refine ⟨fun h => ?_, fun h => (measure_mono hA).trans_lt (hzero h)⟩
  obtain ⟨hev, Pm, hfit⟩ := hpos h
  obtain ⟨L, τ, hL⟩ := collapsed_lowerModel_error hT (Nat.succ_le_of_lt h) μ g hρ a hev Pm
  refine ⟨L, τ, ?_⟩
  have hρp : 0 ≤ ρ ^ (k + 2) := pow_nonneg hρ.le _
  have h1 : 0 ≤ a * ρ ^ (k + 2) := mul_nonneg ha hρp
  have h2 : 0 ≤ CB * B * ρ ^ (k + 2) := mul_nonneg (mul_nonneg hCB hB) hρp
  calc ∫⁻ z in A, Metric.infEDist z (T.collapseModelSet L τ) ^ 2 ∂μ
      ≤ ∫⁻ z in Metric.ball g ρ, Metric.infEDist z (T.collapseModelSet L τ) ^ 2 ∂μ :=
        lintegral_mono_set hA
    _ ≤ ENNReal.ofReal (a * ρ ^ (k + 2)) + 2 * fit μ Pm g ρ := hL
    _ ≤ ENNReal.ofReal (a * ρ ^ (k + 2)) + 2 * ENNReal.ofReal (CB * B * ρ ^ (k + 2)) :=
        add_le_add_right (mul_le_mul_right hfit 2) _
    _ = ENNReal.ofReal (a * ρ ^ (k + 2) + 2 * (CB * B * ρ ^ (k + 2))) := by
        rw [ENNReal.ofReal_add h1 (mul_nonneg (by norm_num) h2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
    _ ≤ ENNReal.ofReal ((1 + 2 * CB) * (a + B) * ρ ^ (k + 2)) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_nonneg (mul_nonneg hCB ha) hρp, mul_nonneg hB hρp]

/-! ## Contracting children -/

/-- **Collapsed tube cover.** There is a
dimensional constant `C` such that the following holds. Let `T` be available with positive
spatial rank, `A ⊆ P(c, d)` a Borel collapsed assignment and `L × {τ}` (horizontal) or
`L × ℝ` (vertical) a lower-rank model with
`∫_A d_P(z, model)^2 dμ ≤ K d^{k+2}`. For every `0 < ρ ≤ 1` there are children of `A` of
radius `3ρd` (`HoleChildren`) whose discarded part has mass at most `4K d^k/ρ²`, and whose
number `m` obeys `m ρ^{k-1} ≤ C`. The conclusion asserts only the fields of `HoleChildren`
(in particular centers in `A`) and these two bounds. Construction behind the statement, not
part of the conclusion: discard the points of `A` at distance at least `ρd/2` from the
model; a net on the parabolically `(k-1)`-dimensional model inside a fixed enlargement of
`P(c,d)` covers the tube with `C ρ^{-(k-1)}` balls of radius `ρd`; cells are recentered at
retained source points and assigned to the first ball in a finite order. -/
theorem collapsed_children (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType}, T.Available n k → 1 ≤ T.rank k →
      ∀ (μ : Measure (Space n)) [IsFiniteMeasure μ] (A : Set (Space n)), MeasurableSet A →
      ∀ (c : Space n) (d : ℝ), 0 < d → A ⊆ Metric.ball c d →
      ∀ (L : AffineSpatialPlane n (T.rank k - 1)) (τ K : ℝ),
        ∫⁻ z in A, Metric.infEDist z (T.collapseModelSet L τ) ^ 2 ∂μ ≤
          ENNReal.ofReal (K * d ^ (k + 2)) →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        ∃ Hc : HoleChildren μ A (3 * ρ * d),
          μ Hc.discard ≤ ENNReal.ofReal (4 * K * d ^ k / ρ ^ 2) ∧
            (Hc.count : ℝ) * ρ ^ (k - 1) ≤ C := by
  exact collapsed_children_proof n

/-- **Terminal tube cover.** There is a
dimensional constant `C` such that, for `2 ≤ k ≤ n`, a Borel terminal assignment
`A ⊆ P(c,d)` with two models `L_H` (horizontal) and `L_V` (vertical) of joint error
`∫_A (d_P(z,L_H)^2 + d_P(z,L_V)^2) dμ ≤ K d^{k+2}` and every
`0 < ε ≤ 1` admit children of radius `2εd` whose discarded part has mass at most
`2K d^k/ε²` and whose number `m` obeys `m ε^{k-2} ≤ C`. The conclusion asserts only the
fields of `HoleChildren` (in particular centers in `A`) and these two bounds. Construction
behind the statement, not part of the conclusion: discard the points of `A` outside the two
open `εd`-tubes; take as centers a maximal spatial `εd`-separated subset of retained points
near the `(k-2)`-plane of `L_V`, inside the time slab of `L_H`. No alignment of the two
planes is used. -/
theorem terminal_children (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ}, 2 ≤ k → k ≤ n →
      ∀ (μ : Measure (Space n)) [IsFiniteMeasure μ] (A : Set (Space n)), MeasurableSet A →
      ∀ (c : Space n) (d : ℝ), 0 < d → A ⊆ Metric.ball c d →
      ∀ (LH : HorizontalModel n k) (LV : VerticalModel n k) (K : ℝ),
        ∫⁻ z in A, (modelCost (T := .horizontal) LH z + modelCost (T := .vertical) LV z) ∂μ ≤
          ENNReal.ofReal (K * d ^ (k + 2)) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ Hc : HoleChildren μ A (2 * ε * d),
          μ Hc.discard ≤ ENNReal.ofReal (2 * K * d ^ k / ε ^ 2) ∧
            (Hc.count : ℝ) * ε ^ (k - 2) ≤ C := by
  exact terminal_children_proof n

end ChargeCollapse

end ParabolicRectifiability
