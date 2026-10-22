import ParabolicRectifiability.Geometry.Neck.ChargeCollapse

/-!
# Charging endpoints

`totalNodeCharge_le` and `nodeErrorMass_sum_le` are finite, parabolic-incidence,
`c₁`-weighted inequalities. This module adds the further forms needed for the Radon neck
construction: unweighted, infinite-series and horizontal (spatial-incidence) versions. They
are derived from `lastWitness_sum` and `nodeErrorMass_le`.

* `incidentWitness_sum_le`: last-witness bound for a finite collection in which every node
  is within `A r_j` of every node of a deeper level (deepest-level selection, no
  measurable choice). Uses `lastWitness_sum`.
* `sum_unweight_of_pos`: cancellation of a positive lower patch constant `c₁ > 0`.
* `nodeCharge_le_of_incidence`: the finite charge over an **arbitrary** measurable
  reference space `X`, with Borel incidence sets, bounded same-level multiplicity and the
  incident-witness comparison (reference-volume summation combined with the last-witness
  bound); `nodeCharge_le_of_incidence_pos` is its unweighted form for `c₁ > 0`.
* `totalNodeCharge_le_pos`: the unweighted (`c₁ > 0`) corollary of `totalNodeCharge_le`.
* `nodeCharge_tsum_le`: the infinite node series, from one reference measure `ω N` for
  each truncation with the same constants (they need not converge), by the supremum of
  the partial sums.
* `vertical_incidence_witness`, `verticalNodeCharge_tsum_le`: parabolic incidence balls
  `P(g, A₀ r_j)` on `X = Space n`.
* `horizontal_witness_dist`, `horizontalNodeCharge_le`, `horizontalNodeCharge_tsum_le`:
  spatial incidence balls `B(x_g, A₀ r_j)` on `X = Spatial n` for the horizontal buffered
  reference measure, which carries no physical time; record-time compatibility supplies
  the witness comparison.
* `nodeErrorMass_sum_le_of_incidence`, `nodeErrorMass_tsum_le`, `nodeErrorMass_iUnion_le`:
  the unweighted node part of the neck error for `c₁ > 0`, with the
  general incidence interface, finite, over all levels, and for the countable union of the
  node error assignments.

Application notes. The charged node family must exclude the artificial root occurrence,
which is not a source point with a tail bound: take the level-zero node set empty or omit
the root. Occurrence indices are translated to finite sets of centers, which is injective
by same-level separation. The buffered reference predicates supply the measures `ω N` and
the lower patch masses with incidence radius `r_j` (`A₀ = 1`). The multiplicity hypotheses are stated with
`Finset.filter` on set membership under classical decidability.
-/

noncomputable section

namespace ParabolicRectifiability

namespace ChargeCollapse

open MeasureTheory Set
open scoped ENNReal

/-! ## Scales and the deepest witness -/

/-- The scales decrease with the level. -/
theorem coherentScale_anti {r₀ : ℝ} (hr₀ : 0 < r₀) {j j' : ℕ} (h : j ≤ j') :
    coherentScale r₀ j' ≤ coherentScale r₀ j :=
  div_le_div_of_nonneg_left hr₀.le (pow_pos (by norm_num) j) (pow_le_pow_right₀ (by norm_num) h)

/-- Last-witness bound when every node at level `j` is within
`A r_j` of every node at every deeper level `j' ≥ j`. The deepest nonempty level and one
node on it are selected as witness; an empty collection gives zero. -/
theorem incidentWitness_sum_le {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ)
    (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n)) (N₀ : ℕ)
    (hcard : ∀ j ≤ N, (I j).card ≤ N₀) (hS : ∀ j ≤ N, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j ≤ N, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (A : ℝ)
    (hwit : ∀ j ≤ N, ∀ g ∈ I j, ∀ j', j ≤ j' → j' ≤ N → ∀ y ∈ I j',
      dist g y ≤ A * coherentScale r₀ j)
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : A + c ≤ H) :
    ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) := by
  classical
  by_cases hne : ∃ j ∈ Finset.range (N + 1), (I j).Nonempty
  · obtain ⟨J, hJL, hJmax⟩ : ∃ J ∈ (Finset.range (N + 1)).filter (fun j => (I j).Nonempty),
        ∀ j ∈ (Finset.range (N + 1)).filter (fun j => (I j).Nonempty), j ≤ J := by
      have hLne : ((Finset.range (N + 1)).filter (fun j => (I j).Nonempty)).Nonempty := by
        obtain ⟨j, hj, hjn⟩ := hne
        exact ⟨j, Finset.mem_filter.mpr ⟨hj, hjn⟩⟩
      exact ⟨_, Finset.max'_mem _ hLne, fun j hj => Finset.le_max' _ j hj⟩
    obtain ⟨hJr, y, hy⟩ := Finset.mem_filter.mp hJL
    have hJN : J ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hJr)
    have hdeep : ∀ j, J < j → j ≤ N → I j = ∅ := by
      intro j hJj hjN
      by_contra hne'
      have hj : j ∈ (Finset.range (N + 1)).filter (fun j => (I j).Nonempty) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hjN),
          Finset.nonempty_iff_ne_empty.mpr hne'⟩
      exact absurd (hJmax j hj) (not_le.mpr hJj)
    exact lastWitness_sum μ k F S f B htail r₀ hr₀ N I N₀ hcard J hJN hdeep y hy
      (hS J hJN y hy) Fc (hf J hJN y hy) A
      (fun j hjJ g hg => hwit j (hjJ.trans hJN) g hg J hjJ hJN y hy) c H hc hH₁ hH₂
  · have hzero : ∀ j ∈ Finset.range (N + 1),
        ∑ g ∈ I j, betaSq μ k F g (c * coherentScale r₀ j) = 0 := by
      intro j hj
      rw [Finset.not_nonempty_iff_eq_empty.mp (fun h => hne ⟨j, hj, h⟩), Finset.sum_empty]
    rw [Finset.sum_eq_zero hzero]
    exact zero_le

/-- **Cancellation of `c₁ > 0`.** A charge weighted by `c₁ r_j^k` and bounded by
`M · C₁ R^k` gives the unweighted charge bound `M · C₁ R^k / c₁`. -/
theorem sum_unweight_of_pos {β : Type*} (s : Finset ℕ) (I : ℕ → Finset β)
    (b : ℕ → β → ℝ≥0∞) (r : ℕ → ℝ) (k : ℕ) (M : ℝ≥0∞) (C₁ c₁ R : ℝ) (hc₁ : 0 < c₁)
    (h : ∑ j ∈ s, ∑ g ∈ I j, b j g * ENNReal.ofReal (c₁ * r j ^ k) ≤
      M * ENNReal.ofReal (C₁ * R ^ k)) :
    ∑ j ∈ s, ∑ g ∈ I j, b j g * ENNReal.ofReal (r j ^ k) ≤
      M * ENNReal.ofReal (C₁ * R ^ k / c₁) := by
  have hsplit : ∑ j ∈ s, ∑ g ∈ I j, b j g * ENNReal.ofReal (c₁ * r j ^ k) =
      ENNReal.ofReal c₁ * ∑ j ∈ s, ∑ g ∈ I j, b j g * ENNReal.ofReal (r j ^ k) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun g _ => ?_
    rw [ENNReal.ofReal_mul hc₁.le]
    ring
  rw [hsplit, ENNReal.mul_le_iff_le_inv (ENNReal.ofReal_pos.mpr hc₁).ne'
    ENNReal.ofReal_ne_top] at h
  refine h.trans_eq ?_
  rw [← ENNReal.ofReal_inv_of_pos hc₁, div_eq_mul_inv,
    ENNReal.ofReal_mul' (inv_nonneg.mpr hc₁.le)]
  ring

/-! ## The finite charge over a general reference space -/

open Classical in
/-- **Finite charge over an arbitrary reference space.** Nodes `g ∈ I_j ⊆ S`,
`j ≤ N`, with cutoff `≤ F r_j`; Borel incidence sets `E j g` in a measurable space `X`
with same-level multiplicity at most `N₀` at every point; the incident-witness
comparison (two nodes incident to one point, the second at a level `j' ≥ j`, are within
`A r_j`); and a reference measure with `ω(X) ≤ C₁ R^k`, `ω(E j g) ≥ c₁ r_j^k`. Then
`∑_{j≤N} ∑_g b_μ(g, c r_j) · c₁ r_j^k ≤ (N₀/log 2)(2H/c)^{k+2} B · C₁ R^k` for
`H ≥ max{F, A + c}`. -/
theorem nodeCharge_le_of_incidence {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ) (F : FamilyKind) (S : Set (Space n))
    (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n))
    (hS : ∀ j ≤ N, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j ≤ N, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (E : ℕ → Space n → Set X)
    (hE : ∀ j ≤ N, ∀ g ∈ I j, MeasurableSet (E j g)) (N₀ : ℕ)
    (hmult : ∀ (x : X), ∀ j ≤ N, ((I j).filter fun g => x ∈ E j g).card ≤ N₀) (A : ℝ)
    (hwit : ∀ (x : X), ∀ j ≤ N, ∀ g ∈ I j, x ∈ E j g → ∀ j', j ≤ j' → j' ≤ N →
      ∀ y ∈ I j', x ∈ E j' y → dist g y ≤ A * coherentScale r₀ j)
    (ω : Measure X) (C₁ c₁ R : ℝ) (hω : ω univ ≤ ENNReal.ofReal (C₁ * R ^ k))
    (hlow : ∀ j ≤ N, ∀ g ∈ I j, ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤ ω (E j g))
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : A + c ≤ H) :
    ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j,
        betaSq μ k F g (c * coherentScale r₀ j) * ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) *
        ENNReal.ofReal (C₁ * R ^ k) := by
  have hpt : ∀ x, ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j,
      (E j g).indicator (fun _ => betaSq μ k F g (c * coherentScale r₀ j)) x ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) := by
    intro x
    have heq : ∀ j, ∑ g ∈ I j, (E j g).indicator
          (fun _ => betaSq μ k F g (c * coherentScale r₀ j)) x =
        ∑ g ∈ (I j).filter (fun g => x ∈ E j g), betaSq μ k F g (c * coherentScale r₀ j) := by
      intro j
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases h : x ∈ E j g
      · rw [Set.indicator_of_mem h, ite_eq_left h]
      · rw [Set.indicator_of_notMem h, ite_eq_right h]
    simp only [heq]
    exact incidentWitness_sum_le μ k F S f B htail r₀ hr₀ N
      (fun j => (I j).filter fun g => x ∈ E j g) N₀ (fun j hj => hmult x j hj)
      (fun j hj g hg => hS j hj g (Finset.mem_filter.mp hg).1) Fc
      (fun j hj g hg => hf j hj g (Finset.mem_filter.mp hg).1) A
      (fun j hj g hg j' hjj' hj'N y hy => hwit x j hj g (Finset.mem_filter.mp hg).1
        (Finset.mem_filter.mp hg).2 j' hjj' hj'N y (Finset.mem_filter.mp hy).1
        (Finset.mem_filter.mp hy).2)
      c H hc hH₁ hH₂
  calc ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j,
        betaSq μ k F g (c * coherentScale r₀ j) * ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k)
      ≤ ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) * ω univ :=
        Charging.referenceCharge_sum ω (Finset.range (N + 1)) I E
          (fun j hj g hg => hE j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) g hg)
          (fun j g => betaSq μ k F g (c * coherentScale r₀ j))
          (fun j _ => ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k))
          (fun j hj g hg => hlow j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) g hg) _ hpt
    _ ≤ ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) *
          ENNReal.ofReal (C₁ * R ^ k) := mul_le_mul_right hω _

open Classical in
/-- **Unweighted finite charge, `c₁ > 0`.** Under the hypotheses of
`nodeCharge_le_of_incidence` with `c₁ > 0`,
`∑_{j≤N} ∑_g b_μ(g, c r_j) r_j^k ≤ (N₀/log 2)(2H/c)^{k+2} B · C₁ R^k / c₁`. -/
theorem nodeCharge_le_of_incidence_pos {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ) (F : FamilyKind) (S : Set (Space n))
    (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n))
    (hS : ∀ j ≤ N, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j ≤ N, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (E : ℕ → Space n → Set X)
    (hE : ∀ j ≤ N, ∀ g ∈ I j, MeasurableSet (E j g)) (N₀ : ℕ)
    (hmult : ∀ (x : X), ∀ j ≤ N, ((I j).filter fun g => x ∈ E j g).card ≤ N₀) (A : ℝ)
    (hwit : ∀ (x : X), ∀ j ≤ N, ∀ g ∈ I j, x ∈ E j g → ∀ j', j ≤ j' → j' ≤ N →
      ∀ y ∈ I j', x ∈ E j' y → dist g y ≤ A * coherentScale r₀ j)
    (ω : Measure X) (C₁ c₁ R : ℝ) (hc₁ : 0 < c₁) (hω : ω univ ≤ ENNReal.ofReal (C₁ * R ^ k))
    (hlow : ∀ j ≤ N, ∀ g ∈ I j, ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤ ω (E j g))
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : A + c ≤ H) :
    ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j,
        betaSq μ k F g (c * coherentScale r₀ j) * ENNReal.ofReal (coherentScale r₀ j ^ k) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) *
        ENNReal.ofReal (C₁ * R ^ k / c₁) :=
  sum_unweight_of_pos _ I (fun j g => betaSq μ k F g (c * coherentScale r₀ j))
    (coherentScale r₀) k _ C₁ c₁ R hc₁
    (nodeCharge_le_of_incidence μ k F S f B htail r₀ hr₀ N I hS Fc hf E hE N₀ hmult A hwit
      ω C₁ c₁ R hω hlow c H hc hH₁ hH₂)

/-- **The `c₁ > 0` corollary of `totalNodeCharge_le`.** Finite parabolic incidence
on `Space n`, unweighted:
`∑_{j≤N} ∑_g b_μ(g, c r_j) r_j^k ≤ (N₀/log 2)(2H/c)^{k+2} B · C₁ R^k / c₁`. -/
theorem totalNodeCharge_le_pos {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ)
    (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n))
    (hS : ∀ j ≤ N, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j ≤ N, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (A₀ : ℝ) (N₀ : ℕ)
    (hmult : ∀ (w : Space n), ∀ j ≤ N,
      ((I j).filter fun g => dist w g < A₀ * coherentScale r₀ j).card ≤ N₀)
    (ω : Measure (Space n)) (C₁ c₁ R : ℝ) (hc₁ : 0 < c₁)
    (hω : ω univ ≤ ENNReal.ofReal (C₁ * R ^ k))
    (hlow : ∀ j ≤ N, ∀ g ∈ I j, ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤
      ω (Metric.ball g (A₀ * coherentScale r₀ j)))
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : 2 * A₀ + c ≤ H) :
    ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j,
        betaSq μ k F g (c * coherentScale r₀ j) * ENNReal.ofReal (coherentScale r₀ j ^ k) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) *
        ENNReal.ofReal (C₁ * R ^ k / c₁) :=
  sum_unweight_of_pos _ I (fun j g => betaSq μ k F g (c * coherentScale r₀ j))
    (coherentScale r₀) k _ C₁ c₁ R hc₁
    (totalNodeCharge_le μ k F S f B htail r₀ hr₀ N I hS Fc hf A₀ N₀ hmult ω C₁ c₁ R hω hlow
      c H hc hH₁ hH₂)

/-! ## The infinite node series -/

open Classical in
/-- **Infinite node series.** For a fixed infinite node family and, for every
truncation `N`, a reference measure `ω N` with the same constants (`ω N (X) ≤ C₁ R^k`,
lower patch masses `≥ c₁ r_j^k` for `j ≤ N`, `c₁ > 0`), the whole nonnegative series
satisfies `∑_j ∑_g b_μ(g, c r_j) r_j^k ≤ (N₀/log 2)(2H/c)^{k+2} B · C₁ R^k / c₁`.
The measures need not converge: each partial sum is bounded with its own `ω N`, and the
series is the supremum of its partial sums. -/
theorem nodeCharge_tsum_le {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ) (F : FamilyKind) (S : Set (Space n))
    (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (I : ℕ → Finset (Space n)) (hS : ∀ j, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (E : ℕ → Space n → Set X)
    (hE : ∀ j, ∀ g ∈ I j, MeasurableSet (E j g)) (N₀ : ℕ)
    (hmult : ∀ (x : X) (j : ℕ), ((I j).filter fun g => x ∈ E j g).card ≤ N₀) (A : ℝ)
    (hwit : ∀ (x : X) (j : ℕ), ∀ g ∈ I j, x ∈ E j g → ∀ j', j ≤ j' →
      ∀ y ∈ I j', x ∈ E j' y → dist g y ≤ A * coherentScale r₀ j)
    (ω : ℕ → Measure X) (C₁ c₁ R : ℝ) (hc₁ : 0 < c₁)
    (hω : ∀ N, ω N univ ≤ ENNReal.ofReal (C₁ * R ^ k))
    (hlow : ∀ N, ∀ j ≤ N, ∀ g ∈ I j,
      ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤ ω N (E j g))
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : A + c ≤ H) :
    ∑' j, ∑ g ∈ I j,
        betaSq μ k F g (c * coherentScale r₀ j) * ENNReal.ofReal (coherentScale r₀ j ^ k) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) *
        ENNReal.ofReal (C₁ * R ^ k / c₁) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  calc ∑ j ∈ Finset.range N, ∑ g ∈ I j,
        betaSq μ k F g (c * coherentScale r₀ j) * ENNReal.ofReal (coherentScale r₀ j ^ k)
      ≤ ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j,
        betaSq μ k F g (c * coherentScale r₀ j) * ENNReal.ofReal (coherentScale r₀ j ^ k) :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.le_succ N))
    _ ≤ _ := nodeCharge_le_of_incidence_pos μ k F S f B htail r₀ hr₀ N I
        (fun j _ g hg => hS j g hg) Fc (fun j _ g hg => hf j g hg) E
        (fun j _ g hg => hE j g hg) N₀ (fun x j _ => hmult x j) A
        (fun x j _ g hg hx j' hjj' _ y hy hy' => hwit x j g hg hx j' hjj' y hy hy')
        (ω N) C₁ c₁ R hc₁ (hω N) (hlow N) c H hc hH₁ hH₂

/-! ## Vertical endpoint: parabolic incidence on `Space n` -/

/-- Two points of parabolic incidence balls `P(g, A₀ r_j)` and `P(y, A₀ r_{j'})`
with a common point and `j ≤ j'` satisfy `d_P(g, y) ≤ 2A₀ r_j`. -/
theorem vertical_incidence_witness {n : ℕ} {r₀ A₀ : ℝ} (hr₀ : 0 < r₀) (hA₀ : 0 ≤ A₀)
    {x g y : Space n} {j j' : ℕ} (hjj' : j ≤ j')
    (hx : x ∈ Metric.ball g (A₀ * coherentScale r₀ j))
    (hy : x ∈ Metric.ball y (A₀ * coherentScale r₀ j')) :
    dist g y ≤ 2 * A₀ * coherentScale r₀ j := by
  have h1 : dist x g < A₀ * coherentScale r₀ j := Metric.mem_ball.mp hx
  have h2 : dist x y < A₀ * coherentScale r₀ j' := Metric.mem_ball.mp hy
  have h3 : A₀ * coherentScale r₀ j' ≤ A₀ * coherentScale r₀ j :=
    mul_le_mul_of_nonneg_left (coherentScale_anti hr₀ hjj') hA₀
  calc dist g y ≤ dist x g + dist x y := by
        have h4 := dist_triangle g x y
        rwa [dist_comm g x] at h4
    _ ≤ A₀ * coherentScale r₀ j + A₀ * coherentScale r₀ j := by linarith
    _ = 2 * A₀ * coherentScale r₀ j := by ring

open Classical in
/-- **Vertical endpoint, infinite series.** The node charge with parabolic
incidence balls `P(g, A₀ r_j)` in `X = Space n` and reference measures `ω N` on `Space n`
(`HasVerticalBufferedReference`, `A₀ = 1`), for `c₁ > 0` and `H ≥ max{F, 2A₀ + c}`. -/
theorem verticalNodeCharge_tsum_le {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ]
    (k : ℕ) (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (I : ℕ → Finset (Space n)) (hS : ∀ j, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (A₀ : ℝ) (hA₀ : 0 ≤ A₀) (N₀ : ℕ)
    (hmult : ∀ (x : Space n) (j : ℕ),
      ((I j).filter fun g => x ∈ Metric.ball g (A₀ * coherentScale r₀ j)).card ≤ N₀)
    (ω : ℕ → Measure (Space n)) (C₁ c₁ R : ℝ) (hc₁ : 0 < c₁)
    (hω : ∀ N, ω N univ ≤ ENNReal.ofReal (C₁ * R ^ k))
    (hlow : ∀ N, ∀ j ≤ N, ∀ g ∈ I j, ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤
      ω N (Metric.ball g (A₀ * coherentScale r₀ j)))
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H) (hH₂ : 2 * A₀ + c ≤ H) :
    ∑' j, ∑ g ∈ I j,
        betaSq μ k F g (c * coherentScale r₀ j) * ENNReal.ofReal (coherentScale r₀ j ^ k) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) *
        ENNReal.ofReal (C₁ * R ^ k / c₁) :=
  nodeCharge_tsum_le μ k F S f B htail r₀ hr₀ I hS Fc hf
    (fun j g => Metric.ball g (A₀ * coherentScale r₀ j)) (fun _ _ _ => measurableSet_ball)
    N₀ hmult (2 * A₀)
    (fun _ _ _ _ hx _ hjj' _ _ hy => vertical_incidence_witness hr₀ hA₀ hjj' hx hy)
    ω C₁ c₁ R hc₁ hω hlow c H hc hH₁ hH₂

/-! ## Horizontal endpoint: spatial incidence on `Spatial n` -/

/-- **Horizontal witness comparison.**
Two nodes `g` (at scale `r_i`) and `y` (at the smaller scale `r_j ≤ r_i`) whose spatial
coordinates are incident to one spatial point `x` (`|x - x_g| < A₀ r_i`,
`|x - x_y| < A₀ r_j`), and whose recorded times are compatible
(`|t_g - t_y| ≤ γ max{|x_g - x_y|², r_i², r_j²}`), satisfy
`d_P(g, y) ≤ max{2A₀, √γ max(2A₀, 1)} r_i`: the spatial distance is at most `2A₀ r_i`,
and `|t_g - t_y| ≤ γ (max(2A₀, 1) r_i)²`. No physical time is attached to the spatial
reference point. -/
theorem horizontal_witness_dist {n : ℕ} {γ A₀ ri rj : ℝ} (hγ : 0 ≤ γ) (hA₀ : 0 ≤ A₀)
    (hrj : 0 < rj) (hij : rj ≤ ri) {g y : Space n} {x : Spatial n}
    (hg : dist x g.1 < A₀ * ri) (hy : dist x y.1 < A₀ * rj)
    (htime : |g.2.val - y.2.val| ≤ γ * max (‖g.1 - y.1‖ ^ 2) (max (ri ^ 2) (rj ^ 2))) :
    dist g y ≤ max (2 * A₀) (Real.sqrt γ * max (2 * A₀) 1) * ri := by
  have hri : 0 < ri := hrj.trans_le hij
  have hdist : dist g y = max ‖g.1 - y.1‖ (Real.sqrt |g.2.val - y.2.val|) := by
    obtain ⟨gx, gt⟩ := g
    obtain ⟨yx, yt⟩ := y
    cases gt
    cases yt
    exact dist_point gx yx _ _
  have hsp : ‖g.1 - y.1‖ ≤ 2 * A₀ * ri := by
    have h2 : A₀ * rj ≤ A₀ * ri := mul_le_mul_of_nonneg_left hij hA₀
    rw [← dist_eq_norm]
    calc dist g.1 y.1 ≤ dist x g.1 + dist x y.1 := by
          have h1 := dist_triangle g.1 x y.1
          rwa [dist_comm g.1 x] at h1
      _ ≤ A₀ * ri + A₀ * ri := by linarith
      _ = 2 * A₀ * ri := by ring
  have hm1 : 1 ≤ max (2 * A₀) 1 := le_max_right _ _
  have hm0 : 0 ≤ max (2 * A₀) 1 := zero_le_one.trans hm1
  have hmri : 0 ≤ max (2 * A₀) 1 * ri := mul_nonneg hm0 hri.le
  have hri_le : ri ≤ max (2 * A₀) 1 * ri := le_mul_of_one_le_left hri.le hm1
  have hsq : max (‖g.1 - y.1‖ ^ 2) (max (ri ^ 2) (rj ^ 2)) ≤ (max (2 * A₀) 1 * ri) ^ 2 := by
    refine max_le ?_ (max_le ?_ ?_)
    · exact pow_le_pow_left₀ (norm_nonneg _)
        (hsp.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hri.le)) 2
    · exact pow_le_pow_left₀ hri.le hri_le 2
    · exact pow_le_pow_left₀ hrj.le (hij.trans hri_le) 2
  have hsqrt : Real.sqrt |g.2.val - y.2.val| ≤ Real.sqrt γ * (max (2 * A₀) 1 * ri) := by
    calc Real.sqrt |g.2.val - y.2.val| ≤ Real.sqrt (γ * (max (2 * A₀) 1 * ri) ^ 2) :=
          Real.sqrt_le_sqrt (htime.trans (mul_le_mul_of_nonneg_left hsq hγ))
      _ = Real.sqrt γ * (max (2 * A₀) 1 * ri) := by
          rw [Real.sqrt_mul hγ, Real.sqrt_sq hmri]
  rw [hdist]
  refine max_le ?_ ?_
  · exact hsp.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hri.le)
  · calc Real.sqrt |g.2.val - y.2.val| ≤ Real.sqrt γ * (max (2 * A₀) 1 * ri) := hsqrt
      _ = Real.sqrt γ * max (2 * A₀) 1 * ri := by ring
      _ ≤ max (2 * A₀) (Real.sqrt γ * max (2 * A₀) 1) * ri :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hri.le

open Classical in
/-- **Horizontal endpoint, finite, weighted.** The analogue of `totalNodeCharge_le`
for a reference measure `ω` on `Spatial n` (no physical time) with spatial incidence balls
`B(x_g, A₀ r_j)`, given record-time compatibility of the nodes
(`|t_g - t_y| ≤ γ max{|x_g - x_y|², r_i², r_j²}`). The
witness comparison is `horizontal_witness_dist`, so `H ≥ max{F, A_h + c}` with
`A_h = max{2A₀, √γ max(2A₀, 1)}`. -/
theorem horizontalNodeCharge_le {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ]
    (k : ℕ) (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n))
    (hS : ∀ j ≤ N, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j ≤ N, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (γ A₀ : ℝ) (hγ : 0 ≤ γ)
    (hA₀ : 0 ≤ A₀)
    (htime : ∀ i ≤ N, ∀ j ≤ N, ∀ g ∈ I i, ∀ y ∈ I j, |g.2.val - y.2.val| ≤
      γ * max (‖g.1 - y.1‖ ^ 2) (max (coherentScale r₀ i ^ 2) (coherentScale r₀ j ^ 2)))
    (N₀ : ℕ)
    (hmult : ∀ (x : Spatial n), ∀ j ≤ N,
      ((I j).filter fun g => x ∈ Metric.ball g.1 (A₀ * coherentScale r₀ j)).card ≤ N₀)
    (ω : Measure (Spatial n)) (C₁ c₁ R : ℝ) (hω : ω univ ≤ ENNReal.ofReal (C₁ * R ^ k))
    (hlow : ∀ j ≤ N, ∀ g ∈ I j, ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤
      ω (Metric.ball g.1 (A₀ * coherentScale r₀ j)))
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H)
    (hH₂ : max (2 * A₀) (Real.sqrt γ * max (2 * A₀) 1) + c ≤ H) :
    ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j,
        betaSq μ k F g (c * coherentScale r₀ j) * ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) *
        ENNReal.ofReal (C₁ * R ^ k) :=
  nodeCharge_le_of_incidence μ k F S f B htail r₀ hr₀ N I hS Fc hf
    (fun j g => Metric.ball g.1 (A₀ * coherentScale r₀ j)) (fun _ _ _ _ => measurableSet_ball)
    N₀ hmult (max (2 * A₀) (Real.sqrt γ * max (2 * A₀) 1))
    (fun _ j hj g hg hx j' hjj' hj'N y hy hy' =>
      horizontal_witness_dist hγ hA₀ (Charging.coherentScale_pos hr₀ j')
        (coherentScale_anti hr₀ hjj') (Metric.mem_ball.mp hx) (Metric.mem_ball.mp hy')
        (htime j hj j' hj'N g hg y hy))
    ω C₁ c₁ R hω hlow c H hc hH₁ hH₂

open Classical in
/-- **Horizontal endpoint, infinite series, `c₁ > 0`.** The infinite node charge
for the horizontal buffered reference measures `ω N` on `X = Spatial n` (no physical
time), with spatial incidence balls `B(x_g, A₀ r_j)` and record-time compatibility of the
nodes; the witness comparison is `horizontal_witness_dist`. -/
theorem horizontalNodeCharge_tsum_le {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ]
    (k : ℕ) (F : FamilyKind) (S : Set (Space n)) (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (I : ℕ → Finset (Space n)) (hS : ∀ j, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (γ A₀ : ℝ) (hγ : 0 ≤ γ)
    (hA₀ : 0 ≤ A₀)
    (htime : ∀ i j, ∀ g ∈ I i, ∀ y ∈ I j, |g.2.val - y.2.val| ≤
      γ * max (‖g.1 - y.1‖ ^ 2) (max (coherentScale r₀ i ^ 2) (coherentScale r₀ j ^ 2)))
    (N₀ : ℕ)
    (hmult : ∀ (x : Spatial n) (j : ℕ),
      ((I j).filter fun g => x ∈ Metric.ball g.1 (A₀ * coherentScale r₀ j)).card ≤ N₀)
    (ω : ℕ → Measure (Spatial n)) (C₁ c₁ R : ℝ) (hc₁ : 0 < c₁)
    (hω : ∀ N, ω N univ ≤ ENNReal.ofReal (C₁ * R ^ k))
    (hlow : ∀ N, ∀ j ≤ N, ∀ g ∈ I j, ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤
      ω N (Metric.ball g.1 (A₀ * coherentScale r₀ j)))
    (c H : ℝ) (hc : 0 < c) (hH₁ : Fc ≤ H)
    (hH₂ : max (2 * A₀) (Real.sqrt γ * max (2 * A₀) 1) + c ≤ H) :
    ∑' j, ∑ g ∈ I j,
        betaSq μ k F g (c * coherentScale r₀ j) * ENNReal.ofReal (coherentScale r₀ j ^ k) ≤
      ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / c) ^ (k + 2) * B) *
        ENNReal.ofReal (C₁ * R ^ k / c₁) :=
  nodeCharge_tsum_le μ k F S f B htail r₀ hr₀ I hS Fc hf
    (fun j g => Metric.ball g.1 (A₀ * coherentScale r₀ j)) (fun _ _ _ => measurableSet_ball)
    N₀ hmult (max (2 * A₀) (Real.sqrt γ * max (2 * A₀) 1))
    (fun _ j g hg hx j' hjj' y hy hy' =>
      horizontal_witness_dist hγ hA₀ (Charging.coherentScale_pos hr₀ j')
        (coherentScale_anti hr₀ hjj') (Metric.mem_ball.mp hx) (Metric.mem_ball.mp hy')
        (htime j j' g hg y hy))
    ω C₁ c₁ R hc₁ hω hlow c H hc hH₁ hH₂

/-! ## Node errors with the repaired interface -/

open Classical in
/-- **Unweighted node error, finite, `c₁ > 0`.** Under the hypotheses of
`nodeCharge_le_of_incidence_pos` with testing radius `c = 40`, suppose each node has a
model attaining its fit on `P(g, 40 r_j)` and a Borel error assignment inside `P(g, r_j)`
outside the `θ r_j`-tube of that model. Then
`θ² ∑_{j≤N} ∑_g μ(e_{j,g}) ≤ 40^{k+2} (N₀/log 2)(2H/40)^{k+2} B · C₁ R^k / c₁`. -/
theorem nodeErrorMass_sum_le_of_incidence {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ) (F : FamilyKind) (S : Set (Space n))
    (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (N : ℕ) (I : ℕ → Finset (Space n))
    (hS : ∀ j ≤ N, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j ≤ N, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (E : ℕ → Space n → Set X)
    (hE : ∀ j ≤ N, ∀ g ∈ I j, MeasurableSet (E j g)) (N₀ : ℕ)
    (hmult : ∀ (x : X), ∀ j ≤ N, ((I j).filter fun g => x ∈ E j g).card ≤ N₀) (A : ℝ)
    (hwit : ∀ (x : X), ∀ j ≤ N, ∀ g ∈ I j, x ∈ E j g → ∀ j', j ≤ j' → j' ≤ N →
      ∀ y ∈ I j', x ∈ E j' y → dist g y ≤ A * coherentScale r₀ j)
    (ω : Measure X) (C₁ c₁ R : ℝ) (hc₁ : 0 < c₁) (hω : ω univ ≤ ENNReal.ofReal (C₁ * R ^ k))
    (hlow : ∀ j ≤ N, ∀ g ∈ I j, ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤ ω (E j g))
    (H : ℝ) (hH₁ : Fc ≤ H) (hH₂ : A + 40 ≤ H)
    (θ : ℝ) (hθ : 0 < θ) (Pm : ℕ → Space n → Models n k F) (e : ℕ → Space n → Set (Space n))
    (hfit : ∀ j ≤ N, ∀ g ∈ I j, fit μ (Pm j g) g (40 * coherentScale r₀ j) ≤
      ENNReal.ofReal ((40 * coherentScale r₀ j) ^ (k + 2)) *
        betaSq μ k F g (40 * coherentScale r₀ j))
    (hem : ∀ j ≤ N, ∀ g ∈ I j, MeasurableSet (e j g))
    (he : ∀ j ≤ N, ∀ g ∈ I j, e j g ⊆ Metric.ball g (coherentScale r₀ j))
    (htube : ∀ j ≤ N, ∀ g ∈ I j, ∀ z ∈ e j g,
      ENNReal.ofReal ((θ * coherentScale r₀ j) ^ 2) < modelCost (Pm j g) z) :
    ENNReal.ofReal (θ ^ 2) * ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, μ (e j g) ≤
      ENNReal.ofReal (40 ^ (k + 2)) *
        (ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / 40) ^ (k + 2) * B) *
          ENNReal.ofReal (C₁ * R ^ k / c₁)) := by
  have hcharge := nodeCharge_le_of_incidence_pos μ k F S f B htail r₀ hr₀ N I hS Fc hf E hE
    N₀ hmult A hwit ω C₁ c₁ R hc₁ hω hlow 40 H (by norm_num) hH₁ hH₂
  have hnode : ∀ j ∈ Finset.range (N + 1), ∀ g ∈ I j,
      ENNReal.ofReal (θ ^ 2) * μ (e j g) ≤ ENNReal.ofReal (40 ^ (k + 2)) *
        (betaSq μ k F g (40 * coherentScale r₀ j) * ENNReal.ofReal (coherentScale r₀ j ^ k)) := by
    intro j hj g hg
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h := nodeErrorMass_le μ g (Charging.coherentScale_pos hr₀ j) hθ (Pm j g)
      (hfit j hjN g hg) (e j g) (hem j hjN g hg) (he j hjN g hg) (htube j hjN g hg)
    calc ENNReal.ofReal (θ ^ 2) * μ (e j g)
        ≤ ENNReal.ofReal (40 ^ (k + 2)) * ENNReal.ofReal (coherentScale r₀ j ^ k) *
            betaSq μ k F g (40 * coherentScale r₀ j) := h
      _ = ENNReal.ofReal (40 ^ (k + 2)) *
            (betaSq μ k F g (40 * coherentScale r₀ j) *
              ENNReal.ofReal (coherentScale r₀ j ^ k)) := by ring
  calc ENNReal.ofReal (θ ^ 2) * ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, μ (e j g)
      = ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, ENNReal.ofReal (θ ^ 2) * μ (e j g) := by
        simp only [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j, ENNReal.ofReal (40 ^ (k + 2)) *
          (betaSq μ k F g (40 * coherentScale r₀ j) *
            ENNReal.ofReal (coherentScale r₀ j ^ k)) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun g hg => hnode j hj g hg
    _ = ENNReal.ofReal (40 ^ (k + 2)) * ∑ j ∈ Finset.range (N + 1), ∑ g ∈ I j,
          betaSq μ k F g (40 * coherentScale r₀ j) * ENNReal.ofReal (coherentScale r₀ j ^ k) := by
        simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_right hcharge _

open Classical in
/-- **Unweighted node error, all levels, `c₁ > 0`.** Under the hypotheses of
`nodeCharge_tsum_le` with testing radius `c = 40`, the node error assignments satisfy
`θ² ∑_j ∑_g μ(e_{j,g}) ≤ 40^{k+2} (N₀/log 2)(2H/40)^{k+2} B · C₁ R^k / c₁`. -/
theorem nodeErrorMass_tsum_le {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ) (F : FamilyKind) (S : Set (Space n))
    (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (I : ℕ → Finset (Space n)) (hS : ∀ j, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (E : ℕ → Space n → Set X)
    (hE : ∀ j, ∀ g ∈ I j, MeasurableSet (E j g)) (N₀ : ℕ)
    (hmult : ∀ (x : X) (j : ℕ), ((I j).filter fun g => x ∈ E j g).card ≤ N₀) (A : ℝ)
    (hwit : ∀ (x : X) (j : ℕ), ∀ g ∈ I j, x ∈ E j g → ∀ j', j ≤ j' →
      ∀ y ∈ I j', x ∈ E j' y → dist g y ≤ A * coherentScale r₀ j)
    (ω : ℕ → Measure X) (C₁ c₁ R : ℝ) (hc₁ : 0 < c₁)
    (hω : ∀ N, ω N univ ≤ ENNReal.ofReal (C₁ * R ^ k))
    (hlow : ∀ N, ∀ j ≤ N, ∀ g ∈ I j,
      ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤ ω N (E j g))
    (H : ℝ) (hH₁ : Fc ≤ H) (hH₂ : A + 40 ≤ H)
    (θ : ℝ) (hθ : 0 < θ) (Pm : ℕ → Space n → Models n k F) (e : ℕ → Space n → Set (Space n))
    (hfit : ∀ j, ∀ g ∈ I j, fit μ (Pm j g) g (40 * coherentScale r₀ j) ≤
      ENNReal.ofReal ((40 * coherentScale r₀ j) ^ (k + 2)) *
        betaSq μ k F g (40 * coherentScale r₀ j))
    (hem : ∀ j, ∀ g ∈ I j, MeasurableSet (e j g))
    (he : ∀ j, ∀ g ∈ I j, e j g ⊆ Metric.ball g (coherentScale r₀ j))
    (htube : ∀ j, ∀ g ∈ I j, ∀ z ∈ e j g,
      ENNReal.ofReal ((θ * coherentScale r₀ j) ^ 2) < modelCost (Pm j g) z) :
    ENNReal.ofReal (θ ^ 2) * ∑' j, ∑ g ∈ I j, μ (e j g) ≤
      ENNReal.ofReal (40 ^ (k + 2)) *
        (ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / 40) ^ (k + 2) * B) *
          ENNReal.ofReal (C₁ * R ^ k / c₁)) := by
  have hcharge := nodeCharge_tsum_le μ k F S f B htail r₀ hr₀ I hS Fc hf E hE N₀ hmult A hwit
    ω C₁ c₁ R hc₁ hω hlow 40 H (by norm_num) hH₁ hH₂
  have hnode : ∀ j, ∀ g ∈ I j, ENNReal.ofReal (θ ^ 2) * μ (e j g) ≤
      ENNReal.ofReal (40 ^ (k + 2)) *
        (betaSq μ k F g (40 * coherentScale r₀ j) * ENNReal.ofReal (coherentScale r₀ j ^ k)) := by
    intro j g hg
    have h := nodeErrorMass_le μ g (Charging.coherentScale_pos hr₀ j) hθ (Pm j g)
      (hfit j g hg) (e j g) (hem j g hg) (he j g hg) (htube j g hg)
    calc ENNReal.ofReal (θ ^ 2) * μ (e j g)
        ≤ ENNReal.ofReal (40 ^ (k + 2)) * ENNReal.ofReal (coherentScale r₀ j ^ k) *
            betaSq μ k F g (40 * coherentScale r₀ j) := h
      _ = ENNReal.ofReal (40 ^ (k + 2)) *
            (betaSq μ k F g (40 * coherentScale r₀ j) *
              ENNReal.ofReal (coherentScale r₀ j ^ k)) := by ring
  calc ENNReal.ofReal (θ ^ 2) * ∑' j, ∑ g ∈ I j, μ (e j g)
      = ∑' j, ∑ g ∈ I j, ENNReal.ofReal (θ ^ 2) * μ (e j g) := by
        rw [← ENNReal.tsum_mul_left]
        simp only [Finset.mul_sum]
    _ ≤ ∑' j, ∑ g ∈ I j, ENNReal.ofReal (40 ^ (k + 2)) *
          (betaSq μ k F g (40 * coherentScale r₀ j) *
            ENNReal.ofReal (coherentScale r₀ j ^ k)) :=
        ENNReal.tsum_le_tsum fun j => Finset.sum_le_sum fun g hg => hnode j g hg
    _ = ENNReal.ofReal (40 ^ (k + 2)) * ∑' j, ∑ g ∈ I j,
          betaSq μ k F g (40 * coherentScale r₀ j) * ENNReal.ofReal (coherentScale r₀ j ^ k) := by
        rw [← ENNReal.tsum_mul_left]
        simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_right hcharge _

open Classical in
/-- **Node error of the countable union, `c₁ > 0`.** The same bound for the measure
of the union of all node error assignments, by countable subadditivity; disjointness of
the assignments (from the construction) is not needed for this upper bound. -/
theorem nodeErrorMass_iUnion_le {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ) (F : FamilyKind) (S : Set (Space n))
    (f : Space n → ℝ) (B : ℝ)
    (htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (I : ℕ → Finset (Space n)) (hS : ∀ j, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
    (hf : ∀ j, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (E : ℕ → Space n → Set X)
    (hE : ∀ j, ∀ g ∈ I j, MeasurableSet (E j g)) (N₀ : ℕ)
    (hmult : ∀ (x : X) (j : ℕ), ((I j).filter fun g => x ∈ E j g).card ≤ N₀) (A : ℝ)
    (hwit : ∀ (x : X) (j : ℕ), ∀ g ∈ I j, x ∈ E j g → ∀ j', j ≤ j' →
      ∀ y ∈ I j', x ∈ E j' y → dist g y ≤ A * coherentScale r₀ j)
    (ω : ℕ → Measure X) (C₁ c₁ R : ℝ) (hc₁ : 0 < c₁)
    (hω : ∀ N, ω N univ ≤ ENNReal.ofReal (C₁ * R ^ k))
    (hlow : ∀ N, ∀ j ≤ N, ∀ g ∈ I j,
      ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤ ω N (E j g))
    (H : ℝ) (hH₁ : Fc ≤ H) (hH₂ : A + 40 ≤ H)
    (θ : ℝ) (hθ : 0 < θ) (Pm : ℕ → Space n → Models n k F) (e : ℕ → Space n → Set (Space n))
    (hfit : ∀ j, ∀ g ∈ I j, fit μ (Pm j g) g (40 * coherentScale r₀ j) ≤
      ENNReal.ofReal ((40 * coherentScale r₀ j) ^ (k + 2)) *
        betaSq μ k F g (40 * coherentScale r₀ j))
    (hem : ∀ j, ∀ g ∈ I j, MeasurableSet (e j g))
    (he : ∀ j, ∀ g ∈ I j, e j g ⊆ Metric.ball g (coherentScale r₀ j))
    (htube : ∀ j, ∀ g ∈ I j, ∀ z ∈ e j g,
      ENNReal.ofReal ((θ * coherentScale r₀ j) ^ 2) < modelCost (Pm j g) z) :
    ENNReal.ofReal (θ ^ 2) * μ (⋃ j, ⋃ g ∈ I j, e j g) ≤
      ENNReal.ofReal (40 ^ (k + 2)) *
        (ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / 40) ^ (k + 2) * B) *
          ENNReal.ofReal (C₁ * R ^ k / c₁)) := by
  have hunion : μ (⋃ j, ⋃ g ∈ I j, e j g) ≤ ∑' j, ∑ g ∈ I j, μ (e j g) :=
    (measure_iUnion_le _).trans
      (ENNReal.tsum_le_tsum fun j => measure_biUnion_finset_le (I j) (e j))
  exact (mul_le_mul_right hunion _).trans
    (nodeErrorMass_tsum_le μ k F S f B htail r₀ hr₀ I hS Fc hf E hE N₀ hmult A hwit ω C₁ c₁ R
      hc₁ hω hlow H hH₁ hH₂ θ hθ Pm e hfit hem he htube)

end ChargeCollapse

end ParabolicRectifiability
