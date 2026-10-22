import ParabolicRectifiability.Measure.Neck.Definitions
import ParabolicRectifiability.Measure.AtomicBarycenterTransfer

/-! # Discrete and variable-radius packing as consequences

Two implications between statements of the source construction:

* `discrete_packing_of_decomposition`: the countable neck decomposition
  (`exists_countable_neck_decomposition`) implies the truncated discrete packing theorem
  (`discrete_packing`);
* `variable_radius_packing_of_discrete`: the truncated discrete packing theorem
  implies the variable-radius packing transfer (`variable_radius_packing`).

Both take the earlier statement as an explicit hypothesis; nothing else is assumed.

The bridge `truncatedAtomicSource_eq_finiteCutoffAtomicMeasure` identifies the
truncated atomic source of discrete packing with the cutoff atomic measure of the
barycenter transfer, with atomic masses `w j * r j ^ k`.

**Discrete packing.** The full atomic source `σ = ∑ b_j r_j^k δ_{z_j}` is carried
by the finite set of centers. Disjointness of `P(z_i,r_i)` and `P(z_j,r_j)` puts
`z_j` outside `P(z_i,r_i)`. Hence below `r_i` the testing ball `P(z_i,s)` sees only
its central atom, which lies on a model, so `β = 0`; above `r_i` an atom with
`r_j > s` is outside `P(z_i,s)`, so full and truncated sources agree there. The
all-scale energy at every center is thus at most `B < B + b`. The decomposition
with budget `B + b > 0` gives the loss `σ(X \ K) ≤ C (B+b) R^k` and the packing
`∑_{z_i ∈ K} r_i^k ≤ C R^k`; the radii satisfy `r_i ≤ R` because
`P(z_i,r_i) ⊆ P(q,R)`.

**Variable-radius packing.** Cells `closure P(z_i, r_i/100)`, cutoff radii
`ρ_i = r_i/2`, atomic masses `ρ_i^k`, and `A = 50^k/a`, with square-good samples
in each cell. The barycenter transfer bounds the atomic energy by
`2^(k+2) 50^k L / a`; the atomic balls `P(c_i, ρ_i) ⊆ P(z_i, r_i)` are disjoint and
lie in `P(q, 2R)`. The discrete theorem with coefficients one gives
`∑ ρ_i^k ≤ C (1 + 2^(k+2) 50^k L/a) (2R)^k`; multiply by `2^k`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-! ## The bridge to cutoff atomic measures -/

/-- The truncated atomic source of discrete packing is the cutoff atomic measure with
masses `w j * r j ^ k` and cutoffs `r j`. No positivity is needed. -/
theorem truncatedAtomicSource_eq_finiteCutoffAtomicMeasure {n l : ℕ} (k : ℕ)
    (z : Fin l → Space n) (r w : Fin l → ℝ) (s : ℝ) :
    truncatedAtomicSource k z r w s =
      finiteCutoffAtomicMeasure z r (fun j => w j * r j ^ k) s := by
  unfold truncatedAtomicSource finiteCutoffAtomicMeasure
  congr

/-! ## Elementary facts -/

/-- In parabolic space, a ball contained in another has no larger radius
(compare time coordinates). -/
theorem radius_le_of_ball_subset {n : ℕ} {z q : Space n} {r R : ℝ} (hr : 0 < r)
    (h : Metric.ball z r ⊆ Metric.ball q R) : r ≤ R := by
  rcases z with ⟨x, ⟨t⟩⟩
  rcases q with ⟨y, ⟨u⟩⟩
  change Metric.ball (point x t) r ⊆ Metric.ball (point y u) R at h
  by_contra hlt
  push Not at hlt
  have hR : 0 < R :=
    lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp (h (Metric.mem_ball_self hr)))
  set ρ := (R + r) / 2 with hρ
  have hρ0 : 0 < ρ := by linarith
  have hρR : R < ρ := by linarith
  have hρr : ρ < r := by linarith
  have hsq : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  obtain ⟨c, hc, hcu⟩ : ∃ c : ℝ, |c| = ρ ^ 2 ∧ ρ ^ 2 ≤ |t + c - u| := by
    rcases le_total u t with hut | hut
    · refine ⟨ρ ^ 2, abs_of_nonneg hsq, ?_⟩
      rw [abs_of_nonneg (by linarith)]
      linarith
    · refine ⟨-ρ ^ 2, by rw [abs_neg, abs_of_nonneg hsq], ?_⟩
      rw [abs_of_nonpos (by linarith)]
      linarith
  have hw : point x (t + c) ∈ Metric.ball (point x t) r := by
    rw [Metric.mem_ball, dist_point, sub_self, norm_zero, show t + c - t = c by ring, hc,
      Real.sqrt_sq hρ0.le, max_eq_right hρ0.le]
    exact hρr
  have hw' := Metric.mem_ball.mp (h hw)
  rw [dist_point] at hw'
  have hρle : ρ ≤ Real.sqrt |t + c - u| := by
    rw [← Real.sqrt_sq hρ0.le]
    exact Real.sqrt_le_sqrt hcu
  have := le_max_right ‖x - y‖ (Real.sqrt |t + c - u|)
  linarith

/-- The center of a ball disjoint from `P(x, r)` is outside `P(x, r)`. -/
theorem not_mem_ball_of_disjoint {n : ℕ} {x y : Space n} {r s : ℝ} (hs : 0 < s)
    (h : Disjoint (Metric.ball x r) (Metric.ball y s)) : y ∉ Metric.ball x r :=
  fun hy => Set.disjoint_left.mp h hy (Metric.mem_ball_self hs)

/-- A finite atomic measure vanishes on a set containing none of its atoms. -/
theorem finset_atomic_apply_eq_zero {n : ℕ} {ι : Type*} (t : Finset ι) (c : ι → ℝ≥0∞)
    (z : ι → Space n) {A : Set (Space n)} (h : ∀ j ∈ t, z j ∉ A) :
    (∑ j ∈ t, c j • Measure.dirac (z j)) A = 0 := by
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_notMem (h j hj), smul_eq_mul,
    mul_zero]

/-! ## The full atomic source -/

/-- The full atomic source `σ = ∑_j b_j r_j^k δ_{z_j}` of discrete packing. -/
def fullAtomicSource {n l : ℕ} (k : ℕ) (z : Fin l → Space n) (r w : Fin l → ℝ) :
    Measure (Space n) :=
  ∑ j, ENNReal.ofReal (w j * r j ^ k) • Measure.dirac (z j)

theorem isFiniteMeasure_fullAtomicSource {n l : ℕ} (k : ℕ) (z : Fin l → Space n)
    (r w : Fin l → ℝ) : IsFiniteMeasure (fullAtomicSource k z r w) := by
  constructor
  simp only [fullAtomicSource, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr (fun j _ => ENNReal.ofReal_lt_top)

theorem fullAtomicSource_eq_truncated_add {n l : ℕ} (k : ℕ) (z : Fin l → Space n)
    (r w : Fin l → ℝ) (s : ℝ) :
    fullAtomicSource k z r w = truncatedAtomicSource k z r w s +
      ∑ j ∈ Finset.univ.filter (fun j => ¬ r j ≤ s),
        ENNReal.ofReal (w j * r j ^ k) • Measure.dirac (z j) := by
  unfold fullAtomicSource truncatedAtomicSource
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

section AtomicEnergy

variable {n l k : ℕ} {T : FamilyKind} {z : Fin l → Space n} {r w : Fin l → ℝ}

/-- Below its own radius, a center sees only its own atom: zero beta. -/
theorem betaSq_fullAtomicSource_eq_zero (hT : Nonempty (Models n k T))
    (hr : ∀ i, 0 < r i)
    (hd : ∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j)))
    (i : Fin l) {s : ℝ} (hs : s ∈ Ioc 0 (r i)) :
    betaSq (fullAtomicSource k z r w) k T (z i) s = 0 := by
  obtain ⟨L, hL⟩ := exists_model_mem hT (z i)
  have hnull : fullAtomicSource k z r w (Metric.ball (z i) s \ {z i}) = 0 := by
    unfold fullAtomicSource
    refine finset_atomic_apply_eq_zero _ _ _ fun j _ hj => ?_
    by_cases hji : j = i
    · subst hji
      exact hj.2 rfl
    · exact not_mem_ball_of_disjoint (hr j) (hd i j (Ne.symm hji))
        (Metric.ball_subset_ball hs.2 hj.1)
  have hcost : modelCost L (z i) = 0 := by
    simp [modelCost, Metric.infEDist_zero_of_mem hL]
  have hfit : fit (fullAtomicSource k z r w) L (z i) s = 0 := by
    unfold fit
    refine le_antisymm ?_ zero_le
    calc ∫⁻ x in Metric.ball (z i) s, modelCost L x ∂fullAtomicSource k z r w
        ≤ ∫⁻ x in (Metric.ball (z i) s \ {z i}) ∪ {z i}, modelCost L x
            ∂fullAtomicSource k z r w := by
          apply lintegral_mono_set
          rw [Set.sdiff_union_self]
          exact subset_union_left
      _ ≤ (∫⁻ x in Metric.ball (z i) s \ {z i}, modelCost L x ∂fullAtomicSource k z r w) +
            ∫⁻ x in {z i}, modelCost L x ∂fullAtomicSource k z r w :=
          lintegral_union_le _ _ _
      _ = 0 := by
          rw [setLIntegral_measure_zero _ _ hnull, lintegral_singleton, hcost, zero_mul,
            add_zero]
  rw [betaSq_of_pos _ _ _ _ hs.1]
  refine le_antisymm ?_ zero_le
  calc (ENNReal.ofReal s)⁻¹ ^ (k + 2) *
        ⨅ L : Models n k T, fit (fullAtomicSource k z r w) L (z i) s
      ≤ (ENNReal.ofReal s)⁻¹ ^ (k + 2) * fit (fullAtomicSource k z r w) L (z i) s :=
        mul_le_mul_of_nonneg_left (iInf_le _ L) zero_le
    _ = 0 := by rw [hfit, mul_zero]

/-- Above its own radius, a center sees the full and truncated sources alike. -/
theorem betaSq_fullAtomicSource_eq_truncated (hr : ∀ i, 0 < r i)
    (hd : ∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j)))
    (i : Fin l) {s : ℝ} (hs : r i < s) :
    betaSq (fullAtomicSource k z r w) k T (z i) s =
      betaSq (truncatedAtomicSource k z r w s) k T (z i) s := by
  have hs0 : 0 < s := (hr i).trans hs
  have hnull : (∑ j ∈ Finset.univ.filter (fun j => ¬ r j ≤ s),
      ENNReal.ofReal (w j * r j ^ k) • Measure.dirac (z j)) (Metric.ball (z i) s) = 0 := by
    refine finset_atomic_apply_eq_zero _ _ _ fun j hj hzj => ?_
    have hjs : s < r j := not_le.mp (Finset.mem_filter.mp hj).2
    have hji : j ≠ i := by
      rintro rfl
      exact absurd hs.le (not_le.mpr hjs)
    have hout := not_mem_ball_of_disjoint (hr i) (hd j i hji)
    apply hout
    rw [Metric.mem_ball, dist_comm]
    exact (Metric.mem_ball.mp hzj).trans hjs
  rw [betaSq_of_pos _ _ _ _ hs0, betaSq_of_pos _ _ _ _ hs0]
  congr 1
  refine iInf_congr fun L => ?_
  unfold fit
  rw [fullAtomicSource_eq_truncated_add k z r w s, Measure.restrict_add,
    lintegral_add_measure, setLIntegral_measure_zero _ _ hnull, add_zero]

/-- The all-scale energy of the full source at a center is at most the truncated
tail energy above its radius. -/
theorem allScaleEnergy_fullAtomicSource_le (hT : Nonempty (Models n k T))
    (hr : ∀ i, 0 < r i)
    (hd : ∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j)))
    (i : Fin l) :
    allScaleEnergy (fullAtomicSource k z r w) k T (z i) ≤
      ∫⁻ s in Ioi (r i), betaSq (truncatedAtomicSource k z r w s) k T (z i) s
        ∂scaleMeasure := by
  unfold allScaleEnergy
  have hsub : Ioi (0 : ℝ) ⊆ Ioc 0 (r i) ∪ Ioi (r i) := by
    intro s hs
    rcases le_or_gt s (r i) with h | h
    · exact Or.inl ⟨hs, h⟩
    · exact Or.inr h
  calc ∫⁻ s in Ioi 0, betaSq (fullAtomicSource k z r w) k T (z i) s ∂scaleMeasure
      ≤ ∫⁻ s in Ioc 0 (r i) ∪ Ioi (r i), betaSq (fullAtomicSource k z r w) k T (z i) s
          ∂scaleMeasure := lintegral_mono_set hsub
    _ ≤ (∫⁻ s in Ioc 0 (r i), betaSq (fullAtomicSource k z r w) k T (z i) s ∂scaleMeasure) +
          ∫⁻ s in Ioi (r i), betaSq (fullAtomicSource k z r w) k T (z i) s ∂scaleMeasure :=
        lintegral_union_le _ _ _
    _ = ∫⁻ s in Ioi (r i), betaSq (truncatedAtomicSource k z r w s) k T (z i) s
          ∂scaleMeasure := by
        rw [setLIntegral_congr_fun measurableSet_Ioc
            (fun s hs => betaSq_fullAtomicSource_eq_zero hT hr hd i hs),
          setLIntegral_congr_fun measurableSet_Ioi
            (fun s hs => betaSq_fullAtomicSource_eq_truncated hr hd i hs),
          lintegral_zero, zero_add]

end AtomicEnergy

/-! ## Discrete packing from the countable decomposition -/

/-- **The countable decomposition implies discrete packing.**

The hypothesis is the statement `exists_countable_neck_decomposition`
with its per-vertex certificate predicate abstracted as `Cert`; instantiating
`Cert := IsCertifiedCore` gives that statement. The conclusion is the statement
`discrete_packing`. The certificate is not used. -/
theorem discrete_packing_of_decomposition (n : ℕ)
    (Cert : ℕ → NeckType → Space n → ℝ → ℝ → ℝ → ℝ → Measure (Space n) →
      Set (Space n) → Prop)
    (h4 : ∃ E C L : ℝ, 0 < E ∧ 0 < C ∧ 1 ≤ L ∧
      ∀ (k : ℕ) (F : FamilyKind), 1 ≤ k → k < n + 2 → Nonempty (Models n k F) →
      ∀ (q : Space n) (R B : ℝ) (ν : Measure (Space n)) (S : Set (Space n)),
        0 < R → 0 < B → IsFiniteMeasure ν → MeasurableSet S → S ⊆ Metric.ball q R →
        ν Sᶜ = 0 →
        (∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B) →
        ∃ D : NeckDecomposition ν k F S q R B E C,
          ∀ v ∈ D.vertices, Cert k (D.coreType v) (D.center v) (D.radius v)
            B B L (ν.restrict (D.source v)) (D.core v)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (T : FamilyKind), 1 ≤ k → k < n + 2 →
      Nonempty (Models n k T) →
      ∀ (q : Space n) (R b B : ℝ) (l : ℕ) (z : Fin l → Space n) (r w : Fin l → ℝ),
        0 < R → 0 < b → 0 ≤ B →
        (∀ i, 0 < r i ∧ Metric.ball (z i) (r i) ⊆ Metric.ball q R) →
        (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
        (∀ i, 0 < w i ∧ w i ≤ b) →
        (∀ i, ∫⁻ s in Ioi (r i), betaSq (truncatedAtomicSource k z r w s) k T (z i) s
            ∂scaleMeasure ≤ ENNReal.ofReal B) →
        ∑ i, ENNReal.ofReal (w i * r i ^ k) ≤ ENNReal.ofReal (C * (b + B) * R ^ k) := by
  obtain ⟨E, C, L, -, hC, -, h4⟩ := h4
  refine ⟨2 * C, by positivity, ?_⟩
  intro k T hk hkn hT q R b B l z r w hR hb hB hball hdisj hw hen
  have hrpos : ∀ i, 0 < r i := fun i => (hball i).1
  have hr_le : ∀ i, r i ≤ R := fun i => radius_le_of_ball_subset (hball i).1 (hball i).2
  have hfin := isFiniteMeasure_fullAtomicSource k z r w
  have hS : MeasurableSet (Set.range z) := (Set.finite_range z).measurableSet
  have hSball : Set.range z ⊆ Metric.ball q R := by
    rintro _ ⟨i, rfl⟩
    exact (hball i).2 (Metric.mem_ball_self (hball i).1)
  have hSc : fullAtomicSource k z r w (Set.range z)ᶜ = 0 := by
    unfold fullAtomicSource
    exact finset_atomic_apply_eq_zero _ _ _ fun j _ hj => hj ⟨j, rfl⟩
  have hEn : ∀ x ∈ Set.range z,
      allScaleEnergy (fullAtomicSource k z r w) k T x ≤ ENNReal.ofReal (B + b) := by
    rintro _ ⟨i, rfl⟩
    exact (allScaleEnergy_fullAtomicSource_le hT hrpos hdisj i).trans
      ((hen i).trans (ENNReal.ofReal_le_ofReal (by linarith)))
  obtain ⟨D, -⟩ := h4 k T hk hkn hT q R (B + b) (fullAtomicSource k z r w) (Set.range z)
    hR (by linarith) hfin hS hSball hSc hEn
  classical
  have hcompl : fullAtomicSource k z r w D.carrierᶜ =
      ∑ i, if z i ∈ D.carrier then 0 else ENNReal.ofReal (w i * r i ^ k) := by
    unfold fullAtomicSource
    rw [Measure.finsetSum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
    by_cases h : z i ∈ D.carrier <;> simp [h]
  have hpack : ∑ i, (if z i ∈ D.carrier then ENNReal.ofReal (r i) ^ k else 0) ≤
      ENNReal.ofReal (C * R ^ k) := by
    have hp := D.packing {i : Fin l // z i ∈ D.carrier} (fun i => z i.1) (fun i => r i.1)
      (fun i => i.2) (fun i => ⟨hrpos i.1, hr_le i.1⟩)
      (fun i j hij => hdisj i.1 j.1 (fun h => hij (Subtype.ext h)))
    rw [tsum_fintype] at hp
    have he : ∑ i, (if z i ∈ D.carrier then ENNReal.ofReal (r i) ^ k else 0) =
        ∑ i : {i : Fin l // z i ∈ D.carrier}, ENNReal.ofReal (r i) ^ k := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun x => by simp) _
    rw [he]
    exact hp
  have hterm : ∀ i, ENNReal.ofReal (w i * r i ^ k) ≤
      ENNReal.ofReal b * ENNReal.ofReal (r i) ^ k := by
    intro i
    rw [← ENNReal.ofReal_pow (hrpos i).le, ← ENNReal.ofReal_mul hb.le]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hw i).2 (pow_nonneg (hrpos i).le k))
  have hCR : 0 ≤ C * R ^ k := mul_nonneg hC.le (pow_nonneg hR.le k)
  calc ∑ i, ENNReal.ofReal (w i * r i ^ k)
      = ∑ i, (if z i ∈ D.carrier then ENNReal.ofReal (w i * r i ^ k) else 0) +
          ∑ i, (if z i ∈ D.carrier then 0 else ENNReal.ofReal (w i * r i ^ k)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : z i ∈ D.carrier <;> simp [h]
    _ ≤ ENNReal.ofReal b * ∑ i, (if z i ∈ D.carrier then ENNReal.ofReal (r i) ^ k else 0) +
          fullAtomicSource k z r w D.carrierᶜ := by
        rw [hcompl, Finset.mul_sum]
        refine add_le_add (Finset.sum_le_sum fun i _ => ?_) le_rfl
        by_cases h : z i ∈ D.carrier
        · simp only [h, ↓reduceIte]
          exact hterm i
        · simp [h]
    _ ≤ ENNReal.ofReal b * ENNReal.ofReal (C * R ^ k) +
          ENNReal.ofReal (C * (B + b) * R ^ k) :=
        add_le_add (mul_le_mul_of_nonneg_left hpack zero_le) D.measure_compl_carrier_le
    _ = ENNReal.ofReal (b * (C * R ^ k) + C * (B + b) * R ^ k) := by
        rw [ENNReal.ofReal_add (mul_nonneg hb.le hCR)
          (mul_nonneg (mul_nonneg hC.le (by linarith)) (pow_nonneg hR.le k)),
          ENNReal.ofReal_mul hb.le]
    _ ≤ ENNReal.ofReal (2 * C * (b + B) * R ^ k) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_nonneg hCR hB]

/-! ## Variable-radius packing from discrete packing -/

/-- **Discrete packing implies the variable-radius transfer.** The hypothesis is the
statement `discrete_packing`; the conclusion is the statement `variable_radius_packing`. -/
theorem variable_radius_packing_of_discrete (n : ℕ)
    (h5 : ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (T : FamilyKind), 1 ≤ k → k < n + 2 →
      Nonempty (Models n k T) →
      ∀ (q : Space n) (R b B : ℝ) (l : ℕ) (z : Fin l → Space n) (r w : Fin l → ℝ),
        0 < R → 0 < b → 0 ≤ B →
        (∀ i, 0 < r i ∧ Metric.ball (z i) (r i) ⊆ Metric.ball q R) →
        (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
        (∀ i, 0 < w i ∧ w i ≤ b) →
        (∀ i, ∫⁻ s in Ioi (r i), betaSq (truncatedAtomicSource k z r w s) k T (z i) s
            ∂scaleMeasure ≤ ENNReal.ofReal B) →
        ∑ i, ENNReal.ofReal (w i * r i ^ k) ≤ ENNReal.ofReal (C * (b + B) * R ^ k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (T : FamilyKind), 1 ≤ k → k < n + 2 →
      Nonempty (Models n k T) →
      ∀ (ν : Measure (Space n)) (L a : ℝ) (K : Set (Space n)), IsFiniteMeasure ν →
        0 ≤ L → 0 < a →
        (∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ ENNReal.ofReal L) →
        HasUniformLowerMass ν k a K →
        HasFiniteBallPacking k (C * (1 + L / a)) K := by
  obtain ⟨C5, hC5, h5⟩ := h5
  refine ⟨C5 * (2 ^ (n + 1) * 2 ^ (n + 1)) * (2 ^ (n + 3) * 50 ^ (n + 1)), by positivity, ?_⟩
  intro k T hk hkn hT ν L a K hfin hL ha hae hlow q R hR hR1 l z r hz hr hd
  -- Lower mass of each cell `closure P(z_i, r_i/100)`.
  have hcell_r : ∀ i, 0 < (1 / 100 : ℝ) * r i := fun i => by
    have := (hr i).1
    positivity
  have hcell_le : ∀ i, (1 / 100 : ℝ) * r i ≤ 1 := fun i => by
    have := (hr i).1
    have := (hr i).2
    linarith
  have hlow_i : ∀ i, ENNReal.ofReal (a * ((1 / 100 : ℝ) * r i) ^ k) ≤
      ν (Metric.closedBall (z i) ((1 / 100 : ℝ) * r i)) :=
    fun i => hlow (z i) (hz i).1 _ (hcell_r i) (hcell_le i)
  have hmass_pos : ∀ i, 0 < a * ((1 / 100 : ℝ) * r i) ^ k :=
    fun i => mul_pos ha (pow_pos (hcell_r i) k)
  have hmass_ne_zero : ∀ i, ν (Metric.closedBall (z i) ((1 / 100 : ℝ) * r i)) ≠ 0 :=
    fun i => (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (hmass_pos i)) (hlow_i i)).ne'
  -- Square-good samples in each cell.
  have hgood : ∀ i, ∃ y ∈ Metric.closedBall (z i) ((1 / 100 : ℝ) * r i),
      allScaleEnergy ν k T y ≤ ENNReal.ofReal L := by
    intro i
    by_contra hne
    push Not at hne
    apply hmass_ne_zero i
    exact measure_mono_null (fun y hy => not_le.mpr (hne y hy)) (ae_iff.mp hae)
  choose y hy hyL using hgood
  have hweight_le : ∀ i, (r i / 2) ^ k ≤ 50 ^ k / a *
      (ν (Metric.closedBall (z i) ((1 / 100 : ℝ) * r i))).toReal := by
    intro i
    have hm : a * ((1 / 100 : ℝ) * r i) ^ k ≤
        (ν (Metric.closedBall (z i) ((1 / 100 : ℝ) * r i))).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top ν _)).mp (hlow_i i)
    have heq : (r i / 2) ^ k = 50 ^ k / a * (a * ((1 / 100 : ℝ) * r i) ^ k) := by
      rw [← mul_assoc, div_mul_cancel₀ _ ha.ne', ← mul_pow]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hm (div_nonneg (pow_nonneg (by norm_num) k) ha.le)
  let D : FiniteBarycenterCells ν (Fin l) :=
    { cell := fun i => Metric.closedBall (z i) ((1 / 100 : ℝ) * r i)
      measurable_cell := fun i => Metric.isClosed_closedBall.measurableSet
      disjoint_cell := fun i j hij => (hd i j hij).mono
        (Metric.closedBall_subset_ball (by have := (hr i).1; linarith))
        (Metric.closedBall_subset_ball (by have := (hr j).1; linarith))
      mass_ne_zero := hmass_ne_zero
      mass_ne_top := fun i => measure_ne_top ν _
      center := z
      radius := r
      radius_pos := fun i => (hr i).1
      ε := 1 / 100
      ε_pos := by norm_num
      ε_le := by norm_num
      cell_subset := fun i => subset_rfl
      sample := y
      sample_mem := hy
      weight := fun i => (r i / 2) ^ k
      weight_pos := fun i => pow_pos (by have := (hr i).1; linarith) k
      A := 50 ^ k / a
      A_nonneg := div_nonneg (pow_nonneg (by norm_num) k) ha.le
      weight_le := hweight_le }
  -- Atomic balls lie inside the original balls.
  have hsub : ∀ i, Metric.ball (D.barycenter i) (D.cutoff i) ⊆ Metric.ball (z i) (r i) := by
    intro i x hx
    have hc : dist (D.barycenter i) (z i) ≤ (1 / 100 : ℝ) * r i :=
      Metric.mem_closedBall.mp (D.barycenter_mem_closedBall i)
    have hx' : dist x (D.barycenter i) < r i / 2 := Metric.mem_ball.mp hx
    have := (hr i).1
    rw [Metric.mem_ball]
    linarith [dist_triangle x (D.barycenter i) (z i)]
  have hball : ∀ i, 0 < D.cutoff i ∧
      Metric.ball (D.barycenter i) (D.cutoff i) ⊆ Metric.ball q (2 * R) := by
    intro i
    refine ⟨D.cutoff_pos i, (hsub i).trans fun x hx => ?_⟩
    have h1 := Metric.mem_ball.mp hx
    have h2 := Metric.mem_ball.mp (hz i).2
    have := (hr i).2
    rw [Metric.mem_ball]
    linarith [dist_triangle x (z i) q]
  have hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (D.barycenter i) (D.cutoff i))
      (Metric.ball (D.barycenter j) (D.cutoff j)) :=
    fun i j hij => (hd i j hij).mono (hsub i) (hsub j)
  -- The atomic energy bound from the barycenter transfer.
  obtain ⟨B', hB'⟩ : ∃ B' : ℝ, B' = 50 ^ k / a * 2 ^ (k + 2) * L := ⟨_, rfl⟩
  have h50a : 0 ≤ (50 : ℝ) ^ k / a := div_nonneg (pow_nonneg (by norm_num) k) ha.le
  have h2p : 0 ≤ (2 : ℝ) ^ (k + 2) := pow_nonneg (by norm_num) _
  have h2k0 : 0 ≤ (2 : ℝ) ^ k := pow_nonneg (by norm_num) _
  have h20 : (0 : ℝ) ≤ 2 := by norm_num
  have hB'0 : 0 ≤ B' := by rw [hB']; exact mul_nonneg (mul_nonneg h50a h2p) hL
  have hsrc : ∀ s, truncatedAtomicSource k D.barycenter D.cutoff (fun _ => (1 : ℝ)) s =
      D.atomicMeasure s := by
    intro s
    rw [truncatedAtomicSource_eq_finiteCutoffAtomicMeasure]
    unfold FiniteBarycenterCells.atomicMeasure
    congr 1
    funext j
    exact one_mul _
  have hen : ∀ i, ∫⁻ s in Ioi (D.cutoff i),
      betaSq (truncatedAtomicSource k D.barycenter D.cutoff (fun _ => (1 : ℝ)) s) k T
        (D.barycenter i) s ∂scaleMeasure ≤ ENNReal.ofReal B' := by
    intro i
    have heq : (∫⁻ s in Ioi (D.cutoff i),
        betaSq (truncatedAtomicSource k D.barycenter D.cutoff (fun _ => (1 : ℝ)) s) k T
          (D.barycenter i) s ∂scaleMeasure) = D.atomicEnergy i k T := by
      unfold FiniteBarycenterCells.atomicEnergy
      congr 1
      funext s
      rw [hsrc s]
    rw [heq]
    refine (D.atomicEnergy_le_of_source_bound i k T (hyL i)).trans (le_of_eq ?_)
    show ENNReal.ofReal (50 ^ k / a) * 2 ^ (k + 2) * ENNReal.ofReal L = ENNReal.ofReal B'
    rw [hB', ENNReal.ofReal_mul (mul_nonneg h50a h2p), ENNReal.ofReal_mul h50a,
      ENNReal.ofReal_pow h20, ENNReal.ofReal_ofNat]
  have h5res := h5 k T hk hkn hT q (2 * R) 1 B' l D.barycenter D.cutoff (fun _ => 1)
    (by positivity) one_pos hB'0 hball hdisj (fun _ => ⟨one_pos, le_rfl⟩) hen
  -- Return to the original radii.
  have hterm : ∀ i, ENNReal.ofReal (r i) ^ k =
      2 ^ k * ENNReal.ofReal (1 * D.cutoff i ^ k) := by
    intro i
    have h2 : ENNReal.ofReal (r i) ^ k = ENNReal.ofReal (2 ^ k * (1 * D.cutoff i ^ k)) := by
      rw [← ENNReal.ofReal_pow (hr i).1.le, one_mul, ← mul_pow]
      show ENNReal.ofReal (r i ^ k) = ENNReal.ofReal ((2 * (r i / 2)) ^ k)
      rw [show 2 * (r i / 2) = r i by ring]
    rw [h2, ENNReal.ofReal_mul h2k0, ENNReal.ofReal_pow h20, ENNReal.ofReal_ofNat]
  have hk1 : k ≤ n + 1 := by omega
  have h2k : (2 : ℝ) ^ k ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) hk1
  have h2k2 : (2 : ℝ) ^ (k + 2) ≤ 2 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h50 : (50 : ℝ) ^ k ≤ 50 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) hk1
  have hY1 : (1 : ℝ) ≤ 2 ^ (n + 3) * 50 ^ (n + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hYk : (2 : ℝ) ^ (k + 2) * 50 ^ k ≤ 2 ^ (n + 3) * 50 ^ (n + 1) :=
    mul_le_mul h2k2 h50 (pow_nonneg (by norm_num) k) (pow_nonneg (by norm_num) _)
  have hX : 0 ≤ L / a := div_nonneg hL ha.le
  have hinner : 1 + (2 ^ (k + 2) * 50 ^ k) * (L / a) ≤
      (2 ^ (n + 3) * 50 ^ (n + 1)) * (1 + L / a) := by
    calc 1 + (2 ^ (k + 2) * 50 ^ k) * (L / a)
        ≤ (2 ^ (n + 3) * 50 ^ (n + 1)) + (2 ^ (n + 3) * 50 ^ (n + 1)) * (L / a) :=
          add_le_add hY1 (mul_le_mul_of_nonneg_right hYk hX)
      _ = _ := by ring
  have hpow : (2 : ℝ) ^ k * 2 ^ k ≤ 2 ^ (n + 1) * 2 ^ (n + 1) :=
    mul_le_mul h2k h2k (pow_nonneg (by norm_num) k) (pow_nonneg (by norm_num) _)
  have hreal : 2 ^ k * (C5 * (1 + B') * (2 * R) ^ k) ≤
      C5 * (2 ^ (n + 1) * 2 ^ (n + 1)) * (2 ^ (n + 3) * 50 ^ (n + 1)) * (1 + L / a) *
        R ^ k := by
    have hCR : 0 ≤ C5 * R ^ k := mul_nonneg hC5.le (pow_nonneg hR.le k)
    calc 2 ^ k * (C5 * (1 + B') * (2 * R) ^ k)
        = (C5 * R ^ k) * ((2 ^ k * 2 ^ k) * (1 + (2 ^ (k + 2) * 50 ^ k) * (L / a))) := by
          rw [hB', mul_pow]
          ring
      _ ≤ (C5 * R ^ k) * ((2 ^ (n + 1) * 2 ^ (n + 1)) *
            ((2 ^ (n + 3) * 50 ^ (n + 1)) * (1 + L / a))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hpow hinner (by positivity) (by positivity)) hCR
      _ = _ := by ring
  calc ∑ i, ENNReal.ofReal (r i) ^ k
      = ∑ i, 2 ^ k * ENNReal.ofReal (1 * D.cutoff i ^ k) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = 2 ^ k * ∑ i, ENNReal.ofReal (1 * D.cutoff i ^ k) := by rw [Finset.mul_sum]
    _ ≤ 2 ^ k * ENNReal.ofReal (C5 * (1 + B') * (2 * R) ^ k) :=
        mul_le_mul_of_nonneg_left h5res zero_le
    _ = ENNReal.ofReal (2 ^ k * (C5 * (1 + B') * (2 * R) ^ k)) := by
        rw [ENNReal.ofReal_mul h2k0, ENNReal.ofReal_pow h20, ENNReal.ofReal_ofNat]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end ParabolicRectifiability
