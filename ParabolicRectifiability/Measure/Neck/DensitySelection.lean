import ParabolicRectifiability.Measure.Neck.Definitions
import ParabolicRectifiability.Measure.AtomicBarycenterTransfer

/-!
# Density selection from discrete packing

The endpoint `density_selection_of_discrete` proves the statement `density_selection`
from the statement `discrete_packing`.

Route:

* compactness of the carrier `K_a` (closedness through continuity from above);
* `ae_largeDimension` by a volume-counting argument;
* the first doubling scale, the deficient balls and a Vitali selection;
* the transfer of disjoint source cells to cutoff barycenter atoms (see `AtomicBarycenterTransfer`) and
  discrete packing, giving the loss `C(a + L)` (`ν(X \ K_a) ≤ C(a + L)`);
* the same transfer with cell radius `r/20`, giving the local separated-set bound with
  factor `C(1 + L/a)`, and from it the local Hausdorff and neighbourhood bounds;
* the one-sided Hausdorff domination `H^k ⌞ K_a ≤ (C/a) ν` (`restrict_hausdorffP_densityCarrier_le`),
  by a Vitali selection and outer regularity of the finite source.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

/-! ## The discrete packing conclusion for a fixed constant -/

/-- The conclusion of `discrete_packing` for one fixed constant `C`. -/
def DiscretePackingBound (n : ℕ) (C : ℝ) : Prop :=
  ∀ (k : ℕ) (T : FamilyKind), 1 ≤ k → k < n + 2 →
    Nonempty (Models n k T) →
    ∀ (q : Space n) (R b B : ℝ) (l : ℕ) (z : Fin l → Space n) (r w : Fin l → ℝ),
      0 < R → 0 < b → 0 ≤ B →
      (∀ i, 0 < r i ∧ Metric.ball (z i) (r i) ⊆ Metric.ball q R) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∀ i, 0 < w i ∧ w i ≤ b) →
      (∀ i, ∫⁻ s in Ioi (r i), betaSq (truncatedAtomicSource k z r w s) k T (z i) s
          ∂scaleMeasure ≤ ENNReal.ofReal B) →
      ∑ i, ENNReal.ofReal (w i * r i ^ k) ≤ ENNReal.ofReal (C * (b + B) * R ^ k)

/-! ## Elementary helpers -/

theorem exists_mem_of_ae_of_measure_ne_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) {s : Set α} (hs : μ s ≠ 0) : ∃ x ∈ s, p x := by
  by_contra hcon
  push Not at hcon
  exact hs (measure_mono_null (fun x hx => hcon x hx) (ae_iff.mp h))

theorem ofReal_sum_const_fin (l : ℕ) (x : ℝ) :
    ∑ _i : Fin l, ENNReal.ofReal x = ENNReal.ofReal ((l : ℝ) * x) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg l), ENNReal.ofReal_natCast]

/-- The scale-truncated source of discrete packing is the cutoff atomic source with weights
`w_j r_j^k` (a decidability-instance bridge). -/
theorem truncatedAtomicSource_eq_finiteCutoffAtomicMeasure {n l : ℕ} (k : ℕ)
    (z : Fin l → Space n) (r w : Fin l → ℝ) (s : ℝ) :
    truncatedAtomicSource k z r w s =
      finiteCutoffAtomicMeasure z r (fun j => w j * r j ^ k) s := by
  unfold truncatedAtomicSource finiteCutoffAtomicMeasure
  congr

/-- `ρ`-separated finite sets. -/
def IsSeparatedFinset {n : ℕ} (ρ : ℝ) (F : Finset (Space n)) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ρ ≤ dist x y

/-- A maximal finite separated subset exists once separated subsets have bounded size;
it is a `ρ`-net of the set (with open balls). -/
theorem exists_maximal_separated_finset {n : ℕ} (S : Set (Space n)) {ρ : ℝ} (hρ : 0 < ρ)
    (N0 : ℕ) (hbound : ∀ F : Finset (Space n), ↑F ⊆ S → IsSeparatedFinset ρ F → F.card ≤ N0) :
    ∃ F : Finset (Space n), ↑F ⊆ S ∧ IsSeparatedFinset ρ F ∧ ∀ x ∈ S, ∃ y ∈ F, dist x y < ρ := by
  classical
  let P : ℕ → Prop := fun m =>
    ∃ F : Finset (Space n), ↑F ⊆ S ∧ IsSeparatedFinset ρ F ∧ F.card = m
  have hP0 : P 0 := ⟨∅, by simp, fun x hx => by simp at hx, rfl⟩
  obtain ⟨F, hFS, hFsep, hFcard⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le N0) hP0
  refine ⟨F, hFS, hFsep, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have hxF : x ∉ F := by
    intro h
    have h' := hcon x h
    rw [dist_self] at h'
    linarith
  have hsep' : IsSeparatedFinset ρ (insert x F) := by
    intro y hy w hw hyw
    rw [Finset.mem_insert] at hy hw
    rcases hy with hy | hy <;> rcases hw with hw | hw
    · exact absurd (hy.trans hw.symm) hyw
    · rw [hy]; exact hcon w hw
    · rw [hw, dist_comm]; exact hcon y hy
    · exact hFsep y hy w hw hyw
  have hS' : (↑(insert x F) : Set (Space n)) ⊆ S := by
    rw [Finset.coe_insert]
    exact insert_subset hx hFS
  have hle := hbound _ hS' hsep'
  have hP' : P (F.card + 1) := ⟨insert x F, hS', hsep', Finset.card_insert_of_notMem hxF⟩
  rw [Finset.card_insert_of_notMem hxF] at hle
  have := Nat.le_findGreatest hle hP'
  omega

/-! ## Compactness of the density carrier -/

theorem isOpen_setOf_measure_closedBall_lt {n : ℕ} (ν : Measure (Space n)) [IsFiniteMeasure ν]
    (r : ℝ) (x : ℝ≥0∞) : IsOpen {z : Space n | ν (Metric.closedBall z r) < x} := by
  rw [Metric.isOpen_iff]
  intro z hz
  have hz' : ν (Metric.closedBall z r) < x := hz
  have hinter : (⋂ ε > r, Metric.closedBall z ε) = Metric.closedBall z r := by
    ext w
    simp only [mem_iInter, Metric.mem_closedBall]
    constructor
    · intro h
      exact le_of_forall_gt_imp_ge_of_dense fun ε hε => h ε hε
    · intro h ε hε
      exact h.trans hε.le
  rw [← hinter] at hz'
  have htend := tendsto_measure_biInter_gt (μ := ν) (s := fun ε => Metric.closedBall z ε)
    (a := r) (fun ε _ => measurableSet_closedBall.nullMeasurableSet)
    (fun i j _ hij => Metric.closedBall_subset_closedBall hij)
    ⟨r + 1, by linarith, measure_ne_top _ _⟩
  have hev : ∀ᶠ ε in 𝓝[>] r, ν (Metric.closedBall z ε) < x :=
    htend.eventually (p := fun y => y < x) (Iio_mem_nhds hz')
  obtain ⟨ε, hε', hεr'⟩ := (hev.and (self_mem_nhdsWithin : Ioi r ∈ 𝓝[>] r)).exists
  have hεr : r < ε := hεr'
  refine ⟨ε - r, sub_pos.mpr hεr, fun w hw => ?_⟩
  have hw' : dist w z < ε - r := hw
  show ν (Metric.closedBall w r) < x
  exact (measure_mono (Metric.closedBall_subset_closedBall' (by linarith))).trans_lt hε'

theorem isClosed_densityCarrier {n : ℕ} (ν : Measure (Space n)) [IsFiniteMeasure ν]
    (k : ℕ) (a : ℝ) : IsClosed (densityCarrier ν k a) := by
  have heq : densityCarrier ν k a = ν.support ∩ ⋂ (r : ℝ) (_ : 0 < r) (_ : r ≤ 1),
      {z | ENNReal.ofReal (a * r ^ k) ≤ ν (Metric.closedBall z r)} := by
    ext z
    simp only [densityCarrier, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [heq]
  refine Measure.isClosed_support.inter
    (isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_)
  have h := (isOpen_setOf_measure_closedBall_lt ν r (ENNReal.ofReal (a * r ^ k))).isClosed_compl
  simpa only [compl_ofPred, not_lt] using h

/-- `K_a` is compact (including the radius `1`). -/
theorem isCompact_densityCarrier {n : ℕ} (ν : Measure (Space n)) [IsFiniteMeasure ν]
    (k : ℕ) (a : ℝ) {c : Space n} {ρ : ℝ} (hsupp : ν.support ⊆ Metric.closedBall c ρ) :
    IsCompact (densityCarrier ν k a) :=
  (isCompact_closedBall c ρ).of_isClosed_subset (isClosed_densityCarrier ν k a)
    fun _ hz => hsupp hz.1

/-! ## Volume counting -/

/-- A `ρ`-separated subset of a closed ball of radius `R` has at most
`((2R + ρ)/ρ)^(n+2)` points (ambient volume of disjoint balls). -/
theorem card_le_of_separated_subset_closedBall {n : ℕ} (c : Space n) {R ρ : ℝ} (hR : 0 ≤ R)
    (hρ : 0 < ρ) (F : Finset (Space n)) (hF : ↑F ⊆ Metric.closedBall c R)
    (hsep : IsSeparatedFinset ρ F) :
    (F.card : ℝ) ≤ ((2 * R + ρ) / ρ) ^ (n + 2) := by
  have hρ2 : 0 < ρ / 2 := half_pos hρ
  have hdisj : (F : Set (Space n)).PairwiseDisjoint (fun x => Metric.ball x (ρ / 2)) := by
    intro x hx y hy hxy
    exact Metric.ball_disjoint_ball (by linarith [hsep x hx y hy hxy])
  have hsub : (⋃ x ∈ F, Metric.ball x (ρ / 2)) ⊆ Metric.ball c (R + ρ / 2) := by
    intro w hw
    obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.mp hw
    have h1 : dist x c ≤ R := hF hx
    have h2 : dist w x < ρ / 2 := hwx
    rw [Metric.mem_ball]
    linarith [dist_triangle w x c]
  have hvol := measure_biUnion_finset (μ := parabolicVolume n) hdisj
    (fun x _ => measurableSet_ball)
  have hle : ∑ x ∈ F, parabolicVolume n (Metric.ball x (ρ / 2)) ≤
      parabolicVolume n (Metric.ball c (R + ρ / 2)) := by
    rw [← hvol]
    exact measure_mono hsub
  simp only [parabolicVolume_ball _ _ hρ2, Finset.sum_const, nsmul_eq_mul,
    parabolicVolume_ball _ _ (by linarith : (0 : ℝ) < R + ρ / 2)] at hle
  have hfin : 2 * omega n * ENNReal.ofReal (R + ρ / 2) ^ (n + 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (omega_lt_top n).ne)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have h3 := ENNReal.toReal_mono hfin hle
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ2.le,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ R + ρ / 2), ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat] at h3
  have hω : 0 < (omega n).toReal := ENNReal.toReal_pos (omega_pos n).ne' (omega_lt_top n).ne
  have hx : 0 < (ρ / 2) ^ (n + 2) := pow_pos hρ2 _
  have h4 : (2 * (omega n).toReal) * ((F.card : ℝ) * (ρ / 2) ^ (n + 2)) ≤
      (2 * (omega n).toReal) * (R + ρ / 2) ^ (n + 2) := by
    calc (2 * (omega n).toReal) * ((F.card : ℝ) * (ρ / 2) ^ (n + 2))
        = (F.card : ℝ) * (2 * (omega n).toReal * (ρ / 2) ^ (n + 2)) := by ring
      _ ≤ _ := h3
  have h5 := le_of_mul_le_mul_left h4 (mul_pos two_pos hω)
  have he : (2 * R + ρ) / ρ = (R + ρ / 2) / (ρ / 2) := by
    rw [div_eq_div_iff hρ.ne' hρ2.ne']
    ring
  rw [he, div_pow, le_div_iff₀ hx]
  exact h5

/-! ## Large dimension almost everywhere -/

/-- The property `limsup_{r↓0} ν(P(z,r))/r^(n+3) = ∞`, in quantified form. -/
def HasLargeDimension {n : ℕ} (ν : Measure (Space n)) (z : Space n) : Prop :=
  ∀ m N : ℕ, ∃ r : ℝ, 0 < r ∧ r ≤ 1 / ((N : ℝ) + 1) ∧
    ENNReal.ofReal ((m : ℝ) * r ^ (n + 3)) < ν (Metric.ball z r)

/-- Almost every point has large dimension. -/
theorem ae_largeDimension {n : ℕ} (ν : Measure (Space n)) [IsFiniteMeasure ν] (c : Space n)
    (hsupp : ν.support ⊆ Metric.closedBall c 1) : ∀ᵐ z ∂ν, HasLargeDimension ν z := by
  unfold HasLargeDimension
  rw [ae_all_iff]
  intro m
  rw [ae_all_iff]
  intro N
  set E : Set (Space n) := {z : Space n | ∀ r : ℝ, 0 < r → r ≤ 1 / ((N : ℝ) + 1) →
      ν (Metric.ball z r) ≤ ENNReal.ofReal ((m : ℝ) * r ^ (n + 3))} with hEdef
  have hS : ν (E ∩ Metric.closedBall c 1) = 0 := by
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
    rw [zero_add]
    have hεr : (0 : ℝ) < ε := hε
    have h3 : (0 : ℝ) < 3 ^ (n + 2) := by positivity
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    set δ : ℝ := (ε : ℝ) / (3 ^ (n + 2) * ((m : ℝ) + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    set ρ : ℝ := min (1 / ((N : ℝ) + 1)) δ with hρ
    have hρpos : 0 < ρ := lt_min (by positivity) hδpos
    have hρN : ρ ≤ 1 / ((N : ℝ) + 1) := min_le_left _ _
    have hρδ : ρ ≤ δ := min_le_right _ _
    have hρ1 : ρ ≤ 1 := hρN.trans (by
      rw [div_le_one (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
    have hcardb : ∀ F : Finset (Space n), ↑F ⊆ Metric.closedBall c 1 →
        IsSeparatedFinset ρ F → (F.card : ℝ) ≤ (3 / ρ) ^ (n + 2) := by
      intro F hF hsep
      calc (F.card : ℝ) ≤ ((2 * 1 + ρ) / ρ) ^ (n + 2) :=
            card_le_of_separated_subset_closedBall c zero_le_one hρpos F hF hsep
        _ ≤ (3 / ρ) ^ (n + 2) := by gcongr; linarith
    have hsub1 : E ∩ Metric.closedBall c 1 ⊆ Metric.closedBall c 1 := inter_subset_right
    obtain ⟨F, hFS, hFsep, hFcov⟩ := exists_maximal_separated_finset
      (E ∩ Metric.closedBall c 1) hρpos ⌊(3 / ρ) ^ (n + 2)⌋₊
      (fun F hF hsep => Nat.le_floor (hcardb F (hF.trans hsub1) hsep))
    have hcard : (F.card : ℝ) ≤ (3 / ρ) ^ (n + 2) := hcardb F (hFS.trans hsub1) hFsep
    have hreal : (F.card : ℝ) * ((m : ℝ) * ρ ^ (n + 3)) ≤ ε := by
      calc (F.card : ℝ) * ((m : ℝ) * ρ ^ (n + 3))
          ≤ (3 / ρ) ^ (n + 2) * ((m : ℝ) * ρ ^ (n + 3)) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 3 ^ (n + 2) * m * ρ * (ρ ^ (n + 2) / ρ ^ (n + 2)) := by ring
        _ = 3 ^ (n + 2) * m * ρ := by rw [div_self (pow_ne_zero _ hρpos.ne'), mul_one]
        _ ≤ 3 ^ (n + 2) * m * δ := by gcongr
        _ ≤ ε := by
          rw [hδ, mul_div_assoc',
            div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ (n + 2) * ((m : ℝ) + 1))]
          have := mul_pos h3 hεr
          nlinarith
    have hmemE : ∀ x ∈ F, ν (Metric.ball x ρ) ≤ ENNReal.ofReal ((m : ℝ) * ρ ^ (n + 3)) := by
      intro x hx
      have hxE : x ∈ E := (hFS hx).1
      rw [hEdef] at hxE
      exact hxE ρ hρpos hρN
    calc ν (E ∩ Metric.closedBall c 1)
        ≤ ν (⋃ x ∈ F, Metric.ball x ρ) := by
          apply measure_mono
          intro z hz
          obtain ⟨y, hy, hzy⟩ := hFcov z hz
          exact mem_iUnion₂.mpr ⟨y, hy, hzy⟩
      _ ≤ ∑ x ∈ F, ν (Metric.ball x ρ) := measure_biUnion_finset_le F _
      _ ≤ ∑ _x ∈ F, ENNReal.ofReal ((m : ℝ) * ρ ^ (n + 3)) := Finset.sum_le_sum hmemE
      _ = ENNReal.ofReal ((F.card : ℝ) * ((m : ℝ) * ρ ^ (n + 3))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg F.card),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hreal
      _ = ε := ENNReal.ofReal_coe_nnreal
  have hnull : ν E = 0 := by
    apply measure_mono_null _ (measure_union_null hS
      (measure_mono_null (compl_subset_compl.mpr hsupp) Measure.measure_compl_support))
    intro z hz
    by_cases hzc : z ∈ Metric.closedBall c 1
    · exact Or.inl ⟨hz, hzc⟩
    · exact Or.inr hzc
  rw [measure_eq_zero_iff_ae_notMem] at hnull
  filter_upwards [hnull] with z hz
  by_contra hcon
  push Not at hcon
  apply hz
  rw [hEdef]
  exact hcon

/-! ## The first doubling scale -/

theorem exists_doubling_scale {n : ℕ} (ν : Measure (Space n)) [IsFiniteMeasure ν]
    {z : Space n} (hz : HasLargeDimension ν z) {R : ℝ} (hR : 0 < R) :
    ∃ j : ℕ, ν (Metric.ball z (R / 50 ^ j)) ≤
        ENNReal.ofReal (50 ^ (n + 3)) * ν (Metric.ball z (R / 50 ^ (j + 1))) ∧
      ∀ i < j, ENNReal.ofReal (50 ^ (n + 3)) * ν (Metric.ball z (R / 50 ^ (i + 1))) <
        ν (Metric.ball z (R / 50 ^ i)) := by
  classical
  have hex : ∃ j : ℕ, ν (Metric.ball z (R / 50 ^ j)) ≤
      ENNReal.ofReal (50 ^ (n + 3)) * ν (Metric.ball z (R / 50 ^ (j + 1))) := by
    by_contra hcon
    push Not at hcon
    have hf : ∀ j : ℕ, (50 : ℝ) ^ (n + 3) * (ν (Metric.ball z (R / 50 ^ (j + 1)))).toReal <
        (ν (Metric.ball z (R / 50 ^ j))).toReal := by
      intro j
      have h := ENNReal.toReal_strict_mono (measure_ne_top ν _) (hcon j)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 50 ^ (n + 3))] at h
    have hfpow : ∀ j : ℕ, ((50 : ℝ) ^ (n + 3)) ^ j *
        (ν (Metric.ball z (R / 50 ^ j))).toReal ≤ (ν (Metric.ball z (R / 50 ^ 0))).toReal := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc ((50 : ℝ) ^ (n + 3)) ^ (j + 1) * (ν (Metric.ball z (R / 50 ^ (j + 1)))).toReal
            = ((50 : ℝ) ^ (n + 3)) ^ j *
                ((50 : ℝ) ^ (n + 3) * (ν (Metric.ball z (R / 50 ^ (j + 1)))).toReal) := by
              ring
          _ ≤ ((50 : ℝ) ^ (n + 3)) ^ j * (ν (Metric.ball z (R / 50 ^ j))).toReal :=
              mul_le_mul_of_nonneg_left (hf j).le (by positivity)
          _ ≤ _ := ih
    have hf0 : (ν (Metric.ball z (R / 50 ^ 0))).toReal ≤ (ν univ).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
    have hM0 : 0 ≤ (ν univ).toReal := ENNReal.toReal_nonneg
    obtain ⟨m, hm⟩ := exists_nat_gt ((ν univ).toReal * 50 ^ (n + 3) / R ^ (n + 3))
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / R)
    obtain ⟨r, hr, hrN, hmr⟩ := hz m N
    have hrR : r ≤ R := by
      refine hrN.trans (le_of_lt ?_)
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      rw [div_lt_iff₀ hR] at hN
      nlinarith
    have hRr : 1 ≤ R / r := (one_le_div hr).mpr hrR
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hRr (by norm_num : (1 : ℝ) < 50)
    have hrj : r ≤ R / 50 ^ j := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 50 ^ j)]
      rw [le_div_iff₀ hr] at hj1
      linarith
    have h1 : (ν (Metric.ball z r)).toReal ≤ (ν (Metric.ball z (R / 50 ^ j))).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Metric.ball_subset_ball hrj))
    have h2 : (m : ℝ) * r ^ (n + 3) < (ν (Metric.ball z r)).toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (measure_ne_top _ _)).mp hmr
    have h4 : R / (50 * r) < 50 ^ j := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 50 * r)]
      rw [div_lt_iff₀ hr, pow_succ] at hj2
      linarith
    have h5 : (R / (50 * r)) ^ (n + 3) * (ν (Metric.ball z (R / 50 ^ j))).toReal ≤
        (ν univ).toReal := by
      calc (R / (50 * r)) ^ (n + 3) * (ν (Metric.ball z (R / 50 ^ j))).toReal
          ≤ ((50 : ℝ) ^ (n + 3)) ^ j * (ν (Metric.ball z (R / 50 ^ j))).toReal := by
            apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
            rw [← pow_mul, mul_comm (n + 3) j, pow_mul]
            exact pow_le_pow_left₀ (by positivity) h4.le _
        _ ≤ _ := (hfpow j).trans hf0
    have h6 : (R / (50 * r)) ^ (n + 3) * ((m : ℝ) * r ^ (n + 3)) < (ν univ).toReal :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_left (h2.trans_le h1) (by positivity)) h5
    have h7 : (R / (50 * r)) ^ (n + 3) * ((m : ℝ) * r ^ (n + 3)) = m * (R / 50) ^ (n + 3) := by
      calc (R / (50 * r)) ^ (n + 3) * ((m : ℝ) * r ^ (n + 3))
          = m * ((R / 50) ^ (n + 3) / r ^ (n + 3) * r ^ (n + 3)) := by
            rw [← div_div, div_pow]
            ring
        _ = m * (R / 50) ^ (n + 3) := by rw [div_mul_cancel₀ _ (pow_ne_zero _ hr.ne')]
    rw [h7, div_pow, ← mul_div_assoc,
      div_lt_iff₀ (by positivity : (0 : ℝ) < 50 ^ (n + 3))] at h6
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < R ^ (n + 3))] at hm
    linarith
  exact ⟨Nat.find hex, Nat.find_spec hex, fun i hi => not_le.mp (Nat.find_min hex hi)⟩

/-! ## Deficient balls -/

/-- At a support point outside `K_a` with large dimension there is a radius `r ≤ 1/5`
with `0 < ν(P(z,r/10))`, `ν(P(z,5r)) ≤ D ν(P(z,r/10))` and `ν(P(z,r/10)) < a(5r)^k`
where `D = 50^(n+3)`. -/
theorem exists_deficient_radius {n : ℕ} (ν : Measure (Space n)) [IsFiniteMeasure ν]
    {k : ℕ} (hk : k ≤ n + 3) {a : ℝ} (_ha : 0 < a) {z : Space n} (hzs : z ∈ ν.support)
    (hzK : z ∉ densityCarrier ν k a) (hz : HasLargeDimension ν z) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 5 ∧
      ν (Metric.ball z (5 * r)) ≤ ENNReal.ofReal (50 ^ (n + 3)) * ν (Metric.ball z (r / 10)) ∧
      ν (Metric.ball z (r / 10)) < ENNReal.ofReal (a * (5 * r) ^ k) ∧
      0 < ν (Metric.ball z (r / 10)) := by
  have hdef : ∃ R : ℝ, 0 < R ∧ R ≤ 1 ∧ ν (Metric.closedBall z R) < ENNReal.ofReal (a * R ^ k) := by
    by_contra hcon
    push Not at hcon
    exact hzK ⟨hzs, fun r hr hr1 => hcon r hr hr1⟩
  obtain ⟨R, hR, hR1, hRlt⟩ := hdef
  obtain ⟨j, hdj, hlt⟩ := exists_doubling_scale ν hz hR
  have hfm : ∀ i < j, (50 : ℝ) ^ (n + 3) * (ν (Metric.ball z (R / 50 ^ (i + 1)))).toReal <
      (ν (Metric.ball z (R / 50 ^ i))).toReal := by
    intro i hi
    have h := ENNReal.toReal_strict_mono (measure_ne_top _ _) (hlt i hi)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 50 ^ (n + 3))] at h
  have hpow : ∀ i, i ≤ j → ((50 : ℝ) ^ (n + 3)) ^ i * (ν (Metric.ball z (R / 50 ^ i))).toReal ≤
      (ν (Metric.ball z (R / 50 ^ 0))).toReal := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      calc ((50 : ℝ) ^ (n + 3)) ^ (i + 1) * (ν (Metric.ball z (R / 50 ^ (i + 1)))).toReal
          = ((50 : ℝ) ^ (n + 3)) ^ i *
              ((50 : ℝ) ^ (n + 3) * (ν (Metric.ball z (R / 50 ^ (i + 1)))).toReal) := by ring
        _ ≤ ((50 : ℝ) ^ (n + 3)) ^ i * (ν (Metric.ball z (R / 50 ^ i))).toReal :=
            mul_le_mul_of_nonneg_left (hfm i (by omega)).le (by positivity)
        _ ≤ _ := ih (by omega)
  have hB0 : (ν (Metric.ball z (R / 50 ^ 0))).toReal < a * R ^ k := by
    rw [pow_zero, div_one]
    exact lt_of_le_of_lt (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono Metric.ball_subset_closedBall))
      ((ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).mp hRlt)
  have hj : (ν (Metric.ball z (R / 50 ^ j))).toReal < a * (R / 50 ^ j) ^ k := by
    have h1 := (hpow j le_rfl).trans_lt hB0
    have h2 : ((50 : ℝ) ^ j) ^ k ≤ ((50 : ℝ) ^ (n + 3)) ^ j := by
      rw [← pow_mul, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by rw [mul_comm (n + 3)]; exact Nat.mul_le_mul_left j hk)
    have hpos : 0 < ((50 : ℝ) ^ j) ^ k := by positivity
    rw [div_pow, ← mul_div_assoc, lt_div_iff₀ hpos]
    calc (ν (Metric.ball z (R / 50 ^ j))).toReal * ((50 : ℝ) ^ j) ^ k
        ≤ (ν (Metric.ball z (R / 50 ^ j))).toReal * ((50 : ℝ) ^ (n + 3)) ^ j :=
          mul_le_mul_of_nonneg_left h2 ENNReal.toReal_nonneg
      _ = ((50 : ℝ) ^ (n + 3)) ^ j * (ν (Metric.ball z (R / 50 ^ j))).toReal := mul_comm _ _
      _ < a * R ^ k := h1
  set r := R / 50 ^ j / 5 with hr
  have h5r : 5 * r = R / 50 ^ j := by rw [hr]; ring
  have h10 : r / 10 = R / 50 ^ (j + 1) := by rw [hr, pow_succ]; ring
  have hrpos : 0 < r := by positivity
  refine ⟨r, hrpos, ?_, ?_, ?_, ?_⟩
  · rw [hr, div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 5)]
    exact (div_le_self hR.le (one_le_pow₀ (by norm_num))).trans hR1
  · rw [h5r, h10]
    exact hdj
  · rw [h10, h5r]
    calc ν (Metric.ball z (R / 50 ^ (j + 1))) ≤ ν (Metric.ball z (R / 50 ^ j)) :=
          measure_mono (Metric.ball_subset_ball (div_le_div_of_nonneg_left hR.le
            (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_succ j))))
      _ < ENNReal.ofReal (a * (R / 50 ^ j) ^ k) :=
          (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).mpr hj
  · exact (Measure.mem_support_iff_forall z).mp hzs _ (Metric.ball_mem_nhds z (by positivity))

/-! ## The atomic transfer to discrete packing -/

/-- Disjoint source cells with barycenter atoms of radius `cutoff` give the discrete packing
bound for their weights. The energy bound is the atomic transfer `A·2^(k+2)·L`. -/
theorem sum_weight_le_of_barycenterCells {n : ℕ} {C5 : ℝ} (hdisc : DiscretePackingBound n C5)
    {k : ℕ} {T : FamilyKind} (hk : 1 ≤ k) (hkn : k < n + 2) (hT : Nonempty (Models n k T))
    {ν : Measure (Space n)} {l : ℕ} (D : FiniteBarycenterCells ν (Fin l)) {L : ℝ} (hL : 0 ≤ L)
    (hsample : ∀ i, allScaleEnergy ν k T (D.sample i) ≤ ENNReal.ofReal L)
    (q : Space n) {R b : ℝ} (hR : 0 < R) (hb : 0 < b)
    (hball : ∀ i, Metric.ball (D.barycenter i) (D.cutoff i) ⊆ Metric.ball q R)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (D.barycenter i) (D.cutoff i))
      (Metric.ball (D.barycenter j) (D.cutoff j)))
    (hw : ∀ i, D.weight i ≤ b * D.cutoff i ^ k) :
    ∑ i, ENNReal.ofReal (D.weight i) ≤
      ENNReal.ofReal (C5 * (b + D.A * 2 ^ (k + 2) * L) * R ^ k) := by
  have hcut : ∀ i, 0 < D.cutoff i ^ k := fun i => pow_pos (D.cutoff_pos i) k
  have hcancel : ∀ i, D.weight i / D.cutoff i ^ k * D.cutoff i ^ k = D.weight i :=
    fun i => div_mul_cancel₀ _ (hcut i).ne'
  have h2pow : (0 : ℝ) ≤ 2 ^ (k + 2) := by positivity
  have hA2 : 0 ≤ D.A * 2 ^ (k + 2) := mul_nonneg D.A_nonneg h2pow
  have hB : 0 ≤ D.A * 2 ^ (k + 2) * L := mul_nonneg hA2 hL
  have hsrc : ∀ s, truncatedAtomicSource k D.barycenter D.cutoff
      (fun j => D.weight j / D.cutoff j ^ k) s = D.atomicMeasure s := by
    intro s
    rw [truncatedAtomicSource_eq_finiteCutoffAtomicMeasure]
    simp only [hcancel]
    rfl
  have henergy : ∀ i, ∫⁻ s in Ioi (D.cutoff i), betaSq (truncatedAtomicSource k D.barycenter
      D.cutoff (fun j => D.weight j / D.cutoff j ^ k) s) k T (D.barycenter i) s ∂scaleMeasure ≤
      ENNReal.ofReal (D.A * 2 ^ (k + 2) * L) := by
    intro i
    have := hT
    have h1 : (∫⁻ s in Ioi (D.cutoff i), betaSq (truncatedAtomicSource k D.barycenter
        D.cutoff (fun j => D.weight j / D.cutoff j ^ k) s) k T (D.barycenter i) s
        ∂scaleMeasure) = D.atomicEnergy i k T := by
      simp only [hsrc]
      rfl
    rw [h1]
    calc D.atomicEnergy i k T ≤ ENNReal.ofReal D.A * 2 ^ (k + 2) * ENNReal.ofReal L :=
          D.atomicEnergy_le_of_source_bound i k T (hsample i)
      _ = ENNReal.ofReal (D.A * 2 ^ (k + 2) * L) := by
          rw [ENNReal.ofReal_mul hA2, ENNReal.ofReal_mul D.A_nonneg,
            ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have key := hdisc k T hk hkn hT q R b (D.A * 2 ^ (k + 2) * L) l D.barycenter D.cutoff
    (fun j => D.weight j / D.cutoff j ^ k) hR hb hB (fun i => ⟨D.cutoff_pos i, hball i⟩) hdisj
    (fun i => ⟨div_pos (D.weight_pos i) (hcut i), (div_le_iff₀ (hcut i)).mpr (hw i)⟩) henergy
  simpa only [hcancel] using key

/-! ## The density loss -/

/-- The finite-subfamily bound for deficient cells: `∑ m_i ≤ C₅ (10^k a + 2^(k+2) L)`. -/
theorem sum_deficient_cells_le {n : ℕ} {C5 : ℝ} (hdisc : DiscretePackingBound n C5)
    {k : ℕ} {T : FamilyKind} (hk : 1 ≤ k) (hkn : k < n + 2) (hT : Nonempty (Models n k T))
    (ν : Measure (Space n)) [IsFiniteMeasure ν] (c : Space n) {L a : ℝ} (hL : 0 ≤ L)
    (ha : 0 < a) (henergy : ∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ ENNReal.ofReal L)
    {l : ℕ} (g : Fin l → Space n) (ρ : Fin l → ℝ) (hρ : ∀ i, 0 < ρ i) (hρ5 : ∀ i, ρ i ≤ 1 / 5)
    (hg : ∀ i, g i ∈ Metric.closedBall c (1 / 16))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (g i) (ρ i)) (Metric.ball (g j) (ρ j)))
    (hpos : ∀ i, 0 < ν (Metric.ball (g i) (ρ i / 10)))
    (hsmall : ∀ i, ν (Metric.ball (g i) (ρ i / 10)) < ENNReal.ofReal (a * (5 * ρ i) ^ k)) :
    ∑ i, ν (Metric.ball (g i) (ρ i / 10)) ≤
      ENNReal.ofReal (C5 * (10 ^ k * a + 1 * 2 ^ (k + 2) * L) * 1 ^ k) := by
  have hsample : ∀ i, ∃ y ∈ Metric.ball (g i) (ρ i / 10), allScaleEnergy ν k T y ≤
      ENNReal.ofReal L := fun i => exists_mem_of_ae_of_measure_ne_zero henergy (hpos i).ne'
  choose y hy hyE using hsample
  have hdisjc : Pairwise fun i j => Disjoint (Metric.ball (g i) (ρ i / 10))
      (Metric.ball (g j) (ρ j / 10)) := fun i j hij =>
    (hdisj i j hij).mono (Metric.ball_subset_ball (by linarith [hρ i]))
      (Metric.ball_subset_ball (by linarith [hρ j]))
  obtain ⟨D, hDcenter, hDradius, hDε, hDsample, hDweight, hDA⟩ :
      ∃ D : FiniteBarycenterCells ν (Fin l), (∀ i, D.center i = g i) ∧
        (∀ i, D.radius i = ρ i) ∧ D.ε = 1 / 10 ∧ (∀ i, D.sample i = y i) ∧
        (∀ i, D.weight i = (ν (Metric.ball (g i) (ρ i / 10))).toReal) ∧ D.A = 1 :=
    ⟨{ cell := fun i => Metric.ball (g i) (ρ i / 10)
       measurable_cell := fun _ => measurableSet_ball
       disjoint_cell := hdisjc
       mass_ne_zero := fun i => (hpos i).ne'
       mass_ne_top := fun _ => measure_ne_top _ _
       center := g
       radius := ρ
       radius_pos := hρ
       ε := 1 / 10
       ε_pos := by norm_num
       ε_le := le_rfl
       cell_subset := fun i => Metric.ball_subset_closedBall.trans
         (Metric.closedBall_subset_closedBall (le_of_eq (by ring)))
       sample := y
       sample_mem := hy
       weight := fun i => (ν (Metric.ball (g i) (ρ i / 10))).toReal
       weight_pos := fun i => ENNReal.toReal_pos (hpos i).ne' (measure_ne_top _ _)
       A := 1
       A_nonneg := zero_le_one
       weight_le := fun i => by rw [one_mul] },
      fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  have hbary : ∀ i, dist (D.barycenter i) (g i) ≤ ρ i / 10 := by
    intro i
    have h := D.barycenter_mem_closedBall i
    rw [hDcenter, hDradius, hDε, Metric.mem_closedBall] at h
    linarith
  have hcut : ∀ i, D.cutoff i = ρ i / 2 := by
    intro i
    show D.radius i / 2 = ρ i / 2
    rw [hDradius]
  have hsub : ∀ i, Metric.ball (D.barycenter i) (D.cutoff i) ⊆ Metric.ball (g i) (ρ i) := by
    intro i w hw
    rw [hcut] at hw
    have h1 : dist w (D.barycenter i) < ρ i / 2 := hw
    rw [Metric.mem_ball]
    linarith [dist_triangle w (D.barycenter i) (g i), hbary i, hρ i]
  have hball : ∀ i, Metric.ball (D.barycenter i) (D.cutoff i) ⊆ Metric.ball c 1 := by
    intro i w hw
    have h1 : dist w (g i) < ρ i := hsub i hw
    have h2 : dist (g i) c ≤ 1 / 16 := hg i
    rw [Metric.mem_ball]
    linarith [dist_triangle w (g i) c, hρ5 i]
  have hdisjb : ∀ i j, i ≠ j → Disjoint (Metric.ball (D.barycenter i) (D.cutoff i))
      (Metric.ball (D.barycenter j) (D.cutoff j)) := fun i j hij =>
    (hdisj i j hij).mono (hsub i) (hsub j)
  have hw : ∀ i, D.weight i ≤ 10 ^ k * a * D.cutoff i ^ k := by
    intro i
    rw [hDweight, hcut]
    have h1 := (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).mp (hsmall i)
    have h2 : a * (5 * ρ i) ^ k = 10 ^ k * a * (ρ i / 2) ^ k := by
      rw [show (5 : ℝ) * ρ i = 10 * (ρ i / 2) by ring, mul_pow]
      ring
    linarith
  have hsampleE : ∀ i, allScaleEnergy ν k T (D.sample i) ≤ ENNReal.ofReal L := by
    intro i
    rw [hDsample]
    exact hyE i
  have key := sum_weight_le_of_barycenterCells hdisc hk hkn hT D hL hsampleE c one_pos
    (by positivity) hball hdisjb hw
  simp only [hDweight, hDA, ENNReal.ofReal_toReal (measure_ne_top ν _)] at key
  exact key

/-- Density loss: `ν(X \ K_a) ≤ C(a + L)`. -/
theorem measure_compl_densityCarrier_le {n : ℕ} {C5 : ℝ} (hdisc : DiscretePackingBound n C5)
    (hC5 : 0 < C5) {k : ℕ} {T : FamilyKind} (hk : 1 ≤ k) (hkn : k < n + 2)
    (hT : Nonempty (Models n k T)) (ν : Measure (Space n)) [IsFiniteMeasure ν] (c : Space n)
    (hsupp : ν.support ⊆ Metric.closedBall c (1 / 16)) {L a : ℝ} (hL : 0 ≤ L) (ha : 0 < a)
    (henergy : ∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ ENNReal.ofReal L) :
    ν (densityCarrier ν k a)ᶜ ≤
      ENNReal.ofReal (50 ^ (n + 3) * C5 * (10 ^ (n + 2) + 2 ^ (n + 3)) * (a + L)) := by
  classical
  have hLD : ∀ᵐ z ∂ν, HasLargeDimension ν z := ae_largeDimension ν c
    (hsupp.trans (Metric.closedBall_subset_closedBall (by norm_num)))
  obtain ⟨G, hG⟩ : ∃ G : Set (Space n), G = {z | z ∈ ν.support ∧
      z ∉ densityCarrier ν k a ∧ HasLargeDimension ν z} := ⟨_, rfl⟩
  have hmemG : ∀ z, z ∈ G ↔ z ∈ ν.support ∧ z ∉ densityCarrier ν k a ∧ HasLargeDimension ν z := by
    intro z
    rw [hG]
    rfl
  have hrad : ∀ z : G, ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 5 ∧
      ν (Metric.ball (z : Space n) (5 * r)) ≤
        ENNReal.ofReal (50 ^ (n + 3)) * ν (Metric.ball (z : Space n) (r / 10)) ∧
      ν (Metric.ball (z : Space n) (r / 10)) < ENNReal.ofReal (a * (5 * r) ^ k) ∧
      0 < ν (Metric.ball (z : Space n) (r / 10)) := by
    intro z
    have hz := (hmemG z).mp z.2
    exact exists_deficient_radius ν (by omega) ha hz.1 hz.2.1 hz.2.2
  choose rad hrad0 hrad1 hdoub hsmall hpos using hrad
  obtain ⟨u, -, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun z : G => Metric.ball (z : Space n) (rad z)) univ rad 2 one_lt_two
    (fun z _ => (hrad0 z).le) (1 / 5) (fun z _ => hrad1 z)
    (fun z _ => ⟨z, Metric.mem_ball_self (hrad0 z)⟩)
  have hucount : u.Countable := hudisj.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
    (fun z _ => ⟨z, Metric.mem_ball_self (hrad0 z)⟩)
  -- finite subfamilies
  have hfin : ∀ s : Finset u, ∑ p ∈ s, ν (Metric.ball ((p : G) : Space n) (rad p / 10)) ≤
      ENNReal.ofReal (C5 * (10 ^ k * a + 1 * 2 ^ (k + 2) * L) * 1 ^ k) := by
    intro s
    obtain ⟨e, -⟩ : ∃ e : Fin s.card ≃ s, True := ⟨s.equivFin.symm, trivial⟩
    have hinj : ∀ i j, i ≠ j → ((e i : u) : G) ≠ ((e j : u) : G) := by
      intro i j hij h
      exact hij (e.injective (Subtype.ext (Subtype.ext h)))
    have hsum := sum_deficient_cells_le hdisc hk hkn hT ν c hL ha henergy
      (fun i => (((e i : u) : G) : Space n)) (fun i => rad ((e i : u) : G))
      (fun i => hrad0 _) (fun i => hrad1 _)
      (fun i => hsupp ((hmemG _).mp ((e i : u) : G).2).1)
      (fun i j hij => hudisj (e i : u).2 (e j : u).2 (hinj i j hij))
      (fun i => hpos _) (fun i => hsmall _)
    rw [← Finset.sum_coe_sort s, ← Equiv.sum_comp e]
    exact hsum
  have htsum : ∑' p : u, ν (Metric.ball ((p : G) : Space n) (rad p / 10)) ≤
      ENNReal.ofReal (C5 * (10 ^ k * a + 1 * 2 ^ (k + 2) * L) * 1 ^ k) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le hfin
  -- the cover
  have hcover : (densityCarrier ν k a)ᶜ ⊆ (ν.supportᶜ ∪ {z | ¬ HasLargeDimension ν z}) ∪
      ⋃ p ∈ u, Metric.ball ((p : G) : Space n) (5 * rad p) := by
    intro z hz
    by_cases hzs : z ∈ ν.support
    swap
    · exact Or.inl (Or.inl hzs)
    by_cases hzl : HasLargeDimension ν z
    swap
    · exact Or.inl (Or.inr hzl)
    right
    have hzG : z ∈ G := (hmemG z).mpr ⟨hzs, hz, hzl⟩
    obtain ⟨b, hbu, ⟨w, hw1, hw2⟩, hrb⟩ := hucov ⟨z, hzG⟩ (mem_univ _)
    refine mem_iUnion₂.mpr ⟨b, hbu, ?_⟩
    have h1 : dist w z < rad ⟨z, hzG⟩ := hw1
    have h2 : dist w ((b : G) : Space n) < rad b := hw2
    rw [Metric.mem_ball]
    linarith [dist_triangle z w ((b : G) : Space n), dist_comm w z, hrad0 b]
  have hbad : ν {z | ¬ HasLargeDimension ν z} = 0 := ae_iff.mp hLD
  have harith : 50 ^ (n + 3) * (C5 * (10 ^ k * a + 1 * 2 ^ (k + 2) * L) * 1 ^ k) ≤
      50 ^ (n + 3) * C5 * (10 ^ (n + 2) + 2 ^ (n + 3)) * (a + L) := by
    have h10 : (10 : ℝ) ^ k ≤ 10 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (k + 2) ≤ 2 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hinner : 10 ^ k * a + 1 * 2 ^ (k + 2) * L ≤ (10 ^ (n + 2) + 2 ^ (n + 3)) * (a + L) := by
      have h10' : (0 : ℝ) ≤ 10 ^ (n + 2) := by positivity
      have h2' : (0 : ℝ) ≤ 2 ^ (n + 3) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h10 ha.le, mul_le_mul_of_nonneg_right h2 hL,
        mul_nonneg h10' hL, mul_nonneg h2' ha.le]
    rw [one_pow, mul_one]
    calc 50 ^ (n + 3) * (C5 * (10 ^ k * a + 1 * 2 ^ (k + 2) * L))
        ≤ 50 ^ (n + 3) * (C5 * ((10 ^ (n + 2) + 2 ^ (n + 3)) * (a + L))) := by gcongr
      _ = _ := by ring
  calc ν (densityCarrier ν k a)ᶜ
      ≤ ν ((ν.supportᶜ ∪ {z | ¬ HasLargeDimension ν z}) ∪
          ⋃ p ∈ u, Metric.ball ((p : G) : Space n) (5 * rad p)) := measure_mono hcover
    _ ≤ ν (ν.supportᶜ ∪ {z | ¬ HasLargeDimension ν z}) +
          ν (⋃ p ∈ u, Metric.ball ((p : G) : Space n) (5 * rad p)) := measure_union_le _ _
    _ = ν (⋃ p ∈ u, Metric.ball ((p : G) : Space n) (5 * rad p)) := by
        rw [measure_union_null Measure.measure_compl_support hbad, zero_add]
    _ ≤ ∑' p : u, ν (Metric.ball ((p : G) : Space n) (5 * rad p)) :=
        measure_biUnion_le ν hucount _
    _ ≤ ∑' p : u, ENNReal.ofReal (50 ^ (n + 3)) *
          ν (Metric.ball ((p : G) : Space n) (rad p / 10)) :=
        ENNReal.tsum_le_tsum fun p => hdoub p
    _ = ENNReal.ofReal (50 ^ (n + 3)) *
          ∑' p : u, ν (Metric.ball ((p : G) : Space n) (rad p / 10)) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (50 ^ (n + 3)) *
          ENNReal.ofReal (C5 * (10 ^ k * a + 1 * 2 ^ (k + 2) * L) * 1 ^ k) :=
        mul_le_mul_right htsum _
    _ = ENNReal.ofReal (50 ^ (n + 3) * (C5 * (10 ^ k * a + 1 * 2 ^ (k + 2) * L) * 1 ^ k)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal harith

/-! ## Separated subsets of the carrier -/

theorem localNet_arith {n k : ℕ} (hk : k ≤ n + 2) {C5 a L R r N : ℝ} (hC5 : 0 < C5)
    (ha : 0 < a) (hL : 0 ≤ L) (hr : 0 < r) (hR : 0 < R)
    (hN : N * (5 * (r / 20)) ^ k ≤ C5 * (1 + 5 ^ k / a * 2 ^ (k + 2) * L) * (3 * R) ^ k) :
    N ≤ 4 * C5 * 120 ^ (n + 2) * (1 + L / a) * (R / r) ^ k := by
  have h5 : 5 * (r / 20) = r / 4 := by ring
  rw [h5] at hN
  have hpos : 0 < (r / 4) ^ k := by positivity
  have hN' : N ≤ C5 * (1 + 5 ^ k / a * 2 ^ (k + 2) * L) * (3 * R) ^ k / (r / 4) ^ k :=
    (le_div_iff₀ hpos).mpr hN
  have e1 : 3 * R / (r / 4) = 12 * (R / r) := by
    rw [div_eq_iff (by positivity), show 12 * (R / r) * (r / 4) = 3 * R * (r / r) by ring,
      div_self hr.ne', mul_one]
  have hX : 1 + 5 ^ k / a * 2 ^ (k + 2) * L ≤ 5 ^ k * 2 ^ (k + 2) * (1 + L / a) := by
    have h1 : (1 : ℝ) ≤ 5 ^ k * 2 ^ (k + 2) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
    have h2 : 0 ≤ L / a := div_nonneg hL ha.le
    have e : (5 : ℝ) ^ k / a * 2 ^ (k + 2) * L = 5 ^ k * 2 ^ (k + 2) * (L / a) := by ring
    rw [e, mul_add, mul_one]
    nlinarith
  have h120 : (120 : ℝ) ^ k ≤ 120 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) hk
  calc N ≤ C5 * (1 + 5 ^ k / a * 2 ^ (k + 2) * L) * (3 * R) ^ k / (r / 4) ^ k := hN'
    _ = C5 * (1 + 5 ^ k / a * 2 ^ (k + 2) * L) * (3 * R / (r / 4)) ^ k := by
        rw [div_pow (3 * R) (r / 4) k, mul_div_assoc]
    _ = C5 * (1 + 5 ^ k / a * 2 ^ (k + 2) * L) * 12 ^ k * (R / r) ^ k := by
        rw [e1, mul_pow]; ring
    _ ≤ C5 * (5 ^ k * 2 ^ (k + 2) * (1 + L / a)) * 12 ^ k * (R / r) ^ k := by gcongr
    _ = 4 * C5 * ((5 * 2 * 12) ^ k) * (1 + L / a) * (R / r) ^ k := by
        rw [mul_pow, mul_pow, pow_add]; ring
    _ = 4 * C5 * 120 ^ k * (1 + L / a) * (R / r) ^ k := by norm_num
    _ ≤ 4 * C5 * 120 ^ (n + 2) * (1 + L / a) * (R / r) ^ k := by
        have hLa : 0 ≤ 1 + L / a := by positivity
        have hRr : 0 ≤ (R / r) ^ k := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h120 (by positivity)) hLa) hRr

/-- A finite `r`-separated subset of `K_a ∩ P(q,R)` has at most `C(1 + L/a)(R/r)^k` points. -/
theorem card_le_of_separated_densityCarrier {n : ℕ} {C5 : ℝ} (hdisc : DiscretePackingBound n C5)
    (hC5 : 0 < C5) {k : ℕ} {T : FamilyKind} (hk : 1 ≤ k) (hkn : k < n + 2)
    (hT : Nonempty (Models n k T)) (ν : Measure (Space n)) [IsFiniteMeasure ν] {L a : ℝ}
    (hL : 0 ≤ L) (ha : 0 < a) (henergy : ∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ ENNReal.ofReal L)
    (q : Space n) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hR1 : R ≤ 1) (F : Finset (Space n))
    (hF : ↑F ⊆ densityCarrier ν k a ∩ Metric.ball q R) (hsep : IsSeparatedFinset r F) :
    (F.card : ℝ) ≤ 4 * C5 * 120 ^ (n + 2) * (1 + L / a) * (R / r) ^ k := by
  classical
  have hR : 0 < R := hr.trans_le hrR
  obtain ⟨zz, hzz_inj, hzzF⟩ : ∃ zz : Fin F.card → Space n, Function.Injective zz ∧
      ∀ i, zz i ∈ F :=
    ⟨fun i => (F.equivFin.symm i : Space n),
      fun i j h => F.equivFin.symm.injective (Subtype.ext h), fun i => (F.equivFin.symm i).2⟩
  set ρ := r / 20 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρdef]; linarith
  have hzzK : ∀ i, zz i ∈ densityCarrier ν k a := fun i => (hF (hzzF i)).1
  have hzzq : ∀ i, zz i ∈ Metric.ball q R := fun i => (hF (hzzF i)).2
  have hsepz : ∀ i j, i ≠ j → r ≤ dist (zz i) (zz j) :=
    fun i j hij => hsep _ (hzzF i) _ (hzzF j) (hzz_inj.ne hij)
  have hmass : ∀ i, ENNReal.ofReal (a * ρ ^ k) ≤ ν (Metric.closedBall (zz i) ρ) :=
    fun i => (hzzK i).2 ρ hρ hρ1
  have hne0 : ∀ i, ν (Metric.closedBall (zz i) ρ) ≠ 0 := fun i =>
    (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) (hmass i)).ne'
  have htoReal : ∀ i, a * ρ ^ k ≤ (ν (Metric.closedBall (zz i) ρ)).toReal := fun i =>
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp (hmass i)
  have hsample : ∀ i, ∃ y ∈ Metric.closedBall (zz i) ρ, allScaleEnergy ν k T y ≤
      ENNReal.ofReal L := fun i => exists_mem_of_ae_of_measure_ne_zero henergy (hne0 i)
  choose y hy hyE using hsample
  obtain ⟨D, hDcenter, hDradius, hDε, hDsample, hDweight, hDA⟩ :
      ∃ D : FiniteBarycenterCells ν (Fin F.card), (∀ i, D.center i = zz i) ∧
        (∀ i, D.radius i = 10 * ρ) ∧ D.ε = 1 / 10 ∧ (∀ i, D.sample i = y i) ∧
        (∀ i, D.weight i = (5 * ρ) ^ k) ∧ D.A = 5 ^ k / a :=
    ⟨{ cell := fun i => Metric.closedBall (zz i) ρ
       measurable_cell := fun _ => measurableSet_closedBall
       disjoint_cell := fun i j hij => Metric.closedBall_disjoint_closedBall (by
         have := hsepz i j hij
         rw [hρdef]
         linarith)
       mass_ne_zero := hne0
       mass_ne_top := fun _ => measure_ne_top _ _
       center := zz
       radius := fun _ => 10 * ρ
       radius_pos := fun _ => by positivity
       ε := 1 / 10
       ε_pos := by norm_num
       ε_le := le_rfl
       cell_subset := fun _ => Metric.closedBall_subset_closedBall (le_of_eq (by ring))
       sample := y
       sample_mem := hy
       weight := fun _ => (5 * ρ) ^ k
       weight_pos := fun _ => by positivity
       A := 5 ^ k / a
       A_nonneg := by positivity
       weight_le := fun i => by
         calc (5 * ρ) ^ k = 5 ^ k / a * (a * ρ ^ k) := by
               rw [div_mul_eq_mul_div, eq_div_iff ha.ne', mul_pow]
               ring
           _ ≤ 5 ^ k / a * (ν (Metric.closedBall (zz i) ρ)).toReal :=
               mul_le_mul_of_nonneg_left (htoReal i) (by positivity) },
      fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  have hbary : ∀ i, dist (D.barycenter i) (zz i) ≤ ρ := by
    intro i
    have h := D.barycenter_mem_closedBall i
    rw [hDcenter, hDradius, hDε, Metric.mem_closedBall] at h
    linarith
  have hcut : ∀ i, D.cutoff i = 5 * ρ := by
    intro i
    show D.radius i / 2 = 5 * ρ
    rw [hDradius]
    ring
  have hball : ∀ i, Metric.ball (D.barycenter i) (D.cutoff i) ⊆ Metric.ball q (3 * R) := by
    intro i w hw
    rw [hcut] at hw
    have h0 : dist w (D.barycenter i) < 5 * ρ := hw
    have h1 := hbary i
    have h2 : dist (zz i) q < R := hzzq i
    rw [Metric.mem_ball]
    have := dist_triangle4 w (D.barycenter i) (zz i) q
    rw [hρdef] at h0 h1
    linarith
  have hdisjb : ∀ i j, i ≠ j → Disjoint (Metric.ball (D.barycenter i) (D.cutoff i))
      (Metric.ball (D.barycenter j) (D.cutoff j)) := by
    intro i j hij
    rw [hcut, hcut]
    apply Metric.ball_disjoint_ball
    have h1 := hbary i
    have h2 := hbary j
    have h3 := hsepz i j hij
    have h4 := dist_triangle4 (zz i) (D.barycenter i) (D.barycenter j) (zz j)
    rw [dist_comm (zz i) (D.barycenter i)] at h4
    rw [hρdef] at h1 h2 ⊢
    linarith
  have hw : ∀ i, D.weight i ≤ 1 * D.cutoff i ^ k := by
    intro i
    rw [hDweight, hcut, one_mul]
  have hsampleE : ∀ i, allScaleEnergy ν k T (D.sample i) ≤ ENNReal.ofReal L := by
    intro i
    rw [hDsample]
    exact hyE i
  have key := sum_weight_le_of_barycenterCells hdisc hk hkn hT D hL hsampleE q
    (by positivity : (0 : ℝ) < 3 * R) one_pos hball hdisjb hw
  simp only [hDweight, hDA] at key
  rw [ofReal_sum_const_fin, ENNReal.ofReal_le_ofReal_iff (by positivity :
    (0 : ℝ) ≤ C5 * (1 + 5 ^ k / a * 2 ^ (k + 2) * L) * (3 * R) ^ k)] at key
  exact localNet_arith (by omega) hC5 ha hL hr hR key

/-! ## Local Hausdorff and neighbourhood bounds from nets -/

/-- Covers by `F_ρ` open balls of radius `ρ`, with `#F_ρ ≤ A (R/ρ)^k` at every scale,
give `H^k_P(S) ≤ A 2^k R^k`. -/
theorem hausdorffP_le_of_nets {n : ℕ} (k : ℕ) (S : Set (Space n)) {A R : ℝ} (_hA : 0 ≤ A)
    (hR : 0 < R) (hnet : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R → ∃ F : Finset (Space n),
      (F.card : ℝ) ≤ A * (R / ρ) ^ k ∧ S ⊆ ⋃ x ∈ F, Metric.ball x ρ) :
    hausdorffP n k S ≤ ENNReal.ofReal (A * 2 ^ k * R ^ k) := by
  obtain ⟨ρf, hρf⟩ : ∃ ρf : ℕ → ℝ, ρf = fun m : ℕ => R / ((m : ℝ) + 1) := ⟨_, rfl⟩
  have hρ : ∀ m, 0 < ρf m := fun m => by rw [hρf]; positivity
  have hρR : ∀ m, ρf m ≤ R := fun m => by
    rw [hρf]
    exact div_le_self hR.le (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  choose F hFcard hFcov using fun m : ℕ => hnet (ρf m) (hρ m) (hρR m)
  have h1 : Tendsto (fun m : ℕ => 2 * ρf m) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * R)
    rw [mul_zero] at this
    refine this.congr fun m => ?_
    simp only [hρf]
    ring
  have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal (2 * ρf m)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal h1
  have ht : ∀ m (x : F m), Metric.ediam (Metric.ball (x : Space n) (ρf m)) ≤
      ENNReal.ofReal (2 * ρf m) := by
    intro m x
    apply Metric.ediam_le
    intro y hy w hw
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have h1 : dist y x < ρf m := hy
    have h2 : dist w x < ρf m := hw
    linarith [dist_triangle_right y w x]
  have hst : ∀ m, S ⊆ ⋃ x : F m, Metric.ball (x : Space n) (ρf m) := by
    intro m y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hFcov m hy)
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hyx⟩
  have key := Measure.hausdorffMeasure_le_liminf_sum (k : ℝ) S _ hlim
    (fun m (x : F m) => Metric.ball (x : Space n) (ρf m))
    (Eventually.of_forall ht) (Eventually.of_forall hst)
  unfold hausdorffP
  refine key.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun m => ?_))
  have hreal : ((F m).card : ℝ) * (2 * ρf m) ^ k ≤ A * 2 ^ k * R ^ k := by
    have e : R / ρf m * (2 * ρf m) = 2 * R := by
      calc R / ρf m * (2 * ρf m) = 2 * R * (ρf m / ρf m) := by ring
        _ = 2 * R := by rw [div_self (hρ m).ne', mul_one]
    calc ((F m).card : ℝ) * (2 * ρf m) ^ k ≤ A * (R / ρf m) ^ k * (2 * ρf m) ^ k :=
          mul_le_mul_of_nonneg_right (hFcard m) (pow_nonneg (mul_nonneg zero_le_two (hρ m).le) k)
      _ = A * (R / ρf m * (2 * ρf m)) ^ k := by rw [mul_pow]; ring
      _ = A * 2 ^ k * R ^ k := by rw [e, mul_pow]; ring
  calc ∑ x : F m, Metric.ediam (Metric.ball (x : Space n) (ρf m)) ^ (k : ℝ)
      ≤ ∑ _x : F m, ENNReal.ofReal (2 * ρf m) ^ (k : ℝ) :=
        Finset.sum_le_sum fun x _ => ENNReal.rpow_le_rpow (ht m x) (Nat.cast_nonneg k)
    _ = ((F m).card : ℝ≥0∞) * ENNReal.ofReal ((2 * ρf m) ^ k) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
          ENNReal.rpow_natCast, ENNReal.ofReal_pow (mul_nonneg zero_le_two (hρ m).le) k]
    _ = ENNReal.ofReal (((F m).card : ℝ) * (2 * ρf m) ^ k) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg (F m).card), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (A * 2 ^ k * R ^ k) := ENNReal.ofReal_le_ofReal hreal

/-- A finite net of `K` at scale `r` controls the ambient volume of the open
`r`-neighbourhood of `K`. -/
theorem parabolicVolume_thickening_le_of_net {n : ℕ} (K : Set (Space n)) {r A : ℝ}
    (hr : 0 < r) (F : Finset (Space n)) (hFcard : (F.card : ℝ) ≤ A)
    (hcov : K ⊆ ⋃ x ∈ F, Metric.ball x r) :
    parabolicVolume n {z | Metric.infEDist z K < ENNReal.ofReal r} ≤
      ENNReal.ofReal (A * (2 * (omega n).toReal) * (2 * r) ^ (n + 2)) := by
  have hsub : {z | Metric.infEDist z K < ENNReal.ofReal r} ⊆
      ⋃ x ∈ F, Metric.ball x (2 * r) := by
    intro z hz
    obtain ⟨y, hyK, hzy⟩ := Metric.infEDist_lt_iff.mp hz
    obtain ⟨x, hxF, hyx⟩ := mem_iUnion₂.mp (hcov hyK)
    refine mem_iUnion₂.mpr ⟨x, hxF, ?_⟩
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr] at hzy
    have h1 : dist y x < r := hyx
    rw [Metric.mem_ball]
    linarith [dist_triangle z y x]
  have h2r : (0 : ℝ) < 2 * r := by positivity
  have hω : (0 : ℝ) ≤ 2 * (omega n).toReal := by positivity
  have hcalc : ∑ _x ∈ F, parabolicVolume n (Metric.ball _x (2 * r)) =
      ENNReal.ofReal ((F.card : ℝ) * (2 * (omega n).toReal * (2 * r) ^ (n + 2))) := by
    simp only [parabolicVolume_ball _ _ h2r]
    rw [Finset.sum_const, nsmul_eq_mul]
    have e1 : ENNReal.ofReal ((F.card : ℝ) * (2 * (omega n).toReal * (2 * r) ^ (n + 2))) =
        (F.card : ℝ≥0∞) * (ENNReal.ofReal (2 * (omega n).toReal) *
          ENNReal.ofReal ((2 * r) ^ (n + 2))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg F.card), ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul hω]
    have e2 : ENNReal.ofReal (2 * (omega n).toReal) = 2 * omega n := by
      rw [ENNReal.ofReal_mul (p := 2) (q := (omega n).toReal) (by norm_num),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal (omega_lt_top n).ne]
    rw [e1, e2, ENNReal.ofReal_pow h2r.le]
  calc parabolicVolume n {z | Metric.infEDist z K < ENNReal.ofReal r}
      ≤ parabolicVolume n (⋃ x ∈ F, Metric.ball x (2 * r)) := measure_mono hsub
    _ ≤ ∑ x ∈ F, parabolicVolume n (Metric.ball x (2 * r)) := measure_biUnion_finset_le F _
    _ = ENNReal.ofReal ((F.card : ℝ) * (2 * (omega n).toReal * (2 * r) ^ (n + 2))) := hcalc
    _ ≤ ENNReal.ofReal (A * (2 * (omega n).toReal) * (2 * r) ^ (n + 2)) := by
        apply ENNReal.ofReal_le_ofReal
        calc (F.card : ℝ) * (2 * (omega n).toReal * (2 * r) ^ (n + 2))
            ≤ A * (2 * (omega n).toReal * (2 * r) ^ (n + 2)) :=
              mul_le_mul_of_nonneg_right hFcard (by positivity)
          _ = _ := by ring

/-! ## Hausdorff domination of the carrier -/

theorem hausdorffP_densityCarrier_inter_open_le {n : ℕ} (ν : Measure (Space n))
    [IsFiniteMeasure ν] {k : ℕ} {a : ℝ} (ha : 0 < a) {U : Set (Space n)} (hU : IsOpen U) :
    hausdorffP n k (densityCarrier ν k a ∩ U) ≤ ENNReal.ofReal (12 ^ k / a) * ν U := by
  classical
  have hfam : ∀ m : ℕ, ∃ u : Set (Space n × ℝ), u.Countable ∧
      (∀ p ∈ u, p.1 ∈ densityCarrier ν k a ∧ 0 < p.2 ∧ p.2 ≤ 1 / ((m : ℝ) + 1) ∧
        Metric.ball p.1 (2 * p.2) ⊆ U) ∧
      u.PairwiseDisjoint (fun p => Metric.ball p.1 (2 * p.2)) ∧
      densityCarrier ν k a ∩ U ⊆ ⋃ p ∈ u, Metric.ball p.1 (6 * p.2) := by
    intro m
    have hδ : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨u, hut, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun p : Space n × ℝ => Metric.ball p.1 (2 * p.2))
      {p : Space n × ℝ | p.1 ∈ densityCarrier ν k a ∩ U ∧ 0 < p.2 ∧
        p.2 ≤ 1 / ((m : ℝ) + 1) ∧ Metric.ball p.1 (2 * p.2) ⊆ U}
      (fun p => p.2) 2 one_lt_two (fun p hp => hp.2.1.le) (1 / ((m : ℝ) + 1))
      (fun p hp => hp.2.2.1) (fun p hp => ⟨p.1, Metric.mem_ball_self (by linarith [hp.2.1])⟩)
    refine ⟨u, hudisj.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
      (fun p hp => ⟨p.1, Metric.mem_ball_self (by linarith [(hut hp).2.1])⟩),
      fun p hp => ⟨(hut hp).1.1, (hut hp).2.1, (hut hp).2.2.1, (hut hp).2.2.2⟩, hudisj, ?_⟩
    intro z hz
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hz.2
    have hs : 0 < min (ε / 2) (1 / ((m : ℝ) + 1)) := lt_min (by linarith) hδ
    have hp : (z, min (ε / 2) (1 / ((m : ℝ) + 1))) ∈ {p : Space n × ℝ |
        p.1 ∈ densityCarrier ν k a ∩ U ∧ 0 < p.2 ∧ p.2 ≤ 1 / ((m : ℝ) + 1) ∧
        Metric.ball p.1 (2 * p.2) ⊆ U} :=
      ⟨hz, hs, min_le_right _ _, (Metric.ball_subset_ball
        (by linarith [min_le_left (ε / 2) (1 / ((m : ℝ) + 1))])).trans hεU⟩
    obtain ⟨b, hbu, ⟨w, hw1, hw2⟩, hsb⟩ := hucov _ hp
    refine mem_iUnion₂.mpr ⟨b, hbu, ?_⟩
    have h1 : dist w z < 2 * min (ε / 2) (1 / ((m : ℝ) + 1)) := hw1
    have h2 : dist w b.1 < 2 * b.2 := hw2
    have h3 : min (ε / 2) (1 / ((m : ℝ) + 1)) ≤ 2 * b.2 := hsb
    rw [Metric.mem_ball]
    linarith [dist_triangle z w b.1, dist_comm w z]
  choose u hucount hut hudisj hucov using hfam
  have : ∀ m, Countable (u m) := fun m => (hucount m).to_subtype
  have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal (12 * (1 / ((m : ℝ) + 1)))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 12
    rw [mul_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  have ht : ∀ m (p : u m), Metric.ediam (Metric.ball (p : Space n × ℝ).1 (6 * (p : Space n × ℝ).2)) ≤
      ENNReal.ofReal (12 * (1 / ((m : ℝ) + 1))) := by
    intro m p
    have hp := hut m p p.2
    apply Metric.ediam_le
    intro y hy w hw
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have h1 : dist y (p : Space n × ℝ).1 < 6 * (p : Space n × ℝ).2 := hy
    have h2 : dist w (p : Space n × ℝ).1 < 6 * (p : Space n × ℝ).2 := hw
    linarith [dist_triangle_right y w (p : Space n × ℝ).1, hp.2.2.1]
  have hst : ∀ m, densityCarrier ν k a ∩ U ⊆
      ⋃ p : u m, Metric.ball (p : Space n × ℝ).1 (6 * (p : Space n × ℝ).2) := by
    intro m z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp (hucov m hz)
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hzp⟩
  have key := Measure.hausdorffMeasure_le_liminf_tsum (k : ℝ) (densityCarrier ν k a ∩ U) _ hlim
    (fun m (p : u m) => Metric.ball (p : Space n × ℝ).1 (6 * (p : Space n × ℝ).2))
    (Eventually.of_forall ht) (Eventually.of_forall hst)
  unfold hausdorffP
  refine key.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun m => ?_))
  have hterm : ∀ p : u m, Metric.ediam (Metric.ball (p : Space n × ℝ).1
      (6 * (p : Space n × ℝ).2)) ^ (k : ℝ) ≤
      ENNReal.ofReal (12 ^ k / a) * ν (Metric.ball (p : Space n × ℝ).1 (2 * (p : Space n × ℝ).2)) := by
    intro p
    have hp := hut m p p.2
    have hpos : 0 < (p : Space n × ℝ).2 := hp.2.1
    have hp1 : (p : Space n × ℝ).2 ≤ 1 := hp.2.2.1.trans (by
      rw [div_le_one (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have hdiam : Metric.ediam (Metric.ball (p : Space n × ℝ).1 (6 * (p : Space n × ℝ).2)) ≤
        ENNReal.ofReal (12 * (p : Space n × ℝ).2) := by
      apply Metric.ediam_le
      intro y hy w hw
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      have h1 : dist y (p : Space n × ℝ).1 < 6 * (p : Space n × ℝ).2 := hy
      have h2 : dist w (p : Space n × ℝ).1 < 6 * (p : Space n × ℝ).2 := hw
      linarith [dist_triangle_right y w (p : Space n × ℝ).1]
    have hmass : ENNReal.ofReal (a * (p : Space n × ℝ).2 ^ k) ≤
        ν (Metric.ball (p : Space n × ℝ).1 (2 * (p : Space n × ℝ).2)) :=
      ((hp.1).2 _ hpos hp1).trans (measure_mono (Metric.closedBall_subset_ball (by linarith)))
    calc Metric.ediam (Metric.ball (p : Space n × ℝ).1 (6 * (p : Space n × ℝ).2)) ^ (k : ℝ)
        ≤ ENNReal.ofReal (12 * (p : Space n × ℝ).2) ^ (k : ℝ) :=
          ENNReal.rpow_le_rpow hdiam (Nat.cast_nonneg k)
      _ = ENNReal.ofReal (12 ^ k / a) * ENNReal.ofReal (a * (p : Space n × ℝ).2 ^ k) := by
          rw [ENNReal.rpow_natCast,
            ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 12 * (p : Space n × ℝ).2),
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 12 ^ k / a)]
          congr 1
          rw [mul_pow, div_mul_eq_mul_div, eq_div_iff ha.ne']
          ring
      _ ≤ _ := mul_le_mul_right hmass _
  calc ∑' p : u m, Metric.ediam (Metric.ball (p : Space n × ℝ).1 (6 * (p : Space n × ℝ).2)) ^ (k : ℝ)
      ≤ ∑' p : u m, ENNReal.ofReal (12 ^ k / a) *
          ν (Metric.ball (p : Space n × ℝ).1 (2 * (p : Space n × ℝ).2)) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (12 ^ k / a) *
          ∑' p : u m, ν (Metric.ball (p : Space n × ℝ).1 (2 * (p : Space n × ℝ).2)) :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (12 ^ k / a) * ν (⋃ p ∈ u m, Metric.ball p.1 (2 * p.2)) := by
        rw [measure_biUnion (hucount m) (hudisj m) (fun _ _ => measurableSet_ball)]
    _ ≤ ENNReal.ofReal (12 ^ k / a) * ν U :=
        mul_le_mul_right (measure_mono (iUnion₂_subset fun p hp => (hut m p hp).2.2.2)) _

/-- Hausdorff domination: `H^k_P ⌞ K_a ≤ (C/a) ν` for any
`C ≥ 12^k`. One-sided; it does not assert `ν ⌞ K_a ≪ H^k_P`. -/
theorem restrict_hausdorffP_densityCarrier_le {n : ℕ} (ν : Measure (Space n)) [IsFiniteMeasure ν]
    {k : ℕ} {a Cd : ℝ} (ha : 0 < a) (hCd : 12 ^ k ≤ Cd) :
    (hausdorffP n k).restrict (densityCarrier ν k a) ≤ ENNReal.ofReal (Cd / a) • ν := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.restrict_apply hs, Measure.smul_apply, smul_eq_mul]
  have hc0 : ENNReal.ofReal (12 ^ k / a) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hctop : ENNReal.ofReal (12 ^ k / a) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmono : ENNReal.ofReal (12 ^ k / a) ≤ ENNReal.ofReal (Cd / a) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hCd ha.le)
  refine le_trans ?_ (mul_le_mul_left hmono _)
  apply le_of_forall_gt_imp_ge_of_dense
  intro x hx
  have hlt : ν s < x / ENNReal.ofReal (12 ^ k / a) :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hc0) (Or.inl hctop)).mpr (by rwa [mul_comm])
  obtain ⟨U, hsU, hUo, hUlt⟩ := s.exists_isOpen_lt_of_lt _ hlt
  calc hausdorffP n k (s ∩ densityCarrier ν k a)
      ≤ hausdorffP n k (densityCarrier ν k a ∩ U) :=
        measure_mono fun w hw => ⟨hw.2, hsU hw.1⟩
    _ ≤ ENNReal.ofReal (12 ^ k / a) * ν U := hausdorffP_densityCarrier_inter_open_le ν ha hUo
    _ ≤ ENNReal.ofReal (12 ^ k / a) * (x / ENNReal.ofReal (12 ^ k / a)) :=
        mul_le_mul_right hUlt.le _
    _ = x := ENNReal.mul_div_cancel hc0 hctop

/-! ## Density selection from discrete packing -/

/-- **Density selection from discrete packing**: the `discrete_packing` statement implies
the `density_selection` statement. -/
theorem density_selection_of_discrete (n : ℕ) :
    (∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (T : FamilyKind), 1 ≤ k → k < n + 2 →
      Nonempty (Models n k T) →
      ∀ (q : Space n) (R b B : ℝ) (l : ℕ) (z : Fin l → Space n) (r w : Fin l → ℝ),
        0 < R → 0 < b → 0 ≤ B →
        (∀ i, 0 < r i ∧ Metric.ball (z i) (r i) ⊆ Metric.ball q R) →
        (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
        (∀ i, 0 < w i ∧ w i ≤ b) →
        (∀ i, ∫⁻ s in Ioi (r i), betaSq (truncatedAtomicSource k z r w s) k T (z i) s
            ∂scaleMeasure ≤ ENNReal.ofReal B) →
        ∑ i, ENNReal.ofReal (w i * r i ^ k) ≤ ENNReal.ofReal (C * (b + B) * R ^ k)) →
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (T : FamilyKind), 1 ≤ k → k < n + 2 →
      Nonempty (Models n k T) →
      ∀ (ν : Measure (Space n)) (c : Space n) (L a : ℝ), IsFiniteMeasure ν →
        ν.support ⊆ Metric.closedBall c (1 / 16) → 0 ≤ L → 0 < a →
        (∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ ENNReal.ofReal L) →
        IsCompact (densityCarrier ν k a) ∧
          ν (densityCarrier ν k a)ᶜ ≤ ENNReal.ofReal (C * (a + L)) ∧
          HasMetricContentBounds k (C * (1 + L / a)) (densityCarrier ν k a) ∧
          (hausdorffP n k).restrict (densityCarrier ν k a) ≤ ENNReal.ofReal (C / a) • ν := by
  rintro ⟨C5, hC5, hdisc⟩
  have hω : (0 : ℝ) ≤ (omega n).toReal := ENNReal.toReal_nonneg
  have hCnet : 0 < 4 * C5 * 120 ^ (n + 2) := by positivity
  refine ⟨50 ^ (n + 3) * C5 * (10 ^ (n + 2) + 2 ^ (n + 3)) +
      (4 * C5 * 120 ^ (n + 2) * 2 ^ (n + 2) +
        4 * C5 * 120 ^ (n + 2) * (2 * (omega n).toReal) * 2 ^ (n + 2) +
        4 * C5 * 120 ^ (n + 2)) + 12 ^ (n + 2), by positivity, ?_⟩
  intro k T hk hkn hT ν c L a hν hsupp hL ha henergy
  set Closs : ℝ := 50 ^ (n + 3) * C5 * (10 ^ (n + 2) + 2 ^ (n + 3)) with hClossdef
  set Cnet : ℝ := 4 * C5 * 120 ^ (n + 2) with hCnetdef
  set Ch : ℝ := Cnet * 2 ^ (n + 2) with hChdef
  set Cm : ℝ := Cnet * (2 * (omega n).toReal) * 2 ^ (n + 2) with hCmdef
  set Cdom : ℝ := (12 : ℝ) ^ (n + 2) with hCdomdef
  set C : ℝ := Closs + (Ch + Cm + Cnet) + Cdom with hCdef
  have hCnetp : 0 ≤ Cnet := hCnet.le
  have hClossp : 0 ≤ Closs := by rw [hClossdef]; positivity
  have hChp : 0 ≤ Ch := by rw [hChdef]; positivity
  have hCmp : 0 ≤ Cm := by rw [hCmdef]; positivity
  have hCdomp : 0 ≤ Cdom := by rw [hCdomdef]; positivity
  have hLa : 0 ≤ 1 + L / a := by positivity
  have hdisc' : DiscretePackingBound n C5 := hdisc
  refine ⟨isCompact_densityCarrier ν k a hsupp, ?_, ?_, ?_⟩
  · -- loss
    refine (measure_compl_densityCarrier_le hdisc' hC5 hk hkn hT ν c hsupp hL ha henergy).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) (by linarith)))
  · -- content bounds
    have hnetK : ∀ (q : Space n) (R ρ : ℝ), 0 < ρ → ρ ≤ R → R ≤ 1 →
        ∃ F : Finset (Space n), (F.card : ℝ) ≤ Cnet * (1 + L / a) * (R / ρ) ^ k ∧
          densityCarrier ν k a ∩ Metric.ball q R ⊆ ⋃ x ∈ F, Metric.ball x ρ := by
      intro q R ρ hρ hρR hR1
      have hb : ∀ F : Finset (Space n), ↑F ⊆ densityCarrier ν k a ∩ Metric.ball q R →
          IsSeparatedFinset ρ F → (F.card : ℝ) ≤ Cnet * (1 + L / a) * (R / ρ) ^ k :=
        fun F hF hsep => card_le_of_separated_densityCarrier hdisc' hC5 hk hkn hT ν hL ha
          henergy q hρ hρR hR1 F hF hsep
      obtain ⟨F, hFS, hFsep, hFcov⟩ := exists_maximal_separated_finset _ hρ
        ⌊Cnet * (1 + L / a) * (R / ρ) ^ k⌋₊ (fun F hF hsep => Nat.le_floor (hb F hF hsep))
      refine ⟨F, hb F hFS hFsep, fun x hx => ?_⟩
      obtain ⟨y, hy, hxy⟩ := hFcov x hx
      exact mem_iUnion₂.mpr ⟨y, hy, hxy⟩
    refine ⟨fun q R hR hR1 => ?_, fun q R r hR hR1 hr hrR F hF hsep => ?_, fun r hr hr1 => ?_⟩
    · -- local Hausdorff
      have h := hausdorffP_le_of_nets k (densityCarrier ν k a ∩ Metric.ball q R)
        (by positivity : 0 ≤ Cnet * (1 + L / a)) hR
        (fun ρ hρ hρR => hnetK q R ρ hρ hρR hR1)
      refine h.trans (ENNReal.ofReal_le_ofReal ?_)
      have h2 : (2 : ℝ) ^ k ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hRk : 0 ≤ R ^ k := by positivity
      calc Cnet * (1 + L / a) * 2 ^ k * R ^ k ≤ Cnet * (1 + L / a) * 2 ^ (n + 2) * R ^ k :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) hRk
        _ = Ch * (1 + L / a) * R ^ k := by rw [hChdef]; ring
        _ ≤ C * (1 + L / a) * R ^ k := by
            gcongr
            rw [hCdef]
            linarith
    · -- local net
      refine (card_le_of_separated_densityCarrier hdisc' hC5 hk hkn hT ν hL ha henergy q hr hrR hR1
        F hF hsep).trans ?_
      have hRr : 0 ≤ (R / r) ^ k := by positivity
      rw [← hCnetdef]
      gcongr
      rw [hCdef]
      linarith
    · -- local tube
      obtain ⟨F, hFcard, hFcov⟩ := hnetK c 1 r hr hr1 le_rfl
      have hKsub : densityCarrier ν k a ⊆ densityCarrier ν k a ∩ Metric.ball c 1 := by
        intro z hz
        refine ⟨hz, ?_⟩
        have := hsupp hz.1
        rw [Metric.mem_closedBall] at this
        rw [Metric.mem_ball]
        linarith
      have h := parabolicVolume_thickening_le_of_net (densityCarrier ν k a) hr F hFcard
        (hKsub.trans hFcov)
      refine h.trans (ENNReal.ofReal_le_ofReal ?_)
      have hsub : n + 2 - k + k = n + 2 := by omega
      have hrk : r ^ (n + 2) = r ^ (n + 2 - k) * r ^ k := by rw [← pow_add, hsub]
      have e : Cnet * (1 + L / a) * (1 / r) ^ k * (2 * (omega n).toReal) * (2 * r) ^ (n + 2) =
          Cm * (1 + L / a) * r ^ (n + 2 - k) := by
        calc Cnet * (1 + L / a) * (1 / r) ^ k * (2 * (omega n).toReal) * (2 * r) ^ (n + 2)
            = Cnet * (2 * (omega n).toReal) * 2 ^ (n + 2) * (1 + L / a) * r ^ (n + 2 - k) *
                (r ^ k / r ^ k) := by
              rw [mul_pow, hrk, one_div_pow]
              ring
          _ = Cm * (1 + L / a) * r ^ (n + 2 - k) := by
              rw [div_self (pow_ne_zero _ hr.ne'), mul_one, hCmdef]
      rw [e]
      have hr0 : 0 ≤ r ^ (n + 2 - k) := by positivity
      gcongr
      rw [hCdef]
      linarith
  · -- domination
    have h12 : (12 : ℝ) ^ k ≤ C := by
      have : (12 : ℝ) ^ k ≤ 12 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [hCdef]
      linarith
    exact restrict_hausdorffP_densityCarrier_le ν ha h12

end ParabolicRectifiability
