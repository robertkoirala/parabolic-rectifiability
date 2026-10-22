import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Measure.ScaleEnergy
import ParabolicRectifiability.Metric.Hausdorff
import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import ParabolicRectifiability.Enhancements.Statements.ScaledCore
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # Finite-energy tail truncation

Proves `b4_tail_truncation_proof`, with exactly the type of `b4_tail_truncation`: for a set of
finite `H_P^k` measure and finite square energy almost everywhere, the tail of the energy can
be truncated on a set of almost full measure.

Route. Scales `s_j = R/(j+1)`. At a point with `S^R_η(z) < ∞`, the measure
`A ↦ ∫_{A} β²_η(z,r) dr/r` (`scaleMeasure.withDensity`) is finite on `(0,R)`, and the
intervals `(0,s_j)` decrease to `∅`, so `S^{s_j}_η(z) → 0` by continuity from above. The sets
`B_j = E ∩ {S^{s_j}_η > e}` are measurable (`measurable_squareEnergy`; `η = H_P^k⌊E` is finite),
decrease, and meet in an `η`-null set; finiteness of `η` gives `η(B_j) → 0`. For `j` with
`η(B_j) < e` the sublevel set `F = E ∩ {S^{s_j}_η ≤ e}` is the witness, and
`H_P^k(E \ F) = η(B_j)`. No rate is claimed. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- Square energy is the `withDensity` measure of the radial interval `(0,s)`. -/
theorem b4p1_squareEnergy_eq_withDensity {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) (s : ℝ) (z : Space n) :
    squareEnergy μ k T s z = (scaleMeasure.withDensity (betaSq μ k T z)) (Ioo 0 s) := by
  rw [withDensity_apply _ measurableSet_Ioo]
  rfl

/-- Square energy is monotone in the endpoint. -/
theorem b4p1_squareEnergy_mono {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    {s t : ℝ} (hst : s ≤ t) (z : Space n) :
    squareEnergy μ k T s z ≤ squareEnergy μ k T t z := by
  rw [b4p1_squareEnergy_eq_withDensity, b4p1_squareEnergy_eq_withDensity]
  exact measure_mono (Ioo_subset_Ioo_right hst)

theorem b4p1_scale_pos {R : ℝ} (hR : 0 < R) (j : ℕ) : 0 < R / ((j : ℝ) + 1) := by
  positivity

theorem b4p1_scale_antitone {R : ℝ} (hR : 0 < R) :
    Antitone (fun j : ℕ => R / ((j : ℝ) + 1)) := by
  intro i j hij
  have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
    have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  exact div_le_div_of_nonneg_left hR.le hi hij'

theorem b4p1_Ioo_antitone {R : ℝ} (hR : 0 < R) :
    Antitone (fun j : ℕ => Ioo (0 : ℝ) (R / ((j : ℝ) + 1))) :=
  fun _ _ hij => Ioo_subset_Ioo_right (b4p1_scale_antitone hR hij)

/-- The intervals `(0, R/(j+1))` have empty intersection. -/
theorem b4p1_iInter_Ioo (R : ℝ) : ⋂ j : ℕ, Ioo (0 : ℝ) (R / ((j : ℝ) + 1)) = ∅ := by
  ext r
  simp only [mem_iInter, mem_Ioo, mem_empty_iff_false, iff_false]
  intro h
  have hr : 0 < r := (h 0).1
  obtain ⟨j, hj⟩ := exists_nat_gt (R / r)
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h1 : r * ((j : ℝ) + 1) < R := (lt_div_iff₀ hj1).1 (h j).2
  have h2 : R < (j : ℝ) * r := (div_lt_iff₀ hr).1 hj
  nlinarith

/-- At a point of finite energy at the endpoint `R`, the energy at `R/(j+1)` tends to `0`. -/
theorem b4p1_tendsto_energy {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    {R : ℝ} (hR : 0 < R) {z : Space n} (hz : squareEnergy μ k T R z < ⊤) :
    Filter.Tendsto (fun j : ℕ => squareEnergy μ k T (R / ((j : ℝ) + 1)) z)
      Filter.atTop (nhds 0) := by
  have h0 : scaleMeasure.withDensity (betaSq μ k T z)
      (Ioo 0 (R / (((0 : ℕ) : ℝ) + 1))) ≠ ⊤ := by
    rw [← b4p1_squareEnergy_eq_withDensity]
    simpa only [Nat.cast_zero, zero_add, div_one] using hz.ne
  have h : Filter.Tendsto
      (fun j : ℕ => scaleMeasure.withDensity (betaSq μ k T z) (Ioo 0 (R / ((j : ℝ) + 1))))
      Filter.atTop
      (nhds (scaleMeasure.withDensity (betaSq μ k T z)
        (⋂ j : ℕ, Ioo (0 : ℝ) (R / ((j : ℝ) + 1))))) :=
    tendsto_measure_iInter_atTop (fun _ => measurableSet_Ioo.nullMeasurableSet)
      (b4p1_Ioo_antitone hR) ⟨0, h0⟩
  rw [b4p1_iInter_Ioo, measure_empty] at h
  exact h.congr (fun j => (b4p1_squareEnergy_eq_withDensity μ k T _ z).symm)

/-- Abstract step: for a finite measure and an antitone sequence of measurable functions that
tends to `0` almost everywhere, some superlevel set `E ∩ {f_j > c}` has measure below `c`. -/
theorem b4p1_exists_small_bad {α : Type*} [MeasurableSpace α] (η : Measure α)
    [IsFiniteMeasure η] {E : Set α} (hE : MeasurableSet E) (f : ℕ → α → ℝ≥0∞)
    (hf : ∀ j, Measurable (f j)) (hanti : ∀ i j, i ≤ j → ∀ z, f j z ≤ f i z)
    (hlim : ∀ᵐ z ∂η, Filter.Tendsto (fun j => f j z) Filter.atTop (nhds 0))
    {c : ℝ≥0∞} (hc : 0 < c) : ∃ j, η (E ∩ {z | c < f j z}) < c := by
  have hm : ∀ j, MeasurableSet (E ∩ {z | c < f j z}) := fun j =>
    hE.inter (measurableSet_lt measurable_const (hf j))
  have hA : Antitone (fun j => E ∩ {z | c < f j z}) := by
    intro i j hij z hz
    exact ⟨hz.1, lt_of_lt_of_le hz.2 (hanti i j hij z)⟩
  have hnull : η (⋂ j, E ∩ {z | c < f j z}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hlim)
    intro z hz
    change ¬ Filter.Tendsto (fun j => f j z) Filter.atTop (nhds 0)
    intro hzlim
    obtain ⟨j, hj⟩ := (hzlim.eventually (gt_mem_nhds hc)).exists
    exact (not_lt.2 hj.le) (mem_iInter.1 hz j).2
  have h : Filter.Tendsto (fun j => η (E ∩ {z | c < f j z})) Filter.atTop
      (nhds (η (⋂ j, E ∩ {z | c < f j z}))) :=
    tendsto_measure_iInter_atTop (fun j => (hm j).nullMeasurableSet) hA ⟨0, measure_ne_top _ _⟩
  rw [hnull] at h
  exact (h.eventually (gt_mem_nhds hc)).exists

/-- Abstract witness: the sublevel set inside `E` satisfies the four required properties once
its complementary superlevel set has small restricted measure. -/
theorem b4p1_witness {α : Type*} [MeasurableSpace α] (H : Measure α) {E : Set α}
    (hE : MeasurableSet E) (g : α → ℝ≥0∞) (hg : Measurable g) (c : ℝ≥0∞)
    (hsmall : H.restrict E (E ∩ {z | c < g z}) < c) :
    MeasurableSet (E ∩ {z | g z ≤ c}) ∧ E ∩ {z | g z ≤ c} ⊆ E ∧
      (∀ z ∈ E ∩ {z | g z ≤ c}, g z ≤ c) ∧ H (E \ (E ∩ {z | g z ≤ c})) < c := by
  have hdiff : E \ (E ∩ {z | g z ≤ c}) = E ∩ {z | c < g z} := by
    ext z
    constructor
    · rintro ⟨hzE, hzF⟩
      refine ⟨hzE, ?_⟩
      show c < g z
      exact not_le.1 (fun h => hzF ⟨hzE, h⟩)
    · rintro ⟨hzE, hz⟩
      have hz' : c < g z := hz
      exact ⟨hzE, fun h => (not_le.2 hz') (show g z ≤ c from h.2)⟩
  refine ⟨hE.inter (measurableSet_le hg measurable_const), inter_subset_left,
    fun z hz => hz.2, ?_⟩
  rw [hdiff]
  rwa [Measure.restrict_apply' hE, inter_eq_left.2 inter_subset_left] at hsmall

/-- **Tail truncation**: the statement of `b4_tail_truncation`. -/
theorem b4_tail_truncation_proof :
    ∀ (n k : ℕ) (T : FamilyKind) (E : Set (Space n)), MeasurableSet E →
      hausdorffP n k E < ⊤ → ∀ R : ℝ, 0 < R →
      (∀ᵐ z ∂(hausdorffP n k).restrict E,
        squareEnergy ((hausdorffP n k).restrict E) k T R z < ⊤) →
      ∀ e : ℝ, 0 < e →
        ∃ s : ℝ, 0 < s ∧ ∃ F : Set (Space n), MeasurableSet F ∧ F ⊆ E ∧
          (∀ z ∈ F, squareEnergy ((hausdorffP n k).restrict E) k T s z ≤ ENNReal.ofReal e) ∧
          hausdorffP n k (E \ F) < ENNReal.ofReal e := by
  intro n k T E hE hfin R hR hae e he
  have : IsFiniteMeasure ((hausdorffP n k).restrict E) := hausdorffP_restrict_isFinite hfin
  obtain ⟨j, hj⟩ := b4p1_exists_small_bad ((hausdorffP n k).restrict E) hE
    (fun j z => squareEnergy ((hausdorffP n k).restrict E) k T (R / ((j : ℝ) + 1)) z)
    (fun j => measurable_squareEnergy _ k T _)
    (fun i j hij z => b4p1_squareEnergy_mono _ k T (b4p1_scale_antitone hR hij) z)
    (hae.mono fun z hz => b4p1_tendsto_energy _ k T hR hz)
    (ENNReal.ofReal_pos.2 he)
  exact ⟨R / ((j : ℝ) + 1), b4p1_scale_pos hR j, _,
    b4p1_witness (hausdorffP n k) hE _ (measurable_squareEnergy _ k T _) _ hj⟩

end ParabolicRectifiability.Characterization
