import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceAdapterStatements
import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.RestrictionLowerDensity
import ParabolicRectifiability.Characterization.Proofs.Fivefold

/-! # Comparison of an Ahlfors-regular measure with Hausdorff measure

Proves `ADRHausdorffComparisonStatement` (`b2_adr_hausdorff_comparison_proof`): a measure `σ`
that is Ahlfors–David regular of dimension `k` with support `Γ` is comparable to the parabolic
Hausdorff measure `H_P^k` restricted to `Γ`. The argument is first given in implication form over
the Vitali-type selection `FivefoldSelectionStatement`, which is then discharged by
`fivefold_ball_selection_proof`.

The constants, positive for arbitrary real `c, C` before the carrier hypothesis, are
`a = 2^k max(C,1)` and `b = 10^k max(c⁻¹,1)`.

* Upper bound `b2hdc_upper`: `σ(S) ≤ 2^k max(C,1) H_P^k(S ∩ Γ)`. `σ(Γᶜ) = 0`
  (`supp σ = Γ`), the singletons of `Γ` are `σ`-null (upper ADR at every radius, `k > 0`), and the
  small-ball-to-Hausdorff comparison `b4p2_outerMeasure_le_ofReal_mul_hausdorffMeasure` is
  applied to the outer measure `σ` on `S ∩ Γ`.
* Lower bound `b2hdc_lower`: `H_P^k(S ∩ Γ) ≤ 10^k c⁻¹ σ(S)`. For an open `U ⊇ S`, centre balls
  of radius `< 1/(j+1)` at the points of `S ∩ Γ` inside `U`, select disjoint ones whose fivefold
  dilates cover (`FivefoldSelectionStatement`), use lower ADR at the selected centres (on `Γ`) and
  `Measure.hausdorffMeasure_le_liminf_tsum`; then outer regularity of **`σ`**
  (`Set.measure_eq_iInf_isOpen`). No regularity of unrestricted `H_P^k` is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.QuantitativeCharacterization

/-- Under the reference hypotheses, the points of the carrier are `σ`-null (upper ADR at every
radius, positive dimension). -/
theorem b2hdc_singleton_null {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (h : IsADRCarrier k c C Γ σ) {z : Space n} (hz : z ∈ Γ) : σ {z} = 0 := by
  have hcont : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r ^ k)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (C * 0 ^ k))) := by
    have : Continuous (fun r : ℝ => ENNReal.ofReal (C * r ^ k)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [zero_pow h.dimension_pos.ne', mul_zero, ENNReal.ofReal_zero] at hcont
  refine le_antisymm (ge_of_tendsto hcont ?_) zero_le
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (measure_mono (singleton_subset_iff.2 (Metric.mem_ball_self hr))).trans
    (h.upper z hz r hr)

/-- **Upper bound.** `σ(S) ≤ 2^k max(C,1) H_P^k(S ∩ Γ)` for every set `S`. -/
theorem b2hdc_upper {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (h : IsADRCarrier k c C Γ σ) (S : Set (Space n)) :
    σ S ≤ ENNReal.ofReal (2 ^ k * max C 1) * hausdorffP n k (S ∩ Γ) := by
  have hnull : σ (S \ Γ) = 0 := by
    refine measure_mono_null ?_ (Measure.measure_compl_support (μ := σ))
    rw [h.support_eq]
    exact fun x hx => hx.2
  have hSΓ : σ S ≤ σ (S ∩ Γ) :=
    calc σ S ≤ σ (S ∩ Γ) + σ (S \ Γ) := measure_le_inter_add_sdiff σ S Γ
      _ = σ (S ∩ Γ) := by rw [hnull, add_zero]
  have hb := b4p2_outerMeasure_le_ofReal_mul_hausdorffMeasure σ.toOuterMeasure k (S ∩ Γ)
    (c' := max C 1) (r₀ := 1) (lt_of_lt_of_le one_pos (le_max_right _ _)) one_pos
    (fun z hz => b2hdc_singleton_null h hz.2)
    (fun z hz r hr _ => (measure_mono inter_subset_right).trans ((h.upper z hz.2 r hr).trans
      (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr.le k)))))
  refine hSΓ.trans ?_
  rw [mul_comm ((2 : ℝ) ^ k), hausdorffP_eq]
  exact hb

/-- The open-set form of the lower comparison: for `E ⊆ Γ` inside an open `U`,
`H_P^k(E) ≤ 10^k c⁻¹ σ(U)`. Selected balls lie in `U`, have centres on `Γ` and radii below
`1/(j+1)`; their fivefold dilates cover `E`. -/
theorem b2hdc_lower_open {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hF : FivefoldSelectionStatement) (h : IsADRCarrier k c C Γ σ)
    (E U : Set (Space n)) (hEΓ : E ⊆ Γ) (hEU : E ⊆ U) (hU : IsOpen U) :
    hausdorffP n k E ≤ ENNReal.ofReal (10 ^ k * c⁻¹) * σ U := by
  classical
  have hc0 : c ≠ 0 := h.lower_pos.ne'
  have hK : 0 ≤ (10 : ℝ) ^ k * c⁻¹ := mul_nonneg (by positivity) (inv_nonneg.2 h.lower_pos.le)
  have hx : ∀ x : E, ∃ δ : ℝ, 0 < δ ∧ Metric.ball (x : Space n) δ ⊆ U :=
    fun x => Metric.isOpen_iff.mp hU x (hEU x.2)
  choose δ hδpos hδsub using hx
  let r : ℕ → E → ℝ := fun j x => min (δ x) (1 / ((j : ℝ) + 1))
  have hrpos (j : ℕ) (x : E) : 0 < r j x := lt_min (hδpos x) (by positivity)
  have hrle (j : ℕ) (x : E) : r j x ≤ 1 / ((j : ℝ) + 1) := min_le_right _ _
  have hrsub (j : ℕ) (x : E) : Metric.ball (x : Space n) (r j x) ⊆ U :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans (hδsub x)
  choose J hJc hJd hJcov using fun j : ℕ =>
    hF (Space n) E (fun x => (x : Space n)) (r j) (hrpos j) ⟨1 / ((j : ℝ) + 1), hrle j⟩
  let (j : ℕ) : Countable (J j) := (hJc j).to_subtype
  have hd (j : ℕ) (x : E) :
      Metric.ediam (Metric.ball (x : Space n) (5 * r j x)) ≤ ENNReal.ofReal (10 * r j x) := by
    apply Metric.ediam_le_of_forall_dist_le
    intro y hy z hz
    have hy' := Metric.mem_ball.mp hy
    have hz' := Metric.mem_ball.mp hz
    have ht := dist_triangle_right y z (x : Space n)
    linarith
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (10 * (1 / ((j : ℝ) + 1)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => 10 * (1 / ((j : ℝ) + 1))) atTop (𝓝 (10 * 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 10
    rw [mul_zero] at h1
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h1
  have hdiam : ∀ j : ℕ, ∀ i : J j,
      Metric.ediam (Metric.ball ((i.1 : E) : Space n) (5 * r j i.1)) ≤
        ENNReal.ofReal (10 * (1 / ((j : ℝ) + 1))) :=
    fun j i => (hd j i.1).trans (ENNReal.ofReal_le_ofReal (by have := hrle j i.1; linarith))
  have hcover : ∀ j : ℕ, E ⊆ ⋃ i : J j, Metric.ball ((i.1 : E) : Space n) (5 * r j i.1) := by
    intro j x hx
    obtain ⟨b, hb, hxb⟩ := hJcov j ⟨x, hx⟩
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, hxb⟩
  have hcost : ∀ j : ℕ,
      ∑' i : J j, Metric.ediam (Metric.ball ((i.1 : E) : Space n) (5 * r j i.1)) ^ (k : ℝ) ≤
        ENNReal.ofReal (10 ^ k * c⁻¹) * σ U := by
    intro j
    have hterm : ∀ i : J j,
        Metric.ediam (Metric.ball ((i.1 : E) : Space n) (5 * r j i.1)) ^ (k : ℝ) ≤
          ENNReal.ofReal (10 ^ k * c⁻¹) * σ (Metric.ball ((i.1 : E) : Space n) (r j i.1)) := by
      intro i
      rw [ENNReal.rpow_natCast]
      have hr := hrpos j i.1
      have hlow := h.lower _ (hEΓ i.1.2) _ hr
      calc Metric.ediam (Metric.ball ((i.1 : E) : Space n) (5 * r j i.1)) ^ k
          ≤ ENNReal.ofReal (10 * r j i.1) ^ k := pow_le_pow_left' (hd j i.1) k
        _ = ENNReal.ofReal (10 ^ k * c⁻¹) * ENNReal.ofReal (c * r j i.1 ^ k) := by
            rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hK]
            congr 1
            rw [mul_pow, mul_assoc, inv_mul_cancel_left₀ hc0]
        _ ≤ ENNReal.ofReal (10 ^ k * c⁻¹) * σ (Metric.ball ((i.1 : E) : Space n) (r j i.1)) := by
            gcongr
    calc ∑' i : J j, Metric.ediam (Metric.ball ((i.1 : E) : Space n) (5 * r j i.1)) ^ (k : ℝ)
        ≤ ∑' i : J j, ENNReal.ofReal (10 ^ k * c⁻¹) *
            σ (Metric.ball ((i.1 : E) : Space n) (r j i.1)) := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (10 ^ k * c⁻¹) *
            σ (⋃ i ∈ J j, Metric.ball ((i : E) : Space n) (r j i)) := by
          rw [ENNReal.tsum_mul_left]
          congr 1
          exact (measure_biUnion (hJc j) (hJd j) (fun _ _ => measurableSet_ball)).symm
      _ ≤ ENNReal.ofReal (10 ^ k * c⁻¹) * σ U := by
          gcongr
          exact iUnion₂_subset fun i _ => hrsub j i
  have H := Measure.hausdorffMeasure_le_liminf_tsum (k : ℝ) E _ hlim
    (fun j (i : J j) => Metric.ball ((i.1 : E) : Space n) (5 * r j i.1))
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)
  rw [hausdorffP_eq]
  exact H.trans (liminf_le_of_frequently_le (Frequently.of_forall hcost))

/-- **Lower bound.** `H_P^k(S ∩ Γ) ≤ 10^k c⁻¹ σ(S)` for every set `S`, by outer regularity of
`σ` (a locally finite measure on the proper, second-countable space `X`). -/
theorem b2hdc_lower {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hF : FivefoldSelectionStatement) (h : IsADRCarrier k c C Γ σ) (S : Set (Space n)) :
    hausdorffP n k (S ∩ Γ) ≤ ENNReal.ofReal (10 ^ k * c⁻¹) * σ S := by
  have := h.finiteOnCompacts
  have hK0 : ENNReal.ofReal (10 ^ k * c⁻¹) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos (by positivity) (inv_pos.2 h.lower_pos)
  rw [S.measure_eq_iInf_isOpen σ]
  simp only [ENNReal.mul_iInf_of_ne hK0 ENNReal.ofReal_ne_top, le_iInf_iff]
  intro U hSU hU
  exact b2hdc_lower_open hF h (S ∩ Γ) U inter_subset_right (inter_subset_left.trans hSU) hU

/-- The ADR–Hausdorff comparison, in implication form over the fivefold ball selection.
Constants `a = 2^k max(C,1)`, `b = 10^k max(c⁻¹,1)`. -/
theorem b2hdc_comparison_of_fivefold :
    FivefoldSelectionStatement → ADRHausdorffComparisonStatement := by
  intro hF k c C
  refine ⟨2 ^ k * max C 1, 10 ^ k * max c⁻¹ 1,
    mul_pos (pow_pos two_pos k) (lt_of_lt_of_le one_pos (le_max_right _ _)),
    mul_pos (pow_pos (by norm_num) k) (lt_of_lt_of_le one_pos (le_max_right _ _)), ?_⟩
  intro n _ Γ σ h S
  refine ⟨b2hdc_upper h S, (b2hdc_lower hF h S).trans ?_⟩
  gcongr
  exact le_max_left _ _

/-- **ADR–Hausdorff comparison.** An Ahlfors–David regular measure is comparable to `H_P^k` on
its support; the fivefold selection is supplied by `fivefold_ball_selection_proof`. -/
theorem b2_adr_hausdorff_comparison_proof : ADRHausdorffComparisonStatement :=
  b2hdc_comparison_of_fivefold fivefold_ball_selection_proof

end ParabolicRectifiability.Characterization
