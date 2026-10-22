import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceAdapterStatements
import ParabolicRectifiability.QuantitativeCharacterization.Coverings
import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Measure.ScaleEnergy

/-! # ADR carriers and localization of square energies

Three short auxiliary facts:

* `b2_isADRCarrier_of_isADR_proof` (`ADRCarrierOfADRStatement`): an Ahlfors–David regular
  measure is an ADR carrier of its support. Closed support; finiteness on compacts from upper ADR around a
  nearby support point (a ball missing the support is null, `measure_compl_support`); inner
  regularity from `InnerRegularCompactLTTop` (complete second-countable Borel space) and
  sigma-finiteness (`source_sigmaFinite`);
* `b2_ae_squareEnergy_lt_top_of_carleson_proof`: a finite root Carleson supremum gives a finite
  square energy `σ`-almost everywhere. One root centre `a ∈ S`, the balls `P(a, N+1)`,
  `ae_lt_top'` and monotonicity in the endpoint;
* `b2_squareEnergy_restrict_closedBall_proof`: if `d(z,a) + R ≤ ρ`, the square energy at `z` up
  to scale `R` is unchanged by restricting the measure to `P̄(a,ρ)`. For `0 < r < R` the testing
  ball lies in `P̄(a,ρ)`, so every `fit` agrees exactly (`Measure.restrict_restrict`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.QuantitativeCharacterization

/-- Upper ADR on the support gives finiteness of every open ball. -/
theorem b2small_ball_lt_top_of_isADR {n k : ℕ} {A : ℝ} {σ : Measure (Space n)}
    (hadr : IsADR A k σ) (z : Space n) (r : ℝ) : σ (Metric.ball z r) < ⊤ := by
  by_cases h : (Metric.ball z r ∩ σ.support).Nonempty
  · obtain ⟨w, hwb, hws⟩ := h
    have hr : 0 < r := Metric.pos_of_mem_ball hwb
    have hsub : Metric.ball z r ⊆ Metric.ball w (2 * r) := by
      intro x hx
      rw [Metric.mem_ball] at hx hwb ⊢
      have h1 := dist_triangle x z w
      have h2 := dist_comm z w
      linarith
    exact (measure_mono hsub).trans_lt
      ((hadr w hws (2 * r) (by positivity)).2.trans_lt ENNReal.ofReal_lt_top)
  · have hsub : Metric.ball z r ⊆ σ.supportᶜ := fun x hx hxs => h ⟨x, hx, hxs⟩
    refine (measure_mono hsub).trans_lt ?_
    rw [Measure.measure_compl_support]
    exact ENNReal.zero_lt_top

/-- An Ahlfors–David regular measure is an ADR carrier of its support
(`ADRCarrierOfADRStatement`). -/
theorem b2_isADRCarrier_of_isADR_proof : ADRCarrierOfADRStatement := by
  intro n k A σ hk hA hne hadr
  have hfin : IsFiniteMeasureOnCompacts σ := by
    refine ⟨fun K hK => ?_⟩
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball hne.some).1 hK.isBounded
    exact (measure_mono hr).trans_lt (b2small_ball_lt_top_of_isADR hadr _ r)
  have := hfin
  have : SigmaFinite σ := source_sigmaFinite σ
  have hir : σ.InnerRegular := inferInstance
  exact
    { dimension_pos := hk
      lower_pos := inv_pos.2 hA
      upper_pos := hA
      nonempty := hne
      isClosed := Measure.isClosed_support
      finiteOnCompacts := hfin
      innerRegular := hir
      support_eq := rfl
      lower := fun z hz r hr => (hadr z hz r hr).1
      upper := fun z hz r hr => (hadr z hz r hr).2 }

/-- One root ball: a finite normalized Carleson supremum gives `S^R < ∞` `σ`-a.e. on `P(a,R)`. -/
theorem b2small_ae_ball_squareEnergy_lt_top {n k : ℕ} {T : FamilyKind} {S : Set (Space n)}
    {σ : Measure (Space n)} [IsFiniteMeasureOnCompacts σ]
    (hM : rootCarlesonSup S σ k (fun R z => squareEnergy σ k T R z) < ⊤)
    {a : Space n} (ha : a ∈ S) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ z ∂σ, z ∈ Metric.ball a R → squareEnergy σ k T R z < ⊤ := by
  have hle : (ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball a R, squareEnergy σ k T R z ∂σ ≤
      rootCarlesonSup S σ k (fun R z => squareEnergy σ k T R z) := by
    unfold rootCarlesonSup
    exact le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le R (le_iSup_of_le hR le_rfl)))
  have hint : ∫⁻ z in Metric.ball a R, squareEnergy σ k T R z ∂σ ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top))]
      at hle
    exact absurd (hle.trans_lt hM) (lt_irrefl _)
  exact (ae_restrict_iff' measurableSet_ball).1
    (ae_lt_top' (measurable_squareEnergy σ k T R).aemeasurable hint)

/-- A finite root Carleson supremum of the square energy gives `S^1 < ∞` `σ`-almost
everywhere. -/
theorem b2_ae_squareEnergy_lt_top_of_carleson_proof :
    ∀ (n k : ℕ) (T : FamilyKind) (S : Set (Space n)) (σ : Measure (Space n)),
      IsFiniteMeasureOnCompacts σ → S.Nonempty →
      rootCarlesonSup S σ k (fun R z => squareEnergy σ k T R z) < ⊤ →
        ∀ᵐ z ∂σ, squareEnergy σ k T 1 z < ⊤ := by
  intro n k T S σ hσ hS hM
  have := hσ
  obtain ⟨a, ha⟩ := hS
  have hN : ∀ N : ℕ, ∀ᵐ z ∂σ, z ∈ Metric.ball a ((N : ℝ) + 1) →
      squareEnergy σ k T ((N : ℝ) + 1) z < ⊤ := fun N =>
    b2small_ae_ball_squareEnergy_lt_top hM ha (by positivity)
  filter_upwards [ae_all_iff.2 hN] with z hz
  obtain ⟨N, hN⟩ := exists_nat_gt (dist z a)
  have hzb : z ∈ Metric.ball a ((N : ℝ) + 1) := by
    rw [Metric.mem_ball]
    linarith
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  have hmono : squareEnergy σ k T 1 z ≤ squareEnergy σ k T ((N : ℝ) + 1) z :=
    lintegral_mono_set (Ioo_subset_Ioo_right (by linarith))
  exact hmono.trans_lt (hz N hzb)

/-- If `d(z,a) + R ≤ ρ`, restricting the measure to `P̄(a,ρ)` does not change the square energy
at `z` up to scale `R`. -/
theorem b2_squareEnergy_restrict_closedBall_proof :
    ∀ (n k : ℕ) (T : FamilyKind) (μ : Measure (Space n)) (a : Space n) (ρ R : ℝ)
      (z : Space n), dist z a + R ≤ ρ →
        squareEnergy (μ.restrict (Metric.closedBall a ρ)) k T R z = squareEnergy μ k T R z := by
  intro n k T μ a ρ R z h
  unfold squareEnergy
  refine setLIntegral_congr_fun measurableSet_Ioo ?_
  intro r hr
  rw [betaSq_of_pos _ _ _ _ hr.1, betaSq_of_pos _ _ _ _ hr.1]
  congr 1
  refine iInf_congr fun L => ?_
  have hsub : Metric.ball z r ⊆ Metric.closedBall a ρ := by
    intro w hw
    rw [Metric.mem_closedBall]
    have h1 := Metric.mem_ball.1 hw
    have h2 := dist_triangle w z a
    linarith [hr.2]
  simp only [fit]
  rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.2 hsub]

end ParabolicRectifiability.Characterization
