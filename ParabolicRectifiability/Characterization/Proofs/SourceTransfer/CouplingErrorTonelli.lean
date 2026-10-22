import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.TransferStatements

/-! # Measurability and Tonelli identity for the coupling error

Proves `CouplingErrorTonelliStatement` (`b3_couplingErrorTonelli_proof`): the coupling error
`x ↦ b3_couplingError k π x R` is Borel, and its integral over a Borel set `D` against `σ` equals
`∫ d_P(p.1,p.2)^2 w_{σ,D}(p.1,R) dπ(p)` with the error weight `b3_errorWeight`.

Proof: the joint integrand
`(x, r, p) ↦ 1_{dist p.1 x < r} r^{-k-2} d(p.1,p.2)^2` is Borel on
`(Space n × ℝ) × (Space n × Space n)` (`b3ton_measurable_kernel`); the coupling error is its
iterated integral `∫_{(0,R)} ∫ … dπ dr/r` (`b3ton_couplingError_eq`), hence Borel in the centre
(`Measurable.lintegral_prod_right'`, twice). Three swaps (`lintegral_lintegral_swap`: `r ↔ p`,
`x ↔ p`, `x ↔ r`) against the s-finite measures `σ⌊D` (`σ` is sigma-finite: finite on compacts
in the sigma-compact `Space n`), `π` (finite) and `scaleMeasure⌊(0,R)` bring the `x`-integral
inside, where `1_{P(x,r)}(p.1) = 1_{P(p.1,r)}(x)` (`dist_comm`) gives `σ(D ∩ P(p.1,r))`
(`b3ton_slice`). No case split on `R` is needed (`Ioo 0 R = ∅` is handled uniformly).
-/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.SourceTransferTree

/-- The joint integrand `((x, r), p) ↦ 1_{dist p.1 x < r} r^{-k-2} d_P(p.1,p.2)^2`. -/
def b3ton_kernel {n : ℕ} (k : ℕ) (q : (Space n × ℝ) × (Space n × Space n)) : ℝ≥0∞ :=
  if dist q.2.1 q.1.1 < q.1.2 then
    (ENNReal.ofReal q.1.2)⁻¹ ^ (k + 2) * edist q.2.1 q.2.2 ^ 2
  else 0

theorem b3ton_measurable_kernel {n : ℕ} (k : ℕ) :
    Measurable (fun q : (Space n × ℝ) × (Space n × Space n) => b3ton_kernel k q) := by
  change Measurable (fun q : (Space n × ℝ) × (Space n × Space n) =>
    if dist q.2.1 q.1.1 < q.1.2 then
      (ENNReal.ofReal q.1.2)⁻¹ ^ (k + 2) * edist q.2.1 q.2.2 ^ 2
    else 0)
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt
      ((measurable_fst.comp measurable_snd).dist (measurable_fst.comp measurable_fst))
      (measurable_snd.comp measurable_fst)
  · exact ((ENNReal.measurable_ofReal.comp (measurable_snd.comp measurable_fst)).inv.pow_const
      (k + 2)).mul (((measurable_fst.comp measurable_snd).edist
        (measurable_snd.comp measurable_snd)).pow_const 2)

theorem b3ton_edist_sq_ne_top {n : ℕ} (p : Space n × Space n) : edist p.1 p.2 ^ 2 ≠ ∞ :=
  ENNReal.pow_ne_top (edist_ne_top _ _)

/-- The weighted inner integral of the coupling error as an integral of the joint integrand. -/
theorem b3ton_inner {n : ℕ} (k : ℕ) (π : Measure (Space n × Space n)) (x : Space n) (r : ℝ) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
        ∫⁻ p in Prod.fst ⁻¹' Metric.ball x r, edist p.1 p.2 ^ 2 ∂π =
      ∫⁻ p, b3ton_kernel k ((x, r), p) ∂π := by
  have hs : MeasurableSet (Prod.fst ⁻¹' Metric.ball x r : Set (Space n × Space n)) :=
    measurable_fst measurableSet_ball
  have he : Measurable (fun p : Space n × Space n => edist p.1 p.2 ^ 2) :=
    (measurable_fst.edist measurable_snd).pow_const 2
  rw [← lintegral_indicator hs, ← lintegral_const_mul _ (he.indicator hs)]
  refine lintegral_congr fun p => ?_
  by_cases h : dist p.1 x < r
  · have hm : p ∈ (Prod.fst ⁻¹' Metric.ball x r : Set (Space n × Space n)) := h
    rw [Set.indicator_of_mem hm]
    simp only [b3ton_kernel, h, ↓reduceIte]
  · have hm : p ∉ (Prod.fst ⁻¹' Metric.ball x r : Set (Space n × Space n)) := h
    rw [Set.indicator_of_notMem hm, mul_zero]
    simp only [b3ton_kernel, h, ↓reduceIte]

theorem b3ton_couplingError_eq {n : ℕ} (k : ℕ) (π : Measure (Space n × Space n))
    (x : Space n) (R : ℝ) :
    b3_couplingError k π x R =
      ∫⁻ r in Ioo 0 R, ∫⁻ p, b3ton_kernel k ((x, r), p) ∂π ∂scaleMeasure :=
  lintegral_congr fun r => b3ton_inner k π x r

theorem b3ton_measurable_couplingError {n : ℕ} (k : ℕ) (π : Measure (Space n × Space n))
    [SFinite π] (R : ℝ) : Measurable (fun x => b3_couplingError k π x R) := by
  have hI : Measurable (fun q : Space n × ℝ => ∫⁻ p, b3ton_kernel k (q, p) ∂π) :=
    Measurable.lintegral_prod_right' (ν := π) (b3ton_measurable_kernel k)
  have h : (fun x => b3_couplingError k π x R) =
      fun x => ∫⁻ r in Ioo 0 R, ∫⁻ p, b3ton_kernel k ((x, r), p) ∂π ∂scaleMeasure :=
    funext fun x => b3ton_couplingError_eq k π x R
  rw [h]
  exact Measurable.lintegral_prod_right' (ν := scaleMeasure.restrict (Ioo 0 R)) hI

/-- The `x`-slice: `∫_D 1_{P(x,r)}(p.1) r^{-k-2} d^2 dσ(x) = d^2 r^{-k-2} σ(D ∩ P(p.1,r))`. -/
theorem b3ton_slice {n : ℕ} (k : ℕ) (σ : Measure (Space n)) (D : Set (Space n))
    (p : Space n × Space n) (r : ℝ) :
    ∫⁻ x in D, b3ton_kernel k ((x, r), p) ∂σ =
      edist p.1 p.2 ^ 2 * ((ENNReal.ofReal r)⁻¹ ^ (k + 2) * σ (D ∩ Metric.ball p.1 r)) := by
  have h : (fun x => b3ton_kernel k ((x, r), p)) =
      (Metric.ball p.1 r).indicator
        (fun _ => (ENNReal.ofReal r)⁻¹ ^ (k + 2) * edist p.1 p.2 ^ 2) := by
    funext x
    by_cases h : dist p.1 x < r
    · have hm : x ∈ Metric.ball p.1 r := by rw [Metric.mem_ball, dist_comm]; exact h
      rw [Set.indicator_of_mem hm]
      simp only [b3ton_kernel, h, ↓reduceIte]
    · have hm : x ∉ Metric.ball p.1 r := by rw [Metric.mem_ball, dist_comm]; exact h
      rw [Set.indicator_of_notMem hm]
      simp only [b3ton_kernel, h, ↓reduceIte]
  rw [h, lintegral_indicator_const measurableSet_ball,
    Measure.restrict_apply measurableSet_ball, inter_comm]
  ring

/-- **Tonelli identity for the coupling error** (`CouplingErrorTonelliStatement`). -/
theorem b3_couplingErrorTonelli_proof : CouplingErrorTonelliStatement := by
  intro n k σ hσ π hπ D _hD R
  have := hσ
  have := hπ
  refine ⟨b3ton_measurable_couplingError k π R, ?_⟩
  have hK := b3ton_measurable_kernel (n := n) k
  calc ∫⁻ x in D, b3_couplingError k π x R ∂σ
      = ∫⁻ x in D, ∫⁻ r in Ioo 0 R, ∫⁻ p, b3ton_kernel k ((x, r), p) ∂π ∂scaleMeasure ∂σ :=
        lintegral_congr fun x => b3ton_couplingError_eq k π x R
    _ = ∫⁻ x in D, ∫⁻ p, ∫⁻ r in Ioo 0 R, b3ton_kernel k ((x, r), p) ∂scaleMeasure ∂π ∂σ := by
        refine lintegral_congr fun x => ?_
        exact lintegral_lintegral_swap ((hK.comp
          (by fun_prop : Measurable fun q : ℝ × (Space n × Space n) => ((x, q.1), q.2))
          ).aemeasurable)
    _ = ∫⁻ p, ∫⁻ x in D, ∫⁻ r in Ioo 0 R, b3ton_kernel k ((x, r), p) ∂scaleMeasure ∂σ ∂π := by
        refine lintegral_lintegral_swap ?_
        exact (Measurable.lintegral_prod_right' (ν := scaleMeasure.restrict (Ioo 0 R))
          (hK.comp (by fun_prop : Measurable
            fun q : (Space n × (Space n × Space n)) × ℝ => ((q.1.1, q.2), q.1.2)))).aemeasurable
    _ = ∫⁻ p, ∫⁻ r in Ioo 0 R, ∫⁻ x in D, b3ton_kernel k ((x, r), p) ∂σ ∂scaleMeasure ∂π := by
        refine lintegral_congr fun p => ?_
        exact lintegral_lintegral_swap ((hK.comp
          (by fun_prop : Measurable fun q : Space n × ℝ => (q, p))).aemeasurable)
    _ = ∫⁻ p, edist p.1 p.2 ^ 2 * b3_errorWeight k σ D p.1 R ∂π := by
        refine lintegral_congr fun p => ?_
        rw [b3_errorWeight, ← lintegral_const_mul' _ _ (b3ton_edist_sq_ne_top p)]
        exact lintegral_congr fun r => b3ton_slice k σ D p r

end ParabolicRectifiability.Characterization.SourceTransferTree
