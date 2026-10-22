import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.TransferStatements
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Recentering
import ParabolicRectifiability.Measure.BetaLaws

/-! # The coupling inequality for square energies

Proves `CouplingEnergyStatement` (`b3_couplingEnergy_proof`): if a finite coupling `π` of
`μ = π.fst` and `ν = π.snd` sends pairs starting in `P(z,r)` into `P(z,ar)` for `0 < r < R`, then
`S^R_μ(z) ≤ 2 a^{k+2} S^{aR}_ν(z) + 2 e(z,R)`, where `e` is the coupling error
`b3_couplingError`.

Proof. For a fixed model `L` and a fixed radius `0 < r < R`, the triangle inequality for the
distance to `L` and `(x+y)^2 ≤ 2x^2 + 2y^2` give
`d(y,L)^2 ≤ 2 d(v,L)^2 + 2 d(y,v)^2`; integrating against `π` over `{y ∈ P(z,r)}` and using
the localization at this radius (its exceptional `π`-null set may depend on `r`) gives
`fit_μ(L;z,r) ≤ 2 fit_ν(L;z,ar) + 2 e(r)`. Only then the infimum over `L` is taken
(`ENNReal.iInf_add`, `ENNReal.mul_iInf_of_ne`; an empty family gives `⊤ ≤ ⊤`). The radius
normalization `r^{-k-2} = a^{k+2} (ar)^{-k-2}` gives the pointwise bound on `betaSq`, and the
dilation invariance of `dr/r` (`setLIntegral_scaleMeasure_comp_const_mul`) identifies
`∫_0^R β_ν(z,ar) dr/r = S^{aR}_ν(z)`. Only the model term needs measurability
(`measurable_betaSq`, finite `ν`); the error term is put second in `lintegral_add_left` and
pulled out by `lintegral_const_mul'`, so no measurability of it is used.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.SourceTransferTree

open ParabolicRectifiability.Foundations

/-- `(x + y)^2 ≤ 2 (x^2 + y^2)` in `[0,∞]`. -/
theorem b3cpl_add_sq_le (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp
  lift x to NNReal using hx
  lift y to NNReal using hy
  exact_mod_cast add_sq_le (a := x) (b := y)

/-- Pointwise transport of the squared model distance along a displacement:
`d(y,L)^2 ≤ 2 d(v,L)^2 + 2 d(y,v)^2`. -/
theorem b3cpl_modelCost_le {n k : ℕ} {T : FamilyKind} (L : Models n k T)
    (p : Space n × Space n) :
    modelCost L p.1 ≤ 2 * modelCost L p.2 + 2 * edist p.1 p.2 ^ 2 := by
  unfold modelCost
  calc Metric.infEDist p.1 (modelSet L) ^ 2
      ≤ (Metric.infEDist p.2 (modelSet L) + edist p.1 p.2) ^ 2 :=
        pow_le_pow_left' Metric.infEDist_le_infEDist_add_edist 2
    _ ≤ 2 * (Metric.infEDist p.2 (modelSet L) ^ 2 + edist p.1 p.2 ^ 2) := b3cpl_add_sq_le _ _
    _ = 2 * Metric.infEDist p.2 (modelSet L) ^ 2 + 2 * edist p.1 p.2 ^ 2 := mul_add _ _ _

/-- **Fixed-plane inequality** at one radius, before any infimum:
`fit_{π.fst}(L;z,r) ≤ 2 fit_{π.snd}(L;z,s) + 2 ∫_{p.1 ∈ P(z,r)} d(p.1,p.2)^2 dπ`,
when `π`-a.e. pair starting in `P(z,r)` ends in `P(z,s)`. -/
theorem b3cpl_fit_le {n k : ℕ} {T : FamilyKind} (π : Measure (Space n × Space n))
    (L : Models n k T) (z : Space n) {r s : ℝ}
    (hloc : ∀ᵐ p ∂π, p.1 ∈ Metric.ball z r → p.2 ∈ Metric.ball z s) :
    fit π.fst L z r ≤ 2 * fit π.snd L z s +
      2 * ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, edist p.1 p.2 ^ 2 ∂π := by
  have hc := measurable_modelCost L
  have hSm : MeasurableSet (Prod.fst ⁻¹' Metric.ball z r : Set (Space n × Space n)) :=
    measurable_fst measurableSet_ball
  have hS'm : MeasurableSet (Prod.snd ⁻¹' Metric.ball z s : Set (Space n × Space n)) :=
    measurable_snd measurableSet_ball
  have h1 : fit π.fst L z r = ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, modelCost L p.1 ∂π := by
    rw [fit, Measure.fst, setLIntegral_map measurableSet_ball hc measurable_fst]
  have h2 : fit π.snd L z s = ∫⁻ p in Prod.snd ⁻¹' Metric.ball z s, modelCost L p.2 ∂π := by
    rw [fit, Measure.snd, setLIntegral_map measurableSet_ball hc measurable_snd]
  have h3 : ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, modelCost L p.2 ∂π ≤
      ∫⁻ p in Prod.snd ⁻¹' Metric.ball z s, modelCost L p.2 ∂π := by
    rw [← lintegral_indicator hSm, ← lintegral_indicator hS'm]
    refine lintegral_mono_ae (hloc.mono fun p hp => ?_)
    by_cases h : p ∈ (Prod.fst ⁻¹' Metric.ball z r : Set (Space n × Space n))
    · rw [indicator_of_mem h,
        indicator_of_mem (show p ∈ (Prod.snd ⁻¹' Metric.ball z s : Set (Space n × Space n))
          from hp h)]
    · rw [indicator_of_notMem h]
      exact bot_le
  have hm : Measurable fun p : Space n × Space n => 2 * modelCost L p.2 :=
    (hc.comp measurable_snd).const_mul 2
  calc fit π.fst L z r
      = ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, modelCost L p.1 ∂π := h1
    _ ≤ ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r,
          (2 * modelCost L p.2 + 2 * edist p.1 p.2 ^ 2) ∂π :=
        lintegral_mono fun p => b3cpl_modelCost_le L p
    _ = 2 * ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, modelCost L p.2 ∂π +
          2 * ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, edist p.1 p.2 ^ 2 ∂π := by
        rw [lintegral_add_left hm, lintegral_const_mul' (2 : ℝ≥0∞) _ (by simp),
          lintegral_const_mul' (2 : ℝ≥0∞) _ (by simp)]
    _ ≤ 2 * fit π.snd L z s +
          2 * ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, edist p.1 p.2 ^ 2 ∂π := by
        rw [h2]
        gcongr

/-- The plane infimum is taken **after** the fixed-plane comparison. -/
theorem b3cpl_iInf_fit_le {n k : ℕ} {T : FamilyKind} (π : Measure (Space n × Space n))
    (z : Space n) {r s : ℝ}
    (hloc : ∀ᵐ p ∂π, p.1 ∈ Metric.ball z r → p.2 ∈ Metric.ball z s) :
    ⨅ L : Models n k T, fit π.fst L z r ≤ 2 * (⨅ L : Models n k T, fit π.snd L z s) +
      2 * ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, edist p.1 p.2 ^ 2 ∂π := by
  rw [ENNReal.mul_iInf_of_ne (by simp) (by simp), ENNReal.iInf_add]
  exact iInf_mono fun L => b3cpl_fit_le π L z hloc

/-- Pointwise bound on the squared beta at one radius `r > 0`, dilation factor `a > 0`. -/
theorem b3cpl_betaSq_le {n k : ℕ} {T : FamilyKind} (π : Measure (Space n × Space n))
    (z : Space n) {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hloc : ∀ᵐ p ∂π, p.1 ∈ Metric.ball z r → p.2 ∈ Metric.ball z (a * r)) :
    betaSq π.fst k T z r ≤ ENNReal.ofReal (2 * a ^ (k + 2)) * betaSq π.snd k T z (a * r) +
      2 * ((ENNReal.ofReal r)⁻¹ ^ (k + 2) *
        ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, edist p.1 p.2 ^ 2 ∂π) := by
  have har : 0 < a * r := mul_pos ha hr
  rw [betaSq_of_pos _ _ _ _ hr, betaSq_of_pos _ _ _ _ har]
  have key := b3cpl_iInf_fit_le (k := k) (T := T) π z hloc
  have hrn := radius_ratio_normalization hr har (k + 2)
    (⨅ L : Models n k T, fit π.snd L z (a * r))
  rw [mul_div_cancel_right₀ a hr.ne'] at hrn
  have hc : ENNReal.ofReal (2 * a ^ (k + 2)) = 2 * ENNReal.ofReal a ^ (k + 2) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow ha.le, ENNReal.ofReal_ofNat]
  calc (ENNReal.ofReal r)⁻¹ ^ (k + 2) * ⨅ L : Models n k T, fit π.fst L z r
      ≤ (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (2 * (⨅ L : Models n k T, fit π.snd L z (a * r)) +
          2 * ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, edist p.1 p.2 ^ 2 ∂π) := by
        gcongr
    _ = 2 * ((ENNReal.ofReal r)⁻¹ ^ (k + 2) * ⨅ L : Models n k T, fit π.snd L z (a * r)) +
          2 * ((ENNReal.ofReal r)⁻¹ ^ (k + 2) *
            ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, edist p.1 p.2 ^ 2 ∂π) := by
        ring
    _ = _ := by
        rw [← hrn, hc]
        ring

/-- Dilation of `dr/r`: `∫_0^R β_ν(z, a r) dr/r = S^{aR}_ν(z)` for `a > 0`. -/
theorem b3cpl_setLIntegral_betaSq_dilate {n k : ℕ} {T : FamilyKind} (ν : Measure (Space n))
    (z : Space n) {R a : ℝ} (ha : 0 < a) :
    ∫⁻ r in Ioo 0 R, betaSq ν k T z (a * r) ∂scaleMeasure = squareEnergy ν k T (a * R) z := by
  have hpre : (fun s => a * s) ⁻¹' Ioo 0 (a * R) = Ioo 0 R := by
    ext s
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 ha.le, lt_of_mul_lt_mul_left h2 ha.le⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos ha h1, mul_lt_mul_of_pos_left h2 ha⟩
  have h := setLIntegral_scaleMeasure_comp_const_mul ha (betaSq ν k T z) (Ioo 0 (a * R))
  rw [hpre] at h
  exact h

/-- **Coupling inequality for square energies** (`CouplingEnergyStatement`). -/
theorem b3_couplingEnergy_proof : CouplingEnergyStatement := by
  intro n k T π hπ z R a hR ha hloc
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hpt : ∀ r ∈ Ioo 0 R, betaSq π.fst k T z r ≤
      ENNReal.ofReal (2 * a ^ (k + 2)) * betaSq π.snd k T z (a * r) +
        2 * ((ENNReal.ofReal r)⁻¹ ^ (k + 2) *
          ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, edist p.1 p.2 ^ 2 ∂π) :=
    fun r hr => b3cpl_betaSq_le π z hr.1 ha0 (hloc r hr.1 hr.2)
  have hmeas : Measurable fun r : ℝ =>
      ENNReal.ofReal (2 * a ^ (k + 2)) * betaSq π.snd k T z (a * r) :=
    ((measurable_betaSq π.snd k T).comp
      (measurable_const.prodMk (measurable_const_mul a))).const_mul _
  unfold b3_couplingError
  calc squareEnergy π.fst k T R z
      = ∫⁻ r in Ioo 0 R, betaSq π.fst k T z r ∂scaleMeasure := rfl
    _ ≤ ∫⁻ r in Ioo 0 R, (ENNReal.ofReal (2 * a ^ (k + 2)) * betaSq π.snd k T z (a * r) +
          2 * ((ENNReal.ofReal r)⁻¹ ^ (k + 2) *
            ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, edist p.1 p.2 ^ 2 ∂π)) ∂scaleMeasure :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = ENNReal.ofReal (2 * a ^ (k + 2)) *
          ∫⁻ r in Ioo 0 R, betaSq π.snd k T z (a * r) ∂scaleMeasure +
        2 * ∫⁻ r in Ioo 0 R, (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
            ∫⁻ p in Prod.fst ⁻¹' Metric.ball z r, edist p.1 p.2 ^ 2 ∂π ∂scaleMeasure := by
        rw [lintegral_add_left hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' (2 : ℝ≥0∞) _ (by simp)]
    _ = _ := by
        rw [b3cpl_setLIntegral_betaSq_dilate π.snd z ha0]

end ParabolicRectifiability.Characterization.SourceTransferTree
