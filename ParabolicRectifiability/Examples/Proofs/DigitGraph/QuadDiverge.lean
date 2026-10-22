import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Divergence of the quadratic energy

Quadratic divergence from disjoint bands with harmonic lower bounds: if `β_{2,ν}(z,r)^2 ≥ δ_j/1024`
on `[3h_j, 4h_j]` for all large `j`, then `S_{2,ν}^a(z) = ∞` for every `a > 0`, since the bands
are disjoint, each has `dr/r`-length `log(4/3)`, and `Σ δ_j = ∞` (`e2_sb_quadDiverge_proof`). -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal Function
namespace ParabolicRectifiability.Examples
open ParabolicRectifiability.Foundations
open ParabolicRectifiability.BetaP (Plane)

private theorem band_mass {h : ℝ} (hh : 0 < h) :
    scaleMeasure (Ioo (3 * h) (4 * h)) = ENNReal.ofReal (Real.log (4 / 3)) := by
  have ha : 0 < 3 * h := by positivity
  have hab : 3 * h ≤ 4 * h := by linarith
  rw [scaleMeasure_apply _ measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo (3 * h) (4 * h) ⊆ Ioi 0 from fun r hr => ha.trans hr.1)]
  have hc : ContinuousOn (fun r : ℝ => 1 / r) (Icc (3 * h) (4 * h)) :=
    continuousOn_const.div continuousOn_id fun r hr => (ha.trans_le hr.1).ne'
  have hi : IntegrableOn (fun r : ℝ => 1 / r) (Ioo (3 * h) (4 * h)) volume :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
      integral_one_div_of_pos ha (ha.trans_le hab)]
    congr 1
    field_simp [ne_of_gt hh]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (one_div_pos.mpr (ha.trans hr.1)).le

private theorem harmonic_band_weights (J : ℕ) :
    (∑' n : ℕ, ENNReal.ofReal (e2_sbDelta (n + J) / 1024)) = ⊤ := by
  by_contra ht
  have hs := ENNReal.summable_toReal ht
  have hnon (n : ℕ) : 0 ≤ e2_sbDelta (n + J) / 1024 := by
    unfold e2_sbDelta
    positivity
  simp only [ENNReal.toReal_ofReal (hnon _)] at hs
  have hd : Summable (fun n : ℕ => e2_sbDelta (n + J)) := by
    simpa only [div_mul_cancel₀ _ (by norm_num : (1024 : ℝ) ≠ 0)] using hs.mul_right 1024
  have hh : Summable (fun n : ℕ => 1 / ((n + (J + 1) : ℕ) : ℝ)) := by
    simpa only [e2_sbDelta, Nat.cast_add, Nat.cast_one, add_assoc] using hd
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff (J + 1)).mp hh)

/-- The band hypothesis forces infinite energy at every positive upper cutoff. -/
theorem e2_sb_quadDiverge_proof (hG : E2sbGrid) (hT : E2sbTails) : E2sbQuadDiverge := by
  intro ν z hband a ha
  have hHpos := hG.2.1
  have hdec := hT.2.2.2.2.2.2.2.1
  have hzero := hT.2.2.2.2.2.2.2.2
  have hsmall : ∀ᶠ j in atTop, e2_sbH j < a / 4 :=
    hzero.eventually (gt_mem_nhds (show (0 : ℝ) < a / 4 by positivity))
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hband.and (hsmall.and (eventually_ge_atTop 1)))
  have hsep (j : ℕ) (hj : 1 ≤ j) : 4 * e2_sbH (j + 1) < 3 * e2_sbH j := by
    have ht := hT.2.1 j hj
    have hd := (hG.2.2.2.2.2.2.2.2 j hj).2
    have hp : (1 : ℝ) ≤ 2 ^ (j + 31) := one_le_pow₀ (by norm_num)
    have hmul : e2_sbDelta j * e2_sbH j ≤ e2_sbH j / 2 := by
      nlinarith [hHpos j]
    have hb : e2_sbH (j + 1) ≤ e2_sbDelta j * e2_sbH j :=
      ht.trans (div_le_self (mul_nonneg ((hG.2.2.2.2.2.2.2.2 j hj).1.le) (hHpos j).le) hp)
    nlinarith [hHpos j]
  let B : ℕ → Set ℝ := fun n => Ioo (3 * e2_sbH (n + J)) (4 * e2_sbH (n + J))
  have hdis : Pairwise (Disjoint on B) := by
    apply (pairwise_disjoint_on B).mpr
    intro n m hlt
    apply Set.disjoint_left.2
    intro r hn hm
    have hle : e2_sbH (m + J) ≤ e2_sbH (n + J + 1) :=
      hdec.antitone (by omega)
    have hs := hsep (n + J) ((hJ (n + J) (by omega)).2.2)
    change 3 * e2_sbH (n + J) < r ∧ r < 4 * e2_sbH (n + J) at hn
    change 3 * e2_sbH (m + J) < r ∧ r < 4 * e2_sbH (m + J) at hm
    linarith
  have hsub : (⋃ n, B n) ⊆ Ioo 0 a := by
    intro r hr
    obtain ⟨n, hn⟩ := mem_iUnion.1 hr
    have hh := hJ (n + J) (by omega)
    change 3 * e2_sbH (n + J) < r ∧ r < 4 * e2_sbH (n + J) at hn
    constructor
    · nlinarith [hHpos (n + J)]
    · linarith [hh.2.1]
  have hlower (n : ℕ) :
      ENNReal.ofReal (e2_sbDelta (n + J) / 1024) * ENNReal.ofReal (Real.log (4 / 3)) ≤
        ∫⁻ r in B n, euclideanBetaPow ν 1 2 z r ∂scaleMeasure := by
    rw [← band_mass (hHpos (n + J)), ← setLIntegral_const]
    apply setLIntegral_mono' measurableSet_Ioo
    intro r hr
    exact (hJ (n + J) (by omega)).1 r hr.1.le hr.2.le
  have hlog : ENNReal.ofReal (Real.log (4 / 3)) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.log_pos (by norm_num)))
  apply top_unique
  calc
    ⊤ = (∑' n : ℕ, ENNReal.ofReal (e2_sbDelta (n + J) / 1024)) *
        ENNReal.ofReal (Real.log (4 / 3)) := by
      rw [harmonic_band_weights J, ENNReal.top_mul hlog]
    _ = ∑' n : ℕ, ENNReal.ofReal (e2_sbDelta (n + J) / 1024) *
        ENNReal.ofReal (Real.log (4 / 3)) := ENNReal.tsum_mul_right.symm
    _ ≤ ∑' n : ℕ, ∫⁻ r in B n, euclideanBetaPow ν 1 2 z r ∂scaleMeasure :=
      ENNReal.tsum_le_tsum hlower
    _ = ∫⁻ r in ⋃ n, B n, euclideanBetaPow ν 1 2 z r ∂scaleMeasure :=
      (lintegral_iUnion (fun _ => measurableSet_Ioo) hdis _).symm
    _ ≤ ∫⁻ r in Ioo 0 a, euclideanBetaPow ν 1 2 z r ∂scaleMeasure := lintegral_mono_set hsub
    _ = euclideanEnergyS ν 1 2 a z := by
      simp only [euclideanEnergyS, div_self (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one]

end ParabolicRectifiability.Examples
