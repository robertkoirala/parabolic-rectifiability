import ParabolicRectifiability.BetaP.Proofs.Packing.PackingStatements
import ParabolicRectifiability.Metric.ProperSpace

/-! # Hölder reduction

Proof of `cpk_holderReduction : CpkHolderReductionStatement`.

For an injection `e : Fin l → Fin N`, a subfamily centre `z_{e j}` and a scale `s > r_{e j}`,
let `σ'_s` be the quadratic truncated source of the subfamily and `σ_s` the `p`-testing source of the
whole family. Then
* `σ'_s ≤ σ_s` (injective sub-sum of labelled summands; `cpk2_subSource_le`);
* `σ'_s` is a finite measure (`cpk2_subSource_univ_lt_top`), hence finite on compacts and inner
  regular on the proper (so σ-compact, metrizable, Borel) space `Space n`;
* `Θ_{σ'_s}(z_{e j}, s) ≤ s^{-k} cpkActiveMass ≤ Λ` (`cpk2_densityRatio_le`);
* `B_2(σ'_s) = betaSq(σ'_s)`, Hölder clause 2 and monotonicity of `B_p` in the source
  give `betaSq(σ'_s) ≤ Λ^{1-2/p} B_p(σ_s)^{2/p}` pointwise; integrate over `s > r_{e j}` and pull
  the finite constant out of the lower integral.

The two visible `truncatedAtomicSource` definitions are qualified at every occurrence.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- `fitPow` is monotone in the source measure (as in `claws_betaPow_mono_measure`). -/
theorem cpk2_fitPow_mono_measure {n k : ℕ} {T : FamilyKind} {ν μ : Measure (Space n)}
    (h : ν ≤ μ) (p : ℝ) (L : Models n k T) (z : Space n) (r : ℝ) :
    fitPow ν p L z r ≤ fitPow μ p L z r :=
  lintegral_mono' (Measure.restrict_mono_measure h _) le_rfl

/-- `B_p` is monotone in the source measure (every family, centre and radius). -/
theorem cpk2_betaPow_mono_measure {n : ℕ} {ν μ : Measure (Space n)} (h : ν ≤ μ) (k : ℕ)
    (T : FamilyKind) (p : ℝ) (z : Space n) (r : ℝ) :
    betaPow ν k T p z r ≤ betaPow μ k T p z r := by
  unfold betaPow
  split_ifs
  · exact mul_le_mul' le_rfl (iInf_mono fun L => cpk2_fitPow_mono_measure h p L z r)
  · exact le_rfl

/-- The quadratic truncated atomic source has finite total mass (finite sum of finite multiples of
Dirac masses). -/
theorem cpk2_subSource_univ_lt_top {n l : ℕ} (k : ℕ) (z : Fin l → Space n) (r w : Fin l → ℝ)
    (s : ℝ) : _root_.ParabolicRectifiability.truncatedAtomicSource k z r w s univ < ⊤ := by
  unfold _root_.ParabolicRectifiability.truncatedAtomicSource
  rw [Measure.finsetSum_apply, ENNReal.sum_lt_top]
  intro j _
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.ofReal_lt_top

/-- The quadratic truncated atomic source is a finite measure. -/
theorem cpk2_subSource_isFiniteMeasure {n l : ℕ} (k : ℕ) (z : Fin l → Space n)
    (r w : Fin l → ℝ) (s : ℝ) :
    IsFiniteMeasure (_root_.ParabolicRectifiability.truncatedAtomicSource k z r w s) :=
  ⟨cpk2_subSource_univ_lt_top k z r w s⟩

/-- For an injection `e`, the subfamily's quadratic truncated source is dominated by the whole
family's `p`-testing source at the same scale (labelled summands; repeated centres allowed). -/
theorem cpk2_subSource_le {n N l : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ)
    (e : Fin l → Fin N) (he : Function.Injective e) (s : ℝ) :
    _root_.ParabolicRectifiability.truncatedAtomicSource k (fun m => z (e m))
        (fun m => r (e m)) (fun m => w (e m)) s ≤
      BetaP.truncatedAtomicSource k z r w s := by
  classical
  rw [Measure.le_iff']
  intro A
  unfold _root_.ParabolicRectifiability.truncatedAtomicSource BetaP.truncatedAtomicSource
  rw [Measure.finsetSum_apply, Measure.finsetSum_apply]
  have himg : (Finset.univ.filter (fun m => r (e m) ≤ s)).image e ⊆
      Finset.univ.filter (fun i => r i ≤ s) := by
    intro i hi
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨m, hm, rfl⟩ := hi
    exact hm
  calc ∑ m ∈ Finset.univ.filter (fun m => r (e m) ≤ s),
        (ENNReal.ofReal (w (e m) * r (e m) ^ k) • Measure.dirac (z (e m))) A
      = ∑ i ∈ (Finset.univ.filter (fun m => r (e m) ≤ s)).image e,
          (ENNReal.ofReal (w i * r i ^ k) • Measure.dirac (z i)) A :=
        (Finset.sum_image
          (f := fun i => (ENNReal.ofReal (w i * r i ^ k) • Measure.dirac (z i)) A)
          (fun a _ b _ hab => he hab)).symm
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => r i ≤ s),
          (ENNReal.ofReal (w i * r i ^ k) • Measure.dirac (z i)) A :=
        Finset.sum_le_sum_of_subset himg

/-- The `p`-testing source gives the open ball `P(x,s)` exactly the active mass at `(x,s)`. -/
theorem cpk2_source_ball_eq {n N : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ)
    (hr : ∀ i, 0 < r i) (hw : ∀ i, 0 < w i) (x : Space n) (s : ℝ) :
    BetaP.truncatedAtomicSource k z r w s (Metric.ball x s) =
      ENNReal.ofReal (cpkActiveMass k z r w x s) := by
  classical
  unfold BetaP.truncatedAtomicSource cpkActiveMass
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => (mul_pos (hw i) (pow_pos (hr i) k)).le),
    Measure.finsetSum_apply, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ measurableSet_ball]
  by_cases h1 : r i ≤ s <;> by_cases h2 : dist (z i) x < s <;>
    simp [h1, h2, Metric.mem_ball]

/-- Density bound for the subfamily source: `Θ_{σ'_s}(z_{e j}, s) ≤ Λ` at every `s > 0`. -/
theorem cpk2_densityRatio_le {n N l : ℕ} (k : ℕ) (z : Fin N → Space n) (r w : Fin N → ℝ)
    (Λ : ℝ) (hr : ∀ i, 0 < r i) (hw : ∀ i, 0 < w i) (hΛ0 : 0 ≤ Λ)
    (hΛ : CpkActiveDensityBound k z r w Λ) (e : Fin l → Fin N) (he : Function.Injective e)
    (j : Fin l) {s : ℝ} (hs : 0 < s) :
    densityRatio (_root_.ParabolicRectifiability.truncatedAtomicSource k (fun m => z (e m))
        (fun m => r (e m)) (fun m => w (e m)) s) k (z (e j)) s ≤ ENNReal.ofReal Λ := by
  unfold densityRatio
  apply ENNReal.div_le_of_le_mul
  calc _root_.ParabolicRectifiability.truncatedAtomicSource k (fun m => z (e m))
          (fun m => r (e m)) (fun m => w (e m)) s (Metric.ball (z (e j)) s)
      ≤ BetaP.truncatedAtomicSource k z r w s (Metric.ball (z (e j)) s) :=
        Measure.le_iff'.1 (cpk2_subSource_le k z r w e he s) _
    _ = ENNReal.ofReal (cpkActiveMass k z r w (z (e j)) s) :=
        cpk2_source_ball_eq k z r w hr hw _ s
    _ ≤ ENNReal.ofReal (Λ * s ^ k) := ENNReal.ofReal_le_ofReal (hΛ _ _ hs)
    _ = ENNReal.ofReal Λ * ENNReal.ofReal s ^ k := by
        rw [ENNReal.ofReal_mul hΛ0, ENNReal.ofReal_pow hs.le]

/-- **Hölder reduction** (`CpkHolderReductionStatement`). -/
theorem cpk_holderReduction_proof : CpkHolderReductionStatement := by
  intro hHolder hTwo n hn k hk hkn T hT p hp N z r w B Λ hr hw _hB hΛ0 hΛ hint l e he j
  have hp0 : 0 < p := by linarith
  have hα : 0 ≤ 1 - 2 / p := by
    have : 2 / p ≤ 1 := (div_le_one hp0).2 hp
    linarith
  have h2p : 0 ≤ 2 / p := (div_pos two_pos hp0).le
  have hkn' : k ≤ n + 2 := hkn.le
  have hpt : ∀ s ∈ Ioi (r (e j)),
      betaSq (_root_.ParabolicRectifiability.truncatedAtomicSource k (fun m => z (e m))
          (fun m => r (e m)) (fun m => w (e m)) s) k T (z (e j)) s ≤
        ENNReal.ofReal Λ ^ (1 - 2 / p) *
          betaPow (BetaP.truncatedAtomicSource k z r w s) k T p (z (e j)) s ^ (2 / p) := by
    intro s hs
    have hs0 : 0 < s := lt_trans (hr (e j)) hs
    have := cpk2_subSource_isFiniteMeasure k (fun m => z (e m)) (fun m => r (e m))
      (fun m => w (e m)) s
    rw [← hTwo n hn k hk hkn' T _ (z (e j)) s]
    refine ((hHolder n hn k hk hkn' T hT _ inferInstance inferInstance (z (e j)) s hs0).2 p
      hp).trans ?_
    exact mul_le_mul'
      (ENNReal.rpow_le_rpow (cpk2_densityRatio_le k z r w Λ hr hw hΛ0 hΛ e he j hs0) hα)
      (ENNReal.rpow_le_rpow
        (cpk2_betaPow_mono_measure (cpk2_subSource_le k z r w e he s) k T p (z (e j)) s) h2p)
  calc (∫⁻ s in Ioi (r (e j)),
        betaSq (_root_.ParabolicRectifiability.truncatedAtomicSource k (fun m => z (e m))
          (fun m => r (e m)) (fun m => w (e m)) s) k T (z (e j)) s ∂scaleMeasure)
      ≤ ∫⁻ s in Ioi (r (e j)), ENNReal.ofReal Λ ^ (1 - 2 / p) *
          betaPow (BetaP.truncatedAtomicSource k z r w s) k T p (z (e j)) s ^ (2 / p)
            ∂scaleMeasure :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal Λ ^ (1 - 2 / p) * ∫⁻ s in Ioi (r (e j)),
          betaPow (BetaP.truncatedAtomicSource k z r w s) k T p (z (e j)) s ^ (2 / p)
            ∂scaleMeasure :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hα ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal Λ ^ (1 - 2 / p) * ENNReal.ofReal B := mul_le_mul' le_rfl (hint (e j))
    _ = ENNReal.ofReal (Λ ^ (1 - 2 / p) * B) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hΛ0 hα, ENNReal.ofReal_mul (Real.rpow_nonneg hΛ0 _)]

end ParabolicRectifiability.BetaP
