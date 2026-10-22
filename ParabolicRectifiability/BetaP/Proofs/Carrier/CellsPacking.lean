import ParabolicRectifiability.BetaP.Proofs.Carrier.CarrierStatements

/-! # Barycenter cells into the truncated active-radius packing

Proves `ccar_cells_packing : CellsFitTransferStatement → CellsPackingStatement`, following the
quadratic `sum_weight_le_of_barycenterCells`:

1. infimum: the fixed-model transfer (the hypothesis `CellsFitTransferStatement`) gives
   `⨅_L fit_p(λ_s; L, c_i, s) ≤ A ⨅_L fit_p(ν; L, y_i, 2s)` (`ccart_fittingInfimum_le`);
2. beta transfer: `s^{-k-p} = 2^{k+p} (2s)^{-k-p}` gives
   `B_p(λ_s; c_i, s) ≤ A 2^{k+p} B_p(ν; y_i, 2s)` for `s ≥ ρ_i` (`ccart_betaPow_atomicMeasure_le`);
3. radius measurability of `u ↦ B_{p,ν}(y,u)` from monotonicity of the unnormalized fitting
   infimum (`ccart_measurable_betaPow_radius`, as `measurable_betaSq_monotone_source`; no
   joint beta-measurability or attainment input);
4. integrated transfer: raising to `2/p`, the substitution `u = 2s` (which keeps `ds/s`) and
   enlarging to `(0,∞)` give
   `∫_{ρ_i}^∞ B_p(λ_s; c_i, s)^{2/p} ds/s ≤ (A 2^{k+p})^{2/p} ∫_0^∞ B_p(ν; y_i, u)^{2/p} du/u`
   (`ccart_atomicEnergy_le`);
5. packing: with packing coefficients `w_j / ρ_j^k` the truncated testing source is exactly
   `λ_s`, the atomic masses are `w_j`, and `B = (A 2^{k+p})^{2/p} L` has
   `B^{p/2} = A 2^{k+p} L^{p/2}` (also for `A = 0` or `L = 0`).

Helpers are prefixed `ccart_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP.CarrierTree

open ParabolicRectifiability.Foundations

variable {n : ℕ}

/-- Radius normalization: `(ofReal s)⁻¹^e = ofReal (2^e) · (ofReal (2s))⁻¹^e` for `s > 0`,
`e ≥ 0`. -/
theorem ccart_inv_rpow_eq {s e : ℝ} (hs : 0 < s) (he : 0 ≤ e) :
    (ENNReal.ofReal s)⁻¹ ^ e =
      ENNReal.ofReal ((2 : ℝ) ^ e) * (ENNReal.ofReal (2 * s))⁻¹ ^ e := by
  have hs2 : 0 < 2 * s := by linarith
  rw [← ENNReal.ofReal_inv_of_pos hs, ← ENNReal.ofReal_inv_of_pos hs2,
    ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hs.le) he,
    ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hs2.le) he,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  congr 1
  have h2 : (0 : ℝ) < 2 ^ e := Real.rpow_pos_of_pos (by norm_num) e
  rw [mul_inv, Real.mul_rpow (by norm_num) (inv_nonneg.mpr hs.le),
    Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc, mul_inv_cancel₀ h2.ne', one_mul]

/-- Infimum step: the fixed-model transfer for every model of the (nonempty) family. -/
theorem ccart_fittingInfimum_le (hfit : CellsFitTransferStatement) {k : ℕ} {T : FamilyKind}
    [Nonempty (Models n k T)] {p : ℝ} (hp : 2 ≤ p) {ν : Measure (Space n)} {l : ℕ}
    (D : FiniteBarycenterCells ν (Fin l)) (i : Fin l) {s : ℝ} (hs : D.cutoff i ≤ s) :
    (⨅ L : Models n k T, fitPow (D.atomicMeasure s) p L (D.barycenter i) s) ≤
      ENNReal.ofReal D.A * ⨅ L : Models n k T, fitPow ν p L (D.sample i) (2 * s) := by
  rw [ENNReal.mul_iInf (fun h => (ENNReal.ofReal_ne_top h).elim)]
  exact iInf_mono fun L => hfit n k T p hp ν l D i s hs L

/-- **Beta transfer**: `B_p(λ_s; c_i, s) ≤ A 2^{k+p} B_p(ν; y_i, 2s)` for `s ≥ ρ_i`. -/
theorem ccart_betaPow_atomicMeasure_le (hfit : CellsFitTransferStatement) {k : ℕ}
    {T : FamilyKind} [Nonempty (Models n k T)] {p : ℝ} (hp : 2 ≤ p) {ν : Measure (Space n)}
    {l : ℕ} (D : FiniteBarycenterCells ν (Fin l)) (i : Fin l) {s : ℝ} (hs : D.cutoff i ≤ s) :
    betaPow (D.atomicMeasure s) k T p (D.barycenter i) s ≤
      ENNReal.ofReal (D.A * (2 : ℝ) ^ ((k : ℝ) + p)) * betaPow ν k T p (D.sample i) (2 * s) := by
  have hs0 : 0 < s := (D.cutoff_pos i).trans_le hs
  have hs2 : 0 < 2 * s := by linarith
  have he : 0 ≤ (k : ℝ) + p := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  unfold betaPow
  rw [ite_eq_left hs0, ite_eq_left hs2, ccart_inv_rpow_eq hs0 he, ENNReal.ofReal_mul D.A_nonneg]
  calc ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) + p)) * (ENNReal.ofReal (2 * s))⁻¹ ^ ((k : ℝ) + p) *
        ⨅ L : Models n k T, fitPow (D.atomicMeasure s) p L (D.barycenter i) s
      ≤ ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) + p)) * (ENNReal.ofReal (2 * s))⁻¹ ^ ((k : ℝ) + p) *
        (ENNReal.ofReal D.A * ⨅ L : Models n k T, fitPow ν p L (D.sample i) (2 * s)) :=
        mul_le_mul_of_nonneg_left (ccart_fittingInfimum_le hfit hp D i hs) zero_le
    _ = _ := by ring

/-- **Radius measurability** of `u ↦ B_{p,ν}(y,u)`: the unnormalized fitting infimum is monotone
in the radius (every fixed-model integral is), and the prefactor is measurable. No joint
measurability, no countable family and no attainment is used. -/
theorem ccart_measurable_betaPow_radius (ν : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (p : ℝ) (z : Space n) : Measurable (fun r => betaPow ν k T p z r) := by
  have hfit : Monotone (fun r => ⨅ L : Models n k T, fitPow ν p L z r) := by
    intro r s hrs
    exact iInf_mono fun L => lintegral_mono_set (Metric.ball_subset_ball hrs)
  unfold betaPow
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    ((measurable_id.ennreal_ofReal.inv.pow_const ((k : ℝ) + p)).mul hfit.measurable)
    measurable_const

/-- **Integrated transfer**: the truncated-source energy above the cutoff is at most
`(A 2^{k+p})^{2/p}` times the all-scale energy of the sample (substitution `u = 2s`, `ds/s`
preserved, no extra factor). -/
theorem ccart_atomicEnergy_le (hfit : CellsFitTransferStatement) {k : ℕ} {T : FamilyKind}
    [Nonempty (Models n k T)] {p : ℝ} (hp : 2 ≤ p) {ν : Measure (Space n)} {l : ℕ}
    (D : FiniteBarycenterCells ν (Fin l)) (i : Fin l) :
    (∫⁻ s in Ioi (D.cutoff i),
        betaPow (D.atomicMeasure s) k T p (D.barycenter i) s ^ (2 / p) ∂scaleMeasure) ≤
      ENNReal.ofReal (D.A * (2 : ℝ) ^ ((k : ℝ) + p)) ^ (2 / p) *
        allScaleEnergyP ν k T p (D.sample i) := by
  have h2p : 0 ≤ 2 / p := div_nonneg zero_le_two (by linarith)
  have hc : ENNReal.ofReal (D.A * (2 : ℝ) ^ ((k : ℝ) + p)) ^ (2 / p) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg h2p ENNReal.ofReal_ne_top
  have hg : Measurable (fun u => betaPow ν k T p (D.sample i) u ^ (2 / p)) :=
    (ccart_measurable_betaPow_radius ν k T p (D.sample i)).pow_const _
  calc
    _ ≤ ∫⁻ s in Ioi (D.cutoff i), ENNReal.ofReal (D.A * (2 : ℝ) ^ ((k : ℝ) + p)) ^ (2 / p) *
        betaPow ν k T p (D.sample i) (2 * s) ^ (2 / p) ∂scaleMeasure := by
      refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
      rw [← ENNReal.mul_rpow_of_nonneg _ _ h2p]
      exact ENNReal.rpow_le_rpow (ccart_betaPow_atomicMeasure_le hfit hp D i (le_of_lt hs)) h2p
    _ = ENNReal.ofReal (D.A * (2 : ℝ) ^ ((k : ℝ) + p)) ^ (2 / p) *
        ∫⁻ s in Ioi (D.cutoff i), betaPow ν k T p (D.sample i) (2 * s) ^ (2 / p)
          ∂scaleMeasure :=
      lintegral_const_mul' _ _ hc
    _ = ENNReal.ofReal (D.A * (2 : ℝ) ^ ((k : ℝ) + p)) ^ (2 / p) *
        ∫⁻ u in Ioi (2 * D.cutoff i), betaPow ν k T p (D.sample i) u ^ (2 / p)
          ∂scaleMeasure := by
      rw [lintegral_comp_two_Ioi_scaleMeasure (D.cutoff_pos i) _ hg]
    _ ≤ ENNReal.ofReal (D.A * (2 : ℝ) ^ ((k : ℝ) + p)) ^ (2 / p) *
        ∫⁻ u in Ioi 0, betaPow ν k T p (D.sample i) u ^ (2 / p) ∂scaleMeasure :=
      mul_le_mul_of_nonneg_left
        (lintegral_mono_set (Ioi_subset_Ioi (mul_pos two_pos (D.cutoff_pos i)).le)) zero_le
    _ = _ := rfl

/-- The packing exponent identity `((A 2^{k+p})^{2/p} L)^{p/2} = A 2^{k+p} L^{p/2}` for
`κ = A 2^{k+p} ≥ 0`, `L ≥ 0` (including `κ = 0` or `L = 0`). -/
theorem ccart_rpow_energy_eq {κ L p : ℝ} (hκ : 0 ≤ κ) (hL : 0 ≤ L) (hp : p ≠ 0) :
    (κ ^ (2 / p) * L) ^ (p / 2) = κ * L ^ (p / 2) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hκ _) hL, ← Real.rpow_mul hκ,
    show 2 / p * (p / 2) = (1 : ℝ) by field_simp, Real.rpow_one]

/-- **Barycenter cells into the truncated packing** (`ccar_cells_packing`:
`CellsFitTransferStatement → CellsPackingStatement`). -/
theorem ccar_cells_packing_proof : CellsFitTransferStatement → CellsPackingStatement := by
  intro hfit n p Ct hp hbound k T hk hkn hT ν l D L hL hsample q R b hR hb hball hdisj hw
  have := hT
  have hp0 : p ≠ 0 := by linarith
  have h2p : 0 ≤ 2 / p := div_nonneg zero_le_two (by linarith)
  have hκ : 0 ≤ D.A * (2 : ℝ) ^ ((k : ℝ) + p) :=
    mul_nonneg D.A_nonneg (Real.rpow_nonneg zero_le_two _)
  have hB : 0 ≤ (D.A * (2 : ℝ) ^ ((k : ℝ) + p)) ^ (2 / p) * L :=
    mul_nonneg (Real.rpow_nonneg hκ _) hL
  have hcut : ∀ i, 0 < D.cutoff i ^ k := fun i => pow_pos (D.cutoff_pos i) k
  have hcancel : ∀ i, D.weight i / D.cutoff i ^ k * D.cutoff i ^ k = D.weight i :=
    fun i => div_mul_cancel₀ _ (hcut i).ne'
  have hsrc : ∀ s, BetaP.truncatedAtomicSource k D.barycenter D.cutoff
      (fun j => D.weight j / D.cutoff j ^ k) s = D.atomicMeasure s := by
    intro s
    have h : BetaP.truncatedAtomicSource k D.barycenter D.cutoff
        (fun j => D.weight j / D.cutoff j ^ k) s =
        ParabolicRectifiability.truncatedAtomicSource k D.barycenter D.cutoff
          (fun j => D.weight j / D.cutoff j ^ k) s := rfl
    rw [h, truncatedAtomicSource_eq_finiteCutoffAtomicMeasure]
    simp only [hcancel]
    rfl
  have henergy : ∀ i, (∫⁻ s in Ioi (D.cutoff i),
      betaPow (BetaP.truncatedAtomicSource k D.barycenter D.cutoff
        (fun j => D.weight j / D.cutoff j ^ k) s) k T p (D.barycenter i) s ^ (2 / p)
        ∂scaleMeasure) ≤ ENNReal.ofReal ((D.A * (2 : ℝ) ^ ((k : ℝ) + p)) ^ (2 / p) * L) := by
    intro i
    simp only [hsrc]
    calc _ ≤ ENNReal.ofReal (D.A * (2 : ℝ) ^ ((k : ℝ) + p)) ^ (2 / p) *
          allScaleEnergyP ν k T p (D.sample i) := ccart_atomicEnergy_le hfit hp D i
      _ ≤ ENNReal.ofReal (D.A * (2 : ℝ) ^ ((k : ℝ) + p)) ^ (2 / p) * ENNReal.ofReal L :=
          mul_le_mul_of_nonneg_left (hsample i) zero_le
      _ = _ := by
          rw [ENNReal.ofReal_rpow_of_nonneg hκ h2p,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hκ _)]
  have hpack : BetaP.IsWeightedPacking q R D.barycenter D.cutoff
      (fun j => D.weight j / D.cutoff j ^ k) b :=
    { radius_pos := D.cutoff_pos
      ball_subset := hball
      pairwise_disjoint := hdisj
      weight_pos := fun i => div_pos (D.weight_pos i) (hcut i)
      weight_le := fun i => (div_le_iff₀ (hcut i)).mpr (hw i) }
  have key := hbound k hk hkn T hT q R hR l D.barycenter D.cutoff
    (fun j => D.weight j / D.cutoff j ^ k) b _ hpack hB henergy
  have hmass : BetaP.atomicSource k D.barycenter D.cutoff
      (fun j => D.weight j / D.cutoff j ^ k) univ = ∑ i, ENNReal.ofReal (D.weight i) := by
    simp only [BetaP.atomicSource, Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one, hcancel]
  rw [hmass, ccart_rpow_energy_eq hκ hL hp0] at key
  exact key

end ParabolicRectifiability.BetaP.CarrierTree
