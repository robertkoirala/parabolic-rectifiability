import ParabolicRectifiability.Characterization.Proofs.Fourier.SpatialAffineMultiplier

/-! # The spatial Fourier energy from translate differences

The right side of the global spatial estimate `b1sas_spatial_global` is
`∫ |ξ|² |Ĝ(ξ)|² dξ = (4π²)⁻¹ ‖∇G‖₂²`. It is bounded here by difference quotients, which is the
form in which it is applied to a Lipschitz `G` with compact support in
`ba1_spatial_affine_square_proof`: if `∫ |G(x + t e_j) - G(x)|² dx ≤ A t²` for every coordinate `j` and every step
`t = 1/(n+1)`, then `∫ |ξ|² |Ĝ|² ≤ k A / 16`.

Proof: Plancherel for one translate (`b1sas_lintegral_comb_sq`), the lower bound
`|e(y) - 1|² = 4 sin²(πy) ≥ 16 y²` for `|y| ≤ 1/2` (Jordan's inequality `Real.mul_le_sin`), and
monotone convergence over the increasing frequency slabs `{2|ξ_j| ≤ n + 1}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

variable {k : ℕ}

/-- `|e(y) - 1|² ≥ 16 y²` for `|y| ≤ 1/2`. -/
theorem b1sas_char_sub_one_sq_ge {y : ℝ} (hy : |y| ≤ 1 / 2) :
    16 * y ^ 2 ≤ ‖(𝐞 y : ℂ) - 1‖ ^ 2 := by
  have hpi : 0 < π := Real.pi_pos
  have hn : ‖(𝐞 y : ℂ) - 1‖ = ‖2 * Real.sin (π * y)‖ := by
    rw [Real.fourierChar_apply, mul_comm ((2 * π * y : ℝ) : ℂ) Complex.I,
      Complex.norm_exp_I_mul_ofReal_sub_one, show 2 * π * y / 2 = π * y by ring]
  have h1 : 2 * |y| ≤ Real.sin (π * |y|) := by
    have hx0 : 0 ≤ π * |y| := by positivity
    have hx1 : π * |y| ≤ π / 2 := by nlinarith [abs_nonneg y]
    have h := Real.mul_le_sin hx0 hx1
    have hpi' : π ≠ 0 := hpi.ne'
    have e : 2 / π * (π * |y|) = 2 * |y| := by field_simp
    linarith
  have h2 : Real.sin (π * y) ^ 2 = Real.sin (π * |y|) ^ 2 := by
    rcases abs_choice y with h | h
    · rw [h]
    · rw [h, mul_neg, Real.sin_neg, neg_sq]
  have h3 : (2 * |y|) ^ 2 ≤ Real.sin (π * |y|) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h4 : (2 * |y|) ^ 2 = 4 * y ^ 2 := by
    rw [mul_pow, sq_abs]
    norm_num
  rw [hn, Real.norm_eq_abs, sq_abs, mul_pow, h2]
  nlinarith

/-- Plancherel for one coordinate translate: `∫ |G(x + t e_j) - G(x)|² = ∫ |e(tξ_j) - 1|² |Ĝ|²`. -/
theorem b1sas_lintegral_translate_sq {G : Spatial k → ℝ} (hG : MemLp G 2 volume) (j : Fin k)
    (t : ℝ) :
    ∫⁻ x, ‖G (x + t • b1sas_unit j) - G x‖ₑ ^ 2 =
      ∫⁻ ξ, ‖(𝐞 (t * ξ j) : ℂ) - 1‖ₑ ^ 2 *
        ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 := by
  have h := b1sas_lintegral_comb_sq (Finset.univ : Finset Unit) (fun _ => (1 : ℝ))
    (fun _ => t • b1sas_unit j) hG
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, b1sas_mult,
    Complex.ofReal_one, real_inner_smul_left, b1sas_inner_unit] at h
  exact h

/-- The frequency slabs `{2|ξ_j| ≤ n + 1}`. -/
def b1sas_slab (j : Fin k) (n : ℕ) : Set (Spatial k) := {ξ | 2 * |ξ j| ≤ (n : ℝ) + 1}

theorem b1sas_measurableSet_slab (j : Fin k) (n : ℕ) : MeasurableSet (b1sas_slab j n) :=
  measurableSet_le ((continuous_const.mul
    ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.abs)).measurable) measurable_const

/-- One slab: `∫_{2|ξ_j| ≤ n+1} ξ_j² |Ĝ|² ≤ A / 16` from the translate bound at `t = 1/(n+1)`. -/
theorem b1sas_slab_le {G : Spatial k → ℝ} (hG : MemLp G 2 volume) (j : Fin k) {A : ℝ}
    (_hA : 0 ≤ A) (n : ℕ)
    (htr : ∫⁻ x, ‖G (x + (1 / ((n : ℝ) + 1)) • b1sas_unit j) - G x‖ₑ ^ 2 ≤
      ENNReal.ofReal (A * (1 / ((n : ℝ) + 1)) ^ 2)) :
    ∫⁻ ξ, (b1sas_slab j n).indicator (fun ξ => ENNReal.ofReal (ξ j ^ 2) *
        ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2) ξ ≤
      ENNReal.ofReal (A / 16) := by
  set t : ℝ := 1 / ((n : ℝ) + 1) with ht
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have ht0 : 0 < t := by positivity
  have ht2 : t ^ 2 ≠ 0 := by positivity
  have hc : (16 * t ^ 2)⁻¹ * (A * t ^ 2) = A / 16 := by
    rw [mul_inv, div_eq_mul_inv]
    calc (16 : ℝ)⁻¹ * (t ^ 2)⁻¹ * (A * t ^ 2) = A * 16⁻¹ * ((t ^ 2)⁻¹ * t ^ 2) := by ring
      _ = A * 16⁻¹ := by rw [inv_mul_cancel₀ ht2, mul_one]
  have hpt : ∀ ξ : Spatial k, (b1sas_slab j n).indicator (fun ξ => ENNReal.ofReal (ξ j ^ 2) *
      ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2) ξ ≤
      ENNReal.ofReal (16 * t ^ 2)⁻¹ * (‖(𝐞 (t * ξ j) : ℂ) - 1‖ₑ ^ 2 *
        ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2) := by
    intro ξ
    by_cases hξ : ξ ∈ b1sas_slab j n
    · rw [indicator_of_mem hξ, ← mul_assoc]
      refine mul_le_mul_left ?_ _
      have hy : |t * ξ j| ≤ 1 / 2 := by
        have hξ' : 2 * |ξ j| ≤ (n : ℝ) + 1 := hξ
        rw [abs_mul, abs_of_pos ht0, ht, div_mul_eq_mul_div, one_mul, div_le_iff₀ hn1]
        linarith
      have hlow := b1sas_char_sub_one_sq_ge hy
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (16 * t ^ 2)⁻¹)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity : (0 : ℝ) < 16 * t ^ 2)]
      nlinarith
    · rw [indicator_of_notMem hξ]
      exact zero_le
  calc ∫⁻ ξ, (b1sas_slab j n).indicator (fun ξ => ENNReal.ofReal (ξ j ^ 2) *
        ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2) ξ
      ≤ ∫⁻ ξ, ENNReal.ofReal (16 * t ^ 2)⁻¹ * (‖(𝐞 (t * ξ j) : ℂ) - 1‖ₑ ^ 2 *
          ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (16 * t ^ 2)⁻¹ * ∫⁻ x, ‖G (x + t • b1sas_unit j) - G x‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, b1sas_lintegral_translate_sq hG j t]
    _ ≤ ENNReal.ofReal (16 * t ^ 2)⁻¹ * ENNReal.ofReal (A * t ^ 2) :=
        mul_le_mul_right htr _
    _ = ENNReal.ofReal (A / 16) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (16 * t ^ 2)⁻¹), hc]

/-- One coordinate: `∫ ξ_j² |Ĝ|² ≤ A / 16`. -/
theorem b1sas_lintegral_coord_sq_le {G : Spatial k → ℝ} (hG : MemLp G 2 volume) (j : Fin k)
    {A : ℝ} (hA : 0 ≤ A)
    (htr : ∀ n : ℕ, ∫⁻ x, ‖G (x + (1 / ((n : ℝ) + 1)) • b1sas_unit j) - G x‖ₑ ^ 2 ≤
      ENNReal.ofReal (A * (1 / ((n : ℝ) + 1)) ^ 2)) :
    ∫⁻ ξ, ENNReal.ofReal (ξ j ^ 2) *
        ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal (A / 16) := by
  set f : Spatial k → ℝ≥0∞ := fun ξ => ENNReal.ofReal (ξ j ^ 2) *
    ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 with hf
  have hfm : Measurable f :=
    (ENNReal.measurable_ofReal.comp
      (((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.pow 2).measurable)).mul
      ((Lp.stronglyMeasurable (𝓕 (b1sas_realLp hG) :
        Lp ℂ 2 (volume : Measure (Spatial k)))).measurable.enorm.pow_const 2)
  have hmono : Monotone fun n : ℕ => (b1sas_slab j n).indicator f := by
    intro a b hab ζ
    refine indicator_le_indicator_of_subset (fun ξ hξ => ?_) (fun _ => zero_le) ζ
    have hξ' : 2 * |ξ j| ≤ (a : ℝ) + 1 := hξ
    have hab' : (a : ℝ) ≤ b := Nat.cast_le.2 hab
    show 2 * |ξ j| ≤ (b : ℝ) + 1
    linarith
  have hsup : ∀ ξ, (⨆ n : ℕ, (b1sas_slab j n).indicator f ξ) = f ξ := by
    intro ξ
    refine le_antisymm (iSup_le fun n => indicator_le_self _ _ ξ) ?_
    obtain ⟨N, hN⟩ := exists_nat_ge (2 * |ξ j|)
    refine le_iSup_of_le N (le_of_eq ?_)
    rw [indicator_of_mem (show ξ ∈ b1sas_slab j N from
      (show 2 * |ξ j| ≤ (N : ℝ) + 1 by linarith))]
  calc ∫⁻ ξ, f ξ = ∫⁻ ξ, ⨆ n : ℕ, (b1sas_slab j n).indicator f ξ :=
        lintegral_congr fun ξ => (hsup ξ).symm
    _ = ⨆ n : ℕ, ∫⁻ ξ, (b1sas_slab j n).indicator f ξ :=
        lintegral_iSup (fun n => hfm.indicator (b1sas_measurableSet_slab j n)) hmono
    _ ≤ ENNReal.ofReal (A / 16) := iSup_le fun n => b1sas_slab_le hG j hA n (htr n)

/-- **The Fourier energy from translate differences.** If for every coordinate `j` and every
`n` the translate bound `∫ |G(x + e_j/(n+1)) - G(x)|² dx ≤ A/(n+1)²` holds, then
`∫ |ξ|² |Ĝ(ξ)|² dξ ≤ k A / 16`. -/
theorem b1sas_fourierEnergy_le {G : Spatial k → ℝ} (hG : MemLp G 2 volume) {A : ℝ}
    (hA : 0 ≤ A)
    (htr : ∀ (j : Fin k) (n : ℕ),
      ∫⁻ x, ‖G (x + (1 / ((n : ℝ) + 1)) • b1sas_unit j) - G x‖ₑ ^ 2 ≤
        ENNReal.ofReal (A * (1 / ((n : ℝ) + 1)) ^ 2)) :
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) *
        ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal (k * (A / 16)) := by
  have hm : ∀ j ∈ (Finset.univ : Finset (Fin k)), Measurable fun ξ : Spatial k =>
      ENNReal.ofReal (ξ j ^ 2) *
        ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 := fun j _ =>
    (ENNReal.measurable_ofReal.comp
      (((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.pow 2).measurable)).mul
      ((Lp.stronglyMeasurable (𝓕 (b1sas_realLp hG) :
        Lp ℂ 2 (volume : Measure (Spatial k)))).measurable.enorm.pow_const 2)
  calc ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) *
        ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2
      = ∫⁻ ξ, ∑ j : Fin k, ENNReal.ofReal (ξ j ^ 2) *
          ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 := by
        refine lintegral_congr fun ξ => ?_
        rw [EuclideanSpace.real_norm_sq_eq, ENNReal.ofReal_sum_of_nonneg
          (fun j _ => sq_nonneg _), Finset.sum_mul]
    _ = ∑ j : Fin k, ∫⁻ ξ, ENNReal.ofReal (ξ j ^ 2) *
          ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 :=
        lintegral_finsetSum _ hm
    _ ≤ ∑ _j : Fin k, ENNReal.ofReal (A / 16) :=
        Finset.sum_le_sum fun j _ => b1sas_lintegral_coord_sq_le hG j hA (htr j)
    _ = ENNReal.ofReal (k * (A / 16)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]

end ParabolicRectifiability.Characterization
