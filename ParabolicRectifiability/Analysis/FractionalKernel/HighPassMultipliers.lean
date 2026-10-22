import ParabolicRectifiability.Analysis.Coordinates
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Temperate growth of the high-pass multipliers

Let `F : ℝ → ℂ` be smooth, compactly supported, and equal to one on a neighbourhood of zero (for
an admissible frequency cutoff `η`, `F = η̂ = 𝓕 (fun t => (η t : ℂ))`). On the ordinary
coordinates `FourierSpace m = ℝ^m × ℝ`, with time frequency `τ = (WithLp.ofLp ζ).2`, this file
proves that

* the low-pass complement `Q(ξ,τ) = 1 - F(τ)` and
* the **complete** high-pass multiplier `M̃(ξ,τ) = (1 - F(τ)) |τ|^{-1/2}`

have temperate growth (`Function.HasTemperateGrowth`), so that `SchwartzMap.smulLeftCLM` by
either maps Schwartz functions to Schwartz functions with the expected pointwise values. The
factor `|τ|^{-1/2}` alone is not smooth at `τ = 0`; `M̃` is, because `1 - F` vanishes near
`τ = 0`. Both multipliers vanish at `τ = 0`.

Proof. `1 - F` is a constant minus a compactly supported smooth function. For `M̃`, choose `r > 0`
with `F = 1` on `(-r, r)`. A bump `β` (`ContDiffBump`, equal to one on `[-r/2, r/2]` and zero for
`|τ| ≥ r`) gives the smooth function `ρ(τ) = τ² + r² β(τ) ≥ r²/4`, and `g = ρ^{-1/4}` has
temperate growth by `Function.HasTemperateGrowth.comp'` (the power `y ↦ y^{-1/4}` has bounded
derivatives on `y > r²/8`). Then `g(τ) = |τ|^{-1/2}` for `|τ| ≥ r`, and `M̃ = (1 - F) g`
everywhere. Composition with the continuous linear time coordinate preserves temperate growth.
-/

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace ParabolicRectifiability.Foundations

/-! ## Composition with the time coordinate -/

/-- A one-variable function of temperate growth, composed with the time coordinate
`ζ ↦ (WithLp.ofLp ζ).2` of `FourierSpace m`, has temperate growth. -/
theorem fhpbb2s_hasTemperateGrowth_comp_time {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} (hf : f.HasTemperateGrowth) (m : ℕ) :
    (fun ζ : FourierSpace m => f (WithLp.ofLp ζ).2).HasTemperateGrowth :=
  hf.comp (WithLp.sndL 2 ℝ (Spatial m) ℝ).hasTemperateGrowth

/-! ## The low-pass complement `Q = 1 - F` -/

/-- `τ ↦ 1 - F τ` has temperate growth when `F` is smooth and compactly supported. -/
theorem fhpbb2s_hasTemperateGrowth_one_sub {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) : (fun τ : ℝ => 1 - F τ).HasTemperateGrowth :=
  (Function.HasTemperateGrowth.const (1 : ℂ)).sub (hFc.hasTemperateGrowth hF)

/-- **Temperate growth of `Q(ξ,τ) = 1 - F(τ)`** on `FourierSpace m`. -/
theorem fhpbb2s_hasTemperateGrowth_lowPassComplement {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (m : ℕ) :
    (fun ζ : FourierSpace m => 1 - F (WithLp.ofLp ζ).2).HasTemperateGrowth :=
  fhpbb2s_hasTemperateGrowth_comp_time (fhpbb2s_hasTemperateGrowth_one_sub hF hFc) m

/-- Zero-frequency value: `1 - F 0 = 0` when `F = 1` near `0`. -/
theorem fhpbb2s_one_sub_apply_zero {F : ℝ → ℂ} (hF0 : ∀ᶠ τ in 𝓝 (0 : ℝ), F τ = 1) :
    1 - F 0 = 0 := by
  rw [hF0.self_of_nhds, sub_self]

/-! ## A smooth substitute for `|τ|^{-1/2}` away from zero -/

/-- The power `y ↦ y^p` with `p ≤ 0` has bounded derivatives on `y > c > 0`: the hypothesis of
`Function.HasTemperateGrowth.comp'` with `k = 0`. -/
theorem fhpbb2s_rpow_iteratedFDerivWithin_bound {c p : ℝ} (hc : 0 < c) (hp : p ≤ 0) (N : ℕ) :
    ∃ (k : ℕ) (C : ℝ), ∃ (_hC : 0 ≤ C), ∀ n ≤ N, ∀ x ∈ Ioi c,
      ‖iteratedFDerivWithin ℝ n (fun y : ℝ => y ^ p) (Ioi c) x‖ ≤ C * (1 + ‖x‖) ^ k := by
  refine ⟨0, ∑ j ∈ Finset.range (N + 1),
    ‖(descPochhammer ℝ j).eval p‖ * c ^ (p - j), by positivity, fun n hn x hx => ?_⟩
  have hxc : c < x := hx
  have hx0 : 0 < x := hc.trans hxc
  have hcd : ContDiffAt ℝ n (fun y : ℝ => y ^ p) x :=
    Real.contDiffAt_rpow_const (Or.inl hx0.ne')
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi c) hcd hx, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, norm_mul, pow_zero, mul_one]
  have hpn : p - (n : ℝ) ≤ 0 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hpow : ‖x ^ (p - n)‖ ≤ c ^ (p - n) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact Real.rpow_le_rpow_of_nonpos hc hxc.le hpn
  calc ‖(descPochhammer ℝ n).eval p‖ * ‖x ^ (p - n)‖
      ≤ ‖(descPochhammer ℝ n).eval p‖ * c ^ (p - n) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ ≤ ∑ j ∈ Finset.range (N + 1), ‖(descPochhammer ℝ j).eval p‖ * c ^ (p - j) :=
        Finset.single_le_sum (f := fun j : ℕ => ‖(descPochhammer ℝ j).eval p‖ * c ^ (p - j))
          (fun j _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_of_le hn))

/-- For `r > 0` there is a real function of temperate growth equal to `|τ|^{-1/2}` for
`|τ| ≥ r`. -/
theorem fhpbb2s_exists_hasTemperateGrowth_eq_rpow_neg_half {r : ℝ} (hr : 0 < r) :
    ∃ g : ℝ → ℝ, g.HasTemperateGrowth ∧
      ∀ τ : ℝ, r ≤ |τ| → g τ = |τ| ^ (-(1 / 2 : ℝ)) := by
  let β : ContDiffBump (0 : ℝ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let ρ : ℝ → ℝ := fun τ => τ ^ 2 + r ^ 2 * β τ
  have hβ : (β : ℝ → ℝ).HasTemperateGrowth := β.hasCompactSupport.hasTemperateGrowth β.contDiff
  have hsq : (fun τ : ℝ => τ ^ 2).HasTemperateGrowth := Function.HasTemperateGrowth.id.pow 2
  have hρ : ρ.HasTemperateGrowth :=
    hsq.add ((Function.HasTemperateGrowth.const (r ^ 2)).mul hβ)
  have hc : 0 < r ^ 2 / 8 := by positivity
  have hrange : range ρ ⊆ Ioi (r ^ 2 / 8) := by
    rintro - ⟨τ, rfl⟩
    show r ^ 2 / 8 < τ ^ 2 + r ^ 2 * β τ
    by_cases hτ : |τ| ≤ r / 2
    · have h1 : β τ = 1 := β.one_of_mem_closedBall (by
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hτ)
      rw [h1]
      nlinarith [sq_nonneg τ, sq_nonneg r]
    · have h2 : r / 2 < |τ| := lt_of_not_ge hτ
      have h3 : (r / 2) ^ 2 < |τ| ^ 2 := by
        exact pow_lt_pow_left₀ h2 (by positivity) two_ne_zero
      rw [sq_abs] at h3
      have h4 : 0 ≤ r ^ 2 * β τ := mul_nonneg (sq_nonneg r) β.nonneg
      nlinarith
  have hpow : ContDiffOn ℝ ∞ (fun y : ℝ => y ^ (-(1 / 4 : ℝ))) (Ioi (r ^ 2 / 8)) :=
    contDiffOn_fun_id.rpow_const_of_ne fun y hy => (hc.trans hy).ne'
  have hg := Function.HasTemperateGrowth.comp' hrange (uniqueDiffOn_Ioi _) hpow
    (fun N => fhpbb2s_rpow_iteratedFDerivWithin_bound hc (by norm_num) N) hρ
  refine ⟨_, hg, fun τ hτ => ?_⟩
  have h0 : β τ = 0 := β.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hτ)
  show (τ ^ 2 + r ^ 2 * β τ) ^ (-(1 / 4 : ℝ)) = |τ| ^ (-(1 / 2 : ℝ))
  rw [h0, mul_zero, add_zero, ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg τ)]
  norm_num

/-! ## The complete high-pass multiplier `M̃ = (1 - F) |τ|^{-1/2}` -/

/-- **Temperate growth of the complete one-variable multiplier** `(1 - F(τ)) |τ|^{-1/2}`, for
`F` smooth, compactly supported and equal to one near `0`. -/
theorem fhpbb2s_hasTemperateGrowth_highPassMultiplier_real {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (hF0 : ∀ᶠ τ in 𝓝 (0 : ℝ), F τ = 1) :
    (fun τ : ℝ => (1 - F τ) * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).HasTemperateGrowth := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hF0
  obtain ⟨g, hg, hgeq⟩ := fhpbb2s_exists_hasTemperateGrowth_eq_rpow_neg_half hr
  have hG : (fun τ : ℝ => (1 - F τ) * ((g τ : ℝ) : ℂ)).HasTemperateGrowth :=
    (fhpbb2s_hasTemperateGrowth_one_sub hF hFc).mul (Complex.hasTemperateGrowth_ofReal.comp hg)
  convert hG using 1
  funext τ
  by_cases hτ : r ≤ |τ|
  · rw [hgeq τ hτ]
  · have hF1 : F τ = 1 := hball τ (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact lt_of_not_ge hτ)
    simp only [hF1, sub_self, zero_mul]

/-- **Temperate growth of the complete high-pass multiplier**
`M̃(ξ,τ) = (1 - F(τ)) |τ|^{-1/2}` on `FourierSpace m`. -/
theorem fhpbb2s_hasTemperateGrowth_highPassMultiplier {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (hF0 : ∀ᶠ τ in 𝓝 (0 : ℝ), F τ = 1) (m : ℕ) :
    (fun ζ : FourierSpace m =>
      (1 - F (WithLp.ofLp ζ).2) *
        ((|(WithLp.ofLp ζ).2| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).HasTemperateGrowth :=
  fhpbb2s_hasTemperateGrowth_comp_time
    (fhpbb2s_hasTemperateGrowth_highPassMultiplier_real hF hFc hF0) m

/-- Zero-frequency value of the complete multiplier: `(1 - F 0) |0|^{-1/2} = 0`. -/
theorem fhpbb2s_highPassMultiplier_apply_zero {F : ℝ → ℂ}
    (hF0 : ∀ᶠ τ in 𝓝 (0 : ℝ), F τ = 1) :
    (1 - F 0) * ((|(0 : ℝ)| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 0 := by
  rw [fhpbb2s_one_sub_apply_zero hF0, zero_mul]

end ParabolicRectifiability.Foundations
