import ParabolicRectifiability.BetaP.Proofs.Packing.PackingLemmas
import ParabolicRectifiability.BetaP.Proofs.Support.Interfaces

/-! # The active-radius packing bound from the discrete packing bound

`cpk_activeRadiusPacking_of_discretePacking` proves `activeRadiusPacking_of_discretePacking`: the
quadratic discrete packing bound implies the active-radius packing bounds for `B_p`, `p ≥ 2`. It
is assembled from the auxiliary statements `CpkActiveSourceStatement`, …, `CpkMassBoundStatement`.

Assembly, for fixed `n ≥ 1`, `p ≥ 2` and a constant `C₀ > 0` with `DiscretePackingBound n C₀`,
with `D = 2^{n+1} C₀` and `C = max{2D, (2D)^{p/2}}` (`cpkPackingConstant`, chosen before `k`, `T`
and the family):
* **truncated form**: if `b ≤ 0` there is no index (`0 < w_i ≤ b`) and `σ = 0`. Otherwise let
  `Λ` be the least active bound (`cpk_leastActiveBound`). The Hölder reduction
  (`cpk_holderReduction`, from the two input laws) bounds the quadratic subfamily tails by
  `Λ^{1-2/p} B`; the doubled parent (`cpk_doubledParent`, from `DiscretePackingBound n C₀`)
  makes `2^k C₀ (b + Λ^{1-2/p} B)` an active bound, hence by minimality
  `Λ ≤ 2^k C₀ (…) ≤ D (b + Λ^{1-2/p} B)` because `k < n+2`. Absorption (`cpk_absorption`) gives
  `Λ ≤ C (b + B^{p/2})`, and the mass bound (`cpk_massBound`) gives
  `σ(X) ≤ Λ R^k ≤ C (b + B^{p/2}) R^k`.
* **main form**: above its own radius each centre sees the full source and the truncated testing
  source alike (`cpk_activeSource`), so the full-source tail hypothesis is the truncated one, and
  the truncated form applies with the same constant.

No packing, content or density property of the family is assumed beyond the hypotheses of
`activeRadiusPacking_of_discretePacking` itself.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- The output constant of the active-radius packing bound: `max{2D, (2D)^{p/2}}` with
`D = 2^{n+1} C₀`. It depends on `n`, `p` and `C₀` only. -/
def cpkPackingConstant (n : ℕ) (p C₀ : ℝ) : ℝ :=
  max (2 * (2 ^ (n + 1) * C₀)) ((2 * (2 ^ (n + 1) * C₀)) ^ (p / 2))

theorem cpkPackingConstant_pos (n : ℕ) (p : ℝ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    0 < cpkPackingConstant n p C₀ :=
  lt_max_of_lt_left (mul_pos two_pos (mul_pos (pow_pos two_pos _) hC₀))

/-- **Active-radius packing from discrete packing**: the statement
`activeRadiusPacking_of_discretePacking`. -/
theorem cpk_activeRadiusPacking_of_discretePacking (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 2 ≤ p)
    (C₀ : ℝ) (hC₀ : 0 < C₀) (hdisc : DiscretePackingBound n C₀) :
    ∃ C : ℝ, 0 < C ∧ ActiveRadiusPackingBound n p C ∧ ActiveRadiusPackingTruncatedBound n p C := by
  have hD : 0 < (2 : ℝ) ^ (n + 1) * C₀ := mul_pos (pow_pos two_pos _) hC₀
  have htrunc : ActiveRadiusPackingTruncatedBound n p (cpkPackingConstant n p C₀) := by
    intro k hk hkn T hT q R hR N z r w b B hpack hB htail
    rcases le_or_gt b 0 with hb | hb
    · -- no index: every weight lies in `(0, b]`
      have hnone : ∀ i : Fin N, False := fun i =>
        absurd ((hpack.weight_pos i).trans_le (hpack.weight_le i)) (not_lt.mpr hb)
      have h0 : atomicSource k z r w = 0 := by
        unfold atomicSource
        exact Finset.sum_eq_zero fun i _ => (hnone i).elim
      rw [h0]
      simp
    · obtain ⟨Λ, hΛ0, hΛ, hleast⟩ :=
        cpk_leastActiveBound k z r w b hpack.radius_pos hpack.weight_pos hpack.weight_le
      have hB' : 0 ≤ Λ ^ (1 - 2 / p) * B := mul_nonneg (Real.rpow_nonneg hΛ0 _) hB
      have hsub : CpkSubfamilyTailBound k T z r w (Λ ^ (1 - 2 / p) * B) :=
        cpk_holderReduction cpk_input_holder cpk_input_betaPowTwo n hn k hk hkn T hT p hp
          z r w B Λ hpack.radius_pos hpack.weight_pos hB hΛ0 hΛ htail
      have hstep : CpkActiveDensityBound k z r w (2 ^ k * C₀ * (b + Λ ^ (1 - 2 / p) * B)) :=
        cpk_doubledParent n C₀ hC₀ hdisc k hk hkn T hT z r w b _ hpack.radius_pos
          hpack.pairwise_disjoint hpack.weight_pos hpack.weight_le hb hB' hsub
      have hself : Λ ≤ (2 : ℝ) ^ (n + 1) * C₀ * (b + Λ ^ (1 - 2 / p) * B) := by
        refine (hleast _ hstep).trans ?_
        have h2k : (2 : ℝ) ^ k ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2k hC₀.le)
          (add_nonneg hb.le hB')
      have habs : Λ ≤ cpkPackingConstant n p C₀ * (b + B ^ (p / 2)) :=
        cpk_absorption p ((2 : ℝ) ^ (n + 1) * C₀) b B Λ hp hD hb.le hB hΛ0 hself
      refine (cpk_massBound k q R z r w b Λ hpack hΛ).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right habs (pow_nonneg hR.le k)
  refine ⟨cpkPackingConstant n p C₀, cpkPackingConstant_pos n p hC₀, ?_, htrunc⟩
  intro k hk hkn T hT q R hR N z r w b B hpack hB htail
  refine htrunc k hk hkn T hT q R hR N z r w b B hpack hB fun i => ?_
  calc (∫⁻ s in Ioi (r i),
        betaPow (BetaP.truncatedAtomicSource k z r w s) k T p (z i) s ^ (2 / p) ∂scaleMeasure)
      = ∫⁻ s in Ioi (r i), betaPow (atomicSource k z r w) k T p (z i) s ^ (2 / p)
          ∂scaleMeasure := by
        refine setLIntegral_congr_fun measurableSet_Ioi ?_
        intro s hs
        exact congrArg (fun x : ℝ≥0∞ => x ^ (2 / p))
          (cpk_activeSource k T p z r w hpack.radius_pos hpack.pairwise_disjoint i s
            (le_of_lt hs))
    _ ≤ ENNReal.ofReal B := htail i

end ParabolicRectifiability.BetaP
