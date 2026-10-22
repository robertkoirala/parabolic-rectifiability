import ParabolicRectifiability.BetaP.Proofs.Carrier.CarrierStatements

/-! # Equal-radius content bounds from the separated-set bound

Proof of `ContentOfSeparatedStatement`. This is the content-bound step of
`density_selection_of_discrete` with `Cnet (1 + L/a)` replaced by the generic separated
constant `A`. The lemmas `exists_maximal_separated_finset`, `hausdorffP_le_of_nets` and
`parabolicVolume_thickening_le_of_net` are used unchanged.

Constant: `C₀ = 1 + 2^{n+2} + 2 ω_n 2^{n+2}`. The edge cases `k = 0`, `A = 0`
(then every net is empty) and `k = n + 2` are covered by the same argument; no measurability of
`K` is used. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.BetaP.CarrierTree

open ParabolicRectifiability.Foundations

/-- Nets from the separated-set bound: every `K ∩ P(q,R)` has, at each scale `ρ ≤ R ≤ 1`, a
finite `ρ`-net (open balls) of at most `A (R/ρ)^k` points, namely a maximal `ρ`-separated
subset. -/
theorem ccarc_net_of_separatedBound {n k : ℕ} {A : ℝ} {K : Set (Space n)}
    (hsep : ccar_separatedBound k A K) (q : Space n) (R ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hR1 : R ≤ 1) :
    ∃ F : Finset (Space n), (F.card : ℝ) ≤ A * (R / ρ) ^ k ∧
      K ∩ Metric.ball q R ⊆ ⋃ x ∈ F, Metric.ball x ρ := by
  have hR : 0 < R := hρ.trans_le hρR
  have hb : ∀ F : Finset (Space n), ↑F ⊆ K ∩ Metric.ball q R →
      IsSeparatedFinset ρ F → (F.card : ℝ) ≤ A * (R / ρ) ^ k :=
    fun F hF hFs => hsep q R ρ hR hR1 hρ hρR F hF hFs
  obtain ⟨F, hFS, hFsep, hFcov⟩ := exists_maximal_separated_finset _ hρ
    ⌊A * (R / ρ) ^ k⌋₊ (fun F hF hFs => Nat.le_floor (hb F hF hFs))
  refine ⟨F, hb F hFS hFsep, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hFcov x hx
  exact mem_iUnion₂.mpr ⟨y, hy, hxy⟩

/-- Equal-radius content bounds from the separated-set bound, with
`C₀ = 1 + 2^{n+2} + 2 ω_n 2^{n+2}`. -/
theorem ccar_content_of_separated_proof : ContentOfSeparatedStatement := by
  intro n
  set Ch : ℝ := (2 : ℝ) ^ (n + 2) with hChdef
  set Cm : ℝ := 2 * (omega n).toReal * 2 ^ (n + 2) with hCmdef
  have hChp : 0 ≤ Ch := by rw [hChdef]; positivity
  have hCmp : 0 ≤ Cm := by rw [hCmdef]; positivity
  refine ⟨1 + Ch + Cm, by positivity, ?_⟩
  intro k hkn K c A hA hKc hsep
  refine ⟨fun q R hR hR1 => ?_, fun q R r hR hR1 hr hrR F hF hFs => ?_, fun r hr hr1 => ?_⟩
  · -- local Hausdorff bound
    have h := hausdorffP_le_of_nets k (K ∩ Metric.ball q R) hA hR
      (fun ρ hρ hρR => ccarc_net_of_separatedBound hsep q R ρ hρ hρR hR1)
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (2 : ℝ) ^ k ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) hkn
    have hRk : 0 ≤ R ^ k := by positivity
    calc A * 2 ^ k * R ^ k ≤ A * 2 ^ (n + 2) * R ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hA) hRk
      _ = Ch * A * R ^ k := by rw [hChdef]; ring
      _ ≤ (1 + Ch + Cm) * A * R ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hA) hRk
  · -- separated sets: the hypothesis itself
    refine (hsep q R r hR hR1 hr hrR F hF hFs).trans ?_
    have hRr : 0 ≤ (R / r) ^ k := by positivity
    have : A ≤ (1 + Ch + Cm) * A := by nlinarith
    exact mul_le_mul_of_nonneg_right this hRr
  · -- tube bound: one net of `K = K ∩ P(c,1)` at scale `r`
    obtain ⟨F, hFcard, hFcov⟩ := ccarc_net_of_separatedBound hsep c 1 r hr hr1 le_rfl
    have hKsub : K ⊆ K ∩ Metric.ball c 1 := fun z hz => ⟨hz, hKc hz⟩
    have h := parabolicVolume_thickening_le_of_net K hr F hFcard (hKsub.trans hFcov)
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsub : n + 2 - k + k = n + 2 := by omega
    have hrk : r ^ (n + 2) = r ^ (n + 2 - k) * r ^ k := by rw [← pow_add, hsub]
    have e : A * (1 / r) ^ k * (2 * (omega n).toReal) * (2 * r) ^ (n + 2) =
        Cm * A * r ^ (n + 2 - k) := by
      calc A * (1 / r) ^ k * (2 * (omega n).toReal) * (2 * r) ^ (n + 2)
          = (2 * (omega n).toReal * 2 ^ (n + 2)) * A * r ^ (n + 2 - k) * (r ^ k / r ^ k) := by
            rw [mul_pow, hrk, one_div_pow]
            ring
        _ = Cm * A * r ^ (n + 2 - k) := by
            rw [div_self (pow_ne_zero _ hr.ne'), mul_one, hCmdef]
    rw [e]
    have hr0 : 0 ≤ r ^ (n + 2 - k) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hA) hr0

end ParabolicRectifiability.BetaP.CarrierTree
