import ParabolicRectifiability.BetaP.Proofs.Carrier.CarrierStatements

/-! # Domination transfer for `B_p`

Proves `ccar_betaPow_domination : BetaPowDominationStatement`.

If `μ ≤ c ν` for a real `c > 0`, then for every model `L`,
`fit_{p,μ}(L;z,r) ≤ fit_{p,cν}(L;z,r) = c fit_{p,ν}(L;z,r)` (monotonicity of the `lintegral` in the
measure, `setLIntegral_smul_measure`); multiplication by the finite nonzero scalar `c` commutes with
the model infimum (`ENNReal.mul_iInf_of_ne`, also for an empty family, where both infima are `⊤`),
and the common normalization `r^{-k-p}` is untouched. For `r ≤ 0` both sides are `0`. The guards of
the statement are not used. The pattern is that of `fit_mono_measure` and `fit_smul`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP.CarrierTree

open ParabolicRectifiability.Foundations

/-- One fixed model: `μ ≤ c • ν` gives `fit_{p,μ}(L;z,r) ≤ c · fit_{p,ν}(L;z,r)`, for every
`ℝ≥0∞` scalar `c`, exponent, centre and radius. -/
theorem ccare_fitPow_le_smul {n k : ℕ} {T : FamilyKind} {μ ν : Measure (Space n)} {c : ℝ≥0∞}
    (h : μ ≤ c • ν) (p : ℝ) (L : Models n k T) (z : Space n) (r : ℝ) :
    fitPow μ p L z r ≤ c * fitPow ν p L z r :=
  calc fitPow μ p L z r ≤ fitPow (c • ν) p L z r :=
        lintegral_mono' (Measure.restrict_mono_measure h _) le_rfl
    _ = c * fitPow ν p L z r := setLIntegral_smul_measure c _ _

/-- `μ ≤ c • ν` with a finite nonzero scalar gives `B_{p,μ}(z,r) ≤ c · B_{p,ν}(z,r)` at every
centre and radius, for every family (an empty family gives `⊤ ≤ c · ⊤ = ⊤` at `r > 0`). -/
theorem ccare_betaPow_le_smul {n : ℕ} {μ ν : Measure (Space n)} {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ⊤) (h : μ ≤ c • ν) (k : ℕ) (T : FamilyKind) (p : ℝ) (z : Space n) (r : ℝ) :
    betaPow μ k T p z r ≤ c * betaPow ν k T p z r := by
  unfold betaPow
  split_ifs with hr
  · rw [mul_left_comm c, ENNReal.mul_iInf_of_ne hc0 hc]
    exact mul_le_mul' le_rfl (iInf_mono fun L => ccare_fitPow_le_smul h p L z r)
  · simp

/-- **Domination transfer for `B_p`** (`BetaPowDominationStatement`). -/
theorem ccar_betaPow_domination_proof : BetaPowDominationStatement := by
  intro n _ k _ _ T μ ν p c _ hc h z r
  exact ccare_betaPow_le_smul (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top h k T p z r

end ParabolicRectifiability.BetaP.CarrierTree
