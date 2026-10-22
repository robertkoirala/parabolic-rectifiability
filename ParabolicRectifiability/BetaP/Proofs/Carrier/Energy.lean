import ParabolicRectifiability.BetaP.Proofs.Carrier.CarrierStatements
import ParabolicRectifiability.BetaP.Statements.Laws
import ParabolicRectifiability.Foundations.Statements.Measurability
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-! # Finite own-Hausdorff square of the carrier measure

Proves `ccar_energy : BetaPowHolderStatement → Foundations.BetaPowTwoStatement →
BetaPowDominationStatement → CarrierEnergyStatement`. The three inputs enter as hypotheses
(implication form).

Argument. Let `η = H_P^k⌊K`.
1. Growth at `(c, 1)` and `K ⊆ P(c,1)` give `η(X) = H_P^k(K) ≤ ofReal U < ∞`; so `η` is finite,
   hence finite on compacts and inner regular (the inner-regularity instance for finite
   measures on complete second-countable spaces is Mathlib's
   `instInnerRegularOfIsCompletelyPseudoMetrizableSpace`).
2. For `0 < r ≤ 1`, `η(P(y,r)) = H_P^k(K ∩ P(y,r)) ≤ ofReal (U r^k)` (`Measure.restrict_apply` on
   the measurable ball; no measurability of `K`), so `Θ_η(y,r) ≤ ofReal U`.
3. For `0 < r < 1`: `betaSq η = B_{2,η}` (`BetaPowTwoStatement`)
   `≤ Θ_η^{1-2/p} B_{p,η}^{2/p}` (Hölder, second part)
   `≤ (ofReal U)^{1-2/p} (ofReal d · B_{p,ν})^{2/p}` (step 2 and domination with `μ = η`)
   `= D₀ B_{p,ν}^{2/p}` with `D₀ = (ofReal U)^{1-2/p} (ofReal d)^{2/p} < ∞`. At `p = 2` the
   exponent `1 - 2/p` is zero and the factor is one, also for `U ≤ 0`.
4. Integrating over `(0,1)` against `dr/r`: `S^1_{2,η}(y) ≤ D₀ ∫_0^∞ B_{p,ν}(y,s)^{2/p} ds/s
   ≤ D₀ ofReal L < ∞` at every `y` of the good set `{allScaleEnergyP ν ≤ ofReal L}`, whose
   complement is `ν`-null, hence `η`-null (`η ≪ ν` from `η ≤ d ν`); the good set is never shown to
   be measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP.CarrierTree

open ParabolicRectifiability.Foundations

/-- The density ratio of `H_P^k⌊K` at radii `0 < r ≤ 1` is at most `ofReal U` under the upper
growth `H_P^k(K ∩ P(q,R)) ≤ ofReal (U R^k)` (`0 < R ≤ 1`); no measurability of `K`. -/
theorem ccare_densityRatio_le {n k : ℕ} {K : Set (Space n)} {U : ℝ}
    (hgrowth : ∀ (q : Space n) (R : ℝ), 0 < R → R ≤ 1 →
      hausdorffP n k (K ∩ Metric.ball q R) ≤ ENNReal.ofReal (U * R ^ k))
    (y : Space n) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    densityRatio ((hausdorffP n k).restrict K) k y r ≤ ENNReal.ofReal U := by
  unfold densityRatio
  apply ENNReal.div_le_of_le_mul
  rw [Measure.restrict_apply measurableSet_ball, inter_comm, ← ENNReal.ofReal_pow hr.le,
    ← ENNReal.ofReal_mul' (pow_nonneg hr.le k)]
  exact hgrowth y r hr hr1

/-- **Finite own-Hausdorff square of the carrier measure** (`ccar_energy`, in implication
form). -/
theorem ccar_energy_proof : BetaPowHolderStatement → Foundations.BetaPowTwoStatement →
    BetaPowDominationStatement → CarrierEnergyStatement := by
  intro hHolder hTwo hDom n hn k hk hkn T hT p hp ν K c U d L hd _ hKc hgrowth hηle hae
  set η : Measure (Space n) := (hausdorffP n k).restrict K with hη
  have hp0 : 0 < p := lt_of_lt_of_le two_pos hp
  -- Step 1: `η` is finite, finite on compacts and inner regular.
  have hKfin : hausdorffP n k K < ⊤ := by
    have h1 := hgrowth c 1 one_pos le_rfl
    rw [inter_eq_left.mpr hKc] at h1
    exact lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
  have : IsFiniteMeasure η := hausdorffP_restrict_isFinite hKfin
  have hηc : IsFiniteMeasureOnCompacts η := inferInstance
  have hηr : η.InnerRegular := inferInstance
  have hac : η ≪ ν := Measure.absolutelyContinuous_of_le_smul hηle
  -- Step 3: the pointwise bound on `(0,1)`.
  have he : 0 ≤ 1 - 2 / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp)
  have h2p : 0 ≤ 2 / p := (div_pos two_pos hp0).le
  have hD₀ : ENNReal.ofReal U ^ (1 - 2 / p) * ENNReal.ofReal d ^ (2 / p) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg he ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg h2p ENNReal.ofReal_ne_top)
  have hpt : ∀ y : Space n, ∀ r ∈ Ioo (0 : ℝ) 1,
      betaSq η k T y r ≤ (ENNReal.ofReal U ^ (1 - 2 / p) * ENNReal.ofReal d ^ (2 / p)) *
        betaPow ν k T p y r ^ (2 / p) := by
    intro y r hr
    rw [← hTwo n hn k hk hkn T η y r]
    calc betaPow η k T 2 y r
        ≤ densityRatio η k y r ^ (1 - 2 / p) * betaPow η k T p y r ^ (2 / p) :=
          (hHolder n hn k hk hkn T hT η hηc hηr y r hr.1).2 p hp
      _ ≤ ENNReal.ofReal U ^ (1 - 2 / p) * (ENNReal.ofReal d * betaPow ν k T p y r) ^ (2 / p) :=
          mul_le_mul' (ENNReal.rpow_le_rpow (ccare_densityRatio_le hgrowth y hr.1 hr.2.le) he)
            (ENNReal.rpow_le_rpow (hDom n hn k hk hkn T η ν p d hp0 hd hηle y r) h2p)
      _ = (ENNReal.ofReal U ^ (1 - 2 / p) * ENNReal.ofReal d ^ (2 / p)) *
            betaPow ν k T p y r ^ (2 / p) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ h2p, mul_assoc]
  -- Step 4: integrate on the good set, which is `η`-conull by domination.
  filter_upwards [hac.ae_le hae] with y hy
  unfold squareEnergy
  calc ∫⁻ r in Ioo (0 : ℝ) 1, betaSq η k T y r ∂scaleMeasure
      ≤ ∫⁻ r in Ioo (0 : ℝ) 1, (ENNReal.ofReal U ^ (1 - 2 / p) * ENNReal.ofReal d ^ (2 / p)) *
          betaPow ν k T p y r ^ (2 / p) ∂scaleMeasure :=
        setLIntegral_mono' measurableSet_Ioo (hpt y)
    _ = (ENNReal.ofReal U ^ (1 - 2 / p) * ENNReal.ofReal d ^ (2 / p)) *
          ∫⁻ r in Ioo (0 : ℝ) 1, betaPow ν k T p y r ^ (2 / p) ∂scaleMeasure :=
        lintegral_const_mul' _ _ hD₀
    _ ≤ (ENNReal.ofReal U ^ (1 - 2 / p) * ENNReal.ofReal d ^ (2 / p)) *
          ∫⁻ r in Ioi (0 : ℝ), betaPow ν k T p y r ^ (2 / p) ∂scaleMeasure :=
        mul_le_mul' le_rfl (lintegral_mono_set Ioo_subset_Ioi_self)
    _ = (ENNReal.ofReal U ^ (1 - 2 / p) * ENNReal.ofReal d ^ (2 / p)) *
          allScaleEnergyP ν k T p y := rfl
    _ ≤ (ENNReal.ofReal U ^ (1 - 2 / p) * ENNReal.ofReal d ^ (2 / p)) * ENNReal.ofReal L :=
        mul_le_mul' le_rfl hy
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hD₀) ENNReal.ofReal_lt_top

end ParabolicRectifiability.BetaP.CarrierTree
