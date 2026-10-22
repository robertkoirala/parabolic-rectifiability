import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # The forest energy

For every direct partition of `supp μ` from `ℓ₀ = R` and every cell `T` of the root forest of
`P(a, R)`, the local hypotheses in `P(a, B R)` give `∑_{Q ⊂ T} a_Q μ(Q) ≤ C_E M μ(T)`
with `B = 2(Λ+2)` and `C_E = 2·6^{k+2} (8(Λ+2))^k A`.
The descendant integral bound and the ADR cell masses enter as the hypotheses
`DescendantIntegralStatement` and `CellMassStatement` (implication form).

Route: `T` lies in a top cell meeting `P(a, R)`, so `z_T ∈ P(a, 5R)` and
`ℓ_T ≤ R`; put `s = 2(Λ+2)ℓ_T ≤ BR`; `T ⊆ P(z_T, 2ℓ_T) ⊆ P(z_T, s)`; the local Carleson
hypothesis at `(z_T, s)` (`z_T ∈ supp μ`) bounds `∫_{P(z_T,s)} S^s dμ ≤ M s^k`; the lower cell
mass gives `s^k = (8(Λ+2))^k (ℓ_T/4)^k ≤ (8(Λ+2))^k A μ(T)`. Local ADR is the first two
conjuncts of `LocalForwardHypotheses`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

open ParabolicRectifiability.Foundations

/-- The real normalization `2·6^p (M s^k) = (2·6^p (8(Λ+2))^k M A)(A⁻¹ (ℓ/4)^k)` for
`s = 2(Λ+2)ℓ`. -/
theorem d1aforest_real_identity (k : ℕ) {A : ℝ} (hA : A ≠ 0) (Λ ℓ M : ℝ) :
    2 * 6 ^ (k + 2) * (M * (2 * ((Λ + 2) * ℓ)) ^ k) =
      2 * 6 ^ (k + 2) * (8 * (Λ + 2)) ^ k * M * A * (A⁻¹ * (ℓ / 4) ^ k) := by
  have hs : (2 * ((Λ + 2) * ℓ)) ^ k = (8 * (Λ + 2)) ^ k * (ℓ / 4) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hs, show 2 * 6 ^ (k + 2) * (8 * (Λ + 2)) ^ k * M * A * (A⁻¹ * (ℓ / 4) ^ k) =
      2 * 6 ^ (k + 2) * (8 * (Λ + 2)) ^ k * M * (ℓ / 4) ^ k * (A * A⁻¹) by ring,
    mul_inv_cancel₀ hA]
  ring

/-- **The forest energy** (`DescendantIntegralStatement → CellMassStatement →
ForestEnergyStatement`). -/
theorem d1a_forestEnergy_proof :
    DescendantIntegralStatement → CellMassStatement → ForestEnergyStatement := by
  intro hD hM n _hn k _hk _hkn A hA Λ hΛ
  have hΛ2 : 0 < Λ + 2 := by linarith
  have hCE : 0 ≤ 2 * 6 ^ (k + 2) * (8 * (Λ + 2)) ^ k * A :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) _)) (by linarith)
  refine ⟨2 * 6 ^ (k + 2) * (8 * (Λ + 2)) ^ k * A, hCE, 2 * (Λ + 2), by linarith, ?_⟩
  intro μ _ _ a _ha R hR M hM0 hloc P T hT
  obtain ⟨z₀, hz₀, ⟨y, hy₀, hya⟩, hbelow⟩ := hT
  have hb : P.IsCell T ∧ (0, z₀).1 ≤ T.1 ∧ P.cellOf T ⊆ P.cellOf (0, z₀) := hbelow
  have hTcell : T.2 ∈ P.center T.1 := hb.1
  have hTsub : P.cellOf T ⊆ P.cell 0 z₀ := hb.2.2
  -- scales
  have hℓpos : 0 < P.scale T.1 := by
    show 0 < R / 10 ^ T.1
    exact div_pos hR (by positivity)
  have hℓR : P.scale T.1 ≤ R := by
    show R / 10 ^ T.1 ≤ R
    exact div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hscale0 : coherentScale R 0 = R := by simp [coherentScale]
  -- the centre of `T` is a support point of `T`, within `5R` of `a`
  have hzT : T.2 ∈ μ.support := P.center_subset T.1 hTcell
  have hzT_cell : T.2 ∈ P.cellOf T :=
    P.inner_subset T.1 T.2 hTcell ⟨hzT, Metric.mem_ball_self (div_pos hℓpos (by norm_num))⟩
  have hd1 : dist T.2 z₀ < 2 * R := by
    have h := Metric.mem_ball.mp (P.cell_subset_ball 0 z₀ hz₀ (hTsub hzT_cell))
    rwa [hscale0] at h
  have hd2 : dist y z₀ < 2 * R := by
    have h := Metric.mem_ball.mp (P.cell_subset_ball 0 z₀ hz₀ hy₀)
    rwa [hscale0] at h
  have hd3 : dist y a < R := Metric.mem_ball.mp hya
  have hzTa : dist T.2 a < 5 * R := by
    have h1 : dist T.2 a ≤ dist T.2 z₀ + dist z₀ a := dist_triangle _ _ _
    have h2 : dist z₀ a ≤ dist z₀ y + dist y a := dist_triangle _ _ _
    have h3 : dist z₀ y = dist y z₀ := dist_comm _ _
    linarith
  have hΛR : R ≤ Λ * R := le_mul_of_one_le_left hR.le hΛ
  have hzTB : T.2 ∈ Metric.ball a (2 * (Λ + 2) * R) := by
    rw [Metric.mem_ball]
    linarith
  -- the Carleson radius `s = 2(Λ+2)ℓ_T`
  have hspos : 0 < 2 * ((Λ + 2) * P.scale T.1) := mul_pos two_pos (mul_pos hΛ2 hℓpos)
  have hsBR : 2 * ((Λ + 2) * P.scale T.1) ≤ 2 * (Λ + 2) * R := by
    have := mul_le_mul_of_nonneg_left hℓR hΛ2.le
    linarith
  have h2ℓ : 2 * P.scale T.1 ≤ 2 * (Λ + 2) * R := by linarith
  have hℓs : 2 * P.scale T.1 ≤ 2 * ((Λ + 2) * P.scale T.1) := by
    have := le_mul_of_one_le_left hℓpos.le (show (1 : ℝ) ≤ Λ + 2 by linarith)
    linarith
  have hcar := (hloc T.2 ⟨hzT, hzTB⟩ _ hspos hsBR).2.2
  have hADR : LocalADR μ k A a (2 * (Λ + 2) * R) := fun b hb t ht htρ =>
    ⟨(hloc b hb t ht htρ).1, (hloc b hb t ht htρ).2.1⟩
  have hmass := (hM n k μ A a (2 * (Λ + 2) * R) R P hADR T hTcell hzTB h2ℓ).1
  have hdesc := hD n k μ μ.support R Λ P hΛ T hTcell
  have hTball : P.cellOf T ⊆ Metric.ball T.2 (2 * ((Λ + 2) * P.scale T.1)) :=
    (P.cell_subset_ball T.1 T.2 hTcell).trans (Metric.ball_subset_ball hℓs)
  have hA0 : A ≠ 0 := by linarith
  have hKA : 0 ≤ 2 * 6 ^ (k + 2) * (8 * (Λ + 2)) ^ k * M * A := by
    have h8 : 0 ≤ (8 * (Λ + 2)) ^ k := pow_nonneg (by linarith) _
    have := mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * 6 ^ (k + 2)) h8)
      hM0) (show (0 : ℝ) ≤ A by linarith)
    exact this
  have hkey : ENNReal.ofReal (2 * 6 ^ (k + 2)) *
        ENNReal.ofReal (M * (2 * ((Λ + 2) * P.scale T.1)) ^ k) =
      ENNReal.ofReal (2 * 6 ^ (k + 2) * (8 * (Λ + 2)) ^ k * M * A) *
        ENNReal.ofReal (A⁻¹ * (P.scale T.1 / 4) ^ k) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hKA,
      d1aforest_real_identity k hA0]
  calc P.descendantEnergy μ k Λ T
      ≤ ENNReal.ofReal (2 * 6 ^ (k + 2)) *
          ∫⁻ x in P.cellOf T, squareEnergy μ k .mixed (2 * ((Λ + 2) * P.scale T.1)) x ∂μ :=
        hdesc
    _ ≤ ENNReal.ofReal (2 * 6 ^ (k + 2)) *
          ∫⁻ x in Metric.ball T.2 (2 * ((Λ + 2) * P.scale T.1)),
            squareEnergy μ k .mixed (2 * ((Λ + 2) * P.scale T.1)) x ∂μ :=
        mul_le_mul' le_rfl (lintegral_mono_set hTball)
    _ ≤ ENNReal.ofReal (2 * 6 ^ (k + 2)) *
          ENNReal.ofReal (M * (2 * ((Λ + 2) * P.scale T.1)) ^ k) :=
        mul_le_mul' le_rfl hcar
    _ = ENNReal.ofReal (2 * 6 ^ (k + 2) * (8 * (Λ + 2)) ^ k * M * A) *
          ENNReal.ofReal (A⁻¹ * (P.scale T.1 / 4) ^ k) := hkey
    _ ≤ ENNReal.ofReal (2 * 6 ^ (k + 2) * (8 * (Λ + 2)) ^ k * M * A) * μ (P.cellOf T) :=
        mul_le_mul' le_rfl hmass
    _ = ENNReal.ofReal (2 * 6 ^ (k + 2) * (8 * (Λ + 2)) ^ k * A * M) * μ (P.cellOf T) := by
        rw [show 2 * 6 ^ (k + 2) * (8 * (Λ + 2)) ^ k * M * A =
          2 * 6 ^ (k + 2) * (8 * (Λ + 2)) ^ k * A * M by ring]

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
