import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Measure.ScaleEnergy
import ParabolicRectifiability.Metric.Hausdorff
import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import ParabolicRectifiability.Enhancements.Statements.ScaledCore
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # The missed-mass bound at one error level

Proves `b4_missed_mass_bound_proof`, with exactly the type of `b4_missed_mass_bound`.

All sums and scalar algebra are in `ENNReal`. No finiteness of `H_P^k(E)`, no measurability
of `E` or of the `U_j`, and no positivity of `C` or `e` is used. The chain is:

* `H(E \ ⋃U) ≤ H(E \ F) + H((⋃U)ᶜ ∩ F) = H(E \ F) + ν((⋃U)ᶜ)` with `ν = H⌊F`
  (`Measure.restrict_apply'`, `F` Borel; arbitrary test set);
* `ν((⋃U)ᶜ) ≤ ν((⋃_j B(z_j,5r_j))ᶜ) + Σ_j ν(B(z_j,5r_j) \ U_j) ≤ 0 + Σ_j C e (5 r_j)^k`;
* `C e (5 r_j)^k = e · (C 5^k / c) · (c r_j^k)` (here `c > 0`);
* `Σ_j c r_j^k ≤ Σ_j ν(B(z_j,r_j)) = ν(⋃_j B(z_j,r_j)) ≤ ν(X) = H(F) ≤ H(E)`
  (pairwise disjoint open balls, countable index `J ⊆ ℕ`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- Scalar identity behind the missed-mass constant: `C e (5r)^k = e · (C 5^k / c) · (c r^k)`
for `c ≠ 0`. -/
theorem b4p5_scalar_identity (C c e ρ : ℝ) (k : ℕ) (hc : c ≠ 0) :
    C * e * (5 * ρ) ^ k = e * (C * 5 ^ k / c) * (c * ρ ^ k) := by
  rw [mul_pow]
  field_simp

/-- The term identity in `ENNReal`. -/
theorem b4p5_term_eq (C c e ρ : ℝ) (k : ℕ) (hc : 0 < c) (hK : 0 ≤ C * 5 ^ k / c)
    (he : 0 ≤ e) :
    ENNReal.ofReal (C * e * (5 * ρ) ^ k) =
      ENNReal.ofReal e * ENNReal.ofReal (C * 5 ^ k / c) * ENNReal.ofReal (c * ρ ^ k) := by
  rw [← ENNReal.ofReal_mul he, ← ENNReal.ofReal_mul (mul_nonneg he hK),
    b4p5_scalar_identity C c e ρ k hc.ne']

/-- **The missed-mass bound at one error level**: the statement of `b4_missed_mass_bound`. -/
theorem b4_missed_mass_bound_proof :
    ∀ (n k : ℕ) (E F : Set (Space n)), MeasurableSet F → F ⊆ E →
    ∀ (C c e : ℝ), 0 ≤ C → 0 < c → 0 ≤ e →
      hausdorffP n k (E \ F) ≤ ENNReal.ofReal e →
    ∀ (J : Set ℕ) (z : J → Space n) (r : J → ℝ), (∀ j, 0 < r j) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∀ j, ENNReal.ofReal (c * r j ^ k) ≤ (hausdorffP n k).restrict F (Metric.ball (z j) (r j))) →
      (hausdorffP n k).restrict F (⋃ j, Metric.ball (z j) (5 * r j))ᶜ = 0 →
    ∀ U : J → Set (Space n),
      (∀ j, (hausdorffP n k).restrict F (Metric.ball (z j) (5 * r j) \ U j) ≤
        ENNReal.ofReal (C * e * (5 * r j) ^ k)) →
      hausdorffP n k (E \ ⋃ j, U j) ≤
        ENNReal.ofReal e * (1 + ENNReal.ofReal (C * 5 ^ k / c) * hausdorffP n k E) := by
  intro n k E F hF hFE C c e hC hc he hEF J z r _hr hdisj hdens hcov U hU
  have hK : 0 ≤ C * 5 ^ k / c :=
    div_nonneg (mul_nonneg hC (pow_nonneg (by norm_num) k)) hc.le
  -- The density sum: `Σ c r_j^k ≤ H(E)`.
  have hsum : ∑' j, ENNReal.ofReal (c * r j ^ k) ≤ hausdorffP n k E := by
    calc ∑' j, ENNReal.ofReal (c * r j ^ k)
        ≤ ∑' j, (hausdorffP n k).restrict F (Metric.ball (z j) (r j)) :=
          ENNReal.tsum_le_tsum hdens
      _ = (hausdorffP n k).restrict F (⋃ j, Metric.ball (z j) (r j)) :=
          (measure_iUnion (fun i j hij => hdisj i j hij)
            (fun _ => Metric.isOpen_ball.measurableSet)).symm
      _ ≤ (hausdorffP n k).restrict F univ := measure_mono (subset_univ _)
      _ = hausdorffP n k F := Measure.restrict_apply_univ F
      _ ≤ hausdorffP n k E := measure_mono hFE
  -- The missed mass inside `F`.
  have hmiss : (hausdorffP n k).restrict F (⋃ j, U j)ᶜ ≤
      ∑' j, ENNReal.ofReal (C * e * (5 * r j) ^ k) := by
    calc (hausdorffP n k).restrict F (⋃ j, U j)ᶜ
        ≤ (hausdorffP n k).restrict F ((⋃ j, Metric.ball (z j) (5 * r j))ᶜ ∪
            ⋃ j, (Metric.ball (z j) (5 * r j) \ U j)) := by
          refine measure_mono ?_
          intro x hx
          by_cases hb : x ∈ ⋃ j, Metric.ball (z j) (5 * r j)
          · right
            obtain ⟨j, hj⟩ := mem_iUnion.1 hb
            exact mem_iUnion.2 ⟨j, hj, fun hu => hx (mem_iUnion.2 ⟨j, hu⟩)⟩
          · left
            exact hb
      _ ≤ (hausdorffP n k).restrict F (⋃ j, Metric.ball (z j) (5 * r j))ᶜ +
            (hausdorffP n k).restrict F (⋃ j, (Metric.ball (z j) (5 * r j) \ U j)) :=
          measure_union_le _ _
      _ = (hausdorffP n k).restrict F (⋃ j, (Metric.ball (z j) (5 * r j) \ U j)) := by
          rw [hcov, zero_add]
      _ ≤ ∑' j, (hausdorffP n k).restrict F (Metric.ball (z j) (5 * r j) \ U j) :=
          measure_iUnion_le _
      _ ≤ ∑' j, ENNReal.ofReal (C * e * (5 * r j) ^ k) := ENNReal.tsum_le_tsum hU
  -- The weighted sum.
  have hweighted : ∑' j, ENNReal.ofReal (C * e * (5 * r j) ^ k) ≤
      ENNReal.ofReal e * ENNReal.ofReal (C * 5 ^ k / c) * hausdorffP n k E := by
    calc ∑' j, ENNReal.ofReal (C * e * (5 * r j) ^ k)
        = ∑' j, ENNReal.ofReal e * ENNReal.ofReal (C * 5 ^ k / c) *
            ENNReal.ofReal (c * r j ^ k) :=
          tsum_congr (fun j => b4p5_term_eq C c e (r j) k hc hK he)
      _ = ENNReal.ofReal e * ENNReal.ofReal (C * 5 ^ k / c) *
            ∑' j, ENNReal.ofReal (c * r j ^ k) := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal e * ENNReal.ofReal (C * 5 ^ k / c) * hausdorffP n k E :=
          mul_le_mul_right hsum _
  calc hausdorffP n k (E \ ⋃ j, U j)
      ≤ hausdorffP n k ((E \ F) ∪ ((⋃ j, U j)ᶜ ∩ F)) := by
        refine measure_mono ?_
        intro x hx
        by_cases hxF : x ∈ F
        · exact Or.inr ⟨hx.2, hxF⟩
        · exact Or.inl ⟨hx.1, hxF⟩
    _ ≤ hausdorffP n k (E \ F) + hausdorffP n k ((⋃ j, U j)ᶜ ∩ F) := measure_union_le _ _
    _ = hausdorffP n k (E \ F) + (hausdorffP n k).restrict F (⋃ j, U j)ᶜ := by
        rw [Measure.restrict_apply' hF]
    _ ≤ ENNReal.ofReal e + ENNReal.ofReal e * ENNReal.ofReal (C * 5 ^ k / c) *
          hausdorffP n k E := add_le_add hEF (hmiss.trans hweighted)
    _ = ENNReal.ofReal e * (1 + ENNReal.ofReal (C * 5 ^ k / c) * hausdorffP n k E) := by
        rw [mul_add, mul_one, mul_assoc]

end ParabolicRectifiability.Characterization
