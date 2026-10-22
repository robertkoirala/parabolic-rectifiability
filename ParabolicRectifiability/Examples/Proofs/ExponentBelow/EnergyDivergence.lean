import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements

/-! # Divergence of the lacunary energy from a nonsummable power tail

Apply the lower-energy estimate on the full interval. A nonsummable
real sequence stays nonsummable after a finite shift, so its nonnegative tail
has infinite `ENNReal` sum. The positive lower-energy coefficient then forces
the energy to be `⊤`.
-/

namespace ParabolicRectifiability.Examples

private theorem e2_below_power_tail_tsum_eq_top {a : ℕ → ℝ} {p : ℝ}
    (ha : ∀ j, 0 < a j) (hnot : ¬ Summable (fun j => a j ^ p)) (j₀ : ℕ) :
    ∑' j, ENNReal.ofReal (a (j + j₀) ^ p) = ⊤ := by
  let tail : ℕ → NNReal := fun j =>
    ⟨a (j + j₀) ^ p, Real.rpow_nonneg (le_of_lt (ha (j + j₀))) p⟩
  have htail_not_summable : ¬ Summable (fun j => (tail j : ℝ)) := by
    intro htail
    have htail' : Summable (fun j : ℕ => a (j + j₀) ^ p) := by
      convert htail using 1
      funext j
      rfl
    exact hnot ((summable_nat_add_iff (f := fun j : ℕ => a j ^ p) j₀).mp htail')
  have htop : (∑' j, (tail j : ENNReal)) = ⊤ :=
    ENNReal.tsum_coe_eq_top_iff_not_summable_coe.mpr htail_not_summable
  have hterm (j : ℕ) : ENNReal.ofReal (a (j + j₀) ^ p) = (tail j : ENNReal) := by
    change ENNReal.ofReal (tail j : ℝ) = (tail j : ENNReal)
    exact ENNReal.ofReal_coe_nnreal
  calc
    ∑' j, ENNReal.ofReal (a (j + j₀) ^ p) = ∑' j, (tail j : ENNReal) :=
      tsum_congr hterm
    _ = ⊤ := htop

/-- A nonsummable amplitude power makes every interior lacunary energy infinite. -/
theorem e2_below_divergence_proof :
    LacunaryLowerEnergyStatement → E2BelowDivergenceStatement := by
  intro hLower ε a N hε hεle hData p hp hnot R hR t ht
  rcases hLower with ⟨c, hc, hLower⟩
  obtain ⟨j₀, hLowerBound⟩ := (hLower ε a N hε hεle hData).2 t ht R hR
  have henergy := hLowerBound p hp
  have htail := e2_below_power_tail_tsum_eq_top hData.amplitude_pos hnot j₀
  have hcoeff : ENNReal.ofReal (c p * ε ^ p) ≠ 0 := by
    apply ENNReal.ofReal_ne_zero_iff.mpr
    exact mul_pos (hc p hp) (Real.rpow_pos_of_pos hε p)
  rw [htail, ENNReal.mul_top hcoeff] at henergy
  exact top_unique henergy

end ParabolicRectifiability.Examples
