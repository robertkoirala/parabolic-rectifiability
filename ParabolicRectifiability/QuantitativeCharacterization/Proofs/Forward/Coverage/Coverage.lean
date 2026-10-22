import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Coverage

/-! # Coverage of good cells by the centres, with the constant `1/99`

Proof of `Terminal.StopScaleLipschitzStatement → CoverageStatement`, in implication form: the
stopping-scale Lipschitz statement of the terminal construction is a hypothesis.

For `z ∈ Q ∈ 𝒢.members` we have `z ∈ S = rootCell` (`below_root`). By `TN.source_eq`:
* `z ∈ limitCore`: then `z ∈ TN.centers ⊆ Γ` (`TN.core_eq`), so `infDist z Γ = 0`;
* `z ∈ TN.assignment c`, `c ∈ TN.centers`, `0 < d_c`: `dist z c < d_c` (`assignment_subset`),
  `100 d_c ≤ ρ(c)` (`TN.cutoff`), `ρ(c) ≤ ρ(z) + dist c z` (clause 2) and `ρ(z) ≤ ℓ_Q`
  (clause 4), hence `99 d_c < ℓ_Q` and `infDist z Γ ≤ dist z c < d_c < ℓ_Q/99`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Coverage

open ParabolicRectifiability.Foundations

/-- The cell sides `ℓ_j = ℓ₀/10^j` of a direct partition are positive. -/
theorem d1fcover_scale_pos {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (j : ℕ) : 0 < P.scale j := by
  unfold DirectPartition.scale coherentScale
  exact div_pos P.scale_pos (pow_pos (by norm_num) _)

/-- **Coverage with the constant `1/99`**: given the stopping-scale Lipschitz statement
`Terminal.StopScaleLipschitzStatement`, every point `z` of a member
cell `Q` of a good region has `infDist z Γ ≤ ℓ_Q/99` for every `Γ ⊇ TN.centers`. -/
theorem d1f_coverage_proof : Terminal.StopScaleLipschitzStatement → CoverageStatement := by
  intro hLip n E ℓ₀ P μ k Λ b 𝒢 δ κ θ γ TN Γ hΓ Q hQ z hz
  obtain ⟨-, hLip2, -, hLip4⟩ := hLip n E ℓ₀ P μ k Λ b 𝒢
  have hscale : 0 < P.scale Q.1 := d1fcover_scale_pos P Q.1
  have hρz : 𝒢.stopScale z ≤ P.scale Q.1 := hLip4 Q hQ z hz
  obtain ⟨-, -, hsub⟩ := 𝒢.below_root Q hQ
  have hzS : z ∈ 𝒢.rootCell := hsub hz
  rw [TN.source_eq] at hzS
  rcases hzS with ⟨-, hcore⟩ | hA
  · -- core point: `z ∈ TN.centers ⊆ Γ`
    rw [← TN.core_eq] at hcore
    rw [Metric.infDist_zero_of_mem (hΓ hcore.1)]
    exact div_nonneg hscale.le (by norm_num)
  · -- assigned point: `z ∈ A_c`, `dist z c < d_c < ℓ_Q/99`
    obtain ⟨c, hcmem, hzc⟩ := Set.mem_iUnion₂.mp hA
    obtain ⟨hc, hrc⟩ := hcmem
    have hzball : dist z c < TN.radius c := ((TN.assignment_subset c hc hrc) hzc).2
    have hcut : 100 * TN.radius c ≤ 𝒢.stopScale c := TN.cutoff c hc hrc
    have hρc : 𝒢.stopScale c ≤ 𝒢.stopScale z + dist c z := hLip2 c z
    have hdist : dist c z = dist z c := dist_comm c z
    calc Metric.infDist z Γ ≤ dist z c := Metric.infDist_le_dist_of_mem (hΓ hc)
      _ ≤ P.scale Q.1 / 99 := by linarith

end Coverage

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
