import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Coverage

/-! # The good scale sets are covered by their references

Proof of `CoverageStatement → GoodSlabCoverStatement`, in implication form: the coverage
statement `CoverageStatement` is a hypothesis.

For `(z,r) ∈ slab Q`, `Q ∈ (SD.region S).members`: `z ∈ Q ∩ P(a,R)`, `ℓ_Q/10 ≤ r < ℓ_Q`.
* `Q ⊆ cell of S.1 ⊆ P(z_S, 2 ℓ_S) ⊆ P(z_S, 4 ℓ_S)` (`below_root`, `region_root`,
  `root_isCell`, `cell_subset_ball`);
* `ℓ_Q ≤ ℓ_S` (`coherentScale` antitone in the level, `S.1.1 ≤ Q.1`), so `r < ℓ_Q < 4 ℓ_S`;
* coverage gives `infDist z Γ ≤ ℓ_Q/99`; with `L ≥ 10/99`,
  `L⁻¹ infDist z Γ ≤ (99/10)(ℓ_Q/99) = ℓ_Q/10 ≤ r`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Coverage

open ParabolicRectifiability.Foundations

/-- The cell sides `ℓ_j = ℓ₀/10^j` of a direct partition are positive. -/
theorem d1fgood_scale_pos {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (j : ℕ) : 0 < P.scale j := by
  unfold DirectPartition.scale coherentScale
  exact div_pos P.scale_pos (pow_pos (by norm_num) _)

/-- The cell sides decrease with the level: `i ≤ j → ℓ_j ≤ ℓ_i`. -/
theorem d1fgood_scale_anti {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    {i j : ℕ} (h : i ≤ j) : P.scale j ≤ P.scale i := by
  unfold DirectPartition.scale coherentScale
  exact div_le_div_of_nonneg_left P.scale_pos.le (pow_pos (by norm_num) i)
    (pow_le_pow_right₀ (by norm_num) h)

/-- **The good scale sets are covered by their references**: given `CoverageStatement`, for `L ≥ 10/99` every pair `(z,r)` of the scale set of
a good root `S` has `z ∈ P(a,R) ∩ P(z_S, 4 ℓ_S)`, `L⁻¹ infDist z Γ ≤ r` and `r < 4 ℓ_S`. -/
theorem d1f_goodSlabCover_proof : CoverageStatement → GoodSlabCoverStatement := by
  intro hCov n μ a R P k Λ b K SD S δ κ θ γ TN Γ hΓ L hL p hp
  simp only [goodSlabs, slab, Set.mem_iUnion, Set.mem_prod, Set.mem_inter_iff, Set.mem_Ico,
    exists_prop] at hp
  obtain ⟨Q, hQ, ⟨hzQ, hza⟩, hr1, hr2⟩ := hp
  have hroot : (SD.region S).root = S.1 := SD.region_root S
  obtain ⟨-, hlev, hsub⟩ := (SD.region S).below_root Q hQ
  rw [hroot] at hlev hsub
  have hcell : P.IsCell S.1 := by
    rw [← hroot]
    exact (SD.region S).root_isCell
  have hball : P.cellOf S.1 ⊆ Metric.ball S.1.2 (2 * P.scale S.1.1) :=
    P.cell_subset_ball S.1.1 S.1.2 hcell
  have hscaleQ : 0 < P.scale Q.1 := d1fgood_scale_pos P Q.1
  have hscaleS : 0 < P.scale S.1.1 := d1fgood_scale_pos P S.1.1
  have hQS : P.scale Q.1 ≤ P.scale S.1.1 := d1fgood_scale_anti P hlev
  have hcov : Metric.infDist p.1 Γ ≤ P.scale Q.1 / 99 :=
    hCov n μ.support R P μ k Λ b (SD.region S) δ κ θ γ TN Γ hΓ Q hQ p.1 hzQ
  rw [Set.mem_ofPred_eq]
  refine ⟨⟨hza, ?_⟩, ?_, ?_⟩
  · exact Metric.ball_subset_ball (by linarith) (hball (hsub hzQ))
  · have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
    have hr0 : 0 ≤ p.2 := le_trans (div_nonneg hscaleQ.le (by norm_num)) hr1
    rw [inv_mul_eq_div, div_le_iff₀ hLpos]
    calc Metric.infDist p.1 Γ ≤ P.scale Q.1 / 99 := hcov
      _ = P.scale Q.1 / 10 * (10 / 99) := by ring
      _ ≤ p.2 * L := mul_le_mul hr1 hL (by norm_num) hr0
  · linarith

end Coverage

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
