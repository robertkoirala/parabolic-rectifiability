import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Coverage

/-! # The model balls

Proof of `ModelBallStatement`.

For a good root `S` (a forest cell, `roots_forest`):
* `z_S ∈ 𝒵_{j} ⊆ supp μ` (`center_subset`) and `z_S ∈ cell S` (`inner_subset`, `ℓ_S/4 > 0`);
* the top cell `cell 0 z₀ ⊇ cell S` meets `P(a,R)` in some `y`; with `cell_subset_ball` at level
  `0` (`ℓ_0 = R`), `d(z_S,a) ≤ d(z_S,z₀) + d(z₀,y) + d(y,a) < 2R + 2R + R = 5R`, and `4 ℓ_S ≤ 4R`, so `P(z_S, 4 ℓ_S) ⊆ P(a, 9R)`;
* a centre `c ∈ TN.centers` (`centers_nonempty`) lies in `closure (cell S)`
  (`centers_subset_closure`, `region_root`) `⊆ closedBall z_S (2 ℓ_S) ⊆ P(z_S, 4 ℓ_S)`, and
  `c ∈ Γ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Coverage

open ParabolicRectifiability.Foundations

/-- The scale bounds `0 < ℓ_j`, `ℓ_j ≤ ℓ₀` and `ℓ_0 = ℓ₀`. -/
theorem d1fball_scale_bounds {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}
    (P : DirectPartition E ℓ₀) (j : ℕ) : 0 < P.scale j ∧ P.scale j ≤ ℓ₀ := by
  have h0 : 0 < ℓ₀ := P.scale_pos
  have hpow : (1 : ℝ) ≤ 10 ^ j := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < 10 ^ j := by positivity
  simp only [DirectPartition.scale, coherentScale]
  refine ⟨div_pos h0 hpos, ?_⟩
  rw [div_le_iff₀ hpos]
  nlinarith

/-- `ℓ_0 = ℓ₀`. -/
theorem d1fball_coherentScale_zero (ℓ₀ : ℝ) : coherentScale ℓ₀ 0 = ℓ₀ := by
  simp [coherentScale]

/-- **The model balls**: for every good root `S`, the centre `z_S` lies in `supp μ` and in its
cell, `P(z_S, 4 ℓ_S) ⊆ P(a, 9R)`, and `P(z_S, 4 ℓ_S)` contains a point of `Γ`. -/
theorem d1f_modelBall_proof : ModelBallStatement := by
  intro n μ a R P k Λ b K SD S δ κ θ γ TN Γ hΓ
  obtain ⟨z₀, hz₀, ⟨y, hy0, hya⟩, hcell, -, hsub⟩ := SD.roots_forest S.1 S.2
  obtain ⟨hℓpos, hℓR⟩ := d1fball_scale_bounds P S.1.1
  have hR : 0 < R := P.scale_pos
  have hzE : S.1.2 ∈ μ.support := P.center_subset S.1.1 hcell
  have hzS : S.1.2 ∈ P.cellOf S.1 := by
    refine P.inner_subset S.1.1 S.1.2 hcell ⟨hzE, ?_⟩
    rw [Metric.mem_ball, dist_self]
    have : 0 < coherentScale R S.1.1 := hℓpos
    exact div_pos this (by norm_num)
  have hball0 : P.cell 0 z₀ ⊆ Metric.ball z₀ (2 * R) := by
    have h := P.cell_subset_ball 0 z₀ hz₀
    rwa [d1fball_coherentScale_zero] at h
  have hz5 : dist S.1.2 a < 5 * R := by
    have h1 : dist S.1.2 z₀ < 2 * R := Metric.mem_ball.1 (hball0 (hsub hzS))
    have h2 : dist y z₀ < 2 * R := Metric.mem_ball.1 (hball0 hy0)
    have h3 : dist y a < R := Metric.mem_ball.1 hya
    have h4 : dist S.1.2 a ≤ dist S.1.2 z₀ + dist z₀ y + dist y a := dist_triangle4 _ _ _ _
    rw [dist_comm z₀ y] at h4
    linarith
  refine ⟨hzE, by linarith, ?_, ?_⟩
  · intro x hx
    rw [Metric.mem_ball] at hx ⊢
    have := dist_triangle x S.1.2 a
    linarith
  · obtain ⟨c, hc⟩ := TN.centers_nonempty
    refine ⟨c, ?_, hΓ hc⟩
    have hcl : c ∈ closure (P.cellOf S.1) := by
      have h := TN.centers_subset_closure hc
      simp only [GoodRegion.rootCell, SD.region_root S] at h
      exact h
    have hcb : P.cellOf S.1 ⊆ Metric.ball S.1.2 (2 * P.scale S.1.1) :=
      P.cell_subset_ball S.1.1 S.1.2 hcell
    have hc2 : c ∈ Metric.closedBall S.1.2 (2 * P.scale S.1.1) :=
      Metric.closure_ball_subset_closedBall (closure_mono hcb hcl)
    exact Metric.closedBall_subset_ball (by linarith) hc2

end Coverage

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
