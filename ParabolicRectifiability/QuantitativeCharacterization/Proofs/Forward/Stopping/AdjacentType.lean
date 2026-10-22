import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Stopping

/-! # Adjacent-cell type rigidity

Proof of `d1b_adjacentType_proof`, in implication form
`PartitionTreeStatement → PartitionEnergy.FittingGapStatement → AdjacentTypeStatement`.

Route. For `Λ ≥ 3` take `c` from the fitting gap and `b₀ = c/[Λ^p(10^p+1)]`, `p = k + 2`.
For a parent/child pair `Q' ⊃ Q` put `ℓ = ℓ_Q`, so `ℓ_{Q'} = 10 ℓ`. The common child-centred
ball `P(z_Q, ℓ)` lies in the child's fitting ball `P(z_Q, Λ ℓ)` and in the parent's fitting ball
`P(z_{Q'}, Λ ℓ_{Q'})`, since `z_Q ∈ Q ⊆ Q' ⊆ P(z_{Q'}, 2 ℓ_{Q'})` and `ℓ + 20 ℓ ≤ 30 ℓ ≤ 10 Λ ℓ`.
`fit` is monotone in the ball, and `modelCoeff ≤ b/2` gives `fit ≤ (b/2)(Λ ℓ_cell)^p` on the
cell's fitting ball. The fitting gap at the support point `z_Q` and radius `ℓ` (with
`P(z_Q, 4ℓ)` in the buffer) gives `c ℓ^p ≤ (b/2) Λ^p (10^p + 1) ℓ^p ≤ (c/2) ℓ^p`, a
contradiction. Helpers carry the prefix `d1badj_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

section AdjacentType

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}

/-- `fit` is monotone in the fitting ball. -/
theorem d1badj_fit_mono {k : ℕ} {T : FamilyKind} (μ : Measure (Space n)) (L : Models n k T)
    {z z' : Space n} {r r' : ℝ} (h : Metric.ball z r ⊆ Metric.ball z' r') :
    fit μ L z r ≤ fit μ L z' r' := by
  unfold fit
  exact lintegral_mono_set h

/-- A normalized error `modelCoeff ≤ β` bounds the unnormalized fit on the coefficient ball by
`(Λ ℓ_Q)^{k+2} β`. -/
theorem d1badj_fit_le_of_modelCoeff_le (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    {k : ℕ} {T : FamilyKind} (Λ : ℝ) (L : Models n k T) (Q : ℕ × Space n) (β : ℝ)
    (hpos : 0 < Λ * P.scale Q.1) (h : P.modelCoeff μ Λ L Q ≤ ENNReal.ofReal β) :
    fit μ L Q.2 (Λ * P.scale Q.1) ≤ ENNReal.ofReal ((Λ * P.scale Q.1) ^ (k + 2) * β) := by
  unfold DirectPartition.modelCoeff at h
  obtain ⟨x, hx⟩ : ∃ x : ℝ≥0∞, x = ENNReal.ofReal (Λ * P.scale Q.1) := ⟨_, rfl⟩
  rw [← hx] at h
  have hx0 : x ≠ 0 := by rw [hx]; exact (ENNReal.ofReal_pos.2 hpos).ne'
  have hxt : x ≠ ⊤ := by rw [hx]; exact ENNReal.ofReal_ne_top
  calc fit μ L Q.2 (Λ * P.scale Q.1)
      = (x ^ (k + 2) * x⁻¹ ^ (k + 2)) * fit μ L Q.2 (Λ * P.scale Q.1) := by
        rw [← mul_pow, ENNReal.mul_inv_cancel hx0 hxt, one_pow, one_mul]
    _ = x ^ (k + 2) * (x⁻¹ ^ (k + 2) * fit μ L Q.2 (Λ * P.scale Q.1)) := mul_assoc _ _ _
    _ ≤ x ^ (k + 2) * ENNReal.ofReal β := by gcongr
    _ = ENNReal.ofReal ((Λ * P.scale Q.1) ^ (k + 2) * β) := by
        rw [ENNReal.ofReal_mul (pow_nonneg hpos.le _), ENNReal.ofReal_pow hpos.le, hx]

/-- The real contradiction: `c ℓ^p ≤ (b/2)(Λℓ)^p + (b/2)(Λ·10ℓ)^p` is impossible for
`0 < b ≤ c/[Λ^p(10^p+1)]`. -/
theorem d1badj_real_contra {c Λ ℓ b : ℝ} {p : ℕ} (hc : 0 < c) (hΛ : 0 < Λ) (hℓ : 0 < ℓ)
    (hbb : b ≤ c / (Λ ^ p * (10 ^ p + 1)))
    (h : c * ℓ ^ p ≤ (Λ * ℓ) ^ p * (b / 2) + (Λ * (10 * ℓ)) ^ p * (b / 2)) : False := by
  rw [mul_pow, mul_pow, mul_pow] at h
  have hX : 0 < Λ ^ p := pow_pos hΛ p
  have hY : 0 < (10 : ℝ) ^ p := pow_pos (by norm_num) p
  have hD : 0 < Λ ^ p * (10 ^ p + 1) := by positivity
  have hb' : b * (Λ ^ p * (10 ^ p + 1)) ≤ c := (le_div_iff₀ hD).1 hbb
  have hL : 0 < ℓ ^ p := pow_pos hℓ p
  have h2 := mul_le_mul_of_nonneg_right hb' hL.le
  have h3 := mul_pos hc hL
  nlinarith

/-- **Adjacent-cell type rigidity** (`AdjacentTypeStatement`, in implication form). -/
theorem d1b_adjacentType_proof :
    PartitionTreeStatement → PartitionEnergy.FittingGapStatement → AdjacentTypeStatement := by
  intro hTree hGap n hn k hk hkn A hA Λ hΛ
  obtain ⟨c, hc, hgap⟩ := hGap n hn k hk hkn A hA
  have hΛpos : 0 < Λ := by linarith
  have hD : 0 < Λ ^ (k + 2) * (10 ^ (k + 2) + 1) := by positivity
  refine ⟨c / (Λ ^ (k + 2) * (10 ^ (k + 2) + 1)), div_pos hc hD, ?_⟩
  intro b hb hbb μ a ρ ℓ₀ hADR P Q Q' hQ' hbelow hlev hball h4 H V
  have hT := hTree n μ.support ℓ₀ P
  have hQcell : P.IsCell Q := hbelow.1
  have hzsupp : Q.2 ∈ μ.support := P.center_subset Q.1 hQcell
  have hℓ : 0 < P.scale Q.1 := hT.scale_pos Q.1
  have hscale : P.scale Q'.1 = 10 * P.scale Q.1 := by
    have h := hT.scale_succ Q'.1
    rw [hlev] at h
    rw [h]
    ring
  -- the child centre lies in the parent's ball `P(z_{Q'}, 2 ℓ_{Q'})`
  have hzQ' : Q.2 ∈ Metric.ball Q'.2 (2 * coherentScale ℓ₀ Q'.1) :=
    P.cell_subset_ball Q'.1 Q'.2 hQ' (hbelow.2.2 (hT.center_mem_cell Q hQcell))
  have hd : dist Q.2 Q'.2 < 2 * P.scale Q'.1 := hzQ'
  have hpos1 : 0 < Λ * P.scale Q.1 := mul_pos hΛpos hℓ
  have hpos2 : 0 < Λ * P.scale Q'.1 := by rw [hscale]; positivity
  -- the common child-centred ball lies in both fitting balls
  have hsub1 : Metric.ball Q.2 (P.scale Q.1) ⊆ Metric.ball Q.2 (Λ * P.scale Q.1) :=
    Metric.ball_subset_ball (le_mul_of_one_le_left hℓ.le (by linarith))
  have hsub2 : Metric.ball Q.2 (P.scale Q.1) ⊆ Metric.ball Q'.2 (Λ * P.scale Q'.1) := by
    intro x hx
    rw [Metric.mem_ball] at hx ⊢
    have h3 : 3 * P.scale Q.1 ≤ Λ * P.scale Q.1 := mul_le_mul_of_nonneg_right hΛ hℓ.le
    have htri := dist_triangle x Q.2 Q'.2
    rw [hscale] at hd ⊢
    nlinarith
  have hS1 : 0 ≤ (Λ * P.scale Q.1) ^ (k + 2) * (b / 2) :=
    mul_nonneg (pow_nonneg hpos1.le _) (by linarith)
  have hS2 : 0 ≤ (Λ * P.scale Q'.1) ^ (k + 2) * (b / 2) :=
    mul_nonneg (pow_nonneg hpos2.le _) (by linarith)
  -- a model on the child and a model on the parent, both with small normalized error
  have key : ∀ (T₁ T₂ : FamilyKind) (L₁ : Models n k T₁) (L₂ : Models n k T₂),
      P.modelCoeff μ Λ L₁ Q ≤ ENNReal.ofReal (b / 2) →
      P.modelCoeff μ Λ L₂ Q' ≤ ENNReal.ofReal (b / 2) →
      fit μ L₁ Q.2 (P.scale Q.1) + fit μ L₂ Q.2 (P.scale Q.1) ≤
        ENNReal.ofReal ((Λ * P.scale Q.1) ^ (k + 2) * (b / 2) +
          (Λ * P.scale Q'.1) ^ (k + 2) * (b / 2)) := by
    intro T₁ T₂ L₁ L₂ h₁ h₂
    have e₁ := (d1badj_fit_mono μ L₁ hsub1).trans
      (d1badj_fit_le_of_modelCoeff_le P μ Λ L₁ Q (b / 2) hpos1 h₁)
    have e₂ := (d1badj_fit_mono μ L₂ hsub2).trans
      (d1badj_fit_le_of_modelCoeff_le P μ Λ L₂ Q' (b / 2) hpos2 h₂)
    rw [ENNReal.ofReal_add hS1 hS2]
    exact add_le_add e₁ e₂
  -- the fitting gap at the support point `z_Q`, radius `ℓ_Q`
  have hg := hgap μ a ρ hADR Q.2 hzsupp (P.scale Q.1) hℓ hball h4 H V
  have finish : ENNReal.ofReal (c * P.scale Q.1 ^ (k + 2)) ≤
      ENNReal.ofReal ((Λ * P.scale Q.1) ^ (k + 2) * (b / 2) +
          (Λ * P.scale Q'.1) ^ (k + 2) * (b / 2)) → False := by
    intro hle
    have hr := (ENNReal.ofReal_le_ofReal_iff (add_nonneg hS1 hS2)).1 hle
    rw [hscale] at hr
    exact d1badj_real_contra hc hΛpos hℓ hbb hr
  rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · exact finish (hg.trans (key _ _ H V h₁ h₂))
  · have hk := key _ _ V H h₁ h₂
    rw [add_comm] at hk
    exact finish (hg.trans hk)

end AdjacentType

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
