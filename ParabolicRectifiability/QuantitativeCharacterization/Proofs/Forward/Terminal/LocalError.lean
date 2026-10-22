import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # The local error

Proof of `d1c_localError_proof : OwnerStatement → LocalErrorStatement` (implication form over
the owner statement `d1c_owner`).

For `Λ ≥ 4000` and an admissible pair `(j, g)` the owner statement supplies a member `O` with
`ℓ_O ≤ 2000 r_j` and `P(g, 40 r_j) ⊆ P(z_O, Λ ℓ_O)`. Then
`fit μ Π_g g (40 r_j) ≤ fit μ Π_O g (40 r_j)` (minimality of the local fit),
`≤ fit μ Π_O z_O (Λ ℓ_O)` (ball inclusion), `= (Λ ℓ_O)^{k+2} · modelCoeff(Π_O, O)`,
`≤ (Λ ℓ_O)^{k+2} b` (the chain-budget term of `O` itself), `≤ (2000 Λ)^{k+2} b r_j^{k+2}`.
For `b ≤ 0` the budget forces a zero fit. Every fit is of the original `μ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- Cell sides are positive. -/
theorem d1cerr_scale_pos (P : DirectPartition E ℓ₀) (j : ℕ) : 0 < P.scale j := by
  unfold DirectPartition.scale coherentScale
  exact div_pos P.scale_pos (pow_pos (by norm_num) _)

/-- The coefficient-ball fit of a member's own model is at most `(Λ ℓ_Q)^{k+2} b`: the
normalized error `modelCoeff` is the `Q`-term of the chain budget of `Q`. -/
theorem d1cerr_fit_le_budget (𝒢 : GoodRegion P μ k Λ b) (Q : ℕ × Space n)
    (hQ : Q ∈ 𝒢.members) (hpos : 0 < Λ * P.scale Q.1) :
    fit μ (𝒢.model Q) Q.2 (Λ * P.scale Q.1) ≤
      ENNReal.ofReal (Λ * P.scale Q.1) ^ (k + 2) * ENNReal.ofReal b := by
  have hbelow : P.IsBelow Q Q := ⟨(𝒢.below_root Q hQ).1, le_rfl, subset_rfl⟩
  have hcoeff : P.modelCoeff μ Λ (𝒢.model Q) Q ≤ ENNReal.ofReal b := by
    refine le_trans ?_ (𝒢.budget Q hQ)
    exact ENNReal.le_tsum
      (f := fun Q' : {Q' : ℕ × Space n // Q' ∈ 𝒢.members ∧ P.IsBelow Q Q'} =>
        P.modelCoeff μ Λ (𝒢.model Q'.1) Q'.1) ⟨Q, hQ, hbelow⟩
  have hx0 : ENNReal.ofReal (Λ * P.scale Q.1) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  have hxt : ENNReal.ofReal (Λ * P.scale Q.1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have heq : fit μ (𝒢.model Q) Q.2 (Λ * P.scale Q.1) =
      ENNReal.ofReal (Λ * P.scale Q.1) ^ (k + 2) * P.modelCoeff μ Λ (𝒢.model Q) Q := by
    rw [DirectPartition.modelCoeff, ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel hx0 hxt,
      one_pow, one_mul]
  rw [heq]
  gcongr

end

/-- **The local error** (`LocalErrorStatement`): for `Λ ≥ 4000` and every admissible `(j, g)`,
`fit μ Π_g g (40 r_j) ≤ (2000 Λ)^{k+2} b r_j^{k+2}`. -/
theorem d1c_localError_proof : OwnerStatement → LocalErrorStatement := by
  intro hOwner n E ℓ₀ P μ k Λ b 𝒢 fits hΛ j g hadm
  obtain ⟨hg, hρ⟩ := hadm
  obtain ⟨O, hO, -, hO2, -, -, -, hincl⟩ := hOwner n E ℓ₀ P μ k Λ b 𝒢 j g hg hρ
  have hΛ0 : 0 < Λ := by linarith
  have hℓ : 0 < P.scale O.1 := d1cerr_scale_pos P O.1
  have hpos : 0 < Λ * P.scale O.1 := mul_pos hΛ0 hℓ
  have hball : Metric.ball g (40 * stageScale 𝒢 j) ⊆ Metric.ball O.2 (Λ * P.scale O.1) :=
    hincl hΛ
  have hkey : fit μ (fits.model j g) g (40 * stageScale 𝒢 j) ≤
      ENNReal.ofReal (Λ * P.scale O.1) ^ (k + 2) * ENNReal.ofReal b :=
    calc fit μ (fits.model j g) g (40 * stageScale 𝒢 j)
        ≤ fit μ (𝒢.model O) g (40 * stageScale 𝒢 j) := fits.minimal j g (𝒢.model O)
      _ ≤ fit μ (𝒢.model O) O.2 (Λ * P.scale O.1) := MeasureTheory.lintegral_mono_set hball
      _ ≤ _ := d1cerr_fit_le_budget 𝒢 O hO hpos
  rcases le_or_gt b 0 with hb | hb
  · rw [ENNReal.ofReal_of_nonpos hb, mul_zero] at hkey
    exact hkey.trans zero_le
  · refine hkey.trans ?_
    rw [← ENNReal.ofReal_pow hpos.le, ← ENNReal.ofReal_mul (pow_nonneg hpos.le _)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : Λ * P.scale O.1 ≤ 2000 * Λ * stageScale 𝒢 j := by
      have h := mul_le_mul_of_nonneg_left hO2 hΛ0.le
      calc Λ * P.scale O.1 ≤ Λ * (2000 * stageScale 𝒢 j) := h
        _ = 2000 * Λ * stageScale 𝒢 j := by ring
    have h2 : (Λ * P.scale O.1) ^ (k + 2) ≤
        (2000 * Λ) ^ (k + 2) * stageScale 𝒢 j ^ (k + 2) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hpos.le h1 _
    calc (Λ * P.scale O.1) ^ (k + 2) * b
        ≤ (2000 * Λ) ^ (k + 2) * stageScale 𝒢 j ^ (k + 2) * b :=
          mul_le_mul_of_nonneg_right h2 hb.le
      _ = (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 j ^ (k + 2) := by ring

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
