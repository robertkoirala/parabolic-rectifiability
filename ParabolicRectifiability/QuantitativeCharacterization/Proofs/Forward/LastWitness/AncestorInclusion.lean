import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.LastWitness

/-! # The ancestor inclusion (`d1d_ancestorInclusion`)

Proof of `Forward.Witness.d1d_ancestorInclusion_proof : AncestorInclusionStatement`.

Write `c(m) = ℓ₀/10^m` (the side of the level-`m` cells), `R = root.1`, so `ℓ_* = c(R)`,
`r_j = 48 c(R + j)`, `ℓ_A = c(A.1)` with `A.1 = R + (j + 1 - 11)`.

* **Ratio.** `R + (j + 1) ≤ A.1 + 11`, hence `ℓ_A / 10^{11} ≤ c(R + j + 1)`, i.e.
  `ℓ_A ≤ 10^{11} r_{j+1} / 48 ≤ 10^{12} r_{j+1}` (the exact ratio is `10^{j+1}/48` for `j ≤ 10`
  and `10^{11}/48` for `j ≥ 11`).
* **Clamped, `j < 10`.** `A.1 = R`; `z ∈ S ⊆ P(q, 2 ℓ_*)` and `z_A ∈ cell A ⊆ S`, so for
  `y ∈ P(z, 40 r_j)`: `d_P(y, z_A) < 1920 ℓ_* + 4 ℓ_* < 4000 ℓ_* ≤ Λ ℓ_A`.
* **Unclamped, `j ≥ 10`.** `A.1 + 10 = R + j`, so `r_j = 48 · 10^{-10} ℓ_A`; `A.1 ≤ O.1` gives
  `ℓ_O ≤ ℓ_A`, `j ≤ i` gives `r_i ≤ r_j`, and `z_O ∈ cell O ⊆ cell A ⊆ P(z_A, 2 ℓ_A)`, so
  `d_P(y, z_A) < 64 r_j + 2000 r_i + 2 ℓ_O + 2 ℓ_A ≤ 2064 r_j + 4 ℓ_A < 5 ℓ_A ≤ Λ ℓ_A`.

Every helper carries the prefix `d1dancinc_`.
-/

set_option autoImplicit false

noncomputable section

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Witness

theorem d1dancinc_c_pos {ℓ₀ : ℝ} (h : 0 < ℓ₀) (m : ℕ) : 0 < coherentScale ℓ₀ m := by
  unfold coherentScale
  exact div_pos h (pow_pos (by norm_num) m)

theorem d1dancinc_c_anti {ℓ₀ : ℝ} (h : 0 < ℓ₀) {m m' : ℕ} (hm : m ≤ m') :
    coherentScale ℓ₀ m' ≤ coherentScale ℓ₀ m := by
  unfold coherentScale
  exact div_le_div_of_nonneg_left h.le (pow_pos (by norm_num) m)
    (pow_le_pow_right₀ (by norm_num) hm)

theorem d1dancinc_c_add (ℓ₀ : ℝ) (m d : ℕ) :
    coherentScale ℓ₀ (m + d) = coherentScale ℓ₀ m / 10 ^ d := by
  unfold coherentScale
  rw [pow_add, div_div]

theorem d1dancinc_r_eq (ℓ₀ : ℝ) (R j : ℕ) :
    coherentScale (48 * coherentScale ℓ₀ R) j = 48 * coherentScale ℓ₀ (R + j) := by
  rw [d1dancinc_c_add]
  unfold coherentScale
  ring

/-- The centre of a cell lies in its cell. -/
theorem d1dancinc_center_mem_cell {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}
    (P : DirectPartition E ℓ₀) {Q : ℕ × Space n} (hQ : P.IsCell Q) : Q.2 ∈ P.cellOf Q :=
  P.inner_subset Q.1 Q.2 hQ
    ⟨P.center_subset Q.1 hQ,
      Metric.mem_ball_self (div_pos (d1dancinc_c_pos P.scale_pos Q.1) (by norm_num))⟩

/-- A cell lies in the ball of twice its side around its centre. -/
theorem d1dancinc_cell_subset_ball {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}
    (P : DirectPartition E ℓ₀) {Q : ℕ × Space n} (hQ : P.IsCell Q) :
    P.cellOf Q ⊆ Metric.ball Q.2 (2 * coherentScale ℓ₀ Q.1) :=
  P.cell_subset_ball Q.1 Q.2 hQ

/-- **Ancestor inclusion** (`AncestorInclusionStatement`). -/
theorem d1d_ancestorInclusion_proof : AncestorInclusionStatement := by
  intro n E ℓ₀ P μ k Λ b 𝒢 i g O j A z hΛ hO hgO hdepth hji hA hA1 hOA hz hzg
  simp only [DirectPartition.scale, GoodRegion.rootScale, d1dancinc_r_eq] at hgO hzg ⊢
  have hℓ : 0 < ℓ₀ := P.scale_pos
  obtain ⟨hOc, hOl, -⟩ := 𝒢.below_root O hO
  obtain ⟨hAc, -, hAs⟩ := 𝒢.below_root A hA
  have hAmem : A.2 ∈ P.cellOf A := d1dancinc_center_mem_cell P hAc
  have hcA := d1dancinc_c_pos hℓ A.1
  refine ⟨?_, ?_⟩
  · intro y hy
    rw [Metric.mem_ball] at hy ⊢
    have hx := d1dancinc_c_pos hℓ (𝒢.root.1 + j)
    rcases Nat.lt_or_ge j 10 with hj | hj
    · -- clamped: the ancestor is the root
      have hA1' : A.1 = 𝒢.root.1 := by omega
      have hzr : dist z 𝒢.root.2 < 2 * coherentScale ℓ₀ 𝒢.root.1 :=
        Metric.mem_ball.1 (d1dancinc_cell_subset_ball P 𝒢.root_isCell hz)
      have hAr : dist A.2 𝒢.root.2 < 2 * coherentScale ℓ₀ 𝒢.root.1 :=
        Metric.mem_ball.1 (d1dancinc_cell_subset_ball P 𝒢.root_isCell (hAs hAmem))
      have hjR := d1dancinc_c_anti hℓ (Nat.le_add_right 𝒢.root.1 j)
      have hcR := d1dancinc_c_pos hℓ 𝒢.root.1
      have hΛc : 4000 * coherentScale ℓ₀ 𝒢.root.1 ≤ Λ * coherentScale ℓ₀ 𝒢.root.1 :=
        mul_le_mul_of_nonneg_right hΛ hcR.le
      have t1 := dist_triangle y z A.2
      have t2 := dist_triangle z 𝒢.root.2 A.2
      have e := dist_comm A.2 𝒢.root.2
      rw [hA1']
      linarith
    · -- unclamped: `r_j = 48 · 10^{-10} ℓ_A`
      have hA1' : A.1 + 10 = 𝒢.root.1 + j := by omega
      have hAO : A.1 ≤ O.1 := by omega
      have hOA' : dist O.2 A.2 < 2 * coherentScale ℓ₀ A.1 :=
        Metric.mem_ball.1 (d1dancinc_cell_subset_ball P hAc (hOA (d1dancinc_center_mem_cell P hOc)))
      have hcj : coherentScale ℓ₀ (𝒢.root.1 + j) = coherentScale ℓ₀ A.1 / 10 ^ 10 := by
        rw [← hA1', d1dancinc_c_add]
      have hcj' : coherentScale ℓ₀ (𝒢.root.1 + j) * 10 ^ 10 = coherentScale ℓ₀ A.1 :=
        (eq_div_iff (by positivity)).1 hcj
      have hij := d1dancinc_c_anti hℓ (Nat.add_le_add_left hji 𝒢.root.1)
      have hOle := d1dancinc_c_anti hℓ hAO
      have hΛc : 4000 * coherentScale ℓ₀ A.1 ≤ Λ * coherentScale ℓ₀ A.1 :=
        mul_le_mul_of_nonneg_right hΛ hcA.le
      have t1 := dist_triangle y z A.2
      have t2 := dist_triangle z g A.2
      have t3 := dist_triangle g O.2 A.2
      linarith
  · -- the ratio `ℓ_A ≤ 10^{12} r_{j+1}`
    have hle : 𝒢.root.1 + (j + 1) ≤ A.1 + 11 := by omega
    have e2 := d1dancinc_c_anti hℓ hle
    rw [d1dancinc_c_add, div_le_iff₀ (by positivity)] at e2
    have hx := d1dancinc_c_pos hℓ (𝒢.root.1 + (j + 1))
    linarith

end Witness

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
