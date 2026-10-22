import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # The owner cell

Proof of `d1c_owner_proof : AncestorStatement → StopScaleLipschitzStatement → OwnerStatement`
The two
statements are taken as hypotheses only.

Write `r = r_j = coherentScale (48 ℓ_*) j`, and let `g ∈ S` with `ρ(g) < 1000 r`.

* Case `r ≤ ℓ_*`. As `ρ(g) < 1000 r`, some member `Q` has `ℓ_Q + dist_P(g, Q) < 1000 r`
  (`exists_lt_of_ciInf_lt`; this is sharper than the `2ρ(g)` / `r_j` choice of the original and
  covers both of its cases). Let `i` be the greatest level `≤ Q.1` with `r ≤ ℓ_i`
  (`Nat.findGreatest`; `root.1` qualifies). `AncestorStatement` gives a member `O` at level `i`
  with `cell Q ⊆ cell O`. Then `r ≤ ℓ_O < 1000 r` (either `O.1 = Q.1`, or `ℓ_{i+1} < r` and
  `ℓ_O = 10 ℓ_{i+1} < 10 r`), `dist_P(g, O) ≤ dist_P(g, Q) < 1000 r`,
  `d_P(g, z_O) ≤ dist_P(g, O) + 2 ℓ_O` (`cell_subset_ball`), `10^{root.1 + j} < 48000 · 10^{O.1}`
  gives `j + root.1 ≤ O.1 + 4`, and `40 r + 1000 r + 2 ℓ_O ≤ 1042 ℓ_O ≤ Λ ℓ_O` gives the inclusion.
* Case `r > ℓ_*`. `O` = the root: `dist_P(g, S) = 0`, `d_P(g, q) < 2 ℓ_*`, `10^j < 48` forces
  `j ≤ 1`, and `40 r + 2 ℓ_* ≤ 40 · 48 ℓ_* + 2 ℓ_* = 1922 ℓ_* ≤ Λ ℓ_*`.

The hypothesis `StopScaleLipschitzStatement` is not needed (the infimum is used directly).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section Owner

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The cell sides are positive. -/
theorem d1cowner_scale_pos (P : DirectPartition E ℓ₀) (j : ℕ) : 0 < P.scale j := by
  unfold DirectPartition.scale coherentScale
  exact div_pos P.scale_pos (pow_pos (by norm_num) _)

/-- `ℓ_i = 10 ℓ_{i+1}`. -/
theorem d1cowner_scale_succ (P : DirectPartition E ℓ₀) (i : ℕ) :
    P.scale i = 10 * P.scale (i + 1) := by
  have h : P.scale (i + 1) = P.scale i / 10 := by
    unfold DirectPartition.scale coherentScale
    rw [pow_succ, div_div]
  linarith

/-- A centre lies in its own cell (`center_subset`, `inner_subset`). -/
theorem d1cowner_center_mem_cell (P : DirectPartition E ℓ₀) {j : ℕ} {z : Space n}
    (hz : z ∈ P.center j) : z ∈ P.cell j z := by
  apply P.inner_subset j z hz
  refine ⟨P.center_subset j hz, ?_⟩
  rw [Metric.mem_ball, dist_self]
  have h : 0 < coherentScale ℓ₀ j := div_pos P.scale_pos (pow_pos (by norm_num) _)
  linarith

/-- `d_P(g, z_O) ≤ dist_P(g, O) + 2 ℓ_O` (`cell_subset_ball`). -/
theorem d1cowner_dist_center_le (P : DirectPartition E ℓ₀) {O : ℕ × Space n}
    (hO : O.2 ∈ P.center O.1) (g : Space n) :
    dist g O.2 ≤ Metric.infDist g (P.cellOf O) + 2 * P.scale O.1 := by
  have hne : (P.cellOf O).Nonempty := ⟨O.2, d1cowner_center_mem_cell P hO⟩
  have h : dist g O.2 - 2 * P.scale O.1 ≤ Metric.infDist g (P.cellOf O) := by
    rw [Metric.le_infDist hne]
    intro y hy
    have hy' : dist y O.2 < 2 * P.scale O.1 :=
      Metric.mem_ball.mp (P.cell_subset_ball O.1 O.2 hO hy)
    have htri := dist_triangle g y O.2
    linarith
  linarith

/-- The depth bound: `ℓ_i < 1000 r_j` forces `j + root.1 ≤ i + 8` (indeed `≤ i + 4`). -/
theorem d1cowner_depth (𝒢 : GoodRegion P μ k Λ b) {i j : ℕ}
    (h : P.scale i < 1000 * coherentScale (48 * 𝒢.rootScale) j) : j + 𝒢.root.1 ≤ i + 8 := by
  have hℓ := P.scale_pos
  unfold GoodRegion.rootScale DirectPartition.scale coherentScale at h
  have hA : (0 : ℝ) < 10 ^ i := by positivity
  have hX : (0 : ℝ) < 10 ^ (𝒢.root.1 + j) := by positivity
  have e : 1000 * (48 * (ℓ₀ / 10 ^ 𝒢.root.1) / 10 ^ j) = 48000 * ℓ₀ / 10 ^ (𝒢.root.1 + j) := by
    rw [pow_add]
    ring
  rw [e, div_lt_div_iff₀ hA hX] at h
  have h2 : (10 : ℝ) ^ (𝒢.root.1 + j) < 10 ^ (i + 5) := by
    have e5 : (10 : ℝ) ^ (i + 5) = 100000 * 10 ^ i := by
      rw [pow_add]
      ring
    rw [e5]
    by_contra hc
    rw [not_lt] at hc
    have h3 : ℓ₀ * (100000 * 10 ^ i) ≤ ℓ₀ * 10 ^ (𝒢.root.1 + j) :=
      mul_le_mul_of_nonneg_left hc hℓ.le
    nlinarith [mul_pos hℓ hA]
  have h4 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 10)).mp h2
  omega

end Owner

/-- **The owner cell** (`OwnerStatement`). -/
theorem d1c_owner_proof :
    AncestorStatement → StopScaleLipschitzStatement → OwnerStatement := by
  intro hAnc _hLips n E ℓ₀ P μ k Λ b 𝒢 j g hg hρ
  classical
  obtain ⟨r, hr_eq⟩ : ∃ r, r = coherentScale (48 * 𝒢.rootScale) j := ⟨_, rfl⟩
  rw [← hr_eq] at hρ ⊢
  have hroot : 𝒢.root.2 ∈ P.center 𝒢.root.1 := 𝒢.root_isCell
  have hℓ : 0 < 𝒢.rootScale := d1c_rootScale_pos 𝒢
  have hr : 0 < r := by
    rw [hr_eq]
    unfold coherentScale
    exact div_pos (by linarith) (pow_pos (by norm_num) _)
  by_cases hcase : r ≤ 𝒢.rootScale
  · -- fine scales: ascend from an approximating member
    have : Nonempty 𝒢.members := ⟨⟨𝒢.root, 𝒢.root_mem⟩⟩
    have hρ' : (⨅ Q : 𝒢.members, (P.scale Q.1.1 + Metric.infDist g (P.cellOf Q.1))) <
        1000 * r := hρ
    obtain ⟨⟨Q, hQmem⟩, hQ⟩ := exists_lt_of_ciInf_lt hρ'
    have hQ' : P.scale Q.1 + Metric.infDist g (P.cellOf Q) < 1000 * r := hQ
    have hQc : Q.2 ∈ P.center Q.1 := (𝒢.below_root Q hQmem).1
    have hQlev : 𝒢.root.1 ≤ Q.1 := (𝒢.below_root Q hQmem).2.1
    have hQpos := d1cowner_scale_pos P Q.1
    have hdist0 : 0 ≤ Metric.infDist g (P.cellOf Q) := Metric.infDist_nonneg
    have hcase' : r ≤ P.scale 𝒢.root.1 := hcase
    obtain ⟨i, hi_def⟩ : ∃ i, i = Nat.findGreatest (fun i => r ≤ P.scale i) Q.1 := ⟨_, rfl⟩
    have hi_root : 𝒢.root.1 ≤ i := by
      rw [hi_def]
      exact Nat.le_findGreatest hQlev hcase'
    have hiQ : i ≤ Q.1 := by
      rw [hi_def]
      exact Nat.findGreatest_le _
    have hri : r ≤ P.scale i := by
      rw [hi_def]
      exact Nat.findGreatest_spec (P := fun i => r ≤ P.scale i) hQlev hcase'
    have hiup : P.scale i < 1000 * r := by
      rcases hiQ.lt_or_eq with hlt | heq
      · have hnot : ¬ r ≤ P.scale (i + 1) := by
          rw [hi_def] at hlt ⊢
          exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hlt
        rw [not_le] at hnot
        have h10 := d1cowner_scale_succ P i
        linarith
      · rw [heq]
        linarith
    obtain ⟨O, hOmem, hOlev, hOsub⟩ := (hAnc n E ℓ₀ P μ k Λ b 𝒢).2 Q hQmem i hi_root hiQ
    have hOc : O.2 ∈ P.center O.1 := (𝒢.below_root O hOmem).1
    have hOlo : r ≤ P.scale O.1 := by
      rw [hOlev]
      exact hri
    have hOhi : P.scale O.1 < 1000 * r := by
      rw [hOlev]
      exact hiup
    have hOpos := d1cowner_scale_pos P O.1
    have hinf : Metric.infDist g (P.cellOf O) ≤ Metric.infDist g (P.cellOf Q) :=
      Metric.infDist_le_infDist_of_subset hOsub ⟨Q.2, d1cowner_center_mem_cell P hQc⟩
    have hdc := d1cowner_dist_center_le P hOc g
    refine ⟨O, hOmem, (min_le_left _ _).trans hOlo, by linarith, by linarith, by linarith, ?_, ?_⟩
    · have h' : P.scale O.1 < 1000 * coherentScale (48 * 𝒢.rootScale) j := by
        rw [← hr_eq]
        exact hOhi
      exact d1cowner_depth 𝒢 h'
    · intro hΛ y hy
      rw [Metric.mem_ball] at hy ⊢
      have htri := dist_triangle y g O.2
      have hΛO : 4000 * P.scale O.1 ≤ Λ * P.scale O.1 := mul_le_mul_of_nonneg_right hΛ hOpos.le
      linarith
  · -- coarse scales (`j ≤ 1`): the root
    rw [not_le] at hcase
    have hgO : g ∈ P.cellOf 𝒢.root := hg
    have hscale : P.scale 𝒢.root.1 = 𝒢.rootScale := rfl
    have hgr : dist g 𝒢.root.2 < 2 * 𝒢.rootScale :=
      Metric.mem_ball.mp (P.cell_subset_ball _ _ hroot hgO)
    refine ⟨𝒢.root, 𝒢.root_mem, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hscale]
      exact min_le_right _ _
    · rw [hscale]
      linarith
    · rw [Metric.infDist_zero_of_mem hgO]
      linarith
    · rw [hscale]
      linarith
    · have h1 : 𝒢.rootScale < 48 * 𝒢.rootScale / 10 ^ j := by
        rw [hr_eq] at hcase
        exact hcase
      rw [lt_div_iff₀ (by positivity)] at h1
      have h2 : (10 : ℝ) ^ j < 100 := by
        by_contra hc
        rw [not_lt] at hc
        have := mul_le_mul_of_nonneg_left hc hℓ.le
        linarith
      have h3 : (10 : ℝ) ^ j < 10 ^ 2 := by
        calc (10 : ℝ) ^ j < 100 := h2
          _ = 10 ^ 2 := by norm_num
      have h4 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 10)).mp h3
      omega
    · intro hΛ y hy
      have hr48 : r ≤ 48 * 𝒢.rootScale := by
        rw [hr_eq]
        unfold coherentScale
        exact div_le_self (by linarith) (one_le_pow₀ (by norm_num))
      rw [Metric.mem_ball] at hy ⊢
      rw [hscale]
      have htri := dist_triangle y g 𝒢.root.2
      have hΛℓ : 4000 * 𝒢.rootScale ≤ Λ * 𝒢.rootScale := mul_le_mul_of_nonneg_right hΛ hℓ.le
      linarith

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
