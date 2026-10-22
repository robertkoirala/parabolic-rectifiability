import ParabolicRectifiability.Measure.Neck.Construction
import ParabolicRectifiability.Measure.Neck.Certificates

/-!
# Normalization of neck certificates

Proof of `isCertified_normalize`.

A neck certified with noncollapse level `a = A B'`, tail bound `B'` and constant `C`,
where `0 < B ≤ B' ≤ C_b B`, is certified with level `B`, tail bound `B` and the constant
`L = max C (max (C/A) (C C_b))`:

* the geometric fields (parametrization, local and total content, core density) only
  need `C ≤ L`;
* core lower mass: `B r^k / L ≤ A B' r^k / C`, since `C ≤ A L` and `B ≤ B'`;
* core domination: `C / (A B') ≤ L / B`, for the same reason;
* core square: `C B' ≤ C C_b B ≤ L B`;
* core own square: `C B' / (A B') = C / A ≤ L = L B / B`.

Every estimate keeps the original source `ν`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal

/-- **`isCertified_normalize`**: normalization of the certificate constants. -/
theorem isCertified_normalize_proof (C A Cb : ℝ) (hC : 1 ≤ C) (hA : 0 < A) (_hCb : 1 ≤ Cb) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ {n k : ℕ} {T : NeckType} {ι : Type} {q : Space n}
      {R c₀ Cd Cs σ δ E κ θ γ : ℝ} (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ)
      (ν : Measure (Space n)) (B B' : ℝ), 0 < B → B ≤ B' → B' ≤ Cb * B →
      N.IsCertified ν (A * B') B' C → N.IsCertified ν B B L := by
  refine ⟨max C (max (C / A) (C * Cb)), le_trans hC (le_max_left _ _), ?_⟩
  intro n k T ι q R c₀ Cd Cs σ δ E κ θ γ N ν B B' hB hBB' hB' h
  have hCL : C ≤ max C (max (C / A) (C * Cb)) := le_max_left _ _
  have hCAL : C / A ≤ max C (max (C / A) (C * Cb)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCCbL : C * Cb ≤ max C (max (C / A) (C * Cb)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  generalize max C (max (C / A) (C * Cb)) = L at hCL hCAL hCCbL ⊢
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hL0 : 0 < L := lt_of_lt_of_le hC0 hCL
  have hB'0 : 0 < B' := lt_of_lt_of_le hB hBB'
  have hR : 0 ≤ R := N.parameters.R_pos.le
  have hAL : C ≤ A * L := by
    have h1 := (div_le_iff₀ hA).mp hCAL
    linarith [mul_comm L A]
  refine
    { isCompact_core := h.isCompact_core
      parametrization := ⟨fun hT => (h.parametrization.1 hT).mono hC0 hCL,
        fun hT => (h.parametrization.2 hT).mono hC0 hCL⟩
      localContent := h.localContent.mono hCL
      totalContent := h.totalContent.mono hCL hR
      coreDensity := h.coreDensity.mono hCL
      core_lower := ?_
      core_domination := ?_
      core_square := ?_
      eta_square := ?_ }
  · intro z hz r hr hrR
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (h.core_lower z hz r hr hrR)
    have hrk : 0 ≤ r ^ k := pow_nonneg hr.le k
    rw [div_le_div_iff₀ hL0 hC0]
    calc B * r ^ k * C ≤ B * r ^ k * (A * L) :=
          mul_le_mul_of_nonneg_left hAL (mul_nonneg hB.le hrk)
      _ ≤ B' * r ^ k * (A * L) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBB' hrk)
            (mul_nonneg hA.le hL0.le)
      _ = A * B' * r ^ k * L := by ring
  · refine h.core_domination.trans ?_
    have hc : ENNReal.ofReal (C / (A * B')) ≤ ENNReal.ofReal (L / B) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_div_iff₀ (mul_pos hA hB'0) hB]
      calc C * B ≤ (A * L) * B := mul_le_mul_of_nonneg_right hAL hB.le
        _ ≤ (A * L) * B' := mul_le_mul_of_nonneg_left hBB' (mul_nonneg hA.le hL0.le)
        _ = L * (A * B') := by ring
    refine Measure.le_iff'.2 fun s => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right hc zero_le
  · intro z hz
    refine (h.core_square z hz).trans (ENNReal.ofReal_le_ofReal ?_)
    calc C * B' ≤ C * (Cb * B) := mul_le_mul_of_nonneg_left hB' hC0.le
      _ = (C * Cb) * B := by ring
      _ ≤ L * B := mul_le_mul_of_nonneg_right hCCbL hB.le
  · intro z hz
    refine (h.eta_square z hz).trans (ENNReal.ofReal_le_ofReal ?_)
    have e1 : C * B' / (A * B') = C / A := by
      exact mul_div_mul_right C A hB'0.ne'
    have e2 : L * B / B = L := mul_div_cancel_right₀ L hB.ne'
    rw [e1, e2]
    exact hCAL

end ParabolicRectifiability
