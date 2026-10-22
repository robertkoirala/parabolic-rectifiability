import ParabolicRectifiability.Measure.Neck.FirstSwitch

/-!
# Type and cutoff selection of one contracting step

For a source carried by
`S ⊆ P(q,R)` with all-scale energy at most `B` for the family `F`:

* if `F` is mixed and both types are available (`2 ≤ k ≤ n`), the type `T` minimizes the
  global fitting error, the cutoff is the first-switch cutoff of `T`, and the inflated
  budget is `B' = (4^{k+2}+1) B`; the tail bound and the two tubes are those of the
  first-switch statement `firstSwitchCutoff_spec_proof`;
* otherwise `T` is the type fixed by the family or the only available type, the cutoff is
  zero and `B' = B`. When the other type is unavailable its model family is empty, so the
  mixed beta square equals the beta square of the available type.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-- When the other type has no admissible model, the mixed natural beta square equals
the beta square of `T` (the empty fitting infimum is `⊤`). -/
theorem ms6_betaSq_mixed_eq_of_isEmpty {n k : ℕ} (ν : Measure (Space n)) (T : NeckType)
    (h : IsEmpty (Models n k T.other.toFamilyKind)) (z : Space n) (r : ℝ) :
    betaSq ν k .mixed z r = betaSq ν k T.toFamilyKind z r := by
  rcases le_or_gt r 0 with hr | hr
  · rw [betaSq_of_nonpos ν k _ z hr, betaSq_of_nonpos ν k _ z hr]
  · rw [betaSq_eq_typeFittingError ν .mixed z hr,
      betaSq_eq_typeFittingError ν T.toFamilyKind z hr, typeFittingError_mixed_eq ν T z r]
    have htop : typeFittingError ν k T.other.toFamilyKind z r = ⊤ := by
      unfold typeFittingError
      exact iInf_of_empty _
    rw [htop, inf_top_eq]

/-- When the other type has no admissible model, the mixed all-scale energy equals the
all-scale energy of `T`. -/
theorem ms6_allScaleEnergy_mixed_eq_of_isEmpty {n k : ℕ} (ν : Measure (Space n))
    (T : NeckType) (h : IsEmpty (Models n k T.other.toFamilyKind)) (z : Space n) :
    allScaleEnergy ν k .mixed z = allScaleEnergy ν k T.toFamilyKind z := by
  unfold allScaleEnergy
  simp only [ms6_betaSq_mixed_eq_of_isEmpty ν T h z]

/-- The zero-cutoff case of `exists_step_type_proof`: an available type `T` compatible with the family and
with all-scale energy at most `B` on `S` gives the cutoff `0` and the budget `B' = B`;
the two-tube clause is vacuous. -/
theorem ms6_stepType_of_zeroCutoff {n k : ℕ} {F : FamilyKind} {R B : ℝ}
    {ν : Measure (Space n)} {S : Set (Space n)} (C₂ : ℝ) (hR : 0 < R) (hB : 0 < B)
    (T : NeckType) (hT : T.Available n k) (hFT : F = .mixed ∨ F = T.toFamilyKind)
    (hE : ∀ z ∈ S, allScaleEnergy ν k T.toFamilyKind z ≤ ENNReal.ofReal B) :
    ∃ (T : NeckType) (f : Space n → ℝ) (B' : ℝ), T.Available n k ∧
      (F = .mixed ∨ F = T.toFamilyKind) ∧ IsSourceCutoff S R f ∧ B ≤ B' ∧
      B' ≤ (4 ^ (n + 4) + 1) * B ∧
      (∀ z ∈ S, tailEnergy ν k T.toFamilyKind (f z) z ≤ ENNReal.ofReal B') ∧
      (F ≠ .mixed → ∀ z ∈ S, f z = 0) ∧
      ∀ c ∈ S, 0 < f c → 2 ≤ k ∧ k ≤ n ∧
        ∃ (LH : HorizontalModel n k) (LV : VerticalModel n k),
          ∫⁻ z in Metric.ball c (f c),
              (modelCost (T := .horizontal) LH z + modelCost (T := .vertical) LV z) ∂ν ≤
            ENNReal.ofReal (C₂ * B * f c ^ (k + 2)) := by
  have h4 : (1 : ℝ) ≤ 4 ^ (n + 4) + 1 := by
    have : (0 : ℝ) ≤ 4 ^ (n + 4) := by positivity
    linarith
  refine ⟨T, fun _ => 0, B, hT, hFT, isSourceCutoff_zero S hR.le, le_rfl,
    le_mul_of_one_le_left hB.le h4, fun z hz => hE z hz, fun _ _ _ => rfl, ?_⟩
  intro c _ hc
  exact absurd hc (lt_irrefl 0)

/-- **`exists_step_type`**: type and cutoff selection of one contracting step. -/
theorem exists_step_type_proof (n : ℕ) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (k : ℕ) (F : FamilyKind), 1 ≤ k → k < n + 2 →
      Nonempty (Models n k F) →
      ∀ (q : Space n) (R B : ℝ) (ν : Measure (Space n)) (S : Set (Space n)),
        0 < R → 0 < B → IsFiniteMeasure ν → MeasurableSet S → S ⊆ Metric.ball q R →
        ν Sᶜ = 0 → (∀ z ∈ S, allScaleEnergy ν k F z ≤ ENNReal.ofReal B) →
        ∃ (T : NeckType) (f : Space n → ℝ) (B' : ℝ), T.Available n k ∧
          (F = .mixed ∨ F = T.toFamilyKind) ∧ IsSourceCutoff S R f ∧ B ≤ B' ∧
          B' ≤ (4 ^ (n + 4) + 1) * B ∧
          (∀ z ∈ S, tailEnergy ν k T.toFamilyKind (f z) z ≤ ENNReal.ofReal B') ∧
          (F ≠ .mixed → ∀ z ∈ S, f z = 0) ∧
          ∀ c ∈ S, 0 < f c → 2 ≤ k ∧ k ≤ n ∧
            ∃ (LH : HorizontalModel n k) (LV : VerticalModel n k),
              ∫⁻ z in Metric.ball c (f c),
                  (modelCost (T := .horizontal) LH z + modelCost (T := .vertical) LV z) ∂ν ≤
                ENNReal.ofReal (C₂ * B * f c ^ (k + 2)) := by
  obtain ⟨C, hC, hspec⟩ := firstSwitchCutoff_spec_proof n
  refine ⟨C, hC, ?_⟩
  intro k F hk hkn hF q R B ν S hR hB hν hSm hSq hSn hSB
  cases F with
  | horizontal =>
    have hT : NeckType.horizontal.Available n k := HorizontalModel.nonempty_iff.mp hF
    exact ms6_stepType_of_zeroCutoff C hR hB .horizontal hT (Or.inr rfl) hSB
  | vertical =>
    have hT : NeckType.vertical.Available n k := VerticalModel.nonempty_iff.mp hF
    exact ms6_stepType_of_zeroCutoff C hR hB .vertical hT (Or.inr rfl) hSB
  | mixed =>
    by_cases hH : 1 ≤ k ∧ k ≤ n
    · by_cases hV : 2 ≤ k ∧ k ≤ n + 2
      · -- Both types are available: the first-switch cutoff of the global minimizer.
        have hk2 : 2 ≤ k := hV.1
        have hkn' : k ≤ n := hH.2
        obtain ⟨T, hglob⟩ : ∃ T : NeckType, globalFittingError ν k T.toFamilyKind ≤
            globalFittingError ν k T.other.toFamilyKind := by
          rcases le_total (globalFittingError ν k .horizontal)
              (globalFittingError ν k .vertical) with h | h
          · exact ⟨.horizontal, h⟩
          · exact ⟨.vertical, h⟩
        obtain ⟨hcut, htail, htube⟩ :=
          hspec k hk2 hkn' q R B ν S T hR hB.le hν hSm hSq hSn hSB hglob
        have hTav : T.Available n k := by
          cases T
          · exact (show 1 ≤ k ∧ k ≤ n from ⟨by omega, by omega⟩)
          · exact (show 2 ≤ k ∧ k ≤ n + 2 from ⟨by omega, by omega⟩)
        have h4k : (0 : ℝ) ≤ 4 ^ (k + 2) := by positivity
        have h4kn : (4 : ℝ) ^ (k + 2) ≤ 4 ^ (n + 4) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        refine ⟨T, firstSwitchCutoff ν k T R, (4 ^ (k + 2) + 1) * B, hTav, Or.inl rfl, hcut,
          le_mul_of_one_le_left hB.le (by linarith),
          mul_le_mul_of_nonneg_right (by linarith) hB.le, htail, ?_, ?_⟩
        · intro h
          exact absurd rfl h
        · intro c hc hpos
          exact ⟨hk2, hkn', htube c hc hpos⟩
      · -- Only the horizontal type is available.
        have hE : IsEmpty (Models n k NeckType.horizontal.other.toFamilyKind) :=
          VerticalModel.isEmpty_of_not_available hV
        refine ms6_stepType_of_zeroCutoff C hR hB .horizontal hH (Or.inl rfl) ?_
        intro z hz
        rw [← ms6_allScaleEnergy_mixed_eq_of_isEmpty ν .horizontal hE z]
        exact hSB z hz
    · -- Only the vertical type is available.
      have hV : 2 ≤ k ∧ k ≤ n + 2 := by
        rcases AdmissibleModel.nonempty_iff.mp hF with h | h
        · exact absurd h hH
        · exact h
      have hE : IsEmpty (Models n k NeckType.vertical.other.toFamilyKind) :=
        HorizontalModel.isEmpty_of_not_available hH
      refine ms6_stepType_of_zeroCutoff C hR hB .vertical hV (Or.inl rfl) ?_
      intro z hz
      rw [← ms6_allScaleEnergy_mixed_eq_of_isEmpty ν .vertical hE z]
      exact hSB z hz

end ParabolicRectifiability
