import ParabolicRectifiability.QuantitativeCharacterization.Statements.ApproximantComponents

/-! # Canonical identification

Proof of `dp2_CanonicalIdentificationStatement` in implication form: the statements about
typed rectifiability of restrictions and of countable sums enter only as the hypotheses `hS1`,
`hS2`.

Proof idea: with `μ_T = μ⌊{S^1_{μ,T} < ∞}`, the competitor
`ρ_H = μ⌊F_H + μ_H⌊Pᶜ`, `ρ_V = μ⌊F_V + μ_V⌊Pᶜ`, `ρ_P = μ_+⌊Pᶜ` satisfies `μ = ρ_H + ρ_V + ρ_P`
(`μ⌊P = μ⌊F_H + μ⌊F_V`, `μ⌊Pᶜ = (μ_H + μ_V + μ_+)⌊Pᶜ`). `ρ_H`, `ρ_V` are typed rectifiable by `hS1`
(`μ_T⌊Pᶜ ≪ μ_T`) and the binary case of `hS2` (`Measure.sum_cond`), `ρ_P` is graph pure as a
restriction of `μ_+`; the field `unique` gives `ρ_T = μ_T`, and restricting to `P` gives
`μ⌊F_T = μ_T⌊P`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- Restricting back to `P`: if `μ⌊F + ν⌊Pᶜ = ρ` with `F ⊆ P` and `P` measurable, then
`μ⌊F = ρ⌊P`. -/
theorem dp2_ci_restrict_back {n : ℕ} {μ ν ρ : Measure (Space n)} {P F : Set (Space n)}
    (hP : MeasurableSet P) (hFP : F ⊆ P) (h : μ.restrict F + ν.restrict Pᶜ = ρ) :
    μ.restrict F = ρ.restrict P := by
  rw [← h, Measure.restrict_add, Measure.restrict_restrict hP, Set.inter_eq_right.mpr hFP,
    Measure.restrict_restrict hP, Set.inter_compl_self, Measure.restrict_empty, add_zero]

/-- Purity of a restriction: a restriction of a graph-pure measure is graph pure. -/
theorem dp2_ci_graphPure_restrict {n k : ℕ} {ν : Measure (Space n)} (s : Set (Space n))
    (h : IntegralCanonical.IsGraphPure k ν) :
    IntegralCanonical.IsGraphPure k (ν.restrict s) := by
  have hle : ∀ t, ν.restrict s t ≤ ν t := Measure.le_iff'.mp Measure.restrict_le_self
  exact ⟨fun ε H => nonpos_iff_eq_zero.mp ((hle _).trans (h.1 ε H).le),
    fun ε V => nonpos_iff_eq_zero.mp ((hle _).trans (h.2 ε V).le)⟩

/-- **Canonical identification** (`dp2_canonical_identification`), proved from the hypotheses `hS1`, `hS2` only. -/
theorem dp2_canonical_identification_proof : dp2_CanonicalIdentificationStatement := by
  intro hS1 hS2 n k μ hcd P FH FV hP hFH hFV hdisj hFHP hFVP hnull hrH hrV
  -- binary sums, from `hS2` at `ι = Bool`
  have hbin : ∀ (T : FamilyKind) (α β : Measure (Space n)),
      IsRegularlyRectifiableMeasure T k α → IsRegularlyRectifiableMeasure T k β →
      IsRegularlyRectifiableMeasure T k (α + β) := by
    intro T α β hα hβ
    rw [← Measure.sum_cond]
    exact hS2 T (fun b => cond b α β) (fun b _ => by cases b <;> assumption)
  -- `μ⌊P = μ⌊F_H + μ⌊F_V`
  have hPeq : μ.restrict P = μ.restrict FH + μ.restrict FV := by
    rw [← Measure.restrict_union hdisj hFV]
    exact Measure.restrict_congr_set (ae_eq_set.mpr ⟨hnull,
      measure_mono_null (fun z hz => (hz.2 (Set.union_subset hFHP hFVP hz.1)).elim) measure_empty⟩)
  -- `μ⌊Pᶜ = μ_H⌊Pᶜ + μ_V⌊Pᶜ + μ_+⌊Pᶜ`
  have hPc : μ.restrict Pᶜ =
      (IntegralCanonical.horizontalPart μ k 1).restrict Pᶜ +
        (IntegralCanonical.verticalPart μ k 1).restrict Pᶜ +
        (IntegralCanonical.purePart μ k 1).restrict Pᶜ := by
    have h := congrArg (fun m : Measure (Space n) => m.restrict Pᶜ) hcd.measure_eq
    simpa only [Measure.restrict_add] using h
  -- the competitor decomposition `μ = ρ_H + ρ_V + ρ_P`
  have hsum : μ =
      (μ.restrict FH + (IntegralCanonical.horizontalPart μ k 1).restrict Pᶜ) +
        (μ.restrict FV + (IntegralCanonical.verticalPart μ k 1).restrict Pᶜ) +
        (IntegralCanonical.purePart μ k 1).restrict Pᶜ := by
    calc μ = μ.restrict P + μ.restrict Pᶜ := (Measure.restrict_add_restrict_compl hP).symm
      _ = (μ.restrict FH + μ.restrict FV) +
            ((IntegralCanonical.horizontalPart μ k 1).restrict Pᶜ +
              (IntegralCanonical.verticalPart μ k 1).restrict Pᶜ +
              (IntegralCanonical.purePart μ k 1).restrict Pᶜ) := by rw [hPeq, hPc]
      _ = _ := by abel
  -- typed rectifiability of `ρ_H`, `ρ_V` (`hS1`, binary `hS2`), purity of `ρ_P`
  have hρH := hbin .horizontal _ _ hrH
    (hS1 .horizontal hcd.horizontal_rectifiable
      (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self (s := Pᶜ))))
  have hρV := hbin .vertical _ _ hrV
    (hS1 .vertical hcd.vertical_rectifiable
      (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self (s := Pᶜ))))
  have hρP := dp2_ci_graphPure_restrict Pᶜ hcd.pure_graphPure
  -- canonical uniqueness, then restriction back to `P`
  obtain ⟨hH, hV, -⟩ := hcd.unique _ _ _ hsum hρH hρV hρP
  exact ⟨dp2_ci_restrict_back hP hFHP hH, dp2_ci_restrict_back hP hFVP hV⟩

end ParabolicRectifiability.QuantitativeCharacterization
