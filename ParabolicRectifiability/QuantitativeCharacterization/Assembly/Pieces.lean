import ParabolicRectifiability.QuantitativeCharacterization.Assembly.TypedReferenceCovers
import ParabolicRectifiability.Foundations.Statements.Measurability

/-! # Quantitative coverings and qualitative rectifiability

* `any_cover_rectifiable_of_providers`: intrinsic sufficiency (through the typed reference
  covers, which also use `reference_estimates`) and `qmr_rectifiable_of_reference_covers`.
* `countable_quantitative_pieces_of_providers`: forward from typed refinement (measure version)
  at `ε = 1` and `countable_pieces_of_typed_covers`; converse from the any-cover theorem on every
  nonzero piece (each piece is locally Radon by the restriction statement) and
  `isRegularlyRectifiableMeasure_of_sum_restrict`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **A measure with a quantitative covering is rectifiable.** -/
theorem any_cover_rectifiable_of_providers
    (hIS : Characterization.IntrinsicSufficiencyStatement) : AnyCoverRectifiableStatement := by
  intro n hn k hk hkn μ hfin hreg K L hK hL hQ
  exact qmr_rectifiable_of_reference_covers n hn k hk hkn L hL
    (reference_typed_covers hIS hn hk hkn hL) μ hfin hreg K hK hQ

/-- **Countable quantitative pieces.** -/
theorem countable_quantitative_pieces_of_providers
    (hIS : Characterization.IntrinsicSufficiencyStatement)
    (hTR : Characterization.TypedRefinementMeasureStatement)
    (hRL : Foundations.RestrictLocallyRadonStatement) :
    CountableQuantitativePiecesStatement := by
  intro n hn k hk hkn μ hfin hreg
  constructor
  · intro hrect
    obtain ⟨EH, EV, hEH, hEV, hdisj, hnull, -, -, hcov, -, -⟩ :=
      hTR n hn k hk hkn μ hfin hreg hrect
    obtain ⟨hH, hV⟩ := hcov 1 one_pos
    exact countable_pieces_of_typed_covers n hn k hk hkn μ hfin hreg hrect.1 EH EV hEH hEV hdisj
      hnull hH hV
  · rintro ⟨E, hE, -, hsum, hpieces⟩
    refine isRegularlyRectifiableMeasure_of_sum_restrict n hn k hk hkn μ E hE hsum
      fun j hj => ?_
    obtain ⟨hfinj, hregj⟩ := hRL n hn μ hfin hreg (E j) (hE j)
    exact any_cover_rectifiable_of_providers hIS n hn k hk hkn (μ.restrict (E j)) hfinj hregj _ _
      (one_le_pow₀ one_le_two) (le_trans one_le_two (le_max_left _ _)) (hpieces j hj)

end ParabolicRectifiability.QuantitativeCharacterization
