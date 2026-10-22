import ParabolicRectifiability.QuantitativeCharacterization.Statements.Characterization
import ParabolicRectifiability.QuantitativeCharacterization.Assembly.Characterization
import ParabolicRectifiability.BetaP.Proofs.Laws.Holder
import ParabolicRectifiability.BetaP.Proofs.Laws.Clamping
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.BetaPowTwo

/-! # Endpoints: the quantitative characterization and its beta-`p` comparison remark

`quantitative_characterization` is `quantitative_characterization_skeleton`, assembled from the
forward covering, the ambient root covering, absolute continuity from upper growth and the local
reverse bound, and `betaPow_carleson_comparison` is
`betaPow_carleson_comparison_of_providers` applied to the beta-`p` Hölder and clamping laws and
the quadratic beta identity. The statements are the exact specifications of
the `Statements` module of the same name.
-/

set_option autoImplicit false

namespace ParabolicRectifiability.QuantitativeCharacterization

/-- **The quantitative characterization.** Obtained from `quantitative_characterization_skeleton`, which combines
`exists_local_forward_covering`, `ambient_root_covering`, `absolutelyContinuous_of_upper_growth`
and `exists_local_reverse_bound`. -/
theorem quantitative_characterization : QuantitativeCharacterizationStatement := by
  exact quantitative_characterization_skeleton

/-- **The beta-`p` Carleson comparison.** Obtained from the quantitative characterization by
`betaPow_carleson_comparison_of_providers` applied to
`BetaP.claws_holder_proof`, `BetaP.cclamp_betaPowClamping_proof` and
`Foundations.f3_betaPow_two_eq_betaSq_proof`. -/
theorem betaPow_carleson_comparison : BetaPowCarlesonComparisonStatement := by
  exact betaPow_carleson_comparison_of_providers BetaP.claws_holder_proof
    BetaP.cclamp_betaPowClamping_proof Foundations.f3_betaPow_two_eq_betaSq_proof

end ParabolicRectifiability.QuantitativeCharacterization
