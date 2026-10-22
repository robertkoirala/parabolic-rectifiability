import ParabolicRectifiability.Characterization.Statements.Main
import ParabolicRectifiability.Characterization.Assembly.Main
import ParabolicRectifiability.Foundations.Assembly.DensityBridges
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.UpperDomination
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.DensityMeasurability
import ParabolicRectifiability.Foundations.Proofs.AmbientEnergy

/-! # The qualitative characterization of regular rectifiability

`qualitative_characterization` proves `QualitativeCharacterizationStatement`. For a locally Radon source, an available family,
and `1 ≤ k ≤ n + 2`, it relates finite-norm graph carriage and absolute continuity to
full-source square finiteness together with either density data or an intrinsic carrier.
Each criterion is given both for one positive endpoint and for every positive endpoint.

The conclusion also gives positive finite densities and typed measure covers at every
positive tolerance. These are qualitative assertions; they do not specify a uniform
Carleson bound or a rate. At `k = n + 2` all available square energies vanish.

The proof applies `qualitative_characterization_of_providers` to the shared
absolute-continuity bridge, upper-density domination, density measurability, and
ambient-energy results.
-/

namespace ParabolicRectifiability.Characterization

/-- The qualitative characterization: for a locally Radon source
in `1 ≤ k ≤ n + 2` and an available mixed or fixed family, regular measure rectifiability
is equivalent to each full-source square/density or square/intrinsic-carrier criterion.
The exact one-endpoint and every-endpoint quantifiers, density improvement, arbitrary
positive graph tolerances, and ambient clause are in `QualitativeCharacterizationStatement`. -/
theorem qualitative_characterization : QualitativeCharacterizationStatement := by
  exact qualitative_characterization_of_providers ParabolicRectifiability.Foundations.ac_bridge_skeleton ParabolicRectifiability.Foundations.fupdom_upper_density_domination ParabolicRectifiability.Foundations.fmeas1_density_measurability (fun n hn μ _ _ T hT => ParabolicRectifiability.Foundations.ambient_betaSq_squareEnergy_eq_zero_proof n hn μ T hT)

end ParabolicRectifiability.Characterization
