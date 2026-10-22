import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements
import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Foundations.Statements.HighPassBracket
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.AmplitudeSquareSummable
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.AmplitudeNotSummable
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.EnergyDivergence
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.HalfHolderModulus
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.ZeroBaseLipschitz
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.PeriodicHalfDerivative
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.PeriodicLocal
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.CosineProductMean
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.HighFrequencyL2
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.LowFrequencyOscillation
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.HighFrequencyLimit
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.IntervalBMO
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.ZeroBaseBMO
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.CosineKernelPairing
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.SeriesPairing
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.ZeroDimRepresentation
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.ZeroBaseRepresentation


/-! # The exponent witness below `p = 2`: intermediate results

Proofs of the intermediate statements of `ExponentWitnessBelowStatement` (amplitudes,
divergence, parabolic Lipschitz bound, periodic half derivative, BMO, representation), each
obtained from the corresponding `…_proof` theorem. Some are stated in implication form over
lacunary estimates proved elsewhere.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative



theorem e2_exponentAmplitude_sq_summable : E2ExponentSquareSummableStatement := by
  exact e2_exponentAmplitude_sq_summable_proof

theorem e2_exponentAmplitude_not_summable : E2ExponentNotSummableStatement := by
  exact e2_exponentAmplitude_not_summable_proof



theorem e2_below_divergence : LacunaryLowerEnergyStatement → E2BelowDivergenceStatement := by
  exact e2_below_divergence_proof



theorem e2_sup_modulus :
    E2KernelBoundStatement → E2KernelSumStatement → E2InvSqrtDecayStatement →
      E2SupModulusStatement := by
  exact e2_sup_modulus_proof

theorem e2_zeroBase_lipschitz : E2ZeroBaseLipschitzStatement := by
  exact e2_zeroBase_lipschitz_proof



theorem e2_periodic_halfDerivative : E2PeriodicLimitStatement := by
  exact e2_periodic_halfDerivative_proof

theorem e2_periodic_local : E2PeriodicLocalStatement := by
  exact e2_periodic_local_proof



theorem e2_cosProduct_mean : E2CosProductMeanStatement := by
  exact e2_cosProduct_mean_proof

theorem e2_highFrequency_L2 : E2CosProductMeanStatement → E2HighFrequencyL2Statement := by
  exact e2_highFrequency_L2_proof

theorem e2_lowFrequency_oscillation : E2LowFrequencyOscillationStatement := by
  exact e2_lowFrequency_oscillation_proof

theorem e2_highFrequency_limit :
    E2HighFrequencyL2Statement → E2PeriodicLocalStatement → E2HighFrequencyLimitStatement := by
  exact e2_highFrequency_limit_proof

theorem e2_below_intervalBMO :
    E2LowFrequencyOscillationStatement → E2HighFrequencyLimitStatement →
      E2PeriodicLocalStatement → E2BelowIntervalBMOStatement := by
  exact e2_below_intervalBMO_proof

theorem e2_zeroBase_bmo : E2ZeroBaseBMOStatement := by
  exact e2_zeroBase_bmo_proof



theorem e2_cosine_kernelPairing : E2CosineKernelPairingStatement := by
  exact e2_cosine_kernelPairing_proof

theorem e2_series_pairing :
    LacunaryConvergenceStatement → E2CosineKernelPairingStatement →
      E2PeriodicLocalStatement → E2SeriesPairingStatement := by
  exact e2_series_pairing_proof

theorem e2_zeroDim_representation :
    HalfTimeBracketIntegrableStatement → E2ZeroDimRepresentationStatement := by
  exact e2_zeroDim_representation_proof

theorem e2_zeroBase_representation : E2ZeroBaseRepresentationStatement := by
  exact e2_zeroBase_representation_proof

end ParabolicRectifiability.Examples
