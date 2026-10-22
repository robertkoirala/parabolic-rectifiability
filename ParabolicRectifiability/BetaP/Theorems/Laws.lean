import ParabolicRectifiability.BetaP.Statements.Laws
import ParabolicRectifiability.BetaP.Proofs.Laws.Basic
import ParabolicRectifiability.BetaP.Proofs.Laws.Rescaling
import ParabolicRectifiability.BetaP.Proofs.Laws.Holder
import ParabolicRectifiability.BetaP.Proofs.Laws.Measurability
import ParabolicRectifiability.BetaP.Proofs.Laws.Clamping
import ParabolicRectifiability.BetaP.Proofs.Laws.Annulus
import ParabolicRectifiability.BetaP.Proofs.Laws.Unavailable
import ParabolicRectifiability.BetaP.Proofs.Laws.Smul
import ParabolicRectifiability.BetaP.Proofs.Laws.ZeroSource

/-! # Laws of the natural beta-`p` normalization

These theorems prove the conventions and laws specified by the `…Statement` definitions:
empty balls and unavailable families, measurability, restriction, finite annuli, amplitude
and dilation laws, the zero source, Hölder comparison with density, and density-free clamping.
The defining normalization is `B_p = r^{-k-p} inf_L ∫_{P(z,r)} d_P(w,L)^p dμ`, without
division by ball mass (see `Foundations.betaPow`).

Availability and local-Radon hypotheses differ by law: in particular the empty-ball and
zero-source laws require a nonempty family, while positive amplitudes, dilation, and
clamping are stated for every family. The finite-annulus result concerns `0 < u < v`
and does not assert integrability down to zero.
-/

namespace ParabolicRectifiability.BetaP

/-- An empty testing ball gives `B_p = 0` for a nonempty family. -/
theorem emptyTestingBall : EmptyTestingBallStatement := claws_emptyTestingBall_proof

/-- For an unavailable family and `p > 0`, `B_p = ⊤` at every positive radius and
`S_p^a = T_p^a = ⊤` at every positive endpoint, for every source.
The nonpositive-radius convention for `B_p` remains zero. -/
theorem unavailableFamily : UnavailableFamilyStatement := by exact ParabolicRectifiability.BetaP.c2_unavailableFamily_proof

/-- Borel measurability of `B_p`, `S_p^a`, `T_p^a`. -/
theorem betaPow_measurability : BetaPowMeasurabilityStatement := cfit_betaPowMeasurability_proof

/-- Monotonicity of `B_p` under source restriction. -/
theorem betaPow_restriction : BetaPowRestrictionStatement := claws_restriction_proof

/-- For a locally Radon source, an available family and `p > 0`, both scale integrands
`B_p^{2/p}` and `B_p` have finite integral over each finite annulus `(u,v)`,
`0 < u < v`. This is the input for positive-endpoint invariance of energy finiteness. -/
theorem betaPow_annulus : BetaPowAnnulusStatement := by exact ParabolicRectifiability.BetaP.c2_betaPowAnnulus_proof

/-- Positive amplitude scaling: `B_{p,cμ} = c B_{p,μ}` for real `c > 0`, every source,
family, centre, and radius. The energy amplitude powers are separately
recorded in `Foundations.EnergyPowSmulStatement`. -/
theorem betaPow_smul : BetaPowSmulStatement := by exact ParabolicRectifiability.BetaP.c2_betaPowSmul_proof

/-- The dilation law for `rescaledSource`, endpoint `aR`. -/
theorem betaPow_rescaling : BetaPowRescalingStatement := claws_rescaling_proof

/-- For an available family and `p > 0`, the zero source has `B_p = 0` at every radius
and zero `S_p^a`, `T_p^a` at every positive endpoint. The availability
hypothesis excludes the empty-infimum value `⊤`. -/
theorem betaPow_zeroSource : BetaPowZeroSourceStatement := by exact ParabolicRectifiability.BetaP.c2_betaPowZeroSource_proof

/-- Hölder with the density factor. -/
theorem betaPow_holder : BetaPowHolderStatement := claws_holder_proof

/-- The density-free clamping comparisons. -/
theorem betaPow_clamping : BetaPowClampingStatement := cclamp_betaPowClamping_proof

end ParabolicRectifiability.BetaP
