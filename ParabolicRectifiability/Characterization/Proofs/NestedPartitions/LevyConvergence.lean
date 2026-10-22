import ParabolicRectifiability.Characterization.Proofs.NestedPartitions.DifferentiationStatements
import Mathlib.Probability.Martingale.Convergence

/-! # Lévy's upward theorem for partition filtrations

Proof of the named statement `CdLevyStatement` (from `b3_cd_levy`).

Route: package `ℱ` as a
`MeasureTheory.Filtration`; take a strongly measurable representative `h'` of `h`
(`AEStronglyMeasurable.mk`), which is `⨆ ℱ_j`-strongly measurable because `⨆ ℱ_j = m`;
apply Lévy's upward theorem `MeasureTheory.Integrable.tendsto_ae_condExp` to `h'`; transfer
from `h'` to `h` by `condExp_congr_ae`; intersect the countably many identification events
with `ae_all_iff` and conclude with `Tendsto.congr`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace ParabolicRectifiability.Characterization.CoordinateDifferentiationTree

/-- `CdLevyStatement`: versions of `𝔼[h | ℱ_j]` along an increasing sequence of
sub-σ-algebras generating the ambient σ-algebra converge to `h` almost everywhere, for a
finite measure and an integrable `h`. -/
theorem bp2_cd_levy_proof : CdLevyStatement := by
  intro Y m ρ hρ ℱ hmono hle hsup a h hh ha
  let F : Filtration ℕ m := ⟨ℱ, hmono, hle⟩
  have hsup' : (⨆ n, F n) = m := hsup
  have hmeas := hh.aestronglyMeasurable
  have hh'eq : h =ᵐ[ρ] hmeas.mk h := hmeas.ae_eq_mk
  have hint' : Integrable (hmeas.mk h) ρ := hh.congr hh'eq
  have hsm : StronglyMeasurable[⨆ n, F n] (hmeas.mk h) := by
    rw [hsup']
    exact hmeas.stronglyMeasurable_mk
  have hlim := hint'.tendsto_ae_condExp hsm
  have hc : ∀ᵐ z ∂ρ, ∀ j, a j z = (ρ[hmeas.mk h | F j]) z :=
    ae_all_iff.2 fun j => (ha j).trans (condExp_congr_ae hh'eq)
  filter_upwards [hlim, hc, hh'eq] with z hz hcz hez
  rw [hez]
  exact hz.congr fun j => (hcz j).symm

end ParabolicRectifiability.Characterization.CoordinateDifferentiationTree
