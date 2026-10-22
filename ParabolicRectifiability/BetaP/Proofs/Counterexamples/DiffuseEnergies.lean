import ParabolicRectifiability.Examples.Proofs.DensityTests.DiffuseEstimates
import ParabolicRectifiability.BetaP.Statements.Corollaries

/-! # Integrated `β_p` energies of a diffuse measure

`c2_diffuse_betaP_integratedEnergy` has the type of `diffuse_betaP_integratedEnergy`: the
integrated square energies of the restriction of parabolic volume to a ball are positive and
finite. It uses the construction `Examples.e2_diffuse_energyBounds` and only unfolds the
integrated-energy definitions (`integratedEnergyS/T μ k T p q R = ∫_{P(q,R)} energy^{2R} dμ`,
here `q = 0`, `R = 1`, endpoint `2 · 1 = 2`).
-/

open MeasureTheory

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- **Diffuse measures have positive finite integrated energies**: the type of
`diffuse_betaP_integratedEnergy`. -/
theorem c2_diffuse_betaP_integratedEnergy (n : ℕ) (_hn : 1 ≤ n) (k : ℕ) (_hk : 1 ≤ k)
    (hkn : k < n + 2) (T : FamilyKind) (hT : Nonempty (Models n k T)) (p : ℝ) (hp : 0 < p) :
    (0 < integratedEnergyS ((parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))) k T p
        (point 0 0) 1 ∧
      integratedEnergyS ((parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))) k T p
        (point 0 0) 1 < ⊤) ∧
    (0 < integratedEnergyT ((parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))) k T p
        (point 0 0) 1 ∧
      integratedEnergyT ((parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))) k T p
        (point 0 0) 1 < ⊤) := by
  obtain ⟨_, _, _, _, _, hS, hT'⟩ := Examples.e2_diffuse_energyBounds n k T p hkn hT hp
  simp only [integratedEnergyS, integratedEnergyT, mul_one]
  exact ⟨hS, hT'⟩

end ParabolicRectifiability.BetaP
