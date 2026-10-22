import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.TransferStatements
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! # The coupling induced by a Markov kernel

Proves `KernelCouplingStatement` (`b3_kernelCoupling_proof`). For a Borel `Γ`, a Markov kernel `K` carried by `Γ` with `K_y`-a.e. `d(y,v) ≤ 3 dist(y,Γ)`, and a
finite measure `μ`, the coupling is `π = μ ⊗ₘ K`:
* finite, since `μ` is finite and `K` is Markov;
* `π.fst = μ` (`Measure.fst_compProd`);
* `π.snd Γᶜ = ∫ K_y(Γᶜ) dμ(y) = 0` (`Measure.snd_apply`, `Measure.compProd_apply`);
* the displacement set `{p | d(p.1,p.2) ≤ 3 dist(p.1,Γ)}` is Borel, so
  `Measure.ae_compProd_iff` reduces the a.e. displacement to the kernel hypothesis.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace ParabolicRectifiability.Characterization.SourceTransferTree

open ParabolicRectifiability.Foundations

/-- The displacement set `{p | d(p.1,p.2) ≤ 3 dist(p.1,Γ)}` is measurable in `X × X`. -/
theorem b3kcpl_measurableSet_displacement {n : ℕ} (Γ : Set (Space n)) :
    MeasurableSet {p : Space n × Space n | edist p.1 p.2 ≤ 3 * Metric.infEDist p.1 Γ} :=
  measurableSet_le (measurable_fst.edist measurable_snd)
    ((measurable_infEDist.comp measurable_fst).const_mul 3)

/-- **Kernel coupling** (`KernelCouplingStatement`): `π = μ ⊗ₘ K` is a finite coupling of `μ`
with a measure carried by `Γ`, moving each point at most three times its distance to `Γ`. -/
theorem b3_kernelCoupling_proof : KernelCouplingStatement := by
  intro n Γ hΓ K hK hKΓ hKd μ hμ
  refine ⟨μ ⊗ₘ K, inferInstance, Measure.fst_compProd μ K, ?_, ?_⟩
  · rw [Measure.snd_apply hΓ.compl, Measure.compProd_apply (measurable_snd hΓ.compl)]
    have h : ∀ y : Space n, K y (Prod.mk y ⁻¹' (Prod.snd ⁻¹' Γᶜ)) = 0 := fun y => hKΓ y
    simp only [h, lintegral_zero]
  · rw [Measure.ae_compProd_iff (b3kcpl_measurableSet_displacement Γ)]
    exact Filter.Eventually.of_forall hKd

/-- `b3_kernelCoupling_proof` has the type `KernelCouplingStatement`. -/
example : KernelCouplingStatement := b3_kernelCoupling_proof

end ParabolicRectifiability.Characterization.SourceTransferTree
