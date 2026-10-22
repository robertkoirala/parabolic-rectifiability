import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiabilityStatements
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Lipschitz extension of a planar curve from an arbitrary parameter set

Extend the two coordinates with the scalar extension theorem, using the sup norm
on the coordinate product. Conversion back to the Euclidean norm increases the
constant by the finite-dimensional norm comparison factor.
-/

open Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.BetaP (Plane)

/-- A planar curve Lipschitz on any subset of the real line has a global
Lipschitz extension. The coordinate extension theorem covers the empty set and
zero Lipschitz constant as well. -/
theorem e2_sb_lipschitzExtend_proof : E2sbLipschitzExtend := by
  intro A f K hf
  have hcoord : LipschitzOnWith K (fun x => WithLp.ofLp (f x)) A := by
    simpa only [one_mul, Function.comp_def] using
      (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin 2 => ℝ)).comp_lipschitzOnWith hf
  obtain ⟨g, hg, heq⟩ := hcoord.extend_pi
  refine ⟨fun x => WithLp.toLp 2 (g x),
    ((Fintype.card (Fin 2) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal) * K, ?_, ?_⟩
  · exact (PiLp.lipschitzWith_toLp 2 (fun _ : Fin 2 => ℝ)).comp hg
  · intro x hx
    exact congrArg (WithLp.toLp 2) (heq hx).symm

end ParabolicRectifiability.Examples
