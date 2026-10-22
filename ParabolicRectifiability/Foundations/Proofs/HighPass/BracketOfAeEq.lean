import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Foundations.Proofs.HighPassBracket.FibreKernel

/-! # The bracket of a test whose half derivative is a real function

Proof of `fhpbc_c2_bracketOfAeEq` (of type `FhpbcBracketOfAeEqStatement`, no hypotheses).

Let `Θ` be a complex Schwartz test whose half derivative agrees a.e. with a real function `ψ`,
and let `G ψ` be integrable. Then `∫ t, halfTimeSpatialBracket G Θ t = ∫ G ψ`.

* The a.e. identity on `FourierSpace m` is pulled back along the measure-preserving time-first
  coordinates `(t,u) ↦ toLp 2 (u,t)` and sliced with time outside (`Measure.ae_ae_of_ae_prod`),
  exactly as in `fhpa_ae_fibre_halfTimeDeriv`: for a.e. `t`, the spatial integrands agree a.e., so
  `halfTimeSpatialBracket G Θ t = ∫ G(u,t) ψ(u,t) du` (a real integral, cast to `ℂ`).
* `G ψ` composed with the coordinates is integrable on `ℝ × ℝ^m`; Fubini (`integral_prod`) and the
  change of variables along the coordinates (`integral_map`) identify the iterated integral with
  `∫ G ψ`; `integral_complex_ofReal` moves the cast outside.

The coordinate lemma `fhpab12_timeFirst_measurePreserving` is taken from the proof of
`fhpa_ae_fibre_halfTimeDeriv`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- Proof-only shortcut, as in the construction of `testKernel`: the default
instance search for `ContinuousSMul ℝ (FourierSpace m)` on the `L²` product exceeds the heartbeat
budget. -/
local instance fhpbc2k_continuousSMul (m : ℕ) : ContinuousSMul ℝ (FourierSpace m) :=
  IsBoundedSMul.continuousSMul

/-- Slicing: if the half derivative of `Θ` agrees a.e. with `ψ` on `FourierSpace m`, then for
a.e. time `t` the spatial fibres agree a.e. -/
theorem fhpbc2k_ae_fibre {m : ℕ} {Θ : 𝓢(FourierSpace m, ℂ)} {ψ : FourierSpace m → ℝ}
    (hae : (halfTimeDeriv m Θ : FourierSpace m → ℂ) =ᵐ[volume] (fun x => (ψ x : ℂ))) :
    ∀ᵐ t : ℝ, ∀ᵐ u : Spatial m,
      halfTimeDeriv m Θ (WithLp.toLp 2 (u, t)) = (ψ (WithLp.toLp 2 (u, t)) : ℂ) := by
  have h1 := (fhpab12_timeFirst_measurePreserving m).quasiMeasurePreserving.ae_eq_comp hae
  exact Measure.ae_ae_of_ae_prod h1

/-- For a.e. time `t`, the spatial bracket is the (cast) real spatial integral of `G ψ`. -/
theorem fhpbc2k_ae_bracket {m : ℕ} (G : FourierSpace m → ℝ) {Θ : 𝓢(FourierSpace m, ℂ)}
    {ψ : FourierSpace m → ℝ}
    (hae : (halfTimeDeriv m Θ : FourierSpace m → ℂ) =ᵐ[volume] (fun x => (ψ x : ℂ))) :
    ∀ᵐ t : ℝ, halfTimeSpatialBracket G Θ t =
      ((∫ u : Spatial m, G (WithLp.toLp 2 (u, t)) * ψ (WithLp.toLp 2 (u, t)) : ℝ) : ℂ) := by
  filter_upwards [fhpbc2k_ae_fibre hae] with t ht
  unfold halfTimeSpatialBracket
  rw [← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [ht] with u hu
  simp only [halfTimeSpatialIntegrand, hu, Complex.ofReal_mul]

/-- Fubini through the time-first coordinates: the iterated integral, time outside, of an
integrable real function on `FourierSpace m` is its integral. -/
theorem fhpbc2k_integral_iterated {m : ℕ} {F : FourierSpace m → ℝ} (hF : Integrable F) :
    ∫ t : ℝ, ∫ u : Spatial m, F (WithLp.toLp 2 (u, t)) = ∫ x, F x := by
  have hmp := fhpab12_timeFirst_measurePreserving m
  have hFi : Integrable (F ∘ fun p : ℝ × Spatial m => WithLp.toLp 2 (p.2, p.1))
      ((volume : Measure ℝ).prod (volume : Measure (Spatial m))) :=
    hmp.integrable_comp_of_integrable hF
  have hmap := integral_map (μ := (volume : Measure ℝ).prod (volume : Measure (Spatial m)))
    hmp.measurable.aemeasurable (f := F) (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)
  rw [hmp.map_eq] at hmap
  rw [hmap]
  exact (integral_prod _ hFi).symm

/-- **The bracket of a test whose half derivative is a real function**
(`fhpbc_c2_bracketOfAeEq`). -/
theorem fhpbc_c2_bracketOfAeEq_proof : FhpbcBracketOfAeEqStatement := by
  intro m G Θ ψ hae hint
  calc ∫ t, halfTimeSpatialBracket G Θ t
      = ∫ t : ℝ, ((∫ u : Spatial m, G (WithLp.toLp 2 (u, t)) * ψ (WithLp.toLp 2 (u, t)) : ℝ)
          : ℂ) := integral_congr_ae (fhpbc2k_ae_bracket G hae)
    _ = ((∫ t : ℝ, ∫ u : Spatial m, G (WithLp.toLp 2 (u, t)) * ψ (WithLp.toLp 2 (u, t)) : ℝ)
          : ℂ) := integral_complex_ofReal
    _ = ((∫ x, G x * ψ x : ℝ) : ℂ) := by
        rw [fhpbc2k_integral_iterated (F := fun x => G x * ψ x) hint]

end ParabolicRectifiability.Foundations
