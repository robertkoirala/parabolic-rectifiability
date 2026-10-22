import ParabolicRectifiability.Examples.Proofs.DensityTests.DiffuseEstimateStatements
import ParabolicRectifiability.Examples.Proofs.DiffuseMeasures.BetaLower
import ParabolicRectifiability.Examples.Proofs.DiffuseMeasures.BetaUpper
import ParabolicRectifiability.Examples.Proofs.DiffuseMeasures.Energy
import ParabolicRectifiability.Examples.Proofs.DiffuseMeasures.HorizontalLower
import ParabolicRectifiability.Examples.Proofs.DiffuseMeasures.Source
import ParabolicRectifiability.Examples.Proofs.DiffuseMeasures.VerticalLower
import ParabolicRectifiability.Examples.Proofs.DiffuseMeasures.ScaleIntegral

/-! # Estimates for the diffuse source

Each statement `E2Diffuse…` is proved by the corresponding module.
-/

namespace ParabolicRectifiability.Examples

/-- **Source bounds.** Route: `ω(P(z,r)) ≤ parabolicVolume(P(z,r)) = 2ω_n r^{n+2}` (`Measure.restrict_le_self`,
`parabolicVolume_ball`); finiteness: `ω univ = λ(P(0,1/4)) < ⊤`
(`omega_lt_top`); `ω(D) = λ(D ∩ P(0,1/4)) = λ(D) = 2ω_n 16^{-(n+2)} > 0` (`omega_pos`). -/
theorem e2_diffuse_source : E2DiffuseSourceStatement := by
  exact e2_diffuse_source_proof

/-- **Uniform beta upper bound.** Route: `exists_model_mem` gives `L ∋ z`;
on `P(z,r)`, `infEDist w (modelSet L) ≤ edist w z < r`, so
`fitPow ω p L z r ≤ r^p ω(P(z,r)) ≤ 2ω_n r^{n+2+p}` (`setLIntegral_mono` with a constant
majorant, `ENNReal.rpow_le_rpow`, ball bound proved inline from
`parabolicVolume_ball` or taken from `Measure.restrict_le_self`); then `iInf_le` and
`r^{-k-p} r^{n+2+p} = r^{n+2-k}` (`ENNReal.inv_rpow`, `ENNReal.rpow_add`, `ofReal r ≠ 0, ⊤`). -/
theorem e2_diffuse_betaUpper : E2DiffuseBetaUpperStatement := by
  exact e2_diffuse_betaUpper_proof

/-- **Horizontal lower fit.**
Route: for `z = (x,t) ∈ D`, `r ∈ I`, the cylinder `P(z,r)` lies in `P(0,1/4)`, so `ω = λ` there.
For the model at time `τ`, take the **open** half interval `J = (t+r²/2, t+r²)` if `τ ≤ t`, else
`J = (t-r², t-r²/2)`; on `B(x,r) × J`, `|s-τ| ≥ r²/2`, so `d_P(w,L) ≥ √|s-τ| ≥ r/√2`
(`HorizontalModel.infEDist_eq_projection`, `dist_projection_sq`). Volume `λ(B(x,r) × J) = ω_n r^n · r²/2`
(`parabolicVolume_apply`, `Measure.prod_prod`, `volume_spatial_ball`). Hence the bound with
`a = ω_n.toReal 2^{-1-p/2}`. Closed half intervals would contain a point outside the open ball. -/
theorem e2_diffuse_horizontalLower : E2DiffuseHorizontalLowerStatement := by
  exact e2_diffuse_horizontalLower_proof

/-- **Vertical lower fit.** Route: the model has spatial rank `q = k - 2 < n`, so its direction
`W` has a unit normal `e` (`Submodule.exists_mem_ne_zero_of_ne_bot` on `Wᗮ ≠ ⊥`, from
`finrank W < n`). With `c = ⟨x - a₀, e⟩` choose `σ = 1` if `c ≥ 0` and `σ = -1` if `c < 0` (the sign of `c`, not its opposite), so that
`|c + σ·3r/4| = |c| + 3r/4 ≥ 3r/4`; the subball `B(x + σ(3r/4)e, r/4) ⊆ B(x,r)` then has
`|⟨y - a₀, e⟩| ≥ 3r/4 - r/4 = r/2`, hence spatial distance to `a₀ + W` at least `r/2`, which is
`d_P` to the vertical model (`VerticalModel.dist_projection_sq`). Times `(t-r², t+r²)`: volume `ω_n (r/4)^n · 2r²`.
Hence `a = 2 ω_n.toReal 4^{-n} 2^{-p}`. No spherical-cap volume is needed. -/
theorem e2_diffuse_verticalLower : E2DiffuseVerticalLowerStatement := by
  exact e2_diffuse_verticalLower_proof

/-- **Infimum and normalization.**
Route: `le_iInf` over the uniform lower fit, then
`r^{-k-p} · a r^{n+2+p} = a r^{n+2-k} ≥ a 32^{-(n+2-k)}` for `r ≥ 1/32` and `n + 2 - k > 0`
(`ENNReal.rpow_le_rpow`, `ENNReal.inv_rpow`, `ENNReal.rpow_add`). An empty family gives
`B_p = ⊤` at positive radii. -/
theorem e2_diffuse_betaLower : E2DiffuseBetaLowerStatement := by
  exact e2_diffuse_betaLower_proof

/-- **Scale integrals.** Route: `setLIntegral_scaleMeasure` turns the left
side into `∫_{(0,2)} r^{γ-1} dr`; `integral_rpow` / `intervalIntegral.integral_rpow` with
`ofReal_integral_eq_lintegral_ofReal` gives `2^γ/γ`. The band: `scaleMeasure_Icc_lt_top` and `scaleMeasure_apply` with density `1/r ≥ 16` on the band. -/
theorem e2_scaleIntegral : E2ScaleIntegralStatement := by
  exact e2_scaleIntegral_proof

/-- **Pointwise and integrated energy assembly.** Implication form over the source bounds, the
beta upper bound, the scale integrals and the conclusion of the infimum statement.
Route: pointwise, `B_p^{(2/p)} ≤ (2ω_n)^{2/p} r^{2α/p}` and `B_p ≤ 2ω_n r^α` on `(0,2)`
(`ENNReal.mul_rpow_of_nonneg`), integrated by the scale integrals (`lintegral_const_mul`), give real
`A_S, A_T > 0`. Finiteness: `∫_{P(0,1)} ≤ A · ω(univ) < ⊤`. Positivity: for `z ∈ D ⊆ P(0,1)`,
`energy(z) ≥ ∫_I b^{(2/p)} = b^{(2/p)} scaleMeasure(I) > 0` (`I ⊆ (0,2)`,
`setLIntegral_mono_set`-type monotonicity, no measurability of the integrand), and
`∫_{P(0,1)} ≥ ω(D) · that > 0`. -/
theorem e2_diffuse_energy : E2DiffuseEnergyStatement := by
  exact e2_diffuse_energy_proof

end ParabolicRectifiability.Examples
