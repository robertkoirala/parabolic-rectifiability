import ParabolicRectifiability.IntegralCanonical.Proofs.Canonical.CanonicalAuxiliaryStatements
import ParabolicRectifiability.Characterization.Assembly.Main
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.UpperDomination
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.DensityMeasurability
import ParabolicRectifiability.IntegralCanonical.Proofs.Canonical.SeparationInequality
import ParabolicRectifiability.IntegralCanonical.Proofs.Canonical.ProjectionLipschitzNull

/-! # Auxiliary results for the canonical decomposition

Proves the three named statements of `i2_UpperDensityCarrierStatement`,
`i2_SeparationInequalityStatement` and `i2_ProjectionLipschitzNullStatement`:

* `i2_separation_inequality` and `i2_projection_lipschitz_null` are the separation
  inequality and the nullity of sets that are Lipschitz graphs over a `(k-2)`-dimensional
  subspace, from `i2_separation_inequality_proof` and `i2_projection_lipschitz_null_proof`;
* `i2_input_upperDensityCarrier` is the carrier statement, obtained from
  `Characterization.hasBorelSigmaFiniteHausdorffCarrier_of_upperDensity_pos` with
  `Foundations.fupdom_upper_density_domination` and `Foundations.fmeas1_density_measurability`.

The density bridge also uses `Foundations.f2i_absolutelyContinuous_of_upperDensity_lt_top`
and the upper-density bound `Foundations.f2i_input_upperDensityBound`.
-/

noncomputable section

namespace ParabolicRectifiability.IntegralCanonical

/-- `i2_UpperDensityCarrierStatement`: positive upper density a.e. gives a Borel
sigma-finite `H_P^k` carrier, by
`Characterization.hasBorelSigmaFiniteHausdorffCarrier_of_upperDensity_pos` with
`Foundations.fupdom_upper_density_domination` and `Foundations.fmeas1_density_measurability`. -/
theorem i2_input_upperDensityCarrier : i2_UpperDensityCarrierStatement := by
  exact fun _ hn _ hk hkn _ hμ hreg hpos => ParabolicRectifiability.Characterization.hasBorelSigmaFiniteHausdorffCarrier_of_upperDensity_pos ParabolicRectifiability.Foundations.fupdom_upper_density_domination ParabolicRectifiability.Foundations.fmeas1_density_measurability hn hk hkn hμ hreg hpos

/-- **Separation inequality** (`i2_SeparationInequalityStatement`).
Proof idea: `L ≥ 0` from the `lipschitz` field. If `ε < 0`, `small_slope` forces `u = v` on the
horizontal domain, so `H.image` is a subsingleton and `p = q` (both sides `≥ 0`). If `ε ≥ 0`,
write `p = (x,t)`, `q = (x',t')`, `d = |x - x'|`, `h = √|t - t'|`, `a = |P_W(x - x')|`,
`b = |P_{W^⊥}(x - x')|`: the horizontal graph gives `h ≤ ε d` (its base difference is an
orthogonal projection of `x - x'`), the vertical graph map `(u,s) ↦ (a₀ + u + G(u,s), s)` with
`p = V.map (P_W x - P_W a₀, t)`-type coordinates and the Lipschitz bound of `G` in the parabolic
metric of `W × Time` give `b ≤ L max(a, h) ≤ L a + L ε d`; with `d ≤ a + b`,
`(1 - Lε) d ≤ (1 + L) a`, so `d ≤ 2(1+L) a`; finally `d_P(p,q) = max(d, h) = d` as `h ≤ ε d ≤ d`.
Useful facts: `ParabolicRectifiability.dist_point`,
`ParabolicRectifiability.SmallGraphs.dist_space`,
`Submodule.lipschitzWith_orthogonalProjectionOnto`. -/
theorem i2_separation_inequality : i2_SeparationInequalityStatement := by
  exact ParabolicRectifiability.IntegralCanonical.i2_separation_inequality_proof

/-- **Projection-Lipschitz sets are null** (`i2_ProjectionLipschitzNullStatement`).
Proof idea: if `C < 0`, `S` is a subsingleton and `hausdorffP_singleton` (`k ≥ 2 > 0`) applies. If
`C ≥ 0`, put `P = W.orthogonalProjectionOnto ∘ Prod.fst`, `f = Function.invFunOn P S` on `P '' S`;
the hypothesis gives `p = f (P p)` for `p ∈ S` and `LipschitzOnWith (Real.toNNReal C) f (P '' S)`,
so `S ⊆ f '' (P '' S)` and `dimH S ≤ dimH (P '' S) ≤ dimH (univ : Set W) = k - 2 < k`
(`LipschitzOnWith.dimH_image_le`, `Real.dimH_univ_eq_finrank`), hence
`μH[k] S = 0` (`hausdorffMeasure_of_dimH_lt`; `hausdorffP_eq`). -/
theorem i2_projection_lipschitz_null : i2_ProjectionLipschitzNullStatement := by
  exact ParabolicRectifiability.IntegralCanonical.i2_projection_lipschitz_null_proof

end ParabolicRectifiability.IntegralCanonical
