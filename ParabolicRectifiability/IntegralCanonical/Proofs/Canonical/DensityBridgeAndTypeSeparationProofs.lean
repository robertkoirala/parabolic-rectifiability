import ParabolicRectifiability.IntegralCanonical.Proofs.Canonical.CanonicalAuxiliaryResults
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.FiniteUpperDensityAbsoluteContinuity

/-! # Density bridge and type separation for the canonical decomposition

This file proves the two auxiliary statements used by the canonical decomposition:

* `i2_isIntrinsicSource_of_hasPositiveFiniteUpperDensity : IntrinsicSourceOfDensityStatement`
  (the same statement as `isIntrinsicSource_of_hasPositiveFiniteUpperDensity` and
  `isIntrinsicSource_of_upperDensity`): positive finite upper density a.e. makes `μ` an
  intrinsic source;
* `i2_horizontalGraph_inter_ordinaryVerticalGraph_separation : TypeSeparationStatement`
  (the same statement as `horizontalGraph_inter_ordinaryVerticalGraph_separation` and
  `type_separation`): a horizontal graph meets an ordinary vertical graph in an `H_P^k`-null
  set on which the projection to `W` is injective.

The first combines the absolute-continuity result
`f2i_absolutelyContinuous_of_upperDensity_lt_top` (with the upper-density bound
`f2i_input_upperDensityBound`) and the carrier statement `i2_input_upperDensityCarrier`. The
second uses `i2_separation_inequality` and `i2_projection_lipschitz_null`; injectivity and the
`k = 2` subsingleton conclusion follow from the inequality (a zero projection distance forces a
zero parabolic distance; at `k = 2` the subspace `W` has rank zero).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

/-- **Density bridge.** `IntrinsicSourceOfDensityStatement`: `0 < Θ^{k,*} < ∞` a.e. gives
`μ ≪ H_P^k` by `f2i_absolutelyContinuous_of_upperDensity_lt_top` applied to the upper-density
bound `f2i_input_upperDensityBound` (finite part), and a Borel sigma-finite `H_P^k` carrier by
`i2_input_upperDensityCarrier` (positive part). No finite-square hypothesis is used. -/
theorem i2_isIntrinsicSource_of_hasPositiveFiniteUpperDensity :
    IntrinsicSourceOfDensityStatement := by
  intro n hn k hk hkn μ hμ hreg hdens
  exact ⟨f2i_absolutelyContinuous_of_upperDensity_lt_top f2i_input_upperDensityBound n hn k hk hkn
      μ hμ hreg (hdens.mono fun z hz => hz.2),
    i2_input_upperDensityCarrier n hn k hk hkn μ hμ hreg (hdens.mono fun z hz => hz.1)⟩

/-- **Type separation.** `TypeSeparationStatement`: the distance inequality is
`i2_separation_inequality`; injectivity and the `k = 2` subsingleton follow from it; nullity is
`i2_projection_lipschitz_null` with `W = V.direction`, `S = H.image ∩ V.image`, `C = 2(1+L)`. -/
theorem i2_horizontalGraph_inter_ordinaryVerticalGraph_separation :
    TypeSeparationStatement := by
  intro n k hk hkn L V ε H hε hLε
  have hineq := i2_separation_inequality n k hk hkn L V ε H hε hLε
  have hzero : ∀ p ∈ H.image ∩ V.image, ∀ q ∈ H.image ∩ V.image,
      V.direction.orthogonalProjectionOnto p.1 = V.direction.orthogonalProjectionOnto q.1 →
        p = q := by
    intro p hp q hq hpq
    have h := hineq p hp q hq
    rw [hpq, dist_self, mul_zero] at h
    exact dist_le_zero.1 h
  refine ⟨?_, hineq,
    i2_projection_lipschitz_null n k V.direction V.rank_eq _ (2 * (1 + L)) hineq, ?_⟩
  · intro p hp q hq hpq
    exact hzero p hp q hq hpq
  · intro hk2 p hp q hq
    apply hzero p hp q hq
    have h0 : Module.finrank ℝ V.direction = 0 := by
      have := V.rank_eq
      omega
    have h0' : ∀ x : V.direction, x = 0 := finrank_zero_iff_forall_zero.1 h0
    exact (h0' _).trans (h0' _).symm

end ParabolicRectifiability.IntegralCanonical
