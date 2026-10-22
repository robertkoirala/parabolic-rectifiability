import ParabolicRectifiability.BetaP.Proofs.Packing.PackingStatements
import ParabolicRectifiability.BetaP.Proofs.Laws.Holder
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.BetaPowTwo
import ParabolicRectifiability.BetaP.Proofs.Packing.Basics
import ParabolicRectifiability.BetaP.Proofs.Packing.HolderReduction
import ParabolicRectifiability.BetaP.Proofs.Packing.DoubledParent

/-! # Auxiliary results for the active-radius packing bound

These are the results used by `cpk_activeRadiusPacking_of_discretePacking` to prove
`activeRadiusPacking_of_discretePacking`. They prove the named statements `Cpk…Statement`.

* Six auxiliary results: `cpk_activeSource`, `cpk_leastActiveBound`, `cpk_holderReduction`,
  `cpk_doubledParent`, `cpk_absorption`, `cpk_massBound`.
* Two input statements: `cpk_input_holder` and `cpk_input_betaPowTwo`.

The quadratic discrete packing theorem is not proved here: `activeRadiusPacking_of_discretePacking`
takes `DiscretePackingBound n C₀` as a hypothesis, supplied from `discrete_packing_proof`.

Neither `BetaPowRestrictionStatement` nor `EmptyTestingBallStatement` is needed: the subfamily
comparison `σ'_s ≤ σ_s` is a comparison of measures, not a restriction, and uses the monotonicity
of `fitPow` in the source; every tail integral is over `s > r_i`, where the central atom is
active, and the zero-mass case of Hölder is inside the Hölder law.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## Input statements -/

/-- **Hölder with the density factor**: `BetaPowHolderStatement`, proved by `claws_holder_proof`.
It is used by `cpk_holderReduction`. -/
theorem cpk_input_holder : BetaPowHolderStatement := ParabolicRectifiability.BetaP.claws_holder_proof

/-- **`B_2 = betaSq`**: `Foundations.BetaPowTwoStatement`, proved by
`f3_betaPow_two_eq_betaSq_proof`. It is used by `cpk_holderReduction`. -/
theorem cpk_input_betaPowTwo : BetaPowTwoStatement := ParabolicRectifiability.Foundations.f3_betaPow_two_eq_betaSq_proof

/-! ## The auxiliary statements -/

/-- **Active-source identity** (`CpkActiveSourceStatement`). For pairwise disjoint open balls `P(z_j,r_j)` of
positive radii and every `s ≥ r_i`, `B_p(σ_s; z_i, s) = B_p(σ; z_i, s)`, where
`σ = atomicSource k z r w` and `σ_s = BetaP.truncatedAtomicSource k z r w s`; every `p`, `T`,
weight.

Proof: disjointness gives `d(z_i,z_j) ≥ r_j` for `j ≠ i`, so for `s ≥ r_i` every atom in
`P(z_i,s)` has `r_j ≤ s`, and the restrictions of `σ` and `σ_s` to `P(z_i,s)` coincide; each
`fitPow` integrates only over that ball. This adapts
`restrict_ball_finiteCutoffAtomicMeasure_eq_fullAtomicMeasure` and
`betaSq_finiteCutoffAtomicMeasure_eq_fullAtomicMeasure`:
`atomicSource k z r w` is `fullAtomicMeasure z (fun j => w j * r j ^ k)` and
`BetaP.truncatedAtomicSource k z r w s` is `finiteCutoffAtomicMeasure z r (fun j => w j * r j ^ k) s`
up to unfolding (compare `truncatedAtomicSource_eq_finiteCutoffAtomicMeasure`), with `fit`
replaced by `fitPow` (the analogue of `fit_eq_of_restrict_ball_eq`). Disjointness in
`∀ i j, i ≠ j → …` form converts to `Pairwise`. -/
theorem cpk_activeSource : CpkActiveSourceStatement := cpk_activeSource_proof

/-- **The least active bound** (`CpkLeastActiveBoundStatement`): for `0 < r_i`, `0 < w_i ≤ b`, there is
`Λ ≥ 0` that is an active bound and is below every active bound.

Proof: take `Λ = sSup {s^{-k} cpkActiveMass k z r w x s | x, s > 0}`. The set is nonempty
(`x = point 0 0`, `s = 1`), nonnegative, and bounded by `N b`: each active term has
`0 < r_i ≤ s`, so `w_i r_i^k s^{-k} ≤ w_i ≤ b`. Then `le_csSup` gives the bound and
`csSup_le` the minimality (divide by `s^k > 0`). -/
theorem cpk_leastActiveBound : CpkLeastActiveBoundStatement := cpk_leastActiveBound_proof

/-- **Hölder reduction** (`CpkHolderReductionStatement`). For an injection `e : Fin l → Fin N`, a
subfamily centre `z_{e j}` and `s > r_{e j}`, with `σ'_s` the quadratic truncated source of the
subfamily and
`σ_s` the `p`-testing source of the whole family:
`B_2(σ'_s) = betaSq(σ'_s) ≤ Θ(σ'_s)^{1-2/p} B_p(σ'_s)^{2/p} ≤ Λ^{1-2/p} B_p(σ_s)^{2/p}` at
`(z_{e j}, s)`; integrating over `s > r_{e j}` gives `≤ Λ^{1-2/p} B`.

Proof:
1. `BetaPowTwoStatement` turns `betaSq σ'_s` into `betaPow σ'_s … 2`.
2. Clause 2 of `BetaPowHolderStatement` at `σ'_s` (a finite sum of Dirac masses: finite, hence
   `IsFiniteMeasureOnCompacts` and inner regular), radius `s > 0`.
3. `densityRatio σ'_s k z_{e j} s ≤ ofReal Λ`: by injectivity of `e`, `σ'_s(P(z_{e j},s))` is a
   sub-sum of `Σ_{r_i ≤ s, z_i ∈ P(z_{e j},s)} ofReal (w_i r_i^k) = ofReal (cpkActiveMass …)`,
   which is `≤ ofReal (Λ s^k)`; then `x ↦ x^{1-2/p}` is monotone (`1 - 2/p ≥ 0`).
4. `σ'_s ≤ σ_s` as measures (injective sub-sum), hence `B_p(σ'_s) ≤ B_p(σ_s)`: monotonicity of
   `fitPow` in the source (as `fit_mono_measure`), then of the infimum and of `x ↦ x^{2/p}`.
   This step is `claws_betaPow_mono_measure`.
5. Pull the constant `(ofReal Λ)^{1-2/p} ≠ ⊤` out of the lower integral
   (`lintegral_const_mul'`) and use the hypothesis at index `e j`;
   `ofReal Λ ^ (1-2/p) * ofReal B = ofReal (Λ^{1-2/p} B)` (`ENNReal.ofReal_rpow_of_nonneg`,
   `ENNReal.ofReal_mul`). At `p = 2` both powers are `^0 = 1`.
Related quadratic facts: `betaSq_fullAtomicSource_eq_truncated` and
`allScaleEnergy_fullAtomicSource_le` for atomic sources, `fit_finiteCutoffAtomicMeasure` for
evaluating atomic fits.

The statement is in implication form over `BetaPowHolderStatement` and `BetaPowTwoStatement`. -/
theorem cpk_holderReduction : CpkHolderReductionStatement := cpk_holderReduction_proof

/-- **Doubled parent** (`CpkDoubledParentStatement`): `CpkSubfamilyTailBound k T z r w B'` and
`DiscretePackingBound n C₀` give the active bound `2^k C₀ (b + B')`.

Proof: fix `x` and `s > 0`; let `I = {i : r_i ≤ s ∧ dist (z i) x < s}` and enumerate it
injectively, `e = (↑) ∘ I.equivFin.symm : Fin I.card → Fin N`. Apply `DiscretePackingBound n C₀`
with parent `P(x, 2s)` to the subfamily `(z ∘ e, r ∘ e, w ∘ e)`: radii positive; each
`P(z_i, r_i) ⊆ P(x, 2s)` since `r_i ≤ s` and `d(z_i,x) < s` (triangle inequality); disjointness
and `0 < w_i ≤ b`, `0 < b`, `0 ≤ B'` are inherited; the tail hypothesis is the hypothesis at `e`.
The conclusion `Σ_j ofReal (w_{e j} r_{e j}^k) ≤ ofReal (C₀ (b + B') (2s)^k)` becomes, with
nonnegative terms (`ENNReal.ofReal_sum_of_nonneg`, `ENNReal.ofReal_le_ofReal_iff` with the
right side `≥ 0` because `C₀ > 0`, `b > 0`, `B' ≥ 0`), `cpkActiveMass k z r w x s ≤
2^k C₀ (b + B') s^k` after reindexing the sum along `e` (`Finset.sum_equiv`/`Finset.sum_coe_sort`)
and `(2s)^k = 2^k s^k`. For `I = ∅` both sides are `0 ≤ …`.
Related facts: the reindexing in `HasFiniteBallPacking.finset` and the use of
`DiscretePackingBound` in `sum_weight_le_of_barycenterCells`. -/
theorem cpk_doubledParent : CpkDoubledParentStatement := cpk_doubledParent_proof

/-- **Bootstrap absorption** (`CpkAbsorptionStatement`), a real inequality.

Proof: if `Λ ≤ 2Db`, then `Λ ≤ 2D(b + B^{p/2}) ≤ max{…}(b + B^{p/2})`. Otherwise `Λ > 2Db ≥ 0`,
so `Λ > 0` and `Λ/2 < Λ - Db ≤ D Λ^{1-2/p} B`; dividing by `Λ^{1-2/p} > 0`
(`Real.rpow_pos_of_pos`) and using `Λ = Λ^{2/p} Λ^{1-2/p}` (`Real.rpow_add`) gives
`Λ^{2/p} < 2DB`; raising to `p/2 > 0` (`Real.rpow_lt_rpow`, `Real.rpow_mul`,
`Real.mul_rpow`) gives `Λ < (2D)^{p/2} B^{p/2} ≤ max{…}(b + B^{p/2})`. At `p = 2` the same
computation runs with `Λ^0 = 1`. -/
theorem cpk_absorption : CpkAbsorptionStatement := cpk_absorption_proof

/-- **Mass bound** (`CpkMassBoundStatement`): for a weighted packing of `P(q,R)` and an active
bound `Λ`, `atomicSource k z r w univ ≤ ofReal (Λ R^k)`.

Proof: if `N = 0` the left side is `0`. Otherwise `R > 0` (the nonempty ball `P(z_0,r_0)`
lies in `P(q,R)`), every `r_i ≤ R` by `radius_le_of_ball_subset`, and every `z_i ∈ P(q,R)`; so the active filter at `(q,R)` is
all of `Fin N` and `atomicSource k z r w univ = Σ_i ofReal (w_i r_i^k) = ofReal (cpkActiveMass k
z r w q R) ≤ ofReal (Λ R^k)` (`Measure.finsetSum_apply`, `Measure.dirac_apply_of_mem`
or `measure_univ`, `ENNReal.ofReal_sum_of_nonneg`). -/
theorem cpk_massBound : CpkMassBoundStatement := cpk_massBound_proof

end ParabolicRectifiability.BetaP
