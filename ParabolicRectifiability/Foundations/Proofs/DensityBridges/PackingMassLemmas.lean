import ParabolicRectifiability.Foundations.Statements.DensityBridges
import ParabolicRectifiability.Characterization.Proofs.Fivefold
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.ElementaryLemmas
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.PackingCover
import ParabolicRectifiability.Characterization.Statements.SourceTransfer

/-! # Packing turns lower density into retained mass: intermediate statements

Target: `restrict_ball_le_of_packing_lowerDensity : PackingMassStatement`, assembled in
`fpack_packing_mass`. The proof is split into selection, countable summation and the limiting
step:
* `fpack_input_fivefold` — the fivefold selection statement `FivefoldSelectionStatement`;
* `fpack_exists_good_radius` — a lower-density bound gives arbitrarily small good radii;
* `fpack_tsum_le_of_finite_packing` — the `Fin l` packing bound gives the same bound for
  an arbitrary disjoint family (countable summation);
* `fpack_restrict_ball_le_add_of_fivefold` — the covering estimate at a fixed density
  slack `ε > 0`, in implication form from `FivefoldSelectionStatement`;
* the limiting step `ε ↓ 0` is performed in `fpack_packing_mass`.

The declarations delegate to the proofs named `<name>_proof`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- **Fivefold selection** `FivefoldSelectionStatement`, proved as
`Characterization.fivefold_ball_selection`. It is not re-proved here; there is no second
Vitali covering. -/
theorem fpack_input_fivefold : Characterization.FivefoldSelectionStatement := by
  exact Characterization.fivefold_ball_selection_proof

/-- **Good radii from a lower-density bound.** There are arbitrarily small `r > 0` such that
`ρ₀(P(z,r)) ≤ (A+ε) r^k`.

For any measure `μ`, any `k`, a point `z` with `Θ_*^k(μ,z) ≤ A` (`A ≥ 0`
real), a slack `ε > 0` and a bound `δ > 0`, there is a radius `0 < r < δ` with
`μ(P(z,r)) ≤ (A+ε) r^k` (through `ENNReal.ofReal`).

Route: `ofReal A < ofReal (A+ε)` (`ENNReal.ofReal_lt_ofReal_iff`, `0 < A + ε`), so
`liminf (densityRatio μ k z) (𝓝[>] 0) < ofReal (A+ε)`; `Filter.frequently_lt_of_liminf_lt`
gives `∃ᶠ r in 𝓝[>] 0, densityRatio μ k z r < ofReal (A+ε)`; intersect with the eventual set
`Ioo 0 δ` (`Ioo_mem_nhdsGT`, `Filter.Frequently.and_eventually`, `.exists`). At `r > 0`,
`ofReal r ^ k ≠ 0, ⊤`, so `μ(P(z,r)) / ofReal r ^ k < ofReal (A+ε)` gives
`μ(P(z,r)) ≤ ofReal (A+ε) * ofReal r ^ k = ofReal ((A+ε) r^k)` (`ENNReal.div_le_iff`,
`ENNReal.ofReal_mul`, `ENNReal.ofReal_pow`). No regularity of `μ`; valid for every `k`. -/
theorem fpack_exists_good_radius {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n)
    (A : ℝ) (hA : 0 ≤ A) (hz : lowerDensity μ k z ≤ ENNReal.ofReal A)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r < δ ∧ μ (Metric.ball z r) ≤ ENNReal.ofReal ((A + ε) * r ^ k) := by
  exact fpack_exists_good_radius_proof μ k z A hA hz ε hε δ hδ

/-- **Finite packing gives packing for arbitrary disjoint families** (countable summation;
finite `Fin l` families are sufficient and equivalent to countable families by taking suprema
of finite subsums).

Fix a centre `q` and a radius `ρ`. If every finite (`Fin l`-indexed) family of
pairwise disjoint balls `P(z_i,r_i)` with `z_i ∈ K ∩ P(q,ρ)` and `0 < r_i ≤ ρ` has
`∑ r_i^k ≤ C_K ρ^k`, then the same bound holds for the `tsum` over an arbitrary index type `ι`
with the same three properties (in `ℝ≥0∞`; no countability needed).

Route: `ENNReal.tsum_eq_iSup_sum` and `iSup_le`: for a finset `s : Finset ι`, reindex by
`s.equivFin.symm` (or `Finset.sum_equiv`/`Finset.sum_coe_sort`) to a `Fin s.card` family; the
disjointness of distinct `Fin` indices follows from injectivity of the reindexing; apply the
hypothesis.

The index type is `ι : Type` (universe `0`), the universe of `FivefoldSelectionStatement`, so
that the covering estimate below can take this statement as a hypothesis without a universe
mismatch. -/
theorem fpack_tsum_le_of_finite_packing {n : ℕ} (k : ℕ) (K : Set (Space n)) (C_K : ℝ)
    (q : Space n) (ρ : ℝ)
    (hpack : ∀ (l : ℕ) (z : Fin l → Space n) (r : Fin l → ℝ),
      (∀ i, z i ∈ K ∩ Metric.ball q ρ) →
      (∀ i, 0 < r i ∧ r i ≤ ρ) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∑ i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C_K * ρ ^ k))
    {ι : Type} (z : ι → Space n) (r : ι → ℝ)
    (hz : ∀ i, z i ∈ K ∩ Metric.ball q ρ) (hr : ∀ i, 0 < r i ∧ r i ≤ ρ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) :
    (∑' i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C_K * ρ ^ k) := by
  exact fpack_tsum_le_of_finite_packing_proof k K C_K q ρ hpack z r hz hr hdisj

/-- **The covering estimate at a fixed density slack.**
Implication form: the fivefold selection `FivefoldSelectionStatement` is the first
hypothesis; `fpack_packing_mass` supplies it from `fpack_input_fivefold`.

The hypotheses of `PackingMassStatement`, in the same order
(Borel `K`; `R₀ > 0`, `C_K ≥ 0` with the `Fin l` disjoint-ball packing bound at every centre and
every `0 < ρ ≤ R₀`; locally Radon `ρ₀`; `A ≥ 0` with `Θ_*^k(ρ₀,z) ≤ A` for `ρ₀`-a.e. `z ∈ K`;
a centre `q` and `0 < ρ ≤ R₀`), and a slack `ε > 0`, give
`(ρ₀⌊K)(P(q,ρ)) ≤ 5^k C_K (A+ε) ρ^k`.

Route. `(ρ₀⌊K)(P(q,ρ)) = ρ₀(P(q,ρ) ∩ K)` (`Measure.restrict_apply measurableSet_ball`). Let
`N = {z | ¬ (z ∈ K → Θ_*^k(ρ₀,z) ≤ A)}`, a `ρ₀`-null set (`ae_iff`; no measurability needed).
Index set `ι := {p : Space n × ℝ // p.1 ∈ (K ∩ P(q,ρ)) \ N ∧ 0 < p.2 ∧ p.2 < 5ρ ∧
ρ₀(P(p.1,p.2)) ≤ (A+ε) p.2^k}` (a `Type`), with the **inner** balls `P(p.1, p.2/5)`: positive
radii bounded by `ρ`. Apply `h5` with `X = Space n` (separable: proper) to the inner family:
a countable `J` with pairwise disjoint inner balls such that every centre lies in
`P(z_j, 5·(r_j/5)) = P(z_j,r_j)` for some `j ∈ J`. Every `z ∈ (K ∩ P(q,ρ)) \ N` is a centre
(`fpack_exists_good_radius` with `δ = 5ρ`). Hence `P(q,ρ) ∩ K ⊆ N ∪ ⋃_{j ∈ J} P(z_j,r_j)` and, by countable
subadditivity (`measure_biUnion_le`, `J` countable),
`ρ₀(P(q,ρ) ∩ K) ≤ ∑'_{j ∈ J} ofReal ((A+ε) r_j^k) = ofReal ((A+ε) 5^k) · ∑'_{j ∈ J} (r_j/5)^k`
(`ENNReal.tsum_mul_left`), and `fpack_tsum_le_of_finite_packing` applied at `(q,ρ)` to the inner family indexed by `J`
(centres in `K ∩ P(q,ρ)`, radii `r_j/5 ∈ (0,ρ]`, disjoint) bounds the sum by
`ofReal (C_K ρ^k)`. Combine through `ENNReal.ofReal_mul` (all factors nonnegative). `A = 0`
and `C_K = 0` need no separate case. Only the inner balls must be disjoint; the outer balls
carry the mass bound.

It uses `fpack_exists_good_radius` and `fpack_tsum_le_of_finite_packing`.
`FivefoldSelectionStatement` is the first hypothesis. -/
theorem fpack_restrict_ball_le_add_of_fivefold
    (h5 : Characterization.FivefoldSelectionStatement) :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ K : Set (Space n), MeasurableSet K →
    ∀ R₀ C_K : ℝ, 0 < R₀ → 0 ≤ C_K →
    (∀ (q : Space n) (ρ : ℝ), 0 < ρ → ρ ≤ R₀ →
      ∀ (l : ℕ) (z : Fin l → Space n) (r : Fin l → ℝ),
        (∀ i, z i ∈ K ∩ Metric.ball q ρ) →
        (∀ i, 0 < r i ∧ r i ≤ ρ) →
        (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
        (∑ i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C_K * ρ ^ k)) →
    ∀ ρ₀ : Measure (Space n), IsFiniteMeasureOnCompacts ρ₀ → ρ₀.InnerRegular →
    ∀ A : ℝ, 0 ≤ A →
    (∀ᵐ z ∂ρ₀, z ∈ K → lowerDensity ρ₀ k z ≤ ENNReal.ofReal A) →
    ∀ (q : Space n) (ρ : ℝ), 0 < ρ → ρ ≤ R₀ →
    ∀ ε : ℝ, 0 < ε →
      ρ₀.restrict K (Metric.ball q ρ) ≤ ENNReal.ofReal (5 ^ k * C_K * (A + ε) * ρ ^ k) := by
  exact fpack_restrict_ball_le_add_of_fivefold_proof h5

end ParabolicRectifiability.Foundations
