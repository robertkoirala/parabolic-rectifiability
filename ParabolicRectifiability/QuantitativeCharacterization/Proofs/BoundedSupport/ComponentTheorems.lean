import ParabolicRectifiability.QuantitativeCharacterization.Statements.BoundedSupportComponents
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.BoundedSupport.SeparatedRootCover
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.BoundedSupport.BandCost
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.BoundedSupport.BoundedUnion

/-! # Bounded-support auxiliary statements: proofs

Each declaration below delegates to its proof, imported above.

* `dp2_separated_root_cover` (the bounded cover by a maximal separated family);
* `dp2_band_cost` (the cost of the declared-bad band);
* `dp2_bounded_union` (the union certificate with the declared-bad band).

The three statements are independent of one another. They are combined in
`dp2_exists_bounded_forward_approximants` with the local forward covering and with the
multiplicity, tail, typed-split and trace-carriage statements.
-/

set_option autoImplicit false

noncomputable section

namespace ParabolicRectifiability.QuantitativeCharacterization

/-- **A bounded cover by a maximal separated family** (`dp2_SeparatedRootCoverStatement`).
Fix `r_* = D_E/B` with `B` larger than all buffer constants. An `r_*/2`-separated family has
disjoint `r_*/4`-balls, so growth gives `N A⁻¹ (r_*/4)^k ≤ μ(P(b_0, 2D_E)) ≤ A (2D_E)^k`, hence
`N ≤ A² (8B)^k`.

Proof sketch.
1. Net: `Forward.PartitionEnergy.d1a_netExtension_proof : NetExtensionStatement` with
   `E = μ.support` (closed: `Measure.isClosed_support`), `s = r/2`, `Z₀ = ∅` gives a countable
   `Z ⊆ E`, `r/2`-separated (`r/2 ≤ dist z z'` for `z ≠ z'`), with every `x ∈ E` within `r/2 < r`
   of `Z`.
2. Counting: for every finite `P ⊆ Z`, the balls `P(z, r/4)`, `z ∈ P`, are pairwise disjoint
   (`Metric.ball_disjoint_ball`), each has `μ ≥ A⁻¹ (r/4)^k` (lower growth, `r/4 ≤ D_E`), and all
   lie in `P(z₀, 2D_E)` for any `z₀ ∈ P` (`Metric.dist_le_diam_of_mem`, `r/4 < D_E`), whose mass
   is `≤ A (2D_E)^k`. Hence `#P · A⁻¹ (r/4)^k ≤ A (2D_E)^k`, i.e. `#P ≤ A² (8 D_E/r)^k`
   (`measure_biUnion_finset`, open balls are Borel).
3. So `Z` is finite (an infinite `Z` has finite subsets of every size) with `#Z ≤ A² (8 D_E/r)^k`;
   enumerate it as `b : Fin N → Space n` (`Set.Finite.toFinset`, `Finset.equivFin`).
4. The edge cases need no care: `E = ∅` gives `N = 0`; `r ≤ D_E` forces `D_E > 0`.

The statement asks only for the finite cover and the cardinality bound; separation and maximality
are proof devices, not outputs. It is used in `dp2_bdd_large_root` at `r = r_* = D_E / B_loc`,
where `8 D_E / r_* = 8 B_loc`. -/
theorem dp2_separated_root_cover : dp2_SeparatedRootCoverStatement := by
  exact dp2_separated_root_cover_proof

/-- **The cost of the declared-bad band** (`dp2_BandCostStatement`). For `R ≥ r_*`, declaring
`r_* ≤ r < R` bad has extra cost at most `μ(E) log_+(R/r_*) ≤ C R^k`, since `D_E/r_*` is fixed.

Proof sketch.
1. `pointScaleMeasure μ (S ×ˢ Ico r R) = μ S * scaleMeasure (Ico r R)` by `Measure.prod_prod`
   (only `SFinite scaleMeasure` is needed; no hypothesis on `μ`).
2. `scaleMeasure (Ico r R) = ofReal (log (R/r))`: as `Foundations.bf1m45_scaleMeasure_Ioo` for
   `Ioo`, plus the null endpoint (`scaleMeasure_singleton`); or directly as
   `Forward.Coverage.d1fbad_scaleMeasure_Ico` does.
3. `μ S · log(R/r) ≤ Q r^k log(R/r) ≤ Q R^k`: with `x = R/r ≥ 1`, `log x ≤ x - 1 < x ≤ x^k`
   (`Real.log_le_sub_one_of_pos`, `le_self_pow₀`, `k ≥ 1`), so `r^k log x ≤ r^k x^k = R^k`.

It is used in `dp2_bdd_large_root` with `S = P(a,R) ∩ E`, `r = r_*`, `Q = A 2^k B_loc^k`
(`μ(E) ≤ μ(P(a, 2D_E)) ≤ A (2 B_loc r_*)^k`). -/
theorem dp2_band_cost : dp2_BandCostStatement := by
  exact dp2_band_cost_proof

/-- **The bounded union of root certificates** (`dp2_BoundedUnionStatement`). For `R ≥ r_*`, take
the union of the root certificates, restrict the regions to `P₀`, and declare `r_* ≤ r < R` bad.
Local packing survives the bounded union.

Proof sketch.
1. Choose `𝒞 j := (h j).some` (`Classical.choice`). Index: encode `Σ j : Fin N, (𝒞 j).index`
   into `ℕ` (e.g. `Nat.pair j i`; the index set is the range, `Equiv.ofInjective`). Reference
   `(𝒞 j).reference i` enlarged by `Reference.mono (L'.le) hL'L`
   (carrier, kind and measure unchanged, `Reference.carrier_mono`), centre and radius those of `𝒞 j`. Every model ball of every `𝒞 j`
   is retained; the statement asks only for existence and the radius-sum bound.
2. Borel assignment, reusing the first pieces of `Forward.PartitionEnergy` with
   `S = univ`, `ord := Fin.val`, `C j = P(b_j, r)`:
   `G_j = d1aassign_firstPiece univ Fin.val (fun j => Metric.ball (b j) r) j`
   `= P(b_j, r) \ ⋃_{l < j} P(b_l, r)`; `G_j ⊆ P(b_j, r)` (`d1aassign_firstPiece_subset`);
   pairwise disjoint (`d1aassign_firstPiece_disjoint` with
   `Set.injOn_of_injective Fin.val_injective`); `⋃_j G_j = ⋃_j P(b_j, r) ⊇ E`
   (`d1aassign_biUnion_firstPiece`); Borel (`d1aassign_firstPiece_measurable` with
   `Set.countable_univ` and open balls).
3. Regions: scale sets `𝒰_{(j,i)} = 𝒰^j_i ∩ ((G_j ∩ P(a,R)) ×ˢ univ)`; bad set
   `𝓑 = (⋃_j 𝓑_j ∩ ((G_j ∩ P(a,R)) ×ˢ univ)) ∪ ((P(a,R) ∩ E) ×ˢ Ico r R)`.
4. Fields. `ball_subset`: `P_i ⊆ P(b_j, L' r) ⊆ P(a, L R)` (`Metric.ball_subset_ball'`).
   `root_packing`: `Σ ≤ Σ_j ofReal (K' r^k) = ofReal (N K' r^k) ≤ ofReal (K R^k)`
   (`ENNReal.tsum_sigma`, `r ≤ R`, `K ≥ N K' ≥ 0`); this is also the stated radius-sum bound.
   `local_packing`: the same sum of the `N` local packings, `≤ N K' s^k ≤ K s^k`.
   `badSet_subset`, `scaleSet_subset`: `rootPairs μ (b_j) r ⊆ E × (0, r)`, `r ≤ R`.
   `bad_inter_scale_null`, `scale_inter_scale_null`: the `G_j` are disjoint, the band has radii
   `≥ r` while every `𝒰^j_i` has radii `< r`; what remains is inside `𝓑_j ∩ 𝒰^j_i` or
   `𝒰^j_i ∩ 𝒰^j_{i'}`. `cover_null`: a pair `(z, t)` of `rootPairs μ a R` with `t ≥ r` is in the
   band; with `t < r`, `z ∈ G_j` for some `j` (`E ⊆ ⋃_j P(b_j, r)`), so it lies in
   `rootPairs μ (b_j) r` and is either covered or in the null remainder of `𝒞 j`
   (`measure_iUnion_null`). `scaleSet_cover`: `L⁻¹ d ≤ L'⁻¹ d ≤ t` (`inv_anti₀`).
   `bad_bound`: `≤ Σ_j ofReal (K' r^k) + ofReal (K_b R^k) ≤ ofReal (K R^k)` (`measure_union_le`,
   `measure_iUnion_fintype_le`).
No measure-theoretic hypothesis on `μ` is needed (only subadditivity). -/
theorem dp2_bounded_union : dp2_BoundedUnionStatement := by
  exact dp2_bounded_union_proof

end ParabolicRectifiability.QuantitativeCharacterization
