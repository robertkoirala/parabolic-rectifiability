import ParabolicRectifiability.BetaP.Assembly.AssemblyStatements
import ParabolicRectifiability.Decomposition.SourceAssembly

/-! # The support bundle of the assembled decomposition, by finite summation

Proves `casm_supportBounds_proof : CasmSupportBoundsStatement`.

Proof (as for `familyDecomposition_of_compactSources`):
* `K_T` is closed in the compact `(⋃ A_T i) ∩ P̄(0,1)`, hence compact, and lies in `P̄(0,1)`;
* for an unavailable type every `A_T i ⊆ (D i).<type> = ∅`, so `K_T = ∅`;
* own-type covers pass from the typed pieces `(D i).<type>` to the subset `K_T` of their union
  (`HasHorizontalGraphCover.of_subset_iUnion`; the general-regular vertical analogue is the local
  helper `casm2_generalVerticalCover_of_subset_iUnion`, an instance of
  `exists_setNat_null_cover` with `GeneralRegularVerticalGraph.image`);
* `K_H ∪ K_V ⊆ ⋃ (K i).set`, so the carriers' metric content and finite packing bounds pass to
  `K_H ∪ K_V` with constant `c C_c ≤ C`; countable packing from finite partial sums;
* `H_P^k((K i).set) ≤ C_c` because `(K i).set ⊆ supp ν_i ⊆ P̄(center i, 1/64) ⊆ P(center i, 1)` and
  the carrier's content bound at radius `1`; summing over the `c` carriers gives `≤ c C_c ≤ C`.

Empty families (`c = 0`) and empty pieces need no case split; `C_c = 0` and `C = 0` are allowed.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- General-regular vertical covers with Hausdorff-null exceptions pass from a countable family
of sets to every subset of their union (the general-regular analogue of
`HasRegularVerticalGraphCover.of_subset_iUnion`). -/
theorem casm2_generalVerticalCover_of_subset_iUnion {n k : ℕ} {ε : ℝ} {ι : Type*}
    [Countable ι] {L : Set (Space n)} (K : ι → Set (Space n)) (hL : L ⊆ ⋃ i, K i)
    (hK : ∀ i, HasGeneralRegularVerticalGraphCover k (K i) ε) :
    HasGeneralRegularVerticalGraphCover k L ε :=
  exists_setNat_null_cover (hausdorffP n k)
    (GeneralRegularVerticalGraph.image (n := n) (k := k) (ε := ε)) K hL hK

/-- A carrier of a source supported in `P̄(c, 1/64)` has `H_P^k` measure at most `C · 1^k`: it lies
in `P(c, 1)`, where the carrier's local Hausdorff bound at radius one applies. -/
theorem casm2_carrier_hausdorff_le {n k : ℕ} {T : FamilyKind} {p M Cc : ℝ}
    {ν : Measure (Space n)} (K : PCarrier ν k T p M Cc) {c : Space n}
    (hc : ν.support ⊆ Metric.closedBall c (1 / 64)) :
    hausdorffP n k K.set ≤ ENNReal.ofReal (Cc * 1 ^ k) := by
  have hsub : K.set ⊆ Metric.ball c 1 := fun z hz =>
    Metric.closedBall_subset_ball (by norm_num) (hc (K.subset_support hz))
  have h := K.content.hausdorff c 1 one_pos le_rfl
  rwa [inter_eq_left.mpr hsub] at h

/-- The typed supports lie in the union of the carriers. -/
theorem casm2_union_subset_carriers {n k c : ℕ} {T : FamilyKind} {p M Cc : ℝ}
    {ν : Fin c → Measure (Space n)} (K : ∀ i, PCarrier (ν i) k T p M Cc)
    (D : ∀ i, TypedSplit k T (K i).set) {AH AV : Fin c → Set (Space n)}
    (hAHD : ∀ i, AH i ⊆ (D i).horizontal) (hAVD : ∀ i, AV i ⊆ (D i).vertical)
    {KH KV B : Set (Space n)} (hKH : KH ⊆ (⋃ i, AH i) ∩ B) (hKV : KV ⊆ (⋃ i, AV i) ∩ B) :
    KH ∪ KV ⊆ ⋃ i, (K i).set := by
  have hH : ∀ i, AH i ⊆ (K i).set := fun i =>
    (hAHD i).trans (subset_union_left.trans (D i).union_eq.subset)
  have hV : ∀ i, AV i ⊆ (K i).set := fun i =>
    (hAVD i).trans (subset_union_right.trans (D i).union_eq.subset)
  exact union_subset ((hKH.trans inter_subset_left).trans (iUnion_mono hH))
    ((hKV.trans inter_subset_left).trans (iUnion_mono hV))

/-- **Support bundle** (`CasmSupportBoundsStatement`): the support bundle of the closed
sets `K_H ⊆ (⋃ A_H i) ∩ P̄(0,1)`, `K_V ⊆ (⋃ A_V i) ∩ P̄(0,1)` at centre `0`, scale `1`, for every
constant `C ≥ c C_c`. -/
theorem casm_supportBounds_proof : CasmSupportBoundsStatement := by
  unfold CasmSupportBoundsStatement
  intro n k c T p M Cc ν center hCc hsupp K D AH AV hAHc hAVc hAHD hAVD KH KV hKHc hKVc hKH hKV
    C hC
  have hU : KH ∪ KV ⊆ ⋃ i, (K i).set := casm2_union_subset_carriers K D hAHD hAVD hKH hKV
  have hm : HasMetricContentBounds k C (KH ∪ KV) :=
    HasMetricContentBounds.of_subset_iUnion le_rfl hCc hC hU fun i => (K i).content
  have hp : HasFiniteBallPacking k C (KH ∪ KV) :=
    HasFiniteBallPacking.of_subset_iUnion le_rfl hCc hC hU fun i => (K i).packing
  have hHD : KH ⊆ ⋃ i, (D i).horizontal := (hKH.trans inter_subset_left).trans (iUnion_mono hAHD)
  have hVD : KV ⊆ ⋃ i, (D i).vertical := (hKV.trans inter_subset_left).trans (iUnion_mono hAVD)
  have h1 : (0 : ℝ) ≤ 1 ^ k := pow_nonneg zero_le_one k
  exact
    { horizontal_compact :=
        ((isCompact_iUnion hAHc).inter_right Metric.isClosed_closedBall).of_isClosed_subset
          hKHc hKH
      vertical_compact :=
        ((isCompact_iUnion hAVc).inter_right Metric.isClosed_closedBall).of_isClosed_subset
          hKVc hKV
      horizontal_subset := hKH.trans inter_subset_right
      vertical_subset := hKV.trans inter_subset_right
      horizontal_unavailable := fun h => eq_empty_of_subset_empty
        (hHD.trans (iUnion_subset fun i => ((D i).horizontal_unavailable h).subset))
      vertical_unavailable := fun h => eq_empty_of_subset_empty
        (hVD.trans (iUnion_subset fun i => ((D i).vertical_unavailable h).subset))
      horizontal_graphs := fun ε hε =>
        HasHorizontalGraphCover.of_subset_iUnion (fun i => (D i).horizontal) hHD
          fun i => (D i).horizontal_graphs ε hε
      vertical_graphs := fun ε hε =>
        casm2_generalVerticalCover_of_subset_iUnion (fun i => (D i).vertical) hVD
          fun i => (D i).vertical_graphs ε hε
      hausdorff_total :=
        calc hausdorffP n k (KH ∪ KV)
            ≤ ∑ i, hausdorffP n k (K i).set :=
              (measure_mono hU).trans (measure_iUnion_fintype_le _ _)
          _ ≤ ∑ _i : Fin c, ENNReal.ofReal (Cc * 1 ^ k) :=
              Finset.sum_le_sum fun i _ => casm2_carrier_hausdorff_le (K i) (hsupp i)
          _ ≤ ENNReal.ofReal (C * 1 ^ k) :=
              sum_fin_ofReal_le le_rfl (mul_nonneg hCc h1) (mul_mul_le_of_mul_le hC h1)
      hausdorff_local := fun q s hs hs1 => hm.hausdorff q s hs hs1
      separated := fun q s r hs hs1 hr hrs => hm.separated q s r hs hs1 hr hrs
      minkowski := fun r hr hr1 => by
        rw [one_pow, mul_one]
        exact hm.minkowski r hr hr1
      finite_packing := hp
      countable_packing := hp.countable }

end ParabolicRectifiability.BetaP
