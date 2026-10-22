import ParabolicRectifiability.QuantitativeCharacterization.Statements.TraceComponents
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Ambient.RootCovering
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.ReferenceBasic
import ParabolicRectifiability.Foundations.Proofs.SquareEnergyBounds

/-! # Trace carriage

Proof of `dp2_trace_carriage : dp2_TraceCarriageStatement`.

Fix a `(K,L)` regular mixed covering of the root `P(a,R)`, with bad set `𝓑`, scale sets `𝓤_i`,
model balls `P_i` and reference carriers `Γ_i`, and write `𝓑_z`, `𝓝_z` for the fibres over `z`
of `𝓑` and of the missed set `𝓝 = rootPairs \ (𝓑 ∪ ⋃_i 𝓤_i)`.

1. **Fubini on `bad_bound`** (`Measure.ae_measure_lt_top`): `𝓑` is Borel and
   `∬_𝓑 dμ dr/r ≤ K R^k < ∞`, so `scaleMeasure 𝓑_z < ∞` for `μ`-a.e. `z`.
2. **Fubini on `cover_null`** (`Measure.measure_prod_null`): `𝓝` is Borel (the index set is a
   subset of `ℕ`, and `damb_measurableSet_rootPairs`), so `scaleMeasure 𝓝_z = 0` for `μ`-a.e.
   `z`. Inner regularity makes `supp μ` conull (`Measure.measure_compl_support_of_innerRegular`).
3. **Distance floor** (`dp2_tc_floor`). Let `z ∈ P(a,R)` have finite multiplicity and lie on no
   trace `P_i ∩ Γ_i`. Each carrier is closed (`dp2_tc_isClosed_carrier`: a support,
   `ba1_vertical_basic_proof`, or `univ`) and nonempty (`ball_meets_carrier`), so
   `dist(z,Γ_i) > 0` for each of the finitely many `i` with `z ∈ P_i`. Hence there is `c > 0`
   with `(z,r) ∉ 𝓤_i` for every `i` and `0 < r < c` (`scaleSet_cover`:
   `z ∈ P_i` and `L⁻¹ dist(z,Γ_i) ≤ r`; `L ≥ 1` gives `L⁻¹ > 0`).
4. **Contradiction** (`dp2_tc_fibre_false`). If moreover `z ∈ supp μ`, then
   `(0, min c R) ⊆ 𝓑_z ∪ 𝓝_z`, while `scaleMeasure (0, min c R) = ∞`
   (`dp2_tc_scaleMeasure_Ioo_zero`, from `bf1m45_scaleMeasure_Ioo`); this contradicts
   `scaleMeasure 𝓑_z < ∞` and `scaleMeasure 𝓝_z = 0`.

So `μ`-a.e. point of `P(a,R)` lies on a trace. The hypothesis `IsFiniteMeasureOnCompacts μ` of the
statement is not used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- Every reference carrier is closed: the support of the horizontal reference measure, the image
of the vertical bi-Lipschitz embedding (`ba1_vertical_basic_proof`, which takes `1 ≤ L`), or
`univ` for the ambient reference. -/
theorem dp2_tc_isClosed_carrier {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (ρ : Reference n k L) :
    IsClosed ρ.carrier := by
  cases ρ with
  | horizontal H => exact (ba1_horizontal_basic_proof n k L hL H).2.1
  | vertical V => exact (ba1_vertical_basic_proof n k L hL V).2.1
  | ambient _ => exact isClosed_univ

/-- `scaleMeasure (0,c) = ∫_0^c dr/r = ∞` for `c > 0`: `(c e^{-x}, c) ⊆ (0,c)` has `dr/r`-mass `x`
for every `x ≥ 0` (`bf1m45_scaleMeasure_Ioo`). -/
theorem dp2_tc_scaleMeasure_Ioo_zero {c : ℝ} (hc : 0 < c) : scaleMeasure (Ioo 0 c) = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun x => ?_
  have hpos : 0 < c / Real.exp x := div_pos hc (Real.exp_pos _)
  have hle : c / Real.exp x ≤ c := div_le_self hc.le (Real.one_le_exp (NNReal.coe_nonneg x))
  calc (x : ℝ≥0∞) = ENNReal.ofReal (Real.log (c / (c / Real.exp x))) := by
        rw [div_div_cancel₀ hc.ne', Real.log_exp, ENNReal.ofReal_coe_nnreal]
    _ = scaleMeasure (Ioo (c / Real.exp x) c) := (bf1m45_scaleMeasure_Ioo hpos hle).symm
    _ ≤ scaleMeasure (Ioo 0 c) := measure_mono (Ioo_subset_Ioo_left hpos.le)

/-- The missed set `rootPairs \ (𝓑 ∪ ⋃_i 𝓤_i)` of a covering is Borel. -/
theorem dp2_tc_measurableSet_missed {n k : ℕ} {K L : ℝ} {μ : Measure (Space n)} {a : Space n}
    {R : ℝ} (𝒞 : RegularMixedCovering k K L μ a R) :
    MeasurableSet (rootPairs μ a R \ (𝒞.badSet ∪ ⋃ i, 𝒞.scaleSet i)) :=
  (damb_measurableSet_rootPairs μ a R).diff
    (𝒞.measurable_badSet.union (MeasurableSet.iUnion 𝒞.measurable_scaleSet))

/-- **Distance floor.** If `z` lies in only finitely many model balls and on no trace
`P_i ∩ Γ_i`, then there is `c > 0` such that no pair `(z,r)` with `0 < r < c` lies in a scale
set: membership in `𝓤_i` forces `z ∈ P_i` and `L⁻¹ dist(z,Γ_i) ≤ r`, and the finitely many
`dist(z,Γ_i)` with `z ∈ P_i` are positive (closed nonempty carriers not containing `z`). -/
theorem dp2_tc_floor {n k : ℕ} {K L : ℝ} {μ : Measure (Space n)} {a : Space n} {R : ℝ}
    (hL : 1 ≤ L) (𝒞 : RegularMixedCovering k K L μ a R) (z : Space n)
    (hfin : {i : 𝒞.index | z ∈ 𝒞.ball i}.Finite)
    (hz : z ∉ ⋃ i, 𝒞.ball i ∩ (𝒞.reference i).carrier) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → r < c → ∀ i, (z, r) ∉ 𝒞.scaleSet i := by
  have hpos : ∀ i ∈ {i : 𝒞.index | z ∈ 𝒞.ball i},
      ∀ᶠ r in nhds (0 : ℝ), r < L⁻¹ * Metric.infDist z (𝒞.reference i).carrier := by
    intro i hi
    have hne : ((𝒞.reference i).carrier).Nonempty :=
      (𝒞.ball_meets_carrier i).mono inter_subset_right
    have hzΓ : z ∉ (𝒞.reference i).carrier := fun h => hz (mem_iUnion.2 ⟨i, hi, h⟩)
    have hd : 0 < Metric.infDist z (𝒞.reference i).carrier :=
      ((dp2_tc_isClosed_carrier hL (𝒞.reference i)).notMem_iff_infDist_pos hne).1 hzΓ
    exact eventually_lt_nhds (mul_pos (inv_pos.2 (zero_lt_one.trans_le hL)) hd)
  have hev : ∀ᶠ r in nhds (0 : ℝ), ∀ i ∈ {i : 𝒞.index | z ∈ 𝒞.ball i},
      r < L⁻¹ * Metric.infDist z (𝒞.reference i).carrier :=
    (Filter.eventually_all_finite hfin).2 hpos
  obtain ⟨ε, hε, hεr⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun r hr0 hrε i hzr => ?_⟩
  have hmem := 𝒞.scaleSet_cover i hzr
  have hzi : i ∈ {i : 𝒞.index | z ∈ 𝒞.ball i} := hmem.1.2
  have hle : L⁻¹ * Metric.infDist z (𝒞.reference i).carrier ≤ r := hmem.2.1
  have hdist : dist r 0 < ε := by rwa [Real.dist_eq, sub_zero, abs_of_pos hr0]
  exact lt_irrefl r ((hεr hdist i hzi).trans_le hle)

/-- **The fibre contradiction.** A support point `z` of the root whose bad fibre has finite
`dr/r`-mass and whose missed fibre is null cannot have a scale floor `c > 0` below which no
scale set contains `(z,r)`: then `(0, min c R) ⊆ 𝓑_z ∪ 𝓝_z`, of infinite `dr/r`-mass. -/
theorem dp2_tc_fibre_false {n k : ℕ} {K L : ℝ} {μ : Measure (Space n)} {a : Space n} {R : ℝ}
    (𝒞 : RegularMixedCovering k K L μ a R) (z : Space n)
    (hz : z ∈ Metric.ball a R ∩ μ.support)
    (hB : scaleMeasure (Prod.mk z ⁻¹' 𝒞.badSet) < ∞)
    (hN : scaleMeasure (Prod.mk z ⁻¹' (rootPairs μ a R \ (𝒞.badSet ∪ ⋃ i, 𝒞.scaleSet i))) = 0)
    {c : ℝ} (hc : 0 < c) (hfloor : ∀ r : ℝ, 0 < r → r < c → ∀ i, (z, r) ∉ 𝒞.scaleSet i) :
    False := by
  have hR : 0 < R := dist_nonneg.trans_lt (Metric.mem_ball.1 hz.1)
  have hsub : Ioo 0 (min c R) ⊆ Prod.mk z ⁻¹' 𝒞.badSet ∪
      Prod.mk z ⁻¹' (rootPairs μ a R \ (𝒞.badSet ∪ ⋃ i, 𝒞.scaleSet i)) := by
    intro r hr
    by_cases hb : (z, r) ∈ 𝒞.badSet
    · exact Or.inl hb
    · refine Or.inr ⟨mk_mem_prod hz ⟨hr.1, hr.2.trans_le (min_le_right c R)⟩, ?_⟩
      rintro (h | h)
      · exact hb h
      · obtain ⟨i, hi⟩ := mem_iUnion.1 h
        exact hfloor r hr.1 (hr.2.trans_le (min_le_left c R)) i hi
  have hle : scaleMeasure (Ioo 0 (min c R)) ≤ scaleMeasure (Prod.mk z ⁻¹' 𝒞.badSet) +
      scaleMeasure (Prod.mk z ⁻¹' (rootPairs μ a R \ (𝒞.badSet ∪ ⋃ i, 𝒞.scaleSet i))) :=
    (measure_mono hsub).trans (measure_union_le _ _)
  rw [dp2_tc_scaleMeasure_Ioo_zero (lt_min hc hR), hN, add_zero] at hle
  exact hB.ne (top_le_iff.1 hle)

/-- **Trace carriage**, with the type `dp2_TraceCarriageStatement` of `dp2_trace_carriage`. -/
theorem dp2_trace_carriage_proof : dp2_TraceCarriageStatement := by
  intro n k K L hL μ _hμc hμr a R 𝒞 hmult
  have := hμr
  -- Step 1: Fubini on `bad_bound`; the bad fibre has finite `dr/r`-mass a.e.
  have hB : ∀ᵐ z ∂μ, scaleMeasure (Prod.mk z ⁻¹' 𝒞.badSet) < ∞ :=
    Measure.ae_measure_lt_top (μ := μ) (ν := scaleMeasure) 𝒞.measurable_badSet
      (𝒞.bad_bound.trans_lt ENNReal.ofReal_lt_top).ne
  -- Step 2: Fubini on `cover_null`; the missed fibre is null a.e.
  have hN : ∀ᵐ z ∂μ,
      scaleMeasure (Prod.mk z ⁻¹' (rootPairs μ a R \ (𝒞.badSet ∪ ⋃ i, 𝒞.scaleSet i))) = 0 := by
    have h := (Measure.measure_prod_null (μ := μ) (ν := scaleMeasure)
      (dp2_tc_measurableSet_missed 𝒞)).1 𝒞.cover_null
    filter_upwards [h] with z hz
    exact hz
  -- Steps 3-4 at every good point.
  have hgood : ∀ᵐ z ∂μ, z ∈ Metric.ball a R →
      z ∈ ⋃ i, 𝒞.ball i ∩ (𝒞.reference i).carrier := by
    filter_upwards [hmult, hB, hN,
      mem_ae_iff.2 (Measure.measure_compl_support_of_innerRegular (μ := μ))]
      with z h1 h2 h3 h4 hzR
    by_contra hzT
    obtain ⟨c, hc, hfloor⟩ :=
      dp2_tc_floor hL 𝒞 z (Set.encard_lt_top_iff.1 (h1 hzR)) hzT
    exact dp2_tc_fibre_false 𝒞 z ⟨hzR, h4⟩ h2 h3 hc hfloor
  refine measure_mono_null ?_ (ae_iff.1 hgood)
  intro z hz hz'
  exact hz.2 (hz' hz.1)

end ParabolicRectifiability.QuantitativeCharacterization
