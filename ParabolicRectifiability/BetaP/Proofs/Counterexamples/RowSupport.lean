import ParabolicRectifiability.BetaP.Proofs.Counterexamples.RowStatements
import ParabolicRectifiability.Metric.ProperSpace
import ParabolicRectifiability.Geometry.Neck.HorizontalReduction
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.BoundedGrowthRescale

/-! # Supporting facts for the `S_p` and `T_p` examples

Facts shared by the `S_p` and `T_p` row and failure arguments:

* `c2_eq_of_good_null`: in a nonnegative decomposition `μ = μ⁺ + μ_G` whose good part is carried
  by a `μ`-null set, the remainder is all of `μ`.
* `c2_quarter_basic`, `c2_quarter_carrier`: for a source on `Space 1` supported in `P(0,1)` with
  mass `1/2` whose countably regular carriers with Hausdorff-null residual are all null (the
  conclusion of `ExponentWitnessAboveCarrierStatement`), the measure is finite, lives on
  `P(0,1)`, and every decomposition of the `T_p` failures has remainder exactly `1/2` on `P(0,1)`.
* `c2_setLIntegral_Ioo_lt_top_of`: finiteness on `(0,b)` and on the annulus `(b,b')` gives
  finiteness on `(0,b')`.
* `c2_tpAbove_endpoint : C2TpAboveEndpointStatement`: the previous fact with the annulus bound
  `BetaPowAnnulusStatement` at `n = 1`, `k = 2`, mixed family.
* `c2_timeSlice_measure : C2TimeSliceMeasureStatement`: the time slice as a measure map, an
  adapter over `isometry_point_zero`.
* `c2_rescaled_mass : C2RescaledMassStatement`: normalized rescaling keeps the unit-ball mass, an
  adapter over `Foundations.fbgrowth_ball_eq_rescaled_proof`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- **Support: a good part carried by a null set vanishes.** If `μ = μ⁺ + μ_G`, `μ_G(Kᶜ) = 0` and
`μ(K) = 0`, then `μ⁺ = μ`. -/
theorem c2_eq_of_good_null {X : Type*} [MeasurableSpace X] {μ μplus μG : Measure X} {K : Set X}
    (hdec : μ = μplus + μG) (hG : μG Kᶜ = 0) (hK : μ K = 0) : μplus = μ := by
  have hGK : μG K = 0 := by
    refine le_antisymm ?_ zero_le
    calc μG K ≤ μplus K + μG K := le_add_self
      _ = μ K := by rw [hdec, Measure.add_apply]
      _ = 0 := hK
  have hG0 : μG = 0 := by
    rw [← Measure.measure_univ_eq_zero]
    refine le_antisymm ?_ zero_le
    calc μG univ ≤ μG K + μG Kᶜ := measure_univ_le_add_compl K
      _ = 0 := by rw [hGK, hG, add_zero]
  rw [hdec, hG0, add_zero]

/-- **Support: the quarter source lives on `P(0,1)`.** Support in `P(0,1)` and mass `1/2` give a
finite measure with `μ(P(0,1)ᶜ) = 0` and `μ(P(0,1)) = 1/2`. -/
theorem c2_quarter_basic {μ : Measure (Space 1)}
    (hsupp : μ.support ⊆ Metric.ball (point 0 0) 1) (hmass : μ univ = ENNReal.ofReal (1 / 2)) :
    IsFiniteMeasure μ ∧ μ (Metric.ball (point 0 0) 1)ᶜ = 0 ∧
      μ (Metric.ball (point 0 0) 1) = ENNReal.ofReal (1 / 2) := by
  have hc : μ (Metric.ball (point 0 0) 1)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hsupp) Measure.measure_compl_support
  refine ⟨⟨by rw [hmass]; exact ENNReal.ofReal_lt_top⟩, hc, ?_⟩
  rw [← hmass, ← measure_add_measure_compl
    (measurableSet_ball : MeasurableSet (Metric.ball (point 0 0 : Space 1) 1)), hc, add_zero]

/-- **Support: the remainder of a `T_p` failure decomposition is the full mass.** For the quarter
source (support in `P(0,1)`, mass `1/2`, every countably regular carrier with an `H_P^2`-null
residual null), every decomposition `μ = μ⁺ + μ_G` with `μ_G` carried by a set `F` covered modulo
`H_P^2` by countably many horizontal and general regular vertical graphs has
`μ⁺(P(0,1)) = 1/2`. -/
theorem c2_quarter_carrier {μ : Measure (Space 1)}
    (hsupp : μ.support ⊆ Metric.ball (point 0 0) 1) (hmass : μ univ = ENNReal.ofReal (1 / 2))
    (hcar : ∀ (I I' : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph 1 2 (εH i))
      (εV : I' → ℝ) (V : ∀ j, GeneralRegularVerticalGraph 1 2 (εV j)) (Z : Set (Space 1)),
      hausdorffP 1 2 Z = 0 → μ ((⋃ i, (H i).image) ∪ (⋃ j, (V j).image) ∪ Z) = 0)
    {μplus μG : Measure (Space 1)} {F : Set (Space 1)} (hdec : μ = μplus + μG)
    (hG : μG Fᶜ = 0)
    (hcov : ∃ (I J : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph 1 2 (εH i))
      (εV : J → ℝ) (V : ∀ j, GeneralRegularVerticalGraph 1 2 (εV j)),
      hausdorffP 1 2 (F \ ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)) = 0) :
    μplus (Metric.ball (point 0 0) 1) = ENNReal.ofReal (1 / 2) := by
  obtain ⟨I, J, εH, H, εV, V, hZ⟩ := hcov
  have hF : μ F = 0 := by
    refine measure_mono_null ?_ (hcar I J εH H εV V _ hZ)
    intro x hx
    by_cases h : x ∈ (⋃ i, (H i).image) ∪ ⋃ j, (V j).image
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  rw [c2_eq_of_good_null hdec hG hF]
  exact (c2_quarter_basic hsupp hmass).2.2

/-! ## Endpoint extension -/

/-- **Finiteness on an initial interval from finiteness on an annulus.** Finiteness on `(0,b)`
and on the annulus `(b,b')` gives finiteness on `(0,b')`; compare `setLIntegral_Ioo_lt_top_of`. -/
theorem c2_setLIntegral_Ioo_lt_top_of {f : ℝ → ℝ≥0∞} {b b' : ℝ} (hbb' : b ≤ b')
    (h0 : ∫⁻ r in Ioo 0 b, f r ∂scaleMeasure < ⊤)
    (hann : b < b' → ∫⁻ r in Ioo b b', f r ∂scaleMeasure < ⊤) :
    ∫⁻ r in Ioo 0 b', f r ∂scaleMeasure < ⊤ := by
  rcases hbb'.eq_or_lt with h | h
  · subst h
    exact h0
  · have hsub : Ioo 0 b' ⊆ Ioo 0 b ∪ ({b} ∪ Ioo b b') := by
      intro r hr
      rcases lt_trichotomy r b with h1 | h1 | h1
      · exact Or.inl ⟨hr.1, h1⟩
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr ⟨h1, hr.2⟩)
    calc ∫⁻ r in Ioo 0 b', f r ∂scaleMeasure
        ≤ ∫⁻ r in Ioo 0 b ∪ ({b} ∪ Ioo b b'), f r ∂scaleMeasure := lintegral_mono_set hsub
      _ ≤ ∫⁻ r in Ioo 0 b, f r ∂scaleMeasure +
            (∫⁻ r in ({b} : Set ℝ), f r ∂scaleMeasure + ∫⁻ r in Ioo b b', f r ∂scaleMeasure) :=
          (lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_union_le _ _ _))
      _ < ⊤ := by
          rw [Measure.restrict_eq_zero.mpr (scaleMeasure_singleton b), lintegral_zero_measure,
            zero_add]
          exact ENNReal.add_lt_top.mpr ⟨h0, hann h⟩

/-- **Endpoint extension for `T_p`**: `T_p^2(z) < ∞` gives `T_p^a(z) < ∞` at every endpoint
`a > 0`, `n = 1`, `k = 2`, mixed family, from `BetaPowAnnulusStatement` (hypothesis) and the
previous lemma. For `a ≤ 2` this is monotonicity; for `a > 2` the annulus `(2,a)` is covered by
`BetaPowAnnulusStatement`. -/
theorem c2_tpAbove_endpoint : C2TpAboveEndpointStatement := by
  intro hA μ hμ hreg p hp z a ha h2
  rcases le_total a 2 with h | h
  · exact (lintegral_mono_set (Ioo_subset_Ioo_right h)).trans_lt h2
  · exact c2_setLIntegral_Ioo_lt_top_of h h2 fun hlt =>
      (hA 1 le_rfl 2 (by norm_num) (by norm_num) .mixed
        (AdmissibleModel.nonempty_of_range le_rfl (by norm_num) (by norm_num))
        μ hμ hreg p hp z 2 a two_pos hlt).2

/-! ## Slice and rescaling adapters -/

/-- **The time slice as a measure map**: `timeSlice` is a measurable embedding and
`(ι_#ν)(P(ιx, r)) = ν(B(x, r))` for every measure, centre and real radius. Adapter over
`isometry_point_zero` (`timeSlice` is definitionally `point · 0`). -/
theorem c2_timeSlice_measure : C2TimeSliceMeasureStatement := by
  have hiso : Isometry timeSlice := isometry_point_zero
  have hme : MeasurableEmbedding timeSlice := hiso.isClosedEmbedding.measurableEmbedding
  refine ⟨hme, fun ν x r => ?_⟩
  rw [hme.map_apply]
  congr 1
  ext y
  simp only [mem_preimage, Metric.mem_ball, hiso.dist_eq]

/-- **Rescaled mass**: `ν(P(q,R)) ≥ c R^k` gives `rescaledSource ν k q R hR (P(0,1)) ≥ c`.
Adapter over `Foundations.fbgrowth_ball_eq_rescaled_proof`, cancelling the positive finite factor
`R^k` with `ENNReal.mul_le_mul_iff_right`. -/
theorem c2_rescaled_mass : C2RescaledMassStatement := by
  intro n k ν q R hR c hc h
  have h0 := fbgrowth_ball_eq_rescaled_proof ν k q R hR
  have hpos : ENNReal.ofReal R ^ k ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hR).ne'
  have hfin : ENNReal.ofReal R ^ k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have h1 : ENNReal.ofReal (c * R ^ k) = ENNReal.ofReal R ^ k * ENNReal.ofReal c := by
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_pow hR.le, mul_comm]
  rw [h0, h1] at h
  exact (ENNReal.mul_le_mul_iff_right hpos hfin).mp h

end ParabolicRectifiability.BetaP
