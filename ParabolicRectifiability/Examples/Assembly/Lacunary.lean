import ParabolicRectifiability.Examples.Assembly.IntermediateStatements
import ParabolicRectifiability.Characterization.Statements.Branches
import ParabolicRectifiability.Foundations.Statements.Measurability
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import ParabolicRectifiability.Examples.Proofs.Lacunary.Support

/-! # Proof of the lacunary examples

The lacunary examples are assembled from the intermediate statements for the examples
(`lacunary_estimates_bundle`, `lacunarySource_finite_innerRegular_ac`, …) and two results
taken as hypotheses (implication form):
* `Characterization.GraphSourceStatement` (the graph-source theorem);
* `Foundations.EnergyTwoStatement` (the compatibility `T_2 = S` of the beta-`p` energies).

Main theorems:
* `lacunary_convergence_skeleton : LacunaryConvergenceStatement`;
* `lacunary_estimates_skeleton : LacunaryEstimatesStatement`;
* `nonregular_of_providers : GraphSourceStatement → EnergyTwoStatement → NonregularStatement`;
* `exponent_witnesses_of_providers :
    GraphSourceStatement → EnergyTwoStatement → ExponentWitnessesStatement`.

The proof of the nonregular example runs as follows: the
amplitudes `j^{-1/2}` tend to zero, lie in `ℓ^p` for `p > 2` and not in `ℓ²`; the lacunary
estimates give the quantitative claims; a regular graph `G` with `ν_J(G) > 0` gives a
positive restricted source `ν_E` carried by `G`, finite Radon and `≪ H_P²`, for which the
graph-source theorem gives finite vertical square on `G` up to an `H_P²`-null set, against the
restriction-stable divergence.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations ParabolicRectifiability.Characterization

/-! ## Convergence and estimates -/

/-- Convergence of the lacunary primitive, from `lacunary_series_convergence`. -/
theorem lacunary_convergence_skeleton : LacunaryConvergenceStatement :=
  lacunary_series_convergence

/-- The lacunary graph estimates, from `lacunary_estimates_bundle`. -/
theorem lacunary_estimates_skeleton : LacunaryEstimatesStatement :=
  lacunary_estimates_bundle

/-! ## Elementary facts -/

/-- The isometry clause makes the graph map continuous (indeed `1/2`-Hölder). -/
theorem continuous_lacunaryGraphMap_of_isometry {ε : ℝ} {a : ℕ → ℝ} {N : ℕ → ℕ}
    (h : ∀ t s : ℝ,
      dist (lacunaryGraphMap ε a N t) (lacunaryGraphMap ε a N s) = Real.sqrt |t - s|) :
    Continuous (lacunaryGraphMap ε a N) := by
  rw [Metric.continuous_iff]
  intro t δ hδ
  refine ⟨δ ^ 2, by positivity, fun s hs => ?_⟩
  rw [h s t]
  rw [Real.dist_eq] at hs
  calc Real.sqrt |s - t| < Real.sqrt (δ ^ 2) := Real.sqrt_lt_sqrt (abs_nonneg _) hs
    _ = δ := Real.sqrt_sq hδ.le

/-- The total mass of a restricted source is the Lebesgue measure of its parameter set. -/
theorem lacunarySource_univ {ε : ℝ} {a : ℕ → ℝ} {N : ℕ → ℕ}
    (hF : Measurable (lacunaryGraphMap ε a N)) (E : Set ℝ) :
    lacunarySource ε a N E univ = volume E := by
  exact ParabolicRectifiability.Examples.e2_lacunarySource_univ hF E

/-- A restricted source vanishes off the image of its parameter set, when that image is
measurable. -/
theorem lacunarySource_compl_image {ε : ℝ} {a : ℕ → ℝ} {N : ℕ → ℕ}
    (hF : Measurable (lacunaryGraphMap ε a N)) {E : Set ℝ}
    (hc : MeasurableSet (lacunaryGraphMap ε a N '' E)) :
    lacunarySource ε a N E (lacunaryGraphMap ε a N '' E)ᶜ = 0 := by
  rw [lacunarySource, Measure.map_apply hF hc.compl, Measure.restrict_apply (hF hc.compl)]
  convert measure_empty (μ := (volume : Measure ℝ))
  ext t
  simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
    not_and]
  exact fun h ht => h (mem_image_of_mem _ ht)

/-- The mixed natural beta is at most the vertical one: every vertical model is a mixed
model. -/
theorem betaSq_mixed_le_vertical {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n)
    (r : ℝ) : betaSq μ k .mixed z r ≤ betaSq μ k .vertical z r := by
  by_cases hr : 0 < r
  · rw [betaSq_of_pos _ _ _ _ hr, betaSq_of_pos _ _ _ _ hr]
    exact mul_le_mul_right
      (le_iInf fun V => iInf_le_of_le (Sum.inr V : AdmissibleModel n k) le_rfl) _
  · simp [betaSq, hr]

/-- The mixed square function is at most the vertical one. -/
theorem squareEnergy_mixed_le_vertical {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (R : ℝ)
    (z : Space n) : squareEnergy μ k .mixed R z ≤ squareEnergy μ k .vertical R z :=
  lintegral_mono fun r => betaSq_mixed_le_vertical μ k z r

/-- At `n = 1`, `k = 2` there is no horizontal graph: its direction would have rank `2` in
`ℝ¹`. -/
theorem horizontalGraph_one_two_elim {ε : ℝ} (H : HorizontalGraph 1 2 ε) : False := by
  have h := Submodule.finrank_le H.direction
  rw [H.rank_eq, finrank_euclideanSpace_fin] at h
  omega

/-- The amplitudes `j^{-1/2}` tend to zero. -/
theorem tendsto_nonregularAmplitude : Tendsto nonregularAmplitude atTop (𝓝 0) := by
  unfold nonregularAmplitude
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))

/-- The amplitudes `j^{-1/2}` are not in `ℓ²`: every tail of `Σ a_j²` is infinite. -/
theorem tsum_nonregularAmplitude_sq_tail_eq_top (j₀ : ℕ) :
    ∑' j, ENNReal.ofReal (nonregularAmplitude (j + j₀) ^ (2 : ℝ)) = ⊤ := by
  by_contra h
  have hs := ENNReal.summable_toReal h
  have heq : ∀ j : ℕ, (ENNReal.ofReal (nonregularAmplitude (j + j₀) ^ (2 : ℝ))).toReal =
      1 / (((j + (j₀ + 1) : ℕ)) : ℝ) := by
    intro j
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (by unfold nonregularAmplitude; positivity) _),
      Real.rpow_two, nonregularAmplitude, inv_pow, Real.sq_sqrt (by positivity), one_div]
    congr 1
    push_cast
    ring
  simp only [heq] at hs
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun m : ℕ => 1 / (m : ℝ)) (j₀ + 1)).mp hs)

/-- The amplitudes `j^{-1/2}` are in `ℓ^p` for `p > 2`. -/
theorem summable_nonregularAmplitude_rpow {p : ℝ} (hp : 2 < p) :
    Summable (fun j => nonregularAmplitude j ^ p) := by
  have hs0 : Summable (fun m : ℕ => ((m : ℝ) ^ (p / 2))⁻¹) :=
    Real.summable_nat_rpow_inv.2 (by linarith)
  have hs1 : Summable (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ (p / 2))⁻¹) :=
    (summable_nat_add_iff 1).2 hs0
  refine hs1.congr fun j => ?_
  unfold nonregularAmplitude
  push_cast
  rw [Real.inv_rpow (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity),
    show (1 / 2 : ℝ) * p = p / 2 by ring]

theorem nonregularAmplitude_rpow_nonneg (p : ℝ) (j : ℕ) : 0 ≤ nonregularAmplitude j ^ p :=
  Real.rpow_nonneg (by unfold nonregularAmplitude; positivity) p

/-- The arithmetic of the `p > 2` bound: `C ε^p Σ_j a_j^p ≤ C (S+1) ε^p` with
`S = Σ_j a_j^p`. -/
theorem upper_bound_nonregular {p C ε : ℝ} (hp : 2 < p) (hC : 0 < C) (hε : 0 < ε)
    {X : ℝ≥0∞}
    (hX : X ≤ ENNReal.ofReal (C * ε ^ p) * ∑' j, ENNReal.ofReal (nonregularAmplitude j ^ p)) :
    X ≤ ENNReal.ofReal (C * ((∑' j, nonregularAmplitude j ^ p) + 1) * ε ^ p) := by
  have hS0 : 0 ≤ ∑' j, nonregularAmplitude j ^ p :=
    tsum_nonneg (nonregularAmplitude_rpow_nonneg p)
  have hεp : 0 ≤ ε ^ p := Real.rpow_nonneg hε.le p
  rw [← ENNReal.ofReal_tsum_of_nonneg (nonregularAmplitude_rpow_nonneg p)
      (summable_nonregularAmplitude_rpow hp),
    ← ENNReal.ofReal_mul (mul_nonneg hC.le hεp)] at hX
  refine hX.trans (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [mul_nonneg hC.le hεp]

/-! ## Restriction-stable divergence of the square function at `a_j = j^{-1/2}` -/

/-- A lower bound of the form of the restriction-stable estimate at `q = 2` forces an infinite
square function, by `Σ_{j ≥ j₀} a_j² = ∞` and `T_2 = S`. -/
theorem squareEnergy_eq_top_of_tail (hE2 : EnergyTwoStatement) {ε : ℝ} (hε : 0 < ε)
    {c : ℝ → ℝ} (hc : ∀ q : ℝ, 0 < q → 0 < c q) {ν : Measure (Space 1)} {R : ℝ} (hR : 0 < R)
    {z : Space 1} (j₀ : ℕ)
    (h : ENNReal.ofReal (c 2 * ε ^ (2 : ℝ)) *
        ∑' j, ENNReal.ofReal (nonregularAmplitude (j + j₀) ^ (2 : ℝ)) ≤
      energyT ν 2 .mixed 2 R z) :
    squareEnergy ν 2 .mixed R z = ⊤ := by
  rw [tsum_nonregularAmplitude_sq_tail_eq_top, ENNReal.mul_top
    (ENNReal.ofReal_pos.2 (mul_pos (hc 2 two_pos) (Real.rpow_pos_of_pos hε 2))).ne',
    top_le_iff] at h
  rw [← (hE2 1 le_rfl 2 (by norm_num) (by norm_num) .mixed ν R hR z).2, h]

/-- Nonregular example: `S^R_{2,ν_E} = ∞` `ν_E`-almost everywhere for every measurable
`E ⊆ J` and `R > 0`, from the restriction-stable lower bound at Lebesgue density points. -/
theorem lacunarySource_ae_squareEnergy_eq_top (hest : LacunaryEstimatesStatement)
    (hE2 : EnergyTwoStatement) {ε : ℝ} {N : ℕ → ℕ} (hε : 0 < ε) (hε' : ε ≤ 3 / 16)
    (hdata : IsLacunaryData nonregularAmplitude N) {E : Set ℝ}
    (hE : NullMeasurableSet E volume) (hEJ : E ⊆ lacunaryInterval) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ z ∂(lacunarySource ε nonregularAmplitude N E),
      squareEnergy (lacunarySource ε nonregularAmplitude N E) 2 .mixed R z = ⊤ := by
  obtain ⟨hiso, -, -, -, -, -, ⟨c, hc, hlow⟩, -⟩ := hest
  have hF : Measurable (lacunaryGraphMap ε nonregularAmplitude N) :=
    (continuous_lacunaryGraphMap_of_isometry (hiso ε _ N hε hε' hdata)).measurable
  obtain ⟨hfin, -, -⟩ :=
    lacunarySource_finite_innerRegular_ac ε _ N hε hε' hdata E hE hEJ
  have hmeas : MeasurableSet
      {z | squareEnergy (lacunarySource ε nonregularAmplitude N E) 2 .mixed R z = ⊤} :=
    measurableSet_eq_fun (measurable_squareEnergy _ 2 .mixed R) measurable_const
  refine (ae_map_iff (μ := volume.restrict E) hF.aemeasurable hmeas).2 ?_
  have hne : ∀ b : ℝ, ∀ᵐ t ∂(volume.restrict E), t ≠ b := fun b =>
    ae_restrict_of_ae (ae_iff.2 (by simp))
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume E, ae_restrict_mem₀ hE,
    hne (-1), hne 1] with t hdens htE h1 h2
  have htJ := hEJ htE
  have ht : t ∈ Ioo (-1 : ℝ) 1 := ⟨lt_of_le_of_ne htJ.1 (Ne.symm h1), lt_of_le_of_ne htJ.2 h2⟩
  obtain ⟨j₀, hj₀⟩ := (hlow ε _ N hε hε' hdata).1 E hE hEJ t ⟨htE, ht⟩ hdens R hR
  exact squareEnergy_eq_top_of_tail hE2 hε hc hR j₀ (hj₀ 2 two_pos)

/-! ## The graph-source contradiction -/

/-- Nonregular example: for every measurable
`E₀ ⊆ J`, every full general regular vertical graph `G` of `Space 1` in dimension `2`, of any
norm, has `ν_{E₀}(G) = 0`. This is where the graph-source theorem enters. -/
theorem lacunarySource_graph_image_eq_zero (hGS : GraphSourceStatement)
    (hest : LacunaryEstimatesStatement) (hE2 : EnergyTwoStatement) {ε : ℝ} {N : ℕ → ℕ}
    (hε : 0 < ε) (hε' : ε ≤ 3 / 16) (hdata : IsLacunaryData nonregularAmplitude N)
    {E₀ : Set ℝ} (hE₀ : NullMeasurableSet E₀ volume) (hE₀J : E₀ ⊆ lacunaryInterval)
    (η : ℝ) (G : GeneralRegularVerticalGraph 1 2 η) :
    lacunarySource ε nonregularAmplitude N E₀ G.image = 0 := by
  obtain ⟨E, hE, hEE₀, hmass, hcarr⟩ :=
    exists_restriction_carried_by_graph ε _ N hε hε' hdata E₀ hE₀ hE₀J η G
  have hEJ : E ⊆ lacunaryInterval := hEE₀.trans hE₀J
  obtain ⟨hfin, hreg, hac⟩ :=
    lacunarySource_finite_innerRegular_ac ε _ N hε hε' hdata E hE hEJ
  have hgs := (hGS 1 le_rfl 2 (by norm_num) (by norm_num)).2 η G
    (lacunarySource ε nonregularAmplitude N E) inferInstance hreg 1 one_pos
  have h1 := hac hgs
  have hdiv := lacunarySource_ae_squareEnergy_eq_top hest hE2 hε hε' hdata hE hEJ one_pos
  have hv : ∀ᵐ z ∂(lacunarySource ε nonregularAmplitude N E),
      squareEnergy (lacunarySource ε nonregularAmplitude N E) 2 .vertical 1 z = ⊤ :=
    hdiv.mono fun z hz => top_le_iff.1 (hz ▸ squareEnergy_mixed_le_vertical _ 2 1 z)
  have h2 := ae_iff.1 hv
  rw [← hmass]
  refine measure_mono_null (fun z _ => ?_) (measure_union_null (measure_union_null hcarr h1) h2)
  by_cases hz : z ∈ G.image
  · by_cases hs : squareEnergy (lacunarySource ε nonregularAmplitude N E) 2 .vertical 1 z = ⊤
    · exact Or.inl (Or.inr ⟨hz, hs⟩)
    · exact Or.inr hs
  · exact Or.inl (Or.inl hz)

/-- Countable unions of regular graphs (horizontal subset graphs and full general regular
vertical graphs, each of its own norm) are `ν_{E₀}`-null for measurable `E₀ ⊆ J`. -/
theorem lacunarySource_regular_carrier_eq_zero (hGS : GraphSourceStatement)
    (hest : LacunaryEstimatesStatement) (hE2 : EnergyTwoStatement) {ε : ℝ} {N : ℕ → ℕ}
    (hε : 0 < ε) (hε' : ε ≤ 3 / 16) (hdata : IsLacunaryData nonregularAmplitude N)
    {E₀ : Set ℝ} (hE₀ : NullMeasurableSet E₀ volume) (hE₀J : E₀ ⊆ lacunaryInterval)
    (I I' : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph 1 2 (εH i))
    (εV : I' → ℝ) (V : ∀ j, GeneralRegularVerticalGraph 1 2 (εV j)) :
    lacunarySource ε nonregularAmplitude N E₀ ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image) = 0 :=
  measure_union_null (measure_iUnion_null fun i => (horizontalGraph_one_two_elim (H i)).elim)
    (measure_iUnion_null fun j =>
      lacunarySource_graph_image_eq_zero hGS hest hE2 hε hε' hdata hE₀ hE₀J _ (V j))

/-! ## The nonregular example -/

/-- The nonregular example, qualitative part, from the lacunary estimates, the two
restricted-source statements, the graph-source theorem and the `p = 2` compatibility
`T_2 = S`. -/
theorem nonregular_qualitative_of_providers (hGS : GraphSourceStatement)
    (hE2 : EnergyTwoStatement) : NonregularQualitativeStatement := by
  intro ε N hε hε' hdata
  have hest := lacunary_estimates_bundle
  obtain ⟨hiso, -, ⟨cH, hcH, hHaus⟩, -, -, -, ⟨c, hc, hlow⟩, hsmall⟩ := hest
  have hFc := continuous_lacunaryGraphMap_of_isometry (hiso ε _ N hε hε' hdata)
  have hF := hFc.measurable
  have hJ : NullMeasurableSet lacunaryInterval volume := measurableSet_Icc.nullMeasurableSet
  have hcpt : IsCompact (lacunaryGraphMap ε nonregularAmplitude N '' lacunaryInterval) :=
    isCompact_Icc.image hFc
  have hvolJ : volume lacunaryInterval = ENNReal.ofReal 2 := by
    rw [lacunaryInterval, Real.volume_Icc]; norm_num
  have hHJ := hHaus ε _ N hε hε' hdata lacunaryInterval hJ subset_rfl
  obtain ⟨-, -, hac⟩ :=
    lacunarySource_finite_innerRegular_ac ε _ N hε hε' hdata lacunaryInterval hJ subset_rfl
  have hmassJ : lacunarySource ε nonregularAmplitude N lacunaryInterval univ ≠ 0 := by
    rw [lacunarySource_univ hF, hvolJ]; exact (ENNReal.ofReal_pos.2 two_pos).ne'
  have hoff := lacunarySource_compl_image hF hcpt.isClosed.measurableSet
  have hcarrier := lacunarySource_regular_carrier_eq_zero hGS lacunary_estimates_bundle hE2
    hε hε' hdata hJ subset_rfl
  refine ⟨hcpt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hHJ, hvolJ]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hcH).ne' (ENNReal.ofReal_pos.2 two_pos).ne'
  · rw [hHJ, hvolJ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · intro η hη
    obtain ⟨m, G, hcov⟩ := hsmall ε _ N hε hε' hdata tendsto_nonregularAmplitude η hη
    refine ⟨∅, {j | j < m}, fun i => (Set.notMem_empty _ i.2).elim,
      fun j => G ⟨j.1, j.2⟩, ?_⟩
    rw [sdiff_eq_empty.2 ?_, measure_empty]
    intro z hz
    obtain ⟨ℓ, hℓ⟩ := mem_iUnion.1 (hcov hz)
    exact Or.inr (mem_iUnion.2 ⟨⟨ℓ.1, ℓ.2⟩, hℓ⟩)
  · intro t ht R hR
    obtain ⟨j₀, hj₀⟩ := (hlow ε _ N hε hε' hdata).2 t ht R hR
    exact squareEnergy_eq_top_of_tail hE2 hε hc hR j₀ (hj₀ 2 two_pos)
  · intro E hE hEJ _ R hR
    exact lacunarySource_ae_squareEnergy_eq_top lacunary_estimates_bundle hE2 hε hε' hdata hE
      hEJ hR
  · intro η G
    exact lacunarySource_graph_image_eq_zero hGS lacunary_estimates_bundle hE2 hε hε' hdata hJ
      subset_rfl η G
  · rintro ⟨I, I', εH, H, εV, V, hnull⟩
    apply hmassJ
    refine measure_mono_null (fun z _ => ?_) (measure_union_null (measure_union_null hoff
      (hac hnull)) (hcarrier I I' εH H εV V))
    by_cases h1 : z ∈ lacunaryGraphMap ε nonregularAmplitude N '' lacunaryInterval
    · by_cases h2 : z ∈ (⋃ i, (H i).image) ∪ ⋃ j, (V j).image
      · exact Or.inr h2
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact Or.inl (Or.inl h1)
  · rintro ⟨-, I, I', εH, H, εV, V, hcarr⟩
    apply hmassJ
    refine measure_mono_null (fun z _ => ?_)
      (measure_union_null hcarr (hcarrier I I' εH H εV V))
    by_cases h2 : z ∈ (⋃ i, (H i).image) ∪ ⋃ j, (V j).image
    · exact Or.inr h2
    · exact Or.inl h2

/-- The nonregular example, the `T_p` bound for `p > 2`: the upper
lacunary estimate with `q = p` and `Σ_j j^{-p/2} < ∞`. -/
theorem nonregular_upper_energy_skeleton : NonregularUpperEnergyStatement := by
  intro p hp
  obtain ⟨-, -, -, -, -, hup, -, -⟩ := lacunary_estimates_bundle
  obtain ⟨C, hC, hupC⟩ := hup p (by linarith)
  have hS0 : 0 ≤ ∑' j, nonregularAmplitude j ^ p :=
    tsum_nonneg (nonregularAmplitude_rpow_nonneg p)
  refine ⟨C * ((∑' j, nonregularAmplitude j ^ p) + 1), mul_pos hC (by linarith), ?_⟩
  intro ε N hε hε' hdata t
  exact upper_bound_nonregular hp hC hε
    (hupC ε _ N hε hε' hdata lacunaryInterval measurableSet_Icc.nullMeasurableSet subset_rfl t)

/-- **The nonregular example**, from the graph-source theorem and `T_2 = S`. -/
theorem nonregular_of_providers :
    GraphSourceStatement → EnergyTwoStatement → NonregularStatement := fun hGS hE2 =>
  ⟨nonregular_qualitative_of_providers hGS hE2, nonregular_upper_energy_skeleton⟩

/-! ## The exponent witnesses -/

/-- The exponent witness above `2`, exponent-free part: support in `P(0,1)`, mass `1/2`,
and vanishing on countably regular carriers with Hausdorff-null residuals. -/
theorem exponent_witness_above_carrier_of_providers (hGS : GraphSourceStatement)
    (hE2 : EnergyTwoStatement) : ExponentWitnessAboveCarrierStatement := by
  intro ε N hε hε' hdata
  obtain ⟨hiso, -, -, -, -, -, -, -⟩ := lacunary_estimates_bundle
  have hFc := continuous_lacunaryGraphMap_of_isometry (hiso ε _ N hε hε' hdata)
  have hF := hFc.measurable
  have hQ : NullMeasurableSet (Icc (-1 / 4 : ℝ) (1 / 4)) volume :=
    measurableSet_Icc.nullMeasurableSet
  have hQJ : Icc (-1 / 4 : ℝ) (1 / 4) ⊆ lacunaryInterval :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  have hcpt : IsCompact (lacunaryGraphMap ε nonregularAmplitude N '' Icc (-1 / 4) (1 / 4)) :=
    isCompact_Icc.image hFc
  obtain ⟨-, -, hac⟩ := lacunarySource_finite_innerRegular_ac ε _ N hε hε' hdata _ hQ hQJ
  refine ⟨?_, ?_, ?_⟩
  · refine (Measure.support_subset_of_isClosed hcpt.isClosed
      (mem_ae_iff.2 (lacunarySource_compl_image hF hcpt.isClosed.measurableSet))).trans ?_
    rintro _ ⟨t, ht, rfl⟩
    exact lacunaryGraphMap_mem_ball_of_quarter ε _ N hε hε' hdata t ht
  · rw [lacunarySource_univ hF, Real.volume_Icc]
    norm_num
  · intro I I' εH H εV V Z hZ
    exact measure_union_null
      (lacunarySource_regular_carrier_eq_zero hGS lacunary_estimates_bundle hE2 hε hε' hdata
        hQ hQJ I I' εH H εV V) (hac hZ)

/-- The exponent witness above `2`, energy part: the supremum and integral bounds from the
upper lacunary estimate with `q = p`, the mass `1/2`, and the positive-energy statement
`lintegral_energyT_quarter_pos`. -/
theorem exponent_witness_above_energy_skeleton : ExponentWitnessAboveEnergyStatement := by
  intro p hp
  obtain ⟨hiso, -, -, -, -, hup, -, -⟩ := lacunary_estimates_bundle
  obtain ⟨C, hC, hupC⟩ := hup p (by linarith)
  have hS0 : 0 ≤ ∑' j, nonregularAmplitude j ^ p :=
    tsum_nonneg (nonregularAmplitude_rpow_nonneg p)
  refine ⟨C * ((∑' j, nonregularAmplitude j ^ p) + 1), mul_pos hC (by linarith), ?_⟩
  intro ε N hε hε' hdata
  have hFc := continuous_lacunaryGraphMap_of_isometry (hiso ε _ N hε hε' hdata)
  have hF := hFc.measurable
  have hQ : NullMeasurableSet (Icc (-1 / 4 : ℝ) (1 / 4)) volume :=
    measurableSet_Icc.nullMeasurableSet
  have hQJ : Icc (-1 / 4 : ℝ) (1 / 4) ⊆ lacunaryInterval :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  have hcpt : IsCompact (lacunaryGraphMap ε nonregularAmplitude N '' Icc (-1 / 4) (1 / 4)) :=
    isCompact_Icc.image hFc
  have hsupp : (lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4))).support ⊆
      lacunaryGraphMap ε nonregularAmplitude N '' Icc (-1 / 4) (1 / 4) :=
    Measure.support_subset_of_isClosed hcpt.isClosed
      (mem_ae_iff.2 (lacunarySource_compl_image hF hcpt.isClosed.measurableSet))
  have hbound : ∀ z ∈ (lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4))).support,
      energyT (lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4))) 2 .mixed p 2 z ≤
        ENNReal.ofReal (C * ((∑' j, nonregularAmplitude j ^ p) + 1) * ε ^ p) := by
    intro z hz
    obtain ⟨t, -, rfl⟩ := hsupp hz
    exact (le_iSup (fun R : ℝ => energyT (lacunarySource ε nonregularAmplitude N
      (Icc (-1 / 4) (1 / 4))) 2 .mixed p R (lacunaryGraphMap ε nonregularAmplitude N t)) 2).trans
      (upper_bound_nonregular hp hC hε (hupC ε _ N hε hε' hdata _ hQ hQJ t))
  refine ⟨hbound, lintegral_energyT_quarter_pos p (by linarith) ε _ N hε hε' hdata, ?_⟩
  calc ∫⁻ z, energyT (lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4))) 2 .mixed
          p 2 z ∂(lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4)))
      ≤ ∫⁻ _, ENNReal.ofReal (C * ((∑' j, nonregularAmplitude j ^ p) + 1) * ε ^ p)
          ∂(lacunarySource ε nonregularAmplitude N (Icc (-1 / 4) (1 / 4))) :=
        lintegral_mono_ae (Filter.mem_of_superset Measure.support_mem_ae hbound)
    _ = ENNReal.ofReal (C * ((∑' j, nonregularAmplitude j ^ p) + 1) * ε ^ p) *
          ENNReal.ofReal (1 / 2) := by
        rw [lintegral_const, lacunarySource_univ hF, Real.volume_Icc]
        norm_num
    _ = ENNReal.ofReal (C * ((∑' j, nonregularAmplitude j ^ p) + 1) * ε ^ p / 2) := by
        rw [← ENNReal.ofReal_mul
          (mul_nonneg (mul_nonneg hC.le (by linarith)) (Real.rpow_nonneg hε.le p))]
        ring_nf

/-- **The exponent witnesses.** The witness above `2` comes from the lacunary estimates, the
graph-source theorem, `T_2 = S` and two small auxiliary statements; the witness below `2` is
`exponent_witness_below_bundle`. -/
theorem exponent_witnesses_of_providers :
    GraphSourceStatement → EnergyTwoStatement → ExponentWitnessesStatement := fun hGS hE2 =>
  ⟨exponent_witness_above_carrier_of_providers hGS hE2, exponent_witness_above_energy_skeleton,
    exponent_witness_below_bundle⟩

end ParabolicRectifiability.Examples
