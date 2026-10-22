import ParabolicRectifiability.QuantitativeCharacterization.Statements.ReverseBound

/-! # The covering assembly

Proves `d2_covering_assembly_proof : CoveringAssemblyStatement`, the type of the statement
`ReverseTree.d2_covering_assembly`.

Proof idea: by Tonelli the left side is the `dμ dr/r` integral of the
mixed `β_μ²` over `P(a,R) × (0,R)`. Off `supp μ` the product is null, so the domain lies in
`𝓑 ∪ ⋃_i 𝓤_i` up to the null set of `cover_null`. Bad pairs: `β_μ² ≤ r^{-k} μ(P(z,r)) ≤ A`
(a model through `z`, upper growth at `z ∈ supp μ ∩ P(a,R)`, `0 < r < R`) and
`(dμ dr/r)(𝓑) ≤ K R^k`. Good pairs: `𝓤_i ⊆ d2_modelPairs L Γ_i a_i R_i`, the mixed beta is at
most the typed beta, the per-model bound and root packing `Σ_i R_i^k ≤ K R^k`. Neither local
packing nor the pairwise-null intersections are used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization.ReverseTree

open ParabolicRectifiability.Foundations

/-- The mixed beta is at most the beta of any fixed family (more models in the infimum). -/
theorem d2asm_betaSq_mixed_le {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (z : Space n) (r : ℝ) : betaSq μ k .mixed z r ≤ betaSq μ k T z r := by
  by_cases hr : 0 < r
  · rw [betaSq_of_pos _ _ _ _ hr, betaSq_of_pos _ _ _ _ hr]
    gcongr
    cases T with
    | horizontal =>
      exact le_iInf fun L => iInf_le (fun L' : Models n k .mixed => fit μ L' z r) (Sum.inl L)
    | vertical =>
      exact le_iInf fun L => iInf_le (fun L' : Models n k .mixed => fit μ L' z r) (Sum.inr L)
    | mixed => exact le_rfl
  · simp [betaSq, hr]

/-- Bad pairs: a model through the centre and upper growth give `β_μ(z,r)² ≤ A`. -/
theorem d2asm_betaSq_le_of_growth {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (μ : Measure (Space n)) {A : ℝ} (hA : 0 ≤ A) (z : Space n) {r : ℝ} (hr : 0 < r)
    (hz : μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) :
    betaSq μ k .mixed z r ≤ ENNReal.ofReal A := by
  have : Nonempty (Models n k .mixed) := AdmissibleModel.nonempty_of_range hn hk hkn
  calc betaSq μ k .mixed z r ≤ (ENNReal.ofReal r)⁻¹ ^ k * μ (Metric.ball z r) :=
        betaSq_le_radius_inv_pow_mul_measure μ k .mixed z hr
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ k * ENNReal.ofReal (A * r ^ k) := by gcongr
    _ = ENNReal.ofReal A := by
        rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_pow hr.le, mul_left_comm, ← mul_pow,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top,
          one_pow, mul_one]

/-- Tonelli: the root integral of the square energy is the `dμ dr/r` integral of `β²` over
`P(a,R) × (0,R)`. -/
theorem d2asm_lintegral_squareEnergy_eq {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (k : ℕ) (T : FamilyKind) (a : Space n) (R : ℝ) :
    ∫⁻ z in Metric.ball a R, squareEnergy μ k T R z ∂μ =
      ∫⁻ p in Metric.ball a R ×ˢ Ioo 0 R, betaSq μ k T p.1 p.2 ∂(pointScaleMeasure μ) := by
  have : SigmaFinite μ := source_sigmaFinite μ
  rw [pointScaleMeasure, ← Measure.prod_restrict]
  exact (lintegral_prod _ (measurable_betaSq μ k T).aemeasurable).symm

/-- Points off `supp μ` are `dμ dr/r`-null. -/
theorem d2asm_pointScale_compl_support {n : ℕ} (μ : Measure (Space n)) [μ.InnerRegular] :
    pointScaleMeasure μ (μ.supportᶜ ×ˢ (univ : Set ℝ)) = 0 := by
  rw [pointScaleMeasure, Measure.prod_prod, Measure.measure_compl_support_of_innerRegular,
    zero_mul]

/-- **Covering assembly**: the type of `ReverseTree.d2_covering_assembly`. -/
theorem d2_covering_assembly_proof : CoveringAssemblyStatement := by
  intro n hn k hk hkn L K A C₁ hL hK hA hC₁ μ hμc hμr a ha R hR 𝒞 hgrowth hmodel
  have := hμc
  have := hμr
  have hA0 : 0 ≤ A := by linarith
  -- the exceptional null set
  set N : Set (Space n × ℝ) :=
    (rootPairs μ a R \ (𝒞.badSet ∪ ⋃ i, 𝒞.scaleSet i)) ∪ (μ.supportᶜ ×ˢ (univ : Set ℝ))
    with hNdef
  have hN : pointScaleMeasure μ N = 0 :=
    measure_union_null 𝒞.cover_null (d2asm_pointScale_compl_support μ)
  have hS : Metric.ball a R ×ˢ Ioo 0 R ⊆ (𝒞.badSet ∪ ⋃ i, 𝒞.scaleSet i) ∪ N := by
    intro p hp
    by_cases hs : p.1 ∈ μ.support
    · by_cases hc : p ∈ 𝒞.badSet ∪ ⋃ i, 𝒞.scaleSet i
      · exact Or.inl hc
      · have hr : p ∈ rootPairs μ a R :=
          (⟨⟨hp.1, hs⟩, hp.2⟩ : p ∈ (Metric.ball a R ∩ μ.support) ×ˢ Ioo 0 R)
        exact Or.inr (Or.inl ⟨hr, hc⟩)
    · exact Or.inr (Or.inr ⟨hs, trivial⟩)
  -- bad pairs
  have hbad : ∫⁻ p in 𝒞.badSet, betaSq μ k .mixed p.1 p.2 ∂(pointScaleMeasure μ) ≤
      ENNReal.ofReal A * ENNReal.ofReal (K * R ^ k) := by
    calc ∫⁻ p in 𝒞.badSet, betaSq μ k .mixed p.1 p.2 ∂(pointScaleMeasure μ)
        ≤ ∫⁻ _p in 𝒞.badSet, ENNReal.ofReal A ∂(pointScaleMeasure μ) := by
          refine setLIntegral_mono measurable_const fun p hp => ?_
          have hp' : p ∈ (Metric.ball a R ∩ μ.support) ×ˢ Ioo 0 R := 𝒞.badSet_subset hp
          exact d2asm_betaSq_le_of_growth hn hk hkn μ hA0 p.1 hp'.2.1
            (hgrowth p.1 ⟨hp'.1.2, hp'.1.1⟩ p.2 hp'.2.1 hp'.2.2.le)
      _ = ENNReal.ofReal A * pointScaleMeasure μ 𝒞.badSet := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (K * R ^ k) := by gcongr; exact 𝒞.bad_bound
  -- good pairs, one model at a time
  have hgood : ∀ i : 𝒞.index,
      ∫⁻ p in 𝒞.scaleSet i, betaSq μ k .mixed p.1 p.2 ∂(pointScaleMeasure μ) ≤
        ENNReal.ofReal C₁ * ENNReal.ofReal (𝒞.radius i) ^ k := by
    intro i
    have hsub : 𝒞.scaleSet i ⊆
        d2_modelPairs L (𝒞.reference i).carrier (𝒞.center i) (𝒞.radius i) := by
      intro p hp
      obtain ⟨⟨-, h1⟩, h2, h3⟩ := 𝒞.scaleSet_cover i hp
      simp only [d2_modelPairs, mem_ofPred_eq]
      exact ⟨h1, h2, h3⟩
    calc ∫⁻ p in 𝒞.scaleSet i, betaSq μ k .mixed p.1 p.2 ∂(pointScaleMeasure μ)
        ≤ ∫⁻ p in 𝒞.scaleSet i, betaSq μ k (𝒞.reference i).kind p.1 p.2
            ∂(pointScaleMeasure μ) :=
          lintegral_mono fun p => d2asm_betaSq_mixed_le μ k _ p.1 p.2
      _ ≤ ∫⁻ p in d2_modelPairs L (𝒞.reference i).carrier (𝒞.center i) (𝒞.radius i),
            betaSq μ k (𝒞.reference i).kind p.1 p.2 ∂(pointScaleMeasure μ) :=
          lintegral_mono_set hsub
      _ ≤ ENNReal.ofReal (C₁ * 𝒞.radius i ^ k) := hmodel i
      _ = ENNReal.ofReal C₁ * ENNReal.ofReal (𝒞.radius i) ^ k := by
          rw [ENNReal.ofReal_mul hC₁.le, ENNReal.ofReal_pow (𝒞.radius_pos i).le]
  have hsum : ∑' i : 𝒞.index, ENNReal.ofReal C₁ * ENNReal.ofReal (𝒞.radius i) ^ k ≤
      ENNReal.ofReal C₁ * ENNReal.ofReal (K * R ^ k) := by
    rw [ENNReal.tsum_mul_left]
    gcongr
    exact 𝒞.root_packing
  rw [d2asm_lintegral_squareEnergy_eq]
  calc ∫⁻ p in Metric.ball a R ×ˢ Ioo 0 R, betaSq μ k .mixed p.1 p.2 ∂(pointScaleMeasure μ)
      ≤ ∫⁻ p in (𝒞.badSet ∪ ⋃ i, 𝒞.scaleSet i) ∪ N, betaSq μ k .mixed p.1 p.2
          ∂(pointScaleMeasure μ) := lintegral_mono_set hS
    _ ≤ (∫⁻ p in 𝒞.badSet ∪ ⋃ i, 𝒞.scaleSet i, betaSq μ k .mixed p.1 p.2
          ∂(pointScaleMeasure μ)) +
        ∫⁻ p in N, betaSq μ k .mixed p.1 p.2 ∂(pointScaleMeasure μ) :=
          lintegral_union_le _ _ _
    _ = ∫⁻ p in 𝒞.badSet ∪ ⋃ i, 𝒞.scaleSet i, betaSq μ k .mixed p.1 p.2
          ∂(pointScaleMeasure μ) := by
          rw [setLIntegral_measure_zero _ _ hN, add_zero]
    _ ≤ (∫⁻ p in 𝒞.badSet, betaSq μ k .mixed p.1 p.2 ∂(pointScaleMeasure μ)) +
        ∫⁻ p in ⋃ i, 𝒞.scaleSet i, betaSq μ k .mixed p.1 p.2 ∂(pointScaleMeasure μ) :=
          lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (K * R ^ k) +
        ∑' i : 𝒞.index, ∫⁻ p in 𝒞.scaleSet i, betaSq μ k .mixed p.1 p.2
          ∂(pointScaleMeasure μ) :=
          add_le_add hbad (lintegral_iUnion_le _ _)
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (K * R ^ k) +
        ENNReal.ofReal C₁ * ENNReal.ofReal (K * R ^ k) :=
          add_le_add le_rfl ((ENNReal.tsum_le_tsum hgood).trans hsum)
    _ = ENNReal.ofReal ((A + C₁) * K * R ^ k) := by
          rw [← add_mul, ← ENNReal.ofReal_add hA0 hC₁.le,
            ← ENNReal.ofReal_mul (by linarith)]
          congr 1
          ring

end ParabolicRectifiability.QuantitativeCharacterization.ReverseTree
