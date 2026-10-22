import ParabolicRectifiability.IntegralCanonical.Defs

/-! # Elementary measure-theoretic helpers for the integral tests and canonical decomposition

These lemmas are the elementary measure theory shared by the proofs of `integral_equivalences`,
`integral_criterion` and `canonical_decomposition`:

* the Borel measurability of the finite-energy sets, from `measurable_squareEnergy`;
* the complement of a finite-energy set is the infinite-energy set;
* the empty finite-energy set of an unavailable family, from `betaSq_of_isEmpty`;
* the inclusion `E_H ∪ E_V ⊆ G`: the mixed infimum is taken over a larger family;
* the restriction of a locally Radon source is locally Radon, from mathlib's restriction
  instances;
* countable-cover null-set bookkeeping, and the passage from a finite set integral of a
  function that is infinite on a set to the nullity of that set.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

variable {n : ℕ}

/-- The finite-energy sets are Borel, by `measurable_squareEnergy`. -/
theorem measurableSet_finiteEnergySet (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ) (T : FamilyKind) (R : ℝ) : MeasurableSet (finiteEnergySet μ k T R) := by
  show MeasurableSet {z | squareEnergy μ k T R z < ⊤}
  exact measurableSet_lt (measurable_squareEnergy μ k T R) measurable_const

/-- The infinite-energy set `{S = ∞}` is Borel. -/
theorem measurableSet_squareEnergy_eq_top (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ) (T : FamilyKind) (R : ℝ) : MeasurableSet {z | squareEnergy μ k T R z = ⊤} :=
  measurable_squareEnergy μ k T R (measurableSet_singleton ⊤)

/-- The complement of `{S < ∞}` is `{S = ∞}`. -/
theorem compl_finiteEnergySet (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (R : ℝ) :
    (finiteEnergySet μ k T R)ᶜ = {z | squareEnergy μ k T R z = ⊤} := by
  ext z
  simp [finiteEnergySet, lt_top_iff_ne_top]

/-- `S < ∞` almost everywhere exactly when `{S = ∞}` is null. -/
theorem ae_squareEnergy_lt_top_iff (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (R : ℝ) :
    (∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) ↔ μ {z | squareEnergy μ k T R z = ⊤} = 0 := by
  rw [ae_iff]
  simp only [not_lt, top_le_iff]

/-- An unavailable family has square `+∞` at every point and every positive endpoint, so its
finite-energy set is empty. -/
theorem finiteEnergySet_eq_empty_of_isEmpty {k : ℕ} {T : FamilyKind} [IsEmpty (Models n k T)]
    (μ : Measure (Space n)) {R : ℝ} (hR : 0 < R) : finiteEnergySet μ k T R = ∅ := by
  have hpos : scaleMeasure (Ioo 0 R) ≠ 0 := by
    rw [scaleMeasure_apply _ measurableSet_Ioo]
    apply ne_of_gt
    rw [setLIntegral_pos_iff measurable_scaleDensity]
    have hsupp : Function.support (fun r : ℝ => ENNReal.ofReal (1 / r)) ∩
        (Ioo 0 R ∩ Ioi 0) = Ioo 0 R := by
      ext r
      simp only [Function.mem_support, mem_inter_iff, mem_Ioo, mem_Ioi, ne_eq,
        ENNReal.ofReal_eq_zero, not_le, one_div, inv_pos]
      tauto
    rw [hsupp, Real.volume_Ioo]
    simpa using hR
  ext z
  simp only [finiteEnergySet, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt,
    top_le_iff]
  rw [squareEnergy, setLIntegral_congr_fun measurableSet_Ioo
    (fun r hr => betaSq_of_isEmpty μ k T z hr.1), setLIntegral_const]
  exact ENNReal.mul_eq_top.mpr (Or.inr ⟨rfl, hpos⟩)

/-- For the zero source and an available family every square vanishes, so the finite-energy
set is everything. -/
theorem finiteEnergySet_zero_measure {k : ℕ} {T : FamilyKind} [Nonempty (Models n k T)]
    (R : ℝ) : finiteEnergySet (0 : Measure (Space n)) k T R = univ := by
  ext z
  simp [finiteEnergySet, squareEnergy]

/-- The mixed square is at most each fixed-family square: the mixed fitting infimum runs over both families. -/
theorem squareEnergy_mixed_le (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (R : ℝ)
    (z : Space n) : squareEnergy μ k .mixed R z ≤ squareEnergy μ k T R z := by
  unfold squareEnergy
  refine lintegral_mono fun r => ?_
  by_cases hr : 0 < r
  · rw [betaSq_of_pos μ k _ z hr, betaSq_of_pos μ k _ z hr]
    gcongr
    cases T with
    | horizontal =>
      exact le_iInf fun L => iInf_le_of_le (show Models n k .mixed from Sum.inl L) le_rfl
    | vertical =>
      exact le_iInf fun L => iInf_le_of_le (show Models n k .mixed from Sum.inr L) le_rfl
    | mixed => exact le_rfl
  · rw [betaSq_of_nonpos μ k _ z (not_lt.mp hr), betaSq_of_nonpos μ k _ z (not_lt.mp hr)]

/-- `E_T ⊆ G` for each family, in particular `E_H ∪ E_V ⊆ G` exactly. -/
theorem finiteEnergySet_subset_mixed (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (R : ℝ) : finiteEnergySet μ k T R ⊆ finiteEnergySet μ k .mixed R :=
  fun z hz => (squareEnergy_mixed_le μ k T R z).trans_lt hz

/-- The restriction of a locally Radon source to any set is locally Radon:
mathlib's restriction instances, using the sigma-finiteness of a measure finite on compacts
(`source_sigmaFinite`). -/
theorem restrict_locallyRadon {μ : Measure (Space n)} (hμ : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular) (A : Set (Space n)) :
    IsFiniteMeasureOnCompacts (μ.restrict A) ∧ (μ.restrict A).InnerRegular := by
  have := hμ
  have := hreg
  have : SigmaFinite μ := source_sigmaFinite μ
  exact ⟨inferInstance, inferInstance⟩

/-- Restriction preserves the intrinsic source class. -/
theorem isIntrinsicSource_restrict {k : ℕ} {μ : Measure (Space n)}
    (h : IsIntrinsicSource k μ) (A : Set (Space n)) : IsIntrinsicSource k (μ.restrict A) := by
  obtain ⟨hac, F, hFm, hFH, hFc⟩ := h
  exact ⟨(Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hac, F, hFm, hFH,
    nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hFc.le)⟩

/-- Countable-cover bookkeeping: if `ρ` vanishes on the part of `E` off `⋃ i, Γ i` and on
each `Γ i ∩ E`, then `ρ E = 0`. -/
theorem measure_eq_zero_of_cover {ι : Type*} [Countable ι] {ρ : Measure (Space n)}
    {E : Set (Space n)} (Γ : ι → Set (Space n)) (hcov : ρ (E ∩ (⋃ i, Γ i)ᶜ) = 0)
    (hE : ∀ i, ρ (Γ i ∩ E) = 0) : ρ E = 0 := by
  have hsub : E ⊆ (E ∩ (⋃ i, Γ i)ᶜ) ∪ ⋃ i, (Γ i ∩ E) := by
    intro z hz
    by_cases h : z ∈ ⋃ i, Γ i
    · obtain ⟨i, hi⟩ := mem_iUnion.1 h
      exact Or.inr (mem_iUnion.2 ⟨i, hi, hz⟩)
    · exact Or.inl ⟨hz, h⟩
  exact measure_mono_null hsub (measure_union_null hcov (measure_iUnion_null hE))

/-- The two-family form of `measure_eq_zero_of_cover`, for mixed covers. -/
theorem measure_eq_zero_of_cover₂ {ι κ : Type*} [Countable ι] [Countable κ]
    {ρ : Measure (Space n)} {E : Set (Space n)} (Γ : ι → Set (Space n))
    (Δ : κ → Set (Space n)) (hcov : ρ (E ∩ ((⋃ i, Γ i) ∪ ⋃ j, Δ j)ᶜ) = 0)
    (hΓ : ∀ i, ρ (Γ i ∩ E) = 0) (hΔ : ∀ j, ρ (Δ j ∩ E) = 0) : ρ E = 0 := by
  have hsub : E ⊆ (E ∩ ((⋃ i, Γ i) ∪ ⋃ j, Δ j)ᶜ) ∪ ((⋃ i, (Γ i ∩ E)) ∪ ⋃ j, (Δ j ∩ E)) := by
    intro z hz
    by_cases h : z ∈ (⋃ i, Γ i) ∪ ⋃ j, Δ j
    · rcases h with h | h
      · obtain ⟨i, hi⟩ := mem_iUnion.1 h
        exact Or.inr (Or.inl (mem_iUnion.2 ⟨i, hi, hz⟩))
      · obtain ⟨j, hj⟩ := mem_iUnion.1 h
        exact Or.inr (Or.inr (mem_iUnion.2 ⟨j, hj, hz⟩))
    · exact Or.inl ⟨hz, h⟩
  exact measure_mono_null hsub (measure_union_null hcov
    (measure_union_null (measure_iUnion_null hΓ) (measure_iUnion_null hΔ)))

/-- A finite set integral of a function that is infinite on a Borel set `N` makes `A ∩ N`
null. No measurability of the integrand is needed. -/
theorem measure_inter_eq_zero_of_setLIntegral_lt_top {μ : Measure (Space n)}
    {A N : Set (Space n)} (hN : MeasurableSet N) {f : Space n → ℝ≥0∞}
    (h : ∫⁻ z in A, f z ∂μ < ⊤) (hf : ∀ z ∈ N, f z = ⊤) : μ (A ∩ N) = 0 := by
  have hle : ∫⁻ z in A, N.indicator (fun _ => (⊤ : ℝ≥0∞)) z ∂μ ≤ ∫⁻ z in A, f z ∂μ := by
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ N
    · simp [Set.indicator_of_mem hz, hf z hz]
    · simp [Set.indicator_of_notMem hz]
  rw [lintegral_indicator_const hN, Measure.restrict_apply hN, inter_comm] at hle
  by_contra hne
  rw [ENNReal.top_mul hne] at hle
  exact absurd hle (not_le.2 h)

end ParabolicRectifiability.IntegralCanonical
