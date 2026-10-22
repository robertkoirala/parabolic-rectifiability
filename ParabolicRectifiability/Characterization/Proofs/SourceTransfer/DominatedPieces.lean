import ParabolicRectifiability.Foundations.Carriers

/-! # Radon–Nikodym exhaustion of an intrinsic source

Proves `exists_dominated_hausdorff_pieces_proof` (the statement of
`exists_dominated_hausdorff_pieces`): a locally finite measure `μ ≪ H_P^k` with a Borel
sigma-finite Hausdorff carrier is carried by countably many Borel pieces `F_m` of finite
`H_P^k`-measure on each of which `H_P^k⌊F_m ≤ c_m μ`.

Proof. Let `F_j` be the Borel finite-Hausdorff pieces of the carrier and `E = ⋃ F_j`. The
measure `η = H_P^k⌊E` is sigma-finite through the finite-measure cover `F_j ∪ Eᶜ` of the
whole space (unrestricted `H_P^k` is never used). `μ` is sigma-finite (finite on compacts in a
proper space) and `μ ≪ η` because `μ(Eᶜ) = 0`. With `h = dμ/dη`, the pieces are
`F_j ∩ {h ≥ 1/(m+1)}`, reindexed by `Nat.unpair`. On such a piece `1 ≤ (m+1) h`, so
`H_P^k⌊piece ≤ (m+1) μ` on the whole space by `∫_S h dη ≤ μ(S)`. Off the union of the pieces
and inside `E` one has `h = 0`, a `μ`-null set since `μ = h η`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- `η = H_P^k⌊E`, `E = ⋃ F_j`, is sigma-finite: the sets `F_j ∪ Eᶜ` cover the space and have
finite `η`-measure. -/
theorem b3rn_sigmaFinite_restrict {n k : ℕ} (F : ℕ → Set (Space n))
    (hFm : ∀ j, MeasurableSet (F j)) (hFH : ∀ j, hausdorffP n k (F j) < ⊤) :
    SigmaFinite ((hausdorffP n k).restrict (⋃ j, F j)) := by
  have hEm : MeasurableSet (⋃ j, F j) := MeasurableSet.iUnion hFm
  refine Measure.FiniteSpanningSetsIn.sigmaFinite (C := univ)
    { set := fun j => F j ∪ (⋃ i, F i)ᶜ
      set_mem := fun _ => mem_univ _
      finite := fun j => ?_
      spanning := ?_ }
  · rw [Measure.restrict_apply' hEm]
    refine (measure_mono ?_).trans_lt (hFH j)
    rintro x ⟨hx | hx, hxE⟩
    · exact hx
    · exact absurd hxE hx
  · refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ ⋃ i, F i
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨j, Or.inl hj⟩
    · exact mem_iUnion.2 ⟨0, Or.inr hx⟩

theorem b3rn_ofReal_succ (m : ℕ) :
    ENNReal.ofReal ((m : ℝ) + 1) = (m : ℝ≥0∞) + 1 := by
  rw [ENNReal.ofReal_add (Nat.cast_nonneg m) zero_le_one, ENNReal.ofReal_natCast,
    ENNReal.ofReal_one]

/-- **Dominated Hausdorff pieces**: `μ` is carried by countably many Borel sets of finite
`H_P^k`-measure on which `H_P^k` is dominated by a multiple of `μ`. -/
theorem exists_dominated_hausdorff_pieces_proof :
    ∀ (n k : ℕ) (μ : Measure (Space n)), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      μ ≪ hausdorffP n k → HasBorelSigmaFiniteHausdorffCarrier k μ →
      ∃ F : ℕ → Set (Space n), (∀ m, MeasurableSet (F m)) ∧
        (∀ m, hausdorffP n k (F m) < ⊤) ∧
        (∀ m, ∃ c : ℝ, 0 < c ∧ (hausdorffP n k).restrict (F m) ≤ ENNReal.ofReal c • μ) ∧
        μ (⋃ m, F m)ᶜ = 0 := by
  intro n k μ hfin _ hac hcar
  obtain ⟨F, hFm, hFH, hFμ⟩ := hcar
  have hEm : MeasurableSet (⋃ j, F j) := MeasurableSet.iUnion hFm
  set E := ⋃ j, F j with hE
  set η := (hausdorffP n k).restrict E with hη
  have : SigmaFinite η := b3rn_sigmaFinite_restrict F hFm hFH
  have : SigmaFinite μ := SigmaFinite.of_isFiniteMeasureOnCompacts μ
  have hμη : μ ≪ η := by
    intro A hA
    rw [hη, Measure.restrict_apply' hEm] at hA
    have h1 : μ (A ∩ E) = 0 := hac hA
    have h2 : μ (A ∩ Eᶜ) = 0 := measure_mono_null inter_subset_right hFμ
    refine le_antisymm ?_ zero_le
    calc μ A ≤ μ ((A ∩ E) ∪ (A ∩ Eᶜ)) := measure_mono (fun x hx => by
            by_cases hxE : x ∈ E
            · exact Or.inl ⟨hx, hxE⟩
            · exact Or.inr ⟨hx, hxE⟩)
      _ ≤ μ (A ∩ E) + μ (A ∩ Eᶜ) := measure_union_le _ _
      _ = 0 := by rw [h1, h2, add_zero]
  have hhm : Measurable (μ.rnDeriv η) := Measure.measurable_rnDeriv μ η
  let G : ℕ → Set (Space n) := fun m =>
    F m.unpair.1 ∩ {x | ((m.unpair.2 : ℝ≥0∞) + 1)⁻¹ ≤ μ.rnDeriv η x}
  have hGm : ∀ m, MeasurableSet (G m) := fun m =>
    (hFm _).inter (measurableSet_le measurable_const hhm)
  have hGE : ∀ m, G m ⊆ E := fun m x hx => mem_iUnion.2 ⟨_, hx.1⟩
  refine ⟨G, hGm, fun m => (measure_mono inter_subset_left).trans_lt (hFH _), ?_, ?_⟩
  · -- domination with `c = m₂ + 1`
    intro m
    refine ⟨(m.unpair.2 : ℝ) + 1, by positivity, ?_⟩
    rw [b3rn_ofReal_succ]
    set a : ℝ≥0∞ := (m.unpair.2 : ℝ≥0∞) + 1 with ha
    have ha0 : a ≠ 0 := by rw [ha]; simp
    have hatop : a ≠ ⊤ := by rw [ha]; exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top _,
      ENNReal.one_ne_top⟩
    refine Measure.le_iff.2 fun A hA => ?_
    rw [Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul]
    have hS : MeasurableSet (A ∩ G m) := hA.inter (hGm m)
    have hηS : η (A ∩ G m) = hausdorffP n k (A ∩ G m) := by
      rw [hη, Measure.restrict_apply' hEm,
        inter_eq_left.2 (inter_subset_right.trans (hGE m))]
    rw [← hηS]
    calc η (A ∩ G m) = ∫⁻ _ in A ∩ G m, 1 ∂η := by rw [setLIntegral_const, one_mul]
      _ ≤ ∫⁻ x in A ∩ G m, a * μ.rnDeriv η x ∂η := by
          refine setLIntegral_mono (measurable_const.mul hhm) fun x hx => ?_
          have hx' : a⁻¹ ≤ μ.rnDeriv η x := hx.2.2
          calc (1 : ℝ≥0∞) = a * a⁻¹ := (ENNReal.mul_inv_cancel ha0 hatop).symm
            _ ≤ a * μ.rnDeriv η x := by gcongr
      _ = a * ∫⁻ x in A ∩ G m, μ.rnDeriv η x ∂η := lintegral_const_mul a hhm
      _ ≤ a * μ (A ∩ G m) := by gcongr; exact Measure.setLIntegral_rnDeriv_le _
      _ ≤ a * μ A := by gcongr; exact inter_subset_left
  · -- the pieces carry `μ`
    set Z : Set (Space n) := {x | μ.rnDeriv η x = 0} with hZ
    have hZm : MeasurableSet Z := hhm (measurableSet_singleton 0)
    have hμZ : μ Z = 0 := by
      rw [← Measure.setLIntegral_rnDeriv' hμη hZm]
      refine le_antisymm ?_ zero_le
      calc ∫⁻ x in Z, μ.rnDeriv η x ∂η ≤ ∫⁻ _ in Z, 0 ∂η :=
            setLIntegral_mono measurable_const fun x hx => le_of_eq hx
        _ = 0 := lintegral_zero
    have hsub : (⋃ m, G m)ᶜ ⊆ Eᶜ ∪ Z := by
      intro x hx
      by_cases hxE : x ∈ E
      · right
        obtain ⟨j, hj⟩ := mem_iUnion.1 hxE
        by_contra hne
        obtain ⟨i, hi⟩ := ENNReal.exists_inv_nat_lt (a := μ.rnDeriv η x) hne
        refine hx (mem_iUnion.2 ⟨Nat.pair j i, ?_⟩)
        refine ⟨by rw [Nat.unpair_pair]; exact hj, ?_⟩
        show ((((Nat.pair j i).unpair.2 : ℕ) : ℝ≥0∞) + 1)⁻¹ ≤ μ.rnDeriv η x
        rw [Nat.unpair_pair]
        exact (ENNReal.inv_le_inv.2 le_self_add).trans hi.le
      · exact Or.inl hxE
    refine le_antisymm ?_ zero_le
    calc μ (⋃ m, G m)ᶜ ≤ μ (Eᶜ ∪ Z) := measure_mono hsub
      _ ≤ μ Eᶜ + μ Z := measure_union_le _ _
      _ = 0 := by rw [hFμ, hμZ, add_zero]

end ParabolicRectifiability.Characterization
