import ParabolicRectifiability.BetaP.Proofs.Support.IntermediateStatements
import ParabolicRectifiability.Enhancements.Statements.MainTheorem
import ParabolicRectifiability.Foundations.Statements.Ambient
import ParabolicRectifiability.Foundations.Statements.Measurability
import ParabolicRectifiability.Characterization.Statements.Branches

/-! # Basic lemmas for the beta-`p` support theorem

Elementary monotonicity, the conversion of a restriction decomposition into a nonnegative
decomposition, the two clamping comparisons of energies, the ambient decomposition from the
Foundations ambient core, and the Borel typing of a carrier from the finite-Hausdorff
criterion and typed refinement with the Hausdorff-null residual assigned to an available type.

Results from other parts of the development enter only as hypotheses (statements such as
`RectifiableReifenbergTheoremStatement`); the laws of `B_p` enter through the theorems of the
beta-`p` laws (for instance `betaPowClamping_law`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## Monotonicity -/

/-- Enlarging the constant preserves the support bundle (for a nonnegative parent radius). -/
theorem supportBounds_mono {n k : ℕ} {C C' : ℝ} {a : Space n} {R : ℝ} {KH KV : Set (Space n)}
    (h : HasRegularSupportBounds k C a R KH KV) (hC : C ≤ C') (hR : 0 ≤ R) :
    HasRegularSupportBounds k C' a R KH KV where
  horizontal_compact := h.horizontal_compact
  vertical_compact := h.vertical_compact
  horizontal_subset := h.horizontal_subset
  vertical_subset := h.vertical_subset
  horizontal_unavailable := h.horizontal_unavailable
  vertical_unavailable := h.vertical_unavailable
  horizontal_graphs := h.horizontal_graphs
  vertical_graphs := h.vertical_graphs
  hausdorff_total := h.hausdorff_total.trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hR _)))
  hausdorff_local := fun q s hs hsR => (h.hausdorff_local q s hs hsR).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hs.le _)))
  separated := fun q s r hs hsR hr hrs F hF hsep => (h.separated q s r hs hsR hr hrs F hF hsep).trans
    (mul_le_mul_of_nonneg_right hC (pow_nonneg (div_nonneg hs.le hr.le) _))
  minkowski := fun r hr hrR => (h.minkowski r hr hrR).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (pow_nonneg hR _))
      (pow_nonneg hr.le _)))
  finite_packing := fun q s hs hsR l z r hz hr hd =>
    (h.finite_packing q s hs hsR l z r hz hr hd).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hs.le _)))
  countable_packing := fun q s hs hsR I z r hz hr hd =>
    (h.countable_packing q s hs hsR I z r hz hr hd).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hs.le _)))

/-- Enlarging the constant and the loss preserves a beta-`p` decomposition. -/
theorem IsBetaPDecomposition.mono {n k : ℕ} {T : FamilyKind} {C C' : ℝ} {a : Space n}
    {R loss loss' : ℝ} {μ μplus μH μV : Measure (Space n)}
    (h : IsBetaPDecomposition k T C a R loss μ μplus μH μV) (hC : C ≤ C') (hR : 0 ≤ R)
    (hloss : loss ≤ loss') : IsBetaPDecomposition k T C' a R loss' μ μplus μH μV :=
  { h with
    remainder_bound := h.remainder_bound.trans (ENNReal.ofReal_le_ofReal hloss)
    supports := supportBounds_mono h.supports hC hR }

/-! ## From the restriction decomposition of the rectifiable Reifenberg theorem -/

/-- A restriction decomposition of the rectifiable Reifenberg theorem is a nonnegative beta-`p` decomposition with
the same constant and the same loss `C M + Γ`; the good restrictions are carried by `P(0,1)`
because the retained sets lie in it. -/
theorem isBetaPDecomposition_of_rectifiableReifenberg {n k : ℕ} {T : FamilyKind} {C M Γ : ℝ}
    {μ : Measure (Space n)} {D : RetainedSets n}
    (hD : Enhancements.IsRectifiableReifenbergDecomposition k C M Γ μ D)
    (hH : T = .vertical → D.horizontalMeasure μ = 0)
    (hV : T = .horizontal → D.verticalMeasure μ = 0) :
    IsBetaPDecomposition k T C (point 0 0) 1 (C * M + Γ) μ (D.remainderMeasure μ)
      (D.horizontalMeasure μ) (D.verticalMeasure μ) where
  measure_eq := hD.measure_eq
  remainder_bound := hD.remainder_bound
  horizontal_carried := by
    rw [RetainedSets.horizontalMeasure, Measure.restrict_apply measurableSet_ball.compl]
    exact measure_mono_null (fun z hz => absurd (D.horizontal_subset hz.2) hz.1) measure_empty
  vertical_carried := by
    rw [RetainedSets.verticalMeasure, Measure.restrict_apply measurableSet_ball.compl]
    exact measure_mono_null (fun z hz => absurd (D.vertical_subset hz.2) hz.1) measure_empty
  horizontal_unavailable := fun h => (hD.horizontal_unavailable h).1
  vertical_unavailable := fun h => (hD.vertical_unavailable h).1
  horizontal_disallowed := hH
  vertical_disallowed := hV
  supports := hD.supports

/-- The rectifiable Reifenberg theorem (`RectifiableReifenbergTheoremStatement`, as a hypothesis), read for every available family with
the family's own unit threshold, as nonnegative decompositions with loss `C M + Γ`. -/
theorem mt1_family_decomposition (hMT1 : Enhancements.RectifiableReifenbergTheoremStatement) (n : ℕ)
    (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
      μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) ≤
        ENNReal.ofReal Γ →
      ∃ μplus μH μV : Measure (Space n),
        IsBetaPDecomposition k T C (point 0 0) 1 (C * M + Γ) μ μplus μH μV := by
  obtain ⟨C, hC, hmixed, hfixed, -⟩ := hMT1 n hn
  refine ⟨C, hC, ?_⟩
  intro k hk hkn T hT μ hμ hreg M Γ hM hΓ hthr
  cases T with
  | mixed =>
    obtain ⟨D, hD⟩ := hmixed k hk hkn μ hμ hreg M Γ hM hΓ hthr
    exact ⟨_, _, _, isBetaPDecomposition_of_rectifiableReifenberg hD (fun h => by cases h)
      (fun h => by cases h)⟩
  | horizontal =>
    obtain ⟨D, hD, hHo, -⟩ :=
      hfixed k hk hkn .horizontal (by decide) hT μ hμ hreg M Γ hM hΓ hthr
    exact ⟨_, _, _, isBetaPDecomposition_of_rectifiableReifenberg hD (fun h => by cases h)
      (fun _ => (hHo rfl).1)⟩
  | vertical =>
    obtain ⟨D, hD, -, hVo⟩ :=
      hfixed k hk hkn .vertical (by decide) hT μ hμ hreg M Γ hM hΓ hthr
    exact ⟨_, _, _, isBetaPDecomposition_of_rectifiableReifenberg hD (fun _ => (hVo rfl).1)
      (fun h => by cases h)⟩

/-! ## The ambient decomposition -/

/-- The Foundations ambient core (statement, as a hypothesis) at `P(0,1)`: retain `μ⌊P(0,1)` as
the vertical part, with zero loss and no energy hypothesis, for every family available at
`k = n+2`. -/
theorem ambient_betaP_decomposition (hAmb : AmbientLocalCoreStatement) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : FamilyKind, Nonempty (Models n (n + 2) T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∃ μplus μH μV : Measure (Space n),
        IsBetaPDecomposition (n + 2) T C (point 0 0) 1 0 μ μplus μH μV := by
  obtain ⟨C, hC, h⟩ := hAmb n hn
  refine ⟨C, hC, fun T hT μ hμ hreg => ?_⟩
  obtain ⟨heq, hzero, hsupp⟩ := h μ hμ hreg (point 0 0) 1 one_pos
  refine ⟨μ.restrict (Metric.ball (point 0 0) 1)ᶜ, 0, μ.restrict (Metric.ball (point 0 0) 1), ?_⟩
  exact {
    measure_eq := by rw [add_zero]; exact heq
    remainder_bound := by rw [hzero]; simp
    horizontal_carried := by simp
    vertical_carried := by
      rw [Measure.restrict_apply measurableSet_ball.compl, compl_inter_self, measure_empty]
    horizontal_unavailable := fun _ => rfl
    vertical_unavailable := fun h => absurd ⟨by omega, le_rfl⟩ h
    horizontal_disallowed := fun _ => rfl
    vertical_disallowed := fun hT' => by
      subst hT'
      have := HorizontalModel.nonempty_iff.mp hT
      omega
    supports := by rw [Measure.support_zero]; exact hsupp }

/-! ## Clamping comparisons of the energies -/

/-- `S_{2,μ,T}^a ≤ 2^{2-p} T_{p,μ,T}^a` for `0 < p ≤ 2`, from the clamping law and the
Foundations identity `B_2 = betaSq`. -/
theorem squareEnergy_le_two_rpow_mul_energyT (hB2 : BetaPowTwoStatement) {n : ℕ} (hn : 1 ≤ n)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2) (T : FamilyKind) (μ : Measure (Space n)) {p : ℝ}
    (hp : 0 < p) (hp2 : p ≤ 2) (a : ℝ) (z : Space n) :
    squareEnergy μ k T a z ≤ (2 : ℝ≥0∞) ^ (2 - p) * energyT μ k T p a z := by
  unfold squareEnergy energyT
  calc ∫⁻ r in Ioo 0 a, betaSq μ k T z r ∂scaleMeasure
      ≤ ∫⁻ r in Ioo 0 a, (2 : ℝ≥0∞) ^ (2 - p) * betaPow μ k T p z r ∂scaleMeasure := by
        refine lintegral_mono fun r => ?_
        rw [← hB2 n hn k hk hkn T μ z r]
        exact (betaPowClamping_law n hn k hk hkn T μ z r).1 p hp hp2
    _ = (2 : ℝ≥0∞) ^ (2 - p) * ∫⁻ r in Ioo 0 a, betaPow μ k T p z r ∂scaleMeasure :=
        lintegral_const_mul' _ _
          (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)

/-- `T_{p,μ,T}^a ≤ 2^{p-2} S_{2,μ,T}^a` for `p ≥ 2`. -/
theorem energyT_le_two_rpow_mul_squareEnergy (hB2 : BetaPowTwoStatement) {n : ℕ} (hn : 1 ≤ n)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2) (T : FamilyKind) (μ : Measure (Space n)) {p : ℝ}
    (hp2 : 2 ≤ p) (a : ℝ) (z : Space n) :
    energyT μ k T p a z ≤ (2 : ℝ≥0∞) ^ (p - 2) * squareEnergy μ k T a z := by
  unfold squareEnergy energyT
  calc ∫⁻ r in Ioo 0 a, betaPow μ k T p z r ∂scaleMeasure
      ≤ ∫⁻ r in Ioo 0 a, (2 : ℝ≥0∞) ^ (p - 2) * betaSq μ k T z r ∂scaleMeasure := by
        refine lintegral_mono fun r => ?_
        rw [← hB2 n hn k hk hkn T μ z r]
        exact (betaPowClamping_law n hn k hk hkn T μ z r).2 p hp2
    _ = (2 : ℝ≥0∞) ^ (p - 2) * ∫⁻ r in Ioo 0 a, betaSq μ k T z r ∂scaleMeasure :=
        lintegral_const_mul' _ _
          (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)

/-! ## Covers and the Borel typing of a carrier -/

theorem hasHorizontalGraphCover_empty {n : ℕ} (k : ℕ) (ε : ℝ) :
    HasHorizontalGraphCover k (∅ : Set (Space n)) ε :=
  ⟨∅, fun i => absurd i.2 (Set.notMem_empty _), by simp⟩

theorem hasGeneralRegularVerticalGraphCover_empty {n : ℕ} (k : ℕ) (ε : ℝ) :
    HasGeneralRegularVerticalGraphCover k (∅ : Set (Space n)) ε :=
  ⟨∅, fun i => absurd i.2 (Set.notMem_empty _), by simp⟩

/-- Adding a Hausdorff-null set keeps a horizontal cover modulo `H_P^k`. -/
theorem horizontalCover_union_null {n k : ℕ} {ε : ℝ} {A N : Set (Space n)}
    (h : HasHorizontalGraphCover k A ε) (hN : hausdorffP n k N = 0) :
    HasHorizontalGraphCover k (A ∪ N) ε := by
  obtain ⟨I, G, hG⟩ := h
  refine ⟨I, G, measure_mono_null ?_ (measure_union_null hG hN)⟩
  intro z hz
  rcases hz.1 with hA | hN'
  · exact Or.inl ⟨hA, hz.2⟩
  · exact Or.inr hN'

/-- Adding a Hausdorff-null set keeps a general regular vertical cover modulo `H_P^k`. -/
theorem verticalCover_union_null {n k : ℕ} {ε : ℝ} {A N : Set (Space n)}
    (h : HasGeneralRegularVerticalGraphCover k A ε) (hN : hausdorffP n k N = 0) :
    HasGeneralRegularVerticalGraphCover k (A ∪ N) ε := by
  obtain ⟨I, G, hG⟩ := h
  refine ⟨I, G, measure_mono_null ?_ (measure_union_null hG hN)⟩
  intro z hz
  rcases hz.1 with hA | hN'
  · exact Or.inl ⟨hA, hz.2⟩
  · exact Or.inr hN'

/-- **Borel typing of a carrier.** For a Borel `K` with finite
`H_P^k` measure whose own Hausdorff source has finite square for the family `T` almost
everywhere: a fixed family uses the fixed-family finite-Hausdorff criterion (only that
type); the mixed family uses the typed refinement, and the Hausdorff-null residual is
assigned to an available type before any tolerance or source approximation. -/
theorem typedSplit_exists (hFH : Characterization.FiniteHausdorffCriterionStatement)
    (hTR : Characterization.TypedRefinementSetStatement) {n : ℕ} (hn : 1 ≤ n) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n + 2) {T : FamilyKind} (hT : Nonempty (Models n k T))
    {K : Set (Space n)} (hKm : MeasurableSet K) (hKfin : hausdorffP n k K < ⊤)
    (hE : ∀ᵐ z ∂(hausdorffP n k).restrict K,
      squareEnergy ((hausdorffP n k).restrict K) k T 1 z < ⊤) :
    Nonempty (TypedSplit k T K) := by
  cases T with
  | horizontal =>
    have hav : 1 ≤ k ∧ k ≤ n := HorizontalModel.nonempty_iff.mp hT
    have hcov := hFH.1 n hn k hk hkn.le .horizontal hT K hKm hKfin ⟨1, one_pos, hE⟩
    exact ⟨{
      horizontal := K
      vertical := ∅
      measurable_horizontal := hKm
      measurable_vertical := MeasurableSet.empty
      disjoint := Set.disjoint_empty K
      union_eq := union_empty K
      horizontal_unavailable := fun h => absurd hav h
      vertical_unavailable := fun _ => rfl
      family := ⟨fun _ => rfl, fun h => absurd h (by decide)⟩
      horizontal_graphs := fun ε hε => hcov ε hε
      vertical_graphs := fun ε _ => hasGeneralRegularVerticalGraphCover_empty k ε }⟩
  | vertical =>
    have hav : 2 ≤ k ∧ k ≤ n + 2 := VerticalModel.nonempty_iff.mp hT
    have hcov := hFH.1 n hn k hk hkn.le .vertical hT K hKm hKfin ⟨1, one_pos, hE⟩
    exact ⟨{
      horizontal := ∅
      vertical := K
      measurable_horizontal := MeasurableSet.empty
      measurable_vertical := hKm
      disjoint := Set.empty_disjoint K
      union_eq := empty_union K
      horizontal_unavailable := fun _ => rfl
      vertical_unavailable := fun h => absurd hav h
      family := ⟨fun h => absurd h (by decide), fun _ => rfl⟩
      horizontal_graphs := fun ε _ => hasHorizontalGraphCover_empty k ε
      vertical_graphs := fun ε hε => hcov ε hε }⟩
  | mixed =>
    obtain ⟨EH, EV, hEHm, hEVm, hdisj, hEHK, hEVK, hnull, -, -, hcov, hHun, hVun⟩ :=
      hTR n hn k hk hkn.le K hKm hKfin hE
    have hNm : MeasurableSet (K \ (EH ∪ EV)) := hKm.diff (hEHm.union hEVm)
    have hunion : ∀ A B : Set (Space n), A ∪ B = EH ∪ EV ∪ K \ (EH ∪ EV) →
        A ∪ B = K := by
      intro A B hAB
      rw [hAB, union_sdiff_self, union_eq_right.mpr (union_subset hEHK hEVK)]
    by_cases hav : 1 ≤ k ∧ k ≤ n
    · exact ⟨{
        horizontal := EH ∪ K \ (EH ∪ EV)
        vertical := EV
        measurable_horizontal := hEHm.union hNm
        measurable_vertical := hEVm
        disjoint := Disjoint.union_left hdisj
          (Set.disjoint_left.mpr fun z hz hzV => hz.2 (Or.inr hzV))
        union_eq := hunion _ _ (by rw [union_right_comm])
        horizontal_unavailable := fun h => absurd hav h
        vertical_unavailable := fun h => hVun fun hV => h (VerticalModel.nonempty_iff.mp hV)
        family := ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
        horizontal_graphs := fun ε hε => horizontalCover_union_null (hcov ε hε).1 hnull
        vertical_graphs := fun ε hε => (hcov ε hε).2 }⟩
    · have hvav : 2 ≤ k ∧ k ≤ n + 2 := by omega
      exact ⟨{
        horizontal := EH
        vertical := EV ∪ K \ (EH ∪ EV)
        measurable_horizontal := hEHm
        measurable_vertical := hEVm.union hNm
        disjoint := Disjoint.union_right hdisj
          (Set.disjoint_left.mpr fun z hzH hz => hz.2 (Or.inl hzH))
        union_eq := hunion _ _ (by rw [union_assoc])
        horizontal_unavailable := fun _ =>
          hHun fun hH => hav (HorizontalModel.nonempty_iff.mp hH)
        vertical_unavailable := fun h => absurd hvav h
        family := ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
        horizontal_graphs := fun ε hε => (hcov ε hε).1
        vertical_graphs := fun ε hε => verticalCover_union_null (hcov ε hε).2 hnull }⟩

/-- A `p`-carrier of a source supported in `P̄(c,1/64)` has finite `H_P^k` measure: it lies in
`P(c,1)`, where its local Hausdorff bound at scale one applies. -/
theorem PCarrier.hausdorff_lt_top {n k : ℕ} {T : FamilyKind} {p M C : ℝ}
    {ν : Measure (Space n)} (K : PCarrier ν k T p M C) {c : Space n}
    (hc : ν.support ⊆ Metric.closedBall c (1 / 64)) : hausdorffP n k K.set < ⊤ := by
  have hsub : K.set ⊆ Metric.ball c 1 := fun z hz =>
    Metric.closedBall_subset_ball (by norm_num) (hc (K.subset_support hz))
  have h := K.content.hausdorff c 1 one_pos le_rfl
  rw [inter_eq_left.mpr hsub] at h
  exact h.trans_lt ENNReal.ofReal_lt_top

end ParabolicRectifiability.BetaP
