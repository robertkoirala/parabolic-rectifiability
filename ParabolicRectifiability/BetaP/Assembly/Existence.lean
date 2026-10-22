import ParabolicRectifiability.BetaP.Assembly.AssemblyLemmas
import ParabolicRectifiability.Decomposition.SourceAssembly

/-! # Finite assembly of a beta-`p` decomposition

`casm_exists_assembled_p_decomposition` proves the statement of
`exists_assembled_p_decomposition` from the three steps `casm_compactApproximation`,
`casm_remainder` and `casm_supportBounds`.

Assembly, for `N`, `C_c > 0` fixed and `C = N C_c + 1` chosen before `k`, `T`, `μ`,
`M`, `Γ`:
1. for each region choose compact `A_{H,i} ⊆ H_i`, `A_{V,i} ⊆ V_i` missing at most
   `M^{p/2}/(N+1)` of `ν_i = μ⌊region_i` inside the carrier (`casm_compactApproximation`); with
   the carrier loss
   `ν_i(K_iᶜ) ≤ C_c M^{p/2}`, each piece misses at most `ℓ = C_c M^{p/2} + M^{p/2}/(N+1)`;
2. `E_T = ⋃_i region_i ∩ A_{T,i}` (`casmRetained`): Borel, disjoint (regions are disjoint and
   `H_i ∩ V_i = ∅`), inside `P(0,1)`;
3. `μ_T = μ⌊E_T`, `μ⁺ = μ⌊(E_H ∪ E_V)ᶜ`, so `μ = μ⁺ + μ_H + μ_V`; the remainder in `P(0,1)` is at
   most `Γ + Σ_i ℓ ≤ Γ + N C_c M^{p/2} + M^{p/2} ≤ C M^{p/2} + Γ` (`casm_remainder`; coefficient
   one on `Γ`);
4. `μ_T` vanishes outside `P(0,1)`, and for an unavailable or (for a fixed family) disallowed type
   `A_{T,i} = ∅`, so `μ_T = 0`;
5. the actual supports lie in `(⋃_i A_{T,i}) ∩ P̄(0,1)` (closure of a set inside a closed set),
   and the support bundle follows by finite summation (`casm_supportBounds`) with
   `count · C_c ≤ C`.

No packing, content, covering or growth of the constructed supports is assumed: these are
derived from the hypotheses `PCarrier` and `TypedSplit`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## Retained sets `⋃_i region_i ∩ A_i` -/

/-- The retained set `⋃_i region_i ∩ A_i` of a finite family of regions and pieces. -/
def casmRetained {n c : ℕ} (region A : Fin c → Set (Space n)) : Set (Space n) :=
  ⋃ i, region i ∩ A i

theorem casm_retained_measurable {n c : ℕ} {region A : Fin c → Set (Space n)}
    (hr : ∀ i, MeasurableSet (region i)) (hA : ∀ i, IsCompact (A i)) :
    MeasurableSet (casmRetained region A) :=
  MeasurableSet.iUnion fun i => (hr i).inter (hA i).isClosed.measurableSet

theorem casm_retained_subset {n c : ℕ} {region : Fin c → Set (Space n)}
    (A : Fin c → Set (Space n)) {B : Set (Space n)} (h : ∀ i, region i ⊆ B) :
    casmRetained region A ⊆ B :=
  iUnion_subset fun i => inter_subset_left.trans (h i)

theorem casm_retained_subset_iUnion {n c : ℕ} (region A : Fin c → Set (Space n)) :
    casmRetained region A ⊆ ⋃ i, A i :=
  iUnion_mono fun _ => inter_subset_right

theorem casm_retained_eq_empty {n c : ℕ} (region : Fin c → Set (Space n))
    {A : Fin c → Set (Space n)} (h : ∀ i, A i = ∅) : casmRetained region A = ∅ :=
  iUnion_eq_empty.mpr fun i => by rw [h i, inter_empty]

theorem casm_retained_disjoint {n c : ℕ} {region AH AV : Fin c → Set (Space n)}
    (hreg : ∀ i j, i ≠ j → Disjoint (region i) (region j))
    (hA : ∀ i, Disjoint (AH i) (AV i)) :
    Disjoint (casmRetained region AH) (casmRetained region AV) := by
  unfold casmRetained
  rw [Set.disjoint_iUnion_left]
  intro i
  rw [Set.disjoint_iUnion_right]
  intro j
  by_cases hij : i = j
  · subst hij
    exact (hA i).mono inter_subset_right inter_subset_right
  · exact (hreg i j hij).mono inter_subset_left inter_subset_left

/-- The actual support of a retained restriction lies in the compact pieces and in `P̄(0,1)`. -/
theorem casm_support_subset {n c : ℕ} (μ : Measure (Space n)) {region A : Fin c → Set (Space n)}
    (hA : ∀ i, IsCompact (A i)) (hball : casmRetained region A ⊆ Metric.ball (point 0 0) 1) :
    (μ.restrict (casmRetained region A)).support ⊆
      (⋃ i, A i) ∩ Metric.closedBall (point 0 0) 1 :=
  support_restrict_subset_of_isClosed μ
    (subset_inter (casm_retained_subset_iUnion region A)
      (hball.trans Metric.ball_subset_closedBall))
    ((isClosed_iUnion_of_finite fun i => (hA i).isClosed).inter Metric.isClosed_closedBall)

/-- `μ = μ⌊(H ∪ V)ᶜ + μ⌊H + μ⌊V` for disjoint Borel `H`, `V`. -/
theorem casm_measure_eq {n : ℕ} (μ : Measure (Space n)) {H V : Set (Space n)}
    (hHV : Disjoint H V) (hH : MeasurableSet H) (hV : MeasurableSet V) :
    μ = μ.restrict (H ∪ V)ᶜ + μ.restrict H + μ.restrict V := by
  rw [add_assoc, ← Measure.restrict_union hHV hV, add_comm,
    Measure.restrict_add_restrict_compl (hH.union hV)]

theorem casm_restrict_compl_ball_eq_zero {n : ℕ} (μ : Measure (Space n)) {E : Set (Space n)}
    (hE : E ⊆ Metric.ball (point 0 0) 1) : μ.restrict E (Metric.ball (point 0 0) 1)ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_ball.compl]
  exact measure_mono_null (fun z hz => absurd (hE hz.2) hz.1) measure_empty

/-- The regions of a localization lie in the open unit ball. -/
theorem casm_region_subset_ball {n k N : ℕ} {T : FamilyKind} {p M : ℝ} {μ : Measure (Space n)}
    (S : PLocalization μ k T p M N) (i : Fin S.count) :
    S.region i ⊆ Metric.ball (point 0 0) 1 := by
  intro z hz
  have hgood : z ∈ pGoodSet μ k T p M := by
    rw [← S.cover]
    exact mem_iUnion.mpr ⟨i, hz⟩
  exact hgood.1

/-! ## The assembly -/

/-- **Finite assembly**: the statement of `exists_assembled_p_decomposition`. -/
theorem casm_exists_assembled_p_decomposition (n : ℕ) (_hn : 1 ≤ n) (p : ℝ) (_hp : 2 ≤ p)
    (N : ℕ) (Cc : ℝ) (hCc : 0 < Cc) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 < M → 0 ≤ Γ →
      μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyS μ k T p 2 z}) ≤
        ENNReal.ofReal Γ →
      ∀ (S : PLocalization μ k T p M N)
        (K : ∀ i : Fin S.count, PCarrier (μ.restrict (S.region i)) k T p M Cc)
        (_D : ∀ i : Fin S.count, TypedSplit k T (K i).set),
        ∃ μplus μH μV : Measure (Space n),
          IsBetaPDecomposition k T C (point 0 0) 1 (C * M ^ (p / 2) + Γ) μ μplus μH μV := by
  have hNCc : 0 ≤ (N : ℝ) * Cc := mul_nonneg (Nat.cast_nonneg N) hCc.le
  refine ⟨(N : ℝ) * Cc + 1, by linarith, ?_⟩
  intro k _hk _hkn T _hT μ _hμ _hreg M Γ hM hΓ hbad S K D
  have hm0 : 0 < M ^ (p / 2) := Real.rpow_pos_of_pos hM _
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hε : 0 < M ^ (p / 2) / ((N : ℝ) + 1) := div_pos hm0 hN1
  -- 1. compact inner approximation of each typing
  choose AH AV hAHc hAVc hAHsub hAVsub hAloss using fun i : Fin S.count =>
    casm_compactApproximation (μ.restrict (S.region i)) (S.finite i) (S.innerRegular i) (D i)
      (M ^ (p / 2) / ((N : ℝ) + 1)) hε
  -- per-piece loss: carrier loss plus compactification allowance
  have hloss : ∀ i, μ.restrict (S.region i) (AH i ∪ AV i)ᶜ ≤
      ENNReal.ofReal (Cc * M ^ (p / 2) + M ^ (p / 2) / ((N : ℝ) + 1)) := by
    intro i
    calc μ.restrict (S.region i) (AH i ∪ AV i)ᶜ
        ≤ μ.restrict (S.region i) ((K i).setᶜ ∪ ((K i).set \ (AH i ∪ AV i))) := by
          refine measure_mono fun x hx => ?_
          by_cases hxK : x ∈ (K i).set
          · exact Or.inr ⟨hxK, hx⟩
          · exact Or.inl hxK
      _ ≤ μ.restrict (S.region i) (K i).setᶜ +
            μ.restrict (S.region i) ((K i).set \ (AH i ∪ AV i)) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Cc * M ^ (p / 2)) + ENNReal.ofReal (M ^ (p / 2) / ((N : ℝ) + 1)) :=
          add_le_add (K i).loss (hAloss i)
      _ = ENNReal.ofReal (Cc * M ^ (p / 2) + M ^ (p / 2) / ((N : ℝ) + 1)) :=
          (ENNReal.ofReal_add (mul_nonneg hCc.le hm0.le) hε.le).symm
  -- 2. the retained sets
  have hregion : ∀ i, S.region i ⊆ Metric.ball (point 0 0) 1 := casm_region_subset_ball S
  have hEHm := casm_retained_measurable S.measurable hAHc
  have hEVm := casm_retained_measurable S.measurable hAVc
  have hEHball := casm_retained_subset AH hregion
  have hEVball := casm_retained_subset AV hregion
  have hdisj := casm_retained_disjoint S.disjoint fun i =>
    (D i).disjoint.mono (hAHsub i) (hAVsub i)
  -- 3. the remainder and the constant `N C_c + 1`
  have hrem := casm_remainder μ S AH AV Γ _ hbad hloss
  have hℓ0 : 0 ≤ Cc * M ^ (p / 2) + M ^ (p / 2) / ((N : ℝ) + 1) :=
    add_nonneg (mul_nonneg hCc.le hm0.le) hε.le
  have hNε : (N : ℝ) * (M ^ (p / 2) / ((N : ℝ) + 1)) ≤ M ^ (p / 2) := by
    rw [mul_div_assoc', div_le_iff₀ hN1]
    nlinarith [hm0.le]
  have hNℓ : (N : ℝ) * (Cc * M ^ (p / 2) + M ^ (p / 2) / ((N : ℝ) + 1)) ≤
      ((N : ℝ) * Cc + 1) * M ^ (p / 2) := by
    calc (N : ℝ) * (Cc * M ^ (p / 2) + M ^ (p / 2) / ((N : ℝ) + 1))
        = (N : ℝ) * Cc * M ^ (p / 2) + (N : ℝ) * (M ^ (p / 2) / ((N : ℝ) + 1)) := by ring
      _ ≤ (N : ℝ) * Cc * M ^ (p / 2) + M ^ (p / 2) := by linarith
      _ = ((N : ℝ) * Cc + 1) * M ^ (p / 2) := by ring
  have hCm0 : 0 ≤ ((N : ℝ) * Cc + 1) * M ^ (p / 2) := mul_nonneg (by linarith) hm0.le
  have hcount : (S.count : ℝ) * Cc ≤ (N : ℝ) * Cc + 1 := by
    have h1 : (S.count : ℝ) ≤ (N : ℝ) := by exact_mod_cast S.count_le
    have h2 : (S.count : ℝ) * Cc ≤ (N : ℝ) * Cc := mul_le_mul_of_nonneg_right h1 hCc.le
    linarith
  refine ⟨μ.restrict (casmRetained S.region AH ∪ casmRetained S.region AV)ᶜ,
    μ.restrict (casmRetained S.region AH), μ.restrict (casmRetained S.region AV), ?_⟩
  exact {
    measure_eq := casm_measure_eq μ hdisj hEHm hEVm
    remainder_bound := by
      rw [Measure.restrict_apply measurableSet_ball]
      refine hrem.trans ?_
      calc ENNReal.ofReal Γ + ∑ _i : Fin S.count,
            ENNReal.ofReal (Cc * M ^ (p / 2) + M ^ (p / 2) / ((N : ℝ) + 1))
          ≤ ENNReal.ofReal Γ + ENNReal.ofReal (((N : ℝ) * Cc + 1) * M ^ (p / 2)) :=
            add_le_add le_rfl (sum_fin_ofReal_le S.count_le hℓ0 hNℓ)
        _ = ENNReal.ofReal (((N : ℝ) * Cc + 1) * M ^ (p / 2) + Γ) := by
            rw [ENNReal.ofReal_add hCm0 hΓ]
            exact add_comm _ _
    horizontal_carried := casm_restrict_compl_ball_eq_zero μ hEHball
    vertical_carried := casm_restrict_compl_ball_eq_zero μ hEVball
    horizontal_unavailable := fun h => by
      rw [(casm_retained_eq_empty S.region fun i =>
        subset_eq_empty (hAHsub i) ((D i).horizontal_unavailable h)), Measure.restrict_empty]
    vertical_unavailable := fun h => by
      rw [(casm_retained_eq_empty S.region fun i =>
        subset_eq_empty (hAVsub i) ((D i).vertical_unavailable h)), Measure.restrict_empty]
    horizontal_disallowed := fun hT' => by
      rw [(casm_retained_eq_empty S.region fun i =>
        subset_eq_empty (hAHsub i) ((D i).family.2 hT')), Measure.restrict_empty]
    vertical_disallowed := fun hT' => by
      rw [(casm_retained_eq_empty S.region fun i =>
        subset_eq_empty (hAVsub i) ((D i).family.1 hT')), Measure.restrict_empty]
    supports := casm_supportBounds (fun i => μ.restrict (S.region i)) S.center hCc.le
      S.support_small K D AH AV hAHc hAVc hAHsub hAVsub
      (μ.restrict (casmRetained S.region AH)).support
      (μ.restrict (casmRetained S.region AV)).support
      Measure.isClosed_support Measure.isClosed_support
      (casm_support_subset μ hAHc hEHball) (casm_support_subset μ hAVc hEVball)
      _ hcount }

end ParabolicRectifiability.BetaP
