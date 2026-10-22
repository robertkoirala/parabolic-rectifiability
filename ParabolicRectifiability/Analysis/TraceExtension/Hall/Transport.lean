import ParabolicRectifiability.Basic

/-!
# Real-capacity transport and weak limits of bounded densities

The two analytic inputs of the real-capacity Hall lemma (see `HallAllocation`).

* `exists_transport_of_hall_condition_proof` (finite real-capacity transport).
  The feasible subflows (nonnegative, carried by the incidence, below every demand and
  capacity) form a nonempty compact set, so some subflow has maximal total value. If a
  demand `j₀` were not met, let `R` be the requests reachable from `j₀` along
  alternating paths (an incidence edge forward, a positive-flow edge backward). Every
  cell adjacent to `R` is saturated: otherwise a positive multiple of an alternating
  direction (`exists_alternating_direction`) increases the value. Summing over the cut
  then contradicts Hall's inequality for `R`. No augmenting algorithm is used, and zero
  capacities, zero demands and empty types are allowed.
* `exists_weakly_convergent_density_subseq_proof` (weak sequential compactness of
  bounded densities), in two halves:
  - *dense-test diagonal convergence* (`exists_subseq_tendsto_pairing`): pairing with a
    function bounded by `M` is a functional on `L¹(σ)` of norm at most `M`
    (`pairingCLM`); since `L¹(σ)` is separable, the sequential Banach–Alaoglu theorem
    (`WeakDual.isSeqCompact_closedBall`, the diagonal argument over a dense sequence of
    tests) gives a subsequence converging against every `L¹` test to a functional `ℓ`;
  - *density representation* (`exists_density_of_continuousLinearMap`): `s ↦ ℓ(1_s)` is
    finitely additive and dominated by `M σ`, hence a finite measure absolutely continuous
    with respect to `σ`; its Radon–Nikodym derivative is at most `M` almost everywhere,
    its truncation at `M` is a density with values in `[0, M]` everywhere, and both sides
    agree on indicators, hence on all of `L¹`.

  `A` can be negative only when `X` is empty; the proof works with `max A 0`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

namespace HallTransport

/-! ## Real-capacity transport -/

section Transport

variable {J T : Type*} [Fintype J] [Fintype T]

/-- Feasible subflows: nonnegative, carried by the incidence, with every row sum at most
its demand and every column sum at most its capacity. -/
def IsSubflow (adj : J → T → Prop) (w : J → ℝ) (κ : T → ℝ) (x : J → T → ℝ) : Prop :=
  (∀ j t, 0 ≤ x j t) ∧ (∀ j t, ¬ adj j t → x j t = 0) ∧ (∀ j, ∑ t, x j t ≤ w j) ∧
    ∀ t, ∑ j, x j t ≤ κ t

/-- The feasible subflows form a compact set (a closed subset of a box). -/
theorem isCompact_setOf_isSubflow (adj : J → T → Prop) (w : J → ℝ) (κ : T → ℝ) :
    IsCompact {x | IsSubflow adj w κ x} := by
  refine (isCompact_Icc (a := (0 : J → T → ℝ)) (b := fun j _ => w j)).of_isClosed_subset
    ?_ ?_
  · have hset : {x | IsSubflow adj w κ x} =
        (⋂ j, ⋂ t, {x : J → T → ℝ | 0 ≤ x j t}) ∩ ((⋂ j, ⋂ t, {x | ¬ adj j t → x j t = 0}) ∩
          ((⋂ j, {x | ∑ t, x j t ≤ w j}) ∩ ⋂ t, {x | ∑ j, x j t ≤ κ t})) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, IsSubflow]
    rw [hset]
    have h₁ : IsClosed (⋂ j, ⋂ t, {x : J → T → ℝ | 0 ≤ x j t}) :=
      isClosed_iInter fun j => isClosed_iInter fun t =>
        isClosed_le continuous_const ((continuous_apply t).comp (continuous_apply j))
    have h₂ : IsClosed (⋂ j, ⋂ t, {x : J → T → ℝ | ¬ adj j t → x j t = 0}) :=
      isClosed_iInter fun j => isClosed_iInter fun t => isClosed_imp isOpen_const
        (isClosed_eq ((continuous_apply t).comp (continuous_apply j)) continuous_const)
    have h₃ : IsClosed (⋂ j, {x : J → T → ℝ | ∑ t, x j t ≤ w j}) :=
      isClosed_iInter fun j => isClosed_le
        (continuous_finsetSum _ fun t _ => (continuous_apply t).comp (continuous_apply j))
        continuous_const
    have h₄ : IsClosed (⋂ t, {x : J → T → ℝ | ∑ j, x j t ≤ κ t}) :=
      isClosed_iInter fun t => isClosed_le
        (continuous_finsetSum _ fun j _ => (continuous_apply t).comp (continuous_apply j))
        continuous_const
    exact h₁.inter (h₂.inter (h₃.inter h₄))
  · rintro x ⟨h0, -, hrow, -⟩
    refine ⟨fun j t => h0 j t, fun j t => ?_⟩
    exact (Finset.single_le_sum (fun t _ => h0 j t) (Finset.mem_univ t)).trans (hrow j)

variable [DecidableEq J] [DecidableEq T]

/-- The unit flow on the single edge `(i₀, s₀)`. -/
def unitFlow (i₀ : J) (s₀ : T) : J → T → ℝ :=
  fun i s => if i = i₀ then (if s = s₀ then 1 else 0) else 0

omit [Fintype J] [Fintype T] in
theorem unitFlow_nonneg (i₀ : J) (s₀ : T) (i : J) (s : T) : 0 ≤ unitFlow i₀ s₀ i s := by
  unfold unitFlow
  split_ifs <;> norm_num

omit [Fintype J] [Fintype T] in
theorem unitFlow_eq_zero {i₀ : J} {s₀ : T} {i : J} {s : T} (h : ¬ (i = i₀ ∧ s = s₀)) :
    unitFlow i₀ s₀ i s = 0 := by
  unfold unitFlow
  split_ifs with h₁ h₂
  · exact absurd ⟨h₁, h₂⟩ h
  · rfl
  · rfl

omit [Fintype J] in
theorem sum_unitFlow_row (i₀ : J) (s₀ : T) (i : J) :
    ∑ s, unitFlow i₀ s₀ i s = if i = i₀ then 1 else 0 := by
  unfold unitFlow
  split_ifs <;> simp

omit [Fintype T] in
theorem sum_unitFlow_col (i₀ : J) (s₀ : T) (s : T) :
    ∑ i, unitFlow i₀ s₀ i s = if s = s₀ then 1 else 0 := by
  unfold unitFlow
  by_cases hs : s = s₀ <;> simp [hs]

/-- Alternating directions. If `j` is reachable from `j₀` along alternating steps
`a → b` (an incidence edge `(a, t)` and positive flow on `(b, t)`), there is a direction
`y` carried by the incidence, negative only where `x` is positive, with zero column sums
and row sums `1_{j₀} - 1_j`. -/
theorem exists_alternating_direction {adj : J → T → Prop} {x : J → T → ℝ}
    (hx : ∀ j t, ¬ adj j t → x j t = 0) {j₀ j : J}
    (hj : Relation.ReflTransGen (fun a b => ∃ t, adj a t ∧ 0 < x b t) j₀ j) :
    ∃ y : J → T → ℝ, (∀ i s, ¬ adj i s → y i s = 0) ∧ (∀ i s, y i s < 0 → 0 < x i s) ∧
      (∀ i, ∑ s, y i s = (if i = j₀ then 1 else 0) - (if i = j then 1 else 0)) ∧
      ∀ s, ∑ i, y i s = 0 := by
  induction hj with
  | refl =>
    exact ⟨0, fun _ _ _ => rfl, fun _ _ h => absurd h (lt_irrefl 0), fun i => by simp,
      fun s => by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨y, hyadj, hyneg, hyrow, hycol⟩ := ih
    obtain ⟨t, hbt, hct⟩ := hbc
    have hct' : adj c t := by
      by_contra h
      rw [hx c t h] at hct
      exact lt_irrefl 0 hct
    refine ⟨fun i s => y i s + unitFlow b t i s - unitFlow c t i s, ?_, ?_, ?_, ?_⟩
    · intro i s his
      have h₁ : unitFlow b t i s = 0 :=
        unitFlow_eq_zero fun h => his (h.1 ▸ h.2 ▸ hbt)
      have h₂ : unitFlow c t i s = 0 :=
        unitFlow_eq_zero fun h => his (h.1 ▸ h.2 ▸ hct')
      simp only [hyadj i s his, h₁, h₂, sub_zero, add_zero]
    · intro i s hneg
      by_cases hcs : i = c ∧ s = t
      · obtain ⟨rfl, rfl⟩ := hcs
        exact hct
      · have h₂ : unitFlow c t i s = 0 := unitFlow_eq_zero hcs
        have h₁ := unitFlow_nonneg b t i s
        simp only [h₂, sub_zero] at hneg
        exact hyneg i s (by linarith)
    · intro i
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hyrow, sum_unitFlow_row]
      ring
    · intro s
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hycol, sum_unitFlow_col]
      ring

end Transport

end HallTransport

open HallTransport

open Classical in
/-- **Real-capacity transport** (the finite combinatorial core of the Hall lemma):
real-capacity supply–demand. Finite requests `w_j ≥ 0` and cells with
capacities `κ_t ≥ 0`, incidence `adj`; if every finite request set `I` satisfies
`Σ_I w ≤ Σ_{t adjacent to I} κ_t`, there is a nonnegative transport supported on
the incidence that meets every demand and respects every capacity.

Proof: a subflow of maximal value (compactness) meets every demand, by the residual-cut
argument described in the module docstring. -/
theorem exists_transport_of_hall_condition_proof {J T : Type*} [Fintype J] [Fintype T]
    (adj : J → T → Prop) (w : J → ℝ) (κ : T → ℝ) (hw : ∀ j, 0 ≤ w j) (hκ : ∀ t, 0 ≤ κ t)
    (hH : ∀ I : Finset J,
      ∑ j ∈ I, w j ≤ ∑ t ∈ Finset.univ.filter (fun t => ∃ j ∈ I, adj j t), κ t) :
    ∃ x : J → T → ℝ, (∀ j t, 0 ≤ x j t) ∧ (∀ j t, ¬ adj j t → x j t = 0) ∧
      (∀ j, ∑ t, x j t = w j) ∧ ∀ t, ∑ j, x j t ≤ κ t := by
  have h0K : (0 : J → T → ℝ) ∈ {x | IsSubflow adj w κ x} :=
    ⟨fun _ _ => le_rfl, fun _ _ _ => rfl, fun j => by simpa using hw j,
      fun t => by simpa using hκ t⟩
  obtain ⟨x, hxK, hxmax⟩ := (isCompact_setOf_isSubflow adj w κ).exists_isMaxOn ⟨0, h0K⟩
    (f := fun x => ∑ j, ∑ t, x j t) (by fun_prop : Continuous _).continuousOn
  obtain ⟨hx0, hxadj, hxrow, hxcol⟩ := hxK
  refine ⟨x, hx0, hxadj, fun j₀ => ?_, hxcol⟩
  by_contra hne
  have hlt : ∑ t, x j₀ t < w j₀ := lt_of_le_of_ne (hxrow j₀) hne
  -- Every cell adjacent to a request reachable from `j₀` is saturated.
  have hsat : ∀ j t, Relation.ReflTransGen (fun a b => ∃ t, adj a t ∧ 0 < x b t) j₀ j →
      adj j t → ∑ i, x i t = κ t := by
    intro j t hj hjt
    by_contra hne'
    have hlt' : ∑ i, x i t < κ t := lt_of_le_of_ne (hxcol t) hne'
    obtain ⟨y, hyadj, hyneg, hyrow, hycol⟩ := exists_alternating_direction hxadj hj
    let z : J → T → ℝ := fun i s => y i s + unitFlow j t i s
    have hzadj : ∀ i s, ¬ adj i s → z i s = 0 := by
      intro i s his
      have h₁ : unitFlow j t i s = 0 := unitFlow_eq_zero fun h => his (h.1 ▸ h.2 ▸ hjt)
      simp only [z, hyadj i s his, h₁, add_zero]
    have hzneg : ∀ i s, z i s < 0 → 0 < x i s := by
      intro i s hneg
      have h₁ := unitFlow_nonneg j t i s
      exact hyneg i s (by simp only [z] at hneg; linarith)
    have hzrow : ∀ i, ∑ s, z i s = if i = j₀ then 1 else 0 := by
      intro i
      simp only [z, Finset.sum_add_distrib, hyrow, sum_unitFlow_row]
      ring
    have hzcol : ∀ s, ∑ i, z i s = if s = t then 1 else 0 := by
      intro s
      simp only [z, Finset.sum_add_distrib, hycol, sum_unitFlow_col, zero_add]
    -- A small positive step along `z` stays feasible.
    have h₁ : ∀ i s, ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 ≤ x i s + δ * z i s := by
      intro i s
      by_cases hzi : 0 ≤ z i s
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact add_nonneg (hx0 i s) (mul_nonneg (le_of_lt hδ) hzi)
      · have hxi : 0 < x i s := hzneg i s (lt_of_not_ge hzi)
        have hT : Tendsto (fun δ : ℝ => x i s + δ * z i s) (𝓝[>] 0) (𝓝 (x i s)) := by
          have hc : Continuous fun δ : ℝ => x i s + δ * z i s := by fun_prop
          simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
        exact (hT.eventually_const_lt hxi).mono fun δ hδ => hδ.le
    have h₂ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∑ s, x j₀ s + δ < w j₀ := by
      have hc : Continuous fun δ : ℝ => ∑ s, x j₀ s + δ := by fun_prop
      have hT : Tendsto (fun δ : ℝ => ∑ s, x j₀ s + δ) (𝓝[>] 0) (𝓝 (∑ s, x j₀ s)) := by
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      exact hT.eventually_lt_const hlt
    have h₃ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∑ i, x i t + δ < κ t := by
      have hc : Continuous fun δ : ℝ => ∑ i, x i t + δ := by fun_prop
      have hT : Tendsto (fun δ : ℝ => ∑ i, x i t + δ) (𝓝[>] 0) (𝓝 (∑ i, x i t)) := by
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      exact hT.eventually_lt_const hlt'
    obtain ⟨δ, ⟨hδ0, hδrow, hδcol⟩, hδpos⟩ :=
      (((eventually_all.2 fun i => eventually_all.2 fun s => h₁ i s).and (h₂.and h₃)).and
        self_mem_nhdsWithin).exists
    have hδpos' : (0 : ℝ) < δ := hδpos
    have hrow' : ∀ i, ∑ s, (x i s + δ * z i s) = ∑ s, x i s + δ * (if i = j₀ then 1 else 0) := by
      intro i
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzrow]
    have hcol' : ∀ s, ∑ i, (x i s + δ * z i s) = ∑ i, x i s + δ * (if s = t then 1 else 0) := by
      intro s
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzcol]
    have hmem : (fun i s => x i s + δ * z i s) ∈ {x | IsSubflow adj w κ x} := by
      refine ⟨hδ0, fun i s his => ?_, fun i => ?_, fun s => ?_⟩
      · simp only [hxadj i s his, hzadj i s his, mul_zero, add_zero]
      · rw [hrow']
        by_cases hi : i = j₀
        · subst hi
          simpa using hδrow.le
        · simpa [hi] using hxrow i
      · rw [hcol']
        by_cases hs : s = t
        · subst hs
          simpa using hδcol.le
        · simpa [hs] using hxcol s
    have hle : ∑ i, ∑ s, (x i s + δ * z i s) ≤ ∑ i, ∑ s, x i s := hxmax hmem
    rw [Finset.sum_congr rfl fun i _ => hrow' i, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ j₀] at hle
    simp only [Finset.mem_univ, ↓reduceIte, mul_one] at hle
    linarith
  -- The cut at the requests reachable from `j₀` violates Hall's inequality.
  let R : Finset J :=
    Finset.univ.filter (fun j => Relation.ReflTransGen (fun a b => ∃ t, adj a t ∧ 0 < x b t) j₀ j)
  have hmemR : ∀ j, j ∈ R ↔
      Relation.ReflTransGen (fun a b => ∃ t, adj a t ∧ 0 < x b t) j₀ j := by
    intro j
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
  have hj₀R : j₀ ∈ R := (hmemR j₀).2 Relation.ReflTransGen.refl
  obtain ⟨N, hN, hHR⟩ : ∃ N : Finset T, (∀ t, t ∈ N ↔ ∃ j ∈ R, adj j t) ∧
      ∑ j ∈ R, w j ≤ ∑ t ∈ N, κ t :=
    ⟨_, fun t => by simp only [Finset.mem_filter, Finset.mem_univ, true_and], hH R⟩
  have hclosed : ∀ t ∈ N, ∀ i, i ∉ R → x i t = 0 := by
    intro t ht i hi
    obtain ⟨j, hjR, hjt⟩ := (hN t).1 ht
    by_contra hne'
    have hpos : 0 < x i t := lt_of_le_of_ne (hx0 i t) (Ne.symm hne')
    exact hi ((hmemR i).2 (((hmemR j).1 hjR).tail ⟨t, hjt, hpos⟩))
  have hout : ∀ i ∈ R, ∀ t ∉ N, x i t = 0 := fun i hi t ht =>
    hxadj i t fun hit => ht ((hN t).2 ⟨i, hi, hit⟩)
  have hsatN : ∀ t ∈ N, ∑ i, x i t = κ t := by
    intro t ht
    obtain ⟨j, hjR, hjt⟩ := (hN t).1 ht
    exact hsat j t ((hmemR j).1 hjR) hjt
  have key : ∑ t ∈ N, κ t < ∑ t ∈ N, κ t :=
    calc ∑ t ∈ N, κ t = ∑ t ∈ N, ∑ i, x i t :=
          Finset.sum_congr rfl fun t ht => (hsatN t ht).symm
      _ = ∑ t ∈ N, ∑ i ∈ R, x i t :=
          Finset.sum_congr rfl fun t ht =>
            (Finset.sum_subset (Finset.subset_univ R) fun i _ hi => hclosed t ht i hi).symm
      _ = ∑ i ∈ R, ∑ t ∈ N, x i t := Finset.sum_comm
      _ = ∑ i ∈ R, ∑ t, x i t :=
          Finset.sum_congr rfl fun i hi =>
            Finset.sum_subset (Finset.subset_univ N) fun t _ ht => hout i hi t ht
      _ < ∑ i ∈ R, w i := Finset.sum_lt_sum (fun i _ => hxrow i) ⟨j₀, hj₀R, hlt⟩
      _ ≤ ∑ t ∈ N, κ t := hHR
  exact lt_irrefl _ key

namespace HallTransport

/-! ## Weak limits of bounded densities -/

section WeakLimit

variable {X : Type*} [MeasurableSpace X] {σ : Measure X}

/-- The pairing of `L¹(σ)` with a function `F` bounded by `M`, as a continuous linear
functional of norm at most `M` (when `0 ≤ M`). -/
def pairingCLM (σ : Measure X) (F : X → ℝ) (M : ℝ) (hF : AEStronglyMeasurable F σ)
    (hFM : ∀ x, ‖F x‖ ≤ M) : Lp ℝ 1 σ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ x, F x * g x ∂σ
      map_add' := fun f g => by
        have hf := (L1.integrable_coeFn f).bdd_mul hF (ae_of_all _ hFM)
        have hg := (L1.integrable_coeFn g).bdd_mul hF (ae_of_all _ hFM)
        rw [← integral_add hf hg]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f g] with x hx
        rw [hx, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul]
        ring }
    M fun g => by
      change ‖∫ x, F x * g x ∂σ‖ ≤ M * ‖g‖
      calc ‖∫ x, F x * g x ∂σ‖ ≤ ∫ x, M * ‖g x‖ ∂σ := by
            refine norm_integral_le_of_norm_le ((L1.integrable_coeFn g).norm.const_mul M)
              (ae_of_all _ fun x => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (hFM x) (norm_nonneg _)
        _ = M * ‖g‖ := by rw [integral_const_mul, L1.norm_eq_integral_norm]

theorem pairingCLM_apply (F : X → ℝ) (M : ℝ) (hF : AEStronglyMeasurable F σ)
    (hFM : ∀ x, ‖F x‖ ≤ M) (g : Lp ℝ 1 σ) :
    pairingCLM σ F M hF hFM g = ∫ x, F x * g x ∂σ := rfl

theorem norm_pairingCLM_le (F : X → ℝ) {M : ℝ} (hM : 0 ≤ M) (hF : AEStronglyMeasurable F σ)
    (hFM : ∀ x, ‖F x‖ ≤ M) : ‖pairingCLM σ F M hF hFM‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ hM _

/-- Pairing with the indicator of a finite-measure set is the set integral. -/
theorem integral_mul_indicatorConstLp_one (F : X → ℝ) {s : Set X} (hs : MeasurableSet s)
    (hμs : σ s ≠ ∞) :
    ∫ x, F x * indicatorConstLp 1 hs hμs (1 : ℝ) x ∂σ = ∫ x in s, F x ∂σ := by
  rw [← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [(indicatorConstLp_coeFn :
    ⇑(indicatorConstLp 1 hs hμs (1 : ℝ)) =ᵐ[σ] s.indicator fun _ => (1 : ℝ))] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem indicatorConstLp_eq_smul_one {s : Set X} (hs : MeasurableSet s) (hμs : σ s ≠ ∞)
    (c : ℝ) : indicatorConstLp 1 hs hμs c = c • indicatorConstLp 1 hs hμs (1 : ℝ) := by
  refine Lp.ext ?_
  filter_upwards [(indicatorConstLp_coeFn :
      ⇑(indicatorConstLp 1 hs hμs c) =ᵐ[σ] s.indicator fun _ => c),
    Lp.coeFn_smul c (indicatorConstLp 1 hs hμs (1 : ℝ)),
    (indicatorConstLp_coeFn :
      ⇑(indicatorConstLp 1 hs hμs (1 : ℝ)) =ᵐ[σ] s.indicator fun _ => (1 : ℝ))]
    with x h₁ h₂ h₃
  rw [h₁, h₂, Pi.smul_apply, h₃]
  by_cases hx : x ∈ s <;> simp [hx]

/-- **Dense-test diagonal convergence.** On a measure space with separable `L¹`, functions
bounded by `M` have a subsequence whose pairings with every `L¹` test converge; the limit
is a continuous linear functional of norm at most `M`. This is the sequential
Banach–Alaoglu theorem for the separable space `L¹(σ)` (`WeakDual.isSeqCompact_closedBall`,
proved by the diagonal argument over a dense sequence of tests). -/
theorem exists_subseq_tendsto_pairing [TopologicalSpace.SeparableSpace (Lp ℝ 1 σ)]
    {M : ℝ} (hM : 0 ≤ M) (h : ℕ → X → ℝ) (hm : ∀ n, AEStronglyMeasurable (h n) σ)
    (hb : ∀ n x, ‖h n x‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (ℓ : Lp ℝ 1 σ →L[ℝ] ℝ), StrictMono φ ∧ ‖ℓ‖ ≤ M ∧
      ∀ g : Lp ℝ 1 σ, Tendsto (fun n => ∫ x, h (φ n) x * g x ∂σ) atTop (𝓝 (ℓ g)) := by
  let T : ℕ → WeakDual ℝ (Lp ℝ 1 σ) := fun n =>
    StrongDual.toWeakDual (pairingCLM σ (h n) M (hm n) (hb n))
  have hT : ∀ n, T n ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ (Lp ℝ 1 σ)) M := by
    intro n
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    exact norm_pairingCLM_le (h n) hM (hm n) (hb n)
  obtain ⟨ℓ, hℓ, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ (Lp ℝ 1 σ) 0 M hT
  refine ⟨φ, WeakDual.toStrongDual ℓ, hφ, ?_, fun g => ?_⟩
  · simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hℓ
  · exact ((WeakDual.eval_continuous g).tendsto ℓ).comp hlim

/-- **Density representation.** A continuous linear functional on `L¹(σ)`, `σ` finite,
with `0 ≤ ℓ(1_s) ≤ M σ(s)` on measurable sets is integration against a measurable density
with values in `[0, M]` everywhere. The set function `s ↦ ℓ(1_s)` is a finite measure
absolutely continuous with respect to `σ` (finitely additive, dominated by `M σ`); its
Radon–Nikodym derivative is at most `M` almost everywhere, and truncation at `M` makes the
bounds hold everywhere. Both sides are continuous in `g` and agree on indicators. -/
theorem exists_density_of_continuousLinearMap [IsFiniteMeasure σ] (ℓ : Lp ℝ 1 σ →L[ℝ] ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hpos : ∀ s (hs : MeasurableSet s), 0 ≤ ℓ (indicatorConstLp 1 hs (measure_ne_top σ s) 1))
    (hle : ∀ s (hs : MeasurableSet s),
      ℓ (indicatorConstLp 1 hs (measure_ne_top σ s) 1) ≤ M * σ.real s) :
    ∃ h₀ : X → ℝ, Measurable h₀ ∧ (∀ x, 0 ≤ h₀ x ∧ h₀ x ≤ M) ∧
      ∀ g : Lp ℝ 1 σ, ℓ g = ∫ x, h₀ x * g x ∂σ := by
  classical
  -- The set function `ν s = ℓ(1_s)`.
  let I : Set X → Lp ℝ 1 σ := fun s =>
    if hs : MeasurableSet s then indicatorConstLp 1 hs (measure_ne_top σ s) (1 : ℝ) else 0
  have hI : ∀ s (hs : MeasurableSet s), I s = indicatorConstLp 1 hs (measure_ne_top σ s) 1 :=
    fun s hs => by simp only [I, hs, ↓reduceDIte]
  let ν : Set X → ℝ := fun s => ℓ (I s)
  have hν : ∀ s (hs : MeasurableSet s), ν s = ℓ (indicatorConstLp 1 hs (measure_ne_top σ s) 1) :=
    fun s hs => by simp only [ν, hI s hs]
  have hν_nonneg : ∀ s, MeasurableSet s → 0 ≤ ν s := fun s hs => (hν s hs).symm ▸ hpos s hs
  have hν_le : ∀ s, MeasurableSet s → ν s ≤ M * σ.real s := fun s hs => (hν s hs).symm ▸ hle s hs
  have hν_empty : ν ∅ = 0 := by
    rw [hν ∅ MeasurableSet.empty, indicatorConstLp_empty, map_zero]
  have hν_union : ∀ s t, MeasurableSet s → MeasurableSet t → Disjoint s t →
      ν (s ∪ t) = ν s + ν t := by
    intro s t hs ht hst
    rw [hν _ (hs.union ht), hν s hs, hν t ht, ← map_add]
    congr 1
    exact indicatorConstLp_disjoint_union hs ht (measure_ne_top σ s) (measure_ne_top σ t) hst 1
  -- Countable additivity, from finite additivity and domination by `M σ`.
  have hν_hasSum : ∀ f : ℕ → Set X, (∀ i, MeasurableSet (f i)) →
      Pairwise (Function.onFun Disjoint f) →
      HasSum (fun i => ν (f i)) (ν (⋃ i, f i)) := by
    intro f hf hd
    let U : ℕ → Set X := fun n => ⋃ i ∈ Finset.range n, f i
    have hUm : ∀ n, MeasurableSet (U n) := fun n =>
      Finset.measurableSet_biUnion _ fun i _ => hf i
    have hpartial : ∀ n, ∑ i ∈ Finset.range n, ν (f i) = ν (U n) := by
      intro n
      induction n with
      | zero => simp [U, hν_empty]
      | succ n ih =>
        have hU : U (n + 1) = f n ∪ U n := by
          simp only [U, Finset.range_add_one, Finset.set_biUnion_insert]
        have hdisj : Disjoint (f n) (U n) := by
          simp only [U, Set.disjoint_iUnion_right]
          intro i hi
          exact hd (Finset.mem_range.1 hi).ne'
        rw [Finset.sum_range_succ, ih, hU, hν_union _ _ (hf n) (hUm n) hdisj, add_comm]
    have hmeasU : MeasurableSet (⋃ i, f i) := MeasurableSet.iUnion hf
    have hsub : ∀ n, U n ⊆ ⋃ i, f i := fun n =>
      Set.iUnion₂_subset fun i _ => Set.subset_iUnion f i
    have htail : ∀ n, ν (⋃ i, f i) - ν (U n) = ν ((⋃ i, f i) \ U n) := by
      intro n
      have h := hν_union (U n) ((⋃ i, f i) \ U n) (hUm n) (hmeasU.diff (hUm n))
        Set.disjoint_sdiff_right
      rw [Set.union_sdiff_cancel (hsub n)] at h
      linarith
    -- The tail measures tend to zero.
    have hσ : Tendsto (fun n => σ.real ((⋃ i, f i) \ U n)) atTop (𝓝 0) := by
      have hanti : Antitone fun n => (⋃ i, f i) \ U n := by
        intro m n hmn
        refine Set.sdiff_subset_sdiff_right ?_
        exact Set.biUnion_subset_biUnion_left (by simpa using Finset.range_mono hmn)
      have hInter : (⋂ n, (⋃ i, f i) \ U n) = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
        rw [Set.mem_iInter] at hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hx 0).1
        exact (hx (i + 1)).2 (Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_self i)) hi)
      have h := tendsto_measure_iInter_atTop (μ := σ)
        (fun n => (hmeasU.diff (hUm n)).nullMeasurableSet) hanti ⟨0, measure_ne_top σ _⟩
      rw [hInter, measure_empty] at h
      have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
      simpa only [Function.comp_def, ENNReal.toReal_zero, measureReal_def] using h'
    have hlim : Tendsto (fun n => ν (U n)) atTop (𝓝 (ν (⋃ i, f i))) := by
      have hsq : Tendsto (fun n => ν (⋃ i, f i) - ν (U n)) atTop (𝓝 0) := by
        have hMσ : Tendsto (fun n => M * σ.real ((⋃ i, f i) \ U n)) atTop (𝓝 0) := by
          simpa using hσ.const_mul M
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hMσ
          (fun n => ?_) (fun n => ?_)
        · rw [htail n]
          exact hν_nonneg _ (hmeasU.diff (hUm n))
        · rw [htail n]
          exact hν_le _ (hmeasU.diff (hUm n))
      have := (tendsto_const_nhds (x := ν (⋃ i, f i))).sub hsq
      simpa using this
    refine (hasSum_iff_tendsto_nat_of_nonneg (fun i => hν_nonneg _ (hf i)) _).2 ?_
    simpa only [hpartial] using hlim
  -- The measure `μ s = ν s`, absolutely continuous with respect to `σ`.
  let μ : Measure X := Measure.ofMeasurable (fun s _ => ENNReal.ofReal (ν s))
    (by simp [hν_empty]) fun f hf hd => by
      have h := hν_hasSum f hf hd
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hν_nonneg _ (hf i)) h.summable, h.tsum_eq]
  have hμ : ∀ s, MeasurableSet s → μ s = ENNReal.ofReal (ν s) := fun s hs =>
    Measure.ofMeasurable_apply s hs
  have : IsFiniteMeasure μ := ⟨by rw [hμ _ MeasurableSet.univ]; exact ENNReal.ofReal_lt_top⟩
  have hμσ : μ ≪ σ := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hσs => ?_
    rw [hμ s hs, ENNReal.ofReal_eq_zero]
    have h := hν_le s hs
    rwa [measureReal_def, hσs, ENNReal.toReal_zero, mul_zero] at h
  -- The Radon–Nikodym derivative is at most `M` almost everywhere.
  have hf_le : ∀ᵐ x ∂σ, μ.rnDeriv σ x ≤ ENNReal.ofReal M := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv μ σ)
      fun s hs _ => ?_
    rw [Measure.setLIntegral_rnDeriv' hμσ hs, setLIntegral_const, hμ s hs]
    calc ENNReal.ofReal (ν s) ≤ ENNReal.ofReal (M * σ.real s) :=
          ENNReal.ofReal_le_ofReal (hν_le s hs)
      _ = ENNReal.ofReal M * σ s := by
          rw [ENNReal.ofReal_mul hM, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top σ s)]
  -- The truncated density.
  let h₀ : X → ℝ := fun x => min M (μ.rnDeriv σ x).toReal
  have hh₀m : Measurable h₀ := measurable_const.min (Measure.measurable_rnDeriv μ σ).ennreal_toReal
  have hh₀b : ∀ x, 0 ≤ h₀ x ∧ h₀ x ≤ M := fun x =>
    ⟨le_min hM ENNReal.toReal_nonneg, min_le_left _ _⟩
  have hh₀norm : ∀ x, ‖h₀ x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hh₀b x).1]
    exact (hh₀b x).2
  have hset : ∀ s, MeasurableSet s → ∫ x in s, h₀ x ∂σ = ν s := by
    intro s hs
    have hae : h₀ =ᵐ[σ] fun x => (μ.rnDeriv σ x).toReal := by
      filter_upwards [hf_le] with x hx
      exact min_eq_right (ENNReal.toReal_le_of_le_ofReal hM hx)
    rw [integral_congr_ae (ae_restrict_of_ae hae),
      integral_toReal (Measure.measurable_rnDeriv μ σ).aemeasurable
        (ae_restrict_of_ae (Measure.rnDeriv_lt_top μ σ)),
      Measure.setLIntegral_rnDeriv' hμσ hs, hμ s hs, ENNReal.toReal_ofReal (hν_nonneg s hs)]
  -- Both functionals agree on indicators, hence everywhere.
  let S := pairingCLM σ h₀ M hh₀m.aestronglyMeasurable hh₀norm
  refine ⟨h₀, hh₀m, hh₀b, fun g => ?_⟩
  change ℓ g = S g
  refine Lp.induction (p := 1) ENNReal.one_ne_top (fun g => ℓ g = S g) ?_ ?_ ?_ g
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_smul_one, map_smul, map_smul]
    congr 1
    rw [pairingCLM_apply, integral_mul_indicatorConstLp_one, hset s hs, hν s hs]
  · intro f g _ _ _ hf hg
    simp only [map_add, hf, hg]
  · exact isClosed_eq ℓ.continuous S.continuous

end WeakLimit

end HallTransport

open HallTransport

/-- **Weak sequential compactness** of
densities bounded by `A` on a finite measure space with separable `L¹`: a
subsequence converges against every integrable test to a density in `[0, A]`. -/
theorem exists_weakly_convergent_density_subseq_proof {X : Type*} [MeasurableSpace X]
    (σ : Measure X) [IsFiniteMeasure σ] [TopologicalSpace.SeparableSpace (Lp ℝ 1 σ)]
    (A : ℝ) (h : ℕ → X → ℝ) (hm : ∀ n, Measurable (h n))
    (hb : ∀ n x, 0 ≤ h n x ∧ h n x ≤ A) :
    ∃ (φ : ℕ → ℕ) (h₀ : X → ℝ), StrictMono φ ∧ Measurable h₀ ∧ (∀ x, 0 ≤ h₀ x ∧ h₀ x ≤ A) ∧
      ∀ ψ : X → ℝ, Integrable ψ σ →
        Tendsto (fun n => ∫ x, h (φ n) x * ψ x ∂σ) atTop (𝓝 (∫ x, h₀ x * ψ x ∂σ)) := by
  -- `A` may be negative only when `X` is empty; work with `M = max A 0`.
  have hM : 0 ≤ max A 0 := le_max_right _ _
  have hbM : ∀ n x, ‖h n x‖ ≤ max A 0 := fun n x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb n x).1]
    exact (hb n x).2.trans (le_max_left _ _)
  obtain ⟨φ, ℓ, hφ, -, hlim⟩ :=
    exists_subseq_tendsto_pairing (σ := σ) hM h (fun n => (hm n).aestronglyMeasurable) hbM
  have hpos : ∀ s (hs : MeasurableSet s), 0 ≤ ℓ (indicatorConstLp 1 hs (measure_ne_top σ s) 1) := by
    intro s hs
    refine ge_of_tendsto' (hlim _) fun n => ?_
    rw [integral_mul_indicatorConstLp_one]
    exact setIntegral_nonneg hs fun x _ => (hb _ x).1
  have hle : ∀ s (hs : MeasurableSet s),
      ℓ (indicatorConstLp 1 hs (measure_ne_top σ s) 1) ≤ max A 0 * σ.real s := by
    intro s hs
    refine le_of_tendsto' (hlim _) fun n => ?_
    rw [integral_mul_indicatorConstLp_one]
    exact (Real.le_norm_self _).trans
      (norm_setIntegral_le_of_norm_le_const (measure_lt_top σ s) fun x _ => hbM _ x)
  obtain ⟨h₀, hh₀m, hh₀b, hrep⟩ := exists_density_of_continuousLinearMap ℓ hM hpos hle
  refine ⟨φ, h₀, hφ, hh₀m, fun x => ⟨(hh₀b x).1, ?_⟩, fun ψ hψ => ?_⟩
  · have hA : 0 ≤ A := (hb 0 x).1.trans (hb 0 x).2
    simpa only [max_eq_left hA] using (hh₀b x).2
  · have h₁ : ∀ n, ∫ x, h (φ n) x * ψ x ∂σ = ∫ x, h (φ n) x * hψ.toL1 ψ x ∂σ := fun n =>
      integral_congr_ae ((Integrable.coeFn_toL1 hψ).mono fun x hx => by simp only [hx])
    have h₂ : ∫ x, h₀ x * ψ x ∂σ = ℓ (hψ.toL1 ψ) := by
      rw [hrep]
      exact integral_congr_ae ((Integrable.coeFn_toL1 hψ).mono fun x hx => by simp only [hx])
    simp only [h₁, h₂]
    exact hlim _

end ParabolicRectifiability
