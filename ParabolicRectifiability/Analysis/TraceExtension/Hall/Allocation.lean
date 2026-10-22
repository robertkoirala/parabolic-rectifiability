import ParabolicRectifiability.Basic

/-!
# Real-capacity Hall allocation

The two reductions of the real-capacity Hall lemma: the finite case
`hall_allocation_iff_proof` and the countable case
`exists_countable_hall_allocation_proof`. The two analytic inputs are explicit
hypotheses:

* finite real-capacity transport (the statement proved by
  `exists_transport_of_hall_condition_proof`), used by the finite case;
* the finite case itself and weak sequential compactness of bounded densities (the
  statement proved by `exists_weakly_convergent_density_subseq_proof`), used by the
  countable case.

A hypothesis cannot quantify over universes, so each such hypothesis is the input
proposition at the universes of the target (`u` for the space, `v` for the index
types); the universe-polymorphic proof of the input instantiates it.

*Finite case.* Necessity integrates `∑_{j ∈ I} h_j` over `⋃_{j ∈ I} S_j`. Sufficiency
partitions the source by membership cells `C_T = {x | {j | x ∈ S_j} = T}`, applies the
transport to requests `w_j`, cells `T` with capacity `A σ(C_T)` and incidence `j ∈ T`
(Hall's condition becomes the transport condition because `⋃_{j∈I} S_j` is the disjoint
union of the cells meeting `I`), and spreads the transported mass `x_{j,T}` uniformly
over `C_T`. The resulting bound `∑_j h_j ≤ A` holds everywhere.

*Countable case.* Enumerate the requests, solve the finite problems for the first `N`
requests (bounded everywhere after a null-set cleanup), extract by a diagonal argument
(`exists_diagonal`) a subsequence along which every density converges weakly on its
`S_j`, and take the limits `h_j`. Testing with `1` preserves every demand; testing with
indicators preserves every finite-sum bound `∑_{j ∈ I} h_j ≤ A` almost everywhere, and the
countably many initial segments give the bound for the whole series.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

universe u v

namespace ParabolicRectifiability

namespace HallAllocation

/-! ## Membership cells -/

section Cells

variable {X : Type u} [MeasurableSpace X] {J : Type v} [Fintype J]

open Classical in
/-- The set of requests whose source set contains `x`. -/
def pattern (S : J → Set X) (x : X) : Finset J := Finset.univ.filter fun j => x ∈ S j

/-- The membership cell of `T`: points whose pattern is exactly `T`. -/
def cell (S : J → Set X) (T : Finset J) : Set X := {x | pattern S x = T}

omit [MeasurableSpace X] in
theorem mem_pattern {S : J → Set X} {x : X} {j : J} : j ∈ pattern S x ↔ x ∈ S j := by
  classical
  simp [pattern]

theorem measurableSet_cell {S : J → Set X} (hS : ∀ j, MeasurableSet (S j)) (T : Finset J) :
    MeasurableSet (cell S T) := by
  classical
  have h : cell S T = ⋂ j, {x | x ∈ S j ↔ j ∈ T} := by
    ext x
    simp only [cell, mem_ofPred_eq, mem_iInter, Finset.ext_iff, mem_pattern]
  rw [h]
  refine MeasurableSet.iInter fun j => ?_
  by_cases hj : j ∈ T
  · have h' : {x | x ∈ S j ↔ j ∈ T} = S j := by
      ext x
      simp [hj]
    rw [h']
    exact hS j
  · have h' : {x | x ∈ S j ↔ j ∈ T} = (S j)ᶜ := by
      ext x
      simp [hj]
    rw [h']
    exact (hS j).compl

omit [MeasurableSpace X] in
theorem disjoint_cell {S : J → Set X} {T T' : Finset J} (h : T ≠ T') :
    Disjoint (cell S T) (cell S T') :=
  Set.disjoint_left.mpr fun _ h1 h2 => h (h1.symm.trans h2)

omit [MeasurableSpace X] in
theorem cell_subset {S : J → Set X} {T : Finset J} {j : J} (hj : j ∈ T) : cell S T ⊆ S j := by
  intro x hx
  have h : pattern S x = T := hx
  rw [← h] at hj
  exact mem_pattern.mp hj

omit [MeasurableSpace X] in
open Classical in
theorem biUnion_eq_biUnion_cell (S : J → Set X) (I : Finset J) :
    (⋃ j ∈ I, S j) = ⋃ T ∈ Finset.univ.filter (fun T : Finset J => ∃ j ∈ I, j ∈ T), cell S T := by
  ext y
  simp only [mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
  constructor
  · rintro ⟨j, hj, hy⟩
    exact ⟨pattern S y, ⟨j, hj, mem_pattern.mpr hy⟩, rfl⟩
  · rintro ⟨T, ⟨j, hj, hjT⟩, hyT⟩
    exact ⟨j, hj, cell_subset hjT hyT⟩

end Cells

/-! ## The finite case -/

section Finite

/-- Necessity in the Hall lemma: integrate the densities over the union. -/
theorem hall_condition_of_allocation {X : Type u} [MeasurableSpace X] (σ : Measure X)
    {J : Type v} [Fintype J] (S : J → Set X) (hS : ∀ j, MeasurableSet (S j))
    (w : J → ℝ≥0) (A : ℝ≥0) (h : J → X → ℝ≥0∞) (hm : ∀ j, Measurable (h j))
    (h0 : ∀ j, ∀ x ∉ S j, h j x = 0) (hint : ∀ j, ∫⁻ x, h j x ∂σ = w j)
    (hle : ∀ᵐ x ∂σ, ∑ j, h j x ≤ A) (I : Finset J) :
    ∑ j ∈ I, (w j : ℝ≥0∞) ≤ A * σ (⋃ j ∈ I, S j) := by
  have hU : MeasurableSet (⋃ j ∈ I, S j) := Finset.measurableSet_biUnion I fun j _ => hS j
  have hsupp : ∀ x, x ∉ (⋃ j ∈ I, S j) → ∑ j ∈ I, h j x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun j hj => h0 j x fun hxj => hx ?_
    exact mem_iUnion₂.mpr ⟨j, hj, hxj⟩
  calc ∑ j ∈ I, (w j : ℝ≥0∞) = ∑ j ∈ I, ∫⁻ x, h j x ∂σ :=
        Finset.sum_congr rfl fun j _ => (hint j).symm
    _ = ∫⁻ x, ∑ j ∈ I, h j x ∂σ := (lintegral_finsetSum I fun j _ => hm j).symm
    _ = ∫⁻ x in ⋃ j ∈ I, S j, ∑ j ∈ I, h j x ∂σ := by
        rw [← lintegral_indicator hU]
        congr 1
        funext x
        by_cases hx : x ∈ ⋃ j ∈ I, S j
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, hsupp x hx]
    _ ≤ ∫⁻ _ in ⋃ j ∈ I, S j, (A : ℝ≥0∞) ∂σ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hle] with x hx
        exact (Finset.sum_le_sum_of_subset (Finset.subset_univ I)).trans hx
    _ = A * σ (⋃ j ∈ I, S j) := setLIntegral_const _ _

-- The transport hypothesis keeps its binder names, hence the linter option.
set_option linter.unusedVariables false in
open Classical in
/-- **Finite Hall allocation.** Finitely many requests `w_j > 0` on sets `S_j` of finite
measure admit densities `h_j` carried by `S_j`, with `∫ h_j dσ = w_j` and `Σ_j h_j ≤ A`
almost everywhere, if and only if Hall's condition `Σ_{j ∈ I} w_j ≤ A σ(⋃_{j ∈ I} S_j)`
holds for every `I`. The hypothesis `hA2a` is finite real-capacity transport (the
statement proved by `exists_transport_of_hall_condition_proof`). -/
theorem hall_allocation_iff_proof
    (hA2a : ∀ {J T : Type v} [Fintype J] [Fintype T]
      (adj : J → T → Prop) (w : J → ℝ) (κ : T → ℝ) (hw : ∀ j, 0 ≤ w j) (hκ : ∀ t, 0 ≤ κ t)
      (hH : ∀ I : Finset J,
        ∑ j ∈ I, w j ≤ ∑ t ∈ Finset.univ.filter (fun t => ∃ j ∈ I, adj j t), κ t),
      ∃ x : J → T → ℝ, (∀ j t, 0 ≤ x j t) ∧ (∀ j t, ¬ adj j t → x j t = 0) ∧
        (∀ j, ∑ t, x j t = w j) ∧ ∀ t, ∑ j, x j t ≤ κ t)
    {X : Type u} [MeasurableSpace X] (σ : Measure X) {J : Type v}
    [Fintype J] (S : J → Set X) (hS : ∀ j, MeasurableSet (S j)) (hfin : ∀ j, σ (S j) < ⊤)
    (w : J → ℝ≥0) (hw : ∀ j, 0 < w j) (A : ℝ≥0) (hA : 0 < A) :
    (∃ h : J → X → ℝ≥0∞, (∀ j, Measurable (h j)) ∧ (∀ j, ∀ x ∉ S j, h j x = 0) ∧
        (∀ j, ∫⁻ x, h j x ∂σ = w j) ∧ ∀ᵐ x ∂σ, ∑ j, h j x ≤ A) ↔
      ∀ I : Finset J, ∑ j ∈ I, (w j : ℝ≥0∞) ≤ A * σ (⋃ j ∈ I, S j) := by
  constructor
  · rintro ⟨h, hm, h0, hint, hle⟩ I
    exact hall_condition_of_allocation σ S hS w A h hm h0 hint hle I
  intro hH
  -- Cells meeting a request have finite measure.
  have hcellfin : ∀ (T : Finset J) (j : J), j ∈ T → σ (cell S T) < ⊤ :=
    fun T j hj => (measure_mono (cell_subset hj)).trans_lt (hfin j)
  -- Hall's condition in transport form.
  have hHr : ∀ I : Finset J, ∑ j ∈ I, (w j : ℝ) ≤
      ∑ T ∈ Finset.univ.filter (fun T : Finset J => ∃ j ∈ I, j ∈ T),
        (A : ℝ) * (σ (cell S T)).toReal := by
    intro I
    have hI := hH I
    rw [biUnion_eq_biUnion_cell S I,
      measure_biUnion_finset (fun T _ T' _ hTT' => disjoint_cell hTT')
        (fun T _ => measurableSet_cell hS T)] at hI
    have hne : ∀ T ∈ Finset.univ.filter (fun T : Finset J => ∃ j ∈ I, j ∈ T),
        σ (cell S T) ≠ ⊤ := by
      intro T hT
      obtain ⟨j, -, hjT⟩ := (Finset.mem_filter.mp hT).2
      exact (hcellfin T j hjT).ne
    have hrhs : (A : ℝ≥0∞) * ∑ T ∈ Finset.univ.filter (fun T : Finset J => ∃ j ∈ I, j ∈ T),
        σ (cell S T) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.sum_ne_top.mpr hne)
    have h1 := ENNReal.toReal_mono hrhs hI
    rw [ENNReal.toReal_sum (s := I) (f := fun j => (w j : ℝ≥0∞)) fun j _ => ENNReal.coe_ne_top,
      ENNReal.toReal_mul,
      ENNReal.toReal_sum hne, Finset.mul_sum] at h1
    simpa only [ENNReal.coe_toReal] using h1
  obtain ⟨x, hx0, hxadj, hxsum, hxcap⟩ := hA2a (fun j T => j ∈ T) (fun j => (w j : ℝ))
    (fun T => (A : ℝ) * (σ (cell S T)).toReal) (fun j => (w j).coe_nonneg)
    (fun T => mul_nonneg A.coe_nonneg ENNReal.toReal_nonneg) (fun I => by
      refine (hHr I).trans_eq (Finset.sum_congr ?_ fun _ _ => rfl)
      ext T
      simp only [Finset.mem_filter])
  -- A transported mass on a null cell vanishes.
  have hxnull : ∀ j T, (σ (cell S T)).toReal = 0 → x j T = 0 := by
    intro j T hT
    have hcap := hxcap T
    rw [hT, mul_zero] at hcap
    have hle := Finset.single_le_sum (fun i _ => hx0 i T) (Finset.mem_univ j)
    exact le_antisymm (hle.trans hcap) (hx0 j T)
  let h : J → X → ℝ≥0∞ := fun j y => ∑ T : Finset J,
    (cell S T).indicator (fun _ => ENNReal.ofReal (x j T / (σ (cell S T)).toReal)) y
  have happly : ∀ j y, h j y = ENNReal.ofReal (x j (pattern S y) /
      (σ (cell S (pattern S y))).toReal) := by
    intro j y
    refine (Finset.sum_eq_single (pattern S y) (fun T _ hT => ?_)
      (fun hy => absurd (Finset.mem_univ _) hy)).trans ?_
    · show (cell S T).indicator (fun _ => ENNReal.ofReal (x j T / (σ (cell S T)).toReal)) y = 0
      have hyT : y ∉ cell S T := fun hy => hT (Eq.symm hy)
      exact Set.indicator_of_notMem hyT _
    · exact Set.indicator_of_mem (show y ∈ cell S (pattern S y) from rfl) _
  refine ⟨h, fun j => ?_, fun j y hy => ?_, fun j => ?_, ae_of_all _ fun y => ?_⟩
  · exact Finset.measurable_sum _ fun T _ => measurable_const.indicator (measurableSet_cell hS T)
  · rw [happly, hxadj j (pattern S y) (fun hj => hy (mem_pattern.mp hj)), zero_div,
      ENNReal.ofReal_zero]
  · have hterm : ∀ T : Finset J, ∫⁻ y, (cell S T).indicator
        (fun _ => ENNReal.ofReal (x j T / (σ (cell S T)).toReal)) y ∂σ =
        ENNReal.ofReal (x j T) := by
      intro T
      rw [lintegral_indicator_const (measurableSet_cell hS T)]
      by_cases hjT : j ∈ T
      · rcases (ENNReal.toReal_nonneg (a := σ (cell S T))).eq_or_lt with h0 | hpos
        · rw [hxnull j T h0.symm, zero_div, ENNReal.ofReal_zero, zero_mul]
        · have hσT : σ (cell S T) = ENNReal.ofReal (σ (cell S T)).toReal :=
            (ENNReal.ofReal_toReal (hcellfin T j hjT).ne).symm
          calc ENNReal.ofReal (x j T / (σ (cell S T)).toReal) * σ (cell S T)
              = ENNReal.ofReal (x j T / (σ (cell S T)).toReal) *
                  ENNReal.ofReal (σ (cell S T)).toReal := by rw [← hσT]
            _ = ENNReal.ofReal (x j T / (σ (cell S T)).toReal * (σ (cell S T)).toReal) :=
                (ENNReal.ofReal_mul (div_nonneg (hx0 j T) hpos.le)).symm
            _ = ENNReal.ofReal (x j T) := by rw [div_mul_cancel₀ _ hpos.ne']
      · rw [hxadj j T hjT, zero_div, ENNReal.ofReal_zero, zero_mul]
    calc ∫⁻ y, h j y ∂σ = ∑ T : Finset J, ∫⁻ y, (cell S T).indicator
          (fun _ => ENNReal.ofReal (x j T / (σ (cell S T)).toReal)) y ∂σ :=
          lintegral_finsetSum _ fun T _ => measurable_const.indicator (measurableSet_cell hS T)
      _ = ∑ T : Finset J, ENNReal.ofReal (x j T) := Finset.sum_congr rfl fun T _ => hterm T
      _ = ENNReal.ofReal (∑ T : Finset J, x j T) :=
          (ENNReal.ofReal_sum_of_nonneg fun T _ => hx0 j T).symm
      _ = w j := by rw [hxsum j, ENNReal.ofReal_coe_nnreal]
  · simp only [happly]
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => div_nonneg (hx0 j _) ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    rw [← Finset.sum_div]
    rcases (ENNReal.toReal_nonneg (a := σ (cell S (pattern S y)))).eq_or_lt with h0 | hpos
    · rw [← h0, div_zero]
      exact A.coe_nonneg
    · rw [div_le_iff₀ hpos]
      exact hxcap _

end Finite

/-! ## The countable case -/

section Countable

/-- A diagonal subsequence: if every subsequence has a further subsequence with property
`P k`, and each `P k` passes to sequences eventually given by a reparametrization tending
to infinity, then one strictly increasing sequence has every `P k`. -/
theorem exists_diagonal (P : ℕ → (ℕ → ℕ) → Prop)
    (hP : ∀ k (θ : ℕ → ℕ), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P k (θ ∘ ψ))
    (hmono : ∀ k (θ θ' β : ℕ → ℕ), P k θ → Tendsto β atTop atTop →
      (∀ᶠ n in atTop, θ' n = θ (β n)) → P k θ') :
    ∃ D : ℕ → ℕ, StrictMono D ∧ ∀ k, P k D := by
  choose ψ hψm hψP using hP
  let Φ : ℕ → ℕ → ℕ := fun k =>
    Nat.rec (motive := fun _ => ℕ → ℕ) (ψ 0 id) (fun k Φk => Φk ∘ ψ (k + 1) Φk) k
  have hΦs : ∀ k, Φ (k + 1) = Φ k ∘ ψ (k + 1) (Φ k) := fun k => rfl
  have hΦP : ∀ k, P k (Φ k) := by
    intro k
    cases k with
    | zero => exact hψP 0 id
    | succ k => rw [hΦs]; exact hψP (k + 1) (Φ k)
  have hΦm : ∀ k, StrictMono (Φ k) := by
    intro k
    induction k with
    | zero => exact hψm 0 id
    | succ k ih => rw [hΦs]; exact ih.comp (hψm _ _)
  have hfac : ∀ k m, ∃ α : ℕ → ℕ, (∀ n, n ≤ α n) ∧ Φ (k + m) = Φ k ∘ α := by
    intro k m
    induction m with
    | zero => exact ⟨id, fun n => le_rfl, rfl⟩
    | succ m ih =>
      obtain ⟨α, hα, hαe⟩ := ih
      refine ⟨α ∘ ψ (k + m + 1) (Φ (k + m)), fun n => ((hψm _ _).id_le n).trans (hα _), ?_⟩
      funext n
      show Φ (k + m) (ψ (k + m + 1) (Φ (k + m)) n) = Φ k (α (ψ (k + m + 1) (Φ (k + m)) n))
      rw [hαe, Function.comp_apply]
  refine ⟨fun n => Φ n n, ?_, fun k => ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    show Φ n n < Φ (n + 1) (n + 1)
    rw [hΦs]
    exact hΦm n (lt_of_lt_of_le (Nat.lt_succ_self n) ((hψm _ _).id_le _))
  · choose α hα hαe using hfac k
    refine hmono k (Φ k) (fun n => Φ n n) (fun n => α (n - k) n) (hΦP k) ?_ ?_
    · exact tendsto_atTop_mono (fun n => hα (n - k) n) tendsto_id
    · filter_upwards [eventually_ge_atTop k] with n hn
      have h := hαe (n - k)
      rw [Nat.add_sub_cancel' hn] at h
      show Φ n n = Φ k (α (n - k) n)
      rw [h, Function.comp_apply]

/-- A finite allocation can be modified on a null set so that its sum bound holds everywhere. -/
theorem exists_allocation_le_everywhere {X : Type u} [MeasurableSpace X] (σ : Measure X)
    {J : Type v} [Fintype J] (S : J → Set X) (w : J → ℝ≥0) (A : ℝ≥0) (h : J → X → ℝ≥0∞)
    (hm : ∀ j, Measurable (h j)) (h0 : ∀ j, ∀ x ∉ S j, h j x = 0)
    (hint : ∀ j, ∫⁻ x, h j x ∂σ = w j) (hle : ∀ᵐ x ∂σ, ∑ j, h j x ≤ A) :
    ∃ h' : J → X → ℝ≥0∞, (∀ j, Measurable (h' j)) ∧ (∀ j, ∀ x ∉ S j, h' j x = 0) ∧
      (∀ j, ∫⁻ x, h' j x ∂σ = w j) ∧ ∀ x, ∑ j, h' j x ≤ A := by
  have hE : MeasurableSet {x | ∑ j, h j x ≤ A} :=
    measurableSet_le (Finset.measurable_sum _ fun j _ => hm j) measurable_const
  refine ⟨fun j => {x | ∑ j, h j x ≤ A}.indicator (h j), fun j => (hm j).indicator hE,
    fun j x hx => ?_, fun j => ?_, fun x => ?_⟩
  · show {x | ∑ j, h j x ≤ (A : ℝ≥0∞)}.indicator (h j) x = 0
    by_cases hxE : x ∈ {x | ∑ j, h j x ≤ A}
    · rw [Set.indicator_of_mem hxE, h0 j x hx]
    · rw [Set.indicator_of_notMem hxE]
  · rw [← hint j]
    apply lintegral_congr_ae
    filter_upwards [hle] with x hx
    exact Set.indicator_of_mem (show x ∈ {x | ∑ j, h j x ≤ A} from hx) _
  · by_cases hxE : x ∈ {x | ∑ j, h j x ≤ A}
    · simp only [Set.indicator_of_mem hxE]
      exact hxE
    · simp only [Set.indicator_of_notMem hxE, Finset.sum_const_zero]
      exact zero_le

/-- Integral of a nonnegative function against an indicator test, as a lintegral. -/
theorem integral_mul_indicator_one {X : Type u} [MeasurableSpace X] (σ : Measure X)
    (g : X → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) {S D : Set X} (hD : MeasurableSet D) :
    ∫ x, g x * D.indicator (fun _ => (1 : ℝ)) x ∂σ.restrict S =
      (∫⁻ x in D ∩ S, ENNReal.ofReal (g x) ∂σ).toReal := by
  have h : (fun x => g x * D.indicator (fun _ => (1 : ℝ)) x) = D.indicator g := by
    funext x
    by_cases hx : x ∈ D
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  rw [h, integral_indicator hD, Measure.restrict_restrict hD,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.aestronglyMeasurable]

-- The input hypotheses keep their binder names, hence the linter option.
set_option linter.unusedVariables false in
/-- **Countable Hall allocation.** Countably many requests `w_j > 0` on sets `S_j` of
finite measure (with separable `L¹(σ⌞S_j)`) satisfying Hall's condition for every finite
`I` admit densities `h_j` carried by `S_j`, with `∫ h_j dσ = w_j` and `Σ_j h_j ≤ A` almost
everywhere. The hypotheses `hB` and `hC` are the finite case (`hall_allocation_iff_proof`)
and weak sequential compactness of bounded densities (the statement proved by
`exists_weakly_convergent_density_subseq_proof`). -/
theorem exists_countable_hall_allocation_proof
    (hB : ∀ {X : Type u} [MeasurableSpace X] (σ : Measure X) {J : Type v}
      [Fintype J] (S : J → Set X) (hS : ∀ j, MeasurableSet (S j)) (hfin : ∀ j, σ (S j) < ⊤)
      (w : J → ℝ≥0) (hw : ∀ j, 0 < w j) (A : ℝ≥0) (hA : 0 < A),
      (∃ h : J → X → ℝ≥0∞, (∀ j, Measurable (h j)) ∧ (∀ j, ∀ x ∉ S j, h j x = 0) ∧
          (∀ j, ∫⁻ x, h j x ∂σ = w j) ∧ ∀ᵐ x ∂σ, ∑ j, h j x ≤ A) ↔
        ∀ I : Finset J, ∑ j ∈ I, (w j : ℝ≥0∞) ≤ A * σ (⋃ j ∈ I, S j))
    (hC : ∀ {X : Type u} [MeasurableSpace X]
      (σ : Measure X) [IsFiniteMeasure σ] [TopologicalSpace.SeparableSpace (Lp ℝ 1 σ)]
      (A : ℝ) (h : ℕ → X → ℝ) (hm : ∀ n, Measurable (h n))
      (hb : ∀ n x, 0 ≤ h n x ∧ h n x ≤ A),
      ∃ (φ : ℕ → ℕ) (h₀ : X → ℝ), StrictMono φ ∧ Measurable h₀ ∧ (∀ x, 0 ≤ h₀ x ∧ h₀ x ≤ A) ∧
        ∀ ψ : X → ℝ, Integrable ψ σ →
          Tendsto (fun n => ∫ x, h (φ n) x * ψ x ∂σ) atTop (𝓝 (∫ x, h₀ x * ψ x ∂σ)))
    {X : Type u} [MeasurableSpace X] (σ : Measure X)
    {J : Type v} [Countable J] (S : J → Set X) (hS : ∀ j, MeasurableSet (S j))
    (hfin : ∀ j, σ (S j) < ⊤)
    (hsep : ∀ j, TopologicalSpace.SeparableSpace (Lp ℝ 1 (σ.restrict (S j))))
    (w : J → ℝ≥0) (hw : ∀ j, 0 < w j) (A : ℝ≥0) (hA : 0 < A)
    (hH : ∀ I : Finset J, ∑ j ∈ I, (w j : ℝ≥0∞) ≤ A * σ (⋃ j ∈ I, S j)) :
    ∃ h : J → X → ℝ≥0∞, (∀ j, Measurable (h j)) ∧ (∀ j, ∀ x ∉ S j, h j x = 0) ∧
      (∀ j, ∫⁻ x, h j x ∂σ = w j) ∧ ∀ᵐ x ∂σ, ∑' j, h j x ≤ A := by
  classical
  rcases isEmpty_or_nonempty J with hJ | hJ
  · refine ⟨fun j => isEmptyElim j, fun j => isEmptyElim j, fun j => isEmptyElim j,
      fun j => isEmptyElim j, ae_of_all _ fun x => ?_⟩
    rw [tsum_empty]
    exact zero_le
  obtain ⟨e, he⟩ := exists_surjective_nat J
  -- The first `N` requests.
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → Finset J, F = fun N => (Finset.range N).image e := ⟨_, rfl⟩
  have hmemF : ∀ k N, k < N → e k ∈ F N := by
    intro k N hkN
    rw [hFdef]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hkN, rfl⟩
  -- Finite allocations for the first `N` requests, bounded everywhere.
  have happrox : ∀ N, ∃ H : J → X → ℝ≥0∞, (∀ j, Measurable (H j)) ∧
      (∀ j, ∀ x ∉ S j, H j x = 0) ∧ (∀ j ∉ F N, ∀ x, H j x = 0) ∧
      (∀ j ∈ F N, ∫⁻ x, H j x ∂σ = w j) ∧ ∀ x, ∑ j ∈ F N, H j x ≤ A := by
    intro N
    have hall : ∀ I : Finset (F N), ∑ j ∈ I, (w j : ℝ≥0∞) ≤ A * σ (⋃ j ∈ I, S j) := by
      intro I
      have h := hH (I.map (Function.Embedding.subtype _))
      rw [Finset.sum_map] at h
      have hU : (⋃ j ∈ I.map (Function.Embedding.subtype _), S j) = ⋃ j ∈ I, S (j : J) := by
        apply Set.Subset.antisymm
        · intro y hy
          obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hy
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hj
          exact mem_iUnion₂.mpr ⟨a, ha, hyj⟩
        · intro y hy
          obtain ⟨a, ha, hya⟩ := mem_iUnion₂.mp hy
          exact mem_iUnion₂.mpr ⟨a, Finset.mem_map_of_mem _ ha, hya⟩
      rw [hU] at h
      exact h
    obtain ⟨h, hm, h0, hint, hle⟩ := (hB σ (J := F N) (fun j => S j) (fun j => hS j)
      (fun j => hfin j) (fun j => w j) (fun j => hw j) A hA).mpr hall
    obtain ⟨h', hm', h0', hint', hle'⟩ :=
      exists_allocation_le_everywhere σ (fun j : F N => S j) (fun j => w j) A h hm h0 hint hle
    refine ⟨fun j x => if hj : j ∈ F N then h' ⟨j, hj⟩ x else 0, fun j => ?_,
      fun j x hx => ?_, fun j hj x => ?_, fun j hj => ?_, fun x => ?_⟩
    · by_cases hj : j ∈ F N
      · simp only [hj, ↓reduceDIte]
        exact hm' ⟨j, hj⟩
      · simp only [hj, ↓reduceDIte]
        exact measurable_const
    · by_cases hj : j ∈ F N
      · simp only [hj, ↓reduceDIte]
        exact h0' ⟨j, hj⟩ x hx
      · simp only [hj, ↓reduceDIte]
    · simp only [hj, ↓reduceDIte]
    · simp only [hj, ↓reduceDIte]
      exact hint' ⟨j, hj⟩
    · calc ∑ j ∈ F N, (if hj : j ∈ F N then h' ⟨j, hj⟩ x else 0)
          = ∑ j : F N, (if hj : (j : J) ∈ F N then h' ⟨j, hj⟩ x else 0) :=
            (Finset.sum_coe_sort (F N) _).symm
        _ = ∑ j : F N, h' j x := Finset.sum_congr rfl fun j _ => by simp only [j.2, ↓reduceDIte]
        _ ≤ A := hle' x
  choose H hHm hH0 hHout hHint hHle using happrox
  have hHA : ∀ N j x, H N j x ≤ A := by
    intro N j x
    by_cases hj : j ∈ F N
    · exact (Finset.single_le_sum (fun i _ => zero_le) hj).trans (hHle N x)
    · rw [hHout N j hj x]
      exact zero_le
  have hHne : ∀ N j x, H N j x ≠ ⊤ := fun N j x => ne_top_of_le_ne_top ENNReal.coe_ne_top (hHA N j x)
  -- The real densities.
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → J → X → ℝ, G = fun N j x => (H N j x).toReal := ⟨_, rfl⟩
  have hGm : ∀ N j, Measurable (G N j) := by
    intro N j
    rw [hGdef]
    exact (hHm N j).ennreal_toReal
  have hGb : ∀ N j x, 0 ≤ G N j x ∧ G N j x ≤ A := by
    intro N j x
    rw [hGdef]
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal A.coe_nonneg
      ((hHA N j x).trans_eq (ENNReal.ofReal_coe_nnreal).symm)⟩
  have hGH : ∀ N j x, ENNReal.ofReal (G N j x) = H N j x := by
    intro N j x
    rw [hGdef]
    exact ENNReal.ofReal_toReal (hHne N j x)
  have hfinite : ∀ j, IsFiniteMeasure (σ.restrict (S j)) :=
    fun j => isFiniteMeasure_restrict.mpr (hfin j).ne
  -- Supports and demands of the finite problems.
  have hHsupp : ∀ N j, (S j).indicator (H N j) = H N j := by
    intro N j
    funext x
    by_cases hx : x ∈ S j
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hH0 N j x hx]
  have hGint : ∀ N j, j ∈ F N → ∫ x, G N j x ∂σ.restrict (S j) = w j := by
    intro N j hj
    have h1 : ∫ x, G N j x ∂σ.restrict (S j) = (∫⁻ x in S j, H N j x ∂σ).toReal := by
      rw [hGdef]
      exact integral_toReal (hHm N j).aemeasurable
        (ae_of_all _ fun x => lt_top_iff_ne_top.mpr (hHne N j x))
    rw [h1, ← lintegral_indicator (hS j), hHsupp N j, hHint N j hj, ENNReal.coe_toReal]
  -- The diagonal subsequence.
  obtain ⟨D, hDm, hDP⟩ := exists_diagonal
    (fun k θ => ∃ h₀ : X → ℝ, Measurable h₀ ∧ (∀ x, 0 ≤ h₀ x ∧ h₀ x ≤ A) ∧
      ∀ ψ : X → ℝ, Integrable ψ (σ.restrict (S (e k))) →
        Tendsto (fun n => ∫ x, G (θ n) (e k) x * ψ x ∂σ.restrict (S (e k))) atTop
          (𝓝 (∫ x, h₀ x * ψ x ∂σ.restrict (S (e k)))))
    (fun k θ => by
      have := hfinite (e k)
      have := hsep (e k)
      obtain ⟨φ, h₀, hφ, hm₀, hb₀, ht₀⟩ := hC (σ.restrict (S (e k))) (A : ℝ)
        (fun n => G (θ n) (e k)) (fun n => hGm _ _) (fun n x => hGb _ _ x)
      exact ⟨φ, hφ, h₀, hm₀, hb₀, ht₀⟩)
    (fun k θ θ' β hθ hβ hev => by
      obtain ⟨h₀, hm₀, hb₀, ht₀⟩ := hθ
      refine ⟨h₀, hm₀, hb₀, fun ψ hψ => ((ht₀ ψ hψ).comp hβ).congr' ?_⟩
      filter_upwards [hev] with n hn
      simp only [Function.comp_apply, hn])
  have hQ : ∀ j, ∃ h₀ : X → ℝ, Measurable h₀ ∧ (∀ x, 0 ≤ h₀ x ∧ h₀ x ≤ A) ∧
      ∀ ψ : X → ℝ, Integrable ψ (σ.restrict (S j)) →
        Tendsto (fun n => ∫ x, G (D n) j x * ψ x ∂σ.restrict (S j)) atTop
          (𝓝 (∫ x, h₀ x * ψ x ∂σ.restrict (S j))) := by
    intro j
    obtain ⟨k, rfl⟩ := he j
    exact hDP k
  choose h₀ hm₀ hb₀ ht₀ using hQ
  -- Every request eventually belongs to the finite problems along the diagonal.
  have hev : ∀ j, ∀ᶠ n in atTop, j ∈ F (D n) := by
    intro j
    obtain ⟨k, rfl⟩ := he j
    filter_upwards [eventually_gt_atTop k] with n hn
    exact hmemF k (D n) (hn.trans_le (hDm.id_le n))
  have hcover : ∀ s : Finset J, ∃ M, s ⊆ F M := by
    intro s
    refine ⟨s.sup (fun j => Classical.choose (he j)) + 1, fun j hj => ?_⟩
    have h := hmemF (Classical.choose (he j)) _
      (Nat.lt_succ_of_le (Finset.le_sup (f := fun j => Classical.choose (he j)) hj))
    rwa [Classical.choose_spec (he j)] at h
  -- Finiteness of the lintegrals of bounded densities.
  have hbdd : ∀ (f : X → ℝ≥0∞) (j : J) (D' : Set X), (∀ x, f x ≤ A) →
      ∫⁻ x in D' ∩ S j, f x ∂σ ≠ ⊤ := by
    intro f j D' hf
    have h1 : ∫⁻ x in D' ∩ S j, f x ∂σ ≤ ∫⁻ _ in D' ∩ S j, (A : ℝ≥0∞) ∂σ := lintegral_mono hf
    rw [setLIntegral_const] at h1
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ne_top_of_le_ne_top (hfin j).ne (measure_mono inter_subset_right))) h1
  have hb₀A : ∀ j x, ENNReal.ofReal (h₀ j x) ≤ A :=
    fun j x => (ENNReal.ofReal_le_ofReal (hb₀ j x).2).trans_eq ENNReal.ofReal_coe_nnreal
  have hmeas : ∀ j, Measurable ((S j).indicator fun x => ENNReal.ofReal (h₀ j x)) :=
    fun j => (ENNReal.measurable_ofReal.comp (hm₀ j)).indicator (hS j)
  -- The finite-sum bound for every finite request set.
  have hseg : ∀ I : Finset J, ∀ᵐ x ∂σ,
      ∑ j ∈ I, (S j).indicator (fun x => ENNReal.ofReal (h₀ j x)) x ≤ A := by
    intro I
    have hUm : MeasurableSet (⋃ j ∈ I, S j) := Finset.measurableSet_biUnion I fun j _ => hS j
    have hUfin : σ (⋃ j ∈ I, S j) < ⊤ :=
      (measure_biUnion_finset_le I S).trans_lt (ENNReal.sum_lt_top.mpr fun j _ => hfin j)
    have : IsFiniteMeasure (σ.restrict (⋃ j ∈ I, S j)) := isFiniteMeasure_restrict.mpr hUfin.ne
    have hSU : ∀ j ∈ I, S j ⊆ ⋃ i ∈ I, S i := fun j hj => subset_biUnion_of_mem hj
    have hres : (fun x => ∑ j ∈ I, (S j).indicator (fun x => ENNReal.ofReal (h₀ j x)) x)
        ≤ᵐ[σ.restrict (⋃ j ∈ I, S j)] fun _ => (A : ℝ≥0∞) := by
      refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite
        (Finset.measurable_sum _ fun j _ => hmeas j) fun D' hD' _ => ?_
      have hterm : ∀ (f : X → ℝ≥0∞) (j : J), j ∈ I →
          ∫⁻ x in D' ∩ ⋃ i ∈ I, S i, (S j).indicator f x ∂σ = ∫⁻ x in D' ∩ S j, f x ∂σ := by
        intro f j hj
        have hset : S j ∩ (D' ∩ ⋃ i ∈ I, S i) = D' ∩ S j := by
          ext y
          constructor
          · rintro ⟨hy, hyD, -⟩
            exact ⟨hyD, hy⟩
          · rintro ⟨hyD, hy⟩
            exact ⟨hy, hyD, hSU j hj hy⟩
        rw [lintegral_indicator (hS j), Measure.restrict_restrict (hS j), hset]
      rw [Measure.restrict_restrict hD', setLIntegral_const,
        lintegral_finsetSum _ fun j _ => hmeas j, Finset.sum_congr rfl fun j hj => hterm _ j hj]
      have hψ : ∀ j, Integrable (D'.indicator fun _ => (1 : ℝ)) (σ.restrict (S j)) := by
        intro j
        have := hfinite j
        exact (integrable_const (1 : ℝ)).indicator hD'
      have hlim : Tendsto (fun n => ∑ j ∈ I,
          ∫ x, G (D n) j x * D'.indicator (fun _ => (1 : ℝ)) x ∂σ.restrict (S j)) atTop
          (𝓝 (∑ j ∈ I, ∫ x, h₀ j x * D'.indicator (fun _ => (1 : ℝ)) x ∂σ.restrict (S j))) :=
        tendsto_finsetSum I fun j _ => ht₀ j _ (hψ j)
      have hDU : (A : ℝ≥0∞) * σ (D' ∩ ⋃ i ∈ I, S i) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top
          (ne_top_of_le_ne_top hUfin.ne (measure_mono inter_subset_right))
      have happ : ∀ᶠ n in atTop, ∑ j ∈ I,
          ∫ x, G (D n) j x * D'.indicator (fun _ => (1 : ℝ)) x ∂σ.restrict (S j) ≤
            ((A : ℝ≥0∞) * σ (D' ∩ ⋃ i ∈ I, S i)).toReal := by
        filter_upwards [(Filter.eventually_all_finset I).mpr fun j _ => hev j] with n hn
        have hconv : ∀ j ∈ I, ∫ x, G (D n) j x * D'.indicator (fun _ => (1 : ℝ)) x
            ∂σ.restrict (S j) = (∫⁻ x in D' ∩ S j, H (D n) j x ∂σ).toReal := by
          intro j _
          rw [integral_mul_indicator_one σ (G (D n) j) (hGm _ _) (fun x => (hGb _ _ x).1) hD']
          simp only [hGH]
        rw [Finset.sum_congr rfl hconv, ← ENNReal.toReal_sum fun j _ => hbdd _ j D' (hHA (D n) j)]
        refine ENNReal.toReal_mono hDU ?_
        calc ∑ j ∈ I, ∫⁻ x in D' ∩ S j, H (D n) j x ∂σ
            ≤ ∑ j ∈ I, ∫⁻ x in D' ∩ ⋃ i ∈ I, S i, H (D n) j x ∂σ :=
              Finset.sum_le_sum fun j hj =>
                lintegral_mono_set (inter_subset_inter_right _ (hSU j hj))
          _ = ∫⁻ x in D' ∩ ⋃ i ∈ I, S i, ∑ j ∈ I, H (D n) j x ∂σ :=
              (lintegral_finsetSum _ fun j _ => hHm _ j).symm
          _ ≤ ∫⁻ _ in D' ∩ ⋃ i ∈ I, S i, (A : ℝ≥0∞) ∂σ :=
              lintegral_mono fun x =>
                (Finset.sum_le_sum_of_subset fun j hj => hn j hj).trans (hHle _ x)
          _ = A * σ (D' ∩ ⋃ i ∈ I, S i) := setLIntegral_const _ _
      have hle := le_of_tendsto hlim happ
      have hconv0 : ∀ j ∈ I, ∫ x, h₀ j x * D'.indicator (fun _ => (1 : ℝ)) x ∂σ.restrict (S j) =
          (∫⁻ x in D' ∩ S j, ENNReal.ofReal (h₀ j x) ∂σ).toReal :=
        fun j _ => integral_mul_indicator_one σ (h₀ j) (hm₀ j) (fun x => (hb₀ j x).1) hD'
      rw [Finset.sum_congr rfl hconv0,
        ← ENNReal.toReal_sum fun j _ => hbdd _ j D' (hb₀A j)] at hle
      exact (ENNReal.toReal_le_toReal
        (ENNReal.sum_ne_top.mpr fun j _ => hbdd _ j D' (hb₀A j)) hDU).mp hle
    have h2 := (ae_restrict_iff' hUm).mp hres
    filter_upwards [h2] with x hx
    by_cases hxU : x ∈ ⋃ j ∈ I, S j
    · exact hx hxU
    · rw [Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (fun hxj => hxU (hSU j hj hxj)) _]
      exact zero_le
  refine ⟨fun j x => (S j).indicator (fun x => ENNReal.ofReal (h₀ j x)) x, hmeas,
    fun j x hx => Set.indicator_of_notMem hx _, fun j => ?_, ?_⟩
  · -- Testing with `1` preserves the demand.
    show ∫⁻ x, (S j).indicator (fun x => ENNReal.ofReal (h₀ j x)) x ∂σ = w j
    have := hfinite j
    have hlim := ht₀ j (fun _ => 1) (integrable_const 1)
    simp only [mul_one] at hlim
    have heq : ∫ x, h₀ j x ∂σ.restrict (S j) = w j := by
      refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
      filter_upwards [hev j] with n hn
      exact (hGint (D n) j hn).symm
    have hint : Integrable (h₀ j) (σ.restrict (S j)) :=
      (integrable_const (A : ℝ)).mono' (hm₀ j).aestronglyMeasurable (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hb₀ j x).1]
        exact (hb₀ j x).2)
    rw [lintegral_indicator (hS j),
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (hb₀ j x).1), heq,
      ENNReal.ofReal_coe_nnreal]
  · -- The finite-sum bounds on the initial segments give the bound for the series.
    filter_upwards [ae_all_iff.mpr fun M => hseg (F M)] with x hx
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    obtain ⟨M, hM⟩ := hcover s
    exact (Finset.sum_le_sum_of_subset hM).trans (hx M)

end Countable

end HallAllocation

end ParabolicRectifiability
