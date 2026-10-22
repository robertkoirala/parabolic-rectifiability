import ParabolicRectifiability.QuantitativeCharacterization.Statements.ReverseBound
import ParabolicRectifiability.Analysis.TraceExtension.Hall.Allocation
import ParabolicRectifiability.Analysis.TraceExtension.Hall.Transport

/-! # The buffered allocation: clipped cells, buffer, Hall densities

First part of the proof of `d2_coupling_of_parts`.

Given Whitney cells `Q_j` of `Γᶜ` with anchors `g_j ∈ Γ` and scales `s_j`, and a model ball
`P(c,ρ)` meeting `Γ`:

* the **clipped cells** `Q'_j = Q_j ∩ P(c,2ρ)` (`d2cpl_clip`) are measurable, disjoint and of
  finite mass; the **positive-mass cells** are reindexed by the countable subtype
  `J = {j : 0 < μ(Q'_j)}` (`d2cpl_Pos`); the omitted cells are null and, up to them, the part
  of `P(c,2ρ)` off the positive cells is `Γ ∩ P(c,2ρ)` (`d2cpl_compl_ae_eq_carrier`);
* **buffer** (`d2cpl_scale_lt`, `d2cpl_dist_anchor_lt`, `d2cpl_growth_at_anchor`): a point of
  `Q'_j` gives `s_j < 3ρ` and `d(g_j,c) < (2 + 3C₀)ρ`, so every growth centre in
  `P(g_j, Ch s_j)` and every radius `≤ Ch s_j` is admissible for the hypothesis on
  `P(c,(2 + 3C₀ + 3Ch)ρ)` (centres and radii only: the whole original-source ball is bounded,
  no containment of the growth ball in the buffer is claimed);
* **Hall densities** (`d2cpl_exists_densities`): the Hall inequality on `J` with targets
  `E_j = Γ ∩ P̄(g_j,s_j)` (`d2cpl_target`, compact, `σ(E_j) < ∞`, separable `L¹(σ⌊E_j)`) and the
  proved base countable allocation
  `HallAllocation.exists_countable_hall_allocation_proof` give measurable densities `h_j`
  vanishing off `E_j` with `∫ h_j dσ = μ(Q'_j)` and `Σ_j h_j ≤ D₁` `σ`-a.e.;
* **normalized targets** (`d2cpl_normalized_target`): `τ_j = μ(Q'_j)⁻¹ • σ.withDensity h_j` is a
  probability measure carried by `E_j`, and `μ(Q'_j) • τ_j = σ.withDensity h_j`
  (normalization by `0 < μ(Q'_j) < ∞`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization.ReverseTree

open ParabolicRectifiability.Foundations

/-! ## Clipped cells and the positive-mass reindexing -/

/-- The clipped source cell `Q'_j = Q_j ∩ P(c,2ρ)`. -/
def d2cpl_clip {n : ℕ} (Q : ℕ → Set (Space n)) (c : Space n) (ρ : ℝ) (j : ℕ) :
    Set (Space n) :=
  Q j ∩ Metric.ball c (2 * ρ)

/-- The countable index type of the positive-mass clipped cells, `J = {j : 0 < μ(Q'_j)}`. -/
abbrev d2cpl_Pos {n : ℕ} (μ : Measure (Space n)) (Q : ℕ → Set (Space n)) (c : Space n)
    (ρ : ℝ) : Type :=
  {j : ℕ // 0 < μ (d2cpl_clip Q c ρ j)}

/-- The Hall target `E_j = Γ ∩ P̄(g_j,s_j)`. -/
def d2cpl_target {n : ℕ} (Γ : Set (Space n)) (g : ℕ → Space n) (s : ℕ → ℝ) (j : ℕ) :
    Set (Space n) :=
  Γ ∩ Metric.closedBall (g j) (s j)

theorem d2cpl_clip_subset_cell {n : ℕ} (Q : ℕ → Set (Space n)) (c : Space n) (ρ : ℝ)
    (j : ℕ) : d2cpl_clip Q c ρ j ⊆ Q j :=
  inter_subset_left

theorem d2cpl_clip_subset_ball {n : ℕ} (Q : ℕ → Set (Space n)) (c : Space n) (ρ : ℝ)
    (j : ℕ) : d2cpl_clip Q c ρ j ⊆ Metric.ball c (2 * ρ) :=
  inter_subset_right

theorem d2cpl_measurableSet_clip {n : ℕ} {Q : ℕ → Set (Space n)}
    (hQm : ∀ j, MeasurableSet (Q j)) (c : Space n) (ρ : ℝ) (j : ℕ) :
    MeasurableSet (d2cpl_clip Q c ρ j) :=
  (hQm j).inter measurableSet_ball

theorem d2cpl_pairwise_disjoint_clip {n : ℕ} {Q : ℕ → Set (Space n)}
    (hQd : Pairwise fun i j => Disjoint (Q i) (Q j)) (c : Space n) (ρ : ℝ) :
    Pairwise fun i j => Disjoint (d2cpl_clip Q c ρ i) (d2cpl_clip Q c ρ j) :=
  fun _ _ hij => (hQd hij).mono (d2cpl_clip_subset_cell Q c ρ _) (d2cpl_clip_subset_cell Q c ρ _)

/-- The clipped cells have finite mass: they lie in the bounded ball `P(c,2ρ)`. -/
theorem d2cpl_clip_lt_top {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (Q : ℕ → Set (Space n)) (c : Space n) (ρ : ℝ) (j : ℕ) :
    μ (d2cpl_clip Q c ρ j) < ⊤ :=
  (measure_mono (d2cpl_clip_subset_ball Q c ρ j)).trans_lt (measure_ball_lt_top μ _ _)

/-- The positive-mass clipped cells, reindexed by `J`, are measurable and pairwise disjoint. -/
theorem d2cpl_pos_pairwise_disjoint {n : ℕ} (μ : Measure (Space n)) {Q : ℕ → Set (Space n)}
    (hQd : Pairwise fun i j => Disjoint (Q i) (Q j)) (c : Space n) (ρ : ℝ) :
    Pairwise fun i j : d2cpl_Pos μ Q c ρ =>
      Disjoint (d2cpl_clip Q c ρ i.1) (d2cpl_clip Q c ρ j.1) :=
  fun _ _ hij => d2cpl_pairwise_disjoint_clip hQd c ρ (Subtype.coe_injective.ne hij)

/-- The omitted (zero-mass) clipped cells are null: up to a `μ`-null set, the part of
`P(c,2ρ)` off the positive-mass cells is the on-carrier part `Γ ∩ P(c,2ρ)`. -/
theorem d2cpl_compl_ae_eq_carrier {n : ℕ} (μ : Measure (Space n)) (Γ : Set (Space n))
    (Q : ℕ → Set (Space n)) (hQU : (⋃ j, Q j) = Γᶜ) (c : Space n) (ρ : ℝ) :
    ((⋃ j : d2cpl_Pos μ Q c ρ, d2cpl_clip Q c ρ j.1)ᶜ ∩ Metric.ball c (2 * ρ) :
        Set (Space n)) =ᵐ[μ] (Γ ∩ Metric.ball c (2 * ρ) : Set (Space n)) := by
  have hnull : μ (⋃ j : {j : ℕ // μ (d2cpl_clip Q c ρ j) = 0}, d2cpl_clip Q c ρ j.1) = 0 :=
    measure_iUnion_null fun j => j.2
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null ?_ hnull
    rintro y ⟨⟨hyU, hyB⟩, hyΓ⟩
    have hyΓ' : y ∈ Γᶜ := Set.mem_compl fun h => hyΓ ⟨h, hyB⟩
    rw [← hQU, mem_iUnion] at hyΓ'
    obtain ⟨j, hj⟩ := hyΓ'
    have hjclip : y ∈ d2cpl_clip Q c ρ j := ⟨hj, hyB⟩
    have hj0 : μ (d2cpl_clip Q c ρ j) = 0 := by
      by_contra hne
      exact hyU (mem_iUnion.mpr ⟨⟨j, pos_iff_ne_zero.mpr hne⟩, hjclip⟩)
    exact mem_iUnion.mpr ⟨⟨j, hj0⟩, hjclip⟩
  · rw [Set.sdiff_eq_empty.mpr, measure_empty]
    rintro y ⟨hyΓ, hyB⟩
    refine ⟨Set.mem_compl fun hyU => ?_, hyB⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hyU
    have hyc : y ∈ Γᶜ := hQU ▸ mem_iUnion.mpr ⟨j.1, d2cpl_clip_subset_cell Q c ρ j.1 hj⟩
    exact hyc hyΓ

/-! ## The buffer: centres and radii of the Hall growth hypothesis -/

/-- A point `y ∈ P(c,2ρ)` has `dist(y,Γ) < 3ρ` when `Γ` meets `P(c,ρ)`; hence `s_j < 3ρ` for a
cell scale `s_j ≤ dist(y,Γ)`. -/
theorem d2cpl_scale_lt {n : ℕ} {Γ : Set (Space n)} {c : Space n} {ρ : ℝ}
    (hΓc : (Metric.ball c ρ ∩ Γ).Nonempty) {y : Space n} (hy : y ∈ Metric.ball c (2 * ρ))
    {r : ℝ} (hr : r ≤ Metric.infDist y Γ) : r < 3 * ρ := by
  obtain ⟨x, hxc, hxΓ⟩ := hΓc
  have h1 : dist y c < 2 * ρ := Metric.mem_ball.mp hy
  have h2 : dist c x < ρ := by rw [dist_comm]; exact Metric.mem_ball.mp hxc
  calc r ≤ Metric.infDist y Γ := hr
    _ ≤ dist y x := Metric.infDist_le_dist_of_mem hxΓ
    _ ≤ dist y c + dist c x := dist_triangle _ _ _
    _ < 2 * ρ + ρ := add_lt_add h1 h2
    _ = 3 * ρ := by ring

/-- The anchor of a cell meeting `P(c,2ρ)` at scale `r < 3ρ` lies in `P(c,(2 + 3C₀)ρ)`. -/
theorem d2cpl_dist_anchor_lt {n : ℕ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {c a y : Space n} {ρ r : ℝ}
    (hy : y ∈ Metric.ball c (2 * ρ)) (hya : y ∈ Metric.ball a (C₀ * r)) (hr : r < 3 * ρ) :
    dist a c < (2 + 3 * C₀) * ρ := by
  have h1 : dist a y < C₀ * r := by rw [dist_comm]; exact Metric.mem_ball.mp hya
  have h2 : dist y c < 2 * ρ := Metric.mem_ball.mp hy
  have h3 : C₀ * r ≤ C₀ * (3 * ρ) := mul_le_mul_of_nonneg_left hr.le hC₀
  calc dist a c ≤ dist a y + dist y c := dist_triangle _ _ _
    _ < C₀ * r + 2 * ρ := add_lt_add h1 h2
    _ ≤ (2 + 3 * C₀) * ρ := by linarith

/-- **Buffer.** Upper growth on `supp μ ∩ P(c,(2 + 3C₀ + 3Ch)ρ)` up to that radius gives upper
growth on `supp μ ∩ P(a, Ch r)` up to radius `Ch r`, for an anchor `a ∈ P(c,(2 + 3C₀)ρ)` and a
scale `r < 3ρ`. Only the centres and radii are checked: the hypothesis bounds the whole
`μ(P(b,t))`. -/
theorem d2cpl_growth_at_anchor {n k : ℕ} {μ : Measure (Space n)} {A C₀ Ch : ℝ}
    (hCh : 0 ≤ Ch) {c : Space n} {ρ : ℝ}
    (hgrowth : ∀ b ∈ μ.support ∩ Metric.ball c ((2 + 3 * C₀ + 3 * Ch) * ρ), ∀ t : ℝ, 0 < t →
      t ≤ (2 + 3 * C₀ + 3 * Ch) * ρ → μ (Metric.ball b t) ≤ ENNReal.ofReal (A * t ^ k))
    {a : Space n} {r : ℝ} (hr : r < 3 * ρ) (ha : dist a c < (2 + 3 * C₀) * ρ) :
    ∀ b ∈ μ.support ∩ Metric.ball a (Ch * r), ∀ t : ℝ, 0 < t → t ≤ Ch * r →
      μ (Metric.ball b t) ≤ ENNReal.ofReal (A * t ^ k) := by
  intro b hb t ht htr
  have hChr : Ch * r ≤ Ch * (3 * ρ) := mul_le_mul_of_nonneg_left hr.le hCh
  have hb' : dist b a < Ch * r := Metric.mem_ball.mp hb.2
  refine hgrowth b ⟨hb.1, ?_⟩ t ht ?_
  · rw [Metric.mem_ball]
    calc dist b c ≤ dist b a + dist a c := dist_triangle _ _ _
      _ < Ch * r + (2 + 3 * C₀) * ρ := add_lt_add hb' ha
      _ ≤ (2 + 3 * C₀ + 3 * Ch) * ρ := by linarith
  · have h2 : 0 ≤ (2 + 3 * C₀) * ρ := le_of_lt (lt_of_le_of_lt dist_nonneg ha)
    linarith

/-- Upper growth at a smaller centre ball and smaller radii (used at radius `2ρ` for the
on-carrier comparison). -/
theorem d2cpl_growth_mono {n k : ℕ} {μ : Measure (Space n)} {A R R' : ℝ} {c : Space n}
    (hRR' : R' ≤ R)
    (hgrowth : ∀ b ∈ μ.support ∩ Metric.ball c R, ∀ t : ℝ, 0 < t → t ≤ R →
      μ (Metric.ball b t) ≤ ENNReal.ofReal (A * t ^ k)) :
    ∀ b ∈ μ.support ∩ Metric.ball c R', ∀ t : ℝ, 0 < t → t ≤ R' →
      μ (Metric.ball b t) ≤ ENNReal.ofReal (A * t ^ k) :=
  fun b hb t ht htR => hgrowth b ⟨hb.1, Metric.ball_subset_ball hRR' hb.2⟩ t ht (htR.trans hRR')

/-! ## Hall targets and the separability instance -/

theorem d2cpl_measurableSet_target {n : ℕ} {Γ : Set (Space n)} (hΓ : IsClosed Γ)
    (g : ℕ → Space n) (s : ℕ → ℝ) (j : ℕ) : MeasurableSet (d2cpl_target Γ g s j) :=
  hΓ.measurableSet.inter Metric.isClosed_closedBall.measurableSet

/-- The Hall targets have finite `σ`-mass: they lie in compact closed balls. -/
theorem d2cpl_target_lt_top {n : ℕ} (σ : Measure (Space n)) [IsFiniteMeasureOnCompacts σ]
    (Γ : Set (Space n)) (g : ℕ → Space n) (s : ℕ → ℝ) (j : ℕ) :
    σ (d2cpl_target Γ g s j) < ⊤ :=
  (measure_mono inter_subset_right).trans_lt (measure_closedBall_lt_top σ _ _)

/-- `L¹(σ⌊S)` is separable for a set `S` of finite `σ`-mass (as in
`exists_whitney_source_allocation_proof`). -/
theorem d2cpl_separable {n : ℕ} (σ : Measure (Space n)) (S : Set (Space n)) (hS : σ S < ⊤) :
    TopologicalSpace.SeparableSpace (Lp ℝ 1 (σ.restrict S)) := by
  have : IsFiniteMeasure (σ.restrict S) := isFiniteMeasure_restrict.mpr hS.ne
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  have : SFinite (σ.restrict S) := inferInstance
  have : MeasureTheory.IsSeparable (σ.restrict S) := inferInstance
  have : SecondCountableTopology (Lp ℝ 1 (σ.restrict S)) :=
    MeasureTheory.Lp.SecondCountableTopology
  infer_instance

/-! ## The Hall densities -/

/-- **Hall densities**. Given the Hall inequality clause at fixed
constants `(C₀, Ch, A, D₁)` (the body of `HallInequalityStatement` after its existentials),
Whitney cells of `Γ = supp σ`, a model ball `P(c,ρ)` meeting `Γ` and upper growth on
`supp μ ∩ P(c,(2 + 3C₀ + 3Ch)ρ)`: there are measurable densities `h_j`, `j ∈ J`, vanishing off
`E_j = Γ ∩ P̄(g_j,s_j)`, with `∫ h_j dσ = μ(Q'_j)` and `Σ_j h_j ≤ D₁` `σ`-a.e. -/
theorem d2cpl_exists_densities {n k : ℕ} {Aref C₀ Ch A D₁ : ℝ} (hC₀ : 1 ≤ C₀) (hCh : 1 ≤ Ch)
    (hD₁ : 0 < D₁)
    (hHall : ∀ (μ σ : Measure (Space n)) (Γ : Set (Space n)), σ.support = Γ →
      IsADR Aref k σ →
      ∀ (ι : Type) (Q : ι → Set (Space n)) (g : ι → Space n) (s : ι → ℝ),
        (∀ j, MeasurableSet (Q j)) → (Pairwise fun i j => Disjoint (Q i) (Q j)) →
        (∀ j, g j ∈ Γ) → (∀ j, 0 < s j) → (∀ j, Q j ⊆ Metric.ball (g j) (C₀ * s j)) →
        (∀ j, ∀ b ∈ μ.support ∩ Metric.ball (g j) (Ch * s j), ∀ t : ℝ, 0 < t →
          t ≤ Ch * s j → μ (Metric.ball b t) ≤ ENNReal.ofReal (A * t ^ k)) →
        ∀ I : Finset ι, ∑ j ∈ I, μ (Q j) ≤
          ENNReal.ofReal D₁ * σ (⋃ j ∈ I, Γ ∩ Metric.closedBall (g j) (s j)))
    (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (Γ : Set (Space n)) (σ : Measure (Space n)) [IsFiniteMeasureOnCompacts σ]
    (hσΓ : σ.support = Γ) (hADR : IsADR Aref k σ)
    (Q : ℕ → Set (Space n)) (g : ℕ → Space n) (s : ℕ → ℝ)
    (hQm : ∀ j, MeasurableSet (Q j)) (hQd : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hg : ∀ j, g j ∈ Γ) (hs : ∀ j, 0 < s j)
    (hQsub : ∀ j, Q j ⊆ Metric.ball (g j) (C₀ * s j))
    (hle : ∀ j, ∀ y ∈ Q j, s j ≤ Metric.infDist y Γ)
    (c : Space n) (ρ : ℝ) (hΓc : (Metric.ball c ρ ∩ Γ).Nonempty)
    (hgrowth : ∀ b ∈ μ.support ∩ Metric.ball c ((2 + 3 * C₀ + 3 * Ch) * ρ), ∀ t : ℝ, 0 < t →
      t ≤ (2 + 3 * C₀ + 3 * Ch) * ρ → μ (Metric.ball b t) ≤ ENNReal.ofReal (A * t ^ k)) :
    ∃ h : d2cpl_Pos μ Q c ρ → Space n → ℝ≥0∞, (∀ j, Measurable (h j)) ∧
      (∀ j, ∀ x ∉ d2cpl_target Γ g s j.1, h j x = 0) ∧
      (∀ j, ∫⁻ x, h j x ∂σ = μ (d2cpl_clip Q c ρ j.1)) ∧
      ∀ᵐ x ∂σ, ∑' j, h j x ≤ ENNReal.ofReal D₁ := by
  have hΓcl : IsClosed Γ := by rw [← hσΓ]; exact Measure.isClosed_support
  -- The Hall growth hypothesis at every positive-mass cell (buffer).
  have hgrowthJ : ∀ j : d2cpl_Pos μ Q c ρ,
      ∀ b ∈ μ.support ∩ Metric.ball (g j.1) (Ch * s j.1), ∀ t : ℝ, 0 < t →
        t ≤ Ch * s j.1 → μ (Metric.ball b t) ≤ ENNReal.ofReal (A * t ^ k) := by
    intro j
    obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero j.2.ne'
    have hyQ : y ∈ Q j.1 := d2cpl_clip_subset_cell Q c ρ j.1 hy
    have hyB : y ∈ Metric.ball c (2 * ρ) := d2cpl_clip_subset_ball Q c ρ j.1 hy
    have hsj : s j.1 < 3 * ρ := d2cpl_scale_lt hΓc hyB (hle j.1 y hyQ)
    have hgj : dist (g j.1) c < (2 + 3 * C₀) * ρ :=
      d2cpl_dist_anchor_lt (by linarith) hyB (hQsub j.1 hyQ) hsj
    exact d2cpl_growth_at_anchor (by linarith) hgrowth hsj hgj
  -- The Hall inequality on the positive-mass cells.
  have hHallJ : ∀ I : Finset (d2cpl_Pos μ Q c ρ), ∑ j ∈ I, μ (d2cpl_clip Q c ρ j.1) ≤
      ENNReal.ofReal D₁ * σ (⋃ j ∈ I, d2cpl_target Γ g s j.1) :=
    hHall μ σ Γ hσΓ hADR (d2cpl_Pos μ Q c ρ) (fun j => d2cpl_clip Q c ρ j.1)
      (fun j => g j.1) (fun j => s j.1) (fun j => d2cpl_measurableSet_clip hQm c ρ j.1)
      (d2cpl_pos_pairwise_disjoint μ hQd c ρ) (fun j => hg j.1) (fun j => hs j.1)
      (fun j => (d2cpl_clip_subset_cell Q c ρ j.1).trans (hQsub j.1)) hgrowthJ
  -- Demands and capacity in `ℝ≥0`.
  set w : d2cpl_Pos μ Q c ρ → ℝ≥0 := fun j => (μ (d2cpl_clip Q c ρ j.1)).toNNReal
  have hwcoe : ∀ j, (w j : ℝ≥0∞) = μ (d2cpl_clip Q c ρ j.1) := fun j =>
    ENNReal.coe_toNNReal (d2cpl_clip_lt_top μ Q c ρ j.1).ne
  have hwpos : ∀ j, 0 < w j := fun j =>
    ENNReal.toNNReal_pos j.2.ne' (d2cpl_clip_lt_top μ Q c ρ j.1).ne
  have hH : ∀ I : Finset (d2cpl_Pos μ Q c ρ), ∑ j ∈ I, (w j : ℝ≥0∞) ≤
      (D₁.toNNReal : ℝ≥0∞) * σ (⋃ j ∈ I, d2cpl_target Γ g s j.1) := by
    intro I
    calc ∑ j ∈ I, (w j : ℝ≥0∞) = ∑ j ∈ I, μ (d2cpl_clip Q c ρ j.1) :=
          Finset.sum_congr rfl fun j _ => hwcoe j
      _ ≤ _ := hHallJ I
  -- The proved countable Hall allocation (weak-* compactness of bounded densities).
  obtain ⟨h, hmeas, hzero, hint, hsum⟩ := HallAllocation.exists_countable_hall_allocation_proof
    (HallAllocation.hall_allocation_iff_proof exists_transport_of_hall_condition_proof)
    exists_weakly_convergent_density_subseq_proof σ
    (fun j : d2cpl_Pos μ Q c ρ => d2cpl_target Γ g s j.1)
    (fun j => d2cpl_measurableSet_target hΓcl g s j.1)
    (fun j => d2cpl_target_lt_top σ Γ g s j.1)
    (fun j => d2cpl_separable σ _ (d2cpl_target_lt_top σ Γ g s j.1)) w hwpos D₁.toNNReal
    (Real.toNNReal_pos.mpr hD₁) hH
  exact ⟨h, hmeas, hzero, fun j => (hint j).trans (hwcoe j), hsum⟩

/-! ## Normalized target probabilities -/

/-- **Normalization**. For a density `h` carried by `E` with
`∫ h dσ = m`, `0 < m < ∞`, the measure `τ = m⁻¹ • σ.withDensity h` is a probability measure
carried by `E`, and `m • τ = σ.withDensity h`. -/
theorem d2cpl_normalized_target {X : Type*} [MeasurableSpace X] (σ : Measure X)
    {h : X → ℝ≥0∞} (hm : Measurable h) {E : Set X} (hzero : ∀ x ∉ E, h x = 0) {m : ℝ≥0∞}
    (hint : ∫⁻ x, h x ∂σ = m) (hm0 : m ≠ 0) (hmt : m ≠ ⊤) :
    IsProbabilityMeasure (m⁻¹ • σ.withDensity h) ∧ (m⁻¹ • σ.withDensity h) Eᶜ = 0 ∧
      m • (m⁻¹ • σ.withDensity h) = σ.withDensity h := by
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, hint]
    exact ENNReal.inv_mul_cancel hm0 hmt
  · rw [Measure.smul_apply, smul_eq_mul]
    have hnull : σ.withDensity h Eᶜ = 0 := by
      rw [withDensity_apply_eq_zero' hm.aemeasurable]
      have : {x | h x ≠ 0} ∩ Eᶜ = ∅ := by
        refine Set.subset_empty_iff.mp ?_
        rintro x ⟨hx, hxE⟩
        exact (hx (hzero x hxE)).elim
      rw [this, measure_empty]
    rw [hnull, mul_zero]
  · rw [smul_smul, ENNReal.mul_inv_cancel hm0 hmt, one_smul]

/-- The normalized targets of the positive-mass cells: `τ_j = μ(Q'_j)⁻¹ • σ.withDensity h_j`. -/
def d2cpl_tau {n : ℕ} (μ σ : Measure (Space n)) (Q : ℕ → Set (Space n)) (c : Space n)
    (ρ : ℝ) (h : d2cpl_Pos μ Q c ρ → Space n → ℝ≥0∞) (j : d2cpl_Pos μ Q c ρ) :
    Measure (Space n) :=
  (μ (d2cpl_clip Q c ρ j.1))⁻¹ • σ.withDensity (h j)

/-- The normalized targets are probability measures carried by `E_j`, and
`μ(Q'_j) • τ_j = σ.withDensity h_j` (normalization by `0 < μ(Q'_j) < ∞`). -/
theorem d2cpl_tau_spec {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (σ : Measure (Space n)) (Γ : Set (Space n)) (Q : ℕ → Set (Space n)) (g : ℕ → Space n)
    (s : ℕ → ℝ) (c : Space n) (ρ : ℝ) (h : d2cpl_Pos μ Q c ρ → Space n → ℝ≥0∞)
    (hmeas : ∀ j, Measurable (h j)) (hzero : ∀ j, ∀ x ∉ d2cpl_target Γ g s j.1, h j x = 0)
    (hint : ∀ j, ∫⁻ x, h j x ∂σ = μ (d2cpl_clip Q c ρ j.1)) (j : d2cpl_Pos μ Q c ρ) :
    IsProbabilityMeasure (d2cpl_tau μ σ Q c ρ h j) ∧
      d2cpl_tau μ σ Q c ρ h j (d2cpl_target Γ g s j.1)ᶜ = 0 ∧
      μ (d2cpl_clip Q c ρ j.1) • d2cpl_tau μ σ Q c ρ h j = σ.withDensity (h j) :=
  d2cpl_normalized_target σ (hmeas j) (hzero j) (hint j) j.2.ne'
    (d2cpl_clip_lt_top μ Q c ρ j.1).ne

end ParabolicRectifiability.QuantitativeCharacterization.ReverseTree
