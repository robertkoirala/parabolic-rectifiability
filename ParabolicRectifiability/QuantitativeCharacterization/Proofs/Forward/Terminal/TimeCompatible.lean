import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.Measure.Neck.PlaneTime.TimeCompatibility

/-! # Horizontal recorded-time compatibility of all records

Proof of `d1c_timeCompatible_proof`, in implication form:

`GenuineTimeStatement → RootThinnessStatement → StageFactsStatement → CoreEqualityStatement →
TimeCompatibleStatement`.

The four statements enter only as hypotheses.

Route. Every record of `C.family 𝒢 fits` with centre set `C.centers 𝒢` and radii `C.radius 𝒢` is
of one of three kinds (`d1ctcomp_Kind`, `d1ctcomp_record_kind`):
* a point with a survival history at its recorded scale: a genuine occurrence of level `j ≥ 1`
  (`cand_history`) or a terminal centre (`term_history`);
* the artificial root, recorded at scale `r₀ = 48 ℓ_*` (level `0`);
* a core point of `𝒞₀` that is not a terminal centre, recorded at scale `0`.

Pairs of histories: the hypothesis `GenuineTimeStatement`. The root against any record: every
position other than the root lies in `closure S` (core equality gives `𝒞₀ ⊆ closure S_0`), so the
initial tube (`RootThinnessStatement` at tolerance `min η 1`) gives
`|t_w - τ_*| ≤ (min η 1 · ℓ_*)² ≤ η r₀²`. Core records: limits of candidates whose levels tend to
infinity (`CoreEqualityStatement`), with recorded scales `r_level → 0`; base `ms3_tc_limit` once
(core against a history) or twice (two core points), with `ms3_tc_symm`.

Constants, in the order of the statement: `Λ₀ = max Λ₀^gen Λ₀^root`; for `Λ ≥ Λ₀`,
`B = max B^gen B^root`; for `η > 0`, `b₀ = min b₀^gen(η) b₀^root(min η 1)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section Helpers

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- Local ADR on a larger buffer gives local ADR on a smaller one. -/
theorem d1ctcomp_localADR_mono {A : ℝ} {a : Space n} {ρ ρ' : ℝ} (h : LocalADR μ k A a ρ)
    (hρ : ρ' ≤ ρ) : LocalADR μ k A a ρ' := by
  intro x hx s hs hsρ
  exact h x ⟨hx.1, Metric.ball_subset_ball hρ hx.2⟩ s hs (hsρ.trans hρ)

/-- The three kinds of records, as a physical point with its recorded scale. -/
def d1ctcomp_Kind (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (q : Space n) (s : ℝ) : Prop :=
  C.HasHistory 𝒢 q s ∨ (q = rootCenter 𝒢 ∧ s = stageScale 𝒢 0) ∨ (q ∈ 𝒢.limitCore ∧ s = 0)

/-- Every record is a history point, the artificial root, or a core point with scale zero. -/
theorem d1ctcomp_record_kind {𝒢 : GoodRegion P μ k Λ b} (fits : LocalFits 𝒢) {C : Choice n}
    (hSF : C.StageFacts 𝒢) {z : NeckRecord n (Space n)}
    (hz : NeckRecord.IsRecord (C.family 𝒢 fits) (C.centers 𝒢) z) :
    d1ctcomp_Kind C 𝒢 (NeckRecord.position (C.family 𝒢 fits) z)
      (NeckRecord.scale (C.family 𝒢 fits) (C.radius 𝒢) z) := by
  rcases z with ⟨j, a⟩ | c
  · have ha : a ∈ (if j = 0 then ({rootCenter 𝒢} : Finset (Space n)) else C.candSet j) := hz
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [ite_eq_left rfl, Finset.mem_singleton] at ha
      exact Or.inr (Or.inl ⟨ha, rfl⟩)
    · rw [ite_eq_right hj.ne'] at ha
      unfold Choice.candSet at ha
      classical
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      exact Or.inl (hSF.cand_history j hj i (Finset.mem_range.1 hi))
  · have hc : c ∈ 𝒢.limitCore ∨ C.IsTermCenter c := hz
    by_cases ht : C.IsTermCenter c
    · exact Or.inl (hSF.term_history c ht)
    · refine Or.inr (Or.inr ⟨hc.resolve_right ht, ?_⟩)
      show C.radius 𝒢 c = 0
      unfold Choice.radius
      exact ite_eq_right ht

/-- The construction scales along levels tending to infinity tend to zero. -/
theorem d1ctcomp_stageScale_tendsto (𝒢 : GoodRegion P μ k Λ b) {level : ℕ → ℕ}
    (hlev : Tendsto level atTop atTop) :
    Tendsto (fun m => stageScale 𝒢 (level m)) atTop (𝓝 0) := by
  have h : Tendsto (fun j : ℕ => 48 * 𝒢.rootScale / 10 ^ j) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact h.comp hlev

/-- The initial tube at tolerance `min η 1` fits inside `η r₀²`. -/
theorem d1ctcomp_root_sq {η : ℝ} (hη : 0 < η) (𝒢 : GoodRegion P μ k Λ b) :
    (min η 1 * 𝒢.rootScale) ^ 2 ≤ η * stageScale 𝒢 0 ^ 2 := by
  have h0 : stageScale 𝒢 0 = 48 * 𝒢.rootScale := by
    simp only [stageScale, coherentScale, pow_zero, div_one]
  rw [h0]
  have hm0 : 0 < min η 1 := lt_min hη one_pos
  have hm1 : min η 1 ≤ 1 := min_le_right _ _
  have hmη : min η 1 ≤ η := min_le_left _ _
  have hm2 : min η 1 ^ 2 ≤ η := by nlinarith
  have hl : 𝒢.rootScale ^ 2 ≤ (48 * 𝒢.rootScale) ^ 2 := by nlinarith [sq_nonneg 𝒢.rootScale]
  calc (min η 1 * 𝒢.rootScale) ^ 2 = min η 1 ^ 2 * 𝒢.rootScale ^ 2 := mul_pow _ _ _
    _ ≤ η * 𝒢.rootScale ^ 2 := mul_le_mul_of_nonneg_right hm2 (sq_nonneg _)
    _ ≤ η * (48 * 𝒢.rootScale) ^ 2 := mul_le_mul_of_nonneg_left hl hη.le

variable {𝒢 : GoodRegion P μ k Λ b} {C : Choice n} {γ : ℝ}

/-- A core point against a history point: limit of the genuine inequality along candidates. -/
theorem d1ctcomp_core_hist
    (hgen : ∀ (z w : Space n) (s s' : ℝ), C.HasHistory 𝒢 z s → C.HasHistory 𝒢 w s' →
      |z.2.val - w.2.val| ≤ γ * max (‖z.1 - w.1‖ ^ 2) (max (s ^ 2) (s' ^ 2)))
    (hcore : ∀ z ∈ 𝒢.limitCore, ∃ (level : ℕ → ℕ) (idx : ℕ → ℕ),
      (∀ m, 1 ≤ level m ∧ idx m < C.candCount (level m)) ∧
      Tendsto level atTop atTop ∧ Tendsto (fun m => C.cand (level m) (idx m)) atTop (𝓝 z))
    (hSF : C.StageFacts 𝒢) {c w : Space n} {s' : ℝ} (hc : c ∈ 𝒢.limitCore)
    (hw : C.HasHistory 𝒢 w s') :
    |c.2.val - w.2.val| ≤ γ * max (‖c.1 - w.1‖ ^ 2) (max (0 ^ 2) (s' ^ 2)) := by
  obtain ⟨level, idx, hli, hlev, hlim⟩ := hcore c hc
  exact ms3_tc_limit hlim (d1ctcomp_stageScale_tendsto 𝒢 hlev) fun m =>
    hgen _ _ _ _ (hSF.cand_history _ (hli m).1 _ (hli m).2) hw

/-- Two core points: the core-against-history inequality, passed to a second limit. -/
theorem d1ctcomp_core_core
    (hgen : ∀ (z w : Space n) (s s' : ℝ), C.HasHistory 𝒢 z s → C.HasHistory 𝒢 w s' →
      |z.2.val - w.2.val| ≤ γ * max (‖z.1 - w.1‖ ^ 2) (max (s ^ 2) (s' ^ 2)))
    (hcore : ∀ z ∈ 𝒢.limitCore, ∃ (level : ℕ → ℕ) (idx : ℕ → ℕ),
      (∀ m, 1 ≤ level m ∧ idx m < C.candCount (level m)) ∧
      Tendsto level atTop atTop ∧ Tendsto (fun m => C.cand (level m) (idx m)) atTop (𝓝 z))
    (hSF : C.StageFacts 𝒢) {c c' : Space n} (hc : c ∈ 𝒢.limitCore) (hc' : c' ∈ 𝒢.limitCore) :
    |c.2.val - c'.2.val| ≤ γ * max (‖c.1 - c'.1‖ ^ 2) (max (0 ^ 2) (0 ^ 2)) := by
  obtain ⟨level, idx, hli, hlev, hlim⟩ := hcore c hc
  exact ms3_tc_limit hlim (d1ctcomp_stageScale_tendsto 𝒢 hlev) fun m =>
    ms3_tc_symm (d1ctcomp_core_hist hgen hcore hSF hc'
      (hSF.cand_history _ (hli m).1 _ (hli m).2))

/-- The record inequality for any two kinds of records, from the genuine inequality, the core
limits, and the initial-tube band around the root time. -/
theorem d1ctcomp_kind_pair (hγ : 0 ≤ γ)
    (hgen : ∀ (z w : Space n) (s s' : ℝ), C.HasHistory 𝒢 z s → C.HasHistory 𝒢 w s' →
      |z.2.val - w.2.val| ≤ γ * max (‖z.1 - w.1‖ ^ 2) (max (s ^ 2) (s' ^ 2)))
    (hcore : ∀ z ∈ 𝒢.limitCore, ∃ (level : ℕ → ℕ) (idx : ℕ → ℕ),
      (∀ m, 1 ≤ level m ∧ idx m < C.candCount (level m)) ∧
      Tendsto level atTop atTop ∧ Tendsto (fun m => C.cand (level m) (idx m)) atTop (𝓝 z))
    (hSF : C.StageFacts 𝒢) (hcoreS : 𝒢.limitCore ⊆ closure 𝒢.rootCell)
    (hband : ∀ q ∈ closure 𝒢.rootCell,
      |q.2.val - (rootCenter 𝒢).2.val| ≤ γ * stageScale 𝒢 0 ^ 2)
    (p q : Space n) (s t : ℝ) (hp : d1ctcomp_Kind C 𝒢 p s) (hq : d1ctcomp_Kind C 𝒢 q t) :
    |p.2.val - q.2.val| ≤ γ * max (‖p.1 - q.1‖ ^ 2) (max (s ^ 2) (t ^ 2)) := by
  have hrootL : ∀ (q : Space n) (t : ℝ), d1ctcomp_Kind C 𝒢 q t →
      |(rootCenter 𝒢).2.val - q.2.val| ≤
        γ * max (‖(rootCenter 𝒢).1 - q.1‖ ^ 2) (max (stageScale 𝒢 0 ^ 2) (t ^ 2)) := by
    intro q t hq
    have hnn : 0 ≤ γ * max (‖(rootCenter 𝒢).1 - q.1‖ ^ 2) (max (stageScale 𝒢 0 ^ 2) (t ^ 2)) :=
      mul_nonneg hγ ((sq_nonneg _).trans (le_max_left _ _))
    have hle : γ * stageScale 𝒢 0 ^ 2 ≤
        γ * max (‖(rootCenter 𝒢).1 - q.1‖ ^ 2) (max (stageScale 𝒢 0 ^ 2) (t ^ 2)) :=
      mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_right _ _)) hγ
    unfold d1ctcomp_Kind at hq
    rcases hq with hq | ⟨rfl, -⟩ | ⟨hq, -⟩
    · have hqS : q ∈ 𝒢.rootCell := by
        unfold Choice.HasHistory at hq
        exact hq.2.1
      rw [abs_sub_comm]
      exact (hband q (subset_closure hqS)).trans hle
    · rw [sub_self, abs_zero]
      exact hnn
    · rw [abs_sub_comm]
      exact (hband q (hcoreS hq)).trans hle
  unfold d1ctcomp_Kind at hp hq
  rcases hp with hp | ⟨rfl, rfl⟩ | ⟨hp, rfl⟩
  · rcases hq with hq | ⟨rfl, rfl⟩ | ⟨hq, rfl⟩
    · exact hgen p q s t hp hq
    · exact ms3_tc_symm (hrootL p s (Or.inl hp))
    · exact ms3_tc_symm (d1ctcomp_core_hist hgen hcore hSF hq hp)
  · exact hrootL q t hq
  · rcases hq with hq | ⟨rfl, rfl⟩ | ⟨hq, rfl⟩
    · exact d1ctcomp_core_hist hgen hcore hSF hp hq
    · exact ms3_tc_symm (hrootL p 0 (Or.inr (Or.inr ⟨hp, rfl⟩)))
    · exact d1ctcomp_core_core hgen hcore hSF hp hq

end Helpers

/-- **Horizontal recorded-time compatibility of all records** (`TimeCompatibleStatement`). Constants: `Λ₀ = max Λ₀^gen Λ₀^root`,
`B = max B^gen B^root`, `b₀ = min b₀^gen(η) b₀^root(min η 1)`. -/
theorem d1c_timeCompatible_proof :
    GenuineTimeStatement → RootThinnessStatement → StageFactsStatement →
      CoreEqualityStatement → TimeCompatibleStatement := by
  intro hGT hRT hSF hCE n hn k hk1 hk2 A hA
  obtain ⟨Λ₁, hΛ₁, hGT1⟩ := hGT n hn k hk1 hk2 A hA
  obtain ⟨Λ₂, -, hRT1⟩ := hRT n hn k hk1 hk2 A hA
  refine ⟨max Λ₁ Λ₂, le_max_of_le_left hΛ₁, fun Λ hΛ => ?_⟩
  obtain ⟨B₁, hB₁, hGT2⟩ := hGT1 Λ (le_of_max_le_left hΛ)
  obtain ⟨B₂, -, hRT2⟩ := hRT1 Λ (le_of_max_le_right hΛ)
  refine ⟨max B₁ B₂, le_max_of_le_left hB₁, fun η hη => ?_⟩
  obtain ⟨b₁, hb₁, hGT3⟩ := hGT2 η hη
  obtain ⟨b₂, hb₂, hRT3⟩ := hRT2 (min η 1) (lt_min hη one_pos)
  refine ⟨min b₁ b₂, lt_min hb₁ hb₂, fun b hb hbb => ?_⟩
  intro μ hμ1 hμ2 a ha R hR hADR P 𝒢 hF fits C hC hH
  have hADR₁ : LocalADR μ k A a (B₁ * R) :=
    d1ctcomp_localADR_mono hADR (mul_le_mul_of_nonneg_right (le_max_left _ _) hR.le)
  have hADR₂ : LocalADR μ k A a (B₂ * R) :=
    d1ctcomp_localADR_mono hADR (mul_le_mul_of_nonneg_right (le_max_right _ _) hR.le)
  have hgen := hGT3 b hb (hbb.trans (min_le_left _ _)) μ hμ1 hμ2 a ha R hR hADR₁ P 𝒢 hF C hC hH
  have hroot := (hRT3 b hb (hbb.trans (min_le_right _ _)) μ hμ1 hμ2 a ha R hR hADR₂ P 𝒢 hF).1
  have hsf : C.StageFacts 𝒢 := hSF n μ.support R P μ k Λ b 𝒢 C hC
  have hce := hCE n μ.support R P μ k Λ b 𝒢 C hC
  have hτ : (rootCenter 𝒢).2.val = NeckSelection.modelTime 𝒢.type (𝒢.model 𝒢.root) := by
    rw [rootCenter, ite_eq_left hH]
    rfl
  have hband : ∀ q ∈ closure 𝒢.rootCell,
      |q.2.val - (rootCenter 𝒢).2.val| ≤ η * stageScale 𝒢 0 ^ 2 := by
    intro q hq
    rw [hτ]
    exact ((hroot q hq).2.2 hH).trans (d1ctcomp_root_sq hη 𝒢)
  have hcoreS : 𝒢.limitCore ⊆ closure 𝒢.rootCell := by
    intro c hc
    rw [← hce.1] at hc
    exact closure_mono (hsf.kept_subset 0) (mem_iInter.1 hc 0)
  unfold RecordsTimeCompatible
  intro z w hz hw
  exact d1ctcomp_kind_pair hη.le hgen hce.2 hsf hcoreS hband _ _ _ _
    (d1ctcomp_record_kind fits hsf hz) (d1ctcomp_record_kind fits hsf hw)

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
