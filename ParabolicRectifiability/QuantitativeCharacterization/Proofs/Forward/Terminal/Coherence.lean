import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # Coherence of the terminal family (`d1c_coherence`)

This module proves `d1c_coherence_proof`, in implication form:

`SameLevelStatement → AdjacentLevelStatement → RootAdjacentStatement → RootThinnessStatement →
StageFactsStatement → CoherenceStatement`.

The base notion is `CoherentFamily.IsCoherentUpTo`.

Constants, in the order of the statement: given `(n, k, A)`, the four estimate hypotheses (same,
adjacent, root comparison, root thinness) give `Λ₀^s, Λ₀^a, Λ₀^r, Λ₀^t`; take `Λ₀` their maximum.
For `Λ ≥ Λ₀` they give `B^s, B^a, B^r, B^t`; take `B` their maximum (local ADR in `P(a, B R)`
restricts to every smaller buffer). For `η > 0` take `b₀ = min(b₀^s(η), b₀^a(η), b₀^r(η),
b₀^t(1))`: root thinness is used only at tolerance `1`.

Fields of `IsCoherentUpTo (1/4) η N` for the family `C.family 𝒢 fits`:
* separation: level `0` is the singleton `{x_*}`; at level `j ≥ 1` distinct indices are distinct
  candidates, `κ_net r_j`-separated (`cand_separated`), `κ_net ≥ 1/4`;
* parents: level `1` → the artificial root, with `d_P(g, x_*) ≤ d_P(g, q) + d_P(q, x_*) <
  2 ℓ_* + ℓ_* ≤ r₀` (root cell, root thinness at tolerance `1`); level `j + 1 ≥ 2` →
  `parentOf j`, a candidate of stage `j` within `κ_net r_j ≤ r_j` (`cand_mem`,
  `kept_succ_subset`, `parentOf_spec`);
* root comparison and level-`0` same comparison: a plane against itself, `0 ≤ η`;
* same comparison at levels `j ≥ 1`: the same-level premise (candidates are admissible,
  `cand_admissible`);
* adjacent comparison at levels `j ≥ 1`: the adjacent premise; at level `0`: the root comparison
  premise at the anchor `x_*`, `‖x_* - x_q‖ ≤ ℓ_* ≤ r₀` (root thinness at tolerance `1`).

All five inputs enter only as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section CohHelpers

variable {n : ℕ}

/-- The net separation constant is at least `1/4`. -/
theorem d1ccoh_quarter_le_sep (T : NeckType) : (1 / 4 : ℝ) ≤ T.sourceSeparation := by
  cases T <;> norm_num [NeckType.sourceSeparation]

/-- The net separation constant is at most `1`. -/
theorem d1ccoh_sep_le_one (T : NeckType) : T.sourceSeparation ≤ 1 := by
  cases T <;> norm_num [NeckType.sourceSeparation]

/-- A plane compared with itself. -/
theorem d1ccoh_planeComparison_self {m : ℕ} (x : Spatial n) (r : ℝ)
    (L : AffineSpatialPlane n m) : planeComparison x r L L = 0 := by
  simp [planeComparison]

/-- Local ADR in a buffer restricts to every smaller buffer. -/
theorem d1ccoh_localADR_mono {μ : Measure (Space n)} {k : ℕ} {A : ℝ} {a : Space n}
    {ρ ρ' : ℝ} (h : LocalADR μ k A a ρ) (hρ : ρ' ≤ ρ) : LocalADR μ k A a ρ' :=
  fun z hz s hs hsρ => h z ⟨hz.1, Metric.ball_subset_ball hρ hz.2⟩ s hs (hsρ.trans hρ)

variable {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The construction scales are positive. -/
theorem d1ccoh_stageScale_pos (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) : 0 < stageScale 𝒢 j := by
  unfold stageScale coherentScale
  have := d1c_rootScale_pos 𝒢
  positivity

/-- `r₀ = 48 ℓ_*`. -/
theorem d1ccoh_stageScale_zero (𝒢 : GoodRegion P μ k Λ b) :
    stageScale 𝒢 0 = 48 * 𝒢.rootScale := by
  unfold stageScale coherentScale
  rw [pow_zero, div_one]

/-- A point of the root cell lies within `2 ℓ_*` of the root centre `q`. -/
theorem d1ccoh_dist_root_lt (𝒢 : GoodRegion P μ k Λ b) {g : Space n} (hg : g ∈ 𝒢.rootCell) :
    dist g 𝒢.root.2 < 2 * 𝒢.rootScale :=
  P.cell_subset_ball 𝒢.root.1 𝒢.root.2 𝒢.root_isCell hg

variable (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (fits : LocalFits 𝒢)

theorem d1ccoh_index (j : ℕ) :
    (C.family 𝒢 fits).index j = if j = 0 then {rootCenter 𝒢} else C.candSet j := rfl

theorem d1ccoh_center (j : ℕ) (a : Space n) : (C.family 𝒢 fits).center j a = a := rfl

theorem d1ccoh_plane (j : ℕ) (a : Space n) :
    (C.family 𝒢 fits).plane j a =
      if j = 0 then rootPlane 𝒢 else NeckSelection.modelPlane 𝒢.type (fits.model j a) := rfl

theorem d1ccoh_parent (j : ℕ) (a : Space n) :
    (C.family 𝒢 fits).parent j a = if j ≤ 1 then rootCenter 𝒢 else C.parentOf 𝒢 (j - 1) a :=
  rfl

theorem d1ccoh_scale (j : ℕ) : (C.family 𝒢 fits).scale j = stageScale 𝒢 j := rfl

theorem d1ccoh_initialPlane : (C.family 𝒢 fits).initialPlane = rootPlane 𝒢 := rfl

theorem d1ccoh_mem_index_zero (a : Space n) :
    a ∈ (C.family 𝒢 fits).index 0 ↔ a = rootCenter 𝒢 := by
  rw [d1ccoh_index, ite_eq_left rfl, Finset.mem_singleton]

theorem d1ccoh_mem_index_pos {j : ℕ} (hj : j ≠ 0) (a : Space n) :
    a ∈ (C.family 𝒢 fits).index j ↔ ∃ i, i < C.candCount j ∧ C.cand j i = a := by
  rw [d1ccoh_index, ite_eq_right hj]
  simp [Choice.candSet]

theorem d1ccoh_plane_zero (a : Space n) : (C.family 𝒢 fits).plane 0 a = rootPlane 𝒢 := by
  rw [d1ccoh_plane, ite_eq_left rfl]

theorem d1ccoh_plane_pos {j : ℕ} (hj : j ≠ 0) (a : Space n) :
    (C.family 𝒢 fits).plane j a = NeckSelection.modelPlane 𝒢.type (fits.model j a) := by
  rw [d1ccoh_plane, ite_eq_right hj]

end CohHelpers

/-- **Coherence of the terminal family** (`d1c_coherence`): every finite truncation of the terminal family is
coherent with separation `1/4` and comparison tolerance `η`, for small `b`, from the same-level,
adjacent and root comparisons, root thinness and the stage facts (all as hypotheses). -/
theorem d1c_coherence_proof :
    SameLevelStatement → AdjacentLevelStatement → RootAdjacentStatement →
      RootThinnessStatement → StageFactsStatement → CoherenceStatement := by
  intro hSame hAdj hRadj hRT hSF n hn k hk hkn A hA
  obtain ⟨Λs, hΛs1, hS⟩ := hSame n hn k hk hkn A hA
  obtain ⟨Λa, -, hAd⟩ := hAdj n hn k hk hkn A hA
  obtain ⟨Λr, -, hRa⟩ := hRadj n hn k hk hkn A hA
  obtain ⟨Λt, -, hRt⟩ := hRT n hn k hk hkn A hA
  refine ⟨max (max Λs Λa) (max Λr Λt), le_max_of_le_left (le_max_of_le_left hΛs1),
    fun Λ hΛ => ?_⟩
  obtain ⟨Bs, hBs1, hS⟩ := hS Λ ((le_max_of_le_left (le_max_left _ _)).trans hΛ)
  obtain ⟨Ba, -, hAd⟩ := hAd Λ ((le_max_of_le_left (le_max_right _ _)).trans hΛ)
  obtain ⟨Br, -, hRa⟩ := hRa Λ ((le_max_of_le_right (le_max_left _ _)).trans hΛ)
  obtain ⟨Bt, -, hRt⟩ := hRt Λ ((le_max_of_le_right (le_max_right _ _)).trans hΛ)
  refine ⟨max (max Bs Ba) (max Br Bt), le_max_of_le_left (le_max_of_le_left hBs1),
    fun η hη => ?_⟩
  obtain ⟨bs, hbs, hS⟩ := hS η hη
  obtain ⟨ba, hba, hAd⟩ := hAd η hη
  obtain ⟨br, hbr, hRa⟩ := hRa η hη
  obtain ⟨bt, hbt, hRt⟩ := hRt 1 one_pos
  refine ⟨min (min bs ba) (min br bt), lt_min (lt_min hbs hba) (lt_min hbr hbt), ?_⟩
  intro b hb hbb μ hfin hreg a ha R hR hADR P 𝒢 hfor fits C hsel N
  have hADR' : ∀ B' : ℝ, B' ≤ max (max Bs Ba) (max Br Bt) → LocalADR μ k A a (B' * R) :=
    fun B' hB' => d1ccoh_localADR_mono hADR (mul_le_mul_of_nonneg_right hB' hR.le)
  have hSl := hS b hb (hbb.trans ((min_le_left _ _).trans (min_le_left _ _))) μ hfin hreg a ha
    R hR (hADR' Bs (le_max_of_le_left (le_max_left _ _))) P 𝒢 hfor fits
  have hAl := hAd b hb (hbb.trans ((min_le_left _ _).trans (min_le_right _ _))) μ hfin hreg a ha
    R hR (hADR' Ba (le_max_of_le_left (le_max_right _ _))) P 𝒢 hfor fits
  have hRl := hRa b hb (hbb.trans ((min_le_right _ _).trans (min_le_left _ _))) μ hfin hreg a ha
    R hR (hADR' Br (le_max_of_le_right (le_max_left _ _))) P 𝒢 hfor fits
  have hT := hRt b hb (hbb.trans ((min_le_right _ _).trans (min_le_right _ _))) μ hfin hreg a ha
    R hR (hADR' Bt (le_max_of_le_right (le_max_right _ _))) P 𝒢 hfor
  have hF := hSF n μ.support R P μ k Λ b 𝒢 C hsel
  have hℓ : 0 < 𝒢.rootScale := d1c_rootScale_pos 𝒢
  have hr0 : stageScale 𝒢 0 = 48 * 𝒢.rootScale := d1ccoh_stageScale_zero 𝒢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- separation
    intro j _ x hx y hy hxy
    rw [d1ccoh_center, d1ccoh_center, d1ccoh_scale]
    by_cases hj : j = 0
    · subst hj
      rw [d1ccoh_mem_index_zero] at hx hy
      exact absurd (hx.trans hy.symm) hxy
    · obtain ⟨i, hi, rfl⟩ := (d1ccoh_mem_index_pos C 𝒢 fits hj x).1 hx
      obtain ⟨l, hl, rfl⟩ := (d1ccoh_mem_index_pos C 𝒢 fits hj y).1 hy
      have hil : i ≠ l := fun h => hxy (by rw [h])
      have hsep := hsel.cand_separated j (Nat.one_le_iff_ne_zero.2 hj) i hi l hl hil
      exact le_trans (mul_le_mul_of_nonneg_right (d1ccoh_quarter_le_sep 𝒢.type)
        (d1ccoh_stageScale_pos 𝒢 j).le) hsep
  · -- parents are preceding indices
    intro j _ x hx
    by_cases hj : j = 0
    · subst hj
      have h01 : 0 + 1 ≤ 1 := le_rfl
      rw [d1ccoh_parent, ite_eq_left h01, d1ccoh_mem_index_zero]
    · obtain ⟨i, hi, rfl⟩ := (d1ccoh_mem_index_pos C 𝒢 fits (Nat.succ_ne_zero j) x).1 hx
      have hj1 : ¬ (j + 1 ≤ 1) := by omega
      rw [d1ccoh_parent, ite_eq_right hj1, Nat.add_sub_cancel, d1ccoh_mem_index_pos C 𝒢 fits hj]
      have hk1 := hF.kept_succ_subset j (hsel.cand_mem (j + 1) (by omega) i hi)
      obtain ⟨i', hi', heq, -⟩ := hF.parentOf_spec j (Nat.one_le_iff_ne_zero.2 hj) _ hk1
      exact ⟨i', hi', heq.symm⟩
  · -- parents are within `r_j`
    intro j _ x hx
    rw [d1ccoh_center, d1ccoh_center, d1ccoh_scale]
    by_cases hj : j = 0
    · subst hj
      have h01 : 0 + 1 ≤ 1 := le_rfl
      rw [d1ccoh_parent, ite_eq_left h01]
      obtain ⟨i, hi, rfl⟩ := (d1ccoh_mem_index_pos C 𝒢 fits (Nat.succ_ne_zero 0) x).1 hx
      have hcell := hF.kept_subset (0 + 1) (hsel.cand_mem (0 + 1) (by norm_num) i hi)
      have h1 := d1ccoh_dist_root_lt 𝒢 hcell
      have h2 : dist (rootCenter 𝒢) 𝒢.root.2 ≤ 1 * 𝒢.rootScale := hT.2.1
      have h3 := dist_triangle_right (C.cand (0 + 1) i) (rootCenter 𝒢) 𝒢.root.2
      rw [hr0]
      linarith
    · obtain ⟨i, hi, rfl⟩ := (d1ccoh_mem_index_pos C 𝒢 fits (Nat.succ_ne_zero j) x).1 hx
      have hj1 : ¬ (j + 1 ≤ 1) := by omega
      rw [d1ccoh_parent, ite_eq_right hj1, Nat.add_sub_cancel]
      have hk1 := hF.kept_succ_subset j (hsel.cand_mem (j + 1) (by omega) i hi)
      obtain ⟨-, -, -, hd⟩ := hF.parentOf_spec j (Nat.one_le_iff_ne_zero.2 hj) _ hk1
      have hsep := mul_le_mul_of_nonneg_right (d1ccoh_sep_le_one 𝒢.type)
        (d1ccoh_stageScale_pos 𝒢 j).le
      rw [one_mul] at hsep
      exact hd.le.trans hsep
  · -- root comparison: a plane against itself
    intro x _
    rw [d1ccoh_plane_zero, d1ccoh_initialPlane, d1ccoh_planeComparison_self]
    exact hη.le
  · -- same-level comparisons
    intro j _ x hx y hy hd
    rw [d1ccoh_center, d1ccoh_center, d1ccoh_scale] at hd
    rw [d1ccoh_center, d1ccoh_scale]
    by_cases hj : j = 0
    · subst hj
      rw [d1ccoh_plane_zero, d1ccoh_plane_zero, d1ccoh_planeComparison_self]
      exact hη.le
    · obtain ⟨i, hi, rfl⟩ := (d1ccoh_mem_index_pos C 𝒢 fits hj x).1 hx
      obtain ⟨l, hl, rfl⟩ := (d1ccoh_mem_index_pos C 𝒢 fits hj y).1 hy
      rw [d1ccoh_plane_pos C 𝒢 fits hj, d1ccoh_plane_pos C 𝒢 fits hj]
      have h1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hj
      exact hSl j _ _ h1 (hF.cand_admissible j h1 i hi) (hF.cand_admissible j h1 l hl) hd
  · -- adjacent comparisons
    intro j _ x hx y hy hd
    rw [d1ccoh_center, d1ccoh_center, d1ccoh_scale] at hd
    rw [d1ccoh_center, d1ccoh_scale]
    obtain ⟨i, hi, rfl⟩ := (d1ccoh_mem_index_pos C 𝒢 fits (Nat.succ_ne_zero j) x).1 hx
    rw [d1ccoh_plane_pos C 𝒢 fits (Nat.succ_ne_zero j)]
    by_cases hj : j = 0
    · subst hj
      rw [d1ccoh_mem_index_zero] at hy
      subst hy
      rw [d1ccoh_plane_zero]
      have hx0 : ‖(rootCenter 𝒢).1 - 𝒢.root.2.1‖ ≤ 48 * 𝒢.rootScale := by
        have := hT.2.2
        linarith
      exact hRl _ (hF.cand_admissible (0 + 1) (by norm_num) i hi) _ hx0
    · obtain ⟨l, hl, rfl⟩ := (d1ccoh_mem_index_pos C 𝒢 fits hj y).1 hy
      rw [d1ccoh_plane_pos C 𝒢 fits hj]
      have h1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hj
      exact hAl j _ _ h1 (hF.cand_admissible (j + 1) (by omega) i hi)
        (hF.cand_admissible j h1 l hl) hd

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
