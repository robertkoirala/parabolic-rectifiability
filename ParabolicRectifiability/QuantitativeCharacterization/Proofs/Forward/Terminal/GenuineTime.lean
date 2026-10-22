import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.Measure.Neck.PlaneTime.TimeCompatibility

/-! # Recorded-time compatibility of genuine records

Proof of `d1c_genuineTime_proof`, in implication form:
`LocalFitsStatement → FittedTimeStatement → ThinnessStatement → RootThinnessStatement →
StageFactsStatement → GenuineTimeStatement`.

Route. Fix a horizontal good region, a selection `C` and local fits (from
`LocalFitsStatement`). For two points with survival histories `(z, s)`, `(w, s')` put
`β = max(d_P(z, w), s, s') > 0`, and let `δ` be the tolerance at which the hypotheses are
applied.
* If some positive level has `r_l ≥ 10 β`, take the deepest one: `10 β ≤ r_l < 100 β` and
  `s, s' ≤ β ≤ r_{l+1}`, so both points lie in `S_l` (histories); their stored parents `g, g'`
  are admissible level-`l` candidates with `d_P(z, g), d_P(w, g') < κ_net r_l ≤ r_l`, hence
  `d_P(g, g') ≤ 20 r_l`. The two tube tests (thinness, time clause) and the fitted-time comparison
  give `|t_z - t_w| ≤ (2 δ² + δ) r_l² ≤ 10⁴ (2 δ² + δ) β²`.
* Otherwise `r_1 < 10 β`, so `ℓ_* < 3 β`, and the initial tube (root thinness) gives
  `|t_z - t_w| ≤ 2 (δ ℓ_*)² ≤ 18 δ² β²`.
Both cases are `d1cgtime_pair`. With `δ = min(η, 1/2)/30000` the factor `γ₀ = 10⁴ (2 δ² + δ)` is at
most `min(η, 1/2)` (`d1cgtime_exists_delta`); since
`β² ≤ max(max(|x_z - x_w|², s², s'²), |t_z - t_w|)` (base `ms3_sq_max_le`, `ms3_dist_sq_eq`), the
base absorption `ms3_absorb` gives `|t_z - t_w| ≤ η max(|x_z - x_w|², s², s'²)`.

Only the uniform errors (through the hypotheses) and the tube history enter, not a square
sum. Every helper has the prefix `d1cgtime_`.
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

/-- Local ADR on a ball passes to every smaller concentric ball. -/
theorem d1cgtime_localADR_mono {A : ℝ} {a : Space n} {ρ ρ' : ℝ} (hρ : ρ' ≤ ρ)
    (h : LocalADR μ k A a ρ) : LocalADR μ k A a ρ' := by
  intro y hy s hs hsρ
  exact h y ⟨hy.1, Metric.ball_subset_ball hρ hy.2⟩ s hs (hsρ.trans hρ)

/-- The root cell lies in the partitioned set (`cell_cover`, `root_isCell`). -/
theorem d1cgtime_rootCell_subset (𝒢 : GoodRegion P μ k Λ b) : 𝒢.rootCell ⊆ E := by
  intro y hy
  rw [← P.cell_cover 𝒢.root.1]
  exact Set.mem_iUnion₂.2 ⟨𝒢.root.2, 𝒢.root_isCell, hy⟩

/-- The net separation constant is at most `1` (`1/4` horizontal, `1` vertical). -/
theorem d1cgtime_sourceSeparation_le_one (T : NeckType) : T.sourceSeparation ≤ 1 := by
  cases T <;> norm_num [NeckType.sourceSeparation]

/-- `r_j = 48 ℓ_* / 10^j`. -/
theorem d1cgtime_stageScale_eq (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    stageScale 𝒢 j = 48 * 𝒢.rootScale / 10 ^ j := rfl

theorem d1cgtime_stageScale_pos (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) : 0 < stageScale 𝒢 j := by
  rw [d1cgtime_stageScale_eq]
  have h := d1c_rootScale_pos 𝒢
  exact div_pos (by linarith) (pow_pos (by norm_num : (0 : ℝ) < 10) j)

/-- `r_{j+1} = r_j / 10`. -/
theorem d1cgtime_stageScale_succ (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    stageScale 𝒢 (j + 1) = stageScale 𝒢 j / 10 := by
  rw [d1cgtime_stageScale_eq, d1cgtime_stageScale_eq, pow_succ, div_div]

/-- Some stage scale `r_{m+1}` lies below any positive bound. -/
theorem d1cgtime_exists_scale_lt (𝒢 : GoodRegion P μ k Λ b) {c : ℝ} (hc : 0 < c) :
    ∃ m : ℕ, stageScale 𝒢 (m + 1) < c := by
  obtain ⟨N, hN⟩ :=
    pow_unbounded_of_one_lt (48 * 𝒢.rootScale / c) (by norm_num : (1 : ℝ) < 10)
  have hN' : stageScale 𝒢 N < c := by
    rw [d1cgtime_stageScale_eq, div_lt_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 10) N)]
    rw [div_lt_iff₀ hc] at hN
    calc 48 * 𝒢.rootScale < 10 ^ N * c := hN
      _ = c * 10 ^ N := mul_comm _ _
  have hpos := d1cgtime_stageScale_pos 𝒢 N
  refine ⟨N, ?_⟩
  rw [d1cgtime_stageScale_succ]
  linarith

/-- **The two-record estimate.** Given, at a tolerance `δ ≥ 0`, the time
clause of the tube tests at every admissible `(j, g)`, `j ≥ 1`, the fitted-time comparison and the
initial tube, two points with survival histories `(z, s)`, `(w, s')` satisfy
`|t_z - t_w| ≤ 10⁴ (2 δ² + δ) β²`, `β = max(d_P(z, w), s, s')`: at the deepest positive level `l`
with `r_l ≥ 10 β` through the two stored parents, and otherwise through the initial tube. -/
theorem d1cgtime_pair (𝒢 : GoodRegion P μ k Λ b) (C : Choice n) (fits : LocalFits 𝒢)
    (hst : C.StageFacts 𝒢) {δ : ℝ} (hδ : 0 ≤ δ)
    (hthin : ∀ (j : ℕ) (g : Space n), 1 ≤ j → Admissible 𝒢 j g →
      ∀ y ∈ 𝒢.rootCell, dist y g < 2 * stageScale 𝒢 j →
        |y.2.val - NeckSelection.modelTime 𝒢.type (fits.model j g)| ≤
          (δ * stageScale 𝒢 j) ^ 2)
    (hftime : ∀ (l : ℕ) (g g' : Space n), 1 ≤ l → Admissible 𝒢 l g → Admissible 𝒢 l g' →
      dist g g' ≤ 20 * stageScale 𝒢 l →
        |NeckSelection.modelTime 𝒢.type (fits.model l g) -
            NeckSelection.modelTime 𝒢.type (fits.model l g')| ≤ δ * stageScale 𝒢 l ^ 2)
    (hroot : ∀ y ∈ 𝒢.rootCell,
      |y.2.val - NeckSelection.modelTime 𝒢.type (𝒢.model 𝒢.root)| ≤ (δ * 𝒢.rootScale) ^ 2)
    {z w : Space n} {s s' : ℝ} (hz : C.HasHistory 𝒢 z s) (hw : C.HasHistory 𝒢 w s') :
    |z.2.val - w.2.val| ≤ 10000 * (2 * δ ^ 2 + δ) * max (dist z w) (max s s') ^ 2 := by
  classical
  obtain ⟨hs, hzS, hzk⟩ := hz
  obtain ⟨-, hwS, hwk⟩ := hw
  set β := max (dist z w) (max s s') with hβ
  have hsβ : s ≤ β := (le_max_left s s').trans (le_max_right _ _)
  have hs'β : s' ≤ β := (le_max_right s s').trans (le_max_right _ _)
  have hdβ : dist z w ≤ β := le_max_left _ _
  have hβpos : 0 < β := hs.trans_le hsβ
  have hδ2 : 0 ≤ δ ^ 2 * β ^ 2 := mul_nonneg (sq_nonneg δ) (sq_nonneg β)
  have hδ1 : 0 ≤ δ * β ^ 2 := mul_nonneg hδ (sq_nonneg β)
  have hex : ∃ m : ℕ, stageScale 𝒢 (m + 1) < 10 * β :=
    d1cgtime_exists_scale_lt 𝒢 (by linarith)
  have hspec : stageScale 𝒢 (Nat.find hex + 1) < 10 * β := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · -- no positive level with `r_l ≥ 10 β`: the initial tube
    rw [h0, d1cgtime_stageScale_eq, show ((10 : ℝ) ^ (0 + 1)) = 10 by norm_num] at hspec
    have hℓ := d1c_rootScale_pos 𝒢
    have hℓβ : 𝒢.rootScale ≤ 3 * β := by linarith
    have hℓ2 : 𝒢.rootScale ^ 2 ≤ 9 * β ^ 2 := by
      calc 𝒢.rootScale ^ 2 ≤ (3 * β) ^ 2 := pow_le_pow_left₀ hℓ.le hℓβ 2
        _ = 9 * β ^ 2 := by ring
    have h1 : (δ * 𝒢.rootScale) ^ 2 ≤ 9 * (δ ^ 2 * β ^ 2) := by
      calc (δ * 𝒢.rootScale) ^ 2 = δ ^ 2 * 𝒢.rootScale ^ 2 := by ring
        _ ≤ δ ^ 2 * (9 * β ^ 2) := mul_le_mul_of_nonneg_left hℓ2 (sq_nonneg δ)
        _ = 9 * (δ ^ 2 * β ^ 2) := by ring
    set τ := NeckSelection.modelTime 𝒢.type (𝒢.model 𝒢.root) with hτ
    have htz := hroot z hzS
    have htw := hroot w hwS
    have htri := abs_sub_le z.2.val τ w.2.val
    rw [abs_sub_comm τ w.2.val] at htri
    calc |z.2.val - w.2.val| ≤ |z.2.val - τ| + |w.2.val - τ| := htri
      _ ≤ (δ * 𝒢.rootScale) ^ 2 + (δ * 𝒢.rootScale) ^ 2 := add_le_add htz htw
      _ ≤ 9 * (δ ^ 2 * β ^ 2) + 9 * (δ ^ 2 * β ^ 2) := add_le_add h1 h1
      _ ≤ 20000 * (δ ^ 2 * β ^ 2) + 10000 * (δ * β ^ 2) := by linarith
      _ = 10000 * (2 * δ ^ 2 + δ) * β ^ 2 := by ring
  · -- the deepest positive level `l` with `r_l ≥ 10 β`
    set l := Nat.find hex with hl
    have hl1 : 1 ≤ l := hpos
    have hmin : 10 * β ≤ stageScale 𝒢 l := by
      have h1 := Nat.find_min hex (show l - 1 < l by omega)
      rw [not_lt, show l - 1 + 1 = l by omega] at h1
      exact h1
    rw [d1cgtime_stageScale_succ] at hspec
    have hr := d1cgtime_stageScale_pos 𝒢 l
    have hrl : stageScale 𝒢 l < 100 * β := by linarith
    have hβr : β ≤ stageScale 𝒢 (l + 1) := by
      rw [d1cgtime_stageScale_succ]
      linarith
    -- both points survive to `S_l` and have stored parents there
    have hzl : z ∈ C.kept 𝒢 l := hzk l hl1 (hsβ.trans hβr)
    have hwl : w ∈ C.kept 𝒢 l := hwk l hl1 (hs'β.trans hβr)
    obtain ⟨i, hi, hgi, hdz⟩ := hst.parentOf_spec l hl1 z hzl
    obtain ⟨i', hi', hgi', hdw⟩ := hst.parentOf_spec l hl1 w hwl
    set g := C.parentOf 𝒢 l z with hg
    set g' := C.parentOf 𝒢 l w with hg'
    have hga : Admissible 𝒢 l g := by
      rw [hgi]
      exact hst.cand_admissible l hl1 i hi
    have hga' : Admissible 𝒢 l g' := by
      rw [hgi']
      exact hst.cand_admissible l hl1 i' hi'
    have hκ : 𝒢.type.sourceSeparation * stageScale 𝒢 l ≤ stageScale 𝒢 l :=
      mul_le_of_le_one_left hr.le (d1cgtime_sourceSeparation_le_one 𝒢.type)
    have hdz' : dist z g < stageScale 𝒢 l := hdz.trans_le hκ
    have hdw' : dist w g' < stageScale 𝒢 l := hdw.trans_le hκ
    have hgg : dist g g' ≤ 20 * stageScale 𝒢 l := by
      have h1 := dist_triangle4 g z w g'
      rw [dist_comm g z] at h1
      linarith
    -- the two tube tests and the fitted-time comparison
    have htz := hthin l g hl1 hga z hzS (by linarith)
    have htw := hthin l g' hl1 hga' w hwS (by linarith)
    have hτ := hftime l g g' hl1 hga hga' hgg
    set τ := NeckSelection.modelTime 𝒢.type (fits.model l g) with hτdef
    set τ' := NeckSelection.modelTime 𝒢.type (fits.model l g') with hτ'def
    have hr2 : stageScale 𝒢 l ^ 2 ≤ 10000 * β ^ 2 := by
      calc stageScale 𝒢 l ^ 2 ≤ (100 * β) ^ 2 := pow_le_pow_left₀ hr.le hrl.le 2
        _ = 10000 * β ^ 2 := by ring
    have h3 : |z.2.val - w.2.val| ≤ |z.2.val - τ| + |τ - τ'| + |w.2.val - τ'| := by
      have h4 := abs_sub_le z.2.val τ w.2.val
      have h5 := abs_sub_le τ τ' w.2.val
      rw [abs_sub_comm τ' w.2.val] at h5
      linarith
    have hc : 0 ≤ 2 * δ ^ 2 + δ := add_nonneg (by positivity) hδ
    calc |z.2.val - w.2.val| ≤ |z.2.val - τ| + |τ - τ'| + |w.2.val - τ'| := h3
      _ ≤ (δ * stageScale 𝒢 l) ^ 2 + δ * stageScale 𝒢 l ^ 2 + (δ * stageScale 𝒢 l) ^ 2 := by
          linarith
      _ = (2 * δ ^ 2 + δ) * stageScale 𝒢 l ^ 2 := by ring
      _ ≤ (2 * δ ^ 2 + δ) * (10000 * β ^ 2) := mul_le_mul_of_nonneg_left hr2 hc
      _ = 10000 * (2 * δ ^ 2 + δ) * β ^ 2 := by ring

end Helpers

/-- **The choice of the tolerance**: some `δ > 0` has
`γ₀ = 10⁴ (2 δ² + δ) ≤ min(η, 1/2)`, namely `δ = min(η, 1/2)/30000`. -/
theorem d1cgtime_exists_delta {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ 10000 * (2 * δ ^ 2 + δ) ≤ 1 / 2 ∧ 10000 * (2 * δ ^ 2 + δ) ≤ η := by
  have hm0 : 0 < min η (1 / 2) := lt_min hη (by norm_num)
  have hm1 : min η (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hmη : min η (1 / 2) ≤ η := min_le_left _ _
  have hδ0 : 0 < min η (1 / 2) / 30000 := div_pos hm0 (by norm_num)
  have hδ1 : min η (1 / 2) / 30000 ≤ 1 := by linarith
  have hδ2 : (min η (1 / 2) / 30000) ^ 2 ≤ min η (1 / 2) / 30000 := by
    calc (min η (1 / 2) / 30000) ^ 2 = (min η (1 / 2) / 30000) * (min η (1 / 2) / 30000) :=
          sq _
      _ ≤ (min η (1 / 2) / 30000) * 1 := mul_le_mul_of_nonneg_left hδ1 hδ0.le
      _ = min η (1 / 2) / 30000 := mul_one _
  have hγ : 10000 * (2 * (min η (1 / 2) / 30000) ^ 2 + min η (1 / 2) / 30000) ≤
      min η (1 / 2) := by
    linarith
  exact ⟨min η (1 / 2) / 30000, hδ0, hγ.trans hm1, hγ.trans hmη⟩

/-- **Recorded-time compatibility of genuine records** (`GenuineTimeStatement`, in
implication form over the preceding statements).

Constants: `Λ₀` and `B` are the maxima of those of `FittedTimeStatement`, `ThinnessStatement` and
`RootThinnessStatement`; for `η > 0` the three statements are applied at the tolerance
`δ = min(η, 1/2)/30000`, and `b₀` is the minimum of their thresholds. -/
theorem d1c_genuineTime_proof :
    LocalFitsStatement → FittedTimeStatement → ThinnessStatement → RootThinnessStatement →
      StageFactsStatement → GenuineTimeStatement := by
  intro hLF hFT hTh hRT hSF n hn k hk1 hk2 A hA
  obtain ⟨Λ₁, hΛ₁, hFT₁⟩ := hFT n hn k hk1 hk2 A hA
  obtain ⟨Λ₂, -, hTh₁⟩ := hTh n hn k hk1 hk2 A hA
  obtain ⟨Λ₃, -, hRT₁⟩ := hRT n hn k hk1 hk2 A hA
  refine ⟨max Λ₁ (max Λ₂ Λ₃), hΛ₁.trans (le_max_left _ _), fun Λ hΛ => ?_⟩
  obtain ⟨B₁, hB₁, hFT₂⟩ := hFT₁ Λ ((le_max_left _ _).trans hΛ)
  obtain ⟨B₂, -, hTh₂⟩ := hTh₁ Λ (((le_max_left _ _).trans (le_max_right _ _)).trans hΛ)
  obtain ⟨B₃, -, hRT₂⟩ := hRT₁ Λ (((le_max_right _ _).trans (le_max_right _ _)).trans hΛ)
  refine ⟨max B₁ (max B₂ B₃), hB₁.trans (le_max_left _ _), fun η hη => ?_⟩
  obtain ⟨δ, hδ, hγ₀1, hγ₀η⟩ := d1cgtime_exists_delta hη
  obtain ⟨b₁, hb₁, hFT₃⟩ := hFT₂ δ hδ
  obtain ⟨b₂, hb₂, hTh₃⟩ := hTh₂ δ hδ
  obtain ⟨b₃, hb₃, hRT₃⟩ := hRT₂ δ hδ
  refine ⟨min b₁ (min b₂ b₃), lt_min hb₁ (lt_min hb₂ hb₃), ?_⟩
  intro b hb hbb μ hμc hμi a ha R hR hADR P 𝒢 hfor C hsel htype z w s s' hz hw
  have hbb₁ : b ≤ b₁ := hbb.trans (min_le_left _ _)
  have hbb₂ : b ≤ b₂ := hbb.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbb₃ : b ≤ b₃ := hbb.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hADR₁ : LocalADR μ k A a (B₁ * R) :=
    d1cgtime_localADR_mono (mul_le_mul_of_nonneg_right (le_max_left _ _) hR.le) hADR
  have hADR₂ : LocalADR μ k A a (B₂ * R) :=
    d1cgtime_localADR_mono (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) hR.le) hADR
  have hADR₃ : LocalADR μ k A a (B₃ * R) :=
    d1cgtime_localADR_mono (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) hR.le) hADR
  obtain ⟨fits⟩ := hLF n μ.support R P μ k Λ b 𝒢 hμc
  have hst : C.StageFacts 𝒢 := hSF n μ.support R P μ k Λ b 𝒢 C hsel
  have hsupp : 𝒢.rootCell ⊆ μ.support := d1cgtime_rootCell_subset 𝒢
  have hpair := d1cgtime_pair 𝒢 C fits hst hδ.le
    (fun j g hj hg y hy hyg =>
      (hTh₃ b hb hbb₂ μ hμc hμi a ha R hR hADR₂ P 𝒢 hfor fits j g hj hg y
        ⟨hsupp hy, Metric.mem_ball.2 hyg⟩).2.2 htype)
    (fun l g g' hl hg hg' hd =>
      hFT₃ b hb hbb₁ μ hμc hμi a ha R hR hADR₁ P 𝒢 hfor fits l g g' hl hg hg' hd htype)
    (fun y hy => ((hRT₃ b hb hbb₃ μ hμc hμi a ha R hR hADR₃ P 𝒢 hfor).1 y
      (subset_closure hy)).2.2 htype)
    hz hw
  have hX : 0 ≤ max (‖z.1 - w.1‖ ^ 2) (max (s ^ 2) (s' ^ 2)) :=
    (sq_nonneg _).trans (le_max_left _ _)
  have hb2 : max (dist z w) (max s s') ^ 2 ≤
      max (max (‖z.1 - w.1‖ ^ 2) (max (s ^ 2) (s' ^ 2))) |z.2.val - w.2.val| := by
    refine ms3_sq_max_le ?_ ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
    rw [ms3_dist_sq_eq]
    exact max_le_max (le_max_left _ _) le_rfl
  have hγ₀ : 0 ≤ 10000 * (2 * δ ^ 2 + δ) :=
    mul_nonneg (by norm_num) (add_nonneg (by positivity) hδ.le)
  exact ms3_absorb (abs_nonneg _) hX hγ₀ hγ₀1 hγ₀η
    (hpair.trans (mul_le_mul_of_nonneg_left hb2 hγ₀))

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
