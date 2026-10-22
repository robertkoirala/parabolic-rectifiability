import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.LastWitness
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.Measure.Neck.PlaneTime.ConstructionFacts

/-! # The finite comparison square sum of a terminal construction

Proof of `d1d_squareUpTo_proof`, in implication form: the statements `WitnessSelectionStatement`,
`IncidenceStatement`, `LevelEstimateStatement`, `ChargingStatement` and
`Terminal.OwnerStatement` are hypotheses.

Route. For a position map `pos` dominating spatial
distances and turning `pos`-incidence of occurrences into parabolic incidence
(`d1dsquare_sum_le`), fix `w` and `N`. The witness statement gives `E_0(w) = 0` and either the
zero case (the sum vanishes) or a cutoff `j₀ + 1 ≤ N` with `E_j(w) = 0` for `j₀ + 1 < j ≤ N` and
an incident genuine occurrence `g_* = z_{i,a}`, `1 ≤ i`, `j₀ ≤ i ≤ j₀ + 1` (only this weaker
exported contract is used). `g_* ∈ S` and `ρ(g_*) < 1000 r_i` (`genuine_mem`, `genuine_scale`,
`initialRadius_eq`), so the owner statement gives a member `O` with
`d_P(g_*, z_O) ≤ 2000 r_i + 2 ℓ_O` and `i + root.1 ≤ O.1 + 8`. The sum is truncated to
`range (j₀ + 2)`; the charging statement with `J = j₀ + 1`, `e = E_·(w)²`, `c = ofReal (4 C₁)`
(`e 0 = 0`; `J + root.1 ≤ O.1 + 11` from the owner's depth; the per-level bounds from the level
estimate) bounds it by `11 · ofReal (4 C₁) · ofReal b = ofReal (44 C₁ b)` (`ofReal_mul` with the
nonnegative factor `44 C₁`, for every real `b`).

The type split (`d1dsquare_typeSquareBoundUpTo`) is generic in the type `T` and the rank `m`:
horizontally `pos = Prod.fst` (spatial domination `dist_eq_norm`, incidence from
`IncidenceStatement` with `TN.timeCompatible` and `γ ≤ 1`), vertically `pos = id` (spatial
domination `ms3_norm_sub_le_dist`, incidence trivial). Every helper carries the prefix
`d1dsquare_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Witness

/-- **The type split**, generic in the type `T` and the rank `m`: the type's truncated square
bound follows from the horizontal bound when `T = .horizontal` and from the vertical bound when
`T = .vertical`. -/
theorem d1dsquare_typeSquareBoundUpTo {n m : ℕ} {ι : Type*} (T : NeckType)
    (F : CoherentFamily n m ι) (E : ℝ) (N : ℕ)
    (hH : T = .horizontal → F.HorizontalSquareBoundUpTo E N)
    (hV : T = .vertical → F.VerticalSquareBoundUpTo E N) :
    TypeSquareBoundUpTo T F E N := by
  cases T
  · exact hH rfl
  · exact hV rfl

/-- The constant bookkeeping `11 · ofReal (4 C₁) · ofReal b = ofReal (44 C₁ b)` for `C₁ ≥ 0` and
every real `b` (both sides vanish for `b ≤ 0`). -/
theorem d1dsquare_const_eq {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (b : ℝ) :
    11 * ENNReal.ofReal (4 * C₁) * ENNReal.ofReal b = ENNReal.ofReal (44 * C₁ * b) := by
  rw [show (44 : ℝ) * C₁ * b = 11 * (4 * C₁) * b by ring,
    ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 11 * (4 * C₁)),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 11), ENNReal.ofReal_ofNat]

/-- The prescribed scales of the terminal family: `r_j = coherentScale (48 ℓ_*) j`. -/
theorem d1dsquare_scale_eq {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} {𝒢 : GoodRegion P μ k Λ b} {δ κ θ γ : ℝ}
    (TN : TerminalNeck 𝒢 δ κ θ γ) (j : ℕ) :
    TN.family.scale j = coherentScale (48 * 𝒢.rootScale) j := by
  show coherentScale TN.family.initialRadius j = _
  rw [TN.initialRadius_eq]

/-- **The finite square sum for one position map**: for a position map `pos`
dominating spatial distances and turning `pos`-incidence of occurrences into parabolic
incidence, every truncated sum `∑_{j ≤ N} E_j(w)²` is at most `ofReal (44 C₁ b)`. -/
theorem d1dsquare_sum_le (hW : WitnessSelectionStatement) (hL : LevelEstimateStatement)
    (hC : ChargingStatement) (hO : Terminal.OwnerStatement)
    {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
    {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b) {δ κ θ γ : ℝ} (TN : TerminalNeck 𝒢 δ κ θ γ)
    {C₁ : ℝ} (hΛ : 4000 ≤ Λ) (hC₁ : 0 ≤ C₁) (hOcc : OccurrenceBound 𝒢 C₁)
    {W : Type} [PseudoMetricSpace W] (pos : Space n → W)
    (hdom : ∀ z z' : Space n, ‖z.1 - z'.1‖ ≤ dist (pos z) (pos z'))
    (hinc : ∀ (i i' : ℕ) (a a' : Space n), a ∈ TN.family.index i → a' ∈ TN.family.index i' →
      ∀ ρ : ℝ, TN.family.scale i ≤ ρ → TN.family.scale i' ≤ ρ →
        dist (pos (TN.family.center i a)) (pos (TN.family.center i' a')) ≤ ρ →
          dist (TN.family.center i a) (TN.family.center i' a') ≤ ρ)
    (w : W) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), TN.family.comparisonEnergy pos j w ^ 2 ≤
      ENNReal.ofReal (44 * C₁ * b) := by
  obtain ⟨h0, hcase⟩ :=
    hW n (𝒢.type.rank k) (Space n) W pos TN.family w N TN.level_zero_plane
  rcases hcase with hzero | ⟨j₀, hj₀N, hvan, i, a, hi1, hj₀i, -, ha, hwit⟩
  · -- the zero case: every comparison through level `N` vanishes
    have hsum : ∑ j ∈ Finset.range (N + 1), TN.family.comparisonEnergy pos j w ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjN : j < N + 1 := Finset.mem_range.mp hj
      rw [hzero j (by omega)]
      exact zero_pow two_ne_zero
    rw [hsum]
    exact zero_le
  · -- the witness `g_* = z_{i,a}` is genuine: `i = i' + 1`
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hgmem : TN.family.center (i' + 1) a ∈ 𝒢.rootCell := TN.genuine_mem i' a ha
    have hgscale : 𝒢.stopScale (TN.family.center (i' + 1) a) <
        1000 * coherentScale (48 * 𝒢.rootScale) (i' + 1) := by
      rw [← d1dsquare_scale_eq TN (i' + 1)]
      exact TN.genuine_scale i' a ha
    -- one owner cell `O` of the witness (from the owner statement)
    obtain ⟨O, hOmem, -, -, -, hOdist, hOdepth, -⟩ :=
      hO n E ℓ₀ P μ k Λ b 𝒢 (i' + 1) (TN.family.center (i' + 1) a) hgmem hgscale
    -- the per-level estimate along the ancestor chain of `O`
    have hlev := hL n E ℓ₀ P μ k Λ b 𝒢 δ κ θ γ TN C₁ W pos hΛ hC₁ hOcc hdom hinc w j₀
      (i' + 1) a hi1 hj₀i ha hwit O hOmem hOdist hOdepth
    -- the chain budget of `O` pays the truncated sum
    have hcharge := hC n E ℓ₀ P μ k Λ b 𝒢 O (j₀ + 1)
      (fun j => TN.family.comparisonEnergy pos j w ^ 2) (ENNReal.ofReal (4 * C₁)) hOmem
      (by omega)
      (by
        show TN.family.comparisonEnergy pos 0 w ^ 2 = 0
        rw [h0]
        exact zero_pow two_ne_zero)
      (fun j hj A hA hAlev hOA => hlev j (by omega) A hA hAlev hOA)
    -- truncation to `range (j₀ + 2)`: the comparisons above the cutoff vanish
    have hsub : Finset.range (j₀ + 1 + 1) ⊆ Finset.range (N + 1) :=
      Finset.range_subset_range.mpr (by omega)
    have htrunc : ∑ j ∈ Finset.range (j₀ + 1 + 1), TN.family.comparisonEnergy pos j w ^ 2 =
        ∑ j ∈ Finset.range (N + 1), TN.family.comparisonEnergy pos j w ^ 2 := by
      apply Finset.sum_subset hsub
      intro x hxN hxj
      rw [Finset.mem_range] at hxN hxj
      rw [hvan x (by omega) (by omega)]
      exact zero_pow two_ne_zero
    rw [← htrunc]
    exact hcharge.trans (d1dsquare_const_eq hC₁ b).le

/-- **Horizontal incidence**: under `𝒢.type = .horizontal` and `γ ≤ 1`, spatial
incidence of occurrences of the terminal family is parabolic incidence (`IncidenceStatement`
with the recorded-time compatibility `TN.timeCompatible`). -/
theorem d1dsquare_incidence_horizontal (hI : IncidenceStatement) {n : ℕ} {E : Set (Space n)}
    {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ}
    {𝒢 : GoodRegion P μ k Λ b} {δ κ θ γ : ℝ} (TN : TerminalNeck 𝒢 δ κ θ γ) (hγ : γ ≤ 1)
    (hT : 𝒢.type = .horizontal) :
    ∀ (i i' : ℕ) (a a' : Space n), a ∈ TN.family.index i → a' ∈ TN.family.index i' →
      ∀ ρ : ℝ, TN.family.scale i ≤ ρ → TN.family.scale i' ≤ ρ →
        dist (TN.family.center i a).1 (TN.family.center i' a').1 ≤ ρ →
          dist (TN.family.center i a) (TN.family.center i' a') ≤ ρ := by
  intro i i' a a' ha ha' ρ hi hi' hd
  rw [dist_eq_norm] at hd
  exact hI n (𝒢.type.rank k) (Space n) TN.family TN.centers TN.radius γ hγ
    (TN.timeCompatible hT) i i' a a' ha ha' ρ hi hi' hd

/-- **The finite comparison square sum**, in implication form: for a terminal construction with `γ ≤ 1`, `Λ ≥ 4000` and the
per-occurrence bound with `C₁ ≥ 0`, every truncation satisfies the square bound of the region's
type with `E = 44 C₁ b`, uniformly in the truncation and the witness. -/
theorem d1d_squareUpTo_proof :
    WitnessSelectionStatement → IncidenceStatement → LevelEstimateStatement →
      ChargingStatement → Terminal.OwnerStatement → SquareUpToStatement := by
  intro hW hI hL hC hO n E ℓ₀ P μ k Λ b 𝒢 δ κ θ γ TN C₁ hΛ hγ hC₁ hOcc N
  apply d1dsquare_typeSquareBoundUpTo
  · intro hT w
    exact d1dsquare_sum_le hW hL hC hO 𝒢 TN hΛ hC₁ hOcc (fun z : Space n => z.1)
      (fun z z' => (dist_eq_norm z.1 z'.1).ge) (d1dsquare_incidence_horizontal hI TN hγ hT) w N
  · intro _ w
    exact d1dsquare_sum_le hW hL hC hO 𝒢 TN hΛ hC₁ hOcc (fun z : Space n => z)
      (fun z z' => ms3_norm_sub_le_dist z z') (fun _ _ _ _ _ _ _ _ _ h => h) w N

end Witness

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
