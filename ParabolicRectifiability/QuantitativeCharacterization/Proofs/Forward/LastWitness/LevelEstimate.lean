import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.LastWitness
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # The level estimate at one comparison index

Proof of `d1d_levelEstimate_proof`, in implication form: the statements `AncestorInclusionStatement`,
`PairBoundStatement` and `Terminal.AncestorStatement` are hypotheses.

Route: the scales of the terminal family are
`r_j = coherentScale (48 ℓ_*) j`; the coefficient `a_Q` of the charged ancestor is finite by `Q`'s
own budget term; the pair bound is applied with the ancestor plane `L_{Π_Q}` and
`D = C₁ (a_Q).toReal`. A level-zero occurrence (only when `j = 0`) carries `L_* = L_{Π_root}` and
`Q = root`, so its comparison is `0`. A genuine occurrence `(m + 1, a')` is within `24 r_j` of the
witness (position triangle through `w`, then the incidence hypothesis), so the ancestor inclusion
puts its fitting ball in `Q`'s coefficient ball with `ℓ_Q ≤ 10^{12} r_{j+1}`, and the
per-occurrence bound applies at `(m + 1, z, M, Q, y, r_j)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Witness

/-- The prescribed scales are positive. -/
theorem d1dlevel_coherentScale_pos {r₀ : ℝ} (h : 0 < r₀) (m : ℕ) : 0 < coherentScale r₀ m := by
  unfold coherentScale
  positivity

/-- The prescribed scales decrease with the level. -/
theorem d1dlevel_coherentScale_anti {r₀ : ℝ} (h : 0 ≤ r₀) {m m' : ℕ} (hm : m ≤ m') :
    coherentScale r₀ m' ≤ coherentScale r₀ m := by
  unfold coherentScale
  exact div_le_div_of_nonneg_left h (pow_pos (by norm_num) _)
    (pow_le_pow_right₀ (by norm_num) hm)

/-- One level down divides the scale by ten. -/
theorem d1dlevel_coherentScale_succ (r₀ : ℝ) (m : ℕ) :
    coherentScale r₀ m = 10 * coherentScale r₀ (m + 1) := by
  unfold coherentScale
  rw [pow_succ, mul_div_assoc', mul_comm (10 : ℝ) r₀,
    mul_div_mul_right r₀ _ (by norm_num : (10 : ℝ) ≠ 0)]

/-- `ofReal c * x = ofReal (c x.toReal)` for `c ≥ 0` and finite `x`. -/
theorem d1dlevel_ofReal_mul_eq {c : ℝ} (hc : 0 ≤ c) {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    ENNReal.ofReal c * x = ENNReal.ofReal (c * x.toReal) := by
  rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hx]

/-- The coefficient of a member is finite: it is one term of its own chain budget. -/
theorem d1dlevel_modelCoeff_ne_top {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}
    {P : DirectPartition E ℓ₀} {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ}
    (𝒢 : GoodRegion P μ k Λ b) {Q : ℕ × Space n} (hQ : Q ∈ 𝒢.members) :
    P.modelCoeff μ Λ (𝒢.model Q) Q ≠ ⊤ := by
  have hbelow : P.IsBelow Q Q := ⟨(𝒢.below_root Q hQ).1, le_rfl, subset_rfl⟩
  have h1 : P.modelCoeff μ Λ (𝒢.model Q) Q ≤ ENNReal.ofReal b :=
    le_trans
      (ENNReal.le_tsum
        (f := fun Q' : {Q' : ℕ × Space n // Q' ∈ 𝒢.members ∧ P.IsBelow Q Q'} =>
          P.modelCoeff μ Λ (𝒢.model Q'.1) Q'.1) ⟨Q, hQ, hbelow⟩)
      (𝒢.budget Q hQ)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1

/-- **Level-zero occurrences** (only at `j = 0`): the charged ancestor is at the root level, hence
is the root (`AncestorStatement`, first clause), and the level-zero plane is `L_* = L_{Π_root}`
(`level_zero_plane`, `initialPlane_fit`), so the comparison vanishes. -/
theorem d1dlevel_levelZero (hAnc : Terminal.AncestorStatement) {n : ℕ} {E : Set (Space n)}
    {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ}
    (𝒢 : GoodRegion P μ k Λ b) {δ κ θ γ : ℝ} (TN : TerminalNeck 𝒢 δ κ θ γ)
    {Q : ℕ × Space n} (hQ : Q ∈ 𝒢.members) (hQlev : Q.1 = 𝒢.root.1 + (0 + 1 - 11))
    (a' : Space n) (ha' : a' ∈ TN.family.index 0) (y : Spatial n) (s : ℝ) (D : ℝ≥0∞) :
    ENNReal.ofReal (planeComparison y s (TN.family.plane 0 a')
        (NeckSelection.modelPlane 𝒢.type (𝒢.model Q)) ^ 2) ≤ D := by
  have hQ1 : Q.1 = 𝒢.root.1 := by simpa using hQlev
  have hQr : Q = 𝒢.root := (hAnc n E ℓ₀ P μ k Λ b 𝒢).1 Q hQ hQ1
  rw [TN.level_zero_plane a' ha', TN.initialPlane_fit, ← hQr]
  simp [planeComparison]

/-- **The level estimate** (`LevelEstimateStatement`, in implication
form). -/
theorem d1d_levelEstimate_proof :
    AncestorInclusionStatement → PairBoundStatement → Terminal.AncestorStatement →
      LevelEstimateStatement := by
  intro hAI hPB hAnc n E ℓ₀ P μ k Λ b 𝒢 δ κ θ γ TN C₁ W _ pos hΛ hC₁ hOcc hdom hinc w j₀ i a
    hi hj₀i ha hwit O hO hOdist hOdepth j hj Q hQ hQlev hOQ
  have hr₀ : 0 < 48 * 𝒢.rootScale := by
    have := Terminal.d1c_rootScale_pos 𝒢
    linarith
  have hsc : ∀ m, TN.family.scale m = coherentScale (48 * 𝒢.rootScale) m := by
    intro m
    rw [CoherentFamily.scale, TN.initialRadius_eq]
  have hpos : ∀ m, 0 < coherentScale (48 * 𝒢.rootScale) m := d1dlevel_coherentScale_pos hr₀
  have hanti : ∀ {m m' : ℕ}, m ≤ m' →
      coherentScale (48 * 𝒢.rootScale) m' ≤ coherentScale (48 * 𝒢.rootScale) m :=
    fun hm => d1dlevel_coherentScale_anti hr₀.le hm
  have hfin := d1dlevel_modelCoeff_ne_top 𝒢 hQ
  rw [hsc j₀] at hwit
  refine le_trans (hPB n (𝒢.type.rank k) (Space n) W pos TN.family
    (NeckSelection.modelPlane 𝒢.type (𝒢.model Q))
    (C₁ * (P.modelCoeff μ Λ (𝒢.model Q) Q).toReal) j w hdom ?_) (le_of_eq ?_)
  · intro i' hi' a' ha' hw' y hy
    rw [hsc j] at hw' hy ⊢
    rcases i' with _ | m
    · -- level zero: only when `j = 0`, and then the comparison is `0`
      have hj0 : j = 0 := by omega
      subst hj0
      exact d1dlevel_levelZero hAnc 𝒢 TN hQ hQlev a' ha' y _ _
    · -- a genuine occurrence of level `m + 1 ∈ {j, j + 1}`
      obtain ⟨M, hMplane, hMmin⟩ := TN.genuine_fit m a' ha'
      have hzS := TN.genuine_mem m a' ha'
      rw [hsc (m + 1)] at hMmin
      have hle1 : coherentScale (48 * 𝒢.rootScale) (m + 1) ≤
          coherentScale (48 * 𝒢.rootScale) j := hanti (by omega)
      have hle10 : coherentScale (48 * 𝒢.rootScale) j ≤
          10 * coherentScale (48 * 𝒢.rootScale) (m + 1) := by
        rcases hi' with h | h
        · rw [← h]
          linarith [hpos (m + 1)]
        · have hmj : m = j := by omega
          rw [hmj, ← d1dlevel_coherentScale_succ]
      have hij : coherentScale (48 * 𝒢.rootScale) i ≤ coherentScale (48 * 𝒢.rootScale) j :=
        hanti (hj.trans hj₀i)
      have hj₀j : coherentScale (48 * 𝒢.rootScale) j₀ ≤ coherentScale (48 * 𝒢.rootScale) j :=
        hanti hj
      -- position distance to the witness, then parabolic distance
      have hdist_pos : dist (pos (TN.family.center (m + 1) a')) (pos (TN.family.center i a)) ≤
          24 * coherentScale (48 * 𝒢.rootScale) j := by
        have h1 := dist_triangle_right (pos (TN.family.center (m + 1) a'))
          (pos (TN.family.center i a)) w
        linarith
      have hdist : dist (TN.family.center (m + 1) a') (TN.family.center i a) ≤
          24 * coherentScale (48 * 𝒢.rootScale) j :=
        hinc (m + 1) i a' a ha' ha _
          (by rw [hsc]; linarith [hpos j]) (by rw [hsc]; linarith [hpos j]) hdist_pos
      -- the ancestor inclusion at the witness's owner
      obtain ⟨hball, hscaleQ⟩ := hAI n E ℓ₀ P μ k Λ b 𝒢 i (TN.family.center i a) O j Q
        (TN.family.center (m + 1) a') hΛ hO hOdist hOdepth (hj.trans hj₀i) hQ hQlev hOQ hzS
        hdist
      have hocc := hOcc (m + 1) (TN.family.center (m + 1) a') M hzS hMmin Q hQ
        ((Metric.ball_subset_ball (by linarith)).trans hball)
        (hscaleQ.trans (mul_le_mul_of_nonneg_left (hanti (by omega)) (by norm_num)))
        y (coherentScale (48 * 𝒢.rootScale) j) (by linarith) hle1 hle10
      rw [hMplane, ← d1dlevel_ofReal_mul_eq hC₁ hfin]
      exact hocc
  · rw [d1dlevel_ofReal_mul_eq (c := 4 * C₁) (by linarith) hfin, mul_assoc]

end Witness

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
