import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.Measure.Neck.PlaneTime.TimeCompatibility

/-! # The fitted-time comparison (`d1c_fittedTime`)

Proof of `d1c_fittedTime_proof : LocalErrorStatement → FittedTimeStatement`.
`LocalErrorStatement` enters only as the hypothesis.

Route. For a horizontal region, two admissible points `g, g'` of level
`l` with `d_P(g, g') ≤ 20 r_l`, and their full fitted models `Π_g = L × {τ}`,
`Π_{g'} = L' × {τ'}` (fits of the original `μ` on `P(g, 40 r_l)`, `P(g', 40 r_l)`):
* the common source ball `B = P(g, 5 r_l)` lies in both fitting balls (`5 + 20 < 40`);
* the base `ms3_time_diff_mass` gives `μ(B) |τ - τ'| ≤ ∫_B d_P(·, Π_g)² dμ + ∫_B d_P(·, Π_{g'})² dμ`
  (the represented sets agree through `NeckSelection.lowerModelSet_modelPlane` and the helper
  `d1cftime_lowerModelSet_horizontal`), hence `≤ I(g, l) + I(g', l)`;
* lower ADR at `g ∈ S ⊆ supp μ`, `g ∈ P(a, 5R)`, radius `5 r_l ≤ 240 R`:
  `μ(B) ≥ A⁻¹ (5 r_l)^k`;
* the local error estimate: `I ≤ (2000 Λ)^{k+2} b r_l^{k+2}` for `Λ ≥ 4000`.
So `|τ - τ'| ≤ 2 A (2000 Λ)^{k+2} b r_l² 5^{-k} ≤ η r_l²` once `b ≤ η / (2 A (2000 Λ)^{k+2})`.

Constants, in the statement's quantifier order: `Λ₀ = 4000`; `B = 240`; `b₀ = η / (2 A (2000 Λ)^{k+2})`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

/-- For the horizontal type, the lower model set is the horizontal slab `L × {τ}`. -/
theorem d1cftime_lowerModelSet_horizontal {n m : ℕ} {T : NeckType} (hT : T = .horizontal)
    (L : AffineSpatialPlane n m) (τ : ℝ) :
    T.lowerModelSet L τ = {z : Space n | z.1 ∈ L.toSet ∧ z.2.val = τ} := by
  subst hT
  rfl

/-- On a subset of the fitting ball, the squared distance to the horizontal slab of a model of a
horizontal type integrates to at most the model's fit. -/
theorem d1cftime_setLIntegral_le_fit {n k : ℕ} {T : NeckType} (hT : T = .horizontal)
    (μ : Measure (Space n)) (M : Models n k T.toFamilyKind) {s : Set (Space n)} {x : Space n}
    {ρ : ℝ} (hs : s ⊆ Metric.ball x ρ) :
    ∫⁻ z in s, Metric.infEDist z (NeckType.horizontal.lowerModelSet
        (NeckSelection.modelPlane T M) (NeckSelection.modelTime T M)) ^ 2 ∂μ ≤
      fit μ M x ρ := by
  have hset : NeckType.horizontal.lowerModelSet (NeckSelection.modelPlane T M)
      (NeckSelection.modelTime T M) = modelSet M := by
    rw [← NeckSelection.lowerModelSet_modelPlane T M, d1cftime_lowerModelSet_horizontal hT]
    rfl
  rw [hset]
  unfold fit modelCost
  exact lintegral_mono_set hs

/-- Points of the root cell lie in the support (the partition covers `supp μ`). -/
theorem d1cftime_mem_support {n : ℕ} {μ : Measure (Space n)} {R : ℝ}
    {P : DirectPartition μ.support R} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b)
    {g : Space n} (hg : g ∈ 𝒢.rootCell) : g ∈ μ.support := by
  rw [← P.cell_cover 𝒢.root.1]
  exact Set.mem_biUnion 𝒢.root_isCell hg

/-- Points of the root cell of a forest region lie in `P(a, 5R)`. -/
theorem d1cftime_dist_lt {n : ℕ} {μ : Measure (Space n)} {R : ℝ}
    {P : DirectPartition μ.support R} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b)
    {a : Space n} (hF : P.InForest a R 𝒢.root) {g : Space n} (hg : g ∈ 𝒢.rootCell) :
    dist g a < 5 * R := by
  obtain ⟨z₀, hz₀, ⟨w, hw₀, hwa⟩, hbelow⟩ := hF
  have hsub : P.cellOf 𝒢.root ⊆ P.cellOf (0, z₀) := hbelow.2.2
  have h0 : coherentScale R 0 = R := by simp [coherentScale]
  have hball := P.cell_subset_ball 0 z₀ hz₀
  have hg' : g ∈ Metric.ball z₀ (2 * coherentScale R 0) := hball (hsub hg)
  have hw' : w ∈ Metric.ball z₀ (2 * coherentScale R 0) := hball hw₀
  rw [h0, Metric.mem_ball] at hg' hw'
  rw [Metric.mem_ball] at hwa
  have hc := dist_comm z₀ w
  calc dist g a ≤ dist g z₀ + dist z₀ w + dist w a := dist_triangle4 _ _ _ _
    _ < 2 * R + 2 * R + R := by linarith
    _ = 5 * R := by ring

/-- The root side is at most the top scale. -/
theorem d1cftime_rootScale_le {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b) :
    𝒢.rootScale ≤ ℓ₀ := by
  unfold GoodRegion.rootScale DirectPartition.scale coherentScale
  exact div_le_self P.scale_pos.le (one_le_pow₀ (by norm_num))

/-- The construction scales are at most `48 ℓ₀`. -/
theorem d1cftime_stageScale_le {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b) (l : ℕ) :
    stageScale 𝒢 l ≤ 48 * ℓ₀ := by
  have h1 := d1cftime_rootScale_le 𝒢
  have h2 := d1c_rootScale_pos 𝒢
  unfold stageScale coherentScale
  calc 48 * 𝒢.rootScale / 10 ^ l ≤ 48 * 𝒢.rootScale :=
        div_le_self (by linarith) (one_le_pow₀ (by norm_num))
    _ ≤ 48 * ℓ₀ := by linarith

/-- The measure-theoretic core: on the common source `P(g, 5r)`, the lower mass bound and the two
fitting errors bound the fitted-time difference. -/
theorem d1cftime_core {n k : ℕ} {T : NeckType} (hT : T = .horizontal) (μ : Measure (Space n))
    (M₁ M₂ : Models n k T.toFamilyKind) (g g' : Space n) (r A X : ℝ) (hr : 0 < r)
    (hA : 0 < A) (hX : 0 ≤ X) (hgg' : dist g g' ≤ 20 * r)
    (hmass : ENNReal.ofReal (A⁻¹ * (5 * r) ^ k) ≤ μ (Metric.ball g (5 * r)))
    (h₁ : fit μ M₁ g (40 * r) ≤ ENNReal.ofReal X)
    (h₂ : fit μ M₂ g' (40 * r) ≤ ENNReal.ofReal X) :
    A⁻¹ * (5 * r) ^ k *
        |NeckSelection.modelTime T M₁ - NeckSelection.modelTime T M₂| ≤ X + X := by
  have hb1 : Metric.ball g (5 * r) ⊆ Metric.ball g (40 * r) :=
    Metric.ball_subset_ball (by linarith)
  have hb2 : Metric.ball g (5 * r) ⊆ Metric.ball g' (40 * r) :=
    Metric.ball_subset_ball' (by linarith)
  have hdiff := ms3_time_diff_mass μ (Metric.ball g (5 * r)) (NeckSelection.modelPlane T M₁)
    (NeckSelection.modelPlane T M₂) (NeckSelection.modelTime T M₁) (NeckSelection.modelTime T M₂)
  have hI₁ := d1cftime_setLIntegral_le_fit hT μ M₁ hb1
  have hI₂ := d1cftime_setLIntegral_le_fit hT μ M₂ hb2
  have hm0 : 0 ≤ A⁻¹ * (5 * r) ^ k :=
    mul_nonneg (inv_nonneg.mpr hA.le) (pow_nonneg (by linarith) k)
  have key : ENNReal.ofReal (A⁻¹ * (5 * r) ^ k *
      |NeckSelection.modelTime T M₁ - NeckSelection.modelTime T M₂|) ≤
      ENNReal.ofReal (X + X) := by
    rw [ENNReal.ofReal_mul hm0, ENNReal.ofReal_add hX hX]
    calc ENNReal.ofReal (A⁻¹ * (5 * r) ^ k) *
          ENNReal.ofReal |NeckSelection.modelTime T M₁ - NeckSelection.modelTime T M₂|
        ≤ μ (Metric.ball g (5 * r)) *
          ENNReal.ofReal |NeckSelection.modelTime T M₁ - NeckSelection.modelTime T M₂| := by
          gcongr
      _ ≤ _ := hdiff
      _ ≤ fit μ M₁ g (40 * r) + fit μ M₂ g' (40 * r) := add_le_add hI₁ hI₂
      _ ≤ ENNReal.ofReal X + ENNReal.ofReal X := add_le_add h₁ h₂
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 key

/-- The real arithmetic: `A⁻¹ (5r)^k Δ ≤ 2 K b r^{k+2}` and `b ≤ η / (2 A K)` give `Δ ≤ η r²`. -/
theorem d1cftime_real {k : ℕ} {A K b η r Δ : ℝ} (hA : 1 ≤ A) (hK : 0 < K) (hbb : b ≤ η / (2 * A * K))
    (hr : 0 < r) (hΔ : 0 ≤ Δ)
    (h : A⁻¹ * (5 * r) ^ k * Δ ≤ K * b * r ^ (k + 2) + K * b * r ^ (k + 2)) :
    Δ ≤ η * r ^ 2 := by
  have hA0 : 0 < A := by linarith
  have hrk : 0 < r ^ k := pow_pos hr k
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have h5 : r ^ k ≤ (5 * r) ^ k := pow_le_pow_left₀ hr.le (by linarith) k
  have h2Kb : 2 * K * b ≤ η / A := by
    rw [le_div_iff₀ (mul_pos (mul_pos two_pos hA0) hK)] at hbb
    rw [le_div_iff₀ hA0]
    linarith
  have e : r ^ (k + 2) = r ^ k * r ^ 2 := pow_add r k 2
  have h1 : A⁻¹ * ((5 * r) ^ k * Δ) ≤ A⁻¹ * (η * r ^ k * r ^ 2) := by
    calc A⁻¹ * ((5 * r) ^ k * Δ) = A⁻¹ * (5 * r) ^ k * Δ := by ring
      _ ≤ K * b * r ^ (k + 2) + K * b * r ^ (k + 2) := h
      _ = 2 * K * b * (r ^ k * r ^ 2) := by rw [e]; ring
      _ ≤ η / A * (r ^ k * r ^ 2) := mul_le_mul_of_nonneg_right h2Kb (mul_pos hrk hr2).le
      _ = A⁻¹ * (η * r ^ k * r ^ 2) := by ring
  have h2 : (5 * r) ^ k * Δ ≤ η * r ^ k * r ^ 2 := le_of_mul_le_mul_left h1 (inv_pos.mpr hA0)
  have h3 : r ^ k * Δ ≤ r ^ k * (η * r ^ 2) := by
    calc r ^ k * Δ ≤ (5 * r) ^ k * Δ := mul_le_mul_of_nonneg_right h5 hΔ
      _ ≤ η * r ^ k * r ^ 2 := h2
      _ = r ^ k * (η * r ^ 2) := by ring
  exact le_of_mul_le_mul_left h3 hrk

/-- **Fitted-time comparison** (`FittedTimeStatement`). Constants:
`Λ₀ = 4000` (so that `LocalErrorStatement` applies), `B = 240` (the root cell lies in `P(a, 5R)`
and `5 r_l ≤ 240 ℓ_* ≤ 240 R`), `b₀ = η / (2 A (2000 Λ)^{k+2})`. -/
theorem d1c_fittedTime_proof : LocalErrorStatement → FittedTimeStatement := by
  intro hErr n _hn k _hk1 _hk2 A hA
  have hA0 : 0 < A := by linarith
  refine ⟨4000, by norm_num, fun Λ hΛ => ⟨240, by norm_num, fun η hη => ?_⟩⟩
  have hK : 0 < (2000 * Λ) ^ (k + 2) := pow_pos (by linarith) _
  refine ⟨η / (2 * A * (2000 * Λ) ^ (k + 2)), div_pos hη (mul_pos (mul_pos two_pos hA0) hK), ?_⟩
  intro b hb hbb μ _hfin _hreg a _ha R hR hADR P 𝒢 hF fits l g g' _hl hg hg' hgg' hT
  have hr : 0 < stageScale 𝒢 l := by
    have := d1c_rootScale_pos 𝒢
    unfold stageScale coherentScale
    exact div_pos (by linarith) (pow_pos (by norm_num) l)
  have hsupp := d1cftime_mem_support 𝒢 hg.1
  have hdist := d1cftime_dist_lt 𝒢 hF hg.1
  have hrle : stageScale 𝒢 l ≤ 48 * R := d1cftime_stageScale_le 𝒢 l
  have hball : g ∈ Metric.ball a (240 * R) := by
    rw [Metric.mem_ball]
    linarith
  have hmass := (hADR g ⟨hsupp, hball⟩ (5 * stageScale 𝒢 l) (by linarith) (by linarith)).1
  have hX : 0 ≤ (2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 l ^ (k + 2) :=
    mul_nonneg (mul_nonneg hK.le hb.le) (pow_nonneg hr.le _)
  have hcore := d1cftime_core hT μ (fits.model l g) (fits.model l g') g g' (stageScale 𝒢 l) A
    ((2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 l ^ (k + 2)) hr hA0 hX hgg' hmass
    (hErr n μ.support R P μ k Λ b 𝒢 fits hΛ l g hg)
    (hErr n μ.support R P μ k Λ b 𝒢 fits hΛ l g' hg')
  exact d1cftime_real hA hK hbb hr (abs_nonneg _) hcore

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
