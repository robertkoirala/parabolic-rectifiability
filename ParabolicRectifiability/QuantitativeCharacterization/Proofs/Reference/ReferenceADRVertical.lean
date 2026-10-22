import ParabolicRectifiability.QuantitativeCharacterization.References
import ParabolicRectifiability.Foundations.ADR

/-! # Uniform ADR of vertical references and of the ambient reference

Proof of `ba1_vertical_adr` and `ba1_ambient_adr`; the statement types are copied below.

Notation: `c_j = (2 ω_j).toReal`, with `ω_j = omega j` the volume of the open unit ball of
`ℝ^j`, so that `parabolicVolume j (P(p,s)) = c_j s^{j+2}` for `s > 0`
(`parabolicVolume_ball`, `b1adra_parabolicVolume_ball`).

* **Vertical** (`b1adra_vertical_bounds`). For a vertical `L`-reference `V` with `1 ≤ L`, map
  `Φ = V.map` and spatial rank `m` (`m + 2 = k`), the bi-Lipschitz field gives
  `P_b(p, r/L) ⊆ Φ⁻¹ P(Φ p, r) ⊆ P_b(p, L r)`. Since `Φ` is a measurable embedding (the
  hypothesis `hbasic`), `σ(P(Φ p, r)) = L^{m+1}(Φ⁻¹ P(Φ p, r))`, hence
  `c_{k-2} (r/L)^k ≤ σ(P(Φ p, r)) ≤ c_{k-2} (L r)^k`. The support of `σ` is the range of `Φ`
  (`hbasic`), so every support point is `Φ p`. The constant
  `A = max(1, max(c_{k-2} L^k, c_{k-2}⁻¹ L^k))` (`b1adra_verticalConst k L`) depends only on
  `(k, L)` and is chosen before `V`.
* **Ambient**. `parabolicVolume n (P(z,r)) = c_n r^{n+2}` exactly; the constant
  `A = max(1, max(c_n, c_n⁻¹))` (`b1adra_ambientConst n`) depends only on `n`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-! ### The base ball volume in real form -/

/-- `2 ω_j` is finite. -/
theorem b1adra_two_omega_ne_top (j : ℕ) : 2 * omega j ≠ ⊤ :=
  ENNReal.mul_ne_top (by simp) (omega_lt_top j).ne

/-- `c_j = (2 ω_j).toReal` is positive. -/
theorem b1adra_volConst_pos (j : ℕ) : 0 < (2 * omega j).toReal :=
  ENNReal.toReal_pos (mul_ne_zero (by norm_num) (omega_pos j).ne') (b1adra_two_omega_ne_top j)

/-- `parabolicVolume j (P(p,s)) = c_j s^{j+2}` for `s > 0`, in `ENNReal.ofReal` form. -/
theorem b1adra_parabolicVolume_ball {j : ℕ} (p : Space j) {s : ℝ} (hs : 0 < s) :
    parabolicVolume j (Metric.ball p s) = ENNReal.ofReal ((2 * omega j).toReal * s ^ (j + 2)) := by
  rw [parabolicVolume_ball p s hs, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (b1adra_two_omega_ne_top j), ENNReal.ofReal_pow hs.le]

/-! ### Vertical references -/

section Vertical

variable {n k : ℕ} {L : ℝ}

/-- The spatial rank of a vertical reference is `k - 2`. -/
theorem b1adra_spatialRank_eq (V : VerticalReference n k L) : V.spatialRank = k - 2 := by
  have := V.rank_eq
  omega

/-- The base ball volume of a vertical reference, with the constant `c_{k-2}` and exponent `k`. -/
theorem b1adra_base_ball (V : VerticalReference n k L) (q : Space V.spatialRank) {s : ℝ}
    (hs : 0 < s) :
    parabolicVolume V.spatialRank (Metric.ball q s) =
      ENNReal.ofReal ((2 * omega (k - 2)).toReal * s ^ k) := by
  rw [b1adra_parabolicVolume_ball q hs, V.rank_eq, b1adra_spatialRank_eq V]

/-- Inner inclusion `P_b(p, r/L) ⊆ Φ⁻¹ P(Φ p, r)` (upper Lipschitz bound). -/
theorem b1adra_ball_subset_preimage (V : VerticalReference n k L) (hL : 1 ≤ L)
    (p : Space V.spatialRank) (r : ℝ) :
    Metric.ball p (r / L) ⊆ V.map ⁻¹' Metric.ball (V.map p) r := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro q hq
  rw [Metric.mem_ball] at hq
  rw [mem_preimage, Metric.mem_ball]
  calc dist (V.map q) (V.map p) ≤ L * dist q p := (V.bilipschitz q p).2
    _ < L * (r / L) := mul_lt_mul_of_pos_left hq hL0
    _ = r := mul_div_cancel₀ r hL0.ne'

/-- Outer inclusion `Φ⁻¹ P(Φ p, r) ⊆ P_b(p, L r)` (lower Lipschitz bound). -/
theorem b1adra_preimage_subset_ball (V : VerticalReference n k L) (hL : 1 ≤ L)
    (p : Space V.spatialRank) (r : ℝ) :
    V.map ⁻¹' Metric.ball (V.map p) r ⊆ Metric.ball p (L * r) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro q hq
  rw [mem_preimage, Metric.mem_ball] at hq
  rw [Metric.mem_ball]
  calc dist q p ≤ L * dist (V.map q) (V.map p) := (V.bilipschitz q p).1
    _ < L * r := mul_lt_mul_of_pos_left hq hL0

/-- **Two-sided ball bounds at range points**:
`c_{k-2} (r/L)^k ≤ σ(P(Φ p, r)) ≤ c_{k-2} (L r)^k`, given that `Φ` is a measurable embedding. -/
theorem b1adra_vertical_bounds (V : VerticalReference n k L) (hL : 1 ≤ L)
    (hemb : MeasurableEmbedding V.map) (p : Space V.spatialRank) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((2 * omega (k - 2)).toReal * (r / L) ^ k) ≤
        V.measure (Metric.ball (V.map p) r) ∧
      V.measure (Metric.ball (V.map p) r) ≤
        ENNReal.ofReal ((2 * omega (k - 2)).toReal * (L * r) ^ k) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [VerticalReference.measure, Measure.map_apply hemb.measurable Metric.isOpen_ball.measurableSet]
  constructor
  · rw [← b1adra_base_ball V p (div_pos hr hL0)]
    exact measure_mono (b1adra_ball_subset_preimage V hL p r)
  · rw [← b1adra_base_ball V p (mul_pos hL0 hr)]
    exact measure_mono (b1adra_preimage_subset_ball V hL p r)

end Vertical

/-- The vertical ADR constant `A = max(1, max(c_{k-2} L^k, c_{k-2}⁻¹ L^k))`, a function of
`(k, L)` only. -/
def b1adra_verticalConst (k : ℕ) (L : ℝ) : ℝ :=
  max 1 (max ((2 * omega (k - 2)).toReal * L ^ k) ((2 * omega (k - 2)).toReal⁻¹ * L ^ k))

/-- **Uniform ADR of one vertical reference** with the constant `b1adra_verticalConst k L`,
given that `Φ` is a measurable embedding with `supp σ = im Φ`. -/
theorem b1adra_vertical_isADR {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (V : VerticalReference n k L)
    (hemb : MeasurableEmbedding V.map) (hsupp : V.measure.support = V.carrier) :
    IsADR (b1adra_verticalConst k L) k V.measure := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hc := b1adra_volConst_pos (k - 2)
  set c : ℝ := (2 * omega (k - 2)).toReal with hc_def
  intro z hz r hr
  rw [hsupp] at hz
  obtain ⟨p, rfl⟩ := hz
  obtain ⟨hlo, hup⟩ := b1adra_vertical_bounds V hL hemb p hr
  rw [← hc_def] at hlo hup
  constructor
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hlo
    have hpos : 0 < c⁻¹ * L ^ k := by positivity
    have hA : c⁻¹ * L ^ k ≤ b1adra_verticalConst k L :=
      (le_max_right _ _).trans (le_max_right _ _)
    calc (b1adra_verticalConst k L)⁻¹ * r ^ k ≤ (c⁻¹ * L ^ k)⁻¹ * r ^ k :=
          mul_le_mul_of_nonneg_right (inv_anti₀ hpos hA) (by positivity)
      _ = c * (r / L) ^ k := by
          rw [mul_inv, inv_inv, div_pow, div_eq_mul_inv]
          ring
  · refine hup.trans (ENNReal.ofReal_le_ofReal ?_)
    have hA : c * L ^ k ≤ b1adra_verticalConst k L :=
      (le_max_left _ _).trans (le_max_right _ _)
    calc c * (L * r) ^ k = (c * L ^ k) * r ^ k := by rw [mul_pow, mul_assoc]
      _ ≤ b1adra_verticalConst k L * r ^ k := mul_le_mul_of_nonneg_right hA (by positivity)

/-- **`ba1_vertical_adr`**, in the
implication form of its type: given the conclusion `hbasic` of `ba1_vertical_basic` (its
measurable-embedding and support clauses are used), for `1 ≤ L` the constant
`A = b1adra_verticalConst k L = max(1, max(c_{k-2} L^k, c_{k-2}⁻¹ L^k))`, which depends only on
`(k, L)`, makes the natural measure `Φ_# L^{m+1}` of every vertical `L`-reference globally
`k`-ADR. -/
theorem ba1_vertical_adr_proof
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ V : VerticalReference n k L,
      MeasurableEmbedding V.map ∧ IsClosed V.carrier ∧ V.measure.support = V.carrier ∧
        IsFiniteMeasureOnCompacts V.measure ∧ V.measure.InnerRegular) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L →
      ∃ A : ℝ, 1 ≤ A ∧ ∀ V : VerticalReference n k L, IsADR A k V.measure :=
  fun n k L hL => ⟨b1adra_verticalConst k L, le_max_left _ _,
    fun V => b1adra_vertical_isADR hL V (hbasic n k L hL V).1 (hbasic n k L hL V).2.2.1⟩

/-! ### The ambient reference -/

/-- The ambient ADR constant `A = max(1, max(c_n, c_n⁻¹))`, a function of `n` only. -/
def b1adra_ambientConst (n : ℕ) : ℝ :=
  max 1 (max (2 * omega n).toReal (2 * omega n).toReal⁻¹)

/-- **`ba1_ambient_adr`**: `parabolicVolume n` is globally
`(n+2)`-ADR with the constant `b1adra_ambientConst n = max(1, max(c_n, c_n⁻¹))`, from the exact
ball volume `c_n r^{n+2} = 2 ω_n r^{n+2}`. -/
theorem ba1_ambient_adr_proof :
    ∀ n : ℕ, ∃ A : ℝ, 1 ≤ A ∧ IsADR A (n + 2) (parabolicVolume n) := by
  intro n
  have hc := b1adra_volConst_pos n
  set c : ℝ := (2 * omega n).toReal with hc_def
  refine ⟨b1adra_ambientConst n, le_max_left _ _, ?_⟩
  intro z _ r hr
  rw [b1adra_parabolicVolume_ball z hr, ← hc_def]
  constructor
  · apply ENNReal.ofReal_le_ofReal
    have hA : c⁻¹ ≤ b1adra_ambientConst n := (le_max_right _ _).trans (le_max_right _ _)
    have h := inv_anti₀ (inv_pos.mpr hc) hA
    rw [inv_inv] at h
    exact mul_le_mul_of_nonneg_right h (by positivity)
  · apply ENNReal.ofReal_le_ofReal
    have hA : c ≤ b1adra_ambientConst n := (le_max_left _ _).trans (le_max_right _ _)
    exact mul_le_mul_of_nonneg_right hA (by positivity)

end ParabolicRectifiability.QuantitativeCharacterization
