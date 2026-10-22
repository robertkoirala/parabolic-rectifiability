import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceAdapterStatements
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Covering.Vitali

/-! # Relative differentiation with an ADR denominator

Proves `RelativeDifferentiationStatement` (`b2_relative_differentiation_proof`): for an
Ahlfors–David regular reference measure `σ` and a locally finite measure `μ`, the ratios
`μ(P(z,r))/σ(P(z,r))` converge to the Radon–Nikodym derivative `(μ.rnDeriv σ) z` for `σ`-almost
every `z`.

## Proof outline

Mathlib's differentiation theorem for Vitali families, applied on the **ambient** space with
the **global** reference measure `σ`; no restriction of `σ` and no localization of `μ`.

1. *Vitali family of `σ` on the ambient space.* `Vitali.vitaliFamily σ K` needs, at **every**
   point `x`, arbitrarily small radii with `σ(B̄(x,3r)) ≤ K σ(B̄(x,r))`. With
   `K = (C/c) 4^k` this holds for every `r > 0` at points of `Γ` (upper ADR on `P(x,4r)`, lower
   ADR on `P(x,r)`), and for all small `r` at points off `Γ`, where both sides vanish because
   `Γ = supp σ` is closed and `σ(Γᶜ) = 0`. No off-carrier ADR estimate and no doubling of `μ`
   is used.
2. *Differentiation.* `VitaliFamily.ae_tendsto_rnDeriv` gives, for `σ`-a.e. `z`,
   `μ(a)/σ(a) → (μ.rnDeriv σ) z` as `a` shrinks to `z` in the family. It covers the full
   locally finite `μ` (singular part and off-carrier mass included) directly.
3. *Closed balls.* For `z ∈ Γ` and `r > 0`, the closed ball `B̄(z,r)` belongs to the family at
   `z` (closed, nonempty interior, doubling by step 1), so `r ↦ B̄(z,r)` tends to the Vitali
   filter at `z` as `r ↓ 0`: the closed-ball ratios converge.
4. *Open balls.* `P(z,r)` is the increasing union of `B̄(z, r - r/(j+2))`. A two-sided bound
   `b σ ≤ μ` (or `μ ≤ b σ`) on all closed balls of radius `< δ` passes to open balls of radius
   `≤ δ` by continuity from below; with `0 < σ(P(z,r)) < ∞` on `Γ` this gives the open-ball
   ratio limit through `tendsto_order`.

The argument uses neither `FivefoldSelectionStatement` nor `RadonApproximationStatement`, so
the statement is proved without hypotheses. The two `IsADRCarrier` fields
`finiteOnCompacts` and `innerRegular` provide local finiteness of `σ` and `σ(Γᶜ) = 0`; the
hypothesis `μ.InnerRegular` of the statement is not needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

section Generic

variable {α : Type*} [PseudoMetricSpace α]

/-- An open ball is the increasing union of the closed balls of radii `r - r/(j+2)`. -/
theorem b2rdiff_ball_eq_iUnion_closedBall (x : α) {r : ℝ} (hr : 0 < r) :
    ball x r = ⋃ j : ℕ, closedBall x (r - r / ((j : ℝ) + 2)) := by
  ext y
  simp only [mem_ball, mem_iUnion, mem_closedBall]
  constructor
  · intro hy
    have hpos : 0 < r - dist y x := sub_pos.2 hy
    obtain ⟨j, hj⟩ := exists_nat_gt (r / (r - dist y x))
    refine ⟨j, ?_⟩
    have hj' : r < (j : ℝ) * (r - dist y x) := (div_lt_iff₀ hpos).1 hj
    have hj2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    have hle : r / ((j : ℝ) + 2) ≤ r - dist y x := by
      rw [div_le_iff₀ hj2]
      nlinarith
    linarith
  · rintro ⟨j, hj⟩
    have : 0 < r / ((j : ℝ) + 2) := by positivity
    linarith

/-- The closed balls of radii `r - r/(j+2)` increase with `j`. -/
theorem b2rdiff_monotone_closedBall (x : α) {r : ℝ} (hr : 0 < r) :
    Monotone fun j : ℕ => closedBall x (r - r / ((j : ℝ) + 2)) := by
  intro i j hij
  show closedBall x (r - r / ((i : ℝ) + 2)) ⊆ closedBall x (r - r / ((j : ℝ) + 2))
  apply closedBall_subset_closedBall
  have hij' : (i : ℝ) + 2 ≤ (j : ℝ) + 2 := by
    have : (i : ℝ) ≤ j := Nat.cast_le.2 hij
    linarith
  have : r / ((j : ℝ) + 2) ≤ r / ((i : ℝ) + 2) :=
    div_le_div_of_nonneg_left hr.le (by positivity) hij'
  linarith

/-- A measure inequality on all closed balls of radius `< δ` about `x` passes to the open balls
of radius `≤ δ` about `x` (continuity from below). -/
theorem b2rdiff_measure_ball_le {_ : MeasurableSpace α} {ρ₁ ρ₂ : Measure α} {x : α} {δ : ℝ}
    (h : ∀ s : ℝ, 0 < s → s < δ → ρ₁ (closedBall x s) ≤ ρ₂ (closedBall x s))
    {r : ℝ} (hr : 0 < r) (hrδ : r ≤ δ) : ρ₁ (ball x r) ≤ ρ₂ (ball x r) := by
  have hmono := b2rdiff_monotone_closedBall x hr
  rw [b2rdiff_ball_eq_iUnion_closedBall x hr, hmono.measure_iUnion, hmono.measure_iUnion]
  refine iSup_mono fun j => h _ ?_ ?_
  · have : 0 < r / ((j : ℝ) + 2) := by positivity
    have h2 : (1 : ℝ) < (j : ℝ) + 2 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have : r / ((j : ℝ) + 2) < r := div_lt_self hr h2
    linarith
  · have : 0 < r / ((j : ℝ) + 2) := by positivity
    linarith

end Generic

section ADR

variable {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}

/-- The reference measure does not charge the complement of its carrier. -/
theorem b2rdiff_measure_compl_carrier (hΓ : IsADRCarrier k c C Γ σ) : σ Γᶜ = 0 := by
  have := hΓ.innerRegular
  rw [← hΓ.support_eq]
  exact Measure.measure_compl_support_of_innerRegular

/-- `σ`-almost every point lies on the carrier. -/
theorem b2rdiff_ae_mem (hΓ : IsADRCarrier k c C Γ σ) : ∀ᵐ z ∂σ, z ∈ Γ := by
  have h : Γ ∈ ae σ := mem_ae_iff.2 (b2rdiff_measure_compl_carrier hΓ)
  exact h

/-- Open balls centred on the carrier have positive reference mass (lower ADR). -/
theorem b2rdiff_measure_ball_ne_zero (hΓ : IsADRCarrier k c C Γ σ) {x : Space n} (hx : x ∈ Γ)
    {r : ℝ} (hr : 0 < r) : σ (ball x r) ≠ 0 :=
  ((ENNReal.ofReal_pos.2 (mul_pos hΓ.lower_pos (pow_pos hr k))).trans_le
    (hΓ.lower x hx r hr)).ne'

/-- Closed balls centred on the carrier have positive reference mass. -/
theorem b2rdiff_measure_closedBall_ne_zero (hΓ : IsADRCarrier k c C Γ σ) {x : Space n}
    (hx : x ∈ Γ) {r : ℝ} (hr : 0 < r) : σ (closedBall x r) ≠ 0 := fun h =>
  b2rdiff_measure_ball_ne_zero hΓ hx hr (measure_mono_null ball_subset_closedBall h)

/-- Closed balls have finite reference mass. -/
theorem b2rdiff_measure_closedBall_ne_top (hΓ : IsADRCarrier k c C Γ σ) (x : Space n) (r : ℝ) :
    σ (closedBall x r) ≠ ∞ := by
  have : IsFiniteMeasureOnCompacts σ := hΓ.finiteOnCompacts
  exact measure_closedBall_lt_top.ne

/-- Open balls have finite reference mass. -/
theorem b2rdiff_measure_ball_ne_top (hΓ : IsADRCarrier k c C Γ σ) (x : Space n) (r : ℝ) :
    σ (ball x r) ≠ ∞ :=
  ne_top_of_le_ne_top (b2rdiff_measure_closedBall_ne_top hΓ x r)
    (measure_mono ball_subset_closedBall)

/-- Closed-ball doubling of `σ` at carrier points, at every radius, with constant
`(C/c) 4^k`: `σ(B̄(x,3r)) ≤ σ(P(x,4r)) ≤ C (4r)^k = (C/c) 4^k · c r^k ≤ (C/c) 4^k σ(B̄(x,r))`. -/
theorem b2rdiff_closedBall_doubling (hΓ : IsADRCarrier k c C Γ σ) {x : Space n} (hx : x ∈ Γ)
    {r : ℝ} (hr : 0 < r) :
    σ (closedBall x (3 * r)) ≤ ((C / c * 4 ^ k).toNNReal : ℝ≥0∞) * σ (closedBall x r) := by
  have hc := hΓ.lower_pos
  have hC := hΓ.upper_pos
  have hconst : C * (4 * r) ^ k = C / c * 4 ^ k * (c * r ^ k) := by
    calc C * (4 * r) ^ k = C * (4 ^ k * r ^ k) * (c / c) := by
          rw [div_self hc.ne', mul_one, mul_pow]
      _ = C / c * 4 ^ k * (c * r ^ k) := by ring
  calc σ (closedBall x (3 * r)) ≤ σ (ball x (4 * r)) :=
        measure_mono (closedBall_subset_ball (by linarith))
    _ ≤ ENNReal.ofReal (C * (4 * r) ^ k) := hΓ.upper x hx _ (by linarith)
    _ = ENNReal.ofReal (C / c * 4 ^ k) * ENNReal.ofReal (c * r ^ k) := by
        rw [hconst, ENNReal.ofReal_mul (show (0 : ℝ) ≤ C / c * 4 ^ k by positivity)]
    _ ≤ ENNReal.ofReal (C / c * 4 ^ k) * σ (ball x r) := by
        gcongr
        exact hΓ.lower x hx r hr
    _ ≤ ENNReal.ofReal (C / c * 4 ^ k) * σ (closedBall x r) := by
        gcongr
        exact ball_subset_closedBall
    _ = ((C / c * 4 ^ k).toNNReal : ℝ≥0∞) * σ (closedBall x r) := rfl

/-- The doubling hypothesis of `Vitali.vitaliFamily` at **every** ambient point: at carrier
points for every radius; off the closed carrier, small closed balls are `σ`-null. -/
theorem b2rdiff_frequently_doubling (hΓ : IsADRCarrier k c C Γ σ) (x : Space n) :
    ∃ᶠ r in 𝓝[>] (0 : ℝ),
      σ (closedBall x (3 * r)) ≤ ((C / c * 4 ^ k).toNNReal : ℝ≥0∞) * σ (closedBall x r) := by
  refine Eventually.frequently ?_
  by_cases hx : x ∈ Γ
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact b2rdiff_closedBall_doubling hΓ hx (mem_Ioi.1 hr)
  · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hΓ.isClosed.isOpen_compl x hx
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ / 3 by positivity)] with r hr
    have hsub : closedBall x (3 * r) ⊆ Γᶜ :=
      (closedBall_subset_ball (by linarith [hr.2])).trans hball
    rw [measure_mono_null hsub (b2rdiff_measure_compl_carrier hΓ)]
    exact zero_le

/-- The Vitali family of closed sets for the global reference measure `σ` on the ambient
space (Mathlib's `Vitali.vitaliFamily`, constant `(C/c) 4^k`). -/
def b2rdiff_vitaliFamily (hΓ : IsADRCarrier k c C Γ σ) : VitaliFamily σ :=
  haveI : IsFiniteMeasureOnCompacts σ := hΓ.finiteOnCompacts
  Vitali.vitaliFamily σ (C / c * 4 ^ k).toNNReal (b2rdiff_frequently_doubling hΓ)

/-- Closed balls of positive radius centred on the carrier belong to the Vitali family. -/
theorem b2rdiff_closedBall_mem_setsAt (hΓ : IsADRCarrier k c C Γ σ) {x : Space n} (hx : x ∈ Γ)
    {r : ℝ} (hr : 0 < r) : closedBall x r ∈ (b2rdiff_vitaliFamily hΓ).setsAt x := by
  show IsClosed (closedBall x r) ∧ (interior (closedBall x r)).Nonempty ∧
    ∃ r', closedBall x r ⊆ closedBall x r' ∧
      σ (closedBall x (3 * r')) ≤ ((C / c * 4 ^ k).toNNReal : ℝ≥0∞) * σ (closedBall x r)
  exact ⟨isClosed_closedBall, (nonempty_ball.2 hr).mono ball_subset_interior_closedBall,
    r, Subset.rfl, b2rdiff_closedBall_doubling hΓ hx hr⟩

/-- At a carrier point, closed balls shrinking to the point converge to the Vitali filter. -/
theorem b2rdiff_tendsto_closedBall_filterAt (hΓ : IsADRCarrier k c C Γ σ) {x : Space n}
    (hx : x ∈ Γ) :
    Tendsto (fun r : ℝ => closedBall x r) (𝓝[>] 0) ((b2rdiff_vitaliFamily hΓ).filterAt x) := by
  rw [VitaliFamily.tendsto_filterAt_iff]
  refine ⟨?_, fun ε hε => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact b2rdiff_closedBall_mem_setsAt hΓ hx (mem_Ioi.1 hr)
  · filter_upwards [Ioo_mem_nhdsGT hε] with r hr
    exact closedBall_subset_closedBall hr.2.le

/-- At a carrier point, convergence of the closed-ball ratios `μ(B̄(x,r))/σ(B̄(x,r))` implies
convergence of the open-ball ratios `μ(P(x,r))/σ(P(x,r))` to the same limit. -/
theorem b2rdiff_tendsto_ball_of_closedBall (hΓ : IsADRCarrier k c C Γ σ) (μ : Measure (Space n))
    {x : Space n} (hx : x ∈ Γ) {L : ℝ≥0∞}
    (h : Tendsto (fun r : ℝ => μ (closedBall x r) / σ (closedBall x r)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun r : ℝ => μ (ball x r) / σ (ball x r)) (𝓝[>] 0) (𝓝 L) := by
  rw [tendsto_order] at h ⊢
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨b, hab, hbL⟩ := exists_between ha
    obtain ⟨δ, hδ, hδsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (h.1 b hbL)
    have hδ0 : (0 : ℝ) < δ := hδ
    have hcl : ∀ s : ℝ, 0 < s → s < δ → (b • σ) (closedBall x s) ≤ μ (closedBall x s) := by
      intro s hs hsδ
      have hs' : b < μ (closedBall x s) / σ (closedBall x s) := hδsub (mem_Ioo.2 ⟨hs, hsδ⟩)
      rw [Measure.smul_apply, smul_eq_mul]
      exact (ENNReal.le_div_iff_mul_le (Or.inl (b2rdiff_measure_closedBall_ne_zero hΓ hx hs))
        (Or.inl (b2rdiff_measure_closedBall_ne_top hΓ x s))).1 hs'.le
    filter_upwards [Ioo_mem_nhdsGT hδ0] with r hr
    have hball := b2rdiff_measure_ball_le hcl hr.1 hr.2.le
    rw [Measure.smul_apply, smul_eq_mul] at hball
    refine hab.trans_le ?_
    exact (ENNReal.le_div_iff_mul_le (Or.inl (b2rdiff_measure_ball_ne_zero hΓ hx hr.1))
      (Or.inl (b2rdiff_measure_ball_ne_top hΓ x r))).2 hball
  · obtain ⟨b, hLb, hba⟩ := exists_between ha
    obtain ⟨δ, hδ, hδsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (h.2 b hLb)
    have hδ0 : (0 : ℝ) < δ := hδ
    have hcl : ∀ s : ℝ, 0 < s → s < δ → μ (closedBall x s) ≤ (b • σ) (closedBall x s) := by
      intro s hs hsδ
      have hs' : μ (closedBall x s) / σ (closedBall x s) < b := hδsub (mem_Ioo.2 ⟨hs, hsδ⟩)
      rw [Measure.smul_apply, smul_eq_mul]
      exact (ENNReal.div_le_iff (b2rdiff_measure_closedBall_ne_zero hΓ hx hs)
        (b2rdiff_measure_closedBall_ne_top hΓ x s)).1 hs'.le
    filter_upwards [Ioo_mem_nhdsGT hδ0] with r hr
    have hball := b2rdiff_measure_ball_le hcl hr.1 hr.2.le
    rw [Measure.smul_apply, smul_eq_mul] at hball
    exact (ENNReal.div_le_of_le_mul hball).trans_lt hba

end ADR

/-- **Relative differentiation** (`RelativeDifferentiationStatement`).

For a global ADR carrier `IsADRCarrier k c C Γ σ` and a locally Radon ambient `μ`, at
`σ`-almost every `z`, `μ(P(z,r))/σ(P(z,r)) → (μ.rnDeriv σ) z` as `r ↓ 0`. The full ambient
`μ` is differentiated, singular part and off-carrier mass included; `σ` is never restricted.
Neither `FivefoldSelectionStatement` nor `RadonApproximationStatement` is used. -/
theorem b2_relative_differentiation_proof : RelativeDifferentiationStatement := by
  intro n _hn k c C Γ σ hΓ μ hμ _hμi
  have : IsFiniteMeasureOnCompacts σ := hΓ.finiteOnCompacts
  have : IsFiniteMeasureOnCompacts μ := hμ
  filter_upwards [(b2rdiff_vitaliFamily hΓ).ae_tendsto_rnDeriv μ, b2rdiff_ae_mem hΓ]
    with z hz hzΓ
  exact b2rdiff_tendsto_ball_of_closedBall hΓ μ hzΓ
    (hz.comp (b2rdiff_tendsto_closedBall_filterAt hΓ hzΓ))

end ParabolicRectifiability.Characterization
