import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.TransferStatements

/-! # Mass of the exceptional centres

Proves `ExceptionalMassStatement` (`b3_exceptionalMass_proof`): for replacement data at level
`A`, the excluded centres `Ξ_A = ⋃_i P(z_i, 20 r_i)` satisfy `σ(Ξ_A) ≤ (C 20^k / c) σ(Ω_A)`,
where `Ω_A = Γ \ G_A` is the complement of the good set in the carrier.

The ambient exceptional set `Ξ_A` is only bounded in mass, never identified with `Ω_A`.
Proof: upper ADR at `z_i ∈ Γ` gives
`σ(P(z_i,20 r_i)) ≤ C 20^k r_i^k`; lower ADR together with `σ(Γᶜ) = 0` (support of an inner
regular measure) gives `c r_i^k ≤ σ(B_i)`, `B_i = Γ ∩ P(z_i, r_i)`; the `B_i` are pairwise
disjoint Borel subsets of `Ω_A`, so `Σ_i σ(B_i) = σ(⋃ B_i) ≤ σ(Ω_A)`.
-/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.SourceTransferTree

open ParabolicRectifiability.Foundations

/-- The reference measure of an ADR carrier is carried by `Γ`. -/
theorem b3exc_compl_null {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hΓ : IsADRCarrier k c C Γ σ) : σ Γᶜ = 0 := by
  have := hΓ.innerRegular
  have h := Measure.measure_compl_support_of_innerRegular (μ := σ)
  rwa [hΓ.support_eq] at h

/-- One enlarged ball against its relative ball: `σ(P(x,20s)) ≤ (C 20^k / c) σ(Γ ∩ P(x,s))`. -/
theorem b3exc_ball_le {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hΓ : IsADRCarrier k c C Γ σ) {x : Space n} (hx : x ∈ Γ) {s : ℝ} (hs : 0 < s) :
    σ (Metric.ball x (20 * s)) ≤
      ENNReal.ofReal (C * 20 ^ k / c) * σ (Γ ∩ Metric.ball x s) := by
  have hc := hΓ.lower_pos
  have hC := hΓ.upper_pos
  have hup := hΓ.upper x hx (20 * s) (by positivity)
  have hlow := hΓ.lower x hx s hs
  have hrel : σ (Γ ∩ Metric.ball x s) = σ (Metric.ball x s) := by
    rw [Set.inter_comm]
    exact measure_inter_conull (b3exc_compl_null hΓ)
  have heq : ENNReal.ofReal (C * (20 * s) ^ k) =
      ENNReal.ofReal (C * 20 ^ k / c) * ENNReal.ofReal (c * s ^ k) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow]
    field_simp
  calc σ (Metric.ball x (20 * s)) ≤ ENNReal.ofReal (C * (20 * s) ^ k) := hup
    _ = ENNReal.ofReal (C * 20 ^ k / c) * ENNReal.ofReal (c * s ^ k) := heq
    _ ≤ ENNReal.ofReal (C * 20 ^ k / c) * σ (Γ ∩ Metric.ball x s) := by
        rw [hrel]
        gcongr

/-- **Mass of the exceptional centres** (`ExceptionalMassStatement`). -/
theorem b3_exceptionalMass_proof : ExceptionalMassStatement := by
  intro n k c C C₀ C₁ Γ σ hΓ ν A I z r E hdata
  obtain ⟨hzr, hdisj, hsub, -⟩ := hdata
  have hmeas : ∀ i, MeasurableSet (Γ ∩ Metric.ball (z i) (r i)) := fun i =>
    hΓ.isClosed.measurableSet.inter Metric.isOpen_ball.measurableSet
  calc σ (⋃ i, Metric.ball (z i) (20 * r i))
      ≤ ∑' i, σ (Metric.ball (z i) (20 * r i)) := measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal (C * 20 ^ k / c) * σ (Γ ∩ Metric.ball (z i) (r i)) :=
        ENNReal.tsum_le_tsum fun i => b3exc_ball_le hΓ (hzr i).1 (hzr i).2
    _ = ENNReal.ofReal (C * 20 ^ k / c) * σ (⋃ i, Γ ∩ Metric.ball (z i) (r i)) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion hdisj hmeas]
    _ ≤ ENNReal.ofReal (C * 20 ^ k / c) * σ (Γ \ adrGoodSet Γ ν k A) := by
        gcongr
        exact iUnion_subset hsub

end ParabolicRectifiability.Characterization.SourceTransferTree
