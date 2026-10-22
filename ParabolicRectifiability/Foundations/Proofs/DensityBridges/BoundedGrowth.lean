import ParabolicRectifiability.Foundations.Proofs.DensityBridges.BoundedGrowthLemmas
import ParabolicRectifiability.Decomposition.Interfaces

/-! # Bounded growth of measures with bounded square energy and lower density

`fbgrowth_exists_boundedGrowth_constant` proves the bounded-growth estimate
`ν(P(q,ρ)) ≤ C_n (A + m) ρ^k` for `0 < ρ ≤ R/2`, whenever `S_ν^R ≤ m` and `Θ_*^k(ν,·) ≤ A`
hold `ν`-almost everywhere. It has the type of `exists_boundedGrowth_constant`, in the
implication form `hcore → PackingMassStatement → …`: the decomposition core and the packing
mass bound are hypotheses.

Proof. Let `C₀ > 0` be the core constant of `hcore`; take `C_n = 5^(n+2) C₀`, chosen before
`k`, `T`, `ν`, `A`, `m`, `R`. Fix `q` and `0 < ρ ≤ R/2`, and `μ' = rescaledSource ν k q ρ hρ`
(finite on compacts by the general instance; inner regular by
`fbgrowth_innerRegular_rescaledSource` below). `fbgrowth_rescaled_threshold` gives the core's
threshold hypothesis with `M = m`, `Γ = 0` (since `2ρ ≤ R`); `hcore` gives retained sets `D`
with `IsRectifiabilityDecomposition k C₀ m 0 μ' D`; `fbgrowth_rescaled_lowerDensity_ae`
transfers the density bound; `fbgrowth_unit_ball_le` (with `hpack`) gives
`μ'(P(0,1)) ≤ C₀ m + 5^k C₀ A`; `fbgrowth_ball_eq_rescaled` scales back:
`ν(P(q,ρ)) = ρ^k μ'(P(0,1)) ≤ ρ^k (C₀ m + 5^k C₀ A) ≤ 5^(n+2) C₀ (A+m) ρ^k`, using
`1 ≤ 5^k ≤ 5^(n+2)`. A single compact support for all balls is not required: `D` is chosen
per ball.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- The rescaled source of an inner regular measure is inner regular (the argument of
`Enhancements.innerRegular_rescaledSource`, restated here to keep the import graph small). -/
theorem fbgrowth_innerRegular_rescaledSource {n : ℕ} (μ : Measure (Space n))
    (hreg : μ.InnerRegular) (k : ℕ) (q : Space n) (ρ : ℝ) (hρ : 0 < ρ) :
    (rescaledSource μ k q ρ hρ).InnerRegular := by
  have : (μ.map (similarity q ρ hρ)).InnerRegular := Measure.InnerRegular.map (similarity q ρ hρ)
  unfold rescaledSource
  infer_instance

/-- **Bounded growth.** Given the decomposition core `hcore` and the packing mass bound, there
is `C > 0` such that `S_ν^R ≤ m` and `Θ_*^k(ν,·) ≤ A` `ν`-a.e. imply
`ν(P(q,ρ)) ≤ C (A + m) ρ^k` for every `q` and `0 < ρ ≤ R/2`; this is the implication form of
`exists_boundedGrowth_constant`. -/
theorem fbgrowth_exists_boundedGrowth_constant (n : ℕ) (hn : 1 ≤ n)
    (hcore : ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
      μ (Metric.ball (point 0 0) 1 ∩
        {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ →
      HasFamilyDecomposition k T C M Γ μ)
    (hpack : PackingMassStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ ν : Measure (Space n), IsFiniteMeasureOnCompacts ν → ν.InnerRegular →
      ∀ A m R : ℝ, 0 ≤ A → 0 ≤ m → 0 < R →
      (∀ᵐ z ∂ν, squareEnergy ν k T R z ≤ ENNReal.ofReal m ∧
        lowerDensity ν k z ≤ ENNReal.ofReal A) →
      ∀ (q : Space n) (ρ : ℝ), 0 < ρ → ρ ≤ R / 2 →
        ν (Metric.ball q ρ) ≤ ENNReal.ofReal (C * (A + m) * ρ ^ k) := by
  obtain ⟨C, hC, hdec⟩ := hcore
  refine ⟨5 ^ (n + 2) * C, by positivity, ?_⟩
  intro k hk hkn T hT ν hν hreg A m R hA hm hR hae q ρ hρ hρR
  have := hν
  have hμc : IsFiniteMeasureOnCompacts (rescaledSource ν k q ρ hρ) := inferInstance
  have hμr := fbgrowth_innerRegular_rescaledSource ν hreg k q ρ hρ
  have h2ρ : 2 * ρ ≤ R := by linarith
  have hthr := fbgrowth_rescaled_threshold hn hk hkn T ν q ρ hρ m R h2ρ
    (hae.mono fun z hz => hz.1)
  obtain ⟨D, hD, -, -⟩ :=
    hdec k hk hkn T hT (rescaledSource ν k q ρ hρ) hμc hμr m 0 hm le_rfl hthr
  have hdens := fbgrowth_rescaled_lowerDensity_ae ν k q ρ hρ A (hae.mono fun z hz => hz.2)
  have hunit := fbgrowth_unit_ball_le hpack hn hk hkn (rescaledSource ν k q ρ hρ) hμc hμr
    C m A hC hm hA D hD hdens
  have h5 : (5 : ℝ) ^ k ≤ 5 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) hkn
  have h1 : (1 : ℝ) ≤ 5 ^ (n + 2) := one_le_pow₀ (by norm_num)
  have hρk : 0 ≤ ρ ^ k := pow_nonneg hρ.le k
  rw [fbgrowth_ball_eq_rescaled ν k q ρ hρ]
  calc ENNReal.ofReal ρ ^ k * rescaledSource ν k q ρ hρ (Metric.ball (point 0 0) 1)
      ≤ ENNReal.ofReal ρ ^ k * ENNReal.ofReal (C * m + 5 ^ k * C * A) :=
        mul_le_mul' le_rfl hunit
    _ = ENNReal.ofReal (ρ ^ k * (C * m + 5 ^ k * C * A)) := by
        rw [ENNReal.ofReal_mul hρk, ENNReal.ofReal_pow hρ.le]
    _ ≤ ENNReal.ofReal (5 ^ (n + 2) * C * (A + m) * ρ ^ k) := by
        apply ENNReal.ofReal_le_ofReal
        have e1 := mul_nonneg (sub_nonneg.2 h1) (mul_nonneg (mul_nonneg hC.le hm) hρk)
        have e2 := mul_nonneg (sub_nonneg.2 h5) (mul_nonneg (mul_nonneg hC.le hA) hρk)
        nlinarith [e1, e2]

end ParabolicRectifiability.Foundations
