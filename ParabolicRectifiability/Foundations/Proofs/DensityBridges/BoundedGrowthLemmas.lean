import ParabolicRectifiability.Foundations.Statements.DensityBridges
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.BoundedGrowthUnit
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.BoundedGrowthRescale
import ParabolicRectifiability.Measure.BetaLaws
import ParabolicRectifiability.Specifications.Rectifiability

/-! # Bounded growth: rescaling and unit-scale mass control

Intermediate lemmas for the bounded-growth estimate `fbgrowth_exists_boundedGrowth_constant`
(the implication form `hcore → PackingMassStatement → …` of `exists_boundedGrowth_constant`),
with constant `C_n = 5^(n+2) C₀`, `C₀` the core constant of `hcore`.

* Rescaling, at a centre `q` and radius `0 < ρ ≤ R/2`, with the rescaled source
  `μ' = rescaledSource ν k q ρ hρ = ρ^{-k} (T_{q,ρ})_# ν`:
  - `fbgrowth_rescaled_lowerDensity_ae`: the lower-density bound transfers to `μ'`;
  - `fbgrowth_rescaled_threshold`: the square bound `S_ν^R ≤ m` gives zero exceptional
    `μ'`-mass in `P(0,1)` at threshold `m` and endpoint `2`;
  - `fbgrowth_ball_eq_rescaled`: `ν(P(q,ρ)) = ρ^k μ'(P(0,1))`.
* Retained-mass control at unit scale, `fbgrowth_unit_ball_le`: the core decomposition of
  `μ'` with `Γ = 0`, plus `PackingMassStatement` applied to the actual compact support, give
  `μ'(P(0,1)) ≤ C₀ m + 5^k C₀ A`.

`hcore` is used only in the final assembly, and `hpack` enters `fbgrowth_unit_ball_le` as an
explicit hypothesis. None of these lemmas assumes growth, absolute continuity, or the
conclusion of `ACBridgeStatement`. Each statement is proved by the corresponding `…_proof`
lemma.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- **Retained-mass control at unit scale.**

For `1 ≤ n`, `1 ≤ k ≤ n+2`, a locally Radon `μ`, reals `C > 0`, `M ≥ 0`,
`A ≥ 0`, and retained sets `D` forming a core decomposition
`IsRectifiabilityDecomposition k C M 0 μ D` (exceptional allowance `Γ = 0`), if
`Θ_*^k(μ,z) ≤ A` for `μ`-a.e. `z`, then `μ(P(0,1)) ≤ C M + 5^k C A`.

Proof. `hD.measure_eq` evaluated on `P(0,1)`: remainder plus `μ(P(0,1) ∩ H) + μ(P(0,1) ∩ V)`.
The remainder is `≤ ofReal (C M + 0)` (`hD.remainder_bound`). Let `K = D.supportUnion μ`
(closed, hence Borel: `Measure.isClosed_support`). The retained part is carried by `K`:
`μ(H \ K) ≤ (μ⌊H)(supp(μ⌊H)ᶜ) = 0` (`Measure.measure_compl_support`; `Space n` is second
countable, hence hereditarily Lindelöf), likewise for `V`; with `H ∩ V = ∅` (`D.disjoint`) this
gives `μ(P(0,1) ∩ H) + μ(P(0,1) ∩ V) ≤ μ(P(0,1) ∩ K) = (μ⌊K)(P(0,1))`
(`measure_union`, `Measure.restrict_apply`). Apply `hpack n hn k hk hkn K _ 1 C one_pos hC.le
hD.content.finite_packing μ hμ hreg A hA _ (point 0 0) 1 one_pos le_rfl`: the content field
`finite_packing` has exactly the shape of the packing hypothesis with `R₀ = 1`, `C_K = C`, and the
`μ`-a.e. density bound restricts to `z ∈ K`. This gives `(μ⌊K)(P(0,1)) ≤ ofReal (5^k C A 1^k)`.
Add (`ENNReal.ofReal_add`, nonnegative terms). No absolute continuity is used.
`PackingMassStatement` is the first hypothesis. -/
theorem fbgrowth_unit_ball_le (hpack : PackingMassStatement) {n : ℕ} (hn : 1 ≤ n) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n + 2) (μ : Measure (Space n)) (hμ : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular) (C M A : ℝ) (hC : 0 < C) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (D : RetainedSets n) (hD : IsRectifiabilityDecomposition k C M 0 μ D)
    (hdens : ∀ᵐ z ∂μ, lowerDensity μ k z ≤ ENNReal.ofReal A) :
    μ (Metric.ball (point 0 0) 1) ≤ ENNReal.ofReal (C * M + 5 ^ k * C * A) := by
  exact fbgrowth_unit_ball_le_proof hpack hn hk hkn μ hμ hreg C M A hC hM hA D hD hdens

/-- **The lower-density bound transfers to the rescaled source** (scale invariance of `Θ_*^k`
under `μ' = ρ^{-k} (T_{q,ρ})_# ν`).

For any measure `ν`, any `k`, a centre `q`, `ρ > 0` and a real `A`, if
`Θ_*^k(ν,z) ≤ A` for `ν`-a.e. `z`, then `Θ_*^k(μ',w) ≤ A` for `μ'`-a.e. `w`, where
`μ' = rescaledSource ν k q ρ hρ`.

Proof. Pointwise identity first: for `r > 0`,
`densityRatio μ' k (T z) r = densityRatio ν k z (ρ r)` with `T = similarity q ρ hρ`
(`rescaledSource`, `Measure.smul_apply`, `MeasurableEquiv.map_apply` for
`(similarity q ρ hρ).toMeasurableEquiv`, `preimage_similarity_ball`, and
`ofReal (ρ r)^k = ofReal ρ^k · ofReal r^k` with `ofReal ρ ≠ 0, ⊤`). Since `r ↦ ρ r` maps
`𝓝[>] 0` onto itself (`Filter.map` of a positive dilation; e.g. via the order isomorphism
`OrderIso.mulLeft₀` or `tendsto_nhdsWithin` both ways), the liminfs agree:
`lowerDensity μ' k (T z) = lowerDensity ν k z`. Then a.e. transfer: `ae_smul_measure` and
`(similarity q ρ hρ).toMeasurableEquiv.ae_map_iff` (no measurability of the density needed),
evaluating at `w = T z` (compare `rescaledSource_apply`). -/
theorem fbgrowth_rescaled_lowerDensity_ae {n : ℕ} (ν : Measure (Space n)) (k : ℕ)
    (q : Space n) (ρ : ℝ) (hρ : 0 < ρ) (A : ℝ)
    (h : ∀ᵐ z ∂ν, lowerDensity ν k z ≤ ENNReal.ofReal A) :
    ∀ᵐ w ∂(rescaledSource ν k q ρ hρ),
      lowerDensity (rescaledSource ν k q ρ hρ) k w ≤ ENNReal.ofReal A := by
  exact fbgrowth_rescaled_lowerDensity_ae_proof ν k q ρ hρ A h

/-- **Zero exceptional mass for the rescaled source.** Since `2ρ ≤ R`, the square energy of
`ν` at endpoint `2ρ` is at most `m` almost everywhere, so the threshold hypothesis holds with
threshold `m` and zero exceptional mass.

For `1 ≤ n`, `1 ≤ k ≤ n+2`, any family `T`, any measure `ν`, a centre `q`,
`ρ > 0`, reals `m`, `R` with `2ρ ≤ R`: if `S_{ν,T}^R ≤ m` for `ν`-a.e. `z`, then
`μ'(P(0,1) ∩ {S_{μ',T}^2 > m}) ≤ ofReal 0`, `μ' = rescaledSource ν k q ρ hρ` — exactly the
threshold hypothesis of the core (`hcore`) with `M = m`, `Γ = 0`.

Proof. `squareEnergy_rescaledSource_eq_proof : SquareEnergyRescalingStatement` gives
`S_{μ',T}^2(w) = S_{ν,T}^{2ρ}(T⁻¹ w)` (`ρ · 2 = 2ρ`). Endpoint monotonicity
`S_{ν,T}^{2ρ} ≤ S_{ν,T}^R` (`squareEnergy` is a set integral over `Ioo 0 ·`;
`lintegral_mono_set`/`setLIntegral_mono_set` with `Ioo 0 (2ρ) ⊆ Ioo 0 R`). Hence the preimage
under `T` of the exceptional set lies in the `ν`-null set `{z | ofReal m < S_{ν,T}^R z}`; evaluate
`μ'` through `rescaledSource_apply` and `measure_mono_null` (compare
`rescaledSource_threshold`). Unavailable families need no case: the identity is for every
family. -/
theorem fbgrowth_rescaled_threshold {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) (T : FamilyKind) (ν : Measure (Space n)) (q : Space n) (ρ : ℝ)
    (hρ : 0 < ρ) (m R : ℝ) (hρR : 2 * ρ ≤ R)
    (h : ∀ᵐ z ∂ν, squareEnergy ν k T R z ≤ ENNReal.ofReal m) :
    rescaledSource ν k q ρ hρ (Metric.ball (point 0 0) 1 ∩
      {z | ENNReal.ofReal m < squareEnergy (rescaledSource ν k q ρ hρ) k T 2 z}) ≤
        ENNReal.ofReal 0 := by
  exact fbgrowth_rescaled_threshold_proof hn hk hkn T ν q ρ hρ m R hρR h

/-- **Scaling back the unit ball** (normalization `μ' = ρ^{-k} (T_{q,ρ})_# ν` at `(q,ρ)`).

For any measure `ν`, any `k`, a centre `q` and `ρ > 0`:
`ν(P(q,ρ)) = ρ^k μ'(P(0,1))` (in `ℝ≥0∞`, `ρ^k` as `ENNReal.ofReal ρ ^ k`).

Proof: `μ'(P(0,1)) = (ofReal ρ)⁻¹^k ν(T⁻¹(P(0,1)))` (`rescaledSource`, `Measure.smul_apply`,
`MeasurableEquiv.map_apply`); `T q = point 0 0` and `preimage_similarity_ball` give
`T⁻¹(P(0,1)) = P(q, ρ·1)`; then `ofReal ρ ^ k * (ofReal ρ)⁻¹ ^ k = 1`
(`ENNReal.mul_inv_cancel`, `mul_pow`, `ofReal ρ ≠ 0, ⊤`). -/
theorem fbgrowth_ball_eq_rescaled {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (q : Space n)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ν (Metric.ball q ρ) =
      ENNReal.ofReal ρ ^ k * rescaledSource ν k q ρ hρ (Metric.ball (point 0 0) 1) := by
  exact fbgrowth_ball_eq_rescaled_proof ν k q ρ hρ

end ParabolicRectifiability.Foundations
