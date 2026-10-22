import ParabolicRectifiability.QuantitativeCharacterization.Assembly.ComponentStatements

/-! # Carleson-energy bookkeeping

Elementary consequences of the definition of the Carleson energy
`M_β = sup_{a ∈ E, R > 0} R^{-k} ∫_{P(a,R)} S^R dμ`:
* a root-by-root bound `∫_{P(a,R)} S^R ≤ c R^k` gives `M_β ≤ c`;
* `M_β < ∞` gives the local Carleson bound `∫_{P(b,s)} S^s ≤ M_β s^k` at every support point
  and radius, hence the local hypotheses of the forward covering with `M = M_β`;
* the local reverse bound gives the global reverse bound at every `L`;
* two-sided growth at small radii gives positive finite upper density almost everywhere
  (the density hypothesis of the canonical decomposition).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

theorem inv_pow_mul_ofReal_mul_pow {c R : ℝ} (hc : 0 ≤ c) (hR : 0 < R) (k : ℕ) :
    (ENNReal.ofReal R)⁻¹ ^ k * ENNReal.ofReal (c * R ^ k) = ENNReal.ofReal c := by
  rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_pow hR.le, mul_left_comm, ← mul_pow,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hR).ne' ENNReal.ofReal_ne_top, one_pow,
    mul_one]

/-- A root-by-root energy bound `∫_{P(a,R)} S^R ≤ c R^k` bounds the Carleson energy by `c`. -/
theorem carlesonEnergy_le_of_root_bound {n k : ℕ} {μ : Measure (Space n)} {c : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R →
      (∫⁻ z in Metric.ball a R, squareEnergy μ k .mixed R z ∂μ) ≤ ENNReal.ofReal (c * R ^ k)) :
    carlesonEnergy μ k ≤ ENNReal.ofReal c := by
  unfold carlesonEnergy rootCarlesonSup
  refine iSup₂_le fun a ha => iSup₂_le fun R hR => ?_
  calc (ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball a R, squareEnergy μ k .mixed R z ∂μ
      ≤ (ENNReal.ofReal R)⁻¹ ^ k * ENNReal.ofReal (c * R ^ k) :=
        mul_le_mul_right (h a ha R hR) _
    _ = ENNReal.ofReal c := inv_pow_mul_ofReal_mul_pow hc hR k

/-- A finite Carleson energy bounds every support-centred root integral. -/
theorem root_bound_of_carlesonEnergy {n k : ℕ} {μ : Measure (Space n)}
    (hM : carlesonEnergy μ k ≠ ⊤) {b : Space n} (hb : b ∈ μ.support) {s : ℝ} (hs : 0 < s) :
    (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) ≤
      ENNReal.ofReal ((carlesonEnergy μ k).toReal * s ^ k) := by
  have h : (ENNReal.ofReal s)⁻¹ ^ k * (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ)
      ≤ carlesonEnergy μ k := by
    unfold carlesonEnergy rootCarlesonSup
    exact le_iSup₂_of_le b hb (le_iSup₂_of_le s hs le_rfl)
  calc (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ)
      = ENNReal.ofReal s ^ k * ((ENNReal.ofReal s)⁻¹ ^ k *
          ∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) := by
        rw [← mul_assoc, ← mul_pow,
          ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top, one_pow,
          one_mul]
    _ ≤ ENNReal.ofReal s ^ k * carlesonEnergy μ k := mul_le_mul_right h _
    _ = ENNReal.ofReal ((carlesonEnergy μ k).toReal * s ^ k) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hM,
          ENNReal.ofReal_pow hs.le, mul_comm]

/-- Global ADR bounds and `M_β < ∞` give the local hypotheses of `exists_local_forward_covering`
at every root and every buffer, with `M = M_β`. -/
theorem localHyps_of_isADR {n k : ℕ} {A : ℝ} {μ : Measure (Space n)} (hADR : IsADR A k μ)
    (hM : carlesonEnergy μ k ≠ ⊤) (a : Space n) (B R : ℝ) :
    ∀ b ∈ μ.support ∩ Metric.ball a (B * R), ∀ s : ℝ, 0 < s → s ≤ B * R →
      ENNReal.ofReal (A⁻¹ * s ^ k) ≤ μ (Metric.ball b s) ∧
        μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k) ∧
        (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) ≤
          ENNReal.ofReal ((carlesonEnergy μ k).toReal * s ^ k) :=
  fun b hb s hs _ =>
    ⟨(hADR b hb.1 s hs).1, (hADR b hb.1 s hs).2, root_bound_of_carlesonEnergy hM hb.1 hs⟩

/-- The global reverse bound at a fixed `L`, from the local reverse bound: under global
upper growth, the `(K,L)` property gives `M_β ≤ C_rev K`. -/
theorem global_reverse (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 2) (L : ℝ)
    (hL : 1 ≤ L) (A : ℝ) (hA : 1 ≤ A) :
    ∃ Crev : ℝ, 0 < Crev ∧ ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ →
      μ.InnerRegular →
      (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) →
      ∀ K : ℝ, 1 ≤ K → IsQuantitativelyMixedRectifiable k K L μ →
        carlesonEnergy μ k ≤ ENNReal.ofReal (Crev * K) := by
  obtain ⟨Brev, -, hBrev⟩ := exists_local_reverse_bound n hn k hk hkn L hL
  obtain ⟨C, hC, h⟩ := hBrev A hA
  refine ⟨C, hC, fun μ hfin hreg hup K hK hQ => ?_⟩
  refine carlesonEnergy_le_of_root_bound (mul_nonneg hC.le (by linarith)) fun a ha R hR => ?_
  exact h μ hfin hreg a ha R hR K hK (hQ.2 a ha R hR) (fun b hb s hs _ => hup b hb.1 s hs)

/-- Two-sided growth `A⁻¹ r^k ≤ μ(P(z,r)) ≤ A r^k` at support points for `0 < r ≤ r₀` gives
`0 < Θ^{k,*}(μ,·) < ∞` almost everywhere (inner regularity makes the support conull). -/
theorem hasPositiveFiniteUpperDensity_of_growth {n k : ℕ} {μ : Measure (Space n)}
    (hreg : μ.InnerRegular) {A r₀ : ℝ} (hA : 0 < A) (hr₀ : 0 < r₀)
    (h : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball z r) ∧
        μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) :
    HasPositiveFiniteUpperDensity k μ := by
  have := hreg
  have hsupp : ∀ᵐ z ∂μ, z ∈ μ.support := Measure.support_mem_ae_of_innerRegular
  filter_upwards [hsupp] with z hz
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal A⁻¹ ≤ densityRatio μ k z r ∧ densityRatio μ k z r ≤ ENNReal.ofReal A := by
    filter_upwards [Ioc_mem_nhdsGT hr₀] with r hr
    obtain ⟨h1, h2⟩ := h z hz r hr.1 hr.2
    have hpos : ENNReal.ofReal r ^ k ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr.1).ne'
    have hfin : ENNReal.ofReal r ^ k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    constructor
    · rw [densityRatio, ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin),
        ← ENNReal.ofReal_pow hr.1.le, ← ENNReal.ofReal_mul (inv_nonneg.mpr hA.le)]
      exact h1
    · rw [densityRatio, ENNReal.div_le_iff_le_mul (Or.inl hpos) (Or.inl hfin),
        ← ENNReal.ofReal_pow hr.1.le, ← ENNReal.ofReal_mul hA.le]
      exact h2
  refine ⟨lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (inv_pos.mpr hA)) ?_,
    lt_of_le_of_lt (b := ENNReal.ofReal A) ?_ ENNReal.ofReal_lt_top⟩
  · exact Filter.le_limsup_of_frequently_le (hev.mono fun r hr => hr.1).frequently
  · exact Filter.limsup_le_of_le (h := hev.mono fun r hr => hr.2)

end ParabolicRectifiability.QuantitativeCharacterization
