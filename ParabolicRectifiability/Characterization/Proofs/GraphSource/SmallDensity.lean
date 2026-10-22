import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceAdapterStatements
import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Measure.Beta

/-! # Positive finite density on an ADR carrier

Two density facts for a measure `μ` relative to an Ahlfors–David regular measure `σ` with
carrier `Γ`:

* `b2_rnDeriv_pos_on_carrier_proof` (the statement of `b2_rnDeriv_pos_on_carrier`): if
  `μ⌊Γ ≪ σ`, then `0 < dμ/dσ < ∞` at `μ`-almost every point of `Γ`. Apply the
  Radon–Nikodym facts to `ν = μ⌊Γ ≪ σ` (`Measure.rnDeriv_pos`, `Measure.rnDeriv_lt_top`), then
  identify `dν/dσ = 1_Γ dμ/dσ` `σ`-a.e. (`Measure.rnDeriv_restrict`), hence `ν`-a.e.;
* `b2_density_of_ratio_proof` (the statement of `b2_density_of_ratio`): if the ball ratio
  `μ(P(z,r))/σ(P(z,r))` at a carrier point `z` tends to `f ∈ (0, ∞)`, then the lower `k`-density
  of `μ` at `z` is positive and the upper one is finite. For small `r > 0` the ratio lies in
  `(f/2, f+1)`, and `c ≤ σ(P(z,r))/r^k ≤ C` (ADR at `z`), so
  `(f/2) c ≤ μ(P(z,r))/r^k ≤ (f+1) C`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- If `μ⌊Γ ≪ σ` for an ADR carrier `Γ` of `σ`, then `0 < dμ/dσ < ∞` at `μ`-almost every point
of `Γ`. -/
theorem b2_rnDeriv_pos_on_carrier_proof :
    ∀ n : ℕ, 1 ≤ n → ∀ (k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
      IsADRCarrier k c C Γ σ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      μ.restrict Γ ≪ σ →
        ∀ᵐ z ∂μ, z ∈ Γ → 0 < μ.rnDeriv σ z ∧ μ.rnDeriv σ z < ⊤ := by
  intro n _ k c C Γ σ hΓ μ hμ _ hac
  have := hΓ.finiteOnCompacts
  have := hμ
  have : SigmaFinite σ := source_sigmaFinite σ
  have : SigmaFinite μ := source_sigmaFinite μ
  have hΓm : MeasurableSet Γ := hΓ.isClosed.measurableSet
  have hpos : ∀ᵐ z ∂(μ.restrict Γ), 0 < (μ.restrict Γ).rnDeriv σ z :=
    Measure.rnDeriv_pos hac
  have htop : ∀ᵐ z ∂(μ.restrict Γ), (μ.restrict Γ).rnDeriv σ z < ⊤ :=
    hac.ae_le (Measure.rnDeriv_lt_top _ _)
  have heq : ∀ᵐ z ∂(μ.restrict Γ),
      (μ.restrict Γ).rnDeriv σ z = Γ.indicator (μ.rnDeriv σ) z :=
    hac.ae_le (Measure.rnDeriv_restrict μ σ hΓm)
  have hall : ∀ᵐ z ∂(μ.restrict Γ), 0 < μ.rnDeriv σ z ∧ μ.rnDeriv σ z < ⊤ := by
    filter_upwards [hpos, htop, heq, ae_restrict_mem hΓm] with z h1 h2 h3 h4
    rw [h3, Set.indicator_of_mem h4] at h1 h2
    exact ⟨h1, h2⟩
  exact (ae_restrict_iff' hΓm).1 hall

/-- `a / x = (a / s) (s / x)` for `0 < s < ∞`. -/
theorem b2small_div_eq_div_mul_div (a : ℝ≥0∞) {s : ℝ≥0∞} (h0 : s ≠ 0) (ht : s ≠ ⊤)
    (x : ℝ≥0∞) : a / x = a / s * (s / x) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc s⁻¹,
    ENNReal.inv_mul_cancel h0 ht, one_mul]

/-- At a carrier point and a positive radius, the density ratio factors through the ball ratio,
and the ADR factor `σ(P(z,r))/r^k` lies in `[c, C]`. -/
theorem b2small_densityRatio_factor {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)}
    {σ : Measure (Space n)} (hΓ : IsADRCarrier k c C Γ σ) (μ : Measure (Space n))
    {z : Space n} (hz : z ∈ Γ) {r : ℝ} (hr : 0 < r) :
    densityRatio μ k z r = (μ (Metric.ball z r) / σ (Metric.ball z r)) *
        (σ (Metric.ball z r) / ENNReal.ofReal (r ^ k)) ∧
      ENNReal.ofReal c ≤ σ (Metric.ball z r) / ENNReal.ofReal (r ^ k) ∧
      σ (Metric.ball z r) / ENNReal.ofReal (r ^ k) ≤ ENNReal.ofReal C := by
  have hx0 : ENNReal.ofReal (r ^ k) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hr k)).ne'
  have hxt : ENNReal.ofReal (r ^ k) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlow : ENNReal.ofReal c * ENNReal.ofReal (r ^ k) ≤ σ (Metric.ball z r) := by
    rw [← ENNReal.ofReal_mul hΓ.lower_pos.le]
    exact hΓ.lower z hz r hr
  have hup : σ (Metric.ball z r) ≤ ENNReal.ofReal C * ENNReal.ofReal (r ^ k) := by
    rw [← ENNReal.ofReal_mul hΓ.upper_pos.le]
    exact hΓ.upper z hz r hr
  have hs0 : σ (Metric.ball z r) ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.2 hΓ.lower_pos).ne' hx0) hlow).ne'
  have hst : σ (Metric.ball z r) ≠ ⊤ :=
    (lt_of_le_of_lt hup (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).ne
  refine ⟨?_, (ENNReal.le_div_iff_mul_le (Or.inl hx0) (Or.inl hxt)).2 hlow,
    ENNReal.div_le_of_le_mul hup⟩
  rw [densityRatio, ← ENNReal.ofReal_pow hr.le]
  exact b2small_div_eq_div_mul_div _ hs0 hst _

/-- A positive finite limit of the ratios `μ(P(z,r))/σ(P(z,r))` at a carrier point `z` gives
positive lower and finite upper `k`-density of `μ` at `z`. -/
theorem b2_density_of_ratio_proof :
    ∀ n : ℕ, 1 ≤ n → ∀ (k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
      IsADRCarrier k c C Γ σ → ∀ (μ : Measure (Space n)) (z : Space n), z ∈ Γ →
      ∀ f : ℝ≥0∞,
        Tendsto (fun r : ℝ => μ (Metric.ball z r) / σ (Metric.ball z r)) (𝓝[>] (0 : ℝ))
          (𝓝 f) →
        0 < f → f < ⊤ → 0 < lowerDensity μ k z ∧ upperDensity μ k z < ⊤ := by
  intro n _ k c C Γ σ hΓ μ z hz f hf hf0 hftop
  have hf0' : f ≠ 0 := hf0.ne'
  have hft' : f ≠ ⊤ := hftop.ne
  have hlo : ∀ᶠ r in 𝓝[>] (0 : ℝ), f / 2 < μ (Metric.ball z r) / σ (Metric.ball z r) :=
    hf.eventually (lt_mem_nhds (ENNReal.half_lt_self hf0' hft'))
  have hhi : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (Metric.ball z r) / σ (Metric.ball z r) < f + 1 :=
    hf.eventually (gt_mem_nhds (ENNReal.lt_add_right hft' one_ne_zero))
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
  unfold lowerDensity upperDensity
  refine ⟨lt_of_lt_of_le (b := f / 2 * ENNReal.ofReal c)
      (ENNReal.mul_pos (ENNReal.half_pos hf0').ne' (ENNReal.ofReal_pos.2 hΓ.lower_pos).ne')
      (le_liminf_of_le (by isBoundedDefault) ?_),
    lt_of_le_of_lt (b := (f + 1) * ENNReal.ofReal C) (limsup_le_of_le (by isBoundedDefault) ?_)
      (ENNReal.mul_lt_top (ENNReal.add_lt_top.2 ⟨hftop, ENNReal.one_lt_top⟩)
        ENNReal.ofReal_lt_top)⟩
  · filter_upwards [hlo, hpos] with r h1 h2
    obtain ⟨he, hl, -⟩ := b2small_densityRatio_factor hΓ μ hz h2
    rw [he]
    exact mul_le_mul' h1.le hl
  · filter_upwards [hhi, hpos] with r h1 h2
    obtain ⟨he, -, hu⟩ := b2small_densityRatio_factor hΓ μ hz h2
    rw [he]
    exact mul_le_mul' h1.le hu

end ParabolicRectifiability.Characterization
