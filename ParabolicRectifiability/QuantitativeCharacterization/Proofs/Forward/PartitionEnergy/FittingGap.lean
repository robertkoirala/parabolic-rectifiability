import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.TubeMass

/-! # Fitting gap

Proof of `d1a_fittingGap_proof : UpperRecenteringStatement → FittingGapStatement`, in
implication form: `UpperRecenteringStatement` is a hypothesis.

Route. Fix `δ = 1 / (2 C A)` with `C = d1atube_massConst n k ≥ 1`, so `0 < δ ≤ 1/2` and
`C A δ² ≤ A⁻¹ / 2`. On `P(z, r)` let `S` be the points whose two costs sum to `< (δ r)²`; the
tube estimate `d1atube_gap_mass` (imported, not re-proved) gives
`μ(S) ≤ C A δ² r^k ≤ A⁻¹ r^k / 2`. Lower ADR at the support point `z` gives
`μ(P(z, r)) ≥ A⁻¹ r^k`, so the complement `G = P(z, r) \ S` has mass `≥ A⁻¹ r^k / 2`; on `G`
the cost sum is `≥ (δ r)²` (Chebyshev). Hence
`fit μ H z r + fit μ V z r ≥ (δ r)² · A⁻¹ r^k / 2 = c r^{k+2}` with `c = δ² A⁻¹ / 2`.

Helpers carry the prefix `d1agap_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

/-- The tube-mass constant is at least one. -/
theorem d1agap_massConst_one_le (n k : ℕ) : 1 ≤ d1atube_massConst n k := by
  unfold d1atube_massConst d1atube_countConst
  have h1 : (1 : ℝ) ≤ (2 * (n : ℝ) + 4) ^ n :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have h2 : (1 : ℝ) ≤ 6 ^ k := one_le_pow₀ (by norm_num)
  nlinarith

/-- The scale `δ = 1 / (2 C A)` of the gap argument. -/
def d1agap_delta (n k : ℕ) (A : ℝ) : ℝ := 1 / (2 * d1atube_massConst n k * A)

/-- The gap constant `c = δ² A⁻¹ / 2`. -/
def d1agap_const (n k : ℕ) (A : ℝ) : ℝ := d1agap_delta n k A ^ 2 * A⁻¹ / 2

theorem d1agap_delta_pos (n k : ℕ) {A : ℝ} (hA : 1 ≤ A) : 0 < d1agap_delta n k A := by
  unfold d1agap_delta
  have := d1atube_massConst_pos n k
  have : 0 < A := by linarith
  positivity

theorem d1agap_delta_le (n k : ℕ) {A : ℝ} (hA : 1 ≤ A) : d1agap_delta n k A ≤ 1 / 2 := by
  unfold d1agap_delta
  have hC := d1agap_massConst_one_le n k
  have hCA : 1 ≤ d1atube_massConst n k * A := by nlinarith
  rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
  nlinarith

/-- `C A δ² ≤ A⁻¹ / 2`. -/
theorem d1agap_small (n k : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    d1atube_massConst n k * A * d1agap_delta n k A ^ 2 ≤ A⁻¹ / 2 := by
  unfold d1agap_delta
  have hC := d1agap_massConst_one_le n k
  have hA0 : 0 < A := by linarith
  set C := d1atube_massConst n k with hCdef
  have hC0 : 0 < C := by linarith
  have h : C * A * (1 / (2 * C * A)) ^ 2 = 1 / (4 * C * A) := by
    field_simp
    ring
  rw [h, div_le_div_iff₀ (by positivity) (by norm_num)]
  rw [show A⁻¹ * (4 * C * A) = 4 * C * (A⁻¹ * A) by ring, inv_mul_cancel₀ hA0.ne', mul_one]
  linarith

theorem d1agap_const_pos (n k : ℕ) {A : ℝ} (hA : 1 ≤ A) : 0 < d1agap_const n k A := by
  unfold d1agap_const
  have := d1agap_delta_pos n k hA
  have : 0 < A := by linarith
  positivity

/-- **The fitting gap for one ball** (the body of (3.5)). -/
theorem d1agap_gap {n k : ℕ} (hUR : UpperRecenteringStatement) {A : ℝ} (hA : 1 ≤ A)
    {μ : Measure (Space n)} {a : Space n} {ρ : ℝ} (hADR : LocalADR μ k A a ρ)
    {z : Space n} (hz : z ∈ μ.support) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball z (4 * r) ⊆ Metric.ball a ρ) (h4 : 4 * r ≤ ρ)
    (H : Models n k .horizontal) (V : Models n k .vertical) :
    ENNReal.ofReal (d1agap_const n k A * r ^ (k + 2)) ≤ fit μ H z r + fit μ V z r := by
  set δ := d1agap_delta n k A with hδdef
  have hδ : 0 < δ := d1agap_delta_pos n k hA
  have hδ2 : δ ≤ 1 / 2 := d1agap_delta_le n k hA
  have hA0 : 0 < A := by linarith
  set B : Set (Space n) := Metric.ball z r with hB
  set F : Space n → ℝ≥0∞ := fun w => modelCost H w + modelCost V w with hF
  have hFm : Measurable F := (measurable_modelCost H).add (measurable_modelCost V)
  set S : Set (Space n) := {w | w ∈ B ∧ F w < ENNReal.ofReal ((δ * r) ^ 2)} with hS
  set G : Set (Space n) := {w | w ∈ B ∧ ENNReal.ofReal ((δ * r) ^ 2) ≤ F w} with hG
  -- the tube mass
  have hSmass : μ S ≤ ENNReal.ofReal (d1atube_massConst n k * A * δ ^ 2 * r ^ k) :=
    d1atube_gap_mass hUR hA0.le hADR hr hball h4 hδ hδ2 H V S (fun w hw => hw.1)
      (fun w hw => hw.2)
  have hSmass' : μ S ≤ ENNReal.ofReal (A⁻¹ * r ^ k / 2) := by
    refine hSmass.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsm := d1agap_small n k hA
    have hrk : 0 ≤ r ^ k := pow_nonneg hr.le _
    calc d1atube_massConst n k * A * δ ^ 2 * r ^ k
        = (d1atube_massConst n k * A * δ ^ 2) * r ^ k := by ring
      _ ≤ (A⁻¹ / 2) * r ^ k := mul_le_mul_of_nonneg_right hsm hrk
      _ = A⁻¹ * r ^ k / 2 := by ring
  -- lower ADR at the support point `z`
  have hzB : z ∈ μ.support ∩ Metric.ball a ρ :=
    ⟨hz, hball (Metric.mem_ball_self (by linarith))⟩
  have hlow : ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ B := (hADR z hzB r hr (by linarith)).1
  -- splitting the ball
  have hsplit : B ⊆ S ∪ G := by
    intro w hw
    rcases lt_or_ge (F w) (ENNReal.ofReal ((δ * r) ^ 2)) with h | h
    · exact Or.inl ⟨hw, h⟩
    · exact Or.inr ⟨hw, h⟩
  have hBSG : μ B ≤ μ S + μ G := (measure_mono hsplit).trans (measure_union_le S G)
  have hGmass : ENNReal.ofReal (A⁻¹ * r ^ k / 2) ≤ μ G := by
    have hhalf : ENNReal.ofReal (A⁻¹ * r ^ k) =
        ENNReal.ofReal (A⁻¹ * r ^ k / 2) + ENNReal.ofReal (A⁻¹ * r ^ k / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have h := (hlow.trans hBSG).trans (add_le_add hSmass' le_rfl)
    rw [hhalf] at h
    exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).1 h
  -- Chebyshev on `G`
  have hGmeas : MeasurableSet G :=
    measurableSet_ball.inter (measurableSet_le measurable_const hFm)
  have hcheb : ENNReal.ofReal ((δ * r) ^ 2) * μ G ≤ ∫⁻ w in B, F w ∂μ := by
    calc ENNReal.ofReal ((δ * r) ^ 2) * μ G
        = ∫⁻ _w in G, ENNReal.ofReal ((δ * r) ^ 2) ∂μ := (setLIntegral_const G _).symm
      _ ≤ ∫⁻ w in G, F w ∂μ := setLIntegral_mono' hGmeas (fun w hw => hw.2)
      _ ≤ ∫⁻ w in B, F w ∂μ := lintegral_mono_set (fun w hw => hw.1)
  have hsum : ∫⁻ w in B, F w ∂μ = fit μ H z r + fit μ V z r :=
    lintegral_add_left (measurable_modelCost H) _
  -- assembly
  have hconst : d1agap_const n k A * r ^ (k + 2) = (δ * r) ^ 2 * (A⁻¹ * r ^ k / 2) := by
    rw [hδdef]
    unfold d1agap_const
    ring
  calc ENNReal.ofReal (d1agap_const n k A * r ^ (k + 2))
      = ENNReal.ofReal ((δ * r) ^ 2) * ENNReal.ofReal (A⁻¹ * r ^ k / 2) := by
        rw [hconst, ENNReal.ofReal_mul (sq_nonneg _)]
    _ ≤ ENNReal.ofReal ((δ * r) ^ 2) * μ G := by gcongr
    _ ≤ ∫⁻ w in B, F w ∂μ := hcheb
    _ = fit μ H z r + fit μ V z r := hsum

/-- **Fitting gap** (`UpperRecenteringStatement → FittingGapStatement`);
`c = δ² A⁻¹ / 2` with `δ = 1/(2 C A)`. -/
theorem d1a_fittingGap_proof : UpperRecenteringStatement → FittingGapStatement := by
  intro hUR n _hn k _hk _hkn A hA
  refine ⟨d1agap_const n k A, d1agap_const_pos n k hA, ?_⟩
  intro μ a ρ hADR z hz r hr hball h4 H V
  exact d1agap_gap hUR hA hADR hz hr hball h4 H V

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
