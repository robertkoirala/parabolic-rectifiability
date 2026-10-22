import ParabolicRectifiability.BetaP.Proofs.Corollaries.GraphEnhancement
import ParabolicRectifiability.BetaP.Proofs.Corollaries.WitnessRows
import ParabolicRectifiability.Examples.Statements.DensityExamples

/-! # Integrated rates and sharp amplitude powers

* Rates: Chebyshev (with the measurability law) gives the threshold at `M` with allowance
  `ℰ/M`; the localized graph-enhanced support theorem at `(q,R)` gives the loss
  `C M^{p/2} R^k + ℰ/M` (resp. `C M R^k + 𝒯/M`); the choice `M = (ℰ/R^k)^{2/(p+2)}`
  (resp. `M = (𝒯/R^k)^{1/2}`) gives exactly `(C+1) R^{2k/(p+2)} ℰ^{p/(p+2)}`
  (resp. `(C+1) R^{k/2} 𝒯^{1/2}`); zero energy uses the exact zero threshold (`M = Γ = 0`).
* Sharpness: for `μ_c = c ω`, every admissible good measure vanishes (the diffuse
  statement `Examples.DiffuseTestStatement`: `σ`-finite `H_P^k` sets are `μ_c`-null), so the
  remainder is `c ω(P(0,1))`, while the integrated energies scale by `c^{1+2/p}` and `c^2`
  (Foundations amplitude law); positivity and finiteness of the base energies is
  `diffuse_betaP_integratedEnergy`. A uniform bound `c V ≤ A c^α` for all `c > 0` forces `α = 1`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## Chebyshev and the exact zero threshold -/

theorem measure_inter_lt_le_ofReal_div {n : ℕ} {μ : Measure (Space n)} {f : Space n → ℝ≥0∞}
    (hf : Measurable f) {A : Set (Space n)} {E M : ℝ} (hM : 0 < M)
    (hint : ∫⁻ z in A, f z ∂μ = ENNReal.ofReal E) :
    μ (A ∩ {z | ENNReal.ofReal M < f z}) ≤ ENNReal.ofReal (E / M) := by
  have h1 := mul_meas_ge_le_lintegral₀ (μ := μ.restrict A) hf.aemeasurable (ENNReal.ofReal M)
  rw [hint, Measure.restrict_apply (measurableSet_le measurable_const hf)] at h1
  have hM' : ENNReal.ofReal M ≠ 0 := (ENNReal.ofReal_pos.mpr hM).ne'
  calc μ (A ∩ {z | ENNReal.ofReal M < f z}) ≤ μ ({z | ENNReal.ofReal M ≤ f z} ∩ A) :=
        measure_mono fun z hz => ⟨show ENNReal.ofReal M ≤ f z from
          le_of_lt (show ENNReal.ofReal M < f z from hz.2), hz.1⟩
    _ ≤ ENNReal.ofReal E / ENNReal.ofReal M := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hM') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact h1
    _ = ENNReal.ofReal (E / M) := (ENNReal.ofReal_div_of_pos hM).symm

theorem measure_inter_pos_eq_zero {n : ℕ} {μ : Measure (Space n)} {f : Space n → ℝ≥0∞}
    (hf : Measurable f) {A : Set (Space n)} (hA : MeasurableSet A)
    (hint : ∫⁻ z in A, f z ∂μ = 0) : μ (A ∩ {z | ENNReal.ofReal 0 < f z}) = 0 := by
  rw [lintegral_eq_zero_iff hf] at hint
  have h := ae_iff.mp hint
  rw [Measure.restrict_apply' hA] at h
  have hsub : A ∩ {z | ENNReal.ofReal 0 < f z} ⊆
      {a | ¬f a = (0 : Space n → ℝ≥0∞) a} ∩ A := by
    intro z hz
    have hz2 : 0 < f z := by simpa using hz.2
    exact ⟨hz2.ne', hz.1⟩
  exact measure_mono_null hsub h

/-! ## The exponent arithmetic -/

/-- With `θ + β = 1`: `x (E/x)^θ = E^θ x^β` and `E/(E/x)^β = E^θ x^β`. -/
theorem rpow_rate_identity {x E θ β : ℝ} (hx : 0 < x) (hE : 0 < E) (hθβ : θ + β = 1) :
    x * (E / x) ^ θ = E ^ θ * x ^ β ∧ E / (E / x) ^ β = E ^ θ * x ^ β := by
  have hxθβ : x ^ θ * x ^ β = x := by rw [← Real.rpow_add hx, hθβ, Real.rpow_one]
  have hEθβ : E ^ θ * E ^ β = E := by rw [← Real.rpow_add hE, hθβ, Real.rpow_one]
  have hxθ : x ^ θ ≠ 0 := (Real.rpow_pos_of_pos hx θ).ne'
  have hxβ : x ^ β ≠ 0 := (Real.rpow_pos_of_pos hx β).ne'
  have hEβ : E ^ β ≠ 0 := (Real.rpow_pos_of_pos hE β).ne'
  constructor
  · rw [Real.div_rpow hE.le hx.le]
    calc x * (E ^ θ / x ^ θ) = (x ^ θ * x ^ β) * (E ^ θ / x ^ θ) := by rw [hxθβ]
      _ = E ^ θ * x ^ β * (x ^ θ / x ^ θ) := by ring
      _ = E ^ θ * x ^ β := by rw [div_self hxθ, mul_one]
  · rw [Real.div_rpow hE.le hx.le]
    calc E / (E ^ β / x ^ β) = (E ^ θ * E ^ β) / (E ^ β / x ^ β) := by rw [hEθβ]
      _ = E ^ θ * x ^ β * (E ^ β / E ^ β) := by field_simp
      _ = E ^ θ * x ^ β := by rw [div_self hEβ, mul_one]

theorem rate_identity_S {CG E R p : ℝ} (k : ℕ) (hE : 0 < E) (hR : 0 < R) (hp : 0 < p) :
    CG * ((E / R ^ k) ^ (2 / (p + 2))) ^ (p / 2) * R ^ k + E / (E / R ^ k) ^ (2 / (p + 2)) =
      (CG + 1) * R ^ (2 * (k : ℝ) / (p + 2)) * E ^ (p / (p + 2)) := by
  have hx : 0 < R ^ k := pow_pos hR k
  have hp2 : p + 2 ≠ 0 := by linarith
  have h21 : 2 / (p + 2) * (p / 2) = p / (p + 2) := by field_simp
  have hθβ : p / (p + 2) + 2 / (p + 2) = 1 := by field_simp
  have hpow : (R ^ k) ^ (2 / (p + 2)) = R ^ (2 * (k : ℝ) / (p + 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 1
    ring
  obtain ⟨h1, h2⟩ := rpow_rate_identity hx hE hθβ
  rw [← Real.rpow_mul (div_pos hE hx).le, h21]
  calc CG * (E / R ^ k) ^ (p / (p + 2)) * R ^ k + E / (E / R ^ k) ^ (2 / (p + 2))
      = CG * (R ^ k * (E / R ^ k) ^ (p / (p + 2))) + E / (E / R ^ k) ^ (2 / (p + 2)) := by ring
    _ = (CG + 1) * R ^ (2 * (k : ℝ) / (p + 2)) * E ^ (p / (p + 2)) := by
      rw [h1, h2, hpow]
      ring

theorem rate_identity_T {CG E R : ℝ} (k : ℕ) (hE : 0 < E) (hR : 0 < R) :
    CG * (E / R ^ k) ^ (1 / 2 : ℝ) * R ^ k + E / (E / R ^ k) ^ (1 / 2 : ℝ) =
      (CG + 1) * R ^ ((k : ℝ) / 2) * E ^ (1 / 2 : ℝ) := by
  have hx : 0 < R ^ k := pow_pos hR k
  have hθβ : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have hpow : (R ^ k) ^ (1 / 2 : ℝ) = R ^ ((k : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 1
    ring
  obtain ⟨h1, h2⟩ := rpow_rate_identity hx hE hθβ
  calc CG * (E / R ^ k) ^ (1 / 2 : ℝ) * R ^ k + E / (E / R ^ k) ^ (1 / 2 : ℝ)
      = CG * (R ^ k * (E / R ^ k) ^ (1 / 2 : ℝ)) + E / (E / R ^ k) ^ (1 / 2 : ℝ) := by ring
    _ = (CG + 1) * R ^ ((k : ℝ) / 2) * E ^ (1 / 2 : ℝ) := by
      rw [h1, h2, hpow]
      ring

/-! ## Integrated rates -/

/-- Integrated rates from the graph-enhanced support theorem (localized clause), Chebyshev and
the choice of `M`. -/
theorem betaPIntegratedRate_of_graphEnhancement (hG : BetaPGraphEnhancementStatement) :
    BetaPIntegratedRateStatement := by
  intro n hn p hp
  obtain ⟨CG, hCG, hGn⟩ := hG n hn p hp
  refine ⟨CG + 1, by linarith, ?_⟩
  intro k hk hkn T hT μ hμ hreg q R hR
  obtain ⟨-, hloc, -⟩ := hGn k hk hkn T hT μ hμ hreg
  obtain ⟨-, hmeas⟩ := betaPowMeasurability_law n hn k hk hkn T hT μ hμ hreg p hp
  have hmS := (hmeas (2 * R) (by positivity)).1
  have hmT := (hmeas (2 * R) (by positivity)).2
  have hCle : CG ≤ CG + 1 := by linarith
  have hx : 0 < R ^ k := pow_pos hR k
  refine ⟨fun hp2 hfin => ?_, fun hp2 hfin => ?_⟩
  · have hEeq : integratedEnergyS μ k T p q R =
        ENNReal.ofReal (integratedEnergyS μ k T p q R).toReal :=
      (ENNReal.ofReal_toReal hfin.ne).symm
    rcases (ENNReal.toReal_nonneg : (0 : ℝ) ≤ (integratedEnergyS μ k T p q R).toReal).eq_or_lt
      with hE0 | hEpos
    · have hzero : ∫⁻ z in Metric.ball q R, energyS μ k T p (2 * R) z ∂μ = 0 := by
        change integratedEnergyS μ k T p q R = 0
        rw [hEeq, ← hE0, ENNReal.ofReal_zero]
      have hthr := measure_inter_pos_eq_zero hmS measurableSet_ball hzero
      obtain ⟨μplus, μH, μV, hD, hcost⟩ :=
        (hloc q R hR 0 0 le_rfl le_rfl).1 hp2 (by rw [hthr]; exact zero_le)
      refine ⟨μplus, μH, μV, hD.mono hCle hR.le ?_, costBounds_mono hcost hCle hR.le⟩
      rw [← hE0, Real.zero_rpow (by positivity : p / 2 ≠ 0),
        Real.zero_rpow (div_pos hp (by linarith)).ne']
      simp
    · have hMpos : 0 < ((integratedEnergyS μ k T p q R).toReal / R ^ k) ^ (2 / (p + 2)) :=
        Real.rpow_pos_of_pos (div_pos hEpos hx) _
      have hthr := measure_inter_lt_le_ofReal_div (A := Metric.ball q R) hmS hMpos hEeq
      obtain ⟨μplus, μH, μV, hD, hcost⟩ := (hloc q R hR _ _ hMpos.le
        (div_nonneg hEpos.le hMpos.le)).1 hp2 hthr
      exact ⟨μplus, μH, μV, hD.mono hCle hR.le (le_of_eq (rate_identity_S k hEpos hR hp)),
        costBounds_mono hcost hCle hR.le⟩
  · have hEeq : integratedEnergyT μ k T p q R =
        ENNReal.ofReal (integratedEnergyT μ k T p q R).toReal :=
      (ENNReal.ofReal_toReal hfin.ne).symm
    rcases (ENNReal.toReal_nonneg : (0 : ℝ) ≤ (integratedEnergyT μ k T p q R).toReal).eq_or_lt
      with hE0 | hEpos
    · have hzero : ∫⁻ z in Metric.ball q R, energyT μ k T p (2 * R) z ∂μ = 0 := by
        change integratedEnergyT μ k T p q R = 0
        rw [hEeq, ← hE0, ENNReal.ofReal_zero]
      have hthr := measure_inter_pos_eq_zero hmT measurableSet_ball hzero
      obtain ⟨μplus, μH, μV, hD, hcost⟩ :=
        (hloc q R hR 0 0 le_rfl le_rfl).2 hp2 (by rw [hthr]; exact zero_le)
      refine ⟨μplus, μH, μV, hD.mono hCle hR.le ?_, costBounds_mono hcost hCle hR.le⟩
      rw [← hE0, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      simp
    · have hMpos : 0 < ((integratedEnergyT μ k T p q R).toReal / R ^ k) ^ (1 / 2 : ℝ) :=
        Real.rpow_pos_of_pos (div_pos hEpos hx) _
      have hthr := measure_inter_lt_le_ofReal_div (A := Metric.ball q R) hmT hMpos hEeq
      obtain ⟨μplus, μH, μV, hD, hcost⟩ := (hloc q R hR _ _ hMpos.le
        (div_nonneg hEpos.le hMpos.le)).2 hp2 hthr
      exact ⟨μplus, μH, μV, hD.mono hCle hR.le (le_of_eq (rate_identity_T k hEpos hR)),
        costBounds_mono hcost hCle hR.le⟩

/-- **Integrated rates.** Inputs: those of `betaPGraphEnhancement_of_providers`, together with
the measurability law `betaPowMeasurability_law`. -/
theorem betaPIntegratedRate_of_providers (hMT1 : Enhancements.RectifiableReifenbergTheoremStatement)
    (hAmb : AmbientLocalCoreStatement) (hB2 : BetaPowTwoStatement)
    (hFH : Characterization.FiniteHausdorffCriterionStatement)
    (hTR : Characterization.TypedRefinementSetStatement)
    (hFC : Enhancements.FixedCarrierGraphDomainStatement) :
    BetaPIntegratedRateStatement :=
  betaPIntegratedRate_of_graphEnhancement
    (betaPGraphEnhancement_of_providers hMT1 hAmb hB2 hFH hTR hFC)

/-! ## Sharp amplitude powers -/

/-- A bound `c V ≤ A c^α` for every `c > 0`, with `V > 0`, forces `α = 1`. -/
theorem exponent_eq_one_of_forall_le {V A α : ℝ} (hV : 0 < V)
    (h : ∀ c : ℝ, 0 < c → c * V ≤ A * c ^ α) : α = 1 := by
  by_contra hα
  have h1α : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  have hKpos : 0 < |A| / V + 1 := by positivity
  have hcpos : 0 < (|A| / V + 1) ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hKpos _
  have hc1 : ((|A| / V + 1) ^ (1 / (1 - α))) ^ (1 - α) = |A| / V + 1 := by
    rw [← Real.rpow_mul hKpos.le, one_div_mul_cancel h1α, Real.rpow_one]
  set c := (|A| / V + 1) ^ (1 / (1 - α)) with hc
  have hcα : 0 < c ^ α := Real.rpow_pos_of_pos hcpos α
  have key : (|A| / V + 1) * V * c ^ α ≤ A * c ^ α := by
    calc (|A| / V + 1) * V * c ^ α = c ^ (1 - α) * c ^ α * V := by rw [hc1]; ring
      _ = c * V := by rw [← Real.rpow_add hcpos, sub_add_cancel, Real.rpow_one]
      _ ≤ A * c ^ α := h c hcpos
  have h2 : (|A| / V + 1) * V ≤ A := le_of_mul_le_mul_right key hcα
  have h3 : (|A| / V + 1) * V = |A| + V := by field_simp
  linarith [le_abs_self A]

/-- In a nonnegative decomposition of `c ω`, a good measure carried by a countable union of
finite-`H_P^k` sets vanishes (the diffuse statement, `σ`-finite nullity clause). -/
theorem diffuse_good_eq_zero (hDiff : Examples.DiffuseTestStatement) {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hkn : k < n + 2) {c : ℝ} (hc : 0 < c) {μplus μG : Measure (Space n)}
    {F : ℕ → Set (Space n)}
    (heq : ENNReal.ofReal c • (parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4)) =
      μplus + μG)
    (hF : ∀ i, hausdorffP n k (F i) < ⊤) (hG : μG (⋃ i, F i)ᶜ = 0) : μG = 0 := by
  obtain ⟨Cd, κ, -, -, hd⟩ := hDiff n hn k hk hkn
  have hnull : (ENNReal.ofReal c • (parabolicVolume n).restrict
      (Metric.ball (point 0 0) (1 / 4))) (⋃ i, F i) = 0 := (hd c hc).2.2.2.2.1 F hF
  have hle : μG ≤ μplus + μG := Measure.le_add_left le_rfl
  have h2 : (μplus + μG) (⋃ i, F i) = 0 := by rw [← heq]; exact hnull
  have h1 : μG (⋃ i, F i) = 0 :=
    nonpos_iff_eq_zero.mp ((Measure.le_iff'.1 hle _).trans h2.le)
  rw [← Measure.measure_univ_eq_zero]
  exact measure_mono_null (fun z _ => by
    by_cases hz : z ∈ ⋃ i, F i
    · exact Or.inl hz
    · exact Or.inr hz) (measure_union_null h1 hG)

/-- The diffuse witness has positive finite mass in `P(0,1)`. -/
theorem diffuse_unit_mass (n : ℕ) :
    0 < ((parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))
      (Metric.ball (point 0 0) 1)).toReal := by
  rw [Measure.restrict_apply measurableSet_ball,
    inter_eq_right.mpr (Metric.ball_subset_ball (by norm_num)),
    parabolicVolume_ball _ _ (by norm_num)]
  refine ENNReal.toReal_pos ?_ ?_
  · exact mul_ne_zero (mul_ne_zero two_ne_zero (omega_pos n).ne')
      (pow_ne_zero _ (ENNReal.ofReal_pos.mpr (by norm_num)).ne')
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (omega_lt_top n).ne)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem integratedEnergyS_smul (hSmul : EnergyPowSmulStatement) {n : ℕ} (hn : 1 ≤ n) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n + 2) (T : FamilyKind) (ω : Measure (Space n)) {p : ℝ} (hp : 0 < p)
    {c : ℝ} (hc : 0 < c) (q : Space n) {R : ℝ} (hR : 0 < R) :
    integratedEnergyS (ENNReal.ofReal c • ω) k T p q R =
      ENNReal.ofReal c * (ENNReal.ofReal c ^ (2 / p) * integratedEnergyS ω k T p q R) := by
  unfold integratedEnergyS
  rw [Measure.restrict_smul, lintegral_smul_measure]
  congr 1
  rw [← lintegral_const_mul' _ _
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)]
  exact lintegral_congr fun z => (hSmul n hn k hk hkn T ω p hp c hc (2 * R) (by positivity) z).1

theorem integratedEnergyT_smul (hSmul : EnergyPowSmulStatement) {n : ℕ} (hn : 1 ≤ n) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n + 2) (T : FamilyKind) (ω : Measure (Space n)) {p : ℝ} (hp : 0 < p)
    {c : ℝ} (hc : 0 < c) (q : Space n) {R : ℝ} (hR : 0 < R) :
    integratedEnergyT (ENNReal.ofReal c • ω) k T p q R =
      ENNReal.ofReal c * (ENNReal.ofReal c * integratedEnergyT ω k T p q R) := by
  unfold integratedEnergyT
  rw [Measure.restrict_smul, lintegral_smul_measure]
  congr 1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_congr fun z => (hSmul n hn k hk hkn T ω p hp c hc (2 * R) (by positivity) z).2

/-- From a decomposition with the claimed remainder bound: `c V ≤ C X^θ`, where `V` is the
unit-ball mass of `ω` and `X` the actual integrated energy of `c ω`. -/
theorem diffuse_remainder_le (hDiff : Examples.DiffuseTestStatement) {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hkn : k < n + 2) {c C θ : ℝ} (hc : 0 < c) {X : ℝ≥0∞}
    {μplus μG : Measure (Space n)} {F : ℕ → Set (Space n)}
    (heq : ENNReal.ofReal c • (parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4)) =
      μplus + μG)
    (hF : ∀ i, hausdorffP n k (F i) < ⊤) (hG : μG (⋃ i, F i)ᶜ = 0)
    (hbound : μplus (Metric.ball (point 0 0) 1) ≤ ENNReal.ofReal (C * X.toReal ^ θ)) :
    c * ((parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))
      (Metric.ball (point 0 0) 1)).toReal ≤ C * X.toReal ^ θ := by
  have hG0 : μG = 0 := diffuse_good_eq_zero hDiff hn hk hkn hc heq hF hG
  rw [hG0, add_zero] at heq
  have hVpos := diffuse_unit_mass n
  have hVfin : (parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))
      (Metric.ball (point 0 0) 1) ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hVpos).2.ne
  rw [← heq, Measure.smul_apply, smul_eq_mul, ← ENNReal.ofReal_toReal hVfin,
    ← ENNReal.ofReal_mul hc.le] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff'.mp hbound).resolve_right
    (not_le.mpr (mul_pos hc hVpos))

theorem betaPSharpness_S (hSmul : EnergyPowSmulStatement) (hDiff : Examples.DiffuseTestStatement)
    {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k < n + 2) {T : FamilyKind}
    (hT : Nonempty (Models n k T)) {p : ℝ} (hp2 : 2 ≤ p) {C θ : ℝ} (hθ : θ ≠ p / (p + 2)) :
    ¬ ∀ c : ℝ, 0 < c →
      ∃ (μplus μG : Measure (Space n)) (F : ℕ → Set (Space n)),
        ENNReal.ofReal c • (parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4)) =
            μplus + μG ∧
          (∀ i, hausdorffP n k (F i) < ⊤) ∧ μG (⋃ i, F i)ᶜ = 0 ∧
          μplus (Metric.ball (point 0 0) 1) ≤ ENNReal.ofReal (C *
            (integratedEnergyS (ENNReal.ofReal c •
              (parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))) k T p
                (point 0 0) 1).toReal ^ θ) := by
  intro hall
  have hp : 0 < p := by linarith
  obtain ⟨⟨hI0, hItop⟩, -⟩ := diffuse_betaP_integratedEnergy n hn k hk hkn T hT p hp
  have hepos : 0 < (integratedEnergyS ((parabolicVolume n).restrict
      (Metric.ball (point 0 0) (1 / 4))) k T p (point 0 0) 1).toReal :=
    ENNReal.toReal_pos hI0.ne' hItop.ne
  have key : ∀ c : ℝ, 0 < c →
      c * ((parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))
        (Metric.ball (point 0 0) 1)).toReal ≤
      (C * (integratedEnergyS ((parabolicVolume n).restrict
        (Metric.ball (point 0 0) (1 / 4))) k T p (point 0 0) 1).toReal ^ θ) *
        c ^ ((1 + 2 / p) * θ) := by
    intro c hc
    obtain ⟨μplus, μG, F, heq, hF, hG, hbound⟩ := hall c hc
    have h2 := diffuse_remainder_le hDiff hn hk hkn hc heq hF hG hbound
    rw [integratedEnergyS_smul hSmul hn hk hkn.le T _ hp hc _ one_pos, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hc.le] at h2
    have hcc : c * c ^ (2 / p) = c ^ (1 + 2 / p) := by rw [Real.rpow_add hc, Real.rpow_one]
    rw [← mul_assoc, hcc, Real.mul_rpow (Real.rpow_nonneg hc.le _) hepos.le,
      ← Real.rpow_mul hc.le] at h2
    linarith
  have hα := exponent_eq_one_of_forall_le (diffuse_unit_mass n) key
  apply hθ
  have hpne : p ≠ 0 := hp.ne'
  have h4 : (p + 2) * θ = p := by
    have : (1 + 2 / p) * θ * p = 1 * p := by rw [hα]
    calc (p + 2) * θ = (1 + 2 / p) * θ * p := by field_simp
      _ = p := by rw [this, one_mul]
  rw [eq_div_iff (by linarith)]
  linarith

theorem betaPSharpness_T (hSmul : EnergyPowSmulStatement) (hDiff : Examples.DiffuseTestStatement)
    {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k < n + 2) {T : FamilyKind}
    (hT : Nonempty (Models n k T)) {p : ℝ} (hp : 0 < p) {C θ : ℝ} (hθ : θ ≠ 1 / 2) :
    ¬ ∀ c : ℝ, 0 < c →
      ∃ (μplus μG : Measure (Space n)) (F : ℕ → Set (Space n)),
        ENNReal.ofReal c • (parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4)) =
            μplus + μG ∧
          (∀ i, hausdorffP n k (F i) < ⊤) ∧ μG (⋃ i, F i)ᶜ = 0 ∧
          μplus (Metric.ball (point 0 0) 1) ≤ ENNReal.ofReal (C *
            (integratedEnergyT (ENNReal.ofReal c •
              (parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))) k T p
                (point 0 0) 1).toReal ^ θ) := by
  intro hall
  obtain ⟨-, ⟨hI0, hItop⟩⟩ := diffuse_betaP_integratedEnergy n hn k hk hkn T hT p hp
  have hepos : 0 < (integratedEnergyT ((parabolicVolume n).restrict
      (Metric.ball (point 0 0) (1 / 4))) k T p (point 0 0) 1).toReal :=
    ENNReal.toReal_pos hI0.ne' hItop.ne
  have key : ∀ c : ℝ, 0 < c →
      c * ((parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))
        (Metric.ball (point 0 0) 1)).toReal ≤
      (C * (integratedEnergyT ((parabolicVolume n).restrict
        (Metric.ball (point 0 0) (1 / 4))) k T p (point 0 0) 1).toReal ^ θ) *
        c ^ (2 * θ) := by
    intro c hc
    obtain ⟨μplus, μG, F, heq, hF, hG, hbound⟩ := hall c hc
    have h2 := diffuse_remainder_le hDiff hn hk hkn hc heq hF hG hbound
    rw [integratedEnergyT_smul hSmul hn hk hkn.le T _ hp hc _ one_pos, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] at h2
    have hcc : c * c = c ^ (2 : ℝ) := by rw [Real.rpow_two, sq]
    rw [← mul_assoc, hcc, Real.mul_rpow (Real.rpow_nonneg hc.le _) hepos.le,
      ← Real.rpow_mul hc.le] at h2
    linarith
  have hα := exponent_eq_one_of_forall_le (diffuse_unit_mass n) key
  exact hθ (by linarith)

/-- **Sharp amplitude powers.** Inputs: `EnergyPowSmulStatement` (amplitude laws) and
`DiffuseTestStatement` (`σ`-finite nullity of the diffuse witness), together with
`diffuse_betaP_integratedEnergy`. -/
theorem betaPIntegratedSharpness_of_providers (hSmul : EnergyPowSmulStatement)
    (hDiff : Examples.DiffuseTestStatement) : BetaPIntegratedSharpnessStatement :=
  fun _ hn _ hk hkn _ hT =>
    ⟨fun _ hp2 _ _ hθ => betaPSharpness_S hSmul hDiff hn hk hkn hT hp2 hθ,
      fun _ hp _ _ _ hθ => betaPSharpness_T hSmul hDiff hn hk hkn hT hp hθ⟩

end ParabolicRectifiability.BetaP
