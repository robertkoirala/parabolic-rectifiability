import ParabolicRectifiability.Enhancements.Assembly.GraphDomains
import ParabolicRectifiability.Enhancements.Statements.ScalingRates
import ParabolicRectifiability.Foundations.Statements.Measurability

/-! # The scaling contract and the power and gauge rates

Main theorems:

* `scaling_identities_of_providers : SquareEnergyRescalingStatement →
  ScalingIdentitiesStatement` — the beta identity is `betaSq_rescaledSource`
  (at `y = F⁻¹(F y)`); the energy identity is `SquareEnergyRescalingStatement` at endpoint `2`;
* `scaled_rectifiable_reifenberg_of_providers : CompactBridgeCoverStatement →
  SquareEnergyRescalingStatement → ScaledRectifiableReifenbergStatement` — apply the unit graph
  enhancement to `ν = R^{-k} (F^{-1})_# μ` (locally Radon) with
  allowance `R^{-k} Γ` (threshold transport by the energy identity), and pull back by
  `isLocalEnhancedDecomposition_of_rescaledSource`;
* `power_rate_of_providers`, `gauge_rate_of_providers` (same hypotheses) — the scaled
  property with the same constant `C₀`, a Markov bound and the choice of
  threshold; zero energy through `M = Γ = 0`
  by a countable union of Markov bounds; the ambient clause from the unit ambient clause
  pulled back by `isLocalEnhancedDecomposition_of_rescaledSource`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Enhancements

open ParabolicRectifiability.Foundations

/-! ## The scaling identities -/

/-- **Scaling identities.** The beta identity is `betaSq_rescaledSource`; the
energy identity is `SquareEnergyRescalingStatement` at endpoint `A = 2`. -/
theorem scaling_identities_of_providers (hER : SquareEnergyRescalingStatement) :
    ScalingIdentitiesStatement := by
  intro n hn k hk hkn μ _ _ a R hR T _
  refine ⟨fun y s hs => ?_, fun y => ?_⟩
  · have h := betaSq_rescaledSource μ k T a R hR ((similarity a R hR).symm y) hs
    rwa [Homeomorph.apply_symm_apply] at h
  · rw [hER n hn k hk hkn T μ a R hR 2 two_pos y, mul_comm R 2]

/-! ## The rescaled source -/

/-- Evaluation of `ν = R^{-k} (F^{-1})_# μ` on any set. -/
theorem rescaledSource_apply {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (a : Space n) (R : ℝ)
    (hR : 0 < R) (S : Set (Space n)) :
    rescaledSource μ k a R hR S = (ENNReal.ofReal R)⁻¹ ^ k * μ (similarity a R hR ⁻¹' S) := by
  rw [rescaledSource, Measure.smul_apply, smul_eq_mul]
  congr 1
  exact (similarity a R hR).toMeasurableEquiv.map_apply S

/-- The rescaled source of an inner regular measure is inner regular. -/
theorem innerRegular_rescaledSource {n : ℕ} (μ : Measure (Space n)) (hreg : μ.InnerRegular)
    (k : ℕ) (a : Space n) (R : ℝ) (hR : 0 < R) : (rescaledSource μ k a R hR).InnerRegular := by
  have : (μ.map (similarity a R hR)).InnerRegular := Measure.InnerRegular.map (similarity a R hR)
  unfold rescaledSource
  infer_instance

/-- The rescaled source of a locally finite measure is finite on compacts. -/
theorem isFiniteMeasureOnCompacts_rescaledSource {n : ℕ} (μ : Measure (Space n))
    (hμ : IsFiniteMeasureOnCompacts μ) (k : ℕ) (a : Space n) (R : ℝ) (hR : 0 < R) :
    IsFiniteMeasureOnCompacts (rescaledSource μ k a R hR) :=
  inferInstance

/-- The similarity `F^{-1}` maps `a` to the origin. -/
theorem similarity_self {n : ℕ} (a : Space n) (R : ℝ) (hR : 0 < R) :
    similarity a R hR a = point 0 0 := by
  simp [similarity_apply]

/-- The similarity `F^{-1}` maps `P(a,R)` onto `P(0,1)`. -/
theorem similarity_mem_unit_ball_iff {n : ℕ} (a : Space n) (R : ℝ) (hR : 0 < R)
    (w : Space n) : similarity a R hR w ∈ Metric.ball (point 0 0) 1 ↔ w ∈ Metric.ball a R := by
  have h := Set.ext_iff.mp (preimage_similarity_ball a R hR a 1) w
  rw [similarity_self, mul_one] at h
  exact h

/-- Threshold transport: the exceptional mass of `ν` on
`P(0,1)` is `R^{-k}` times that of `μ` on `P(a,R)`, by the energy identity. -/
theorem rescaledSource_threshold (hER : SquareEnergyRescalingStatement) {n k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2) (μ : Measure (Space n)) (a : Space n)
    (R : ℝ) (hR : 0 < R) (T : FamilyKind) (M Γ : ℝ)
    (hbad : μ (Metric.ball a R ∩ {z | ENNReal.ofReal M < squareEnergy μ k T (2 * R) z}) ≤
      ENNReal.ofReal Γ) :
    rescaledSource μ k a R hR (Metric.ball (point 0 0) 1 ∩
        {z | ENNReal.ofReal M < squareEnergy (rescaledSource μ k a R hR) k T 2 z}) ≤
      ENNReal.ofReal (Γ / R ^ k) := by
  rw [rescaledSource_apply]
  have hpre : similarity a R hR ⁻¹' (Metric.ball (point 0 0) 1 ∩
        {z | ENNReal.ofReal M < squareEnergy (rescaledSource μ k a R hR) k T 2 z}) =
      Metric.ball a R ∩ {z | ENNReal.ofReal M < squareEnergy μ k T (2 * R) z} := by
    ext w
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq]
    rw [hER n hn k hk hkn T μ a R hR 2 two_pos, Homeomorph.symm_apply_apply, mul_comm R 2,
      similarity_mem_unit_ball_iff]
  rw [hpre]
  calc (ENNReal.ofReal R)⁻¹ ^ k *
        μ (Metric.ball a R ∩ {z | ENNReal.ofReal M < squareEnergy μ k T (2 * R) z})
      ≤ (ENNReal.ofReal R)⁻¹ ^ k * ENNReal.ofReal Γ := mul_le_mul' le_rfl hbad
    _ = ENNReal.ofReal (Γ / R ^ k) := by
      rw [ENNReal.ofReal_div_of_pos (pow_pos hR k), ENNReal.ofReal_pow hR.le, div_eq_mul_inv,
        ← ENNReal.inv_pow, mul_comm]

/-! ## The scaled threshold decomposition and the local ambient clause -/

/-- From the unit graph enhancement: the scaled threshold property and the local ambient
clause, with the same constant `C`. The pull-back is
`isLocalEnhancedDecomposition_of_rescaledSource`. -/
theorem scaled_and_ambient_of_graphEnhanced (hER : SquareEnergyRescalingStatement)
    (hGE : GraphEnhancedRectifiableReifenbergStatement) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ScaledThresholdProperty n C ∧
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ (a : Space n) (R : ℝ), 0 < R →
        ∃ EH EV : Set (Space n), IsLocalEnhancedDecomposition (n + 2) .mixed C a R μ EH EV ∧
          μ.restrict (EH ∪ EV)ᶜ (Metric.ball a R) = 0 := by
  obtain ⟨C, hC, hmix, hfix, hamb⟩ := hGE n hn
  refine ⟨C, hC, ?_, ?_⟩
  · intro k hk hkn μ hμ hreg a R hR T hT M Γ hM hΓ hbad
    have hνc := isFiniteMeasureOnCompacts_rescaledSource μ hμ k a R hR
    have hνr := innerRegular_rescaledSource μ hreg k a R hR
    have hΓ' : 0 ≤ Γ / R ^ k := div_nonneg hΓ (pow_nonneg hR.le k)
    have hbadν := rescaledSource_threshold hER hn hk hkn μ a R hR T M Γ hbad
    obtain ⟨D, hD, hH, hV, hG⟩ : ∃ D : RetainedSets n,
        IsRectifiableReifenbergDecomposition k C M (Γ / R ^ k) (rescaledSource μ k a R hR) D ∧
        (T = .horizontal → D.verticalMeasure (rescaledSource μ k a R hR) = 0 ∧
          D.verticalSupport (rescaledSource μ k a R hR) = ∅) ∧
        (T = .vertical → D.horizontalMeasure (rescaledSource μ k a R hR) = 0 ∧
          D.horizontalSupport (rescaledSource μ k a R hR) = ∅) ∧
        ∀ ε δ : ℝ, 0 < ε → 0 < δ →
          HasScaledGraphDomainCover k (D.horizontalSupport (rescaledSource μ k a R hR))
            (D.verticalSupport (rescaledSource μ k a R hR)) C ε δ 1 := by
      cases T with
      | mixed =>
        obtain ⟨D, hD, hG⟩ := hmix k hk hkn _ hνc hνr M _ hM hΓ' hbadν
        exact ⟨D, hD, fun h => absurd h (by decide), fun h => absurd h (by decide), hG⟩
      | horizontal => exact hfix k hk hkn _ (by decide) hT _ hνc hνr M _ hM hΓ' hbadν
      | vertical => exact hfix k hk hkn _ (by decide) hT _ hνc hνr M _ hM hΓ' hbadν
    obtain ⟨hloc, hloss⟩ := isLocalEnhancedDecomposition_of_rescaledSource hn hk hkn μ hμ hreg
      a R hR T C D hD.horizontal_unavailable hD.vertical_unavailable hH hV hD.supports hG
    refine ⟨_, _, hloc, ?_⟩
    rw [hloss]
    have hRk : R ^ k ≠ 0 := (pow_pos hR k).ne'
    calc ENNReal.ofReal R ^ k *
          D.remainderMeasure (rescaledSource μ k a R hR) (Metric.ball (point 0 0) 1)
        ≤ ENNReal.ofReal R ^ k * ENNReal.ofReal (C * M + Γ / R ^ k) :=
          mul_le_mul' le_rfl hD.remainder_bound
      _ = ENNReal.ofReal (C * M * R ^ k + Γ) := by
        rw [← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (pow_nonneg hR.le k)]
        congr 1
        field_simp
  · intro μ hμ hreg a R hR
    obtain ⟨D, hD, hrem, hG⟩ := hamb (rescaledSource μ (n + 2) a R hR)
      (isFiniteMeasureOnCompacts_rescaledSource μ hμ (n + 2) a R hR)
      (innerRegular_rescaledSource μ hreg (n + 2) a R hR)
    obtain ⟨hloc, hloss⟩ := isLocalEnhancedDecomposition_of_rescaledSource hn (by omega) le_rfl
      μ hμ hreg a R hR .mixed C D hD.horizontal_unavailable hD.vertical_unavailable
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hD.supports hG
    exact ⟨_, _, hloc, by rw [hloss, hrem, mul_zero]⟩

/-- **Full scaling contract.** Hypotheses: `CompactBridgeCoverStatement` (through the parabolic rectifiable Reifenberg theorem)
and `SquareEnergyRescalingStatement`. -/
theorem scaled_rectifiable_reifenberg_of_providers (hbridge : CompactBridgeCoverStatement)
    (hER : SquareEnergyRescalingStatement) : ScaledRectifiableReifenbergStatement := by
  refine ⟨scaling_identities_of_providers hER, fun n hn => ?_⟩
  obtain ⟨C, hC, hS, -⟩ := scaled_and_ambient_of_graphEnhanced hER
    (graph_enhanced_rectifiable_reifenberg_of_providers hbridge) n hn
  exact ⟨C, hC, hS⟩

/-! ## The power-energy rate -/

/-- The real arithmetic of the power rate: with
`Θ = R^{kq/(q+1)} Λ^{1/(q+1)}` and the threshold `M = Θ / R^k = (Λ/R^k)^{1/(q+1)}`, both
`M R^k` and `Λ / M^q` equal `Θ`. -/
theorem power_rate_arith (C L R q Θ : ℝ) (hL : 0 < L) (hR : 0 < R) (hq : 0 < q) (k : ℕ)
    (hΘdef : Θ = R ^ ((k : ℝ) * q / (q + 1)) * L ^ (1 / (q + 1))) :
    0 < Θ / R ^ k ∧ C * (Θ / R ^ k) * R ^ k + L / (Θ / R ^ k) ^ q = (C + 1) * Θ := by
  have hΘ : 0 < Θ := hΘdef ▸ mul_pos (Real.rpow_pos_of_pos hR _) (Real.rpow_pos_of_pos hL _)
  have hRk : 0 < R ^ k := pow_pos hR k
  refine ⟨div_pos hΘ hRk, ?_⟩
  have hq1 : q + 1 ≠ 0 := by linarith
  have hpow : Θ ^ (q + 1) = R ^ ((k : ℝ) * q) * L := by
    rw [hΘdef, Real.mul_rpow (Real.rpow_nonneg hR.le _) (Real.rpow_nonneg hL.le _),
      ← Real.rpow_mul hR.le, ← Real.rpow_mul hL.le]
    congr 1
    · congr 1
      field_simp
    · rw [one_div, inv_mul_cancel₀ hq1, Real.rpow_one]
  have hMq : (Θ / R ^ k) ^ q = Θ ^ q / R ^ ((k : ℝ) * q) := by
    rw [Real.div_rpow hΘ.le hRk.le, ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
  have hΘq : 0 < Θ ^ q := Real.rpow_pos_of_pos hΘ q
  have key : L * R ^ ((k : ℝ) * q) = Θ ^ q * Θ := by
    rw [← Real.rpow_add_one hΘ.ne', hpow, mul_comm]
  rw [hMq, mul_assoc, div_mul_cancel₀ _ hRk.ne', div_div_eq_mul_div, key,
    mul_div_cancel_left₀ _ hΘq.ne']
  ring

/-- Zero integrated power energy makes the strict exceptional set at threshold `0` null,
by Markov at the thresholds `1/(m+1)` and a countable union. -/
theorem measure_pos_squareEnergy_eq_zero {n k : ℕ} (μ : Measure (Space n))
    (hμ : IsFiniteMeasureOnCompacts μ) (T : FamilyKind) (a : Space n) (R q : ℝ) (hq : 0 < q)
    (h0 : powerEnergy μ k T q a R = 0) :
    μ (Metric.ball a R ∩ {z | ENNReal.ofReal 0 < squareEnergy μ k T (2 * R) z}) = 0 := by
  have hsub : Metric.ball a R ∩ {z | ENNReal.ofReal 0 < squareEnergy μ k T (2 * R) z} ⊆
      ⋃ m : ℕ, Metric.ball a R ∩
        {z | ENNReal.ofReal (1 / ((m : ℝ) + 1)) < squareEnergy μ k T (2 * R) z} := by
    rintro z ⟨hz, hpos⟩
    obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
    have hr : 0 < r := by
      rcases hr0.lt_or_eq with h | h
      · exact h
      · rw [← h, ENNReal.ofReal_zero] at hr1
        exact absurd hr1 (lt_irrefl _)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
    exact mem_iUnion.mpr ⟨m, hz, ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hm).trans hr2⟩
  refine measure_mono_null hsub (measure_iUnion_null fun m => ?_)
  have hMpos : 0 < 1 / ((m : ℝ) + 1) := by positivity
  have h := measure_lt_squareEnergy_le_gaugeEnergy_div k μ hμ T a R (fun x => x ^ q)
    (ENNReal.monotone_rpow_of_nonneg hq.le) ENNReal.continuous_rpow_const.measurable
    (1 / ((m : ℝ) + 1)) (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hMpos) ENNReal.ofReal_ne_top)
    (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
  have h0' : gaugeEnergy (fun x => x ^ q) μ k T a R = 0 := h0
  rw [h0', ENNReal.zero_div] at h
  exact le_antisymm h zero_le

/-- The power rate from the scaled property with the same constant `C₀`. -/
theorem powerRateProperty_of_scaled {n : ℕ} {C₀ : ℝ} (hS : ScaledThresholdProperty n C₀)
    (hamb : ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ (a : Space n) (R : ℝ), 0 < R →
        ∃ EH EV : Set (Space n), IsLocalEnhancedDecomposition (n + 2) .mixed C₀ a R μ EH EV ∧
          μ.restrict (EH ∪ EV)ᶜ (Metric.ball a R) = 0) :
    PowerRateProperty n C₀ := by
  refine ⟨?_, hamb⟩
  intro k hk hkn μ hμ hreg a R hR T hT q hq hfin
  by_cases hΛ0 : powerEnergy μ k T q a R = 0
  · have hnull := measure_pos_squareEnergy_eq_zero μ hμ T a R q hq hΛ0
    obtain ⟨EH, EV, hloc, hloss⟩ := hS k hk hkn μ hμ hreg a R hR T hT 0 0 le_rfl le_rfl
      (by rw [hnull]; exact zero_le)
    have hzero : μ.restrict (EH ∪ EV)ᶜ (Metric.ball a R) = 0 := by
      refine le_antisymm (hloss.trans (le_of_eq ?_)) zero_le
      simp
    exact ⟨EH, EV, hloc, by rw [hzero]; exact zero_le, fun _ => hzero⟩
  · have hΛtop : powerEnergy μ k T q a R ≠ ⊤ := hfin.ne
    have hLpos : 0 < (powerEnergy μ k T q a R).toReal := ENNReal.toReal_pos hΛ0 hΛtop
    obtain ⟨hMpos, hident⟩ := power_rate_arith C₀ (powerEnergy μ k T q a R).toReal R q _
      hLpos hR hq k rfl
    set L := (powerEnergy μ k T q a R).toReal with hL
    set M := R ^ ((k : ℝ) * q / (q + 1)) * L ^ (1 / (q + 1)) / R ^ k with hMdef
    have hΓ : 0 ≤ L / M ^ q := div_nonneg hLpos.le (Real.rpow_nonneg hMpos.le q)
    have hmarkov := measure_lt_squareEnergy_le_gaugeEnergy_div k μ hμ T a R (fun x => x ^ q)
      (ENNReal.monotone_rpow_of_nonneg hq.le) ENNReal.continuous_rpow_const.measurable M
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hMpos) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
    have hbad : μ (Metric.ball a R ∩ {z | ENNReal.ofReal M < squareEnergy μ k T (2 * R) z}) ≤
        ENNReal.ofReal (L / M ^ q) := by
      refine hmarkov.trans_eq ?_
      change powerEnergy μ k T q a R / ENNReal.ofReal M ^ q = _
      rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hMpos q),
        ← ENNReal.ofReal_rpow_of_pos hMpos, hL, ENNReal.ofReal_toReal hΛtop]
    obtain ⟨EH, EV, hloc, hloss⟩ := hS k hk hkn μ hμ hreg a R hR T hT M (L / M ^ q)
      hMpos.le hΓ hbad
    refine ⟨EH, EV, hloc, hloss.trans (le_of_eq ?_), fun h => absurd h hΛ0⟩
    rw [hident]
    ring_nf

/-- **Power-energy rate.** The rate holds for the same constant `C₀` as the scaled threshold
property. Hypotheses: `CompactBridgeCoverStatement` and `SquareEnergyRescalingStatement`. -/
theorem power_rate_of_providers (hbridge : CompactBridgeCoverStatement)
    (hER : SquareEnergyRescalingStatement) : PowerRateStatement := by
  intro n hn
  obtain ⟨C, hC, hS, hamb⟩ := scaled_and_ambient_of_graphEnhanced hER
    (graph_enhanced_rectifiable_reifenberg_of_providers hbridge) n hn
  exact ⟨C, hC, hS, powerRateProperty_of_scaled hS hamb⟩

/-! ## The gauge rate -/

/-- The gauge rate from the scaled property with the same constant `C₀`. -/
theorem gaugeRateProperty_of_scaled {n : ℕ} {C₀ : ℝ} (hC₀ : 0 < C₀) (hn : 1 ≤ n)
    (hS : ScaledThresholdProperty n C₀) : GaugeRateProperty n C₀ := by
  intro k hk hkn μ hμ hreg a R hR Φ hΦ hΦm hΦfin hΛ
  set Λ := gaugeEnergy Φ μ k .mixed a R with hΛdef
  have hmixed : Nonempty (Models n k .mixed) := AdmissibleModel.nonempty_of_range hn hk hkn
  have hone : ∀ M : ℝ, 0 < M → 0 < Φ (ENNReal.ofReal M) →
      ∃ EH EV : Set (Space n), IsLocalEnhancedDecomposition k .mixed C₀ a R μ EH EV ∧
        μ.restrict (EH ∪ EV)ᶜ (Metric.ball a R) ≤
          ENNReal.ofReal (C₀ * M * R ^ k) + Λ / Φ (ENNReal.ofReal M) := by
    intro M hM hΦM
    have hΦtop : Φ (ENNReal.ofReal M) ≠ ⊤ := hΦfin _ ENNReal.ofReal_ne_top
    have hq : Λ / Φ (ENNReal.ofReal M) ≠ ⊤ := (ENNReal.div_lt_top hΛ.ne hΦM.ne').ne
    have hbad := measure_lt_squareEnergy_le_gaugeEnergy_div k μ hμ .mixed a R Φ hΦ hΦm M
      hΦM hΦtop
    obtain ⟨EH, EV, hloc, hloss⟩ := hS k hk hkn μ hμ hreg a R hR .mixed hmixed M
      (Λ / Φ (ENNReal.ofReal M)).toReal hM.le ENNReal.toReal_nonneg
      (hbad.trans_eq (ENNReal.ofReal_toReal hq).symm)
    refine ⟨EH, EV, hloc, hloss.trans_eq ?_⟩
    rw [ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hq]
  refine ⟨hone, ?_⟩
  rintro ⟨M₀, hM₀, hΦM₀⟩ η hη
  have hinf_le : (⨅ (M : ℝ) (_ : 0 < M) (_ : 0 < Φ (ENNReal.ofReal M)),
        ENNReal.ofReal (C₀ * M * R ^ k) + Λ / Φ (ENNReal.ofReal M)) ≤
      ENNReal.ofReal (C₀ * M₀ * R ^ k) + Λ / Φ (ENNReal.ofReal M₀) :=
    (iInf_le _ M₀).trans ((iInf_le _ hM₀).trans (iInf_le _ hΦM₀))
  have hfin₀ : ENNReal.ofReal (C₀ * M₀ * R ^ k) + Λ / Φ (ENNReal.ofReal M₀) ≠ ⊤ :=
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.div_lt_top hΛ.ne hΦM₀.ne'⟩).ne
  have hlt := ENNReal.lt_add_right (ne_top_of_le_ne_top hfin₀ hinf_le)
    (ENNReal.ofReal_pos.mpr hη).ne'
  obtain ⟨M, hM⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hMpos, hM'⟩ := iInf_lt_iff.mp hM
  obtain ⟨hΦM, hM''⟩ := iInf_lt_iff.mp hM'
  obtain ⟨EH, EV, hloc, hloss⟩ := hone M hMpos hΦM
  exact ⟨EH, EV, hloc, hloss.trans hM''.le⟩

/-- **Gauge rate.** Same constant `C₀` as the scaled threshold property. Hypotheses:
`CompactBridgeCoverStatement` and `SquareEnergyRescalingStatement`. -/
theorem gauge_rate_of_providers (hbridge : CompactBridgeCoverStatement)
    (hER : SquareEnergyRescalingStatement) : GaugeRateStatement := by
  intro n hn
  obtain ⟨C, hC, hS, -⟩ := scaled_and_ambient_of_graphEnhanced hER
    (graph_enhanced_rectifiable_reifenberg_of_providers hbridge) n hn
  exact ⟨C, hC, hS, gaugeRateProperty_of_scaled hC hn hS⟩

end ParabolicRectifiability.Enhancements
