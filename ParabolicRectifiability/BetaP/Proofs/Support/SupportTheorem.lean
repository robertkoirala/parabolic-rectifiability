import ParabolicRectifiability.BetaP.Proofs.Support.Basic
import ParabolicRectifiability.BetaP.Proofs.Packing.MainPacking

/-! # The beta-`p` support theorem (`BetaPSupportStatement`)

Assembly, for fixed `n ≥ 1` and `0 < p`, with one constant `C = C(n,p)`:
* `T_p` threshold (`p ≤ 2`): `S_2^2 ≤ 2^{2-p} T_p^2` (clamping law and `B_2 = betaSq`) turns the
  `T_p` threshold into the quadratic threshold at `2^{2-p} M`, and the rectifiable Reifenberg theorem
  (`Enhancements.RectifiableReifenbergTheoremStatement`, hypothesis) gives a restriction decomposition,
  read as a nonnegative one.
* `S_p` threshold (`p ≥ 2`):
  - `k = n+2`: the Foundations ambient core (hypothesis), zero loss;
  - `k < n+2`, `M = 0`: the zero-error bridge turns the zero `S_p` threshold into the
    zero quadratic threshold, and the rectifiable Reifenberg theorem at `M = 0` gives loss `Γ`;
  - `k < n+2`, `M > 0`: localization, `p`-carrier, Borel typing (hypotheses) and
    assembly (`positive_p_branch`).
* Localized clause: normalized rescaling of the source and of the threshold, the unit clause for
  the rescaled source with allowance `Γ/R₀^k`, and transport of the decomposition back.
* Ambient clause: the Foundations ambient core.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- The positive `S_p` branch (`p ≥ 2`, `k < n+2`, `M > 0`): localization, the `p`-carrier of
each localized source, the Borel typing of each carrier by the finite-Hausdorff criterion and
typed refinement, and assembly. The active-radius packing statements enter the carrier
construction. -/
theorem positive_p_branch (hFH : Characterization.FiniteHausdorffCriterionStatement)
    (hTR : Characterization.TypedRefinementSetStatement) (n : ℕ) (hn : 1 ≤ n) (p : ℝ)
    (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 < M → 0 ≤ Γ →
      μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyS μ k T p 2 z}) ≤
        ENNReal.ofReal Γ →
      ∃ μplus μH μV : Measure (Space n),
        IsBetaPDecomposition k T C (point 0 0) 1 (C * M ^ (p / 2) + Γ) μ μplus μH μV := by
  classical
  obtain ⟨N, -, hloc⟩ := exists_p_localization n hn
  obtain ⟨Cc, hCc, hcar⟩ := exists_p_carrier activeRadiusPacking_skeleton
    activeRadiusPacking_truncated_skeleton n hn p hp
  obtain ⟨C, hC, hasm⟩ := exists_assembled_p_decomposition n hn p hp N Cc hCc
  refine ⟨C, hC, ?_⟩
  intro k hk hkn T hT μ hμ hreg M Γ hM hΓ hthr
  let S : PLocalization μ k T p M N :=
    Classical.choice (hloc p (by linarith) k hk hkn T hT μ hμ hreg M hM.le)
  let K : ∀ i : Fin S.count, PCarrier (μ.restrict (S.region i)) k T p M Cc := fun i =>
    Classical.choice (hcar k hk hkn T hT _ (S.finite i) (S.innerRegular i) (S.center i)
      (S.support_small i) M hM (S.energy i))
  have hsplit : ∀ i, Nonempty (TypedSplit k T (K i).set) := fun i =>
    typedSplit_exists hFH hTR hn hk hkn hT (K i).compact.isClosed.measurableSet
      ((K i).hausdorff_lt_top (S.support_small i)) (K i).energy
  exact hasm k hk hkn T hT μ hμ hreg M Γ hM hΓ hthr S K fun i => Classical.choice (hsplit i)

/-- The unit and ambient clauses of the support theorem with one constant. -/
theorem unitClause_of_providers (hMT1 : Enhancements.RectifiableReifenbergTheoremStatement)
    (hAmb : AmbientLocalCoreStatement) (hB2 : BetaPowTwoStatement)
    (hFH : Characterization.FiniteHausdorffCriterionStatement)
    (hTR : Characterization.TypedRefinementSetStatement) (n : ℕ) (hn : 1 ≤ n) (p : ℝ)
    (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
        BetaPUnitClause k T p C μ ∧ BetaPAmbientClause k T C μ := by
  obtain ⟨CA, hCA, hA⟩ := mt1_family_decomposition hMT1 n hn
  obtain ⟨CF, hCF, hF⟩ := ambient_betaP_decomposition hAmb n hn
  obtain ⟨CP, hCP, hP⟩ : ∃ CP : ℝ, 0 < CP ∧ (2 ≤ p →
      ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 < M → 0 ≤ Γ →
      μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyS μ k T p 2 z}) ≤
        ENNReal.ofReal Γ →
      ∃ μplus μH μV : Measure (Space n),
        IsBetaPDecomposition k T CP (point 0 0) 1 (CP * M ^ (p / 2) + Γ) μ μplus μH μV) := by
    by_cases hp2 : 2 ≤ p
    · obtain ⟨CP, hCP, hP⟩ := positive_p_branch hFH hTR n hn p hp2
      exact ⟨CP, hCP, fun _ => hP⟩
    · exact ⟨1, one_pos, fun h => absurd h hp2⟩
  have h2p : 0 < (2 : ℝ) ^ (2 - p) := Real.rpow_pos_of_pos two_pos _
  have hCA_le : CA ≤ CA * ((2 : ℝ) ^ (2 - p) + 1) + CP + CF := by nlinarith
  have hCA2_le : CA * (2 : ℝ) ^ (2 - p) ≤ CA * ((2 : ℝ) ^ (2 - p) + 1) + CP + CF := by nlinarith
  have hCP_le : CP ≤ CA * ((2 : ℝ) ^ (2 - p) + 1) + CP + CF := by nlinarith
  have hCF_le : CF ≤ CA * ((2 : ℝ) ^ (2 - p) + 1) + CP + CF := by nlinarith
  refine ⟨CA * ((2 : ℝ) ^ (2 - p) + 1) + CP + CF, by positivity, ?_⟩
  intro k hk hkn T hT μ hμ hreg
  refine ⟨fun M Γ hM hΓ => ⟨fun hp2 hthr => ?_, fun hp2 hthr => ?_⟩, fun hk2 => ?_⟩
  · -- the `S_p` threshold, `p ≥ 2`
    by_cases hk2 : k = n + 2
    · subst hk2
      obtain ⟨μplus, μH, μV, hD⟩ := hF T hT μ hμ hreg
      have hMp : 0 ≤ M ^ (p / 2) := Real.rpow_nonneg hM _
      exact ⟨μplus, μH, μV, hD.mono hCF_le zero_le_one (by positivity)⟩
    · have hklt : k < n + 2 := lt_of_le_of_ne hkn hk2
      rcases hM.eq_or_lt with hM0 | hMpos
      · subst hM0
        have hthr2 : μ (Metric.ball (point 0 0) 1 ∩
            {z | ENNReal.ofReal 0 < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ := by
          refine (measure_mono ?_).trans hthr
          rintro z ⟨hz1, hz2⟩
          refine ⟨hz1, ?_⟩
          have hz2' : 0 < squareEnergy μ k T 2 z := by simpa using hz2
          show ENNReal.ofReal 0 < energyS μ k T p 2 z
          rw [ENNReal.ofReal_zero, pos_iff_ne_zero]
          exact fun h0 => hz2'.ne'
            (squareEnergy_eq_zero_of_energyS_eq_zero hn hk hkn hT hμ hreg hp two_pos h0)
        obtain ⟨μplus, μH, μV, hD⟩ := hA k hk hkn T hT μ hμ hreg 0 Γ le_rfl hΓ hthr2
        refine ⟨μplus, μH, μV, hD.mono hCA_le zero_le_one ?_⟩
        rw [Real.zero_rpow (by positivity)]
        simp
      · obtain ⟨μplus, μH, μV, hD⟩ := hP hp2 k hk hklt T hT μ hμ hreg M Γ hMpos hΓ hthr
        exact ⟨μplus, μH, μV, hD.mono hCP_le zero_le_one (add_le_add_left
          (mul_le_mul_of_nonneg_right hCP_le (Real.rpow_nonneg hM _)) Γ)⟩
  · -- the `T_p` threshold, `p ≤ 2`
    have hthr2 : μ (Metric.ball (point 0 0) 1 ∩
        {z | ENNReal.ofReal ((2 : ℝ) ^ (2 - p) * M) < squareEnergy μ k T 2 z}) ≤
          ENNReal.ofReal Γ := by
      refine (measure_mono ?_).trans hthr
      rintro z ⟨hz1, hz2⟩
      refine ⟨hz1, ?_⟩
      change ENNReal.ofReal ((2 : ℝ) ^ (2 - p) * M) < squareEnergy μ k T 2 z at hz2
      change ENNReal.ofReal M < energyT μ k T p 2 z
      by_contra hcon
      have hcon' := not_lt.mp hcon
      have hcmp := squareEnergy_le_two_rpow_mul_energyT hB2 hn hk hkn T μ hp hp2 2 z
      rw [ENNReal.ofReal_mul h2p.le, ← ENNReal.ofReal_rpow_of_pos two_pos,
        ENNReal.ofReal_ofNat] at hz2
      exact lt_irrefl _ (hz2.trans_le (hcmp.trans (mul_le_mul_right hcon' _)))
    obtain ⟨μplus, μH, μV, hD⟩ :=
      hA k hk hkn T hT μ hμ hreg _ Γ (mul_nonneg h2p.le hM) hΓ hthr2
    refine ⟨μplus, μH, μV, hD.mono hCA_le zero_le_one ?_⟩
    have : CA * ((2 : ℝ) ^ (2 - p) * M) ≤ (CA * ((2 : ℝ) ^ (2 - p) + 1) + CP + CF) * M := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hCA2_le hM
    linarith
  · -- the ambient clause
    subst hk2
    obtain ⟨μplus, μH, μV, hD⟩ := hF T hT μ hμ hreg
    exact ⟨μplus, μH, μV, hD.mono hCF_le zero_le_one le_rfl⟩

/-- The localized clause from the unit clause for every locally Radon source: rescale the source
and its threshold, apply the unit clause with allowance `Γ/R₀^k`, and transport the decomposition
back with loss `R₀^k (C M^{p/2} + Γ/R₀^k) = C M^{p/2} R₀^k + Γ` (resp. `C M R₀^k + Γ`). -/
theorem localizedClause_of_unitClause {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 0 < p) {C : ℝ}
    (hC : 0 < C) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2) {T : FamilyKind}
    (hunit : ∀ ν : Measure (Space n), IsFiniteMeasureOnCompacts ν → ν.InnerRegular →
      BetaPUnitClause k T p C ν)
    (μ : Measure (Space n)) (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) :
    BetaPLocalizedClause k T p C μ := by
  intro q R₀ hR₀ M Γ hM hΓ
  obtain ⟨hνμ, hνreg, hS, hT⟩ :=
    rescaledSource_betaP_threshold hn hk hkn T μ hμ hreg q R₀ hR₀ p hp M
  have hR₀k : 0 < R₀ ^ k := pow_pos hR₀ k
  have hscale : (ENNReal.ofReal R₀)⁻¹ ^ k * ENNReal.ofReal Γ = ENNReal.ofReal (Γ / R₀ ^ k) := by
    rw [← ENNReal.ofReal_inv_of_pos hR₀, ← ENNReal.ofReal_pow (inv_nonneg.mpr hR₀.le),
      ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hR₀.le) _), div_eq_mul_inv, inv_pow,
      mul_comm]
  have hΓ' : 0 ≤ Γ / R₀ ^ k := div_nonneg hΓ hR₀k.le
  have hloss : ∀ x : ℝ, R₀ ^ k * (x + Γ / R₀ ^ k) = x * R₀ ^ k + Γ := by
    intro x
    rw [mul_add, mul_div_cancel₀ _ hR₀k.ne', mul_comm]
  refine ⟨fun hp2 hthr => ?_, fun hp2 hthr => ?_⟩
  · have hthrν : (rescaledSource μ k q R₀ hR₀) (Metric.ball (point 0 0) 1 ∩
        {z | ENNReal.ofReal M < energyS (rescaledSource μ k q R₀ hR₀) k T p 2 z}) ≤
          ENNReal.ofReal (Γ / R₀ ^ k) := by
      rw [hS, ← hscale]
      exact mul_le_mul_right hthr _
    obtain ⟨νplus, νH, νV, hD⟩ := (hunit _ hνμ hνreg M (Γ / R₀ ^ k) hM hΓ').1 hp2 hthrν
    obtain ⟨μplus, μH, μV, hE⟩ := IsBetaPDecomposition.of_rescaledSource hn hk hkn hR₀ hC hD
    exact ⟨μplus, μH, μV, hE.mono le_rfl hR₀.le (le_of_eq (hloss _))⟩
  · have hthrν : (rescaledSource μ k q R₀ hR₀) (Metric.ball (point 0 0) 1 ∩
        {z | ENNReal.ofReal M < energyT (rescaledSource μ k q R₀ hR₀) k T p 2 z}) ≤
          ENNReal.ofReal (Γ / R₀ ^ k) := by
      rw [hT, ← hscale]
      exact mul_le_mul_right hthr _
    obtain ⟨νplus, νH, νV, hD⟩ := (hunit _ hνμ hνreg M (Γ / R₀ ^ k) hM hΓ').2 hp2 hthrν
    obtain ⟨μplus, μH, μV, hE⟩ := IsBetaPDecomposition.of_rescaledSource hn hk hkn hR₀ hC hD
    exact ⟨μplus, μH, μV, hE.mono le_rfl hR₀.le (le_of_eq (hloss _))⟩

/-- **The beta-`p` support theorem.**

Hypotheses:
* `Enhancements.RectifiableReifenbergTheoremStatement`;
* `Foundations.AmbientLocalCoreStatement` and `Foundations.BetaPowTwoStatement`;
* `Characterization.FiniteHausdorffCriterionStatement` and
  `Characterization.TypedRefinementSetStatement`.
Results used: `betaPowClamping_law`, `activeRadiusPacking_of_discretePacking`
(fed by `discrete_packing_proof`), `exists_p_localization`, `exists_p_carrier`,
`exists_assembled_p_decomposition`, `squareEnergy_eq_zero_of_energyS_eq_zero`,
`rescaledSource_betaP_threshold`, `IsBetaPDecomposition.of_rescaledSource`. -/
theorem betaPSupport_of_providers (hMT1 : Enhancements.RectifiableReifenbergTheoremStatement)
    (hAmb : AmbientLocalCoreStatement) (hB2 : BetaPowTwoStatement)
    (hFH : Characterization.FiniteHausdorffCriterionStatement)
    (hTR : Characterization.TypedRefinementSetStatement) :
    BetaPSupportStatement := by
  rw [betaPSupportStatement_iff]
  intro n hn p hp
  obtain ⟨C, hC, h⟩ := unitClause_of_providers hMT1 hAmb hB2 hFH hTR n hn p hp
  refine ⟨C, hC, fun k hk hkn T hT μ hμ hreg =>
    ⟨(h k hk hkn T hT μ hμ hreg).1, ?_, (h k hk hkn T hT μ hμ hreg).2⟩⟩
  exact localizedClause_of_unitClause hn hp hC hk hkn
    (fun ν hν hνreg => (h k hk hkn T hT ν hν hνreg).1) μ hμ hreg

end ParabolicRectifiability.BetaP
