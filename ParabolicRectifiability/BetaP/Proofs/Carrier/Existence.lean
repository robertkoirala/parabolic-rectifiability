import ParabolicRectifiability.BetaP.Proofs.Carrier.CarrierLemmas
import ParabolicRectifiability.Decomposition.ZeroThresholdAssembly

/-! # Assembly of the `p`-carrier

`ccar_exists_p_carrier` proves the existence statement `exists_p_carrier` (a compact carrier `K`
for a finite measure `ν` with bounded all-scale `p`-energy) from the auxiliary statements
`CellsPackingStatement`, `CarrierLossStatement`, `CarrierSeparatedStatement`,
`ContentOfSeparatedStatement`, `CarrierVariablePackingStatement` and `CarrierEnergyStatement`.

**Assembly** (the carrier construction, with `a = L^{p/2}`):
1. From the truncated packing hypothesis take `Ct = Ct(n,p)`; the loss, separated-set and
   variable-radius statements give `C_l, C_s, C_v` depending on `n, p, Ct`; the content statement
   gives `C₀(n)`. The constant `C = 2 C_l 2^{p/2} + 2 C₀ C_s + 2 C_v` is fixed before
   `k, T, ν, c, M` (the quantifier order of the statement).
2. For the data `k, T, ν, c, M`, put `L = 2M`, `a = L^{p/2} = (2M)^{p/2} > 0` and
   `K = densityCarrier ν k a` (the quadratic-case set `K_a`). The support hypothesis `P̄(c,1/64)`
   implies the `P̄(c,1/16)` used in the auxiliary statements and `K ⊆ P(c,1)`.
3. Compactness: `isCompact_densityCarrier`. `K ⊆ supp ν`: definition of `K_a`.
4. Loss: `C_l (a + L^{p/2}) = 2 C_l 2^{p/2} M^{p/2} ≤ C M^{p/2}` (`Real.mul_rpow`).
5. Content: the separated-set bound `C_s (1 + L^{p/2}/a) = 2 C_s` (lower mass of `K_a` is its
   definition), then `ContentOfSeparatedStatement`, then `HasMetricContentBounds.mono`.
6. Packing: `C_v (1 + L^{p/2}/a) = 2 C_v`, then `HasFiniteBallPacking.mono`.
7. Energy: domination `H_P^k⌊K_a ≤ (12^k/a) ν` (`restrict_hausdorffP_densityCarrier_le`),
   growth from the content bound just proved (step 5, never assumed), and
   `CarrierEnergyStatement` with the `ν`-a.e. bound `2M`.

No packing, content, growth, coverage or regularity of `K` or of `ν` is assumed: every such
property of `K` is an output of one of the auxiliary statements or of a general lemma. The
full-source packing hypothesis is not used (all three transfers use the truncated testing
sources; for the equal radii of the nets the two coincide above the common cutoff), hence its
binder is named `_hpack`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP.CarrierTree

open ParabolicRectifiability.Foundations

/-- **Existence of the `p`-carrier**, assembled from the auxiliary statements; it has the type of
`exists_p_carrier`. -/
theorem ccar_exists_p_carrier (_hpack : ActiveRadiusPackingStatement)
    (htrunc : ActiveRadiusPackingTruncatedStatement) (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν.InnerRegular →
      ∀ c : Space n, ν.support ⊆ Metric.closedBall c (1 / 64) →
      ∀ M : ℝ, 0 < M →
      (∀ᵐ z ∂ν, allScaleEnergyP ν k T p z ≤ ENNReal.ofReal (2 * M)) →
        Nonempty (PCarrier ν k T p M C) := by
  obtain ⟨Ct, hCt, htr⟩ := htrunc n hn p hp
  have hcells : CellsPackingStatement := ccar_cells_packing ccar_cells_fit_transfer
  obtain ⟨Cl, hCl, hloss⟩ := ccar_loss hcells n hn p hp Ct hCt htr
  obtain ⟨Cs, hCs, hsep⟩ := ccar_separated hcells n hn p hp Ct hCt htr
  obtain ⟨Cv, hCv, hvar⟩ := ccar_variable_packing hcells n hn p hp Ct hCt htr
  obtain ⟨C0, hC0, hcont⟩ := ccar_content_of_separated n
  have henergy : CarrierEnergyStatement :=
    ccar_energy ccar_input_holder ccar_input_betaPowTwo ccar_betaPow_domination
  have h2p : 0 < (2 : ℝ) ^ (p / 2) := Real.rpow_pos_of_pos two_pos _
  have hA : 0 < 2 * Cl * (2 : ℝ) ^ (p / 2) := by positivity
  have hB : 0 < C0 * (Cs * 2) := by positivity
  have hV : 0 < Cv * 2 := by positivity
  refine ⟨2 * Cl * (2 : ℝ) ^ (p / 2) + C0 * (Cs * 2) + Cv * 2, by linarith, ?_⟩
  intro k hk hkn T hT ν hν _hreg c hsupp M hM hae
  have := hν
  have hL : 0 < 2 * M := by linarith
  have ha : 0 < (2 * M) ^ (p / 2) := Real.rpow_pos_of_pos hL _
  have hratio : 1 + (2 * M) ^ (p / 2) / (2 * M) ^ (p / 2) = 2 := by
    rw [div_self ha.ne']
    norm_num
  have hsupp16 : ν.support ⊆ Metric.closedBall c (1 / 16) :=
    hsupp.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hKball : densityCarrier ν k ((2 * M) ^ (p / 2)) ⊆ Metric.ball c 1 := fun z hz =>
    Metric.closedBall_subset_ball (by norm_num) (hsupp hz.1)
  have hlow : HasUniformLowerMass ν k ((2 * M) ^ (p / 2))
      (densityCarrier ν k ((2 * M) ^ (p / 2))) := fun z hz r hr hr1 => hz.2 r hr hr1
  -- loss
  have hlossC : ν (densityCarrier ν k ((2 * M) ^ (p / 2)))ᶜ ≤
      ENNReal.ofReal ((2 * Cl * (2 : ℝ) ^ (p / 2) + C0 * (Cs * 2) + Cv * 2) * M ^ (p / 2)) := by
    refine (hloss k hk hkn T hT ν hν c hsupp16 (2 * M) ((2 * M) ^ (p / 2)) hL.le ha hae).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hsplit : (2 * M) ^ (p / 2) = (2 : ℝ) ^ (p / 2) * M ^ (p / 2) :=
      Real.mul_rpow (by norm_num) hM.le
    have hMp : 0 ≤ M ^ (p / 2) := Real.rpow_nonneg hM.le _
    rw [hsplit]
    calc Cl * ((2 : ℝ) ^ (p / 2) * M ^ (p / 2) + (2 : ℝ) ^ (p / 2) * M ^ (p / 2))
        = 2 * Cl * (2 : ℝ) ^ (p / 2) * M ^ (p / 2) := by ring
      _ ≤ (2 * Cl * (2 : ℝ) ^ (p / 2) + C0 * (Cs * 2) + Cv * 2) * M ^ (p / 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hMp
  -- content: separated sets, then the generic content bounds
  have hcontent : HasMetricContentBounds k (C0 * (Cs * 2))
      (densityCarrier ν k ((2 * M) ^ (p / 2))) := by
    have h := hcont k (by omega) (densityCarrier ν k ((2 * M) ^ (p / 2))) c
      (Cs * (1 + (2 * M) ^ (p / 2) / (2 * M) ^ (p / 2))) (by positivity) hKball
      (hsep k hk hkn T hT ν hν (2 * M) ((2 * M) ^ (p / 2)) hL.le ha hae _ hlow)
    rwa [hratio] at h
  -- variable-radius packing
  have hpacking : HasFiniteBallPacking k (Cv * 2) (densityCarrier ν k ((2 * M) ^ (p / 2))) := by
    have h := hvar k hk hkn T hT ν hν (2 * M) ((2 * M) ^ (p / 2)) hL.le ha hae _ hlow
    rwa [hratio] at h
  -- domination of the carrier measure
  have hdom := restrict_hausdorffP_densityCarrier_le ν ha (le_refl ((12 : ℝ) ^ k))
  exact ⟨{
    set := densityCarrier ν k ((2 * M) ^ (p / 2))
    compact := isCompact_densityCarrier ν k _ hsupp
    subset_support := fun z hz => hz.1
    loss := hlossC
    content := hcontent.mono (by linarith)
    packing := HasFiniteBallPacking.mono hpacking (by linarith)
    energy := henergy n hn k hk (by omega) T hT p hp ν _ c (C0 * (Cs * 2))
      ((12 : ℝ) ^ k / (2 * M) ^ (p / 2)) (2 * M) (by positivity) hL.le hKball
      hcontent.hausdorff hdom hae }⟩

end ParabolicRectifiability.BetaP.CarrierTree
