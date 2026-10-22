import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.ComponentEstimates

/-! # Reference estimates: assembly

`ba1_reference_estimates` has exactly the type `ReferenceEstimatesStatement`. It is assembled
from the horizontal, vertical and ambient statements (`ba1_horizontal_adr`, `ba1_vertical_adr`,
`ba1_ambient_adr`, `ba1_horizontal_energy`, …), which delegate to their proofs. Every sibling
hypothesis of one of these statements is discharged here by the corresponding sibling result.

Assembly. For `n ≥ 1`, `1 ≤ k ≤ n + 2` and `L ≥ 1` the constants are chosen after `(n,k,L)` and
before the reference: `A = max A_H (max A_V A_amb)` and `C = max C_H C_V`, from the uniform
horizontal, vertical and ambient estimates. A horizontal reference needs `k ≤ n` and a vertical
one `k < n + 2`, so the zero-energy clause at `k = n + 2` concerns only the ambient reference,
whose energy vanishes by the F statement `AmbientEnergyZeroStatement` (every vertical model
at `k = n + 2` is the whole space), applied to the locally Radon measure `parabolicVolume n`.
ADR bounds are monotone in the constant (`ba1_isADR_mono`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- ADR bounds are monotone in the constant: if `0 < A ≤ A'`, an `A`-ADR measure is `A'`-ADR
(`A'⁻¹ ≤ A⁻¹` for the lower bound). -/
theorem ba1_isADR_mono {n k : ℕ} {μ : Measure (Space n)} {A A' : ℝ} (hA : 0 < A)
    (hAA' : A ≤ A') (h : IsADR A k μ) : IsADR A' k μ := by
  intro z hz r hr
  obtain ⟨h1, h2⟩ := h z hz r hr
  have hrk : 0 ≤ r ^ k := pow_nonneg hr.le k
  exact ⟨le_trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (inv_anti₀ hA hAA') hrk)) h1,
    h2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAA' hrk))⟩

/-- The ambient reference has zero own-type Carleson energy: at `k = n + 2` every available
natural beta and square function of the locally Radon measure `parabolicVolume n` vanishes
(`AmbientEnergyZeroStatement`), so every term of the root supremum is zero. Finiteness on
compacts is the existing instance; inner regularity is the ambient basic statement. -/
theorem ba1_ambient_energy_eq_zero
    (hbasic : ∀ n : ℕ, (parabolicVolume n).InnerRegular ∧ (parabolicVolume n).support = Set.univ)
    (hAZ : AmbientEnergyZeroStatement) {n k : ℕ} (hn : 1 ≤ n) (L : ℝ) (h : k = n + 2) :
    referenceEnergy (Reference.ambient h : Reference n k L) = 0 := by
  subst h
  have hreg : (parabolicVolume n).InnerRegular := (hbasic n).1
  have hne : Nonempty (Models n (n + 2) FamilyKind.vertical) :=
    VerticalModel.nonempty_iff.mpr ⟨by omega, le_rfl⟩
  have hz : ∀ R : ℝ, 0 < R → ∀ z : Space n,
      squareEnergy (parabolicVolume n) (n + 2) FamilyKind.vertical R z = 0 :=
    (hAZ n hn (parabolicVolume n) inferInstance hreg FamilyKind.vertical hne).2
  simp only [referenceEnergy, rootCarlesonSup, Reference.carrier, Reference.measure,
    Reference.kind]
  refine le_antisymm ?_ bot_le
  refine iSup₂_le fun a _ => iSup₂_le fun R hR => ?_
  simp [hz R hR]

/-- **Reference estimates**, assembled from the horizontal, vertical and ambient statements.
Type: exactly `ReferenceEstimatesStatement`. -/
theorem ba1_reference_estimates : ReferenceEstimatesStatement := by
  intro n hn k hk hkn L hL
  obtain ⟨AH, hAH, hADRH⟩ := ba1_horizontal_adr ba1_horizontal_basic n k L hL
  obtain ⟨AV, hAV, hADRV⟩ := ba1_vertical_adr ba1_vertical_basic n k L hL
  obtain ⟨AA, hAA, hADRA⟩ := ba1_ambient_adr n
  obtain ⟨CH, hCH, hEH⟩ :=
    ba1_horizontal_energy ba1_horizontal_basic (ba1_horizontal_beta ba1_horizontal_basic)
      ba1_input_spatialAffineSquare
      (ba1_horizontal_temporal ba1_horizontal_basic
        (ba1_horizontal_coarse ba1_horizontal_interpolation) ba1_horizontal_fine)
      n k L hL
  obtain ⟨CV, hCV, hEV⟩ :=
    ba1_vertical_energy ba1_vertical_basic (ba1_vertical_beta ba1_vertical_basic)
      (ba1_vertical_carleson
        (ba1_vertical_unit_carleson ba1_input_localization ba1_input_fourierAffineSquare)
        ba1_standard_dilation)
      n k L hL
  refine ⟨max AH (max AV AA), le_trans hAH (le_max_left _ _), max CH CV,
    lt_of_lt_of_le hCH (le_max_left _ _), fun ρ => ?_⟩
  cases ρ with
  | horizontal H =>
    obtain ⟨_, hkn'⟩ := H.available
    exact ⟨ba1_isADR_mono (by linarith) (le_max_left _ _) (hADRH H),
      (hEH H).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
      fun h => absurd h (by omega)⟩
  | vertical V =>
    have hlt := V.lt_ambient
    exact ⟨ba1_isADR_mono (by linarith) (le_trans (le_max_left _ _) (le_max_right _ _))
        (hADRV V),
      (hEV V).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)),
      fun h => absurd h (by omega)⟩
  | ambient h =>
    have hz := ba1_ambient_energy_eq_zero ba1_ambient_basic ba1_input_ambientEnergyZero hn L h
    refine ⟨?_, by rw [hz]; exact bot_le, fun _ => hz⟩
    show IsADR _ k (parabolicVolume n)
    rw [h]
    exact ba1_isADR_mono (by linarith) (le_trans (le_max_right _ _) (le_max_right _ _)) hADRA

end ParabolicRectifiability.QuantitativeCharacterization
