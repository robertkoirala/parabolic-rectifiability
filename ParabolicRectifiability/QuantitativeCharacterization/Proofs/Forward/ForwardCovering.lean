import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ForwardCovering
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Stopping
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.LastWitness
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Coverage
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion
import ParabolicRectifiability.QuantitativeCharacterization.Statements.WhitneyPlateau
import ParabolicRectifiability.QuantitativeCharacterization.Assembly.Monotonicity
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.PartitionEnergy
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Stopping.StoppingPacking
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.TerminalConstruction
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.LastWitness.LastWitness
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.Completion
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Coverage.CoverageAssembly
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Plateau.Completion
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalCarrier

/-! # The local forward covering

Proof of the local forward covering `exists_local_forward_covering`: under the local
hypotheses, a direct partition of the support with its discrete energy, a stopping decomposition
into bad cells and good regions, a terminal construction with a comparison square bound and a
completed reference in every good region, and the slab covering combine into the required neck
regions with explicit constants. The six main steps are supplied by:

| Step | Supplied by |
|---|---|
| partition and discrete energy | `PartitionEnergy.d1acomp_partitionEnergy` |
| stopping decomposition and packing | `Stopping.d1bcomp_stoppingPacking_of_fittingGap PartitionEnergy.d1acomp_fittingGap` |
| terminal construction | `Terminal.d1ccomp_terminalConstruction` |
| comparison square bound (last witness) | `Witness.d1dcomp_lastWitness_of_inputs Terminal.d1ccomp_owner Terminal.d1c_ancestor_proof PartitionEnergy.d1acomp_planeComparison` |
| completed reference | `d1ecomp_hub_completion_glue b2_whitney_plateau_completion_proof Characterization.b2_horizontalReference_map_mem_carrier_proof` |
| slab covering | `Coverage.d1fcomp_coverageAssembly_of_input Terminal.d1c_stopScaleLipschitz_proof` |

The type of `d1comp_exists_local_forward_covering` is exactly that of
`exists_local_forward_covering`.
-/
set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

open ParabolicRectifiability.Foundations

variable {n : ℕ}

/-- The local hypotheses persist in a smaller buffer. -/
theorem d1comp_localForward_mono {k : ℕ} {μ : Measure (Space n)} {A M : ℝ} {a : Space n}
    {ρ ρ' : ℝ} (h : LocalForwardHypotheses μ k A M a ρ) (hρ : ρ' ≤ ρ) :
    LocalForwardHypotheses μ k A M a ρ' := fun b hb s hs hsρ =>
  h b ⟨hb.1, Metric.ball_subset_ball hρ hb.2⟩ s hs (hsρ.trans hρ)

/-- The local hypotheses contain local ADR in the same buffer. -/
theorem d1comp_localADR_of_localForward {k : ℕ} {μ : Measure (Space n)} {A M : ℝ} {a : Space n}
    {ρ : ℝ} (h : LocalForwardHypotheses μ k A M a ρ) : LocalADR μ k A a ρ := fun b hb s hs hsρ =>
  ⟨(h b hb s hs hsρ).1, (h b hb s hs hsρ).2.1⟩

/-- The root side of a good region is positive. -/
theorem d1comp_rootScale_pos {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b) :
    0 < 𝒢.rootScale := by
  unfold GoodRegion.rootScale DirectPartition.scale coherentScale
  exact div_pos P.scale_pos (pow_pos (by norm_num) _)

/-- **A terminal construction together with a comparison square bound is a neck region**
(`NeckRegion`) with container `P(z_{Q_*}, 6 ℓ_*)`, `c₀ = 1`,
`C_d = 1`, `C_* = 8`, `σ = 1/4`. The square bound is supplied separately (by the last-witness
estimate). -/
def d1comp_toNeckRegion {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} {𝒢 : GoodRegion P μ k Λ b} {δ κ θ γ : ℝ}
    (TN : TerminalNeck 𝒢 δ κ θ γ) {E' : ℝ} (hE' : 0 ≤ E')
    (hsq : 𝒢.type.SquareBound TN.family E') :
    NeckRegion n k 𝒢.type (Space n) 𝒢.root.2 (6 * 𝒢.rootScale) 1 1 8 (1 / 4)
      δ E' κ θ γ where
  available := 𝒢.type_available
  parameters :=
    ⟨by have := d1comp_rootScale_pos 𝒢; linarith, one_pos, one_pos, by norm_num, by norm_num,
      by norm_num, TN.tolerance_nonneg.1, hE', TN.tolerance_nonneg.2.1,
      TN.tolerance_nonneg.2.2.1, fun _ => TN.tolerance_nonneg.2.2.2⟩
  centers := TN.centers
  isCompact_centers := TN.isCompact_centers
  centers_subset := TN.centers_subset
  radius := TN.radius
  radius_nonneg := TN.radius_nonneg
  radius_le := fun c hc => by rw [one_mul]; exact TN.radius_le c hc
  stop_separation := fun c hc c' hc' h h' hne => by
    rw [one_mul]; exact TN.stop_separation c hc c' hc' h h' hne
  core_separation := fun c hc h z hz hz0 => by
    have := TN.core_separation c hc h z hz hz0
    linarith
  family := TN.family
  initialRadius_le := by rw [TN.initialRadius_eq]; linarith
  initialPoint := TN.initialPoint
  initialPoint_mem := TN.initialPoint_mem
  initialPoint_near := by have := TN.initialPoint_near; linarith
  center_mem := fun j a ha => by
    have h := TN.center_mem j a ha
    rwa [show (8 : ℝ) * (6 * 𝒢.rootScale) = 48 * 𝒢.rootScale by ring]
  coherent := TN.coherent
  centerHeight := TN.centerHeight
  squareBound := hsq
  core_limit := TN.core_limit
  stoppingParent := TN.stoppingParent
  stoppingParent_spec := TN.stoppingParent_spec
  timeCompatible := TN.timeCompatible

/-- The final constant comparison: `C₆ C₂ (1 + C_E M / b) ≤ C₆ C₂ (1 + C_E / b) (1 + M)`. -/
theorem d1comp_constant_le {C₆ C₂ CE M b : ℝ} (hC₆ : 0 ≤ C₆) (hC₂ : 0 ≤ C₂) (hCE : 0 ≤ CE)
    (hM : 0 ≤ M) (hb : 0 < b) :
    C₆ * (C₂ * (1 + CE * M / b)) ≤ C₆ * (C₂ * (1 + CE / b)) * (1 + M) := by
  have hx : 0 ≤ CE / b := div_nonneg hCE hb.le
  have h1 : 1 + CE * M / b ≤ (1 + CE / b) * (1 + M) := by
    have h2 : CE * M / b = CE / b * M := by ring
    rw [h2]
    nlinarith [mul_nonneg hx hM]
  calc C₆ * (C₂ * (1 + CE * M / b)) ≤ C₆ * (C₂ * ((1 + CE / b) * (1 + M))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hC₂) hC₆
    _ = C₆ * (C₂ * (1 + CE / b)) * (1 + M) := by ring

/-- **The local forward covering**, assembled from the six main steps listed in the module
documentation (including the two inputs of the completion step). Type: exactly that of
`exists_local_forward_covering`. -/
theorem d1comp_exists_local_forward_covering :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Bloc : ℝ, 1 ≤ Bloc ∧ ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ M : ℝ, 0 ≤ M →
      (∀ b ∈ μ.support ∩ Metric.ball a (Bloc * R), ∀ s : ℝ, 0 < s → s ≤ Bloc * R →
        ENNReal.ofReal (A⁻¹ * s ^ k) ≤ μ (Metric.ball b s) ∧
          μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k) ∧
          (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) ≤
            ENNReal.ofReal (M * s ^ k)) →
      Nonempty (RegularMixedCovering k (C * (1 + M)) L₀ μ a R) := by
  intro n hn k hk hkn A hA
  -- Steps 5 and 6: constants depending on `n, k` only.
  obtain ⟨L₅, hL₅, ε₅, hε₅, h5⟩ :=
    d1ecomp_hub_completion_glue b2_whitney_plateau_completion_proof
      Characterization.b2_horizontalReference_map_mem_carrier_proof n hn k hk hkn 1 (1 / 4) one_pos
      (by norm_num) (by norm_num)
  obtain ⟨C₆, hC₆, L₆, -, h6⟩ :=
    Coverage.d1fcomp_coverageAssembly_of_input Terminal.d1c_stopScaleLipschitz_proof n hn k hk hkn
  -- The coefficient dilation `Λ`, before every threshold.
  obtain ⟨Λ₂, hΛ₂, h2⟩ :=
    Stopping.d1bcomp_stoppingPacking_of_fittingGap PartitionEnergy.d1acomp_fittingGap n hn k hk
      hkn A hA
  obtain ⟨Λ₃, -, h3⟩ := Terminal.d1ccomp_terminalConstruction n hn k hk hkn A hA
  obtain ⟨Λ₄, -, h4⟩ :=
    Witness.d1dcomp_lastWitness_of_inputs Terminal.d1ccomp_owner Terminal.d1c_ancestor_proof
      PartitionEnergy.d1acomp_planeComparison n hn k hk hkn A hA
  obtain ⟨Λ, hΛ2, hΛ3, hΛ4⟩ : ∃ Λ : ℝ, Λ₂ ≤ Λ ∧ Λ₃ ≤ Λ ∧ Λ₄ ≤ Λ :=
    ⟨max Λ₂ (max Λ₃ Λ₄), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨C₂, hC₂, B₂, -, b₂, hb₂, h2⟩ := h2 Λ hΛ2
  obtain ⟨B₃, -, h3⟩ := h3 Λ hΛ3
  obtain ⟨B₄, -, C₄, hC₄, ε₄, hε₄, b₄, hb₄, h4⟩ := h4 Λ hΛ4
  obtain ⟨CE, hCE, B₁, hB₁, h1⟩ :=
    PartitionEnergy.d1acomp_partitionEnergy n hn k hk hkn A hA Λ (hΛ₂.trans hΛ2)
  -- The tolerance and the stopping threshold.
  obtain ⟨ε, hε, hε4, hε5⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₄ ∧ ε ≤ ε₅ :=
    ⟨min ε₄ ε₅, lt_min hε₄ hε₅, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨b₃, hb₃, h3⟩ := h3 ε hε
  obtain ⟨b, hb, hbb₂, hbb₃, hbb₄, hbE⟩ :
      ∃ b : ℝ, 0 < b ∧ b ≤ b₂ ∧ b ≤ b₃ ∧ b ≤ b₄ ∧ C₄ * b ≤ ε₅ := by
    have hC₄1 : (0 : ℝ) < C₄ + 1 := by linarith
    refine ⟨min (min b₂ b₃) (min b₄ (ε₅ / (C₄ + 1))),
      lt_min (lt_min hb₂ hb₃) (lt_min hb₄ (div_pos hε₅ hC₄1)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), ?_⟩
    have hle : min (min b₂ b₃) (min b₄ (ε₅ / (C₄ + 1))) ≤ ε₅ / (C₄ + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hpos : 0 < min (min b₂ b₃) (min b₄ (ε₅ / (C₄ + 1))) :=
      lt_min (lt_min hb₂ hb₃) (lt_min hb₄ (div_pos hε₅ hC₄1))
    have h' := (le_div_iff₀ hC₄1).mp hle
    nlinarith
  -- The reported constants.
  obtain ⟨Bloc, hBloc, hB1, hB2, hB3, hB4⟩ :
      ∃ B : ℝ, 1 ≤ B ∧ B₁ ≤ B ∧ B₂ ≤ B ∧ B₃ ≤ B ∧ B₄ ≤ B :=
    ⟨max B₁ (max B₂ (max B₃ B₄)), hB₁.trans (le_max_left _ _), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _),
      ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _),
      ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)⟩
  obtain ⟨L₀, hL₀, hL₅₀, hL₆₀⟩ : ∃ L : ℝ, 1 ≤ L ∧ L₅ ≤ L ∧ L₆ ≤ L :=
    ⟨max L₅ L₆, hL₅.trans (le_max_left _ _), le_max_left _ _, le_max_right _ _⟩
  have hC : 1 ≤ C₆ * (C₂ * (1 + CE / b)) :=
    one_le_mul_of_one_le_of_one_le hC₆
      (one_le_mul_of_one_le_of_one_le hC₂ (le_add_of_nonneg_right (div_nonneg hCE hb.le)))
  refine ⟨Bloc, hBloc, L₀, hL₀, C₆ * (C₂ * (1 + CE / b)), hC, ?_⟩
  intro μ hfin hreg a ha R hR M hM hloc
  have hloc' : LocalForwardHypotheses μ k A M a (Bloc * R) := hloc
  have hbuf : ∀ {B : ℝ}, B ≤ Bloc → B * R ≤ Bloc * R := fun hB =>
    mul_le_mul_of_nonneg_right hB hR.le
  have hadr : LocalADR μ k A a (Bloc * R) := d1comp_localADR_of_localForward hloc'
  have hadr_mono : ∀ {B : ℝ}, B ≤ Bloc → LocalADR μ k A a (B * R) := by
    intro B hB b' hb' s hs hsB
    exact hadr b' ⟨hb'.1, Metric.ball_subset_ball (hbuf hB) hb'.2⟩ s hs (hsB.trans (hbuf hB))
  -- Step 1: the partition and the discrete energy.
  obtain ⟨P, hP⟩ :=
    h1 μ hfin hreg a ha R hR M hM (d1comp_localForward_mono hloc' (hbuf hB1))
  -- Step 2: the stopping decomposition.
  obtain ⟨SD⟩ :=
    h2 b hb hbb₂ μ hfin hreg a ha R hR (CE * M) (mul_nonneg hCE hM) (hadr_mono hB2) P hP
  have hforest : ∀ S : SD.roots, P.InForest a R (SD.region S).root := fun S => by
    rw [SD.region_root]
    exact SD.roots_forest S.1 S.2
  -- Step 3: a terminal construction for every good region.
  let tn : ∀ S : SD.roots, TerminalNeck (SD.region S) ε ε ε ε := fun S =>
    Classical.choice (h3 b hb hbb₃ μ hfin hreg a ha R hR (hadr_mono hB3) P (SD.region S)
      (hforest S))
  -- Step 4: its comparison square bound.
  have hsq : ∀ S : SD.roots, (SD.region S).type.SquareBound (tn S).family (C₄ * b) :=
    fun S => h4 b hb hbb₄ μ hfin hreg a ha R hR (hadr_mono hB4) P (SD.region S) (hforest S)
      ε ε ε ε hε4 hε4 hε4 hε4 (tn S)
  -- Step 5: the completed reference of every good region.
  have href : ∀ S : SD.roots, ∃ ρ : Reference n k L₅,
      ρ.kind = (SD.region S).type.toFamilyKind ∧ (tn S).centers ⊆ ρ.carrier := fun S =>
    h5 (SD.region S).type (Space n) (SD.region S).root.2 (6 * (SD.region S).rootScale) 1 8
      ε (C₄ * b) ε ε ε hε5 hbE hε5 hε5 hε5
      (d1comp_toNeckRegion (tn S) (mul_nonneg hC₄ hb.le) (hsq S))
  choose ref _ hrefc using href
  have hL₅0 : (0 : ℝ) ≤ L₅ := by linarith
  -- Step 6: the covering.
  obtain ⟨𝒞⟩ :=
    h6 L₀ hL₆₀ μ hfin hreg a ha R hR Λ b (C₂ * (1 + CE * M / b))
      (mul_nonneg (by linarith) (add_nonneg zero_le_one (div_nonneg (mul_nonneg hCE hM) hb.le)))
      P SD ε ε ε ε tn (fun S => (ref S).mono hL₅0 hL₅₀)
      (fun S => by simpa only [Reference.carrier_mono] using hrefc S)
  exact ⟨𝒞.mono hR.le (by linarith)
    (d1comp_constant_le (by linarith) (by linarith) hCE hM hb) le_rfl⟩

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
