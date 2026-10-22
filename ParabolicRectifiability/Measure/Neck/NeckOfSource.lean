import ParabolicRectifiability.Measure.Neck.Certificates
import ParabolicRectifiability.Measure.Neck.ConstructionEstimates
import ParabolicRectifiability.Measure.Neck.ConstructionCoherence
import ParabolicRectifiability.Measure.Neck.NodeCharge
import ParabolicRectifiability.Measure.Neck.Selection.Root
import ParabolicRectifiability.Measure.Neck.Selection.StageChoice
import ParabolicRectifiability.Measure.Neck.Selection.Recursion
import ParabolicRectifiability.Measure.Neck.Selection.Invariants
import ParabolicRectifiability.Measure.Neck.Selection.Partition
import ParabolicRectifiability.Measure.Neck.Selection.Thresholds
import ParabolicRectifiability.Measure.Neck.PlaneTime.PlaneComparison
import ParabolicRectifiability.Measure.Neck.PlaneTime.TimeCompatibility
import ParabolicRectifiability.Measure.Neck.PlaneTime.AmbientSquare
import ParabolicRectifiability.Measure.Neck.RegionCore.Region
import ParabolicRectifiability.Measure.Neck.RegionCore.CoreLower
import ParabolicRectifiability.Measure.Neck.RegionCore.CoreSquare
import ParabolicRectifiability.Geometry.Neck.NeckTheorems
import ParabolicRectifiability.Geometry.Neck.ChargeCollapse
import ParabolicRectifiability.Geometry.Neck.ChargingConclusions

/-!
# The neck of a source

This file assembles the proof that every admissible source carries a neck
(`exists_neck_of_source_proof`) from the auxiliary statements proved in the neighboring
files; it adds no new mathematics.

* `neck_structure_conclusions_proof` and the reductions `exists_sourceConstruction_proof`,
  `partitionFacts_of_construction_proof`, `recordsTimeCompatible_of_construction_proof`,
  `nodeError_le_proof`, `regionFacts_of_construction_proof` and
  `ambientSquare_of_construction_proof` prove the statements without the suffix;
* `exists_neck_of_source_bundled_proof` proves `exists_neck_of_source_bundled`, and
  `exists_neck_of_source_proof` proves `exists_neck_of_source`.

Statements proved in implication form are applied to the proofs of their hypotheses:
`errorSet_le_proof n (nodeError_le_proof n)`,
`measure_eq_of_construction_proof n (partitionFacts_of_construction_proof n)`,
`coherent_of_construction_proof n (planeComparison_sq_le_proof n)`,
`centerHeight_stoppingParent_of_construction_proof n (planeComparison_sq_le_proof n)`,
`fittedTime_comparison_of_construction_proof n (nodeBeta_le_proof n)`,
`ambientSquare_finite_of_construction_proof n (nodeBeta_le_proof n)`. The node error
statement uses `NeckHubTree.<name>_proof` for the neck tree statements, the charge
statements `ChargeCollapse.lastWitness_sum` and `ChargeCollapse.nodeErrorMass_iUnion_le`, and
the buffered reference statements.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-! ## Geometric conclusions of the neck -/

/-- Monotonicity of the parametrization predicate in the distortion. -/
theorem NeckRegion.HasParametrization.mono_distortion {n k : ℕ} {T : NeckType} {ι : Type*}
    {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ} {N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ}
    {Λ Λ' : ℝ} (h : N.HasParametrization Λ) (hΛ : 0 < Λ) (hΛΛ' : Λ ≤ Λ') :
    N.HasParametrization Λ' := by
  obtain ⟨hH, hV⟩ := h
  exact ⟨fun hT => (hH hT).mono hΛ hΛΛ', fun hT => (hV hT).mono hΛ hΛΛ'⟩

/-- The statement `neck_structure_conclusions`, from
`NeckHubTree.vertical_neck_structure_proof` and `NeckHubTree.horizontal_neck_structure_proof`. -/
theorem neck_structure_conclusions_proof (n : ℕ) :
    ∃ C δ₀ E₀ κ₀ θ₀ γ₀ : ℝ, 1 ≤ C ∧ 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < θ₀ ∧ 0 < γ₀ ∧
      ∀ {k : ℕ} {T : NeckType} {ι : Type} {q : Space n} {R Cd Cs δ E κ θ γ : ℝ}
        (N : NeckRegion n k T ι q R (1 / 20) Cd Cs T.sourceSeparation δ E κ θ γ),
        δ ≤ δ₀ → E ≤ E₀ → κ ≤ κ₀ → θ ≤ θ₀ → γ ≤ γ₀ →
        N.HasParametrization 2 ∧ N.HasLocalContentBound C ∧
          N.HasTotalContentBound (C * (2 + Cd) ^ k) ∧ N.HasCoreDensity C := by
  obtain ⟨_, _, _, -, hV⟩ := NeckHubTree.vertical_neck_structure_proof.{0} n
  obtain ⟨_, _, _, -, hH⟩ := NeckHubTree.horizontal_neck_structure_proof.{0} n
  obtain ⟨CV, hCV, hV'⟩ := hV (1 / 20) (by norm_num)
  obtain ⟨CH, hCH, hH'⟩ := hH (1 / 20) (by norm_num)
  obtain ⟨δV, EV, κV, θV, hδV, hEV, hκV, hθV, hVN⟩ := hV' 1 one_pos le_rfl
  obtain ⟨δH, EH, κH, θH, hδH, hEH, hκH, hθH, hHN⟩ := hH' (1 / 4) (by norm_num) (by norm_num)
  refine ⟨CV + CH, min δV δH, min EV EH, min κV κH, min θV θH,
    min ((1 / 4 : ℝ) ^ 2) (min ((1 / 20 : ℝ) ^ 2) 1) / 4, by linarith, lt_min hδV hδH,
    lt_min hEV hEH, lt_min hκV hκH, lt_min hθV hθH,
    div_pos (lt_min (by norm_num) (lt_min (by norm_num) one_pos)) (by norm_num), ?_⟩
  intro k T ι q R Cd Cs δ E κ θ γ N hδ hE hκ hθ hγ
  have hCd : 0 ≤ (2 + Cd) ^ k := pow_nonneg (by linarith [N.parameters.Cd_pos]) k
  have hR : 0 ≤ R := N.parameters.R_pos.le
  cases T with
  | horizontal =>
    obtain ⟨hpar, hloc, htot, hden, -⟩ := hHN N (hδ.trans (min_le_right _ _))
      (hE.trans (min_le_right _ _)) (hκ.trans (min_le_right _ _))
      (hθ.trans (min_le_right _ _)) hγ
    refine ⟨⟨fun _ => hpar, (fun h => nomatch h)⟩, hloc.mono (by linarith), ?_,
      hden.mono (by linarith)⟩
    exact htot.mono (mul_le_mul_of_nonneg_right (by linarith) hCd) hR
  | vertical =>
    obtain ⟨hpar, hloc, htot, hden, -⟩ := hVN N (hδ.trans (min_le_left _ _))
      (hE.trans (min_le_left _ _)) (hκ.trans (min_le_left _ _))
      (hθ.trans (min_le_left _ _))
    refine ⟨⟨(fun h => nomatch h), fun _ => hpar⟩, hloc.mono (by linarith), ?_,
      hden.mono (by linarith)⟩
    exact htot.mono (mul_le_mul_of_nonneg_right (by linarith) hCd) hR

/-! ## Reductions to the auxiliary statements -/

/-- The statement `exists_sourceConstruction`, from the normalized root, the stage choice and the
recursive construction. -/
theorem exists_sourceConstruction_proof (n : ℕ) :
    ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n), T.Available n k → k < n + 2 →
      P.IsAdmissible → ∃ D : ConstructionData n k T, D.IsSourceConstruction P := by
  intro k T P hT hk hP
  exact sourceConstruction_of_choices_proof n P (exists_normalizedRoot_proof n P hT hk hP)
    (exists_stageChoice_proof n P hT hk hP)

/-- The statement `partitionFacts_of_construction`, from the stage invariants and the partition
facts they imply. -/
theorem partitionFacts_of_construction_proof (n : ℕ) :
    ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T),
      T.Available n k → k < n + 2 → P.IsAdmissible → D.IsSourceConstruction P →
      D.PartitionFacts P := by
  intro k T P D hT hk hP hD
  exact partitionFacts_of_stageInvariants_proof n P D hP hD
    (stageInvariants_of_construction_proof n P D hT hk hP hD)

/-- The statement `recordsTimeCompatible_of_construction`, from the fitted-time comparison
(given `nodeBeta_le_proof`), the genuine-record compatibility and the passage to all records. -/
theorem recordsTimeCompatible_of_construction_proof (n : ℕ) :
    ∃ C θ₁ A₁ : ℝ, 0 < C ∧ 0 < θ₁ ∧ 0 < A₁ ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
      (D : ConstructionData n k T) (B : ℝ), T.Available n k → k < n + 2 →
      ∀ hP : P.IsAdmissible, 0 < B → P.TailBound k T B → D.IsSourceConstruction P →
      P.θ ≤ θ₁ → A₁ * B ≤ P.a → T = .horizontal → ∀ γ : ℝ, C * (P.θ ^ 2 + B / P.a) ≤ γ →
      RecordsTimeCompatible (D.family P hP.R_pos) (D.centers P) (D.radius P) γ := by
  obtain ⟨C₀, hC₀, hfit⟩ := fittedTime_comparison_of_construction_proof n (nodeBeta_le_proof n)
  obtain ⟨Cb, θ₁, A₁, hCb, hθ₁, hA₁, hgen⟩ := genuineRecords_timeCompatible_proof n C₀ hC₀
  obtain ⟨Cc, hCc, hext⟩ := recordsTimeCompatible_of_genuine_proof n
  refine ⟨Cb + Cc, θ₁, A₁, by linarith, hθ₁, hA₁, ?_⟩
  intro k T P D B hT hk hP hB htail hD hθ hA hH γ hγ
  have hx : 0 ≤ P.θ ^ 2 + B / P.a := add_nonneg (sq_nonneg _) (div_nonneg hB.le hP.a_pos.le)
  have hγb : Cb * (P.θ ^ 2 + B / P.a) ≤ γ :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) hx) hγ
  have hγc : Cc * (P.θ ^ 2 + B / P.a) ≤ γ :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) hx) hγ
  exact hext P D B hT hk hP hB hD hH γ hγc
    (hgen P D B hT hk hP hB htail hD hθ hA hH (hfit P D B hT hk hP hB htail hD hH) γ hγb)

/-- The statement `nodeError_le`, from the node charge data (given coherence, the finite
comparison-incidence bound, center heights, time compatibility, separation facts and the
buffered reference statements) and the total node charge (given
`ChargeCollapse.nodeErrorMass_iUnion_le`). -/
theorem nodeError_le_proof (n : ℕ) :
    ∃ C θ₁ A₁ : ℝ, 0 < C ∧ 0 < θ₁ ∧ 0 < A₁ ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
      (D : ConstructionData n k T) (B : ℝ), T.Available n k → k < n + 2 → P.IsAdmissible →
      0 < B → P.TailBound k T B → D.IsSourceConstruction P → P.θ ≤ θ₁ → A₁ * B ≤ P.a →
      P.ν (D.nodeErrorSet P) ≤ ENNReal.ofReal (C * B * P.R ^ k / P.θ ^ 2) := by
  obtain ⟨Fc, A, Cω, c₁, θ₁, A₁, N₀, hc₁, hθ₁, hA₁, hdata⟩ :=
    nodeChargeData_of_construction_proof
      (fun n => coherent_of_construction_proof n (planeComparison_sq_le_proof n))
      (fun n => ambientSquare_finite_of_construction_proof n (nodeBeta_le_proof n)
        ChargeCollapse.lastWitness_sum)
      (fun n => centerHeight_stoppingParent_of_construction_proof n (planeComparison_sq_le_proof n))
      recordsTimeCompatible_of_construction_proof separationFacts_of_construction_proof
      NeckHubTree.vertical_buffered_reference_proof
      NeckHubTree.horizontal_buffered_reference_proof n
  obtain ⟨C, hC, hcharge⟩ := nodeError_le_of_chargeData_proof
    @ChargeCollapse.nodeErrorMass_iUnion_le n Fc A Cω c₁ N₀ hc₁
  refine ⟨C, θ₁, A₁, hC, hθ₁, hA₁, ?_⟩
  intro k T P D B hT hk hP hB htail hD hθ hA
  exact hcharge P D B hk hP hB htail (hdata P D B hT hk hP hB htail hD hθ hA)

/-- The statement `regionFacts_of_construction`, from the separation facts and compactness of the
center set. -/
theorem regionFacts_of_construction_proof (n : ℕ) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T),
      T.Available n k → k < n + 2 → ∀ hP : P.IsAdmissible, D.IsSourceConstruction P →
      D.RegionFacts P hP.R_pos Cs := by
  obtain ⟨Cs, hCs, hsep⟩ := separationFacts_of_construction_proof n
  refine ⟨Cs, hCs, ?_⟩
  intro k T P D hT hk hP hD
  have h1 := hsep P D hT hk hP hD
  obtain ⟨h2, h3, h4⟩ := compactness_of_separationFacts_proof n P D Cs hT hk hP hD h1
  exact
    { isCompact_centers := h2
      centers_subset := h1.centers_subset
      radius_nonneg := h1.radius_nonneg
      radius_le := h1.radius_le
      stop_separation := h1.stop_separation
      core_separation := h1.core_separation
      initialRadius_le := h1.initialRadius_le
      initialPoint_mem := h1.initialPoint_mem
      initialPoint_near := h1.initialPoint_near
      center_mem := h1.center_mem
      core_limit := h3
      isCompact_core := h4 }

/-- The statement `ambientSquare_of_construction`, from the finiteness of the ambient square
(given `nodeBeta_le_proof` and `ChargeCollapse.lastWitness_sum`), time compatibility and the
thresholds. -/
theorem ambientSquare_of_construction_proof (n : ℕ) :
    ∃ C θ₁ A₁ : ℝ, 0 < C ∧ 0 < θ₁ ∧ 0 < A₁ ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
      (D : ConstructionData n k T) (B : ℝ), T.Available n k → k < n + 2 →
      ∀ hP : P.IsAdmissible, 0 < B → P.TailBound k T B → D.IsSourceConstruction P →
      P.θ ≤ θ₁ → A₁ * B ≤ P.a → ∀ E : ℝ, C * (B / P.a) ≤ E →
      T.SquareBound (D.family P hP.R_pos) E := by
  obtain ⟨C, θa, Aa, hC, hθa, hAa, hfin⟩ :=
    ambientSquare_finite_of_construction_proof n (nodeBeta_le_proof n)
      ChargeCollapse.lastWitness_sum
  obtain ⟨Ct, θt, At, hCt, hθt, hAt, htime⟩ := recordsTimeCompatible_of_construction_proof n
  obtain ⟨θ₀, A, hθ₀, hθ₀₁, hAA, hthr⟩ := exists_neck_thresholds_proof Ct 1 1 1 (min θa θt) 1
    (Aa + At) hCt one_pos one_pos one_pos (lt_min hθa hθt) one_pos (by linarith)
  refine ⟨C, θ₀, A, hC, hθ₀, by linarith, ?_⟩
  intro k T P D B hT hk hP hB htail hD hθ hA E hE
  have hθ' : P.θ ≤ min θa θt := hθ.trans hθ₀₁
  have hAa' : Aa * B ≤ P.a := le_trans (mul_le_mul_of_nonneg_right (by linarith) hB.le) hA
  have hAt' : At * B ≤ P.a := le_trans (mul_le_mul_of_nonneg_right (by linarith) hB.le) hA
  obtain ⟨-, -, -, hγ1⟩ := hthr P.θ B P.a hP.θ_pos hθ hB hA
  have hγ0 : 0 ≤ Ct * (P.θ ^ 2 + B / P.a) :=
    mul_nonneg hCt.le (add_nonneg (sq_nonneg _) (div_nonneg hB.le hP.a_pos.le))
  have hfin' := hfin P D B hT hk hP hB htail hD (hθ'.trans (min_le_left _ _)) hAa'
    (fun hH => ⟨_, hγ0, hγ1, htime P D B hT hk hP hB htail hD (hθ'.trans (min_le_right _ _))
      hAt' hH _ le_rfl⟩)
  cases T with
  | horizontal =>
    exact CoherentFamily.squareBound_of_upTo (fun z : Space n => z.1) (D.family P hP.R_pos) E
      fun N w => ((hfin' N).2 rfl w).trans (ENNReal.ofReal_le_ofReal hE)
  | vertical =>
    exact CoherentFamily.squareBound_of_upTo (fun z : Space n => z) (D.family P hP.R_pos) E
      fun N w => ((hfin' N).1 rfl w).trans (ENNReal.ofReal_le_ofReal hE)

/-! ## The neck of a source -/

/-- The statement `exists_neck_of_source_bundled` (the neck of a source for a bundled setup). -/
theorem exists_neck_of_source_bundled_proof (n : ℕ) :
    ∃ C θ₀ A Cs : ℝ, 1 ≤ C ∧ 0 < θ₀ ∧ 0 < A ∧ 0 < Cs ∧
      ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (B : ℝ), T.Available n k → k < n + 2 →
        P.IsAdmissible → 0 < B → P.TailBound k T B → P.θ ≤ θ₀ → A * B ≤ P.a →
        ∃ (ι : Type) (N : NeckRegion n k T ι P.q P.R (1 / 20) 4 Cs T.sourceSeparation
            (C * Real.sqrt (B / P.a)) (C * (B / P.a)) (C * (P.θ + Real.sqrt (B / P.a))) P.θ
            (C * (P.θ ^ 2 + B / P.a)))
          (Pa : NeckSourcePartition P.S P.f N),
          P.ν = P.ν.restrict Pa.errorSet + P.ν.restrict Pa.coreSet +
              Measure.sum (fun c : N.stopping => P.ν.restrict (Pa.assignment c)) ∧
            P.ν Pa.errorSet ≤ ENNReal.ofReal (C * B * P.R ^ k / P.θ ^ 2) ∧
            N.IsCertified P.ν P.a B C ∧
            ∀ c ∈ N.stopping, c ∉ Pa.terminal →
              CollapsedAssignmentBound T k P.ν (Pa.assignment c) (N.radius c) P.a B C := by
  obtain ⟨CG, δG, EG, κG, θG, γG, hCG, hδG, hEG, hκG, hθG, hγG, hGM⟩ :=
    neck_structure_conclusions_proof n
  obtain ⟨Ce, θe, Ae, hCe, hθe, hAe, herr⟩ := errorSet_le_proof n (nodeError_le_proof n)
  obtain ⟨Cc, hCc, hcoh⟩ := coherent_of_construction_proof n (planeComparison_sq_le_proof n)
  obtain ⟨Ca, θa, Aa, hCa, hθa, hAa, hamb⟩ := ambientSquare_of_construction_proof n
  obtain ⟨Ch, hCh, hheight⟩ :=
    centerHeight_stoppingParent_of_construction_proof n (planeComparison_sq_le_proof n)
  obtain ⟨Ct, θt, At, hCt, hθt, hAt, htime⟩ := recordsTimeCompatible_of_construction_proof n
  obtain ⟨Cs, hCs, hreg⟩ := regionFacts_of_construction_proof n
  obtain ⟨Cf, hCf, hfit⟩ := collapsedFit_le_proof n
  obtain ⟨Cl, hCl, hlow⟩ := core_lower_of_construction_proof n
  obtain ⟨Cm, hCm, hdom⟩ := core_domination_of_construction_proof n
  obtain ⟨Cq, hCq, hsq⟩ := core_square_of_construction_proof n
  obtain ⟨Cη, hCη, heta⟩ := eta_square_of_construction_proof n
  have h6 : 0 ≤ CG * 6 ^ (n + 2) := mul_nonneg (by linarith) (pow_nonneg (by norm_num) _)
  obtain ⟨C, hC1, hC2, hCG', hCG6, hCe', hCc', hCa', hCh', hCt', hCf', hCl', hCm', hCq', hCη'⟩ :
      ∃ C : ℝ, 1 ≤ C ∧ 2 ≤ C ∧ CG ≤ C ∧ CG * 6 ^ (n + 2) ≤ C ∧ Ce ≤ C ∧ Cc ≤ C ∧ Ca ≤ C ∧
        Ch ≤ C ∧ Ct ≤ C ∧ 1 + 2 * Cf ≤ C ∧ Cl ≤ C ∧ Cm ≤ C ∧ Cq ≤ C ∧ Cη ≤ C :=
    ⟨3 + CG + CG * 6 ^ (n + 2) + Ce + Cc + Ca + Ch + Ct + 2 * Cf + Cl + Cm + Cq + Cη,
      by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith⟩
  obtain ⟨θ₀, A, hθ₀, hθ₀₁, hAA, hthr⟩ := exists_neck_thresholds_proof C δG EG κG
    (min (min θG θe) (min θa θt)) γG (Ae + Aa + At) (by linarith) hδG hEG hκG
    (lt_min (lt_min hθG hθe) (lt_min hθa hθt)) hγG (by linarith)
  refine ⟨C, θ₀, A, Cs, hC1, hθ₀, by linarith, hCs, ?_⟩
  intro k T P B hT hk hP hB htail hθ hA
  have hR : 0 < P.R := hP.R_pos
  have ha : 0 < P.a := hP.a_pos
  have hθpos : 0 < P.θ := hP.θ_pos
  obtain ⟨D, hD⟩ := exists_sourceConstruction_proof n P hT hk hP
  have hθ' : P.θ ≤ min (min θG θe) (min θa θt) := hθ.trans hθ₀₁
  have hθG' : P.θ ≤ θG := hθ'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hθe' : P.θ ≤ θe := hθ'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hθa' : P.θ ≤ θa := hθ'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθt' : P.θ ≤ θt := hθ'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hAe' : Ae * B ≤ P.a := le_trans (mul_le_mul_of_nonneg_right (by linarith) hB.le) hA
  have hAa' : Aa * B ≤ P.a := le_trans (mul_le_mul_of_nonneg_right (by linarith) hB.le) hA
  have hAt' : At * B ≤ P.a := le_trans (mul_le_mul_of_nonneg_right (by linarith) hB.le) hA
  obtain ⟨hδth, hEth, hκth, hγth⟩ := hthr P.θ B P.a hθpos hθ hB hA
  have hsqrt : 0 ≤ Real.sqrt (B / P.a) := Real.sqrt_nonneg _
  have hBa : 0 ≤ B / P.a := div_nonneg hB.le ha.le
  have hC0 : 0 ≤ C := by linarith
  have hregD : D.RegionFacts P hR Cs := hreg P D hT hk hP hD
  obtain ⟨hheight1, hheight2⟩ := hheight P D B hT hk hP hB htail hD
  have hfacts : D.NeckFacts P hR Cs (C * Real.sqrt (B / P.a)) (C * (B / P.a))
      (C * (P.θ + Real.sqrt (B / P.a))) (C * (P.θ ^ 2 + B / P.a)) :=
    { available := hT
      parameters :=
        { R_pos := hR
          c₀_pos := by norm_num
          Cd_pos := by norm_num
          Cs_pos := hCs
          σ_pos := T.sourceSeparation_pos
          σ_le_one := T.sourceSeparation_le_one
          δ_nonneg := mul_nonneg hC0 hsqrt
          E_nonneg := mul_nonneg hC0 hBa
          κ_nonneg := mul_nonneg hC0 (add_nonneg hθpos.le hsqrt)
          θ_nonneg := hθpos.le
          γ_nonneg := fun _ => mul_nonneg hC0 (add_nonneg (sq_nonneg _) hBa) }
      region := hregD
      coherent := hcoh P D B hT hk hP hB htail hD _ (mul_le_mul_of_nonneg_right hCc' hsqrt)
      centerHeight := hheight1 _ (mul_le_mul_of_nonneg_right hCh' (add_nonneg hθpos.le hsqrt))
      squareBound := hamb P D B hT hk hP hB htail hD hθa' hAa' _
        (mul_le_mul_of_nonneg_right hCa' hBa)
      stoppingParent_spec := hheight2
      timeCompatible := fun hH => htime P D B hT hk hP hB htail hD hθt' hAt' hH _
        (mul_le_mul_of_nonneg_right hCt' (add_nonneg (sq_nonneg _) hBa)) }
  have hpart : D.PartitionFacts P := partitionFacts_of_construction_proof n P D hT hk hP hD
  refine ⟨ℕ, D.toNeckRegion P hR hfacts, D.toSourcePartition P hR hfacts hpart, ?_, ?_, ?_, ?_⟩
  · exact measure_eq_of_construction_proof n
      (partitionFacts_of_construction_proof n) P D hT hk hP hD
  · exact herr P D B hT hk hP hB htail hD hθe' hAe' C hCe'
  · obtain ⟨hpar, hloc, htot, hden⟩ :=
      hGM (D.toNeckRegion P hR hfacts) hδth hEth hκth hθG' hγth
    have hCGtot : CG * (2 + 4 : ℝ) ^ k ≤ C := by
      have h6k : (2 + 4 : ℝ) ^ k ≤ 6 ^ (n + 2) := by
        rw [show (2 + 4 : ℝ) = 6 by norm_num]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      calc CG * (2 + 4 : ℝ) ^ k ≤ CG * 6 ^ (n + 2) :=
            mul_le_mul_of_nonneg_left h6k (by linarith)
        _ ≤ C := hCG6
    exact
      { isCompact_core := hregD.isCompact_core
        parametrization := hpar.mono_distortion two_pos hC2
        localContent := hloc.mono hCG'
        totalContent := htot.mono hCGtot hR.le
        coreDensity := hden.mono hCG'
        core_lower := hlow P D hT hk hP hD C hCl'
        core_domination := hdom P D hT hk hP hD C hCm'
        core_square := hsq P D B hT hk hP hB htail hD C hCq'
        eta_square := heta P D B hT hk hP hB htail hD C hCη' }
  · intro c hc hterm
    obtain ⟨j, i, hj, hi, rfl, hcont, hrad⟩ := collapsedCenter_spec_proof
      n P D hT hk hP hD c hc hterm
    have hρ : 0 < 5 * P.scale T j := by
      have := P.scale_pos T hR j
      linarith
    have hA : D.assignment P (D.cand j i) ⊆ Metric.ball (D.cand j i) (5 * P.scale T j) := by
      rw [← hrad]
      exact hpart.assignment_subset_ball _ hc
    have := P.finite
    have hcol := ChargeCollapse.collapsedAssignmentBound_of_failure hT P.ν (D.cand j i) hρ
      (D.assignment P (D.cand j i)) hA ha.le hB.le (by linarith : (0 : ℝ) ≤ Cf)
      (fun hr => ⟨not_le.mp fun hle => hcont (Or.inl ⟨hr, hρ, hle⟩),
        hfit P D B hT hk hP hB htail hD j hj i hi⟩)
      (fun hr0 => not_le.mp fun hle => hcont (Or.inr ⟨hr0, hle⟩))
    change CollapsedAssignmentBound T k P.ν (D.assignment P (D.cand j i))
      (D.radius P (D.cand j i)) P.a B C
    rw [hrad]
    obtain ⟨hcol1, hcol2⟩ := hcol
    refine ⟨fun hr => ?_, hcol2⟩
    obtain ⟨L, τ, hL⟩ := hcol1 hr
    refine ⟨L, τ, ?_⟩
    rw [← NeckType.collapseModelSet_eq_lowerModelSet]
    refine le_trans hL (ENNReal.ofReal_le_ofReal ?_)
    have hρk : 0 ≤ (5 * P.scale T j) ^ (k + 2) := pow_nonneg hρ.le _
    have hab : 0 ≤ P.a + B := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCf' hab) hρk

/-- The statement `exists_neck_of_source`: every admissible source carries a neck. -/
theorem exists_neck_of_source_proof (n : ℕ) :
    ∃ C θ₀ A Cs : ℝ, 1 ≤ C ∧ 0 < θ₀ ∧ 0 < A ∧ 0 < Cs ∧
      ∀ (k : ℕ) (T : NeckType), T.Available n k → k < n + 2 →
      ∀ (q : Space n) (R : ℝ) (ν : Measure (Space n)) (S : Set (Space n))
        (f : Space n → ℝ) (B θ a : ℝ),
        0 < R → IsFiniteMeasure ν → MeasurableSet S → S ⊆ Metric.ball q R → ν Sᶜ = 0 →
        IsSourceCutoff S R f → 0 < B →
        (∀ z ∈ S, tailEnergy ν k T.toFamilyKind (f z) z ≤ ENNReal.ofReal B) →
        0 < θ → θ ≤ θ₀ → A * B ≤ a →
        ∃ (ι : Type) (N : NeckRegion n k T ι q R (1 / 20) 4 Cs T.sourceSeparation
            (C * Real.sqrt (B / a)) (C * (B / a)) (C * (θ + Real.sqrt (B / a))) θ
            (C * (θ ^ 2 + B / a)))
          (P : NeckSourcePartition S f N),
          ν = ν.restrict P.errorSet + ν.restrict P.coreSet +
              Measure.sum (fun c : N.stopping => ν.restrict (P.assignment c)) ∧
            ν P.errorSet ≤ ENNReal.ofReal (C * B * R ^ k / θ ^ 2) ∧
            N.IsCertified ν a B C ∧
            ∀ c ∈ N.stopping, c ∉ P.terminal →
              CollapsedAssignmentBound T k ν (P.assignment c) (N.radius c) a B C := by
  obtain ⟨C, θ₀, A, Cs, hC, hθ₀, hA, hCs, h⟩ := exists_neck_of_source_bundled_proof n
  refine ⟨C, θ₀, A, Cs, hC, hθ₀, hA, hCs, ?_⟩
  intro k T hT hk q R ν S f B θ a hR hν hSm hSq hSn hf hB htail hθ hθ' ha
  exact h (⟨ν, hν, S, f, q, R, θ, a⟩ : SourceSetup n) B hT hk
    ⟨hR, hSm, hSq, hSn, hf, hθ, lt_of_lt_of_le (mul_pos hA hB) ha⟩ hB htail hθ' ha

end ParabolicRectifiability
