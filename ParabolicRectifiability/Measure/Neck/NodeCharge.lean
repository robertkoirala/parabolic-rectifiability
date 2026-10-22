import ParabolicRectifiability.Measure.Neck.NodeChargeSetup

/-!
# Node charge data and node error of the source construction

Proofs, in implication form, of the two parts of `nodeError_le`:

* `nodeChargeData_of_construction_proof` proves `nodeChargeData_of_construction` from the
  statements it uses as hypotheses: coherence (`coherent_of_construction`), the finite
  comparison-incidence bound (`ambientSquare_finite_of_construction`), center heights
  (`centerHeight_stoppingParent_of_construction`), time compatibility
  (`recordsTimeCompatible_of_construction`) and the separation facts
  (`separationFacts_of_construction`), and the buffered reference statements
  `vertical_buffered_reference` and `horizontal_buffered_reference` (at universe `0`).
* `nodeError_le_of_chargeData_proof` proves `nodeError_le_of_chargeData` (the total node
  charge and Chebyshev's inequality) from `ChargeCollapse.nodeErrorMass_iUnion_le` (at
  universe `0`), taken as a hypothesis.

Construction of the charging data. The charged nodes of level `j ≥ 1` are the centers
of the continuing candidates of stage `j` (distinct by net separation); level `0` has no
node, so the artificial root is not charged. The cutoff constant is `F_c = 1` (`f < r_j` after
the terminal phase), the witness constant is `A = 2`, the multiplicity is `N₀ = 9^{n+2}`.

* Vertical: `X = Space n`, incidence sets `P(g, r_j)`, reference measures `ω_N` the
  buffered measures `Φ_#(λ_b ⌞ D)` of the truncation `N`; the nodes of one level are
  `r_j`-separated, so at most `3^{n+2}` incidence balls contain a point.
* Horizontal: `X = Spatial n`, incidence sets `B(x_g, r_j)`, `ω_N = F_#(vol ⌞ D)`; time
  compatibility with `γ ≤ 1/64` makes the nodes of one level spatially `r_j/4`-separated,
  so at most `9^n` spatial balls contain a point; the witness bound is the pairwise bridge
  `CoherentFamily.horizontal_occurrence_witness`.

The buffered reference statements are applied to every truncation of the constructed family with
`δ = C₉ √(B/a)`, `E = C₁₀ B/a`, `κ = C₁₁ (θ + √(B/a))`, `γ = C₁₂ (θ² + B/a)`, which are below
the thresholds of those statements for `θ ≤ θ₁` and `a ≥ A₁ B`; the constants `C_ω = max(C_m^V, C_m^H)` and
`c₁ = min(c_b^V, c_b^H) > 0` do not depend on `k`, the type or the truncation.

Coefficient of the total node charge: with `H = max{max(F_c, A + 40), 40}`,
`40^{k+2} (N₀/log 2) (2H/40)^{k+2} B C_ω R^k / c₁ = (N₀/log 2)(2H)^{k+2} B C_ω R^k / c₁
≤ (N₀/log 2)(2H)^{n+3} max(C_ω,0)/c₁ · B R^k` for `k < n + 2`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-! ## Reference measures of the buffered predicates -/

/-- The vertical buffered predicates for every truncation give one reference measure per
truncation, with the total and lower patch masses. -/
theorem ms5_vertical_measures {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι)
    {R Cr Cm cb : ℝ} (h : ∀ N, F.HasVerticalBufferedReference R Cr Cm cb N) :
    ∃ ω : ℕ → Measure (Space n), (∀ N, ω N univ ≤ ENNReal.ofReal (Cm * R ^ (m + 2))) ∧
      ∀ N, ∀ j ≤ N, ∀ a ∈ F.index j, ENNReal.ofReal (cb * F.scale j ^ (m + 2)) ≤
        ω N (Metric.ball (F.center j a) (F.scale j)) := by
  unfold CoherentFamily.HasVerticalBufferedReference at h
  choose G p₀ h1 h2 hω hlow using h
  exact ⟨fun N => Measure.map (timePreservingMap (G N))
    ((parabolicVolume m).restrict (Metric.ball (p₀ N) (Cr * R))), hω, hlow⟩

/-- The horizontal buffered predicates for every truncation give one spatial reference
measure per truncation, with the total and lower patch masses. -/
theorem ms5_horizontal_measures {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι)
    {R Cr Cm cb : ℝ} (h : ∀ N, F.HasHorizontalBufferedReference R Cr Cm cb N) :
    ∃ ω : ℕ → Measure (Spatial n), (∀ N, ω N univ ≤ ENNReal.ofReal (Cm * R ^ m)) ∧
      ∀ N, ∀ j ≤ N, ∀ a ∈ F.index j, ENNReal.ofReal (cb * F.scale j ^ m) ≤
        ω N (Metric.ball (F.center j a).1 (F.scale j)) := by
  unfold CoherentFamily.HasHorizontalBufferedReference at h
  choose G u₀ h1 h2 hω hlow using h
  exact ⟨fun N => Measure.map (G N)
    ((volume : Measure (Spatial m)).restrict (Metric.ball (u₀ N) (Cr * R))), hω, hlow⟩

/-! ## The node charge data -/

/-- **`nodeChargeData_of_construction`**, in implication form: it follows from
`coherent_of_construction`, `ambientSquare_finite_of_construction`,
`centerHeight_stoppingParent_of_construction`, `recordsTimeCompatible_of_construction`,
`separationFacts_of_construction`, `vertical_buffered_reference` and
`horizontal_buffered_reference` (universe `0`). -/
theorem nodeChargeData_of_construction_proof
    (hcoh : ∀ (n : ℕ),
      ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T)
        (B : ℝ), T.Available n k → k < n + 2 → ∀ hP : P.IsAdmissible, 0 < B →
        P.TailBound k T B → D.IsSourceConstruction P → ∀ δ : ℝ, C * Real.sqrt (B / P.a) ≤ δ →
        ∀ N : ℕ, (D.family P hP.R_pos).IsCoherentUpTo T.sourceSeparation δ N)
    (hsq : ∀ (n : ℕ),
      ∃ C θ₁ A₁ : ℝ, 0 < C ∧ 0 < θ₁ ∧ 0 < A₁ ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
        (D : ConstructionData n k T) (B : ℝ), T.Available n k → k < n + 2 →
        ∀ hP : P.IsAdmissible, 0 < B → P.TailBound k T B → D.IsSourceConstruction P →
        P.θ ≤ θ₁ → A₁ * B ≤ P.a →
        (T = .horizontal → ∃ γ : ℝ, 0 ≤ γ ∧ γ ≤ 1 ∧
          RecordsTimeCompatible (D.family P hP.R_pos) (D.centers P) (D.radius P) γ) →
        ∀ N : ℕ,
          (T = .vertical →
            (D.family P hP.R_pos).VerticalSquareBoundUpTo (C * (B / P.a)) N) ∧
          (T = .horizontal →
            (D.family P hP.R_pos).HorizontalSquareBoundUpTo (C * (B / P.a)) N))
    (hht : ∀ (n : ℕ),
      ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T)
        (B : ℝ), T.Available n k → k < n + 2 → ∀ hP : P.IsAdmissible, 0 < B →
        P.TailBound k T B → D.IsSourceConstruction P →
        (∀ κ : ℝ, C * (P.θ + Real.sqrt (B / P.a)) ≤ κ → (D.family P hP.R_pos).HasCenterHeight κ) ∧
        ∀ c ∈ D.centers P, 0 < D.radius P c →
          (D.family P hP.R_pos).IsStoppingParent P.θ c (D.radius P c) (D.stoppingParent P c))
    (htc : ∀ (n : ℕ),
      ∃ C θ₁ A₁ : ℝ, 0 < C ∧ 0 < θ₁ ∧ 0 < A₁ ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
        (D : ConstructionData n k T) (B : ℝ), T.Available n k → k < n + 2 →
        ∀ hP : P.IsAdmissible, 0 < B → P.TailBound k T B → D.IsSourceConstruction P →
        P.θ ≤ θ₁ → A₁ * B ≤ P.a → T = .horizontal → ∀ γ : ℝ, C * (P.θ ^ 2 + B / P.a) ≤ γ →
        RecordsTimeCompatible (D.family P hP.R_pos) (D.centers P) (D.radius P) γ)
    (hsep : ∀ (n : ℕ),
      ∃ Cs : ℝ, 0 < Cs ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
        (D : ConstructionData n k T), T.Available n k → k < n + 2 →
        ∀ hP : P.IsAdmissible, D.IsSourceConstruction P → D.SeparationFacts P hP.R_pos Cs)
    (hvbuf : ∀ (n : ℕ) (σ : ℝ) (_hσ : 0 < σ) (_hσ₁ : σ ≤ 1),
      ∃ δ₀ E₀ κ₀ cb : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < cb ∧
        ∀ Cs : ℝ, 0 < Cs → ∃ Cr Cm : ℝ, 0 < Cr ∧ 0 < Cm ∧
          ∀ {m : ℕ} {ι : Type} (F : CoherentFamily n m ι) (N : ℕ) (q : Space n)
            (R δ E κ : ℝ), 0 < R → 0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → 0 ≤ κ → κ ≤ κ₀ →
            F.IsCoherentUpTo σ δ N → F.VerticalSquareBoundUpTo E N →
            F.HasCenterHeightUpTo κ N →
            F.initialRadius ≤ Cs * R →
            (∀ j ≤ N, ∀ a ∈ F.index j, F.center j a ∈ Metric.ball q (Cs * R)) →
            (∃ x ∈ F.initialPlane.toSet, ‖x - q.1‖ ≤ Cs * R) →
            F.HasVerticalBufferedReference R Cr Cm cb N)
    (hhbuf : ∀ (n : ℕ) (σ : ℝ) (_hσ : 0 < σ) (_hσ₁ : σ ≤ 1),
      ∃ δ₀ E₀ κ₀ cb : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < cb ∧
        ∀ Cs : ℝ, 0 < Cs → ∃ Cr Cm : ℝ, 0 < Cr ∧ 0 < Cm ∧
          ∀ {m : ℕ} {ι : Type} (F : CoherentFamily n m ι) (N : ℕ) (q : Space n)
            (R δ E κ γ : ℝ), 0 < R → 0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → 0 ≤ κ → κ ≤ κ₀ →
            0 ≤ γ → γ ≤ min (σ ^ 2) 1 / 4 →
            F.IsCoherentUpTo σ δ N → F.HorizontalSquareBoundUpTo E N →
            F.HasCenterHeightUpTo κ N → F.IsTimeCompatibleUpTo γ N →
            F.initialRadius ≤ Cs * R →
            (∀ j ≤ N, ∀ a ∈ F.index j, F.center j a ∈ Metric.ball q (Cs * R)) →
            (∃ x ∈ F.initialPlane.toSet, ‖x - q.1‖ ≤ Cs * R) →
            F.HasHorizontalBufferedReference R Cr Cm cb N)
    (n : ℕ) :
    ∃ (Fc A Cω c₁ θ₁ A₁ : ℝ) (N₀ : ℕ), 0 < c₁ ∧ 0 < θ₁ ∧ 0 < A₁ ∧
      ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T) (B : ℝ),
        T.Available n k → k < n + 2 → P.IsAdmissible → 0 < B → P.TailBound k T B →
        D.IsSourceConstruction P → P.θ ≤ θ₁ → A₁ * B ≤ P.a →
        D.NodeChargeData P Fc A Cω c₁ N₀ := by
  obtain ⟨C9, hC9, h9⟩ := hcoh n
  obtain ⟨C10, θ10, A10, hC10, hθ10, hA10, h10⟩ := hsq n
  obtain ⟨C11, hC11, h11⟩ := hht n
  obtain ⟨C12, θ12, A12, hC12, hθ12, hA12, h12⟩ := htc n
  obtain ⟨Cs, hCs, h13⟩ := hsep n
  obtain ⟨δv, Ev, κv, cbv, hδv, hEv, hκv, hcbv, hv⟩ := hvbuf n 1 one_pos le_rfl
  obtain ⟨Crv, Cmv, -, -, hv⟩ := hv Cs hCs
  obtain ⟨δh, Eh, κh, cbh, hδh, hEh, hκh, hcbh, hh⟩ :=
    hhbuf n (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨Crh, Cmh, -, -, hh⟩ := hh Cs hCs
  -- the thresholds of the buffered statements, uniform in the type
  have hδ₀ : 0 < min δv δh := lt_min hδv hδh
  have hE₀ : 0 < min Ev Eh := lt_min hEv hEh
  have hκ₀ : 0 < min κv κh := lt_min hκv hκh
  -- smallness of `√(B/a)`
  obtain ⟨s₀, hs₀, hs₀δ, hs₀κ⟩ : ∃ s₀ : ℝ, 0 < s₀ ∧ C9 * s₀ ≤ min δv δh ∧
      C11 * s₀ ≤ min κv κh / 2 := by
    refine ⟨min (min δv δh / C9) (min κv κh / 2 / C11),
      lt_min (div_pos hδ₀ hC9) (div_pos (half_pos hκ₀) hC11), ?_, ?_⟩
    · calc C9 * min (min δv δh / C9) (min κv κh / 2 / C11) ≤ C9 * (min δv δh / C9) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hC9.le
        _ = min δv δh := mul_div_cancel₀ _ hC9.ne'
    · calc C11 * min (min δv δh / C9) (min κv κh / 2 / C11) ≤ C11 * (min κv κh / 2 / C11) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hC11.le
        _ = min κv κh / 2 := mul_div_cancel₀ _ hC11.ne'
  -- smallness of `B/a`
  obtain ⟨x₀, hx₀, hx₀s, hx₀E, hx₀γ⟩ : ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ ≤ s₀ ^ 2 ∧
      C10 * x₀ ≤ min Ev Eh ∧ C12 * x₀ ≤ 1 / 128 := by
    refine ⟨min (s₀ ^ 2) (min (min Ev Eh / C10) (1 / 128 / C12)),
      lt_min (pow_pos hs₀ 2) (lt_min (div_pos hE₀ hC10) (div_pos (by norm_num) hC12)),
      min_le_left _ _, ?_, ?_⟩
    · calc C10 * min (s₀ ^ 2) (min (min Ev Eh / C10) (1 / 128 / C12)) ≤
            C10 * (min Ev Eh / C10) :=
            mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) hC10.le
        _ = min Ev Eh := mul_div_cancel₀ _ hC10.ne'
    · calc C12 * min (s₀ ^ 2) (min (min Ev Eh / C10) (1 / 128 / C12)) ≤
            C12 * (1 / 128 / C12) :=
            mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) hC12.le
        _ = 1 / 128 := mul_div_cancel₀ _ hC12.ne'
  -- smallness of `θ`
  obtain ⟨θ₁, hθ₁, hθ₁10, hθ₁12, hθ₁κ, hθ₁1, hθ₁γ⟩ : ∃ θ₁ : ℝ, 0 < θ₁ ∧ θ₁ ≤ θ10 ∧
      θ₁ ≤ θ12 ∧ C11 * θ₁ ≤ min κv κh / 2 ∧ θ₁ ≤ 1 ∧ C12 * θ₁ ≤ 1 / 128 := by
    refine ⟨min (min θ10 θ12) (min (min κv κh / 2 / C11) (min 1 (1 / 128 / C12))),
      lt_min (lt_min hθ10 hθ12) (lt_min (div_pos (half_pos hκ₀) hC11)
        (lt_min one_pos (div_pos (by norm_num) hC12))),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      ?_, (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)), ?_⟩
    · calc C11 * min (min θ10 θ12) (min (min κv κh / 2 / C11) (min 1 (1 / 128 / C12))) ≤
            C11 * (min κv κh / 2 / C11) :=
            mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) hC11.le
        _ = min κv κh / 2 := mul_div_cancel₀ _ hC11.ne'
    · calc C12 * min (min θ10 θ12) (min (min κv κh / 2 / C11) (min 1 (1 / 128 / C12))) ≤
            C12 * (1 / 128 / C12) :=
            mul_le_mul_of_nonneg_left
              ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) hC12.le
        _ = 1 / 128 := mul_div_cancel₀ _ hC12.ne'
  have hA₁ : 0 < max (max A10 A12) x₀⁻¹ := lt_max_of_lt_left (lt_max_of_lt_left hA10)
  refine ⟨1, 2, max Cmv Cmh, min cbv cbh, θ₁, max (max A10 A12) x₀⁻¹, 9 ^ (n + 2),
    lt_min hcbv hcbh, hθ₁, hA₁, ?_⟩
  intro k T P D B hT hk hP hB htail hD hθ hA
  have hR := hP.R_pos
  have ha := hP.a_pos
  have hθ0 := hP.θ_pos
  -- the parameter bounds
  have hθ10' : P.θ ≤ θ10 := hθ.trans hθ₁10
  have hθ12' : P.θ ≤ θ12 := hθ.trans hθ₁12
  have hA10' : A10 * B ≤ P.a :=
    (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hB.le).trans hA
  have hA12' : A12 * B ≤ P.a :=
    (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) hB.le).trans hA
  have hx : B / P.a ≤ x₀ := by
    have h1 : x₀⁻¹ * B ≤ P.a :=
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hB.le).trans hA
    have h2 : B ≤ x₀ * P.a := by
      have h3 : x₀ * (x₀⁻¹ * B) = B := by rw [← mul_assoc, mul_inv_cancel₀ hx₀.ne', one_mul]
      calc B = x₀ * (x₀⁻¹ * B) := h3.symm
        _ ≤ x₀ * P.a := mul_le_mul_of_nonneg_left h1 hx₀.le
    rw [div_le_iff₀ ha]
    exact h2
  have hy0 : 0 ≤ B / P.a := div_nonneg hB.le ha.le
  have hsqrt : Real.sqrt (B / P.a) ≤ s₀ :=
    calc Real.sqrt (B / P.a) ≤ Real.sqrt (s₀ ^ 2) := Real.sqrt_le_sqrt (hx.trans hx₀s)
      _ = s₀ := Real.sqrt_sq hs₀.le
  have hδ : C9 * Real.sqrt (B / P.a) ≤ min δv δh :=
    (mul_le_mul_of_nonneg_left hsqrt hC9.le).trans hs₀δ
  have hE : C10 * (B / P.a) ≤ min Ev Eh := (mul_le_mul_of_nonneg_left hx hC10.le).trans hx₀E
  have hκ : C11 * (P.θ + Real.sqrt (B / P.a)) ≤ min κv κh := by
    have h1 : C11 * P.θ ≤ min κv κh / 2 := (mul_le_mul_of_nonneg_left hθ hC11.le).trans hθ₁κ
    have h2 : C11 * Real.sqrt (B / P.a) ≤ min κv κh / 2 :=
      (mul_le_mul_of_nonneg_left hsqrt hC11.le).trans hs₀κ
    rw [mul_add]
    linarith
  have hγ : C12 * (P.θ ^ 2 + B / P.a) ≤ 1 / 64 := by
    have hθ1 : P.θ ≤ 1 := hθ.trans hθ₁1
    have h1 : P.θ ^ 2 ≤ θ₁ := by
      rw [sq]
      exact (mul_le_of_le_one_right hθ0.le hθ1).trans hθ
    have h2 : C12 * P.θ ^ 2 ≤ 1 / 128 := (mul_le_mul_of_nonneg_left h1 hC12.le).trans hθ₁γ
    have h3 : C12 * (B / P.a) ≤ 1 / 128 := (mul_le_mul_of_nonneg_left hx hC12.le).trans hx₀γ
    rw [mul_add]
    linarith
  have hγ0 : 0 ≤ C12 * (P.θ ^ 2 + B / P.a) := mul_nonneg hC12.le (add_nonneg (sq_nonneg _) hy0)
  have hγ1 : C12 * (P.θ ^ 2 + B / P.a) ≤ 1 := hγ.trans (by norm_num)
  have hδ0 : 0 ≤ C9 * Real.sqrt (B / P.a) := mul_nonneg hC9.le (Real.sqrt_nonneg _)
  have hE0 : 0 ≤ C10 * (B / P.a) := mul_nonneg hC10.le hy0
  have hκ0 : 0 ≤ C11 * (P.θ + Real.sqrt (B / P.a)) :=
    mul_nonneg hC11.le (add_nonneg hθ0.le (Real.sqrt_nonneg _))
  -- the facts shared by both types
  have hS := h13 P D hT hk hP hD
  have hcohN := h9 P D B hT hk hP hB htail hD _ le_rfl
  have hcH : ∀ N, (D.family P hP.R_pos).HasCenterHeightUpTo
      (C11 * (P.θ + Real.sqrt (B / P.a))) N :=
    fun N j _ a ha => (h11 P D B hT hk hP hB htail hD).1 _ le_rfl j a ha
  have hinit : (D.family P hP.R_pos).initialRadius ≤ Cs * P.R := hS.initialRadius_le
  have hcent : ∀ N, ∀ j ≤ N, ∀ a ∈ (D.family P hP.R_pos).index j,
      (D.family P hP.R_pos).center j a ∈ Metric.ball P.q (Cs * P.R) :=
    fun N j _ a ha => hS.center_mem j a ha
  have hpl : ∃ x ∈ (D.family P hP.R_pos).initialPlane.toSet, ‖x - P.q.1‖ ≤ Cs * P.R :=
    ⟨D.rootCenter.1, hS.initialPoint_mem, hS.initialPoint_near⟩
  cases T with
  | horizontal =>
    have htime := h12 P D B hT hk hP hB htail hD hθ12' hA12' rfl _ le_rfl
    have hsqN : ∀ N, (D.family P hP.R_pos).HorizontalSquareBoundUpTo (C10 * (B / P.a)) N :=
      fun N => (h10 P D B hT hk hP hB htail hD hθ10' hA10'
        (fun _ => ⟨_, hγ0, hγ1, htime⟩) N).2 rfl
    have hmin : min ((1 / 4 : ℝ) ^ 2) 1 / 4 = 1 / 64 := by
      rw [min_eq_left (by norm_num)]
      norm_num
    have hbuf : ∀ N, (D.family P hP.R_pos).HasHorizontalBufferedReference P.R Crh Cmh cbh N :=
      fun N => hh (D.family P hP.R_pos) N P.q P.R _ _ _ _ hR hδ0 (hδ.trans (min_le_right _ _))
        hE0 (hE.trans (min_le_right _ _)) hκ0 (hκ.trans (min_le_right _ _)) hγ0
        (hγ.trans hmin.ge) (hcohN N) (hsqN N) (hcH N)
        (fun i _ j _ a ha b hb => htime (Sum.inl (i, a)) (Sum.inl (j, b)) ha hb) hinit
        (hcent N) hpl
    obtain ⟨ω, hω, hlow⟩ := ms5_horizontal_measures _ hbuf
    refine ms5_nodeChargeData_of_incidence P D hT hP hD 1 2 (max Cmv Cmh) (min cbv cbh)
      (9 ^ (n + 2)) le_rfl
      (fun j g => Metric.ball g.1 (coherentScale (NeckType.horizontal.rootRadius P.R) j)) ω
      (fun _ _ _ => measurableSet_ball) ?_ ?_ ?_ ?_
    · intro x j
      classical
      exact le_trans (ms5_horizontal_card_le P D hR hD hγ0 (hγ.trans le_rfl) htime j x _
        (Finset.filter_subset _ _) fun g hg => (Finset.mem_filter.1 hg).2)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    · intro x j g hg hxg j' hjj y hy hxy
      exact ms5_horizontal_witness P D hR hγ0 hγ1 htime hjj hg hy hxg hxy
    · intro N
      refine (hω N).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hR.le _)
    · intro N j hjN g hg
      obtain ⟨hj, i, hi, hc, rfl⟩ := ms5_mem_nodes.1 hg
      have hiF : i ∈ (D.family P hR).index j := by
        rw [ms5_family_index D P hR hj]
        exact ms5_mem_contIndex.2 ⟨hi, hc⟩
      have h := hlow N j hjN i hiF
      rw [ms5_family_center D P hR hj] at h
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
      exact mul_le_mul_of_nonneg_right (min_le_right _ _)
        (pow_nonneg (P.scale_pos _ hR j).le _)
  | vertical =>
    have hrk : NeckType.vertical.rank k + 2 = k :=
      Nat.sub_add_cancel (show 2 ≤ k ∧ k ≤ n + 2 from hT).1
    have hsqN : ∀ N, (D.family P hP.R_pos).VerticalSquareBoundUpTo (C10 * (B / P.a)) N :=
      fun N => (h10 P D B hT hk hP hB htail hD hθ10' hA10' (fun h => by cases h) N).1 rfl
    have hbuf : ∀ N, (D.family P hP.R_pos).HasVerticalBufferedReference P.R Crv Cmv cbv N :=
      fun N => hv (D.family P hP.R_pos) N P.q P.R _ _ _ hR hδ0 (hδ.trans (min_le_left _ _))
        hE0 (hE.trans (min_le_left _ _)) hκ0 (hκ.trans (min_le_left _ _)) (hcohN N) (hsqN N)
        (hcH N) hinit (hcent N) hpl
    obtain ⟨ω, hω, hlow⟩ := ms5_vertical_measures _ hbuf
    rw [hrk] at hω hlow
    refine ms5_nodeChargeData_of_incidence P D hT hP hD 1 2 (max Cmv Cmh) (min cbv cbh)
      (9 ^ (n + 2)) le_rfl
      (fun j g => Metric.ball g (coherentScale (NeckType.vertical.rootRadius P.R) j)) ω
      (fun _ _ _ => measurableSet_ball) ?_ ?_ ?_ ?_
    · intro x j
      classical
      exact le_trans (ms5_vertical_card_le P D hR hD j x _ (Finset.filter_subset _ _)
        fun g hg => (Finset.mem_filter.1 hg).2) (Nat.pow_le_pow_left (by norm_num) _)
    · intro x j g _ hxg j' hjj y _ hxy
      exact ms5_vertical_witness (T := .vertical) P hR hjj hxg hxy
    · intro N
      refine (hω N).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hR.le _)
    · intro N j hjN g hg
      obtain ⟨hj, i, hi, hc, rfl⟩ := ms5_mem_nodes.1 hg
      have hiF : i ∈ (D.family P hR).index j := by
        rw [ms5_family_index D P hR hj]
        exact ms5_mem_contIndex.2 ⟨hi, hc⟩
      have h := hlow N j hjN i hiF
      rw [ms5_family_center D P hR hj] at h
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
      exact mul_le_mul_of_nonneg_right (min_le_left _ _)
        (pow_nonneg (P.scale_pos _ hR j).le _)

/-! ## The node error -/

open Classical in
/-- **`nodeError_le_of_chargeData`**, in implication form, from
`ChargeCollapse.nodeErrorMass_iUnion_le` (universe `0`): apply the endpoint with `H = max{max(F_c, A + 40), 40}`, use the error coverage, and divide
by `θ² > 0`; the coefficient `(N₀/log 2)(2H)^{k+2} C_ω/c₁` is bounded uniformly for
`k < n + 2` with `max(C_ω, 0)`. -/
theorem nodeError_le_of_chargeData_proof
    (hU : ∀ {X : Type} [MeasurableSpace X] {n : ℕ}
      (μ : Measure (Space n)) [IsFiniteMeasure μ] (k : ℕ) (F : FamilyKind) (S : Set (Space n))
      (f : Space n → ℝ) (B : ℝ)
      (_htail : ∀ y ∈ S, ∫⁻ s in Ioi (f y), betaSq μ k F y s ∂scaleMeasure ≤ ENNReal.ofReal B)
      (r₀ : ℝ) (_hr₀ : 0 < r₀) (I : ℕ → Finset (Space n)) (_hS : ∀ j, ∀ g ∈ I j, g ∈ S) (Fc : ℝ)
      (_hf : ∀ j, ∀ g ∈ I j, f g ≤ Fc * coherentScale r₀ j) (E : ℕ → Space n → Set X)
      (_hE : ∀ j, ∀ g ∈ I j, MeasurableSet (E j g)) (N₀ : ℕ)
      (_hmult : ∀ (x : X) (j : ℕ), ((I j).filter fun g => x ∈ E j g).card ≤ N₀) (A : ℝ)
      (_hwit : ∀ (x : X) (j : ℕ), ∀ g ∈ I j, x ∈ E j g → ∀ j', j ≤ j' →
        ∀ y ∈ I j', x ∈ E j' y → dist g y ≤ A * coherentScale r₀ j)
      (ω : ℕ → Measure X) (C₁ c₁ R : ℝ) (_hc₁ : 0 < c₁)
      (_hω : ∀ N, ω N univ ≤ ENNReal.ofReal (C₁ * R ^ k))
      (_hlow : ∀ N, ∀ j ≤ N, ∀ g ∈ I j,
        ENNReal.ofReal (c₁ * coherentScale r₀ j ^ k) ≤ ω N (E j g))
      (H : ℝ) (_hH₁ : Fc ≤ H) (_hH₂ : A + 40 ≤ H)
      (θ : ℝ) (_hθ : 0 < θ) (Pm : ℕ → Space n → Models n k F) (e : ℕ → Space n → Set (Space n))
      (_hfit : ∀ j, ∀ g ∈ I j, fit μ (Pm j g) g (40 * coherentScale r₀ j) ≤
        ENNReal.ofReal ((40 * coherentScale r₀ j) ^ (k + 2)) *
          betaSq μ k F g (40 * coherentScale r₀ j))
      (_hem : ∀ j, ∀ g ∈ I j, MeasurableSet (e j g))
      (_he : ∀ j, ∀ g ∈ I j, e j g ⊆ Metric.ball g (coherentScale r₀ j))
      (_htube : ∀ j, ∀ g ∈ I j, ∀ z ∈ e j g,
        ENNReal.ofReal ((θ * coherentScale r₀ j) ^ 2) < modelCost (Pm j g) z),
      ENNReal.ofReal (θ ^ 2) * μ (⋃ j, ⋃ g ∈ I j, e j g) ≤
        ENNReal.ofReal (40 ^ (k + 2)) *
          (ENNReal.ofReal (N₀ / Real.log 2 * (2 * H / 40) ^ (k + 2) * B) *
            ENNReal.ofReal (C₁ * R ^ k / c₁)))
    (n : ℕ) :
    ∀ (Fc A Cω c₁ : ℝ) (N₀ : ℕ), 0 < c₁ → ∃ C : ℝ, 0 < C ∧
      ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T) (B : ℝ),
        k < n + 2 → P.IsAdmissible → 0 < B → P.TailBound k T B →
        D.NodeChargeData P Fc A Cω c₁ N₀ →
        P.ν (D.nodeErrorSet P) ≤ ENNReal.ofReal (C * B * P.R ^ k / P.θ ^ 2) := by
  intro Fc A Cω c₁ N₀ hc₁
  obtain ⟨H, hH₁, hH₂, hH40⟩ : ∃ H : ℝ, Fc ≤ H ∧ A + 40 ≤ H ∧ 40 ≤ H :=
    ⟨max (max Fc (A + 40)) 40, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _⟩
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hH0 : 0 ≤ 2 * H := by linarith
  have hK0 : 0 ≤ (N₀ : ℝ) / Real.log 2 * (2 * H) ^ (n + 3) * max Cω 0 / c₁ :=
    div_nonneg (mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hlog.le)
      (pow_nonneg hH0 _)) (le_max_right _ _)) hc₁.le
  refine ⟨(N₀ : ℝ) / Real.log 2 * (2 * H) ^ (n + 3) * max Cω 0 / c₁ + 1, by linarith, ?_⟩
  intro k T P D B hk hP hB htail hdata
  have := P.finite
  have hR := hP.R_pos
  have hθ := hP.θ_pos
  unfold ConstructionData.NodeChargeData at hdata
  obtain ⟨X, hX, I, E, ω, Pm, e, hI0, hS, hf, hE, hmult, hwit, hω, hlow, hfit, hem, he, htube,
    hcover⟩ := hdata
  have h := hU P.ν k T.toFamilyKind P.S P.f B htail (T.rootRadius P.R) (T.rootRadius_pos hR) I
    hS Fc hf E hE N₀ hmult A hwit ω Cω c₁ P.R hc₁ hω hlow H hH₁ hH₂ P.θ hθ Pm e hfit hem he
    htube
  -- the coefficient
  have ha0 : 0 ≤ (N₀ : ℝ) / Real.log 2 * (2 * H / 40) ^ (k + 2) * B :=
    mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hlog.le)
      (pow_nonneg (by linarith) _)) hB.le
  have hb0 : 0 ≤ max Cω 0 * P.R ^ k / c₁ :=
    div_nonneg (mul_nonneg (le_max_right _ _) (pow_nonneg hR.le k)) hc₁.le
  have hmono : ENNReal.ofReal (Cω * P.R ^ k / c₁) ≤ ENNReal.ofReal (max Cω 0 * P.R ^ k / c₁) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hR.le k)) hc₁.le)
  have hkey : (40 : ℝ) ^ (k + 2) *
      ((N₀ : ℝ) / Real.log 2 * (2 * H / 40) ^ (k + 2) * B * (max Cω 0 * P.R ^ k / c₁)) ≤
      ((N₀ : ℝ) / Real.log 2 * (2 * H) ^ (n + 3) * max Cω 0 / c₁ + 1) * B * P.R ^ k := by
    have h1 : (40 : ℝ) ^ (k + 2) * (2 * H / 40) ^ (k + 2) = (2 * H) ^ (k + 2) := by
      rw [← mul_pow]
      congr 1
      ring
    have h2 : (2 * H) ^ (k + 2) ≤ (2 * H) ^ (n + 3) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hX0 : 0 ≤ (N₀ : ℝ) / Real.log 2 * max Cω 0 / c₁ * (B * P.R ^ k) :=
      mul_nonneg (div_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hlog.le)
        (le_max_right _ _)) hc₁.le) (mul_nonneg hB.le (pow_nonneg hR.le k))
    have hBR : 0 ≤ B * P.R ^ k := mul_nonneg hB.le (pow_nonneg hR.le k)
    calc (40 : ℝ) ^ (k + 2) *
          ((N₀ : ℝ) / Real.log 2 * (2 * H / 40) ^ (k + 2) * B * (max Cω 0 * P.R ^ k / c₁))
        = ((40 : ℝ) ^ (k + 2) * (2 * H / 40) ^ (k + 2)) *
            ((N₀ : ℝ) / Real.log 2 * max Cω 0 / c₁ * (B * P.R ^ k)) := by ring
      _ = (2 * H) ^ (k + 2) * ((N₀ : ℝ) / Real.log 2 * max Cω 0 / c₁ * (B * P.R ^ k)) := by
          rw [h1]
      _ ≤ (2 * H) ^ (n + 3) * ((N₀ : ℝ) / Real.log 2 * max Cω 0 / c₁ * (B * P.R ^ k)) :=
          mul_le_mul_of_nonneg_right h2 hX0
      _ = ((N₀ : ℝ) / Real.log 2 * (2 * H) ^ (n + 3) * max Cω 0 / c₁) * (B * P.R ^ k) := by
          ring
      _ ≤ ((N₀ : ℝ) / Real.log 2 * (2 * H) ^ (n + 3) * max Cω 0 / c₁ + 1) * (B * P.R ^ k) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hBR
      _ = ((N₀ : ℝ) / Real.log 2 * (2 * H) ^ (n + 3) * max Cω 0 / c₁ + 1) * B * P.R ^ k := by
          ring
  have hbound : ENNReal.ofReal (P.θ ^ 2) * P.ν (⋃ j, ⋃ g ∈ I j, e j g) ≤
      ENNReal.ofReal (((N₀ : ℝ) / Real.log 2 * (2 * H) ^ (n + 3) * max Cω 0 / c₁ + 1) * B *
        P.R ^ k) := by
    refine h.trans ?_
    calc ENNReal.ofReal (40 ^ (k + 2)) *
          (ENNReal.ofReal ((N₀ : ℝ) / Real.log 2 * (2 * H / 40) ^ (k + 2) * B) *
            ENNReal.ofReal (Cω * P.R ^ k / c₁))
        ≤ ENNReal.ofReal (40 ^ (k + 2)) *
          (ENNReal.ofReal ((N₀ : ℝ) / Real.log 2 * (2 * H / 40) ^ (k + 2) * B) *
            ENNReal.ofReal (max Cω 0 * P.R ^ k / c₁)) :=
          mul_le_mul_right (mul_le_mul_right hmono _) _
      _ = ENNReal.ofReal ((40 : ℝ) ^ (k + 2) *
            ((N₀ : ℝ) / Real.log 2 * (2 * H / 40) ^ (k + 2) * B * (max Cω 0 * P.R ^ k / c₁))) := by
          rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 40 ^ (k + 2) by positivity),
            ENNReal.ofReal_mul ha0]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hkey
  have hν : P.ν (D.nodeErrorSet P) ≤ P.ν (⋃ j, ⋃ g ∈ I j, e j g) := measure_mono hcover
  have hθ2 : 0 < P.θ ^ 2 := pow_pos hθ 2
  rw [ENNReal.ofReal_div_of_pos hθ2,
    ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hθ2).ne')
      (Or.inl ENNReal.ofReal_ne_top), mul_comm (P.ν (D.nodeErrorSet P))]
  exact (mul_le_mul_right hν _).trans hbound

end ParabolicRectifiability
