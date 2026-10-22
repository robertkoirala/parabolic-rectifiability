import ParabolicRectifiability.Geometry.Neck.Conclusions

/-!
# Neck, part 3: the neck structure theorem

The neck structure theorems `vertical_neck_structure` and `horizontal_neck_structure`
are assembled here from the chart and buffer theorems and the neck-level estimates.

**Inputs** (explicit hypotheses):

* the chart theorem of the neck's type (`vertical_coherent_chart`,
  `horizontal_coherent_chart`) and the buffer theorem of the neck's type
  (`vertical_buffered_reference`, `horizontal_buffered_reference`);
* the neck-level statements:
  - vertical: `vertical_hasParametrization_of_chart` (exact attachment applied to the
    chart), `vertical_localContent_of_parametrization` (local content),
    `vertical_coreLowerDensity_of_parametrization` (lower density of the core);
  - horizontal: `horizontal_dist_eq_of_mem_centers` (spatial projection is
    isometric on the centers), `horizontal_hasParametrization_of_chart` (Euclidean
    exact attachment and the physical time on the compact preimage),
    `horizontal_localContent_of_parametrization`, `horizontal_coreLowerDensity_of_parametrization`.

**Proved here**: the total content bound from the local one at the testing
radius `(2 + C_d) R` (`totalContent_of_localContent`), the core's upper growth from the
local content bound (`coreUpper_of_localContent`), occurrence time compatibility from
record time compatibility (`isTimeCompatible_of_records`), and the stopping numerics
`C·10·(θ+δ)·d ≤ 2ζ d` for `θ, δ ≤ ζ/(10C)`, `ζ = min(c₀,1)/720`.

**Constants.** The buffer functions
`c_b(σ), C_r(σ, C_*), C_m(σ, C_*)` are chosen from the buffer theorem before `c₀` (by
choice, for `σ ∈ (0,1]`, `C_* > 0`; value `1` elsewhere); the content constant
`C(n, c₀) ≥ 1` is that of the local content statement; the thresholds are
`δ₀ = min(δ₀^chart, δ₀^buffer, ζ/(10 C^chart))`, `E₀ = min(E₀^chart, E₀^buffer)`,
`κ₀ = min(κ₀^chart, κ₀^buffer)`, `θ₀ = ζ/(10 C^chart)`, depending on `n, σ, c₀` only.
-/

noncomputable section

namespace ParabolicRectifiability

namespace NeckHubTree

open MeasureTheory Set
open scoped ENNReal

universe u

section Helpers

variable {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}

/-- The core's own Hausdorff measure has upper `k`-growth with the local content constant. -/
theorem coreUpper_of_localContent (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ) {C : ℝ}
    (h : N.HasLocalContentBound C) (z : Space n) (s : ℝ) (hs : 0 < s) :
    (hausdorffP n k).restrict N.core (Metric.ball z s) ≤ ENNReal.ofReal (C * s ^ k) := by
  rw [Measure.restrict_apply measurableSet_ball, Set.inter_comm]
  exact le_trans le_self_add (h z s hs)

/-- `HasCoreDensity` from the local content bound and the almost-everywhere lower density. -/
theorem coreDensity_of_localContent (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ) {C : ℝ}
    (h : N.HasLocalContentBound C)
    (hlow : ∀ᵐ z ∂(hausdorffP n k).restrict N.core, ∃ a r₀ : ℝ, 0 < a ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        ENNReal.ofReal (a * r ^ k) ≤ (hausdorffP n k).restrict N.core (Metric.ball z r)) :
    N.HasCoreDensity C :=
  ⟨coreUpper_of_localContent N h, hlow⟩

/-- **Total content** (a consequence of the local bound): the local bound at the testing
radius `(2 + C_d) R` about `q` contains every center and every stopping radius. -/
theorem totalContent_of_localContent (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ)
    {C : ℝ} (h : N.HasLocalContentBound C) : N.HasTotalContentBound (C * (2 + Cd) ^ k) := by
  have hR := N.parameters.R_pos
  have hCd := N.parameters.Cd_pos
  have hs : 0 < (2 + Cd) * R := mul_pos (by linarith) hR
  have hRs : R < (2 + Cd) * R := by nlinarith [mul_pos hCd hR]
  have hmem : ∀ c ∈ N.centers, c ∈ Metric.ball q ((2 + Cd) * R) := fun c hc =>
    Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 (N.centers_subset hc)) hRs)
  have hcore : N.core ∩ Metric.ball q ((2 + Cd) * R) = N.core :=
    Set.inter_eq_left.2 fun c hc => hmem c hc.1
  have hstop : N.stopping ∩ Metric.ball q ((2 + Cd) * R) ∩ {c | N.radius c ≤ (2 + Cd) * R} =
      N.stopping := by
    refine Set.Subset.antisymm (fun c hc => hc.1.1) fun c hc => ⟨⟨hc, hmem c hc.1⟩, ?_⟩
    show N.radius c ≤ (2 + Cd) * R
    have h1 := N.radius_le c hc.1
    nlinarith
  have hloc := h q ((2 + Cd) * R) hs
  rw [hcore, hstop] at hloc
  show hausdorffP n k N.core + ∑' c : ↥N.stopping, ENNReal.ofReal (N.radius c ^ k) ≤
    ENNReal.ofReal (C * (2 + Cd) ^ k * R ^ k)
  refine hloc.trans (le_of_eq ?_)
  rw [mul_pow, ← mul_assoc]

end Helpers

/-- Occurrence time compatibility (`IsTimeCompatible`) is the occurrence part of record time
compatibility (`RecordsTimeCompatible`). -/
theorem isTimeCompatible_of_records {n m : ℕ} {ι : Type*} {F : CoherentFamily n m ι}
    {C : Set (Space n)} {d : Space n → ℝ} {γ : ℝ} (h : RecordsTimeCompatible F C d γ) :
    F.IsTimeCompatible γ :=
  fun _ i _ j _ a ha b hb => h (.inl (i, a)) (.inl (j, b)) ha hb

/-- Stopping numerics: `θ, δ ≤ ζ/(10C)` give
`C·10·(θ+δ)·d ≤ 2ζ d`. -/
theorem stopping_le_of_small {C θ δ ζ d : ℝ} (hC : 0 < C) (hθ : θ ≤ ζ / (10 * C))
    (hδ : δ ≤ ζ / (10 * C)) (hd : 0 ≤ d) : C * 10 * (θ + δ) * d ≤ 2 * ζ * d := by
  have h10 : 0 < 10 * C := by linarith
  have h1 : θ * (10 * C) ≤ ζ := (le_div_iff₀ h10).1 hθ
  have h2 : δ * (10 * C) ≤ ζ := (le_div_iff₀ h10).1 hδ
  have h3 : C * 10 * (θ + δ) = θ * (10 * C) + δ * (10 * C) := by ring
  rw [h3]
  exact mul_le_mul_of_nonneg_right (by linarith) hd

/-- **Vertical neck structure** from the chart and buffer theorems and three neck-level
statements. The conclusion is the statement of `vertical_neck_structure`. Proof: the chart
theorem applied to the neck's family covers the core (level limits) and places every stopping center within
`C·10·(θ+δ)·d_c ≤ 2ζ d_c` of the chart at its own time; the exact attachment corrects the
chart to an exact parametrization with distortion `2`; the local content statement gives the local
bound, whose consequences are the total bound and upper growth; the density statement gives the
lower density; the buffer theorem, applied to every truncation, gives the buffers. -/
theorem vertical_neck_structure_of_hubs
    (h1 : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ 1 →
      ∃ δ₀ E₀ κ₀ C : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < C ∧
        ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (δ E : ℝ),
          0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ →
          F.IsCoherent σ δ → F.VerticalSquareBound E →
          ∃ G : Spatial m → ℝ → Spatial n,
            (∀ p p' : Space m,
              4 / 5 * dist p p' ≤ dist (timePreservingMap G p) (timePreservingMap G p') ∧
                dist (timePreservingMap G p) (timePreservingMap G p') ≤ 11 / 10 * dist p p') ∧
            (∀ (u : Spatial m) (t s : ℝ), ‖G u t - G u s‖ ≤ C * δ * Real.sqrt |t - s|) ∧
            IsClosed (Set.range (timePreservingMap G)) ∧
            ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ₀ → F.HasCenterHeight κ →
              (∀ z : Space n, F.IsLevelLimit z → z ∈ Set.range (timePreservingMap G)) ∧
              ∀ θ : ℝ, 0 ≤ θ → ∀ (c : Space n) (d : ℝ) (p : Option (ℕ × ι)),
                F.IsStoppingParent θ c d p →
                  ∃ u : Spatial m, ‖G u c.2.val - c.1‖ ≤ C * 10 * (θ + δ) * d)
    (h3 : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ 1 →
      ∃ δ₀ E₀ κ₀ cb : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < cb ∧
        ∀ Cs : ℝ, 0 < Cs → ∃ Cr Cm : ℝ, 0 < Cr ∧ 0 < Cm ∧
          ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (N : ℕ) (q : Space n)
            (R δ E κ : ℝ), 0 < R → 0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → 0 ≤ κ → κ ≤ κ₀ →
            F.IsCoherentUpTo σ δ N → F.VerticalSquareBoundUpTo E N →
            F.HasCenterHeightUpTo κ N →
            F.initialRadius ≤ Cs * R →
            (∀ j ≤ N, ∀ a ∈ F.index j, F.center j a ∈ Metric.ball q (Cs * R)) →
            (∃ x ∈ F.initialPlane.toSet, ‖x - q.1‖ ≤ Cs * R) →
            F.HasVerticalBufferedReference R Cr Cm cb N)
    (hpar : ∀ {n k : ℕ} {ι : Type u} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
      (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ)
      (G : Spatial (k - 2) → ℝ → Spatial n),
      (∀ p p' : Space (k - 2),
        4 / 5 * dist p p' ≤ dist (timePreservingMap G p) (timePreservingMap G p') ∧
          dist (timePreservingMap G p) (timePreservingMap G p') ≤ 11 / 10 * dist p p') →
      N.core ⊆ Set.range (timePreservingMap G) →
      (∀ c ∈ N.stopping, ∃ u : Spatial (k - 2),
        ‖G u c.2.val - c.1‖ ≤ 2 * (min c₀ 1 / 720) * N.radius c) →
      N.HasVerticalParametrization 2)
    (hcontent : ∀ (n : ℕ) (c₀ : ℝ), 0 < c₀ → ∃ C : ℝ, 1 ≤ C ∧
      ∀ {k : ℕ} {ι : Type u} {q : Space n} {R Cd Cs σ δ E κ θ γ : ℝ}
        (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ),
        N.HasVerticalParametrization 2 → N.HasLocalContentBound C)
    (hlower : ∀ {n k : ℕ} {ι : Type u} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
      (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ),
      N.HasVerticalParametrization 2 →
        ∀ᵐ z ∂(hausdorffP n k).restrict N.core, ∃ a r₀ : ℝ, 0 < a ∧ 0 < r₀ ∧
          ∀ r : ℝ, 0 < r → r ≤ r₀ →
            ENNReal.ofReal (a * r ^ k) ≤ (hausdorffP n k).restrict N.core (Metric.ball z r)) :
    ∀ n : ℕ,
    ∃ (cb : ℝ → ℝ) (Cr Cm : ℝ → ℝ → ℝ),
      (∀ σ : ℝ, 0 < σ → σ ≤ 1 →
        0 < cb σ ∧ ∀ Cs : ℝ, 0 < Cs → 0 < Cr σ Cs ∧ 0 < Cm σ Cs) ∧
      ∀ c₀ : ℝ, 0 < c₀ → ∃ C : ℝ, 1 ≤ C ∧ ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
        ∃ δ₀ E₀ κ₀ θ₀ : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < θ₀ ∧
          ∀ {k : ℕ} {ι : Type u} {q : Space n} {R Cd Cs δ E κ θ γ : ℝ}
            (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ),
            δ ≤ δ₀ → E ≤ E₀ → κ ≤ κ₀ → θ ≤ θ₀ →
            N.HasVerticalParametrization 2 ∧ N.HasLocalContentBound C ∧
              N.HasTotalContentBound (C * (2 + Cd) ^ k) ∧ N.HasCoreDensity C ∧
              ∀ M : ℕ, N.family.HasVerticalBufferedReference R (Cr σ Cs) (Cm σ Cs) (cb σ) M := by
  intro n
  classical
  -- the buffer constants, as functions of `σ` and `C_*`, from the buffer theorem
  have H3 := fun (σ : ℝ) (hσ : 0 < σ ∧ σ ≤ 1) => h3 n σ hσ.1 hσ.2
  choose δ₃ E₃ κ₃ cb₃ hδ₃ hE₃ hκ₃ hcb₃ hbuf₃ using H3
  choose Cr₃ Cm₃ hCr₃ hCm₃ hbuf using hbuf₃
  obtain ⟨cbF, hcbF⟩ : ∃ f : ℝ → ℝ, ∀ σ (hσ : 0 < σ ∧ σ ≤ 1), f σ = cb₃ σ hσ :=
    ⟨fun σ => if hσ : 0 < σ ∧ σ ≤ 1 then cb₃ σ hσ else 1,
      fun σ hσ => by simp only [dite_eq_left hσ]⟩
  obtain ⟨CrF, hCrF⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ σ Cs (hσ : 0 < σ ∧ σ ≤ 1) (hCs : 0 < Cs),
      f σ Cs = Cr₃ σ hσ Cs hCs :=
    ⟨fun σ Cs => if hσ : 0 < σ ∧ σ ≤ 1 then (if hCs : 0 < Cs then Cr₃ σ hσ Cs hCs else 1)
      else 1, fun σ Cs hσ hCs => by simp only [dite_eq_left hσ, dite_eq_left hCs]⟩
  obtain ⟨CmF, hCmF⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ σ Cs (hσ : 0 < σ ∧ σ ≤ 1) (hCs : 0 < Cs),
      f σ Cs = Cm₃ σ hσ Cs hCs :=
    ⟨fun σ Cs => if hσ : 0 < σ ∧ σ ≤ 1 then (if hCs : 0 < Cs then Cm₃ σ hσ Cs hCs else 1)
      else 1, fun σ Cs hσ hCs => by simp only [dite_eq_left hσ, dite_eq_left hCs]⟩
  refine ⟨cbF, CrF, CmF, fun σ hσ hσ₁ => ?_, fun c₀ hc₀ => ?_⟩
  · have h : 0 < σ ∧ σ ≤ 1 := ⟨hσ, hσ₁⟩
    refine ⟨by rw [hcbF σ h]; exact hcb₃ σ h, fun Cs hCs => ⟨?_, ?_⟩⟩
    · rw [hCrF σ Cs h hCs]; exact hCr₃ σ h Cs hCs
    · rw [hCmF σ Cs h hCs]; exact hCm₃ σ h Cs hCs
  obtain ⟨C, hC1, hloc⟩ := hcontent n c₀ hc₀
  refine ⟨C, hC1, fun σ hσ hσ₁ => ?_⟩
  have h : 0 < σ ∧ σ ≤ 1 := ⟨hσ, hσ₁⟩
  obtain ⟨δ₁, E₁, κ₁, C₁, hδ₁, hE₁, hκ₁, hC₁, hchart⟩ := h1 n σ hσ hσ₁
  have hζ : 0 < min c₀ 1 / 720 := div_pos (lt_min hc₀ one_pos) (by norm_num)
  have hθ₀ : 0 < min c₀ 1 / 720 / (10 * C₁) := div_pos hζ (by linarith)
  refine ⟨min (min δ₁ (δ₃ σ h)) (min c₀ 1 / 720 / (10 * C₁)), min E₁ (E₃ σ h),
    min κ₁ (κ₃ σ h), min c₀ 1 / 720 / (10 * C₁), lt_min (lt_min hδ₁ (hδ₃ σ h)) hθ₀,
    lt_min hE₁ (hE₃ σ h), lt_min hκ₁ (hκ₃ σ h), hθ₀, ?_⟩
  intro k ι q R Cd Cs δ E κ θ γ N hδ hE hκ hθ
  have hδ0 := N.parameters.δ_nonneg
  have hE0 := N.parameters.E_nonneg
  have hκ0 := N.parameters.κ_nonneg
  have hθ0 := N.parameters.θ_nonneg
  have hδ₁' : δ ≤ δ₁ := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ₃' : δ ≤ δ₃ σ h := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδζ : δ ≤ min c₀ 1 / 720 / (10 * C₁) := hδ.trans (min_le_right _ _)
  have hsq : N.family.VerticalSquareBound E := N.squareBound
  obtain ⟨G, hbilip, -, -, hcov⟩ :=
    hchart N.family δ E hδ0 hδ₁' hE0 (hE.trans (min_le_left _ _)) N.coherent hsq
  obtain ⟨hlev, hstop⟩ := hcov κ hκ0 (hκ.trans (min_le_left _ _)) N.centerHeight
  have hcore : N.core ⊆ Set.range (timePreservingMap G) := fun z hz =>
    hlev z (N.core_limit z hz.1 hz.2)
  have hstop' : ∀ c ∈ N.stopping, ∃ u : Spatial (k - 2),
      ‖G u c.2.val - c.1‖ ≤ 2 * (min c₀ 1 / 720) * N.radius c := by
    intro c hc
    obtain ⟨u, hu⟩ := hstop θ hθ0 c (N.radius c) (N.stoppingParent c)
      (N.stoppingParent_spec c hc.1 hc.2)
    exact ⟨u, hu.trans (stopping_le_of_small hC₁ hθ hδζ hc.2.le)⟩
  have hP : N.HasVerticalParametrization 2 := hpar N G hbilip hcore hstop'
  have hL : N.HasLocalContentBound C := hloc N hP
  refine ⟨hP, hL, totalContent_of_localContent N hL,
    coreDensity_of_localContent N hL (hlower N hP), fun M => ?_⟩
  have hCs := N.parameters.Cs_pos
  rw [hCrF σ Cs h hCs, hCmF σ Cs h hCs, hcbF σ h]
  exact hbuf σ h Cs hCs N.family M q R δ E κ N.parameters.R_pos hδ0 hδ₃' hE0
    (hE.trans (min_le_right _ _)) hκ0 (hκ.trans (min_le_right _ _)) (N.coherent M)
    (fun w => (ENNReal.sum_le_tsum _).trans (hsq w)) (fun j _ a ha => N.centerHeight j a ha)
    N.initialRadius_le (fun j _ a ha => N.center_mem j a ha)
    ⟨N.initialPoint, N.initialPoint_mem, N.initialPoint_near⟩

/-- **Horizontal neck structure** from the chart and buffer theorems and four neck-level
statements. The conclusion is the statement of `horizontal_neck_structure`. Proof: record
time compatibility gives occurrence time compatibility, so the horizontal chart theorem
applies with
`γ ≤ min(σ², 1)/4`; it covers the spatial projection of the core and places every stopping
center spatially within `2ζ d_c`; the isometry statement (`γ ≤ min(c₀², 1)/4`) and the
exact attachment give the exact parametrization with distortion `2`; content, density and
buffers as in the vertical case. -/
theorem horizontal_neck_structure_of_hubs
    (h2 : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ 1 →
      ∃ δ₀ E₀ κ₀ C : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < C ∧
        ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (δ E γ : ℝ),
          0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → 0 ≤ γ → γ ≤ min (σ ^ 2) 1 / 4 →
          F.IsCoherent σ δ → F.HorizontalSquareBound E → F.IsTimeCompatible γ →
          ∃ G : Spatial m → Spatial n,
            (∀ u v : Spatial m,
              4 / 5 * ‖u - v‖ ≤ ‖G u - G v‖ ∧ ‖G u - G v‖ ≤ 11 / 10 * ‖u - v‖) ∧
            IsClosed (Set.range G) ∧
            ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ₀ → F.HasCenterHeight κ →
              (∀ z : Space n, F.IsLevelLimit z → z.1 ∈ Set.range G) ∧
              ∀ θ : ℝ, 0 ≤ θ → ∀ (c : Space n) (d : ℝ) (p : Option (ℕ × ι)),
                F.IsStoppingParent θ c d p →
                  ∃ u : Spatial m, ‖G u - c.1‖ ≤ C * 10 * (θ + δ) * d)
    (h4 : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ 1 →
      ∃ δ₀ E₀ κ₀ cb : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < cb ∧
        ∀ Cs : ℝ, 0 < Cs → ∃ Cr Cm : ℝ, 0 < Cr ∧ 0 < Cm ∧
          ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (N : ℕ) (q : Space n)
            (R δ E κ γ : ℝ), 0 < R → 0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → 0 ≤ κ → κ ≤ κ₀ →
            0 ≤ γ → γ ≤ min (σ ^ 2) 1 / 4 →
            F.IsCoherentUpTo σ δ N → F.HorizontalSquareBoundUpTo E N →
            F.HasCenterHeightUpTo κ N → F.IsTimeCompatibleUpTo γ N →
            F.initialRadius ≤ Cs * R →
            (∀ j ≤ N, ∀ a ∈ F.index j, F.center j a ∈ Metric.ball q (Cs * R)) →
            (∃ x ∈ F.initialPlane.toSet, ‖x - q.1‖ ≤ Cs * R) →
            F.HasHorizontalBufferedReference R Cr Cm cb N)
    (hiso : ∀ {n k : ℕ} {ι : Type u} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
      (N : NeckRegion n k .horizontal ι q R c₀ Cd Cs σ δ E κ θ γ),
      γ ≤ min (c₀ ^ 2) 1 / 4 →
      ∀ c ∈ N.centers, ∀ c' ∈ N.centers, dist c c' = dist c.1 c'.1)
    (hpar : ∀ {n k : ℕ} {ι : Type u} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
      (N : NeckRegion n k .horizontal ι q R c₀ Cd Cs σ δ E κ θ γ),
      (∀ c ∈ N.centers, ∀ c' ∈ N.centers, dist c c' = dist c.1 c'.1) →
      ∀ G : Spatial k → Spatial n,
      (∀ u v : Spatial k,
        4 / 5 * ‖u - v‖ ≤ ‖G u - G v‖ ∧ ‖G u - G v‖ ≤ 11 / 10 * ‖u - v‖) →
      (∀ z ∈ N.core, z.1 ∈ Set.range G) →
      (∀ c ∈ N.stopping, ∃ u : Spatial k, ‖G u - c.1‖ ≤ 2 * (min c₀ 1 / 720) * N.radius c) →
      N.HasHorizontalParametrization 2)
    (hcontent : ∀ (n : ℕ) (c₀ : ℝ), 0 < c₀ → ∃ C : ℝ, 1 ≤ C ∧
      ∀ {k : ℕ} {ι : Type u} {q : Space n} {R Cd Cs σ δ E κ θ γ : ℝ}
        (N : NeckRegion n k .horizontal ι q R c₀ Cd Cs σ δ E κ θ γ),
        N.HasHorizontalParametrization 2 → N.HasLocalContentBound C)
    (hlower : ∀ {n k : ℕ} {ι : Type u} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
      (N : NeckRegion n k .horizontal ι q R c₀ Cd Cs σ δ E κ θ γ),
      N.HasHorizontalParametrization 2 →
        ∀ᵐ z ∂(hausdorffP n k).restrict N.core, ∃ a r₀ : ℝ, 0 < a ∧ 0 < r₀ ∧
          ∀ r : ℝ, 0 < r → r ≤ r₀ →
            ENNReal.ofReal (a * r ^ k) ≤ (hausdorffP n k).restrict N.core (Metric.ball z r)) :
    ∀ n : ℕ,
    ∃ (cb : ℝ → ℝ) (Cr Cm : ℝ → ℝ → ℝ),
      (∀ σ : ℝ, 0 < σ → σ ≤ 1 →
        0 < cb σ ∧ ∀ Cs : ℝ, 0 < Cs → 0 < Cr σ Cs ∧ 0 < Cm σ Cs) ∧
      ∀ c₀ : ℝ, 0 < c₀ → ∃ C : ℝ, 1 ≤ C ∧ ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
        ∃ δ₀ E₀ κ₀ θ₀ : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < θ₀ ∧
          ∀ {k : ℕ} {ι : Type u} {q : Space n} {R Cd Cs δ E κ θ γ : ℝ}
            (N : NeckRegion n k .horizontal ι q R c₀ Cd Cs σ δ E κ θ γ),
            δ ≤ δ₀ → E ≤ E₀ → κ ≤ κ₀ → θ ≤ θ₀ → γ ≤ min (σ ^ 2) (min (c₀ ^ 2) 1) / 4 →
            N.HasHorizontalParametrization 2 ∧ N.HasLocalContentBound C ∧
              N.HasTotalContentBound (C * (2 + Cd) ^ k) ∧ N.HasCoreDensity C ∧
              ∀ M : ℕ,
                N.family.HasHorizontalBufferedReference R (Cr σ Cs) (Cm σ Cs) (cb σ) M := by
  intro n
  classical
  have H4 := fun (σ : ℝ) (hσ : 0 < σ ∧ σ ≤ 1) => h4 n σ hσ.1 hσ.2
  choose δ₄ E₄ κ₄ cb₄ hδ₄ hE₄ hκ₄ hcb₄ hbuf₄ using H4
  choose Cr₄ Cm₄ hCr₄ hCm₄ hbuf using hbuf₄
  obtain ⟨cbF, hcbF⟩ : ∃ f : ℝ → ℝ, ∀ σ (hσ : 0 < σ ∧ σ ≤ 1), f σ = cb₄ σ hσ :=
    ⟨fun σ => if hσ : 0 < σ ∧ σ ≤ 1 then cb₄ σ hσ else 1,
      fun σ hσ => by simp only [dite_eq_left hσ]⟩
  obtain ⟨CrF, hCrF⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ σ Cs (hσ : 0 < σ ∧ σ ≤ 1) (hCs : 0 < Cs),
      f σ Cs = Cr₄ σ hσ Cs hCs :=
    ⟨fun σ Cs => if hσ : 0 < σ ∧ σ ≤ 1 then (if hCs : 0 < Cs then Cr₄ σ hσ Cs hCs else 1)
      else 1, fun σ Cs hσ hCs => by simp only [dite_eq_left hσ, dite_eq_left hCs]⟩
  obtain ⟨CmF, hCmF⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ σ Cs (hσ : 0 < σ ∧ σ ≤ 1) (hCs : 0 < Cs),
      f σ Cs = Cm₄ σ hσ Cs hCs :=
    ⟨fun σ Cs => if hσ : 0 < σ ∧ σ ≤ 1 then (if hCs : 0 < Cs then Cm₄ σ hσ Cs hCs else 1)
      else 1, fun σ Cs hσ hCs => by simp only [dite_eq_left hσ, dite_eq_left hCs]⟩
  refine ⟨cbF, CrF, CmF, fun σ hσ hσ₁ => ?_, fun c₀ hc₀ => ?_⟩
  · have h : 0 < σ ∧ σ ≤ 1 := ⟨hσ, hσ₁⟩
    refine ⟨by rw [hcbF σ h]; exact hcb₄ σ h, fun Cs hCs => ⟨?_, ?_⟩⟩
    · rw [hCrF σ Cs h hCs]; exact hCr₄ σ h Cs hCs
    · rw [hCmF σ Cs h hCs]; exact hCm₄ σ h Cs hCs
  obtain ⟨C, hC1, hloc⟩ := hcontent n c₀ hc₀
  refine ⟨C, hC1, fun σ hσ hσ₁ => ?_⟩
  have h : 0 < σ ∧ σ ≤ 1 := ⟨hσ, hσ₁⟩
  obtain ⟨δ₁, E₁, κ₁, C₁, hδ₁, hE₁, hκ₁, hC₁, hchart⟩ := h2 n σ hσ hσ₁
  have hζ : 0 < min c₀ 1 / 720 := div_pos (lt_min hc₀ one_pos) (by norm_num)
  have hθ₀ : 0 < min c₀ 1 / 720 / (10 * C₁) := div_pos hζ (by linarith)
  refine ⟨min (min δ₁ (δ₄ σ h)) (min c₀ 1 / 720 / (10 * C₁)), min E₁ (E₄ σ h),
    min κ₁ (κ₄ σ h), min c₀ 1 / 720 / (10 * C₁), lt_min (lt_min hδ₁ (hδ₄ σ h)) hθ₀,
    lt_min hE₁ (hE₄ σ h), lt_min hκ₁ (hκ₄ σ h), hθ₀, ?_⟩
  intro k ι q R Cd Cs δ E κ θ γ N hδ hE hκ hθ hγ
  have hδ0 := N.parameters.δ_nonneg
  have hE0 := N.parameters.E_nonneg
  have hκ0 := N.parameters.κ_nonneg
  have hθ0 := N.parameters.θ_nonneg
  have hγ0 : 0 ≤ γ := N.parameters.γ_nonneg rfl
  have hγσ : γ ≤ min (σ ^ 2) 1 / 4 := by
    have := min_le_min (le_refl (σ ^ 2)) (min_le_right (c₀ ^ 2) (1 : ℝ))
    linarith
  have hγc : γ ≤ min (c₀ ^ 2) 1 / 4 := by
    have := min_le_right (σ ^ 2) (min (c₀ ^ 2) (1 : ℝ))
    linarith
  have hδ₁' : δ ≤ δ₁ := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ₄' : δ ≤ δ₄ σ h := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδζ : δ ≤ min c₀ 1 / 720 / (10 * C₁) := hδ.trans (min_le_right _ _)
  have hsq : N.family.HorizontalSquareBound E := N.squareBound
  have htime : N.family.IsTimeCompatible γ := isTimeCompatible_of_records (N.timeCompatible rfl)
  obtain ⟨G, hbilip, -, hcov⟩ :=
    hchart N.family δ E γ hδ0 hδ₁' hE0 (hE.trans (min_le_left _ _)) hγ0 hγσ N.coherent hsq htime
  obtain ⟨hlev, hstop⟩ := hcov κ hκ0 (hκ.trans (min_le_left _ _)) N.centerHeight
  have hcore : ∀ z ∈ N.core, z.1 ∈ Set.range G := fun z hz =>
    hlev z (N.core_limit z hz.1 hz.2)
  have hstop' : ∀ c ∈ N.stopping, ∃ u : Spatial k,
      ‖G u - c.1‖ ≤ 2 * (min c₀ 1 / 720) * N.radius c := by
    intro c hc
    obtain ⟨u, hu⟩ := hstop θ hθ0 c (N.radius c) (N.stoppingParent c)
      (N.stoppingParent_spec c hc.1 hc.2)
    exact ⟨u, hu.trans (stopping_le_of_small hC₁ hθ hδζ hc.2.le)⟩
  have hP : N.HasHorizontalParametrization 2 := hpar N (hiso N hγc) G hbilip hcore hstop'
  have hL : N.HasLocalContentBound C := hloc N hP
  refine ⟨hP, hL, totalContent_of_localContent N hL,
    coreDensity_of_localContent N hL (hlower N hP), fun M => ?_⟩
  have hCs := N.parameters.Cs_pos
  rw [hCrF σ Cs h hCs, hCmF σ Cs h hCs, hcbF σ h]
  exact hbuf σ h Cs hCs N.family M q R δ E κ γ N.parameters.R_pos hδ0 hδ₄' hE0
    (hE.trans (min_le_right _ _)) hκ0 (hκ.trans (min_le_right _ _)) hγ0 hγσ (N.coherent M)
    (fun w => (ENNReal.sum_le_tsum _).trans (hsq w)) (fun j _ a ha => N.centerHeight j a ha)
    (htime M) N.initialRadius_le (fun j _ a ha => N.center_mem j a ha)
    ⟨N.initialPoint, N.initialPoint_mem, N.initialPoint_near⟩

end NeckHubTree

end ParabolicRectifiability
