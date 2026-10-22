import ParabolicRectifiability.QuantitativeCharacterization.Statements.WhitneyPlateau
import ParabolicRectifiability.QuantitativeCharacterization.Assembly.Monotonicity
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.TimePoincare
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.SpatialPoincare
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.SpatialSecondPoincare
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.AffinePoincareAssembly
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.DerivativeRecurrence
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.AttachmentEnergy
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.AffineCarlesonAdd
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.StandardAffineBMO
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.AffineInvariance
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.HorizontalTrace
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.Chart
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.ExistsCompletion
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.Attachment
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.ProjectionDisplacement
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.ProjectionEnergy.ProjectionEnergy

/-! # Completion of the forward reference: composition

The proofs of the completion statements, assembled under `d1ecomp_` names.
`d1ecomp_hub_completion_glue` has the type of `d1_hub_completion`: it keeps two inputs as
premises (`WhitneyPlateauCompletionStatement` and the trace-point-on-carrier statement).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

open ParabolicRectifiability.Foundations

/-! ## Elementary helpers -/

/-- The affine Carleson bound on the standard base is monotone in its constant. -/
theorem d1ecomp_hasAffineCarlesonBound_mono {m d : ℕ} {f : Space m → Spatial d} {B B' : ℝ}
    (h : HasAffineCarlesonBound (parabolicVolume m) f B) (hB : B ≤ B') :
    HasAffineCarlesonBound (parabolicVolume m) f B' :=
  ⟨h.1.trans hB, fun z R hR => (h.2 z R hR).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hB (pow_nonneg hR.le _)))⟩

/-- The displacement of the completed map splits as `(F⁰ - F₀) + G`. -/
theorem d1ecomp_displacement_eq {n k : ℕ} {ι : Type*} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
    {N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ} {χ ζ : ℝ}
    (K : d1e_VerticalCompletion N χ ζ) :
    K.displacement = (fun p => K.limitMap p - K.initialMap p) + K.attachment := by
  funext p
  simp only [d1e_VerticalCompletion.displacement, d1e_VerticalCompletion.spatialMap,
    Pi.add_apply]
  abel

/-! ## Branch 2: Poincaré and `q-wholev` -/

/-- **Second-order parabolic affine Poincaré** (`d1e_AffinePoincareStatement`): the parabolic
assembly `d1e_affinePoincare_assembly_proof` fed by the
first-order time inequality `d1e_time_poincare_proof` and the second-order spatial step
`d1e_spatial_secondPoincare_proof`, itself fed by the first-order spatial inequality
`d1e_spatial_poincare_proof`. -/
theorem d1ecomp_affine_poincare : d1e_AffinePoincareStatement :=
  d1e_affinePoincare_assembly_proof d1e_time_poincare_proof (d1e_spatial_secondPoincare_proof d1e_spatial_poincare_proof)

/-- **`q-wholev`**: the whole-map affine energy of the completed map from the
projection-energy estimate `d1e2comp_hub_projectionEnergy_glue` (fed by `d1e_derivative_recurrence_proof` and
`d1ecomp_affine_poincare`), the attachment energy `d1e_attachment_energy_proof` (fed by
`d1ecomp_affine_poincare`) and subadditivity `d1e_affineCarleson_add_proof`, with
`C = 2 (C₃ + C₄)`. -/
theorem d1ecomp_wholeAffineEnergy : d1e_WholeAffineEnergyStatement := by
  intro n _hn k σ hσ hσ₁
  obtain ⟨C₃, δ₃, E₃, hC₃, hδ₃, hE₃, h3⟩ :=
    d1e2comp_hub_projectionEnergy_glue d1e_derivative_recurrence_proof d1ecomp_affine_poincare n σ hσ hσ₁
  obtain ⟨C₄, hC₄, h4⟩ := d1e_attachment_energy_proof d1ecomp_affine_poincare n k
  refine ⟨2 * (C₃ + C₄), δ₃, E₃, mul_nonneg zero_le_two (add_nonneg hC₃ hC₄), hδ₃, hE₃, ?_⟩
  intro ι q R c₀ Cd Cs δ E κ θ γ N hδ hE χ ζ a hχ ha hζ K hFc hGc
  have hE0 : 0 ≤ E := N.parameters.E_nonneg
  have hP := h3 N.family δ E N.parameters.δ_nonneg hδ hE0 hE N.coherent N.squareBound K.chart
  have hA := h4 N χ ζ a hχ ha hζ K
  have hS := d1e_affineCarleson_add_proof _ _ _ _ _ _ hFc hGc hP hA
  rw [d1ecomp_displacement_eq K]
  refine d1ecomp_hasAffineCarlesonBound_mono hS ?_
  nlinarith [mul_nonneg hC₃ (sq_nonneg a), mul_nonneg hC₄ hE0]

/-! ## Branch 3: `q-affinebmo` -/

/-- **The standard-coordinate BMO bridge**: each coordinate of the displacement
`F - F₀` has the bound `C (L + √B)` (`d1e_standard_affineBMO_proof`), and adding back the coordinate
`x₀^α + (U u)^α` of the time-independent affine map keeps it (`d1e_affine_invariance_proof`). -/
theorem d1ecomp_bmoBridge : d1e_BMOBridgeStatement := by
  intro m
  obtain ⟨C, hC, h1⟩ := d1e_standard_affineBMO_proof m
  refine ⟨C, hC, fun d F x₀ U L B hL hc hB α => ?_⟩
  have hH : HasHalfTimeBMOBound m (fun p => (F p - (x₀ + U p.1)) α)
      (C * ((L : ℝ) + Real.sqrt B)) := h1 d (fun p => F p - (x₀ + U p.1)) L B hc hL hB α
  have hα := d1e_affine_invariance_proof m (fun p => (F p - (x₀ + U p.1)) α)
    (C * ((L : ℝ) + Real.sqrt B)) (x₀ α) ((EuclideanSpace.proj α).comp U.toContinuousLinearMap) hH
  have hfun : (fun z : Space m => F z α) = fun p : Space m =>
      x₀ α + ((EuclideanSpace.proj α).comp U.toContinuousLinearMap) p.1 +
        (F p - (x₀ + U p.1)) α := by
    funext p
    show F p α = x₀ α + U p.1 α + (F p - (x₀ + U p.1)) α
    simp only [PiLp.sub_apply, PiLp.add_apply]
    ring
  show HasHalfTimeBMOBound m (fun z => F z α) (C * ((L : ℝ) + Real.sqrt B))
  rw [hfun]
  exact hα

/-! ## Branch 4: `q-wholeh` -/

/-- **`q-wholeh`**: the trace of `d1e_horizontal_trace_proof` is completed by the Whitney
plateau statement (spatial map `G`, domain `D`, height `τ` on `D`); every centre is a trace point
`H.map u`, `u ∈ D`, hence on the carrier `Γ = supp σ` by the trace-point input. -/
theorem d1ecomp_horizontalCompletion (hWPC : WhitneyPlateauCompletionStatement)
    (hmem : ∀ (n k : ℕ) (L : ℝ) (H : HorizontalReference n k L) (u : Spatial k),
      u ∈ H.domain → H.map u ∈ H.carrier) :
    d1e_HorizontalCompletionStatement := by
  intro n k c₀ σ hc₀ hσ hσ₁
  obtain ⟨ε₀, hε₀, htr⟩ := d1e_horizontal_trace_proof n k c₀ σ hc₀ hσ hσ₁
  refine ⟨ε₀, hε₀, fun ι q R Cd Cs δ E κ θ γ hδ hE hκ hθ hγ N => ?_⟩
  obtain ⟨G, hG, D, τ, hDne, hDc, hτ, hsub⟩ := htr ι q R Cd Cs δ E κ θ γ hδ hE hκ hθ hγ N
  have hav : 1 ≤ k ∧ k ≤ n := N.available
  obtain ⟨H, hHF, hHD, hHτ⟩ := hWPC n k hav.1 hav.2 2 G hG D hDne hDc τ hτ
  refine ⟨H, fun c hc => ?_⟩
  obtain ⟨u, hu, rfl⟩ := hsub hc
  have huH : u ∈ H.domain := by rw [hHD]; exact hu
  have hmap : H.map u = point (G u) (τ u) := by
    simp only [HorizontalReference.map, hHF, hHτ u hu]
  have hon := hmem n k 2 H u huH
  rw [hmap] at hon
  exact hon

/-! ## The vertical completed reference -/

/-- **The vertical completed reference.** One completion datum `K` (initial chart
and stopping parameters) is produced from the chart (`d1e_chart_proof`) and `d1e_exists_completion_proof`;
the attachment, the compact displacement, the whole-map energy and the BMO bridge are
all applied to this same `K`, and the vertical reference has spatial map `K.spatialMap = F⁰ + G`. -/
theorem d1ecomp_verticalCompletion : d1e_VerticalCompletionStatement := by
  intro n hn k hkn c₀ σ hc₀ hσ hσ₁
  -- the four branches' constants (none depends on a neck)
  obtain ⟨δ₁, E₁, κ₁, C₁, hδ₁, hE₁, hκ₁, hC₁, hchart⟩ := d1e_chart_proof n hn σ hσ hσ₁
  obtain ⟨δ₂, hδ₂, hdisp⟩ := d1e_projection_displacement_proof n σ hσ hσ₁
  obtain ⟨cA, hcA, hatt⟩ := d1e_attachment_proof n k
  obtain ⟨Cw, δ₃, E₃, hCw, hδ₃, hE₃, hwhole⟩ := d1ecomp_wholeAffineEnergy n hn k σ hσ hσ₁
  obtain ⟨Cb, _hCb, hbridge⟩ := d1ecomp_bmoBridge (NeckType.vertical.rank k)
  -- the attachment ratios, fixed before the tolerances
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min cA (1 / 24) := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha]; exact lt_min hcA (by norm_num)
  have haA : a ≤ cA := by rw [ha]; exact min_le_left _ _
  have ha24 : a ≤ 1 / 24 := by rw [ha]; exact min_le_right _ _
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ, χ = min c₀ 1 / 30 := ⟨_, rfl⟩
  have hχpos : 0 < χ := by rw [hχ]; exact div_pos (lt_min hc₀ one_pos) (by norm_num)
  have hχ30 : 30 * χ ≤ min c₀ 1 := le_of_eq (by rw [hχ]; ring)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ, ζ = a * χ := ⟨_, rfl⟩
  have hζpos : 0 < ζ := by rw [hζ]; exact mul_pos hapos hχpos
  have hζ24 : 24 * ζ ≤ χ := by
    rw [hζ]
    nlinarith [mul_le_mul_of_nonneg_right ha24 hχpos.le]
  have hζA : ζ ≤ cA * χ := by rw [hζ]; exact mul_le_mul_of_nonneg_right haA hχpos.le
  -- the tolerance threshold
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ,
      ε₀ = min (min (min δ₁ δ₂) δ₃) (min (min E₁ E₃) (min κ₁ (ζ / C₁))) := ⟨_, rfl⟩
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀]
    exact lt_min (lt_min (lt_min hδ₁ hδ₂) hδ₃)
      (lt_min (lt_min hE₁ hE₃) (lt_min hκ₁ (div_pos hζpos hC₁)))
  have hεδ₁ : ε₀ ≤ δ₁ := by
    rw [hε₀]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεδ₂ : ε₀ ≤ δ₂ := by
    rw [hε₀]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεδ₃ : ε₀ ≤ δ₃ := by
    rw [hε₀]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hεE₁ : ε₀ ≤ E₁ := by
    rw [hε₀]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεE₃ : ε₀ ≤ E₃ := by
    rw [hε₀]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεκ₁ : ε₀ ≤ κ₁ := by
    rw [hε₀]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεζ : ε₀ ≤ ζ / C₁ := by
    rw [hε₀]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the reference constant
  obtain ⟨Bbar, hBbar⟩ : ∃ B : ℝ, B = Cw * (ε₀ + a ^ 2) := ⟨_, rfl⟩
  refine ⟨max 2 (Cb * (((3 : ℝ≥0) : ℝ) + Real.sqrt Bbar)), le_max_left _ _, ε₀, hε₀pos, ?_⟩
  intro ι q R Cd Cs δ E κ θ γ hδ hE hκ hθ N
  have hpar := N.parameters
  have hδ0 : 0 ≤ δ := hpar.δ_nonneg
  have hE0 : 0 ≤ E := hpar.E_nonneg
  have hκ0 : 0 ≤ κ := hpar.κ_nonneg
  have hθ0 : 0 ≤ θ := hpar.θ_nonneg
  have hcoh : N.family.IsCoherent σ δ := N.coherent
  have hsq : N.family.VerticalSquareBound E := N.squareBound
  have hch := hchart N.family δ E κ hδ0 (hδ.trans hεδ₁) hE0 (hE.trans hεE₁) hκ0
    (hκ.trans hεκ₁) hcoh hsq N.centerHeight
  obtain ⟨P⟩ := CoherentChart.nonempty_initialChart N.family
  -- branch 1: the stopping parameters with error `2 ζ d_c`
  have hC₁ne : C₁ ≠ 0 := hC₁.ne'
  have hC₁ζ : C₁ * (θ + δ) ≤ 2 * ζ := by
    have h1 : θ ≤ ζ / C₁ := hθ.trans hεζ
    have h2 : δ ≤ ζ / C₁ := hδ.trans hεζ
    have h3 : C₁ * (ζ / C₁) = ζ := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 hC₁.le, mul_le_mul_of_nonneg_left h2 hC₁.le]
  have hstop : ∀ c ∈ N.stopping, ∃ u : Spatial (NeckType.vertical.rank k),
      ‖d1e_projectionLimit N.family P u c.2.val - c.1‖ ≤ 2 * ζ * N.radius c := by
    intro c hc
    have hc' : c ∈ N.centers ∧ 0 < N.radius c := hc
    obtain ⟨u, hu⟩ := (hch P).2.2 θ hθ0 c (N.radius c) (N.stoppingParent c)
      (N.stoppingParent_spec c hc'.1 hc'.2)
    exact ⟨u, hu.trans (mul_le_mul_of_nonneg_right hC₁ζ hc'.2.le)⟩
  -- branch 1: one completion datum `K`, its attachments and compact displacement
  obtain ⟨K, -⟩ := d1e_exists_completion_proof N P χ ζ hχpos hζpos.le hχ30 hζ24 (hch P).1 hstop
  have hcore : ∀ z ∈ N.core,
      z ∈ Set.range (timePreservingMap (d1e_projectionLimit N.family K.chart)) := by
    intro z hz
    have hz' : z ∈ N.centers ∧ N.radius z = 0 := hz
    exact (hch K.chart).2.1 z (N.core_limit z hz'.1 hz'.2)
  obtain ⟨hbil, hcont, hGcont, hGc, hLip⟩ := hatt N χ ζ hχpos hζA K (hch K.chart).1 hcore
  obtain ⟨hFcont, hFc⟩ := hdisp N.family δ hδ0 (hδ.trans hεδ₂) hcoh K.chart
  have hcs : HasCompactSupport K.displacement := by
    rw [d1ecomp_displacement_eq K]
    exact hFc.add hGc
  -- branch 2: the whole-map affine energy of the same `K`
  have hen := hwhole N (hδ.trans hεδ₃) (hE.trans hεE₃) χ ζ a hχpos hapos.le hζ.le K hFcont hGcont
  have hen' : HasAffineCarlesonBound (parabolicVolume (NeckType.vertical.rank k))
      K.displacement Bbar := by
    refine d1ecomp_hasAffineCarlesonBound_mono hen ?_
    rw [hBbar]
    exact mul_le_mul_of_nonneg_left (by linarith) hCw
  -- branch 3: the standard-coordinate BMO bridge for the same `K`
  have hbmo := hbridge n K.spatialMap K.chart.origin K.chart.isometry 3 Bbar hLip hcs hen'
  -- the vertical reference
  have hav : 2 ≤ k ∧ k ≤ n + 2 := N.available
  have h2k : 2 ≤ k := hav.1
  refine ⟨{ spatialRank := NeckType.vertical.rank k
            rank_eq := by show k - 2 + 2 = k; omega
            lt_ambient := hkn
            spatialMap := K.spatialMap
            bilipschitz := fun p p' =>
              ⟨(hbil p p').1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg),
                (hbil p p').2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)⟩
            coordinate_bmo := hasCoordinateHalfTimeBMOBound_mono hbmo (le_max_right _ _) }, ?_⟩
  exact hcont

/-! ## Completion of the forward reference -/

/-- **Completion of the forward reference** (`d1_hub_completion`, implication form of
`ForwardCompletionStatement`). Type: exactly that of
`d1_hub_completion`. Horizontal necks receive the plateau
completion (`L = 2`, raised by `Reference.mono`), vertical necks the smooth completion of the
actual projection limit; the threshold is the minimum of the two branch thresholds. -/
theorem d1ecomp_hub_completion_glue :
    WhitneyPlateauCompletionStatement →
      (∀ (n k : ℕ) (L : ℝ) (H : HorizontalReference n k L) (u : Spatial k),
        u ∈ H.domain → H.map u ∈ H.carrier) →
      ForwardCompletionStatement := by
  intro hWPC hmem n hn k _hk hkn c₀ σ hc₀ hσ hσ₁
  obtain ⟨εh, hεh, hH⟩ := d1ecomp_horizontalCompletion hWPC hmem n k c₀ σ hc₀ hσ hσ₁
  obtain ⟨L, hL, εv, hεv, hV⟩ := d1ecomp_verticalCompletion n hn k hkn c₀ σ hc₀ hσ hσ₁
  refine ⟨L, le_trans (by norm_num) hL, min εh εv, lt_min hεh hεv, ?_⟩
  intro T
  cases T with
  | horizontal =>
    intro ι q R Cd Cs δ E κ θ γ hδ hE hκ hθ hγ N
    obtain ⟨H, hHc⟩ := hH ι q R Cd Cs δ E κ θ γ (hδ.trans (min_le_left _ _))
      (hE.trans (min_le_left _ _)) (hκ.trans (min_le_left _ _)) (hθ.trans (min_le_left _ _))
      (hγ.trans (min_le_left _ _)) N
    refine ⟨(Reference.horizontal H).mono (by norm_num) hL, ?_, ?_⟩
    · rw [Reference.kind_mono]
      rfl
    · rw [Reference.carrier_mono]
      exact hHc
  | vertical =>
    intro ι q R Cd Cs δ E κ θ γ hδ hE hκ hθ _hγ N
    obtain ⟨V, hVc⟩ := hV ι q R Cd Cs δ E κ θ γ (hδ.trans (min_le_right _ _))
      (hE.trans (min_le_right _ _)) (hκ.trans (min_le_right _ _)) (hθ.trans (min_le_right _ _)) N
    exact ⟨Reference.vertical V, rfl, hVc⟩

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
