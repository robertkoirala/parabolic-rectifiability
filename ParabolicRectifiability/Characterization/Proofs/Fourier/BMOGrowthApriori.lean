import ParabolicRectifiability.Characterization.Proofs.Fourier.BMOGrowthCells

/-! # The `L²` oscillation estimate on parabolic cells

Cell estimate used in the proof of `ba1_bmo_growth_proof`. For a locally integrable `g`
whose mean oscillation on every grid cell is at most `β`,
`∫_R |g - g_R|² ≤ (32 + 16·4^(m+2)) (2β)² |R|` for every cell `R`
(`b1bmo_cellSq_bound`).

Route. For bounded `g` the supremum `Φ` of `|R|⁻¹ ∫_R |g - g_R|²` over all cells is finite.
One generation of stopping (`b1bmo_stopping`, threshold `4β`) bounds
`2 ∫_R |g - g_R|² ≤ ((32 + 16·4^(m+2)) β² + Φ) |R|`, whence `Φ ≤ (32 + 16·4^(m+2)) β²`
(`b1bmo_apriori`). A general `g` is the pointwise limit of its truncations, whose cell
oscillation is at most `2β`; Fatou's lemma passes the bound to the limit. This replaces the
usual iterated stopping and layer-cake argument by the equivalent a priori form; the
differentiation step is the same dyadic differentiation (`b1bmo_ae_tendsto_cells`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ParabolicRectifiability.Characterization

variable {m : ℕ}

/-- The squared oscillation of `g` on a cell. -/
def b1bmo_cellSq (g : Space m → ℝ) (a : Spatial m) (s σ : ℝ) (z : Space m) : ℝ≥0∞ :=
  ∫⁻ w in b1bmo_cell a s σ z,
    ‖g w - b1bmo_avg (parabolicVolume m) (b1bmo_cell a s σ z) g‖ₑ ^ 2 ∂parabolicVolume m

/-- The supremum over all cells of the normalized squared oscillation. -/
def b1bmo_Phi (g : Space m → ℝ) : ℝ≥0∞ :=
  ⨆ (a : Spatial m) (s : ℝ) (σ : ℝ) (_ : 0 < σ) (z : Space m),
    b1bmo_cellSq g a s σ z / parabolicVolume m (b1bmo_cell a s σ z)

theorem b1bmo_cellSq_le_Phi (g : Space m → ℝ) (a : Spatial m) (s : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (z : Space m) :
    b1bmo_cellSq g a s σ z ≤ b1bmo_Phi g * parabolicVolume m (b1bmo_cell a s σ z) := by
  have h : b1bmo_cellSq g a s σ z / parabolicVolume m (b1bmo_cell a s σ z) ≤ b1bmo_Phi g :=
    le_iSup_of_le a (le_iSup_of_le s (le_iSup_of_le σ (le_iSup_of_le hσ
      (le_iSup_of_le z le_rfl))))
  exact (ENNReal.div_le_iff (b1bmo_volume_cell_pos a s hσ z)
    (b1bmo_volume_cell_lt_top a s hσ z)).mp h

theorem b1bmo_abs_avg_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {D : Set α}
    (hDt : μ D ≠ ∞) {g : α → ℝ} {N : ℝ} (hN : 0 ≤ N) (hb : ∀ w, |g w| ≤ N) :
    |b1bmo_avg μ D g| ≤ N := by
  unfold b1bmo_avg
  rw [abs_mul, abs_inv, abs_of_nonneg ENNReal.toReal_nonneg]
  have hI : |∫ x in D, g x ∂μ| ≤ N * (μ D).toReal := by
    have := norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hDt)
      (fun x _ => (by rw [Real.norm_eq_abs]; exact hb x : ‖g x‖ ≤ N))
    rwa [Real.norm_eq_abs, measureReal_def] at this
  rcases eq_or_ne (μ D).toReal 0 with h0 | h0
  · rw [h0, inv_zero, zero_mul]
    exact hN
  · calc (μ D).toReal⁻¹ * |∫ x in D, g x ∂μ| ≤ (μ D).toReal⁻¹ * (N * (μ D).toReal) := by
          gcongr
      _ = N := by field_simp

/-- For a bounded function the supremum `Φ` is finite. -/
theorem b1bmo_Phi_ne_top {g : Space m → ℝ} {N : ℝ} (hN : 0 ≤ N) (hb : ∀ w, |g w| ≤ N) :
    b1bmo_Phi g ≠ ∞ := by
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := (2 * N) ^ 2)) ?_
  refine iSup_le fun a => iSup_le fun s => iSup_le fun σ => iSup_le fun hσ =>
    iSup_le fun z => ENNReal.div_le_of_le_mul ?_
  have havg : |b1bmo_avg (parabolicVolume m) (b1bmo_cell a s σ z) g| ≤ N :=
    b1bmo_abs_avg_le _ (b1bmo_volume_cell_lt_top a s hσ z) hN hb
  calc b1bmo_cellSq g a s σ z ≤ ∫⁻ _ in b1bmo_cell a s σ z, ENNReal.ofReal ((2 * N) ^ 2)
        ∂parabolicVolume m := by
        refine lintegral_mono fun w => ?_
        rw [b1bmo_enorm_sq]
        refine ENNReal.ofReal_le_ofReal ?_
        obtain ⟨h1, h2⟩ := abs_le.mp (hb w)
        obtain ⟨h3, h4⟩ := abs_le.mp havg
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * N - (g w - b1bmo_avg (parabolicVolume m) (b1bmo_cell a s σ z) g))
          (by linarith : (0 : ℝ) ≤ 2 * N + (g w - b1bmo_avg (parabolicVolume m) (b1bmo_cell a s σ z) g))]
    _ = ENNReal.ofReal ((2 * N) ^ 2) * parabolicVolume m (b1bmo_cell a s σ z) :=
        setLIntegral_const _ _

/-- The constant of the cell estimate. -/
def b1bmo_A (m : ℕ) : ℝ≥0∞ := 32 + 16 * (2 ^ (m + 2)) ^ 2

/-- **The a priori estimate** for functions with finite `Φ`. -/
theorem b1bmo_apriori {g : Space m → ℝ} (hg : LocallyIntegrable g (parabolicVolume m))
    (hΦ : b1bmo_Phi g ≠ ∞) {β : ℝ≥0∞} (hβ0 : β ≠ 0) (hβt : β ≠ ∞)
    (hosc : b1bmo_cellOsc m g β) : b1bmo_Phi g ≤ b1bmo_A m * β ^ 2 := by
  set μ := parabolicVolume m with hμ
  set Φ := b1bmo_Phi g with hΦdef
  have key : ∀ (a : Spatial m) (s σ : ℝ), 0 < σ → ∀ z : Space m,
      2 * b1bmo_cellSq g a s σ z ≤ (b1bmo_A m * β ^ 2 + Φ) * μ (b1bmo_cell a s σ z) := by
    intro a s σ hσ z
    set R := b1bmo_cell a s σ z with hR
    set c := b1bmo_avg μ R g with hc
    set lam : ℝ≥0∞ := 4 * β with hlam
    set K : ℝ≥0∞ := 2 * Φ + 2 * (2 ^ (m + 2) * lam) ^ 2 with hK
    have hQ : b1bmo_cellOf (b1bmo_gridIdx a s σ 0) z = R := b1bmo_cell_gridIdx_zero a s σ z
    have hoscR : ∫⁻ w in R, ‖g w - c‖ₑ ∂μ ≤ β * μ R := hosc a s σ hσ z
    have hgood0 : b1bmo_good μ (b1bmo_gridIdx a s σ) (fun w => ‖g w - c‖ₑ) lam 0 z := by
      unfold b1bmo_good
      rw [hQ]
      refine hoscR.trans ?_
      have h4 : β ≤ lam := le_mul_of_one_le_left zero_le (by norm_num)
      gcongr
    have hdiff : ∀ᵐ z' ∂μ, b1bmo_gridIdx a s σ 0 z' = b1bmo_gridIdx a s σ 0 z →
        (∀ k, b1bmo_good μ (b1bmo_gridIdx a s σ) (fun w => ‖g w - c‖ₑ) lam k z') →
        ‖g z' - c‖ₑ ≤ lam := by
      filter_upwards [b1bmo_ae_tendsto_cells hg] with z' hz' _ hgood
      exact b1bmo_le_of_tendsto (D := fun k => b1bmo_cell a s (σ / 2 ^ k) z')
        (fun k => b1bmo_volume_cell_pos a s (by positivity) z')
        (fun k => b1bmo_volume_cell_lt_top a s (by positivity) z')
        (fun k => (b1bmo_integrableOn_cell hg a s (by positivity) z').aestronglyMeasurable)
        c z' (fun k => hgood k) (hz' a s σ hσ)
    have hcell : ∀ k z', b1bmo_gridIdx a s σ 0 z' = b1bmo_gridIdx a s σ 0 z →
        b1bmo_good μ (b1bmo_gridIdx a s σ) (fun w => ‖g w - c‖ₑ) lam k z' →
        ∫⁻ w in b1bmo_cellOf (b1bmo_gridIdx a s σ (k + 1)) z', ‖g w - c‖ₑ ^ 2 ∂μ ≤
          K * μ (b1bmo_cellOf (b1bmo_gridIdx a s σ (k + 1)) z') := by
      intro k z' _ hgood
      have hk1 : 0 < σ / 2 ^ (k + 1) := by positivity
      exact b1bmo_child_sq_le μ (b1bmo_gridCell_succ_subset a s σ hσ k z')
        (b1bmo_volume_cell_pos a s hk1 z') (b1bmo_volume_cell_lt_top a s hk1 z')
        (b1bmo_integrableOn_cell hg a s hk1 z') c
        (b1bmo_cellSq_le_Phi g a s hk1 z') hgood
        (b1bmo_volume_gridCell_succ a s σ hσ k z' z').le
    obtain ⟨U, -, hsq, hbad⟩ := b1bmo_stopping μ (b1bmo_gridIdx a s σ)
      (fun k => b1bmo_measurable_idx _ _ _) (fun k z w h => b1bmo_gridIdx_nest a s σ hσ k z w h)
      z (fun w => ‖g w - c‖ₑ) lam K hgood0 hdiff hcell
    rw [hQ] at hsq hbad
    have hbad' : lam * μ U ≤ β * μ R := hbad.trans hoscR
    have hsq' : b1bmo_cellSq g a s σ z ≤ lam ^ 2 * μ R + K * μ U := hsq
    have h2β0 : 2 * β ≠ 0 := mul_ne_zero two_ne_zero hβ0
    have h2βt : 2 * β ≠ ∞ := ENNReal.mul_ne_top (by simp) hβt
    have h1 : (2 * β) * (2 * b1bmo_cellSq g a s σ z) ≤
        (2 * β) * ((b1bmo_A m * β ^ 2 + Φ) * μ R) := by
      calc (2 * β) * (2 * b1bmo_cellSq g a s σ z) = lam * b1bmo_cellSq g a s σ z := by
            rw [hlam]
            ring
        _ ≤ lam * (lam ^ 2 * μ R + K * μ U) := by gcongr
        _ = lam ^ 3 * μ R + K * (lam * μ U) := by ring
        _ ≤ lam ^ 3 * μ R + K * (β * μ R) := by gcongr
        _ = (2 * β) * ((b1bmo_A m * β ^ 2 + Φ) * μ R) := by
            rw [hK, hlam, b1bmo_A]
            ring
    calc 2 * b1bmo_cellSq g a s σ z = (2 * β)⁻¹ * ((2 * β) * (2 * b1bmo_cellSq g a s σ z)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h2β0 h2βt, one_mul]
      _ ≤ (2 * β)⁻¹ * ((2 * β) * ((b1bmo_A m * β ^ 2 + Φ) * μ R)) := by gcongr
      _ = (b1bmo_A m * β ^ 2 + Φ) * μ R := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h2β0 h2βt, one_mul]
  have h2 : 2 * Φ ≤ b1bmo_A m * β ^ 2 + Φ := by
    conv_lhs => rw [hΦdef, b1bmo_Phi]
    simp only [ENNReal.mul_iSup]
    refine iSup_le fun a => iSup_le fun s => iSup_le fun σ => iSup_le fun hσ =>
      iSup_le fun z => ?_
    rw [← mul_div_assoc]
    exact ENNReal.div_le_of_le_mul (key a s σ hσ z)
  rw [two_mul] at h2
  exact ENNReal.le_of_add_le_add_right hΦ h2

/-- **The cell `L²` oscillation estimate** for a locally integrable function with cell
oscillation at most `β`. -/
theorem b1bmo_cellSq_bound {g : Space m → ℝ} (hg : LocallyIntegrable g (parabolicVolume m))
    {β : ℝ≥0∞} (hβ0 : β ≠ 0) (hβt : β ≠ ∞) (hosc : b1bmo_cellOsc m g β)
    (a : Spatial m) (s : ℝ) {σ : ℝ} (hσ : 0 < σ) (z : Space m) :
    b1bmo_cellSq g a s σ z ≤
      b1bmo_A m * (2 * β) ^ 2 * parabolicVolume m (b1bmo_cell a s σ z) := by
  set μ := parabolicVolume m with hμ
  set D := b1bmo_cell a s σ z with hD
  let G : ℕ → Space m → ℝ := fun N w => b1bmo_trunc N (g w)
  have hGloc : ∀ N : ℕ, LocallyIntegrable (G N) μ := fun N =>
    b1bmo_locallyIntegrable_trunc hg N (Nat.cast_nonneg N)
  have hGbound : ∀ N : ℕ, b1bmo_cellSq (G N) a s σ z ≤ b1bmo_A m * (2 * β) ^ 2 * μ D := by
    intro N
    have hb : ∀ w, |G N w| ≤ N := fun w => b1bmo_abs_trunc_le N (g w) (Nat.cast_nonneg N)
    have hΦ := b1bmo_apriori (hGloc N) (b1bmo_Phi_ne_top (Nat.cast_nonneg N) hb)
      (mul_ne_zero two_ne_zero hβ0) (ENNReal.mul_ne_top (by simp) hβt)
      (b1bmo_cellOsc_trunc hg hosc N (Nat.cast_nonneg N))
    exact (b1bmo_cellSq_le_Phi (G N) a s hσ z).trans (by gcongr)
  have hint : IntegrableOn g D μ := b1bmo_integrableOn_cell hg a s hσ z
  -- the truncations converge pointwise, and so do their averages
  have hpt : ∀ w, Tendsto (fun N : ℕ => G N w) atTop (𝓝 (g w)) := by
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop |g w|] with N hN
    exact (b1bmo_trunc_eq N (g w) hN).symm
  have havg : Tendsto (fun N : ℕ => b1bmo_avg μ D (G N)) atTop (𝓝 (b1bmo_avg μ D g)) := by
    unfold b1bmo_avg
    refine Tendsto.const_mul _ ?_
    refine tendsto_integral_of_dominated_convergence (fun w => |g w|)
      (fun N => (hGloc N).aestronglyMeasurable.restrict) hint.abs (fun N => ?_)
      (ae_of_all _ hpt)
    refine ae_of_all _ fun w => ?_
    rw [Real.norm_eq_abs]
    exact b1bmo_abs_trunc_le_abs N (g w) (Nat.cast_nonneg N)
  have hlim : ∀ w, Tendsto (fun N : ℕ => ‖G N w - b1bmo_avg μ D (G N)‖ₑ ^ 2) atTop
      (𝓝 (‖g w - b1bmo_avg μ D g‖ₑ ^ 2)) := by
    intro w
    simp only [b1bmo_enorm_sq]
    exact ENNReal.tendsto_ofReal (((hpt w).sub havg).pow 2)
  have hmeas : ∀ N : ℕ, AEMeasurable (fun w => ‖G N w - b1bmo_avg μ D (G N)‖ₑ ^ 2)
      (μ.restrict D) := fun N =>
    (((hGloc N).aestronglyMeasurable.restrict.sub aestronglyMeasurable_const).enorm).pow_const 2
  calc b1bmo_cellSq g a s σ z
      = ∫⁻ w in D, liminf (fun N : ℕ => ‖G N w - b1bmo_avg μ D (G N)‖ₑ ^ 2) atTop ∂μ := by
        refine lintegral_congr fun w => ?_
        exact ((hlim w).liminf_eq).symm
    _ ≤ liminf (fun N : ℕ => ∫⁻ w in D, ‖G N w - b1bmo_avg μ D (G N)‖ₑ ^ 2 ∂μ) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ liminf (fun _ : ℕ => b1bmo_A m * (2 * β) ^ 2 * μ D) atTop :=
        liminf_le_liminf (Eventually.of_forall hGbound)
    _ = b1bmo_A m * (2 * β) ^ 2 * μ D := liminf_const _

end ParabolicRectifiability.Characterization
