import ParabolicRectifiability.Analysis.TraceExtension.TracePieces.Normalize

/-! # One buffered trace piece

See the module `Normalize` for the construction and constants. The compact cutoff (`hcut`)
and the source extension (`hext`) enter as hypotheses (at the universe of the values).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

universe u

/-! ## The normalized piece: geometry, trace, density and energy

Throughout `T = similarity x₀ ρ`, `E' = T(K ∩ P̄(x₀,4ρ))`, `F' = T F` and
`f' = ρ⁻¹ (f ∘ T⁻¹ - f(p*))`. -/

/-- Geometry of the normalized piece. -/
theorem similarity_piece_geometry {m : ℕ} (x₀ : Space m) {ρ : ℝ} (hρ : 0 < ρ)
    {K F : Set (Space m)} (hK : IsCompact K) (hFK : F ⊆ K)
    (hFx : F ⊆ Metric.closedBall x₀ ρ) :
    MeasurableSet (similarity x₀ ρ hρ '' (K ∩ Metric.closedBall x₀ (4 * ρ))) ∧
      similarity x₀ ρ hρ '' F ⊆ similarity x₀ ρ hρ '' (K ∩ Metric.closedBall x₀ (4 * ρ)) ∧
      similarity x₀ ρ hρ '' F ⊆ Metric.closedBall (point 0 0) 1 ∧
      similarity x₀ ρ hρ '' (K ∩ Metric.closedBall x₀ (4 * ρ)) ⊆
        Metric.closedBall (point 0 0) 4 := by
  have hTx₀ : similarity x₀ ρ hρ x₀ = point 0 0 := by
    rw [similarity_apply]
    simp
  have hTball : ∀ z (a : ℝ), dist z x₀ ≤ a * ρ → dist (similarity x₀ ρ hρ z) (point 0 0) ≤ a := by
    intro z a hz
    rw [← hTx₀, dist_similarity]
    calc ρ⁻¹ * dist z x₀ ≤ ρ⁻¹ * (a * ρ) := mul_le_mul_of_nonneg_left hz (inv_nonneg.2 hρ.le)
      _ = a := by rw [mul_left_comm, inv_mul_cancel₀ hρ.ne', mul_one]
  have hFKb : F ⊆ K ∩ Metric.closedBall x₀ (4 * ρ) := fun z hz =>
    ⟨hFK hz, Metric.closedBall_subset_closedBall (by linarith) (hFx hz)⟩
  refine ⟨((hK.inter_right Metric.isClosed_closedBall).image
    (similarity x₀ ρ hρ).continuous).isClosed.measurableSet, image_mono hFKb, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact Metric.mem_closedBall.2
      (hTball z 1 (by rw [one_mul]; exact Metric.mem_closedBall.1 (hFx hz)))
  · rintro _ ⟨z, hz, rfl⟩
    exact Metric.mem_closedBall.2 (hTball z 4 (Metric.mem_closedBall.1 hz.2))

/-- The normalized trace is `L`-Lipschitz on the normalized source and bounded by `8 L`. -/
theorem similarity_piece_trace {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    {m : ℕ} (x₀ : Space m) {ρ : ℝ} (hρ : 0 < ρ) {K F : Set (Space m)} {f : Space m → Y}
    {L : ℝ≥0} (hf : LipschitzOnWith L f K) (hFK : F ⊆ K) (hFx : F ⊆ Metric.closedBall x₀ ρ)
    {ps : Space m} (hps : ps ∈ F) :
    LipschitzOnWith L (fun q => ρ⁻¹ • (f ((similarity x₀ ρ hρ).symm q) - f ps))
        (similarity x₀ ρ hρ '' (K ∩ Metric.closedBall x₀ (4 * ρ))) ∧
      ∀ q ∈ similarity x₀ ρ hρ '' (K ∩ Metric.closedBall x₀ (4 * ρ)),
        ‖ρ⁻¹ • (f ((similarity x₀ ρ hρ).symm q) - f ps)‖ ≤ 8 * L := by
  have hρi : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ.le
  refine ⟨LipschitzOnWith.of_dist_le_mul fun q hq q' hq' => ?_, ?_⟩
  · obtain ⟨z, hz, rfl⟩ := hq
    obtain ⟨w, hw, rfl⟩ := hq'
    simp only [Homeomorph.symm_apply_apply]
    rw [dist_smul₀, Real.norm_of_nonneg hρi, dist_sub_right, dist_similarity]
    calc ρ⁻¹ * dist (f z) (f w) ≤ ρ⁻¹ * (L * dist z w) :=
          mul_le_mul_of_nonneg_left (hf.dist_le_mul z hz.1 w hw.1) hρi
      _ = L * (ρ⁻¹ * dist z w) := by ring
  · rintro _ ⟨z, hz, rfl⟩
    simp only [Homeomorph.symm_apply_apply]
    rw [norm_smul, Real.norm_of_nonneg hρi, ← dist_eq_norm]
    have h1 : dist (f z) (f ps) ≤ L * dist z ps := hf.dist_le_mul z hz.1 ps (hFK hps)
    have hzx : dist z x₀ ≤ 4 * ρ := Metric.mem_closedBall.1 hz.2
    have hpx : dist ps x₀ ≤ ρ := Metric.mem_closedBall.1 (hFx hps)
    have h2 : dist z ps ≤ 5 * ρ := by
      have := dist_triangle_right z ps x₀
      linarith
    have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
    calc ρ⁻¹ * dist (f z) (f ps) ≤ ρ⁻¹ * (L * (5 * ρ)) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hL0)) hρi
      _ = 5 * L := by
          rw [show ρ⁻¹ * (↑L * (5 * ρ)) = 5 * ↑L * (ρ⁻¹ * ρ) by ring, inv_mul_cancel₀ hρ.ne',
            mul_one]
      _ ≤ 8 * L := by linarith

/-- Half density of the normalized source up to radius one. -/
theorem similarity_piece_density {m : ℕ} (x₀ : Space m) {ρ : ℝ} (hρ : 0 < ρ)
    {K F : Set (Space m)} (hFx : F ⊆ Metric.closedBall x₀ ρ)
    (hdens : ∀ p ∈ F, ∀ r : ℝ, 0 < r → r ≤ ρ →
      parabolicVolume m (Metric.ball p r) ≤ 2 * parabolicVolume m (K ∩ Metric.ball p r)) :
    ∀ p ∈ similarity x₀ ρ hρ '' F, ∀ r : ℝ, 0 < r → r ≤ 1 →
      parabolicVolume m (Metric.ball p r) ≤
        2 * parabolicVolume m
          (similarity x₀ ρ hρ '' (K ∩ Metric.closedBall x₀ (4 * ρ)) ∩ Metric.ball p r) := by
  have hρk0 : ENNReal.ofReal ρ ^ (m + 2) ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.2 hρ)
  have hρkt : ENNReal.ofReal ρ ^ (m + 2) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rintro _ ⟨p, hp, rfl⟩ r hr hr1
  have hρr : 0 < ρ * r := mul_pos hρ hr
  have hball : similarity x₀ ρ hρ '' Metric.ball p (ρ * r) =
      Metric.ball (similarity x₀ ρ hρ p) r := by
    rw [image_similarity_ball, mul_div_cancel_left₀ _ hρ.ne']
  have hsub : Metric.ball p (ρ * r) ⊆ Metric.closedBall x₀ (4 * ρ) := by
    intro q hq
    rw [Metric.mem_ball] at hq
    rw [Metric.mem_closedBall]
    have hpx : dist p x₀ ≤ ρ := Metric.mem_closedBall.1 (hFx hp)
    have hρr1 : ρ * r ≤ ρ := by nlinarith
    linarith [dist_triangle q p x₀]
  have hinter : similarity x₀ ρ hρ '' (K ∩ Metric.closedBall x₀ (4 * ρ)) ∩
      Metric.ball (similarity x₀ ρ hρ p) r = similarity x₀ ρ hρ '' (K ∩ Metric.ball p (ρ * r)) := by
    rw [← hball, ← image_inter (similarity x₀ ρ hρ).injective]
    congr 1
    ext q
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, hsub h3⟩, h3⟩
  have hd := hdens p hp (ρ * r) hρr (by nlinarith)
  rw [parabolicVolume_eq_mul_image_similarity x₀ hρ (Metric.ball p (ρ * r)),
    parabolicVolume_eq_mul_image_similarity x₀ hρ (K ∩ Metric.ball p (ρ * r)), hball,
    ← hinter, mul_left_comm] at hd
  exact (ENNReal.mul_le_mul_iff_right hρk0 hρkt).1 hd

/-- The normalized trace energy up to radius `2/ρ`: exact change of variables and restriction
monotonicity. -/
theorem similarity_piece_energy {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    {m : ℕ} (x₀ : Space m) {ρ : ℝ} (hρ : 0 < ρ) {K F : Set (Space m)} (f : Space m → Y)
    (v : Y) {B₀ : ℝ}
    (henergy : ∀ p ∈ F, ∫⁻ r in Ioo 0 2, traceErrorSq (parabolicVolume m) K f p r ∂scaleMeasure ≤
      ENNReal.ofReal B₀) :
    ∀ p ∈ similarity x₀ ρ hρ '' F, ∫⁻ r in Ioo 0 (2 / ρ),
      traceErrorSq (parabolicVolume m) (similarity x₀ ρ hρ '' (K ∩ Metric.closedBall x₀ (4 * ρ)))
        (fun q => ρ⁻¹ • (f ((similarity x₀ ρ hρ).symm q) - v)) p r ∂scaleMeasure ≤
        ENNReal.ofReal B₀ := by
  rintro _ ⟨p, hp, rfl⟩
  have hpt : ∀ s, traceErrorSq (parabolicVolume m)
      (similarity x₀ ρ hρ '' (K ∩ Metric.closedBall x₀ (4 * ρ)))
      (fun q => ρ⁻¹ • (f ((similarity x₀ ρ hρ).symm q) - v)) (similarity x₀ ρ hρ p) s ≤
      traceErrorSq (parabolicVolume m) K f p (ρ * s) := by
    intro s
    have h := traceErrorSq_similarity_proof x₀ ρ hρ (K ∩ Metric.closedBall x₀ (4 * ρ)) f v p
      (ρ * s)
    rw [mul_div_cancel_left₀ _ hρ.ne'] at h
    rw [h]
    exact traceErrorSq_mono_set _ inter_subset_left _ _ _
  calc _ ≤ ∫⁻ s in Ioo 0 (2 / ρ), traceErrorSq (parabolicVolume m) K f p (ρ * s) ∂scaleMeasure :=
        lintegral_mono fun s => hpt s
    _ = ∫⁻ r in Ioo 0 2, traceErrorSq (parabolicVolume m) K f p r ∂scaleMeasure :=
        setLIntegral_Ioo_scaleMeasure_comp_const_mul hρ
          (fun r => traceErrorSq (parabolicVolume m) K f p r) 2
    _ ≤ ENNReal.ofReal B₀ := henergy p hp

/-- **Single buffered piece.** A nonempty compact piece
`F ⊆ K ∩ P̄(x₀,ρ)`, `0 < ρ ≤ 1/64`, with half base density in `K` up to radius `ρ` and
trace energy at most `B₀` on `(0,2)` at each of its points, carries a compact perturbation
`c + H` of a constant that agrees with `f` on `F`, with `Lip(c + H) ≤ C L` and affine
Carleson constant `(C (L + √B₀))^2` for `H`; `C = C(m)`. -/
theorem exists_trace_piece_extension
    (hcut : ∀ m : ℕ, ∃ C : ℝ≥0, 0 < C ∧ ∀ {Y : Type u} [NormedAddCommGroup Y]
      [InnerProductSpace ℝ Y] (F : Space m → Y) (L : ℝ≥0) (B : ℝ), LipschitzWith L F →
      HasAffineCarlesonBound (parabolicVolume m) F B →
      ∀ (z₀ : Space m) (R₀ : ℝ), 0 < R₀ →
        ∃ (c : Y) (H : Space m → Y), (∀ p ∈ Metric.ball z₀ R₀, c + H p = F p) ∧
          HasCompactSupport H ∧ LipschitzWith (C * L) (fun p => c + H p) ∧
          HasAffineCarlesonBound (parabolicVolume m) H (C * (B + (L : ℝ) ^ 2)))
    (hext : ∀ (m : ℕ) (c : ℝ), 0 < c →
      ∃ C : ℝ≥0, 0 < C ∧ ∀ {Y : Type u} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [FiniteDimensional ℝ Y] (F₀ : Set (Space m)), IsCompact F₀ → F₀.Nonempty →
      ∀ σ : Measure (Space m), σ ≤ parabolicVolume m →
      ∀ T : Set (Space m), MeasurableSet T → F₀ ⊆ T → σ Tᶜ = 0 →
      ∀ (f : Space m → Y) (L : ℝ≥0), LipschitzOnWith L f T →
      (∀ x ∈ F₀, ∀ r : ℝ, 0 < r → ENNReal.ofReal (c * r ^ (m + 2)) ≤ σ (Metric.ball x r)) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ x ∈ F₀, ∫⁻ r in Ioi 0, affineErrorSq σ f x r ∂scaleMeasure ≤ ENNReal.ofReal B) →
      ∃ F : Space m → Y, (∀ x ∈ F₀, F x = f x) ∧ LipschitzWith (C * L) F ∧
        HasAffineCarlesonBound (parabolicVolume m) F (C * ((L : ℝ) ^ 2 + B)))
    (m : ℕ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ {Y : Type u} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [FiniteDimensional ℝ Y] (K F : Set (Space m)) (f : Space m → Y) (L : ℝ≥0) (B₀ : ℝ)
      (x₀ : Space m) (ρ : ℝ), IsCompact K → IsCompact F → F.Nonempty → F ⊆ K →
      F ⊆ Metric.closedBall x₀ ρ → 0 < ρ → ρ ≤ 1 / 64 → LipschitzOnWith L f K →
      0 ≤ B₀ →
      (∀ p ∈ F, ∀ r : ℝ, 0 < r → r ≤ ρ →
        parabolicVolume m (Metric.ball p r) ≤ 2 * parabolicVolume m (K ∩ Metric.ball p r)) →
      (∀ p ∈ F, ∫⁻ r in Ioo 0 2, traceErrorSq (parabolicVolume m) K f p r ∂scaleMeasure ≤
        ENNReal.ofReal B₀) →
      ∃ (c : Y) (H : Space m → Y), (∀ p ∈ F, c + H p = f p) ∧ HasCompactSupport H ∧
        LipschitzWith (C * L) (fun p => c + H p) ∧
        HasAffineCarlesonBound (parabolicVolume m) H
          (((C : ℝ) * ((L : ℝ) + Real.sqrt B₀)) ^ 2) := by
  classical
  obtain ⟨c₃, C₃, hc₃, hC₃, hbuf⟩ := TraceExtension.buffered_exterior_source.{u} m
  obtain ⟨Cm, hCm, hextm⟩ := hext m c₃ hc₃
  obtain ⟨Ccut, hCcut, hcutm⟩ := hcut m
  set C : ℝ≥0 := 1 + Ccut * Cm + Ccut * (Cm * (1 + C₃.toNNReal) + Cm ^ 2) with hCdef
  have hCpos : 0 < C := add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg one_pos zero_le)
    zero_le
  refine ⟨C, hCpos, ?_⟩
  intro Y _ _ _ K F f L B₀ x₀ ρ hK hF hFne hFK hFx hρ hρ1 hf hB₀ hdens henergy
  -- normalization data
  obtain ⟨ps, hps⟩ := hFne
  obtain ⟨hE'm, hF'E', hF'1, hE'4⟩ := similarity_piece_geometry x₀ hρ hK hFK hFx
  obtain ⟨hf'L, hf'8⟩ := similarity_piece_trace x₀ hρ hf hFK hFx hps
  have hdens' := similarity_piece_density x₀ hρ hFx hdens
  have henergy' := similarity_piece_energy x₀ hρ f (f ps) henergy
  set T := similarity x₀ ρ hρ with hT
  set o : Space m := point 0 0 with ho
  set E' : Set (Space m) := T '' (K ∩ Metric.closedBall x₀ (4 * ρ)) with hE'
  set F' : Set (Space m) := T '' F with hF'
  set f' : Space m → Y := fun q => ρ⁻¹ • (f (T.symm q) - f ps) with hf'
  -- buffered source, extension and cutoff
  obtain ⟨hLs, hds, hes⟩ := hbuf E' F' f' L B₀ ρ hE'm hF'E' hF'1 hE'4 hρ hρ1 hB₀ hf'L hf'8
    hdens' henergy'
  obtain ⟨hEsm, hF'Es, hσle, hσnull⟩ :=
    TraceExtension.buffered_exterior_source_support (m := m) hE'm hF'E'
  have hB : 0 ≤ B₀ + C₃ * (L : ℝ) ^ 2 := add_nonneg hB₀ (mul_nonneg hC₃ (sq_nonneg _))
  obtain ⟨G, hGagree, hGlip, hGcarl⟩ := hextm F' (hF.image T.continuous)
    ⟨T ps, mem_image_of_mem _ hps⟩ _ hσle _ hEsm hF'Es hσnull _ L hLs hds _ hB hes
  obtain ⟨c, H, hcH, hHsupp, hHlip, hHcarl⟩ := hcutm G (Cm * L) _ hGlip hGcarl o 2 two_pos
  -- undo the normalization
  obtain ⟨hR1, -, -⟩ := similarity_rescale_affine_proof x₀ ρ hρ (fun p => c + H p)
    (Ccut * (Cm * L)) 0
  obtain ⟨-, hR2, hR3⟩ := similarity_rescale_affine_proof x₀ ρ hρ H (Ccut * (Cm * L))
    (Ccut * (Cm * ((L : ℝ) ^ 2 + (B₀ + C₃ * (L : ℝ) ^ 2)) + ((Cm * L : ℝ≥0) : ℝ) ^ 2))
  refine ⟨f ps + ρ • c, fun p => ρ • H (T p), ?_, hR2 hHsupp, ?_, ?_⟩
  · -- agreement on the piece
    intro p hp
    have hTp : T p ∈ F' := mem_image_of_mem _ hp
    have hTb : T p ∈ Metric.ball o 2 :=
      Metric.closedBall_subset_ball (by norm_num) (hF'1 hTp)
    have h1 := hcH (T p) hTb
    have h2 := hGagree (T p) hTp
    simp only [hF'E' hTp, ↓reduceIte] at h2
    calc f ps + ρ • c + ρ • H (T p) = f ps + ρ • (c + H (T p)) := by
          rw [smul_add, add_assoc]
      _ = f ps + ρ • f' (T p) := by rw [h1, h2]
      _ = f p := by
          simp only [hf', Homeomorph.symm_apply_apply, smul_smul, mul_inv_cancel₀ hρ.ne',
            one_smul]
          abel
  · -- Lipschitz bound
    have hl := hR1 hHlip
    have hCL : Ccut * (Cm * L) ≤ C * L := by
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ zero_le
      rw [hCdef]
      calc Ccut * Cm ≤ 1 + Ccut * Cm := le_add_of_nonneg_left zero_le
        _ ≤ _ := le_add_of_nonneg_right zero_le
    refine (LipschitzWith.of_dist_le_mul fun p q => ?_).weaken hCL
    have h := hl.dist_le_mul p q
    simp only [smul_add, dist_add_left] at h ⊢
    exact h
  · -- Carleson bound
    refine (hR3 hHcarl).mono_const ?_
    have hC3 : ((C₃.toNNReal : ℝ≥0) : ℝ) = C₃ := Real.coe_toNNReal _ hC₃
    have hCr : (C : ℝ) = 1 + (Ccut : ℝ) * Cm + Ccut * (Cm * (1 + C₃) + (Cm : ℝ) ^ 2) := by
      rw [hCdef]
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one, NNReal.coe_pow, hC3]
    have key := trace_piece_constant_le (a := (Ccut : ℝ)) (b := (Cm : ℝ)) (c₃ := C₃)
      (l := (L : ℝ)) (s := Real.sqrt B₀) (C := (C : ℝ)) Ccut.coe_nonneg Cm.coe_nonneg hC₃
      L.coe_nonneg (Real.sqrt_nonneg _) hCr.ge
    rw [Real.sq_sqrt hB₀] at key
    rw [NNReal.coe_mul]
    exact key

end ParabolicRectifiability
