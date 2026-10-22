import ParabolicRectifiability.Decomposition.Carrier.BetaPointBoundAndRankZero
import ParabolicRectifiability.Decomposition.Carrier.CoercivityAndGeometricBounds
import ParabolicRectifiability.Decomposition.Carrier.RetainedPiecesAndLargeScaleSquare
import ParabolicRectifiability.Decomposition.Carrier.SquareBound
import ParabolicRectifiability.Decomposition.Carrier.Transport
import ParabolicRectifiability.Analysis.RegularExtension.RegularTraceAndGraphs
import ParabolicRectifiability.Geometry.SmallGraphs
import ParabolicRectifiability.Geometry.Neck.NeckTheorems

/-! # The regular vertical carrier: `vertical_core_graph_cover`

`vertical_core_graph_cover_proof` proves the statement `vertical_core_graph_cover`: a
compact set with finite own-Hausdorff square, upper growth and positive lower density
is covered, up to an `H^k_P`-null set, by regular full vertical graphs. The proof
assembles the intermediate results of the carrier construction:

* retained pieces `vertical_core_retained_pieces_proof`, the carrier family
  `exists_isCarrierFamily_proof`, the ambient square bound
  `isCarrierFamily_verticalSquareBound_proof`, the large-scale square
  `partial_graph_large_scale_square_le_proof`, the normalization
  `normalize_partial_graph_proof`, similarity invariance of covers
  `hasRegularVerticalGraphCover_similarity_symm_proof`, the rank-zero time graph
  `rank_zero_partial_time_graph_proof` and countable unions
  `hasRegularVerticalGraphCover_of_iUnion_proof`;
* coherence and center heights `isCarrierFamily_isCoherent_proof` and
  `isCarrierFamily_hasCenterHeight_proof`, applied to the beta point bound
  `betaSq_le_lintegral_Icc_proof`;
* regular extension of partial graphs with small vertical square,
  `exists_regular_graphs_of_vertical_square_proof`;
* small partial graphs `smallPartialGraphs` (the statement `exists_small_partial_graphs`);
* the vertical coherent chart `NeckHubTree.vertical_coherent_chart_proof`.

The separate rank-zero regular-extension bridge is not used.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-- Step 1 of the carrier construction (the statement `partial_graph_regular_cover`): a
compact partial graph of slope `ℓ ≤ L₀` inside a retained piece has a regular vertical graph
cover at tolerance `C ℓ`, by the large-scale square bound, normalization, regular extension
and similarity invariance. -/
theorem partial_graph_regular_cover_proof (n m : ℕ) :
    ∃ L₀ C : ℝ, 0 < L₀ ∧ L₀ ≤ 1 ∧ 0 < C ∧
      ∀ (W : Submodule ℝ (Spatial n)), Module.finrank ℝ W = m →
      ∀ (K : Set (Space n)) (D : Set (SubspaceSpace W))
        (g : SubspaceSpace W → W.orthogonal) (ℓ : ℝ≥0) (T b ρ : ℝ) (z₀ : Space n),
        (ℓ : ℝ) ≤ L₀ → 0 < T → 0 ≤ b → b ≤ (ℓ : ℝ) ^ 2 → 0 < ρ → ρ ≤ T →
        IsCompact (verticalLift W g '' D) → verticalLift W g '' D ⊆ K →
        verticalLift W g '' D ⊆ Metric.ball z₀ ρ → LipschitzOnWith ℓ g D →
        (∀ z ∈ verticalLift W g '' D,
          squareEnergy ((hausdorffP n (m + 2)).restrict K) (m + 2) .vertical T z ≤
            ENNReal.ofReal b) →
        HasRegularVerticalGraphCover (m + 2) (verticalLift W g '' D) (C * ℓ) := by
  obtain ⟨L₀, hL₀, hL₀1, h6⟩ := exists_regular_graphs_of_vertical_square_proof m
  obtain ⟨C₆, hC₆, h6⟩ := h6 (n - m)
  obtain ⟨C₅, hC₅, h5⟩ := partial_graph_large_scale_square_le_proof m
  refine ⟨L₀, C₆ * (1 + Real.sqrt (1 + C₅)), hL₀, hL₀1,
    mul_pos hC₆ (by have := Real.sqrt_nonneg (1 + C₅); linarith), ?_⟩
  intro W hW K D g ℓ T b ρ z₀ hℓ hT hb hbℓ hρ hρT hSc hSK hSρ hg htail
  have hWd : Module.finrank ℝ W.orthogonal = n - m := by
    have := subspace_finrank_add_normal W
    omega
  have hℓ1 : (ℓ : ℝ) ≤ 1 := hℓ.trans hL₀1
  have hℓ0 : (0 : ℝ) ≤ ℓ := ℓ.2
  have hC₅' : (0 : ℝ) ≤ 1 + C₅ := by linarith
  set B₀ : ℝ := (1 + C₅) * (ℓ : ℝ) ^ 2 with hB₀
  have hX : C₅ * (ℓ : ℝ) ^ 2 * (ρ / T) ^ (m + 4) / ((m : ℝ) + 4) ≤ C₅ * (ℓ : ℝ) ^ 2 := by
    have h1 : (ρ / T) ^ (m + 4) ≤ 1 :=
      pow_le_one₀ (div_nonneg hρ.le hT.le) ((div_le_one hT).2 hρT)
    have h2 : C₅ * (ℓ : ℝ) ^ 2 * (ρ / T) ^ (m + 4) ≤ C₅ * (ℓ : ℝ) ^ 2 :=
      mul_le_of_le_one_right (mul_nonneg hC₅.le (sq_nonneg _)) h1
    have h3 : (1 : ℝ) ≤ (m : ℝ) + 4 := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact (div_le_self (mul_nonneg (mul_nonneg hC₅.le (sq_nonneg _))
      (pow_nonneg (div_nonneg hρ.le hT.le) _)) h3).trans h2
  have hX0 : 0 ≤ C₅ * (ℓ : ℝ) ^ 2 * (ρ / T) ^ (m + 4) / ((m : ℝ) + 4) :=
    div_nonneg (mul_nonneg (mul_nonneg hC₅.le (sq_nonneg _))
      (pow_nonneg (div_nonneg hρ.le hT.le) _)) (by positivity)
  have hfull : ∀ p ∈ D, ∫⁻ s in Ioi 0,
      betaSq ((hausdorffP n (m + 2)).restrict (verticalLift W g '' D)) (m + 2) .vertical
        (verticalLift W g p) s ∂scaleMeasure ≤ ENNReal.ofReal B₀ := by
    intro p hp
    have hz : verticalLift W g p ∈ verticalLift W g '' D := mem_image_of_mem _ hp
    calc _ ≤ squareEnergy ((hausdorffP n (m + 2)).restrict (verticalLift W g '' D)) (m + 2)
            .vertical T (verticalLift W g p) +
          ∫⁻ s in Ici T, betaSq ((hausdorffP n (m + 2)).restrict (verticalLift W g '' D))
            (m + 2) .vertical (verticalLift W g p) s ∂scaleMeasure :=
          lintegral_Ioi_betaSq_le _ _ _ _
      _ ≤ ENNReal.ofReal b +
          ENNReal.ofReal (C₅ * (ℓ : ℝ) ^ 2 * (ρ / T) ^ (m + 4) / ((m : ℝ) + 4)) := by
          gcongr
          · exact (squareEnergy_mono_measure (Measure.restrict_mono_set _ hSK) _ _ _ _).trans
              (htail _ hz)
          · exact h5 W hW D g ℓ hℓ1 hg z₀ ρ T hρ hT hSρ _
      _ ≤ ENNReal.ofReal B₀ := by
          rw [← ENNReal.ofReal_add hb hX0]
          apply ENNReal.ofReal_le_ofReal
          have hsplit : B₀ = (ℓ : ℝ) ^ 2 + C₅ * (ℓ : ℝ) ^ 2 := by rw [hB₀]; ring
          rw [hsplit]
          linarith
  obtain ⟨q, a, ha, D', g', hD'c, hD'1, hg', himg, hB'⟩ :=
    normalize_partial_graph_proof (m + 2) W D g ℓ B₀ z₀ ρ hρ hSc hSρ hg hfull
  have hB0 : 0 ≤ B₀ := mul_nonneg hC₅' (sq_nonneg _)
  obtain ⟨I, G, hG, hnull⟩ := h6 W hW hWd D' g' ℓ B₀ hD'c hD'1 hg' hℓ hB0
    (ae_restrict_of_forall_mem hD'c.isClosed.measurableSet hB')
  have hcov := hasRegularVerticalGraphCover_of_sameBase W hW (verticalLift W g' '' D') _ I G
    hG hnull
  have hcov' := hasRegularVerticalGraphCover_similarity_symm_proof q a ha hcov
  have hback : (similarity q a ha).symm '' (verticalLift W g' '' D') =
      verticalLift W g '' D := by
    rw [himg, image_image]
    simp only [Homeomorph.symm_apply_apply, image_id']
  rw [hback] at hcov'
  refine hcov'.mono (le_of_eq ?_)
  have hsq : Real.sqrt B₀ = Real.sqrt (1 + C₅) * ℓ := by
    rw [hB₀, Real.sqrt_mul hC₅', Real.sqrt_sq hℓ0]
  rw [hsq]
  ring

/-- Step 2 of the carrier construction (the statement `carrier_piece_cover_of_pos`), spatial
rank `m ≥ 1`: carrier family, coherence, center heights, ambient square bound, the vertical
coherent chart, small partial graphs and countable unions. -/
theorem carrier_piece_cover_of_pos_proof (n m : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ∀ U : ℝ, 0 ≤ U → ∀ a : ℝ, 0 < a →
      ∃ b : ℝ, 0 < b ∧ ∀ (K : Set (Space n)) (T : ℝ) (F : Set (Space n)) (z₀ : Space n),
        hausdorffP n (m + 2) K < ⊤ → 0 < T →
        HasUpperGrowthUpTo ((hausdorffP n (m + 2)).restrict K) (m + 2) U T →
        F ⊆ K → F ⊆ Metric.ball z₀ (c * T) →
        IsCarrierPiece ((hausdorffP n (m + 2)).restrict K) (m + 2) a b T F →
        HasRegularVerticalGraphCover (m + 2) F ε := by
  obtain ⟨L₀, Cp, hL₀, hL₀1, hCp, hpipe⟩ := partial_graph_regular_cover_proof n m
  obtain ⟨δ₀, E₀, κ₀, Cch, hδ₀, hE₀, hκ₀, hCch, hchart⟩ :=
    NeckHubTree.vertical_coherent_chart_proof.{0} n 1 one_pos le_rfl
  obtain ⟨A₂, hA₂, h2⟩ := isCarrierFamily_isCoherent_proof betaSq_le_lintegral_Icc_proof n m hm (Λ := 21) le_rfl
  obtain ⟨A₃, C₃, hA₃, hC₃, h3⟩ := isCarrierFamily_hasCenterHeight_proof betaSq_le_lintegral_Icc_proof n m (Λ := 21) (by norm_num)
  obtain ⟨A₄, hA₄, h4⟩ := isCarrierFamily_verticalSquareBound_proof n m hm (Λ := 21) le_rfl
  set S : ℝ := A₂ + A₃ + A₄ + 1 with hS
  have hSpos : 0 < S := by linarith
  have hS1 : 1 ≤ S := by linarith
  refine ⟨1 / (2 * S), div_pos one_pos (by linarith), ?_, ?_⟩
  · rw [div_le_one (by linarith)]
    linarith
  intro ε hε U hU a ha
  obtain ⟨K₂, hK₂, h2a⟩ := h2 a U ha hU
  obtain ⟨K₄, hK₄, h4a⟩ := h4 a U ha hU
  -- the target slope `ℓ`, fixed from `ε` before `U` and `a`
  set ℓr : ℝ := min (1 / 2) (min L₀ (ε / Cp)) with hℓr
  have hℓpos : 0 < ℓr := lt_min (by norm_num) (lt_min hL₀ (div_pos hε hCp))
  have hℓhalf : ℓr ≤ 1 / 2 := min_le_left _ _
  have hℓL₀ : ℓr ≤ L₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hℓε : ℓr ≤ ε / Cp := (min_le_right _ _).trans (min_le_right _ _)
  -- the coherence target `δ'`
  set δ' : ℝ := min δ₀ (ℓr / (2 * Cch)) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ₀ (div_pos hℓpos (by linarith))
  -- the budget `b = b(a, U, ℓ)`
  set P₃ : ℝ := C₃ * 21 ^ (m + 4) with hP₃
  set Q₃ : ℝ := C₃ * (2 * 21) ^ (m + 4) with hQ₃
  have hP₃pos : 0 < P₃ := mul_pos hC₃ (by positivity)
  have hQ₃pos : 0 < Q₃ := mul_pos hC₃ (by positivity)
  set b : ℝ := min (ℓr ^ 2) (min (δ' ^ 2 / K₂) (min (E₀ / K₄)
    (min (a / (2 * P₃)) (κ₀ ^ (m + 4) * a / Q₃)))) with hbdef
  have hbpos : 0 < b := lt_min (pow_pos hℓpos 2) (lt_min (div_pos (pow_pos hδ'pos 2) hK₂)
    (lt_min (div_pos hE₀ hK₄) (lt_min (div_pos ha (by linarith))
      (div_pos (mul_pos (pow_pos hκ₀ _) ha) hQ₃pos))))
  have hb1 : b ≤ ℓr ^ 2 := min_le_left _ _
  have hb2 : b ≤ δ' ^ 2 / K₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hb3 : b ≤ E₀ / K₄ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb4 : b ≤ a / (2 * P₃) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hb5 : b ≤ κ₀ ^ (m + 4) * a / Q₃ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨b, hbpos, ?_⟩
  intro K T F z₀ hfin hT hgrowth hFK hFz hpiece
  have : IsFiniteMeasure ((hausdorffP n (m + 2)).restrict K) := hausdorffP_restrict_isFinite hfin
  -- the initial radius `R = T / S`; every family estimate sees `A R ≤ T`
  set R : ℝ := T / S with hR
  have hRpos : 0 < R := div_pos hT hSpos
  have hAR : ∀ A : ℝ, 0 ≤ A → A ≤ S → A * R ≤ T := by
    intro A hA hAS
    rw [hR, mul_div_assoc', div_le_iff₀ hSpos]
    calc A * T ≤ S * T := mul_le_mul_of_nonneg_right hAS hT.le
      _ = T * S := mul_comm _ _
  have hRhalf : R / 2 = 1 / (2 * S) * T := by
    rw [hR, div_div, one_div_mul_eq_div, mul_comm S 2]
  obtain ⟨Φ, hΦR, hΦ⟩ := exists_isCarrierFamily_proof (m := m) hmn.le
    ((hausdorffP n (m + 2)).restrict K) hpiece.compact z₀ hRpos (by rw [hRhalf]; exact hFz)
    (Λ := 21) (by norm_num)
  have hcoh := h2a _ F R T b Φ hRpos (hAR A₂ hA₂.le (by linarith)) hbpos.le hΦR hΦ hgrowth hpiece
  have hsq := h4a _ F R T b Φ hRpos (hAR A₄ hA₄.le (by linarith)) hbpos.le hΦR hΦ hgrowth hpiece
  have h3a : P₃ * b < a := by
    have := (le_div_iff₀ (by linarith)).1 hb4
    linarith [mul_pos hP₃pos hbpos]
  have h3b : Q₃ * b ≤ κ₀ ^ (m + 4) * a := by
    have := (le_div_iff₀ hQ₃pos).1 hb5
    linarith
  have hht := h3 _ F R T a b κ₀ Φ hRpos (hAR A₃ hA₃.le (by linarith)) ha hbpos.le hκ₀ hΦR hΦ
    hpiece h3a h3b
  -- the vertical coherent chart with `δ = √(K₂ b)` and `E = K₄ b`
  set δ : ℝ := Real.sqrt (K₂ * b) with hδdef
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hδδ' : δ ≤ δ' := by
    have hK : K₂ * b ≤ δ' ^ 2 := by
      have := (le_div_iff₀ hK₂).1 hb2
      linarith
    calc δ ≤ Real.sqrt (δ' ^ 2) := Real.sqrt_le_sqrt hK
      _ = δ' := Real.sqrt_sq hδ'pos.le
  have hδδ₀ : δ ≤ δ₀ := hδδ'.trans (min_le_left _ _)
  have hδℓ : Cch * δ ≤ ℓr / 2 := by
    have h : δ ≤ ℓr / (2 * Cch) := hδδ'.trans (min_le_right _ _)
    rw [le_div_iff₀ (by linarith)] at h
    linarith
  have hE : K₄ * b ≤ E₀ := by
    have := (le_div_iff₀ hK₄).1 hb3
    linarith
  obtain ⟨G, hbilip, htime, -, hcover⟩ :=
    hchart Φ δ (K₄ * b) hδ0 hδδ₀ (mul_pos hK₄ hbpos).le hE hcoh hsq
  obtain ⟨hlim, -⟩ := hcover κ₀ hκ₀.le le_rfl hht
  have hFrange : ∀ z ∈ F, z ∈ Set.range (timePreservingMap G) :=
    fun z hz => hlim z (hΦ.isLevelLimit hz)
  -- the chart in the form required by `smallPartialGraphs`
  set Ψ : Space m → Space n := fun z => ((G z.1 z.2.val, z.2) : Space n) with hΨ
  have hΨlip : ∀ p p' : Space m, dist (Ψ p) (Ψ p') ≤ 11 / 10 * dist p p' :=
    fun p p' => (hbilip p p').2
  have hΨcont : Continuous Ψ := (LipschitzWith.of_dist_le' hΨlip).continuous
  have hFcont : Continuous (fun z : Space m => G z.1 z.2.val) := continuous_fst.comp hΨcont
  have hlower : ∀ (u v : Spatial m) (t : ℝ), 4 / 5 * ‖u - v‖ ≤ ‖G u t - G v t‖ := by
    intro u v t
    have h := (hbilip (point u t) (point v t)).1
    change 4 / 5 * dist (point u t) (point v t) ≤
      dist (point (G u t) t) (point (G v t) t) at h
    rwa [dist_point_same_time, dist_point_same_time] at h
  have hupper : ∀ (u v : Spatial m) (t : ℝ), ‖G u t - G v t‖ ≤ 11 / 10 * ‖u - v‖ := by
    intro u v t
    have h := (hbilip (point u t) (point v t)).2
    change dist (point (G u t) t) (point (G v t) t) ≤
      11 / 10 * dist (point u t) (point v t) at h
    rwa [dist_point_same_time, dist_point_same_time] at h
  have htime' : ∀ (u : Spatial m) (t s : ℝ),
      ‖G u t - G u s‖ ≤ (Cch * δ) * Real.sqrt |t - s| := fun u t s => htime u t s
  have hAclosed : IsClosed (Ψ ⁻¹' F) := hpiece.compact.isClosed.preimage hΨcont
  have hslope : 8 * (ℓr / 20) / (4 / 5) + Cch * δ ≤ ℓr := by
    have : 8 * (ℓr / 20) / (4 / 5 : ℝ) = ℓr / 2 := by ring
    linarith
  obtain ⟨I, P, hP, -, hHnull⟩ := smallPartialGraphs hm
    (fun z : Space m => G z.1 z.2.val) hFcont (4 / 5) (11 / 10) (Cch * δ) (by norm_num)
    (by norm_num) (mul_nonneg hCch.le hδ0) (by linarith) hlower hupper htime' (Ψ ⁻¹' F)
    hAclosed.measurableSet.nullMeasurableSet (ℓr / 20) (by linarith) (by linarith)
  -- each partial graph is covered by step 1
  let ℓ : ℝ≥0 := ⟨ℓr, hℓpos.le⟩
  have hρ : 0 < 1 / (2 * S) * T := mul_pos (div_pos one_pos (by linarith)) hT
  have hρT : 1 / (2 * S) * T ≤ T := by
    have h : 1 / (2 * S) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    calc 1 / (2 * S) * T ≤ 1 * T := mul_le_mul_of_nonneg_right h hT.le
      _ = T := one_mul T
  have hpieces : ∀ j : I, HasRegularVerticalGraphCover (m + 2) (Ψ '' P j) ε := by
    intro j
    obtain ⟨hPc, hPA, W, D, g, hW, hgd, himg⟩ := hP j
    have himg' : Ψ '' P j = verticalLift W g '' D := himg
    have hsub : verticalLift W g '' D ⊆ F := by
      rw [← himg']
      rintro _ ⟨p, hp, rfl⟩
      exact hPA hp
    have hg : LipschitzOnWith ℓ g D := LipschitzOnWith.of_dist_le_mul fun p hp q hq =>
      (hgd p hp q hq).trans (mul_le_mul_of_nonneg_right hslope dist_nonneg)
    rw [himg']
    refine (hpipe W hW K D g ℓ T b (1 / (2 * S) * T) z₀ hℓL₀ hT hbpos.le hb1 hρ hρT
      (by rw [← himg']; exact hPc.image hΨcont) (hsub.trans hFK) (hsub.trans hFz) hg
      (fun z hz => hpiece.small_tail z (hsub hz))).mono ?_
    have := (le_div_iff₀ hCp).1 hℓε
    change Cp * ℓr ≤ ε
    linarith
  -- the pieces cover the retained set up to an `H^k_P`-null set
  have hcover_null : hausdorffP n (m + 2) (F \ ⋃ j : I, Ψ '' P j) = 0 := by
    refine measure_mono_null ?_ hHnull
    rintro x ⟨hxF, hxU⟩
    obtain ⟨p, rfl⟩ := hFrange x hxF
    refine ⟨p, ⟨hxF, fun hp => hxU ?_⟩, rfl⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 hp
    exact mem_iUnion.2 ⟨j, mem_image_of_mem Ψ hj⟩
  exact hasRegularVerticalGraphCover_of_iUnion_proof (fun j : I => Ψ '' P j) hcover_null hpieces

/-- Step 3 of the carrier construction (the statement `carrier_piece_cover_of_rank_zero`),
spatial rank zero: the two-ball time graph and step 1. -/
theorem carrier_piece_cover_of_rank_zero_proof (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ∀ U : ℝ, 0 ≤ U → ∀ a : ℝ, 0 < a →
      ∃ b : ℝ, 0 < b ∧ ∀ (K : Set (Space n)) (T : ℝ) (F : Set (Space n)) (z₀ : Space n),
        hausdorffP n (0 + 2) K < ⊤ → 0 < T →
        HasUpperGrowthUpTo ((hausdorffP n (0 + 2)).restrict K) (0 + 2) U T →
        F ⊆ K → F ⊆ Metric.ball z₀ (c * T) →
        IsCarrierPiece ((hausdorffP n (0 + 2)).restrict K) (0 + 2) a b T F →
        HasRegularVerticalGraphCover (0 + 2) F ε := by
  obtain ⟨L₀, Cp, hL₀, hL₀1, hCp, hpipe⟩ := partial_graph_regular_cover_proof n 0
  obtain ⟨A₈, C₈, hA₈, hC₈, h8⟩ := rank_zero_partial_time_graph_proof n
  have hA₈1 : 0 < A₈ + 1 := by linarith
  refine ⟨1 / (A₈ + 1), div_pos one_pos hA₈1, ?_, ?_⟩
  · rw [div_le_one hA₈1]
    linarith
  intro ε hε U hU a ha
  set ℓr : ℝ := min (1 / 2) (min L₀ (ε / Cp)) with hℓr
  have hℓpos : 0 < ℓr := lt_min (by norm_num) (lt_min hL₀ (div_pos hε hCp))
  have hℓhalf : ℓr ≤ 1 / 2 := min_le_left _ _
  have hℓL₀ : ℓr ≤ L₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hℓε : ℓr ≤ ε / Cp := (min_le_right _ _).trans (min_le_right _ _)
  set b : ℝ := min (ℓr ^ 2) (ℓr ^ 4 * a / C₈) with hbdef
  have hbpos : 0 < b := lt_min (pow_pos hℓpos 2) (div_pos (mul_pos (pow_pos hℓpos 4) ha) hC₈)
  have hb1 : b ≤ ℓr ^ 2 := min_le_left _ _
  have hCb : C₈ * b ≤ ℓr ^ 4 * a := by
    have := (le_div_iff₀ hC₈).1 (min_le_right (ℓr ^ 2) (ℓr ^ 4 * a / C₈))
    linarith
  refine ⟨b, hbpos, ?_⟩
  intro K T F z₀ hfin hT hgrowth hFK hFz hpiece
  let ℓ : ℝ≥0 := ⟨ℓr, hℓpos.le⟩
  have hρ : 0 < 1 / (A₈ + 1) * T := mul_pos (div_pos one_pos hA₈1) hT
  have hAρ : A₈ * (1 / (A₈ + 1) * T) ≤ T := by
    have h : A₈ * (1 / (A₈ + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one hA₈1]
      linarith
    calc A₈ * (1 / (A₈ + 1) * T) = A₈ * (1 / (A₈ + 1)) * T := by ring
      _ ≤ 1 * T := mul_le_mul_of_nonneg_right h hT.le
      _ = T := one_mul T
  have hρT : 1 / (A₈ + 1) * T ≤ T := by
    have h : 1 / (A₈ + 1) ≤ 1 := by
      rw [div_le_one hA₈1]
      linarith
    calc 1 / (A₈ + 1) * T ≤ 1 * T := mul_le_mul_of_nonneg_right h hT.le
      _ = T := one_mul T
  obtain ⟨W, D, g, hW, hg, hFeq⟩ := h8 ((hausdorffP n (0 + 2)).restrict K) F z₀
    (1 / (A₈ + 1) * T) T a b ℓ hρ hAρ ha hbpos.le (by change ℓr < 1; linarith) hFz hpiece hCb
  subst hFeq
  refine (hpipe W hW K D g ℓ T b (1 / (A₈ + 1) * T) z₀ hℓL₀ hT hbpos.le hb1 hρ hρT
    hpiece.compact hFK hFz hg hpiece.small_tail).mono ?_
  have := (le_div_iff₀ hCp).1 hℓε
  change Cp * ℓr ≤ ε
  linarith

/-- Steps 2 and 3 combined (the statement `carrier_piece_cover`), for every spatial rank
`0 ≤ m < n`. -/
theorem carrier_piece_cover_proof (n m : ℕ) (hmn : m < n) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ∀ U : ℝ, 0 ≤ U → ∀ a : ℝ, 0 < a →
      ∃ b : ℝ, 0 < b ∧ ∀ (K : Set (Space n)) (T : ℝ) (F : Set (Space n)) (z₀ : Space n),
        hausdorffP n (m + 2) K < ⊤ → 0 < T →
        HasUpperGrowthUpTo ((hausdorffP n (m + 2)).restrict K) (m + 2) U T →
        F ⊆ K → F ⊆ Metric.ball z₀ (c * T) →
        IsCarrierPiece ((hausdorffP n (m + 2)).restrict K) (m + 2) a b T F →
        HasRegularVerticalGraphCover (m + 2) F ε := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact carrier_piece_cover_of_rank_zero_proof n
  · exact carrier_piece_cover_of_pos_proof n m hm hmn

/-- **Regular vertical carrier** (the statement `vertical_core_graph_cover`): finite own-Hausdorff square, upper growth and positive lower density
yield regular full vertical graphs, including spatial rank zero. The slope is fixed from `ε`; for
every density level `2^{-j}` the budget is chosen from `(U, ℓ)`; then the retained pieces and their
scales (`vertical_core_retained_pieces_proof`); countable unions assemble the countably many piece covers, whose exceptions and the remainder of the retained pieces are
`H^k_P`-null. -/
theorem vertical_core_graph_cover_proof {n k : ℕ} {K : Set (Space n)}
    (hK : IsVerticalCore k K) (ε : ℝ) (hε : 0 < ε) :
    HasRegularVerticalGraphCover k K ε := by
  obtain ⟨hk2, hkn, hKc, hfin, U, r₀, hU, hr₀, hgrowth, hae⟩ := hK
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  obtain ⟨c, hc, -, hpiece⟩ := carrier_piece_cover_proof n m (by omega)
  have hpiece := hpiece ε hε U hU
  choose b hbpos hcov using hpiece
  obtain ⟨level, T, ctr, F, hT, hF, hnull⟩ :=
    vertical_core_retained_pieces_proof hKc hfin r₀ hr₀ hae c hc
      (fun j => b ((1 / 2 : ℝ) ^ j) (by positivity)) (fun j => hbpos _ _)
  refine hasRegularVerticalGraphCover_of_iUnion_proof F hnull fun i => ?_
  obtain ⟨hFK, hFz, hFpiece⟩ := hF i
  exact hcov _ _ K (T i) (F i) (ctr i) hfin (hT i).1
    (fun q r hr hrT => hgrowth q r hr (hrT.trans (hT i).2)) hFK hFz hFpiece

end ParabolicRectifiability
