import ParabolicRectifiability.Basic

/-! # Spatial graph pieces of a Euclidean bi-Lipschitz chart

A compact small-diameter cover up to a null set, the Rademacher linearization of a
bi-Lipschitz map, the normal slope over the range of the linearization, and the resulting
compact spatial graph pieces `exists_spatial_graph_pieces_proof`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-! ## Compact small-diameter cover up to a null set -/

/-- **Compact cover.** For a sigma-finite measure that is inner regular with
respect to compact sets, every measurable set is covered, up to a `μ`-null set, by
countably many compact subsets in each of which all distances are less than `δ`.

Each finite-measure slice `E ∩ spanningSets μ n` is approximated from inside by compact
sets `K n m` with defect below `1/m`; each `K n m` is then cut into the finitely many
compact pieces `K n m ∩ closedBall x (δ/3)` with centers from a finite `δ/3`-net. -/
theorem exists_compact_small_cover_ae_proof {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [SigmaFinite μ] [μ.InnerRegular] {E : Set X}
    (hE : MeasurableSet E) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℕ → Set X, (∀ j, IsCompact (C j)) ∧ (∀ j, C j ⊆ E) ∧
      (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y < δ) ∧ μ (E \ ⋃ j, C j) = 0 := by
  classical
  -- Compact inner approximation of the finite-measure slices.
  have happrox : ∀ n m : ℕ, ∃ K : Set X, K ⊆ E ∩ spanningSets μ n ∧ IsCompact K ∧
      μ ((E ∩ spanningSets μ n) \ K) < (m : ℝ≥0∞)⁻¹ := fun n m =>
    (hE.inter (measurableSet_spanningSets μ n)).exists_isCompact_sdiff_lt
      ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m))
  choose K hKsub hKc hKμ using happrox
  -- Finite `δ/3`-nets of the compact sets.
  have hnet : ∀ n m, ∃ t : Set X, t ⊆ K n m ∧ t.Finite ∧
      K n m ⊆ ⋃ x ∈ t, Metric.ball x (δ / 3) :=
    fun n m => (hKc n m).finite_cover_balls (by positivity)
  choose T _hTsub hTfin hTcov using hnet
  -- The countable family of small compact pieces, with `∅` added for nonemptiness.
  let P : Set (Set X) :=
    insert ∅ (⋃ n, ⋃ m, (fun x => K n m ∩ Metric.closedBall x (δ / 3)) '' T n m)
  have hPc : P.Countable :=
    (Set.countable_iUnion fun n => Set.countable_iUnion fun m =>
      ((hTfin n m).image _).countable).insert ∅
  obtain ⟨C, hC⟩ := hPc.exists_eq_range (Set.insert_nonempty _ _)
  have hmem : ∀ j, C j = ∅ ∨ ∃ n m x, C j = K n m ∩ Metric.closedBall x (δ / 3) := by
    intro j
    have hj : C j ∈ P := by rw [hC]; exact Set.mem_range_self j
    rcases Set.mem_insert_iff.1 hj with h | h
    · exact Or.inl h
    · simp only [Set.mem_iUnion, Set.mem_image] at h
      obtain ⟨n, m, x, -, hx⟩ := h
      exact Or.inr ⟨n, m, x, hx.symm⟩
  refine ⟨C, fun j => ?_, fun j => ?_, fun j => ?_, ?_⟩
  · rcases hmem j with h | ⟨n, m, x, h⟩
    · rw [h]; exact isCompact_empty
    · rw [h]; exact (hKc n m).inter_right Metric.isClosed_closedBall
  · rcases hmem j with h | ⟨n, m, x, h⟩
    · rw [h]; exact Set.empty_subset _
    · rw [h]; exact Set.inter_subset_left.trans ((hKsub n m).trans Set.inter_subset_left)
  · rcases hmem j with h | ⟨n, m, x, h⟩
    · rw [h]; intro y hy; exact hy.elim
    · rw [h]
      rintro y ⟨-, hy⟩ z ⟨-, hz⟩
      calc dist y z ≤ dist y x + dist z x := dist_triangle_right y z x
        _ ≤ δ / 3 + δ / 3 :=
          add_le_add (Metric.mem_closedBall.1 hy) (Metric.mem_closedBall.1 hz)
        _ < δ := by linarith
  · -- Every point of `E` outside the pieces lies outside all `K n m` of its slice.
    have hsub : E \ ⋃ j, C j ⊆ ⋃ n, ((E ∩ spanningSets μ n) \ ⋃ m, K n m) := by
      rintro y ⟨hyE, hyC⟩
      have hy : y ∈ ⋃ n, spanningSets μ n := by
        rw [iUnion_spanningSets]; exact Set.mem_univ y
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hy
      refine Set.mem_iUnion.2 ⟨n, ⟨hyE, hn⟩, ?_⟩
      intro hyK
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hyK
      have hball := hTcov n m hm
      simp only [Set.mem_iUnion] at hball
      obtain ⟨x, hx, hyx⟩ := hball
      have hin : K n m ∩ Metric.closedBall x (δ / 3) ∈ Set.range C := by
        rw [← hC]
        refine Set.mem_insert_of_mem _ ?_
        simp only [Set.mem_iUnion, Set.mem_image]
        exact ⟨n, m, x, hx, rfl⟩
      obtain ⟨j, hj⟩ := hin
      apply hyC
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      rw [hj]
      exact ⟨hm, Metric.ball_subset_closedBall hyx⟩
    refine measure_mono_null hsub (measure_iUnion_null fun n => ?_)
    refine le_antisymm ?_ zero_le
    refine ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun m => ?_
    exact (measure_mono (Set.sdiff_subset_sdiff_right (Set.subset_iUnion (K n) m))).trans
      (hKμ n m).le

/-! ## Lebesgue-null parameter sets are `μH[k]`-null -/

/-- A Lebesgue-null subset of `ℝ^k` is `μH[k]`-null. The coordinate map
`(Fin k → ℝ) → ℝ^k` is Lipschitz and volume preserving, and `μH[k] = volume` on
`Fin k → ℝ` (`hausdorffMeasure_pi_real`). -/
theorem spatial_hausdorffMeasure_eq_zero_of_volume_eq_zero {k : ℕ} {E : Set (Spatial k)}
    (hE : (volume : Measure (Spatial k)) E = 0) :
    (Measure.hausdorffMeasure (k : ℝ) : Measure (Spatial k)) E = 0 := by
  have hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin k → ℝ))
      (volume : Measure (Fin k → ℝ)) (volume : Measure (Spatial k)) :=
    PiLp.volume_preserving_toLp (Fin k)
  have hpre : (volume : Measure (Fin k → ℝ)) (MeasurableEquiv.toLp 2 (Fin k → ℝ) ⁻¹' E) = 0 := by
    rw [← MeasurableEquiv.map_apply, hmp.map_eq]
    exact hE
  have hH : (Measure.hausdorffMeasure (k : ℝ) : Measure (Fin k → ℝ))
      (MeasurableEquiv.toLp 2 (Fin k → ℝ) ⁻¹' E) = 0 := by
    have h := hausdorffMeasure_pi_real (ι := Fin k)
    rw [Fintype.card_fin] at h
    rw [h]
    exact hpre
  have himg : MeasurableEquiv.toLp 2 (Fin k → ℝ) '' (MeasurableEquiv.toLp 2 (Fin k → ℝ) ⁻¹' E) =
      E := Set.image_preimage_eq E (MeasurableEquiv.toLp 2 (Fin k → ℝ)).surjective
  have hlip : LipschitzWith ((Fintype.card (Fin k) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal)
      (MeasurableEquiv.toLp 2 (Fin k → ℝ) : (Fin k → ℝ) → Spatial k) :=
    PiLp.lipschitzWith_toLp 2 (fun _ : Fin k => ℝ)
  refine nonpos_iff_eq_zero.1 ?_
  calc (Measure.hausdorffMeasure (k : ℝ) : Measure (Spatial k)) E
      = (Measure.hausdorffMeasure (k : ℝ) : Measure (Spatial k))
          (MeasurableEquiv.toLp 2 (Fin k → ℝ) '' (MeasurableEquiv.toLp 2 (Fin k → ℝ) ⁻¹' E)) := by
        rw [himg]
    _ ≤ _ * (Measure.hausdorffMeasure (k : ℝ) : Measure (Fin k → ℝ))
          (MeasurableEquiv.toLp 2 (Fin k → ℝ) ⁻¹' E) :=
        hlip.hausdorffMeasure_image_le (Nat.cast_nonneg k) _
    _ = 0 := by rw [hH, mul_zero]

/-! ## Linearization of the global spatial chart -/

/-- An antilipschitz map has derivatives with the same lower bound: if
`‖x - y‖ ≤ L ‖F x - F y‖` and `F` has derivative `A` at `y`, then `‖v‖ ≤ L ‖A v‖`.
Let `t → 0⁺` in `t ‖v‖ ≤ L ‖F (y + t v) - F y‖`. -/
theorem norm_le_mul_norm_apply_of_hasFDerivAt_of_antilipschitz {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {L : ℝ≥0} (hF' : AntilipschitzWith L F) {y : E} {A : E →L[ℝ] G}
    (hA : HasFDerivAt F A y) (v : E) :
    ‖v‖ ≤ (L : ℝ) * ‖A v‖ := by
  have hlim : Tendsto (fun t : ℝ => (L : ℝ) * ‖t⁻¹ • (F (y + t • v) - F y)‖) (𝓝[>] 0)
      (𝓝 ((L : ℝ) * ‖A v‖)) :=
    ((hA.hasLineDerivAt v).tendsto_slope_zero_right.norm).const_mul _
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have h1 := hF'.le_mul_dist (y + t • v) y
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg ht.le] at h1
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le)]
  calc ‖v‖ = t⁻¹ * (t * ‖v‖) := (inv_mul_cancel_left₀ ht.ne' _).symm
    _ ≤ t⁻¹ * ((L : ℝ) * ‖F (y + t • v) - F y‖) :=
      mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 ht.le)
    _ = (L : ℝ) * (t⁻¹ * ‖F (y + t • v) - F y‖) := by ring

/-- **Linearization.** Rademacher decomposition of
a global Euclidean bi-Lipschitz map: measurable parameter pieces covering `ℝ^k` up to a
Lebesgue-null set, on each of which `F` is `α`-approximated by a derivative `A m` with
`‖v‖ ≤ L ‖A m v‖`.

The pieces are `D ∩ t m` for the differentiability set `D` (full measure by Rademacher's
theorem, measurable) and the measurable partition of mathlib. Each `A m` is a derivative at
a point of `D`, which is nonempty since its complement is null in a nonzero Haar measure. -/
theorem exists_spatial_linearization_pieces_proof {n k : ℕ} {F : Spatial k → Spatial n}
    {L : ℝ≥0} (hF : LipschitzWith L F) (hF' : AntilipschitzWith L F) {α : ℝ≥0} (hα : 0 < α) :
    ∃ (S : ℕ → Set (Spatial k)) (A : ℕ → Spatial k →L[ℝ] Spatial n),
      (∀ m, MeasurableSet (S m)) ∧ (∀ m, ApproximatesLinearOn F (A m) (S m) α) ∧
      (∀ m (v : Spatial k), ‖v‖ ≤ (L : ℝ) * ‖A m v‖) ∧
      (volume : Measure (Spatial k)) (⋃ m, S m)ᶜ = 0 := by
  let D : Set (Spatial k) := {x | DifferentiableAt ℝ F x}
  have hDmeas : MeasurableSet D := measurableSet_of_differentiableAt ℝ F
  have hDnull : (volume : Measure (Spatial k)) Dᶜ = 0 :=
    ae_iff.1 (hF.ae_differentiableAt (μ := (volume : Measure (Spatial k))))
  have hDne : D.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.compl_empty] at hDnull
    exact (NeZero.ne (volume : Measure (Spatial k))) (Measure.measure_univ_eq_zero.1 hDnull)
  obtain ⟨t, A, -, htmeas, hDt, happrox, hAeq⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F D (fderiv ℝ F)
      (fun x hx => (show DifferentiableAt ℝ F x from hx).hasFDerivAt.hasFDerivWithinAt)
      (fun _ => α) (fun _ => hα.ne')
  refine ⟨fun m => D ∩ t m, A, fun m => hDmeas.inter (htmeas m), happrox, ?_, ?_⟩
  · intro m v
    obtain ⟨y, hy, hyA⟩ := hAeq hDne m
    rw [hyA]
    exact norm_le_mul_norm_apply_of_hasFDerivAt_of_antilipschitz hF'
      (show DifferentiableAt ℝ F y from hy).hasFDerivAt v
  · refine measure_mono_null (Set.compl_subset_compl.2 ?_) hDnull
    intro x hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 (hDt hx)
    exact Set.mem_iUnion.2 ⟨m, hx, hm⟩

/-! ## Normal slope over the range of the linearization -/

/-- **Projection slope.** With `d = u - v`,
`Δ = F u - F v` and `W = range A`: `‖P_{W⊥} Δ‖ ≤ α ‖d‖` and
`(1 - α L) ‖d‖ ≤ L ‖P_W Δ‖`, which give the slope `α L / (1 - α L)` without dividing
by `L`. The lower bound makes `A` injective, so `W` has rank `k`. -/
theorem projection_slope_of_approximatesLinearOn_proof {n k : ℕ} {F : Spatial k → Spatial n}
    {A : Spatial k →L[ℝ] Spatial n} {S : Set (Spatial k)} {L α : ℝ≥0}
    (hA : ∀ v : Spatial k, ‖v‖ ≤ (L : ℝ) * ‖A v‖) (hFA : ApproximatesLinearOn F A S α)
    (hαL : (α : ℝ) * L < 1) :
    Module.finrank ℝ (LinearMap.range (A : Spatial k →ₗ[ℝ] Spatial n)) = k ∧
      ∀ u ∈ S, ∀ v ∈ S,
        ‖(LinearMap.range (A : Spatial k →ₗ[ℝ] Spatial n))ᗮ.starProjection (F u - F v)‖ ≤
          ((α : ℝ) * L / (1 - (α : ℝ) * L)) *
            ‖(LinearMap.range (A : Spatial k →ₗ[ℝ] Spatial n)).starProjection (F u - F v)‖ := by
  set W := LinearMap.range (A : Spatial k →ₗ[ℝ] Spatial n) with hW
  have hinj : Function.Injective (A : Spatial k →ₗ[ℝ] Spatial n) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h := hA v
    rw [show A v = 0 from hv, norm_zero, mul_zero] at h
    exact norm_le_zero_iff.1 h
  refine ⟨?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]
  · intro u hu v hv
    have hAd : A (u - v) ∈ W := LinearMap.mem_range_self _ (u - v)
    have hde : F u - F v = A (u - v) + (F u - F v - A (u - v)) := by abel
    have heb : ‖F u - F v - A (u - v)‖ ≤ (α : ℝ) * ‖u - v‖ := hFA u hu v hv
    have h1 : ‖Wᗮ.starProjection (F u - F v)‖ ≤ (α : ℝ) * ‖u - v‖ := by
      rw [hde, map_add, Submodule.starProjection_orthogonal_apply_eq_zero hAd, zero_add]
      exact (Submodule.norm_starProjection_apply_le _ _).trans heb
    have h2 : ‖A (u - v)‖ ≤ ‖W.starProjection (F u - F v)‖ + (α : ℝ) * ‖u - v‖ := by
      have hpar : W.starProjection (F u - F v) =
          A (u - v) + W.starProjection (F u - F v - A (u - v)) := by
        conv_lhs => rw [hde]
        rw [map_add, Submodule.starProjection_eq_self_iff.2 hAd]
      have h3 : ‖A (u - v)‖ ≤ ‖W.starProjection (F u - F v)‖ +
          ‖W.starProjection (F u - F v - A (u - v))‖ := by
        rw [hpar]
        simpa using norm_sub_le (A (u - v) + W.starProjection (F u - F v - A (u - v)))
          (W.starProjection (F u - F v - A (u - v)))
      have h4 := (Submodule.norm_starProjection_apply_le W (F u - F v - A (u - v))).trans heb
      linarith
    have hpos : 0 < 1 - (α : ℝ) * L := by linarith
    have h5 : (1 - (α : ℝ) * L) * ‖u - v‖ ≤ (L : ℝ) * ‖W.starProjection (F u - F v)‖ := by
      have h6 := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
      have h7 := hA (u - v)
      nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    calc ‖Wᗮ.starProjection (F u - F v)‖ * (1 - (α : ℝ) * L)
        ≤ ((α : ℝ) * ‖u - v‖) * (1 - (α : ℝ) * L) := mul_le_mul_of_nonneg_right h1 hpos.le
      _ = (α : ℝ) * ((1 - (α : ℝ) * L) * ‖u - v‖) := by ring
      _ ≤ (α : ℝ) * ((L : ℝ) * ‖W.starProjection (F u - F v)‖) :=
          mul_le_mul_of_nonneg_left h5 α.coe_nonneg
      _ = (α : ℝ) * L * ‖W.starProjection (F u - F v)‖ := by ring

/-! ## Compact spatial graph pieces -/

/-- **Compact spatial graph pieces.**
Countably many compact parameter pieces, covering `ℝ^k` up to a `μH[k]`-null set, over
each of which `F` is a graph of normal slope at most `s` over a rank-`k` subspace.

Take `α = s / ((1 + s)(L + 1))`, so `α L ≤ s/(1+s)` and `α L/(1 - α L) ≤ s`; linearize
(linearization), bound the slope (projection slope), cover each measurable piece by compact
subsets up to a Lebesgue-null set (compact cover), reindex by `Nat.unpair`, and transfer the Lebesgue-null
complement to `μH[k]` by `spatial_hausdorffMeasure_eq_zero_of_volume_eq_zero`. -/
theorem exists_spatial_graph_pieces_proof {n k : ℕ} {F : Spatial k → Spatial n} {L : ℝ≥0}
    (hF : LipschitzWith L F) (hF' : AntilipschitzWith L F) {s : ℝ} (hs : 0 < s) :
    ∃ (S : ℕ → Set (Spatial k)) (W : ℕ → Submodule ℝ (Spatial n)),
      (∀ m, IsCompact (S m)) ∧ (∀ m, Module.finrank ℝ (W m) = k) ∧
      (∀ m, ∀ u ∈ S m, ∀ v ∈ S m,
        ‖(W m)ᗮ.starProjection (F u - F v)‖ ≤ s * ‖(W m).starProjection (F u - F v)‖) ∧
      (Measure.hausdorffMeasure (k : ℝ) : Measure (Spatial k)) (⋃ m, S m)ᶜ = 0 := by
  classical
  -- The linearization tolerance.
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  set α : ℝ≥0 := Real.toNNReal (s / ((1 + s) * ((L : ℝ) + 1))) with hαdef
  have hαr : (α : ℝ) = s / ((1 + s) * ((L : ℝ) + 1)) := Real.coe_toNNReal _ (by positivity)
  have hα : 0 < α := by rw [← NNReal.coe_pos, hαr]; positivity
  have hαL : (α : ℝ) * L ≤ s / (1 + s) := by
    have hsplit : (α : ℝ) * L = s / (1 + s) * ((L : ℝ) / ((L : ℝ) + 1)) := by
      rw [hαr, div_mul_eq_mul_div, div_mul_div_comm]
    rw [hsplit]
    exact mul_le_of_le_one_right (by positivity) (div_le_one_of_le₀ (by linarith) (by positivity))
  have hαL1 : (α : ℝ) * L < 1 :=
    hαL.trans_lt ((div_lt_one (by positivity)).2 (by linarith))
  have hc : (α : ℝ) * L / (1 - (α : ℝ) * L) ≤ s := by
    have hpos : 0 < 1 - (α : ℝ) * L := by linarith
    rw [div_le_iff₀ hpos]
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + s)).1 hαL
    nlinarith
  obtain ⟨S, A, hSm, hSA, hAlow, hSnull⟩ := exists_spatial_linearization_pieces_proof hF hF' hα
  have hcov : ∀ m, ∃ C : ℕ → Set (Spatial k), (∀ j, IsCompact (C j)) ∧ (∀ j, C j ⊆ S m) ∧
      (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y < 1) ∧
      (volume : Measure (Spatial k)) (S m \ ⋃ j, C j) = 0 :=
    fun m => exists_compact_small_cover_ae_proof (volume : Measure (Spatial k)) (hSm m) one_pos
  choose C hCc hCsub _hCdiam hCnull using hcov
  have hvol : (volume : Measure (Spatial k)) (⋃ i, C (Nat.unpair i).1 (Nat.unpair i).2)ᶜ = 0 := by
    have hsub : (⋃ i, C (Nat.unpair i).1 (Nat.unpair i).2)ᶜ ⊆
        (⋃ m, S m)ᶜ ∪ ⋃ m, (S m \ ⋃ j, C m j) := by
      intro x hx
      by_cases hS : x ∈ ⋃ m, S m
      · right
        obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hS
        refine Set.mem_iUnion.2 ⟨m, hm, ?_⟩
        intro hC
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hC
        apply hx
        refine Set.mem_iUnion.2 ⟨Nat.pair m j, ?_⟩
        simpa only [Nat.unpair_pair] using hj
      · left; exact hS
    exact measure_mono_null hsub (measure_union_null hSnull (measure_iUnion_null hCnull))
  refine ⟨fun i => C (Nat.unpair i).1 (Nat.unpair i).2,
    fun i => LinearMap.range (A (Nat.unpair i).1 : Spatial k →ₗ[ℝ] Spatial n),
    fun i => hCc _ _,
    fun i => (projection_slope_of_approximatesLinearOn_proof (hAlow _) (hSA _) hαL1).1,
    ?_, ?_⟩
  · intro i u hu v hv
    have h := (projection_slope_of_approximatesLinearOn_proof (hAlow (Nat.unpair i).1)
      (hSA (Nat.unpair i).1) hαL1).2 u (hCsub _ _ hu) v (hCsub _ _ hv)
    exact h.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  · exact spatial_hausdorffMeasure_eq_zero_of_volume_eq_zero hvol

end ParabolicRectifiability
