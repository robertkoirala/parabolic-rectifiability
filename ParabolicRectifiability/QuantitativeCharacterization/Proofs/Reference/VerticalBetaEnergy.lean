import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry
import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Characterization.Proofs.Fourier.EstimateStatements
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # The vertical beta bound and the own-type energy of vertical references

Proof of `ba1_vertical_beta` and `ba1_vertical_energy`; the statement types are copied below.

Notation: `V` a vertical `L`-reference, `m = V.spatialRank` (`m + 2 = k`), `F = V.spatialMap`,
`Φ = V.map`, `σ = Φ_# parabolicVolume m`, `κ_F = affineErrorSq (parabolicVolume m) F`.

* **Beta** (`b1vbe_vertical_beta`). For an affine competitor `A(u) = a + B u` choose a spatial
  `m`-plane `W ⊇ range B` (`b1vbe_exists_superspace`; `m < n`), and the vertical model
  `(a + W) × ℝ` (`b1vbe_verticalModel`). The point `(a + B u, t)` lies on it, so the model
  cost at `Φ(u,t)` is at most `|F(u,t) - a - B u|²`. The fit over `P(Φ p, r)` is the base
  integral over `Φ⁻¹ P(Φ p, r) ⊆ P_b(p, L r)` (lower Lipschitz bound; `Φ` is a measurable
  embedding by `hbasic`). Finally `r^{-k-2} = L^{k+2} (L r)^{-k-2}`.
* **Energy** (`b1vbe_energy_bound`). Centres are `Φ p₀`. Push `σ` forward, shrink
  `Φ⁻¹ P(Φ p₀, R) ⊆ P_b(p₀, L R)`, apply the beta bound at every scale and substitute
  `s = L r` in `dr/r` (`b1vbe_setLIntegral_scaleMeasure_comp_const_mul`, a local restatement of
  `setLIntegral_scaleMeasure_comp_const_mul`). The
  Carleson bound at radius `L R`, with Lipschitz constant `L` (`b1vbe_lipschitz`) and BMO
  constant `L` (field `coordinate_bmo`), gives
  `R^{-k} ∫_{P(Φ p₀,R)} S^R dσ ≤ L^{k+2} D L^k` with `D = C₀ (L² + L²)`, where `C₀` is the
  Carleson constant of `hcarl (k - 2) n`, chosen before `V`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-! ### Linear algebra: a superspace of prescribed dimension -/

/-- Every subspace `U` with `dim U ≤ j ≤ dim V` lies in a subspace of dimension exactly `j`
(induction on `j - dim U`, adding one vector outside the current subspace at a time). -/
theorem b1vbe_exists_le_finrank_aux {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (d : ℕ) :
    ∀ (U : Submodule ℝ V) (j : ℕ), Module.finrank ℝ U + d = j → j ≤ Module.finrank ℝ V →
      ∃ W : Submodule ℝ V, U ≤ W ∧ Module.finrank ℝ W = j := by
  induction d with
  | zero =>
    intro U j hj _
    exact ⟨U, le_rfl, by omega⟩
  | succ d ih =>
    intro U j hj hjV
    have hlt : Module.finrank ℝ U < Module.finrank ℝ V := by omega
    obtain ⟨v, hv⟩ := U.exists_of_finrank_lt hlt
    have hv1 : v ∉ U := by simpa using hv 1 one_ne_zero
    obtain ⟨W, hW, hWr⟩ := ih (U ⊔ Submodule.span ℝ {v}) j
      (by rw [Submodule.finrank_sup_span_singleton hv1]; omega) hjV
    exact ⟨W, le_sup_left.trans hW, hWr⟩

/-- For `m ≤ n`, the range of a linear map `B : ℝ^m → ℝ^n` lies in an `m`-dimensional
subspace (deficient rank is harmless). -/
theorem b1vbe_exists_superspace {n m : ℕ} (hmn : m ≤ n) (B : Spatial m →L[ℝ] Spatial n) :
    ∃ W : Submodule ℝ (Spatial n),
      LinearMap.range (B : Spatial m →ₗ[ℝ] Spatial n) ≤ W ∧ Module.finrank ℝ W = m := by
  have hr : Module.finrank ℝ (LinearMap.range (B : Spatial m →ₗ[ℝ] Spatial n)) ≤ m :=
    (LinearMap.finrank_range_le (B : Spatial m →ₗ[ℝ] Spatial n)).trans_eq
      finrank_euclideanSpace_fin
  have hn : m ≤ Module.finrank ℝ (Spatial n) := hmn.trans_eq finrank_euclideanSpace_fin.symm
  exact b1vbe_exists_le_finrank_aux
    (m - Module.finrank ℝ (LinearMap.range (B : Spatial m →ₗ[ℝ] Spatial n))) _ m
    (by omega) hn

/-! ### Vertical models and their costs -/

/-- The vertical model `(a + W) × ℝ` of rank `k = m + 2`, for an `m`-dimensional `W`. -/
def b1vbe_verticalModel {n k m : ℕ} (hk : m + 2 = k) (W : Submodule ℝ (Spatial n))
    (hW : Module.finrank ℝ W = m) (a : Spatial n) : VerticalModel n k :=
  ⟨m, by omega, hk, AffineSpatialPlane.ofTranslate W hW a⟩

/-- The model cost at `(x,t)` is at most `|x - z|²` for every spatial point `z` of the
model plane (test at the same time `t`). -/
theorem b1vbe_modelCost_le {n k : ℕ} (M : VerticalModel n k) (x : Spatial n) (t : Time)
    {z : Spatial n} (hz : z ∈ M.spatial.toSet) :
    modelCost (T := .vertical) M (x, t) ≤ ‖x - z‖ₑ ^ 2 := by
  have hmem : ((z, t) : Space n) ∈ modelSet (T := .vertical) M := hz
  have hd : edist ((x, t) : Space n) (z, t) = ‖x - z‖ₑ := by
    rw [Prod.edist_eq, edist_self, max_eq_left zero_le, edist_eq_enorm_sub]
  exact pow_le_pow_left' ((Metric.infEDist_le_edist_of_mem hmem).trans_eq hd) 2

/-- Outer inclusion `Φ⁻¹ P(Φ p, r) ⊆ P_b(p, L r)` (lower Lipschitz bound; a local restatement
of the lemma `b1adra_preimage_subset_ball`). -/
theorem b1vbe_preimage_subset_ball {n k : ℕ} {L : ℝ} (V : VerticalReference n k L)
    (hL : 1 ≤ L) (p : Space V.spatialRank) (r : ℝ) :
    V.map ⁻¹' Metric.ball (V.map p) r ⊆ Metric.ball p (L * r) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro q hq
  rw [mem_preimage, Metric.mem_ball] at hq
  rw [Metric.mem_ball]
  calc dist q p ≤ L * dist (V.map q) (V.map p) := (V.bilipschitz q p).1
    _ < L * r := mul_lt_mul_of_pos_left hq hL0

/-! ### The vertical beta bound -/

/-- **One fixed affine competitor.** The fit of `σ` over `P(Φ p, r)` against the model
`(a + W) × ℝ`, `W ⊇ range B`, is at most the affine fit integral of `F` against `a + B u`
over `P_b(p, L r)`. -/
theorem b1vbe_fit_le {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (V : VerticalReference n k L)
    (hemb : MeasurableEmbedding V.map) (p : Space V.spatialRank) (r : ℝ) (a : Spatial n)
    (B : Spatial V.spatialRank →L[ℝ] Spatial n) :
    ⨅ M : Models n k .vertical, fit V.measure M (V.map p) r ≤
      affineFitIntegral (parabolicVolume V.spatialRank) V.spatialMap a B p (L * r) := by
  have hmn : V.spatialRank ≤ n := by
    have h1 := V.rank_eq
    have h2 := V.lt_ambient
    omega
  obtain ⟨W, hBW, hW⟩ := b1vbe_exists_superspace hmn B
  refine (iInf_le _ (b1vbe_verticalModel V.rank_eq W hW a : Models n k .vertical)).trans ?_
  unfold fit affineFitIntegral
  rw [VerticalReference.measure, hemb.restrict_map, hemb.lintegral_map]
  calc ∫⁻ q in V.map ⁻¹' Metric.ball (V.map p) r,
        modelCost (T := .vertical) (b1vbe_verticalModel V.rank_eq W hW a) (V.map q)
          ∂parabolicVolume V.spatialRank
      ≤ ∫⁻ q in Metric.ball p (L * r),
        modelCost (T := .vertical) (b1vbe_verticalModel V.rank_eq W hW a) (V.map q)
          ∂parabolicVolume V.spatialRank :=
        lintegral_mono_set (b1vbe_preimage_subset_ball V hL p r)
    _ ≤ ∫⁻ q in Metric.ball p (L * r), ‖V.spatialMap q - (a + B q.1)‖ₑ ^ 2
          ∂parabolicVolume V.spatialRank := by
        refine lintegral_mono fun q => ?_
        refine b1vbe_modelCost_le _ (V.spatialMap q) q.2 ?_
        change a + B q.1 ∈ (AffineSpatialPlane.ofTranslate W hW a).toSet
        rw [AffineSpatialPlane.ofTranslate_toSet]
        have hy : B q.1 ∈ W := hBW ⟨q.1, rfl⟩
        simpa using hy

/-- `r^{-j} = L^j (L r)^{-j}` in `ℝ≥0∞`, for `L, r > 0`. -/
theorem b1vbe_scale_factor {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (j : ℕ) :
    (ENNReal.ofReal r)⁻¹ ^ j = ENNReal.ofReal (L ^ j) * (ENNReal.ofReal (L * r))⁻¹ ^ j := by
  have hLr : 0 < L * r := mul_pos hL hr
  rw [← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_inv_of_pos hLr,
    ← ENNReal.ofReal_pow (inv_nonneg.mpr hr.le), ← ENNReal.ofReal_pow (inv_nonneg.mpr hLr.le),
    ← ENNReal.ofReal_mul (pow_nonneg hL.le j)]
  congr 1
  rw [mul_inv, mul_pow, inv_pow L, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero j hL.ne'), one_mul]

/-- The base dimension of the spatial base of a vertical reference is `k`. -/
theorem b1vbe_baseDimension {n k : ℕ} {L : ℝ} (V : VerticalReference n k L) :
    baseDimension (Spatial V.spatialRank) = k := by
  rw [baseDimension, finrank_euclideanSpace_fin, V.rank_eq]

/-- **The vertical beta bound** for one reference:
`β_{σ,V}(Φ p, r)² ≤ L^{k+2} κ_F(p, L r)²`. -/
theorem b1vbe_vertical_beta {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (V : VerticalReference n k L)
    (hemb : MeasurableEmbedding V.map) (p : Space V.spatialRank) {r : ℝ} (hr : 0 < r) :
    betaSq V.measure k .vertical (V.map p) r ≤
      ENNReal.ofReal (L ^ (k + 2)) *
        affineErrorSq (parabolicVolume V.spatialRank) V.spatialMap p (L * r) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLr : 0 < L * r := mul_pos hL0 hr
  rw [betaSq_of_pos _ _ _ _ hr, affineErrorSq_of_pos _ _ _ hLr, b1vbe_baseDimension V,
    ← mul_assoc, b1vbe_scale_factor hL0 hr (k + 2)]
  exact mul_le_mul_right (le_iInf₂ fun a B => b1vbe_fit_le hL V hemb p r a B) _

/-- **`ba1_vertical_beta`**, in the
implication form of its type: given the conclusion `hbasic` of `ba1_vertical_basic` (only its
measurable-embedding clause is used), for `1 ≤ L`, every vertical `L`-reference `V`, base
point `p` and `r > 0`, `β_{σ,V}(Φ(p), r)² ≤ L^{k+2} κ_F(p, L r)²`. -/
theorem ba1_vertical_beta_proof
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ V : VerticalReference n k L,
      MeasurableEmbedding V.map ∧ IsClosed V.carrier ∧ V.measure.support = V.carrier ∧
        IsFiniteMeasureOnCompacts V.measure ∧ V.measure.InnerRegular) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L →
      ∀ (V : VerticalReference n k L) (p : Space V.spatialRank) (r : ℝ), 0 < r →
        betaSq V.measure k .vertical (V.map p) r ≤
          ENNReal.ofReal (L ^ (k + 2)) *
            affineErrorSq (parabolicVolume V.spatialRank) V.spatialMap p (L * r) :=
  fun n k L hL V p _ hr => b1vbe_vertical_beta hL V (hbasic n k L hL V).1 p hr

/-! ### The scale measure `dr/r` under `r ↦ c r` (local restatement) -/

/-- The scale measure `ds/s` is invariant under multiplication by `c > 0` (local restatement of
`map_const_mul_scaleMeasure`). -/
theorem b1vbe_map_const_mul_scaleMeasure {c : ℝ} (hc : 0 < c) :
    Measure.map (fun s => c * s) scaleMeasure = scaleMeasure := by
  ext A hA
  have hA' : MeasurableSet (A ∩ Ioi 0) := hA.inter measurableSet_Ioi
  have hpre : MeasurableSet ((fun s => c * s) ⁻¹' A) := measurable_const_mul c hA
  rw [Measure.map_apply (measurable_const_mul c) hA, scaleMeasure_apply _ hpre,
    scaleMeasure_apply _ hA]
  have hset : (fun s => c * s) ⁻¹' A ∩ Ioi 0 = (fun s => c * s) ⁻¹' (A ∩ Ioi 0) := by
    ext r
    simp only [mem_inter_iff, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, mul_pos hc h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, pos_of_mul_pos_right h2 hc.le⟩
  rw [hset, ← lintegral_indicator (measurable_const_mul c hA'), ← lintegral_indicator hA']
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ≥0∞,
      G = (A ∩ Ioi 0).indicator (fun t => ENNReal.ofReal (1 / t)) := ⟨_, rfl⟩
  rw [← hG]
  have hfun : ∀ r, ((fun s => c * s) ⁻¹' (A ∩ Ioi 0)).indicator
      (fun r => ENNReal.ofReal (1 / r)) r = ENNReal.ofReal c * G (c * r) := by
    intro r
    rw [hG]
    by_cases hr : c * r ∈ A ∩ Ioi 0
    · rw [indicator_of_mem (show r ∈ (fun s => c * s) ⁻¹' (A ∩ Ioi 0) from hr),
        indicator_of_mem hr, ← ENNReal.ofReal_mul hc.le, mul_one_div,
        div_mul_cancel_left₀ hc.ne', one_div]
    · rw [indicator_of_notMem (show r ∉ (fun s => c * s) ⁻¹' (A ∩ Ioi 0) from hr),
        indicator_of_notMem hr, mul_zero]
  have hmap : ∫⁻ r, G (c * r) = ENNReal.ofReal |c⁻¹| * ∫⁻ t, G t := by
    calc
      ∫⁻ r, G (c * r) = ∫⁻ t, G t ∂(Measure.map (fun s => c * s) volume) :=
        (lintegral_map_equiv G (MeasurableEquiv.mulLeft₀ c hc.ne')).symm
      _ = ∫⁻ t, G t ∂(ENNReal.ofReal |c⁻¹| • volume) := by
        rw [Real.map_volume_mul_left hc.ne']
      _ = ENNReal.ofReal |c⁻¹| * ∫⁻ t, G t := by
        rw [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_congr hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmap, ← mul_assoc,
    ← ENNReal.ofReal_mul hc.le, abs_of_pos (inv_pos.mpr hc), mul_inv_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]

/-- Change of scale `t = c s` for `ds/s`, valid for every function (local restatement of `setLIntegral_scaleMeasure_comp_const_mul`). -/
theorem b1vbe_setLIntegral_scaleMeasure_comp_const_mul {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ≥0∞)
    (T : Set ℝ) :
    ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure = ∫⁻ t in T, f t ∂scaleMeasure := by
  set e := MeasurableEquiv.mulLeft₀ c hc.ne' with he_def
  have he : ⇑e = fun s => c * s := MeasurableEquiv.coe_mulLeft₀ hc.ne'
  symm
  calc
    ∫⁻ t in T, f t ∂scaleMeasure = ∫⁻ t in T, f t ∂(Measure.map e scaleMeasure) := by
      rw [he, b1vbe_map_const_mul_scaleMeasure hc]
    _ = ∫⁻ t, f t ∂((scaleMeasure.restrict (e ⁻¹' T)).map e) := by
      rw [e.measurableEmbedding.restrict_map]
    _ = ∫⁻ s, f (e s) ∂(scaleMeasure.restrict (e ⁻¹' T)) := lintegral_map_equiv f e
    _ = ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure := by
      rw [he]

/-- `∫_0^R g(c r) dr/r = ∫_0^{cR} g(s) ds/s` for `c > 0` and every `g`. -/
theorem b1vbe_scale_subst {c : ℝ} (hc : 0 < c) (R : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioo 0 R, g (c * r) ∂scaleMeasure = ∫⁻ s in Ioo 0 (c * R), g s ∂scaleMeasure := by
  have hpre : (fun s => c * s) ⁻¹' Ioo 0 (c * R) = Ioo 0 R := by
    ext r
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hc.le, lt_of_mul_lt_mul_left h2 hc.le⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hc h1, mul_lt_mul_of_pos_left h2 hc⟩
  rw [← b1vbe_setLIntegral_scaleMeasure_comp_const_mul hc g (Ioo 0 (c * R)), hpre]

/-! ### The own-type energy of vertical references -/

/-- `F` is `L`-Lipschitz: `|F p - F q| ≤ d_P(Φ p, Φ q) ≤ L d_P(p,q)`. -/
theorem b1vbe_lipschitz {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (V : VerticalReference n k L) :
    LipschitzWith (Real.toNNReal L) V.spatialMap := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.coe_toNNReal L (by linarith)]
  calc dist (V.spatialMap p) (V.spatialMap q)
      ≤ dist ((V.spatialMap p, p.2) : Space n) (V.spatialMap q, q.2) := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
    _ ≤ L * dist p q := (V.bilipschitz p q).2

/-- Scale integral at one base point: `S^R(Φ q) ≤ L^{k+2} ∫_0^{LR} κ_F(q,s)² ds/s`. -/
theorem b1vbe_squareEnergy_le {n k : ℕ} {L : ℝ} (hL0 : 0 < L) (V : VerticalReference n k L)
    (hbeta : ∀ (p : Space V.spatialRank) (r : ℝ), 0 < r →
      betaSq V.measure k .vertical (V.map p) r ≤
        ENNReal.ofReal (L ^ (k + 2)) *
          affineErrorSq (parabolicVolume V.spatialRank) V.spatialMap p (L * r))
    (q : Space V.spatialRank) (R : ℝ) :
    squareEnergy V.measure k .vertical R (V.map q) ≤
      ENNReal.ofReal (L ^ (k + 2)) *
        ∫⁻ s in Ioo 0 (L * R),
          affineErrorSq (parabolicVolume V.spatialRank) V.spatialMap q s ∂scaleMeasure := by
  unfold squareEnergy
  calc ∫⁻ r in Ioo 0 R, betaSq V.measure k .vertical (V.map q) r ∂scaleMeasure
      ≤ ∫⁻ r in Ioo 0 R, ENNReal.ofReal (L ^ (k + 2)) *
          affineErrorSq (parabolicVolume V.spatialRank) V.spatialMap q (L * r) ∂scaleMeasure :=
        setLIntegral_mono' measurableSet_Ioo fun r hr => hbeta q r hr.1
    _ = ENNReal.ofReal (L ^ (k + 2)) * ∫⁻ r in Ioo 0 R,
          affineErrorSq (parabolicVolume V.spatialRank) V.spatialMap q (L * r) ∂scaleMeasure :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := congrArg (ENNReal.ofReal (L ^ (k + 2)) * ·)
        (b1vbe_scale_subst hL0 R
          (fun s => affineErrorSq (parabolicVolume V.spatialRank) V.spatialMap q s))

/-- **Energy of one vertical reference** from the beta bound and an affine Carleson bound
`D` for `F`: `referenceEnergy (vertical V) ≤ L^{k+2} D L^k`. -/
theorem b1vbe_energy_bound {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (V : VerticalReference n k L)
    (hemb : MeasurableEmbedding V.map)
    (hbeta : ∀ (p : Space V.spatialRank) (r : ℝ), 0 < r →
      betaSq V.measure k .vertical (V.map p) r ≤
        ENNReal.ofReal (L ^ (k + 2)) *
          affineErrorSq (parabolicVolume V.spatialRank) V.spatialMap p (L * r))
    {D : ℝ} (hD : HasAffineCarlesonBound (parabolicVolume V.spatialRank) V.spatialMap D) :
    referenceEnergy (Reference.vertical V) ≤ ENNReal.ofReal (L ^ (k + 2) * D * L ^ k) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hD0 : 0 ≤ D := hD.1
  unfold referenceEnergy rootCarlesonSup
  refine iSup₂_le fun a ha => iSup₂_le fun R hR => ?_
  have ha' : a ∈ Set.range V.map := ha
  obtain ⟨p₀, rfl⟩ := ha'
  have hLR : 0 < L * R := mul_pos hL0 hR
  change (ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball (V.map p₀) R,
      squareEnergy V.measure k .vertical R z ∂V.measure ≤ _
  have hpush : ∫⁻ z in Metric.ball (V.map p₀) R, squareEnergy V.measure k .vertical R z
        ∂V.measure =
      ∫⁻ q in V.map ⁻¹' Metric.ball (V.map p₀) R,
        squareEnergy V.measure k .vertical R (V.map q) ∂parabolicVolume V.spatialRank := by
    rw [VerticalReference.measure, hemb.restrict_map, hemb.lintegral_map]
  have hint : ∫⁻ z in Metric.ball (V.map p₀) R, squareEnergy V.measure k .vertical R z
        ∂V.measure ≤
      ENNReal.ofReal (L ^ (k + 2)) * ENNReal.ofReal (D * (L * R) ^ k) := by
    rw [hpush]
    calc ∫⁻ q in V.map ⁻¹' Metric.ball (V.map p₀) R,
          squareEnergy V.measure k .vertical R (V.map q) ∂parabolicVolume V.spatialRank
        ≤ ∫⁻ q in Metric.ball p₀ (L * R),
          squareEnergy V.measure k .vertical R (V.map q) ∂parabolicVolume V.spatialRank :=
          lintegral_mono_set (b1vbe_preimage_subset_ball V hL p₀ R)
      _ ≤ ∫⁻ q in Metric.ball p₀ (L * R), ENNReal.ofReal (L ^ (k + 2)) *
            ∫⁻ s in Ioo 0 (L * R),
              affineErrorSq (parabolicVolume V.spatialRank) V.spatialMap q s ∂scaleMeasure
            ∂parabolicVolume V.spatialRank :=
          lintegral_mono fun q => b1vbe_squareEnergy_le hL0 V hbeta q R
      _ = ENNReal.ofReal (L ^ (k + 2)) *
            affineCarlesonIntegral (parabolicVolume V.spatialRank) V.spatialMap p₀ (L * R) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by
          refine mul_le_mul_right ?_ _
          have h := hD.2 p₀ (L * R) hLR
          rwa [b1vbe_baseDimension V] at h
  have h1 : R⁻¹ ^ k * R ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ hR.ne', one_pow]
  calc (ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball (V.map p₀) R,
        squareEnergy V.measure k .vertical R z ∂V.measure
      ≤ (ENNReal.ofReal R)⁻¹ ^ k *
          (ENNReal.ofReal (L ^ (k + 2)) * ENNReal.ofReal (D * (L * R) ^ k)) :=
        mul_le_mul_right hint _
    _ = ENNReal.ofReal (R⁻¹ ^ k * (L ^ (k + 2) * (D * (L * R) ^ k))) := by
        rw [← ENNReal.ofReal_mul (pow_nonneg hL0.le _), ← ENNReal.ofReal_inv_of_pos hR,
          ← ENNReal.ofReal_pow (inv_nonneg.mpr hR.le),
          ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hR.le) _)]
    _ = ENNReal.ofReal (L ^ (k + 2) * D * L ^ k) := by
        congr 1
        calc R⁻¹ ^ k * (L ^ (k + 2) * (D * (L * R) ^ k))
            = L ^ (k + 2) * D * L ^ k * (R⁻¹ ^ k * R ^ k) := by ring
          _ = L ^ (k + 2) * D * L ^ k := by rw [h1, mul_one]

/-- **`ba1_vertical_energy`**, in the implication
form of its type: given the conclusions `hbasic` (its measurable-embedding clause), `hbeta`
of `ba1_vertical_beta` and `hcarl` of `ba1_vertical_carleson`, for `1 ≤ L` the constant
`C = L^{k+2} C₀ (L² + L²) L^k`, with `C₀` the Carleson constant of `hcarl (k - 2) n` (chosen
before the reference), bounds the own-type energy of every vertical `L`-reference. -/
theorem ba1_vertical_energy_proof
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ V : VerticalReference n k L,
      MeasurableEmbedding V.map ∧ IsClosed V.carrier ∧ V.measure.support = V.carrier ∧
        IsFiniteMeasureOnCompacts V.measure ∧ V.measure.InnerRegular)
    (hbeta : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L →
      ∀ (V : VerticalReference n k L) (p : Space V.spatialRank) (r : ℝ), 0 < r →
        betaSq V.measure k .vertical (V.map p) r ≤
          ENNReal.ofReal (L ^ (k + 2)) *
            affineErrorSq (parabolicVolume V.spatialRank) V.spatialMap p (L * r))
    (hcarl : ∀ m d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (F : Space m → Spatial d) (L : ℝ≥0) (B : ℝ),
        LipschitzWith L F → HasCoordinateHalfTimeBMOBound m d F B →
        HasAffineCarlesonBound (parabolicVolume m) F (C * ((L : ℝ) ^ 2 + B ^ 2))) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ V : VerticalReference n k L, referenceEnergy (Reference.vertical V) ≤ ENNReal.ofReal C := by
  intro n k L hL
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨C₀, hC₀, hC⟩ := hcarl (k - 2) n
  have hC' : ∀ m : ℕ, m = k - 2 → ∀ (F : Space m → Spatial n) (L' : ℝ≥0) (B : ℝ),
      LipschitzWith L' F → HasCoordinateHalfTimeBMOBound m n F B →
      HasAffineCarlesonBound (parabolicVolume m) F (C₀ * ((L' : ℝ) ^ 2 + B ^ 2)) := by
    intro m hm
    subst hm
    exact hC
  have hpos : 0 < L ^ (k + 2) * (C₀ * (((Real.toNNReal L : ℝ≥0) : ℝ) ^ 2 + L ^ 2)) * L ^ k := by
    have h2 : 0 < ((Real.toNNReal L : ℝ≥0) : ℝ) ^ 2 + L ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hL0 2)
    exact mul_pos (mul_pos (pow_pos hL0 _) (mul_pos hC₀ h2)) (pow_pos hL0 _)
  refine ⟨_, hpos, fun V => ?_⟩
  have hrank : V.spatialRank = k - 2 := by
    have := V.rank_eq
    omega
  exact b1vbe_energy_bound hL V (hbasic n k L hL V).1 (hbeta n k L hL V)
    (hC' V.spatialRank hrank V.spatialMap (Real.toNNReal L) L (b1vbe_lipschitz hL V)
      V.coordinate_bmo)

end ParabolicRectifiability.QuantitativeCharacterization
