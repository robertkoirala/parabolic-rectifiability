import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry
import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Characterization.Proofs.Fourier.EstimateStatements
import ParabolicRectifiability.Foundations.Statements.Ambient
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Recentering

/-! # The horizontal temporal energy and the horizontal own-type energy

Proof of `ba1_horizontal_temporal` and `ba1_horizontal_energy`.

Write `τ_L(u,r) = r^{-k-2} ∫_{|v-u| < Lr, |T(v)-T(u)| < r²} |T(v) - T(u)| dv`
(`b1hte_cost`, the temporal cost, with the actual time restriction).

* `b1hte_measurable_cost`: `(u,r) ↦ τ_L(u,r)` is Borel, since `T` is Borel (from the basic
  statement: `(F,T)` is measurable).
* `b1hte_temporal_le`: the ball `B(b,R)` is covered by `B(b,R) ∩ D` and the countably many
  pieces `B(b,R) ∩ face Q` (`faces_cover`); for a centre in a face,
  `(0,R) ⊆ [ℓ_Q, R) ∪ (0, min(R, ℓ_Q))`. Only countable subadditivity of the lower integral
  and the measurability of one scale integral (to split a sum) are used.
* `b1hte_preimage_subset_ball`: a nonempty preimage `(F,T)⁻¹ P(a,R)` lies in `B(v₀, 2LR)`
  for any of its points `v₀`.
* `b1hte_squareEnergy_le`: `S^R(F u, T u) ≤ L^{k+2} ∫_0^{2LR} a_F(u,s)² ds/s +
  ∫_0^R τ_L(u,r) dr/r` from the beta statement and the substitution `s = L r` (the `dr/r`
  invariance `setLIntegral_scaleMeasure_comp_const_mul` of `WhitneyRecentering`).
* `b1hte_energy_bound`: the root bound
  `R^{-k} ∫_{P(a,R)} S^R dσ ≤ L^{k+2} C_sp L² (2L)^k + C_t (2L)^k`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-! ### The temporal cost and its measurability -/

/-- The horizontal temporal cost `τ_L(u,r)`, exactly as written in the statements:
`r^{-k-2} ∫_{|v-u| < Lr, |T(v)-T(u)| < r²} |T(v) - T(u)| dv`. -/
def b1hte_cost {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L) (u : Spatial k) (r : ℝ) :
    ℝ≥0∞ :=
  (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
    (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
      ENNReal.ofReal |H.height v - H.height u|)

/-- The plateau function `T` is Borel when `(F,T)` is. -/
theorem b1hte_measurable_height {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L)
    (hmap : Measurable H.map) : Measurable H.height := by
  show Measurable fun u => Metric.Snowflaking.ofSnowflaking (H.map u).2
  exact Metric.Snowflaking.continuous_ofSnowflaking.measurable.comp (measurable_snd.comp hmap)

/-- The temporal cost is jointly Borel in the centre and the radius. -/
theorem b1hte_measurable_cost {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L)
    (hT : Measurable H.height) : Measurable (Function.uncurry (b1hte_cost H)) := by
  have hdiff : Measurable fun q : (Spatial k × ℝ) × Spatial k =>
      |H.height q.2 - H.height q.1.1| :=
    ((hT.comp measurable_snd).sub (hT.comp measurable_fst.fst)).abs
  have hS : MeasurableSet {q : (Spatial k × ℝ) × Spatial k |
      dist q.2 q.1.1 < L * q.1.2 ∧ |H.height q.2 - H.height q.1.1| < q.1.2 ^ 2} :=
    (measurableSet_lt (measurable_snd.dist measurable_fst.fst)
      (measurable_const.mul measurable_fst.snd)).inter
      (measurableSet_lt hdiff (measurable_fst.snd.pow_const 2))
  have hI := (hdiff.ennreal_ofReal.indicator hS).lintegral_prod_right'
    (ν := (volume : Measure (Spatial k)))
  have hJ : Measurable fun p : Spatial k × ℝ =>
      ∫⁻ v in {v : Spatial k | dist v p.1 < L * p.2 ∧ |H.height v - H.height p.1| < p.2 ^ 2},
        ENNReal.ofReal |H.height v - H.height p.1| := by
    convert hI using 1
    funext p
    have hSp : MeasurableSet
        {v : Spatial k | dist v p.1 < L * p.2 ∧ |H.height v - H.height p.1| < p.2 ^ 2} :=
      (measurableSet_lt (measurable_id.dist measurable_const) measurable_const).inter
        (measurableSet_lt (hT.sub measurable_const).abs measurable_const)
    rw [← lintegral_indicator hSp]
    rfl
  exact (measurable_snd.ennreal_ofReal.inv.pow_const (k + 2)).mul hJ

/-! ### The temporal energy at every radius -/

/-- For a centre in a face of side `ℓ`, `(0,R) ⊆ [ℓ, R) ∪ (0, min(R, ℓ))`; the scale integral
of a measurable cost then splits under the outer integral. -/
theorem b1hte_face_split {k : ℕ} {f : Spatial k → ℝ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (s : Set (Spatial k)) (ℓ R : ℝ) :
    ∫⁻ u in s, ∫⁻ r in Ioo 0 R, f u r ∂scaleMeasure ≤
      (∫⁻ u in s, ∫⁻ r in Ico ℓ R, f u r ∂scaleMeasure) +
        ∫⁻ u in s, ∫⁻ r in Ioo 0 (min R ℓ), f u r ∂scaleMeasure := by
  have hsplit : ∀ u, ∫⁻ r in Ioo 0 R, f u r ∂scaleMeasure ≤
      (∫⁻ r in Ico ℓ R, f u r ∂scaleMeasure) + ∫⁻ r in Ioo 0 (min R ℓ), f u r ∂scaleMeasure := by
    intro u
    refine (lintegral_mono_set ?_).trans (lintegral_union_le _ _ _)
    intro r hr
    by_cases h : ℓ ≤ r
    · exact Or.inl ⟨h, hr.2⟩
    · exact Or.inr ⟨hr.1, lt_min hr.2 (not_le.1 h)⟩
  calc ∫⁻ u in s, ∫⁻ r in Ioo 0 R, f u r ∂scaleMeasure
      ≤ ∫⁻ u in s, ((∫⁻ r in Ico ℓ R, f u r ∂scaleMeasure) +
          ∫⁻ r in Ioo 0 (min R ℓ), f u r ∂scaleMeasure) := lintegral_mono hsplit
    _ = _ := lintegral_add_left
        (hf.lintegral_prod_right' (ν := scaleMeasure.restrict (Ico ℓ R))) _

/-- **Assembly of the temporal energy**: the integral over `B(b,R)` is at most the
coarse part plus the fine part. -/
theorem b1hte_temporal_le {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L)
    (hT : Measurable H.height) (b : Spatial k) (R : ℝ) {A B : ℝ≥0∞}
    (hc : (∫⁻ u in Metric.ball b R ∩ H.domain, ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure) +
        (∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
          ∫⁻ r in Ico (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) R, b1hte_cost H u r ∂scaleMeasure) ≤
        A)
    (hf : (∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
          ∫⁻ r in Ioo 0 (min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i)),
            b1hte_cost H u r ∂scaleMeasure) ≤ B) :
    ∫⁻ u in Metric.ball b R, ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure ≤ A + B := by
  have hcover : Metric.ball b R ⊆
      (Metric.ball b R ∩ H.domain) ∪ ⋃ i : H.cubeIndex, (Metric.ball b R ∩ H.face i) := by
    intro u hu
    by_cases hD : u ∈ H.domain
    · exact Or.inl ⟨hu, hD⟩
    · have hu' : u ∈ ⋃ i, H.face i := by
        rw [H.faces_cover]
        exact hD
      obtain ⟨i, hi⟩ := mem_iUnion.1 hu'
      exact Or.inr (mem_iUnion.2 ⟨i, hu, hi⟩)
  have hmc := b1hte_measurable_cost H hT
  calc ∫⁻ u in Metric.ball b R, ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure
      ≤ ∫⁻ u in (Metric.ball b R ∩ H.domain) ∪ ⋃ i : H.cubeIndex, (Metric.ball b R ∩ H.face i),
          ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure := lintegral_mono_set hcover
    _ ≤ (∫⁻ u in Metric.ball b R ∩ H.domain, ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure) +
          ∫⁻ u in ⋃ i : H.cubeIndex, (Metric.ball b R ∩ H.face i),
            ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure := lintegral_union_le _ _ _
    _ ≤ (∫⁻ u in Metric.ball b R ∩ H.domain, ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure) +
          ∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
            ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure :=
        add_le_add le_rfl (lintegral_iUnion_le _ _)
    _ ≤ (∫⁻ u in Metric.ball b R ∩ H.domain, ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure) +
          ∑' i : H.cubeIndex, ((∫⁻ u in Metric.ball b R ∩ H.face i,
            ∫⁻ r in Ico (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) R,
              b1hte_cost H u r ∂scaleMeasure) +
            ∫⁻ u in Metric.ball b R ∩ H.face i,
              ∫⁻ r in Ioo 0 (min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i)),
                b1hte_cost H u r ∂scaleMeasure) :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum fun i =>
          b1hte_face_split hmc _ (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) R)
    _ = ((∫⁻ u in Metric.ball b R ∩ H.domain, ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure) +
          ∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
            ∫⁻ r in Ico (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) R,
              b1hte_cost H u r ∂scaleMeasure) +
          ∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
            ∫⁻ r in Ioo 0 (min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i)),
              b1hte_cost H u r ∂scaleMeasure := by
        rw [ENNReal.tsum_add, add_assoc]
    _ ≤ A + B := add_le_add hc hf

/-- **`ba1_horizontal_temporal`**, in the implication form of
its type: given the conclusions `hbasic` (only `Measurable H.map` is used), `hcoarse` of
`ba1_horizontal_coarse` and `hfine` of `ba1_horizontal_fine`, the constant `C = C_coarse +
C_fine` bounds the temporal energy `∫_{B(b,R)} ∫_0^R τ_L(u,r) dr/r du` by `C R^k`. -/
theorem ba1_horizontal_temporal_proof
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      Measurable H.map ∧ IsClosed H.carrier ∧ IsFiniteMeasureOnCompacts H.measure ∧
        H.measure.InnerRegular)
    (hcoarse : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ (H : HorizontalReference n k L) (b : Spatial k) (R : ℝ), 0 < R →
        (∫⁻ u in Metric.ball b R ∩ H.domain, ∫⁻ r in Ioo 0 R,
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) +
          (∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
            ∫⁻ r in Ico (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) R,
              (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
                (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                  ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) ≤
          ENNReal.ofReal (C * R ^ k))
    (hfine : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ (H : HorizontalReference n k L) (b : Spatial k) (R : ℝ), 0 < R →
        (∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
          ∫⁻ r in Ioo 0 (min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i)),
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) ≤
          ENNReal.ofReal (C * R ^ k)) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ (H : HorizontalReference n k L) (b : Spatial k) (R : ℝ), 0 < R →
        ∫⁻ u in Metric.ball b R, ∫⁻ r in Ioo 0 R,
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure ≤
          ENNReal.ofReal (C * R ^ k) := by
  intro n k L hL
  obtain ⟨Cc, hCc, hc⟩ := hcoarse n k L hL
  obtain ⟨Cf, hCf, hf⟩ := hfine n k L hL
  refine ⟨Cc + Cf, add_pos hCc hCf, fun H b R hR => ?_⟩
  have hT : Measurable H.height := b1hte_measurable_height H (hbasic n k L hL H).1
  have hRk : 0 ≤ R ^ k := pow_nonneg hR.le k
  have h := b1hte_temporal_le H hT b R (hc H b R hR) (hf H b R hR)
  rw [← ENNReal.ofReal_add (mul_nonneg hCc.le hRk) (mul_nonneg hCf.le hRk), ← add_mul] at h
  exact h

/-! ### The own-type energy of horizontal references -/

/-- `F` is `L`-Lipschitz (upper half of the bi-Lipschitz field). -/
theorem b1hte_lipschitz {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (H : HorizontalReference n k L) :
    LipschitzWith (Real.toNNReal L) H.spatialMap := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  rw [Real.coe_toNNReal L (by linarith)]
  exact (H.spatialMap_bilipschitz u v).2

/-- The root preimage: if `(F,T)(v₀) ∈ P(a,R)` then `(F,T)⁻¹ P(a,R) ⊆ B(v₀, 2LR)`, since
`|v - v₀| ≤ L |F(v) - F(v₀)| ≤ L d_P((F,T)(v), (F,T)(v₀)) < 2LR`. -/
theorem b1hte_preimage_subset_ball {n k : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (H : HorizontalReference n k L) {a : Space n} {R : ℝ} {v₀ : Spatial k}
    (hv₀ : H.map v₀ ∈ Metric.ball a R) :
    H.map ⁻¹' Metric.ball a R ⊆ Metric.ball v₀ (2 * L * R) := by
  intro v hv
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hv' : dist (H.map v) a < R := hv
  have hv₀' : dist (H.map v₀) a < R := hv₀
  have hF : dist (H.spatialMap v) (H.spatialMap v₀) ≤ dist (H.map v) (H.map v₀) := by
    show dist (H.spatialMap v) (H.spatialMap v₀) ≤
      dist (point (H.spatialMap v) (H.height v)) (point (H.spatialMap v₀) (H.height v₀))
    rw [point, point, Prod.dist_eq]
    exact le_max_left _ _
  have htri : dist (H.map v) (H.map v₀) < 2 * R := by
    have := dist_triangle_right (H.map v) (H.map v₀) a
    linarith
  rw [Metric.mem_ball]
  calc dist v v₀ ≤ L * dist (H.spatialMap v) (H.spatialMap v₀) :=
        (H.spatialMap_bilipschitz v v₀).1
    _ ≤ L * dist (H.map v) (H.map v₀) := mul_le_mul_of_nonneg_left hF hL0.le
    _ < L * (2 * R) := mul_lt_mul_of_pos_left htri hL0
    _ = 2 * L * R := by ring

/-- Scale integral at one base point: `S^R(F u, T u) ≤ L^{k+2} ∫_0^{2LR} a_F(u,s)² ds/s +
∫_0^R τ_L(u,r) dr/r`, from the beta bound and the substitution `s = L r`. -/
theorem b1hte_squareEnergy_le {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (H : HorizontalReference n k L)
    (hT : Measurable H.height)
    (hbeta : ∀ (u : Spatial k) (r : ℝ), 0 < r →
      betaSq H.measure k .horizontal (H.map u) r ≤
        ENNReal.ofReal (L ^ (k + 2)) *
            Characterization.spatialAffineErrorSq H.spatialMap u (L * r) +
          b1hte_cost H u r)
    (u : Spatial k) {R : ℝ} (hR : 0 < R) :
    squareEnergy H.measure k .horizontal R (H.map u) ≤
      ENNReal.ofReal (L ^ (k + 2)) *
          ∫⁻ s in Ioo 0 (2 * L * R),
            Characterization.spatialAffineErrorSq H.spatialMap u s ∂scaleMeasure +
        ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hmr : Measurable (b1hte_cost H u) := (b1hte_measurable_cost H hT).of_uncurry_left
  have hsub : Ioo 0 R ⊆ (fun s => L * s) ⁻¹' Ioo 0 (2 * L * R) := by
    intro r hr
    have h1 : L * r < L * R := mul_lt_mul_of_pos_left hr.2 hL0
    have h2 : 0 < L * R := mul_pos hL0 hR
    exact ⟨mul_pos hL0 hr.1, by linarith⟩
  have hsubst : ∫⁻ r in Ioo 0 R,
        Characterization.spatialAffineErrorSq H.spatialMap u (L * r) ∂scaleMeasure ≤
      ∫⁻ s in Ioo 0 (2 * L * R),
        Characterization.spatialAffineErrorSq H.spatialMap u s ∂scaleMeasure :=
    calc ∫⁻ r in Ioo 0 R,
          Characterization.spatialAffineErrorSq H.spatialMap u (L * r) ∂scaleMeasure
        ≤ ∫⁻ r in (fun s => L * s) ⁻¹' Ioo 0 (2 * L * R),
          Characterization.spatialAffineErrorSq H.spatialMap u (L * r) ∂scaleMeasure :=
          lintegral_mono_set hsub
      _ = _ := setLIntegral_scaleMeasure_comp_const_mul hL0
          (fun s => Characterization.spatialAffineErrorSq H.spatialMap u s) _
  unfold squareEnergy
  calc ∫⁻ r in Ioo 0 R, betaSq H.measure k .horizontal (H.map u) r ∂scaleMeasure
      ≤ ∫⁻ r in Ioo 0 R, (ENNReal.ofReal (L ^ (k + 2)) *
            Characterization.spatialAffineErrorSq H.spatialMap u (L * r) +
          b1hte_cost H u r) ∂scaleMeasure :=
        setLIntegral_mono' measurableSet_Ioo fun r hr => hbeta u r hr.1
    _ = ENNReal.ofReal (L ^ (k + 2)) * ∫⁻ r in Ioo 0 R,
            Characterization.spatialAffineErrorSq H.spatialMap u (L * r) ∂scaleMeasure +
          ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure := by
        rw [lintegral_add_right' _ hmr.aemeasurable,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by gcongr

/-- **Energy of one horizontal reference** from the beta bound, a spatial bound `C_sp` and a
temporal bound `C_t`:
`referenceEnergy (horizontal H) ≤ L^{k+2} (C_sp L² (2L)^k) + C_t (2L)^k`. -/
theorem b1hte_energy_bound {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (H : HorizontalReference n k L)
    (hmap : Measurable H.map) [IsFiniteMeasureOnCompacts H.measure]
    (hbeta : ∀ (u : Spatial k) (r : ℝ), 0 < r →
      betaSq H.measure k .horizontal (H.map u) r ≤
        ENNReal.ofReal (L ^ (k + 2)) *
            Characterization.spatialAffineErrorSq H.spatialMap u (L * r) +
          b1hte_cost H u r)
    {Csp Ct : ℝ} (hCsp : 0 ≤ Csp) (hCt : 0 ≤ Ct)
    (hsp : ∀ (b : Spatial k) (R : ℝ), 0 < R →
      ∫⁻ u in Metric.ball b R, ∫⁻ s in Ioo 0 R,
          Characterization.spatialAffineErrorSq H.spatialMap u s ∂scaleMeasure ≤
        ENNReal.ofReal (Csp * L ^ 2 * R ^ k))
    (htemp : ∀ (b : Spatial k) (R : ℝ), 0 < R →
      ∫⁻ u in Metric.ball b R, ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure ≤
        ENNReal.ofReal (Ct * R ^ k)) :
    referenceEnergy (Reference.horizontal H) ≤
      ENNReal.ofReal (L ^ (k + 2) * (Csp * L ^ 2 * (2 * L) ^ k) + Ct * (2 * L) ^ k) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hT : Measurable H.height := b1hte_measurable_height H hmap
  unfold referenceEnergy rootCarlesonSup
  refine iSup₂_le fun a _ => iSup₂_le fun R hR => ?_
  change (ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball a R,
      squareEnergy H.measure k .horizontal R z ∂H.measure ≤ _
  have h2LR : 0 < 2 * L * R := by positivity
  have hRle : R ≤ 2 * L * R := by nlinarith
  set M : ℝ≥0∞ := ENNReal.ofReal (L ^ (k + 2)) * ENNReal.ofReal (Csp * L ^ 2 * (2 * L * R) ^ k) +
    ENNReal.ofReal (Ct * (2 * L * R) ^ k) with hM
  have hpush : ∫⁻ z in Metric.ball a R, squareEnergy H.measure k .horizontal R z ∂H.measure =
      ∫⁻ u in H.map ⁻¹' Metric.ball a R, squareEnergy H.measure k .horizontal R (H.map u) :=
    setLIntegral_map (μ := volume) measurableSet_ball
      (measurable_squareEnergy H.measure k .horizontal R) hmap
  have hint : ∫⁻ z in Metric.ball a R, squareEnergy H.measure k .horizontal R z ∂H.measure ≤ M := by
    rw [hpush]
    by_cases hne : (H.map ⁻¹' Metric.ball a R).Nonempty
    · obtain ⟨v₀, hv₀⟩ := hne
      have hY : Measurable fun u => ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure :=
        (b1hte_measurable_cost H hT).lintegral_prod_right' (ν := scaleMeasure.restrict (Ioo 0 R))
      calc ∫⁻ u in H.map ⁻¹' Metric.ball a R, squareEnergy H.measure k .horizontal R (H.map u)
          ≤ ∫⁻ u in Metric.ball v₀ (2 * L * R),
              squareEnergy H.measure k .horizontal R (H.map u) :=
            lintegral_mono_set (b1hte_preimage_subset_ball hL H hv₀)
        _ ≤ ∫⁻ u in Metric.ball v₀ (2 * L * R), (ENNReal.ofReal (L ^ (k + 2)) *
                ∫⁻ s in Ioo 0 (2 * L * R),
                  Characterization.spatialAffineErrorSq H.spatialMap u s ∂scaleMeasure +
              ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure) :=
            lintegral_mono fun u => b1hte_squareEnergy_le hL H hT hbeta u hR
        _ = ENNReal.ofReal (L ^ (k + 2)) * (∫⁻ u in Metric.ball v₀ (2 * L * R),
                ∫⁻ s in Ioo 0 (2 * L * R),
                  Characterization.spatialAffineErrorSq H.spatialMap u s ∂scaleMeasure) +
              ∫⁻ u in Metric.ball v₀ (2 * L * R),
                ∫⁻ r in Ioo 0 R, b1hte_cost H u r ∂scaleMeasure := by
            rw [lintegral_add_right' _ hY.aemeasurable,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (L ^ (k + 2)) * ENNReal.ofReal (Csp * L ^ 2 * (2 * L * R) ^ k) +
              ∫⁻ u in Metric.ball v₀ (2 * L * R),
                ∫⁻ r in Ioo 0 (2 * L * R), b1hte_cost H u r ∂scaleMeasure := by
            exact add_le_add (mul_le_mul_right (hsp v₀ (2 * L * R) h2LR) _)
              (lintegral_mono fun u => lintegral_mono_set (Ioo_subset_Ioo_right hRle))
        _ ≤ M := by
            rw [hM]
            exact add_le_add le_rfl (htemp v₀ (2 * L * R) h2LR)
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, Measure.restrict_empty, lintegral_zero_measure]
      exact zero_le
  have hRi : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  have h2L : 0 ≤ 2 * L * R := h2LR.le
  have hA : 0 ≤ Csp * L ^ 2 * (2 * L * R) ^ k := by positivity
  have hB : 0 ≤ Ct * (2 * L * R) ^ k := by positivity
  have h1 : R⁻¹ ^ k * R ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ hR.ne', one_pow]
  calc (ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball a R,
        squareEnergy H.measure k .horizontal R z ∂H.measure
      ≤ (ENNReal.ofReal R)⁻¹ ^ k * M := mul_le_mul_right hint _
    _ = ENNReal.ofReal (R⁻¹ ^ k * (L ^ (k + 2) * (Csp * L ^ 2 * (2 * L * R) ^ k) +
          Ct * (2 * L * R) ^ k)) := by
        rw [hM, ← ENNReal.ofReal_mul (pow_nonneg hL0.le _),
          ← ENNReal.ofReal_add (mul_nonneg (pow_nonneg hL0.le _) hA) hB,
          ← ENNReal.ofReal_inv_of_pos hR, ← ENNReal.ofReal_pow hRi,
          ← ENNReal.ofReal_mul (pow_nonneg hRi _)]
    _ = ENNReal.ofReal (L ^ (k + 2) * (Csp * L ^ 2 * (2 * L) ^ k) + Ct * (2 * L) ^ k) := by
        congr 1
        calc R⁻¹ ^ k * (L ^ (k + 2) * (Csp * L ^ 2 * (2 * L * R) ^ k) + Ct * (2 * L * R) ^ k)
            = (L ^ (k + 2) * (Csp * L ^ 2 * (2 * L) ^ k) + Ct * (2 * L) ^ k) *
                (R⁻¹ ^ k * R ^ k) := by ring
          _ = _ := by rw [h1, mul_one]

/-- **`ba1_horizontal_energy`**, in the implication form of its
type: given the conclusions `hbasic` (measurability of `(F,T)` and finiteness of `σ` on
compacts are used), `hbeta` of `ba1_horizontal_beta`, the input `hsp`
(`Characterization.SpatialAffineSquareStatement`, used at `(k, n)` with the vector map `F` and
Lipschitz constant `L`) and `htemp` of `ba1_horizontal_temporal`, the constant
`C = L^{k+2} C_sp L² (2L)^k + C_t (2L)^k`, chosen from `(n,k,L)` before the reference, bounds
the own-type energy of every horizontal `L`-reference. -/
theorem ba1_horizontal_energy_proof
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      Measurable H.map ∧ IsClosed H.carrier ∧ IsFiniteMeasureOnCompacts H.measure ∧
        H.measure.InnerRegular)
    (hbeta : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L →
      ∀ (H : HorizontalReference n k L) (u : Spatial k) (r : ℝ), 0 < r →
        betaSq H.measure k .horizontal (H.map u) r ≤
          ENNReal.ofReal (L ^ (k + 2)) *
              Characterization.spatialAffineErrorSq H.spatialMap u (L * r) +
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|))
    (hsp : Characterization.SpatialAffineSquareStatement)
    (htemp : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ (H : HorizontalReference n k L) (b : Spatial k) (R : ℝ), 0 < R →
        ∫⁻ u in Metric.ball b R, ∫⁻ r in Ioo 0 R,
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure ≤
          ENNReal.ofReal (C * R ^ k)) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ H : HorizontalReference n k L,
        referenceEnergy (Reference.horizontal H) ≤ ENNReal.ofReal C := by
  intro n k L hL
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨Csp, hCsp, hsp'⟩ := hsp k n
  obtain ⟨Ct, hCt, htemp'⟩ := htemp n k L hL
  have hpos : 0 < L ^ (k + 2) * (Csp * L ^ 2 * (2 * L) ^ k) + Ct * (2 * L) ^ k := by
    have h2L : 0 < 2 * L := by positivity
    exact add_pos (mul_pos (pow_pos hL0 _) (mul_pos (mul_pos hCsp (pow_pos hL0 2))
      (pow_pos h2L _))) (mul_pos hCt (pow_pos h2L _))
  refine ⟨_, hpos, fun H => ?_⟩
  obtain ⟨hmap, -, hfin, -⟩ := hbasic n k L hL H
  have := hfin
  have hspH : ∀ (b : Spatial k) (R : ℝ), 0 < R →
      ∫⁻ u in Metric.ball b R, ∫⁻ s in Ioo 0 R,
          Characterization.spatialAffineErrorSq H.spatialMap u s ∂scaleMeasure ≤
        ENNReal.ofReal (Csp * L ^ 2 * R ^ k) := by
    intro b R hR
    have h := hsp' H.spatialMap (Real.toNNReal L) (b1hte_lipschitz hL H) b R hR
    rwa [Real.coe_toNNReal L hL0.le] at h
  exact b1hte_energy_bound hL H hmap (hbeta n k L hL H) hCsp.le hCt.le hspH
    (htemp' H)

end ParabolicRectifiability.QuantitativeCharacterization
