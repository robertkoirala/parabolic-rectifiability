import ParabolicRectifiability.Analysis.ParabolicBMO
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Gluing local half-time representatives

`exists_halfTime_representative_of_local_proof` glues local half-time representatives into a
global one. The ingredients are:

* **Uniqueness on an open set** (`rx3_repHalf_ae_eq`): two local representatives of the same
  `L²` function on an open set `Ω` agree almost everywhere on `Ω`. This is mathlib's open-set
  lemma `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` applied to their
  difference, not its global variant.
* **Transport** between `SubspaceSpace W` with `intrinsicParabolicVolume W` and Fourier
  coordinates with `volume`, by the measure-preserving measurable equivalence
  `subspaceFourierToParabolic W`, and between `W^⊥` and its orthonormal coordinates by the
  linear isometry `normalCoordinates W`.
* **Countable exhaustion**: with `p₀ = Φ 0`, local representatives `G k` on the balls
  `P(p₀, k+1)` are glued as `g x = G (N x) x`, where `N x` is the least `k` with
  `x ∈ P(p₀, k+1)`. On each ball `g = G k` almost everywhere (countably many overlaps), every
  compact test support lies in some `Φ⁻¹ P(p₀, k+1)`, and local integrability follows from
  the components. At `d = 0` nothing special happens: all statements over `Fin 0` are vacuous.

The helper `rx3_memLp_assemble` repeats the proof of `rx5_memLp_assemble` (`LocalComponent`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability

open HalfTimeDerivative

section Scalar

variable {m : ℕ}

/-- Restriction of a local representation to an open subset. -/
theorem rx3_repHalf_mono {H g : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    {Ω Ω' : Set (FourierSpace m)} (h : RepHalf hH g Ω) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) :
    RepHalf hH g Ω' :=
  ⟨hΩ', h.2.1.mono_set hsub, fun φ hφ hc hs => h.2.2 φ hφ hc (hs.trans hsub)⟩

/-- **Uniqueness on an open set.** Two local representatives of the same `L²` function on the
same open set agree almost everywhere there. -/
theorem rx3_repHalf_ae_eq {H g₁ g₂ : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    {Ω : Set (FourierSpace m)} (h₁ : RepHalf hH g₁ Ω) (h₂ : RepHalf hH g₂ Ω) :
    g₁ =ᵐ[volume.restrict Ω] g₂ := by
  have hΩ : IsOpen Ω := h₁.1
  have hloc : LocallyIntegrableOn (fun x => (g₁ x : ℂ) - (g₂ x : ℂ)) Ω volume :=
    ((Complex.ofRealCLM.locallyIntegrableOn_comp h₁.2.1).sub
      (Complex.ofRealCLM.locallyIntegrableOn_comp h₂.2.1) :)
  have key := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun φ hφ hc hs => by
    have e : (∫ x, (g₁ x : ℂ) * (φ x : ℂ)) = ∫ x, (g₂ x : ℂ) * (φ x : ℂ) :=
      (h₁.2.2 φ hφ hc hs).symm.trans (h₂.2.2 φ hφ hc hs)
    have i₁ := (repHalf_test_integrable hH h₁ φ hφ hc hs).2
    have i₂ := (repHalf_test_integrable hH h₂ φ hφ hc hs).2
    calc (∫ x, φ x • ((g₁ x : ℂ) - (g₂ x : ℂ)))
        = ∫ x, ((g₁ x : ℂ) * (φ x : ℂ) - (g₂ x : ℂ) * (φ x : ℂ)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [Complex.real_smul]
          ring
      _ = 0 := by rw [integral_sub i₁ i₂, e, sub_self]
  rw [Filter.EventuallyEq, ae_restrict_iff' hΩ.measurableSet]
  filter_upwards [key] with x hx hxΩ
  have h0 : (g₁ x : ℂ) - (g₂ x : ℂ) = 0 := hx hxΩ
  exact_mod_cast sub_eq_zero.1 h0

/-- **Exhaustion.** A representation on each set of a family absorbing every compact set is a
global representation. -/
theorem rx3_repHalf_univ_of_exhaustion {H g : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (Ω : ℕ → Set (FourierSpace m)) (hrep : ∀ k, RepHalf hH g (Ω k))
    (hcov : ∀ K : Set (FourierSpace m), IsCompact K → ∃ k, K ⊆ Ω k) :
    RepHalf hH g univ := by
  refine ⟨isOpen_univ, ?_, fun φ hφ hc _ => ?_⟩
  · rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro K hK
    obtain ⟨k, hk⟩ := hcov K hK
    exact (hrep k).2.1.integrableOn_compact_subset hk hK
  · obtain ⟨k, hk⟩ := hcov _ hc
    exact (hrep k).2.2 φ hφ hc hk

end Scalar

section Cylinder

theorem rx3_isOpen_analyticCylinder {k : ℕ} (z : Space k) (r : ℝ) :
    IsOpen (analyticCylinder z r) :=
  (Metric.isOpen_ball.prod isOpen_Ioo).preimage (fourierCoordinatesHomeomorph k).continuous

theorem rx3_exists_isCompact_superset_analyticCylinder {k : ℕ} (z : Space k) (r : ℝ) :
    ∃ K, IsCompact K ∧ analyticCylinder z r ⊆ K :=
  ⟨fourierCoordinatesHomeomorph k ⁻¹'
      (Metric.closedBall z.1 r ×ˢ Icc (z.2.val - r ^ 2) (z.2.val + r ^ 2)),
    (fourierCoordinatesHomeomorph k).isCompact_preimage.2
      ((isCompact_closedBall _ _).prod isCompact_Icc),
    fun _ hx => ⟨Metric.ball_subset_closedBall hx.1, Ioo_subset_Icc_self hx.2⟩⟩

end Cylinder

section Vector

variable {n : ℕ}

theorem rx3_isOpen_preimage_ball (W : Submodule ℝ (Spatial n)) (p : SubspaceSpace W)
    (r : ℝ) : IsOpen (subspaceFourierToParabolic W ⁻¹' Metric.ball p r) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Metric.ball_eq_empty.2 hr, preimage_empty]
    exact isOpen_empty
  · rw [subspaceFourier_preimage_ball W p r hr]
    exact rx3_isOpen_analyticCylinder _ r

/-- Componentwise almost-everywhere equality in Fourier coordinates gives vector
almost-everywhere equality for the intrinsic volume. -/
theorem rx3_ae_eq_of_components (W : Submodule ℝ (Spatial n))
    {u v : SubspaceSpace W → W.orthogonal} (S : Set (SubspaceSpace W))
    (h : ∀ i, normalFourierComponent W u i =ᵐ[volume.restrict (subspaceFourierToParabolic W ⁻¹' S)]
      normalFourierComponent W v i) :
    u =ᵐ[(intrinsicParabolicVolume W).restrict S] v := by
  have hmp := (subspaceFourierToParabolic_measurePreserving W).restrict_preimage_emb
    (subspaceFourierToParabolic W).measurableEmbedding S
  rw [Filter.EventuallyEq, ← hmp.map_eq,
    (subspaceFourierToParabolic W).measurableEmbedding.ae_map_iff]
  filter_upwards [ae_all_iff.2 h] with x hx
  exact (normalCoordinates W).injective (PiLp.ext fun i => hx i)

/-- Vector almost-everywhere equality gives componentwise equality in Fourier coordinates. -/
theorem rx3_components_of_ae_eq (W : Submodule ℝ (Spatial n))
    {u v : SubspaceSpace W → W.orthogonal} (S : Set (SubspaceSpace W))
    (h : u =ᵐ[(intrinsicParabolicVolume W).restrict S] v) (i : Fin (Module.finrank ℝ W.orthogonal)) :
    normalFourierComponent W u i =ᵐ[volume.restrict (subspaceFourierToParabolic W ⁻¹' S)]
      normalFourierComponent W v i := by
  have hmp := (subspaceFourierToParabolic_measurePreserving W).restrict_preimage_emb
    (subspaceFourierToParabolic W).measurableEmbedding S
  filter_upwards [hmp.quasiMeasurePreserving.ae h] with x hx
  unfold normalFourierComponent
  rw [hx]

/-- **Vector uniqueness.** Two local representatives of the same `F` on `Φ⁻¹ S` agree
almost everywhere on `S`. -/
theorem rx3_ae_eq_of_local_rep (W : Submodule ℝ (Spatial n))
    (F g₁ g₂ : SubspaceSpace W → W.orthogonal) (S : Set (SubspaceSpace W))
    (h₁ : ∀ i, ∃ hH : MemLp (normalFourierComponent W F i) 2 volume,
      RepHalf hH (normalFourierComponent W g₁ i) (subspaceFourierToParabolic W ⁻¹' S))
    (h₂ : ∀ i, ∃ hH : MemLp (normalFourierComponent W F i) 2 volume,
      RepHalf hH (normalFourierComponent W g₂ i) (subspaceFourierToParabolic W ⁻¹' S)) :
    g₁ =ᵐ[(intrinsicParabolicVolume W).restrict S] g₂ :=
  rx3_ae_eq_of_components W S fun i => by
    obtain ⟨hH, r₁⟩ := h₁ i
    obtain ⟨_, r₂⟩ := h₂ i
    exact rx3_repHalf_ae_eq hH r₁ r₂

theorem rx3_assemble_components (W : Submodule ℝ (Spatial n)) (v : W.orthogonal) :
    (normalCoordinates W).symm (WithLp.toLp 2 (fun i => normalCoordinates W v i)) = v := by
  rw [LinearIsometryEquiv.symm_apply_eq]

/-- Same statement and proof as `rx5_memLp_assemble` (`LocalComponent`). -/
theorem rx3_memLp_assemble {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (W : Submodule ℝ (Spatial n)) (c : Fin (Module.finrank ℝ W.orthogonal) → α → ℝ)
    (hc : ∀ i, MemLp (c i) p μ) :
    MemLp (fun x => (normalCoordinates W).symm (WithLp.toLp 2 (fun i => c i x))) p μ := by
  have hv : MemLp (fun x => (WithLp.toLp 2 (fun i => c i x) :
      Spatial (Module.finrank ℝ W.orthogonal))) p μ := memLp_piLp_iff.2 hc
  exact (normalCoordinates W).symm.lipschitzWith.comp_memLp (map_zero _) hv

/-- **`exists_halfTime_representative_of_local`**: local half-time representatives combine
into a global one. -/
theorem exists_halfTime_representative_of_local_proof {n : ℕ} (W : Submodule ℝ (Spatial n))
    (F : SubspaceSpace W → W.orthogonal)
    (hloc : ∀ (p : SubspaceSpace W) (r : ℝ), 0 < r → ∃ g' : SubspaceSpace W → W.orthogonal,
      ∀ i, ∃ hH : MemLp (normalFourierComponent W F i) 2 volume,
        HalfTimeDerivative.RepHalf hH (normalFourierComponent W g' i)
          (subspaceFourierToParabolic W ⁻¹' Metric.ball p r)) :
    ∃ g : SubspaceSpace W → W.orthogonal,
      RepresentsHalfTimeDerivative W F g ∧ LocallyIntegrable g (intrinsicParabolicVolume W) ∧
      ∀ (p : SubspaceSpace W) (r : ℝ), 0 < r → ∀ g' : SubspaceSpace W → W.orthogonal,
        (∀ i, ∃ hH : MemLp (normalFourierComponent W F i) 2 volume,
          HalfTimeDerivative.RepHalf hH (normalFourierComponent W g' i)
            (subspaceFourierToParabolic W ⁻¹' Metric.ball p r)) →
        g =ᵐ[(intrinsicParabolicVolume W).restrict (Metric.ball p r)] g' := by
  classical
  let p₀ : SubspaceSpace W := subspaceFourierToParabolic W 0
  have hpos : ∀ k : ℕ, (0 : ℝ) < k + 1 := fun k => by positivity
  choose G hG using fun k : ℕ => hloc p₀ (k + 1) (hpos k)
  have hmono : ∀ {j k : ℕ}, j ≤ k →
      Metric.ball p₀ ((j : ℝ) + 1) ⊆ Metric.ball p₀ ((k : ℝ) + 1) := fun hjk => by
    have := (Nat.cast_le (α := ℝ)).2 hjk
    exact Metric.ball_subset_ball (by linarith)
  have hex : ∀ x : SubspaceSpace W, ∃ k : ℕ, x ∈ Metric.ball p₀ ((k : ℝ) + 1) := fun x => by
    obtain ⟨k, hk⟩ := exists_nat_gt (dist x p₀)
    exact ⟨k, Metric.mem_ball.2 (by linarith)⟩
  -- `G k` restricted to a smaller ball of the exhaustion
  have hGmono : ∀ {j k : ℕ}, j ≤ k → ∀ i, ∃ hH : MemLp (normalFourierComponent W F i) 2 volume,
      RepHalf hH (normalFourierComponent W (G k) i)
        (subspaceFourierToParabolic W ⁻¹' Metric.ball p₀ ((j : ℝ) + 1)) := fun hjk i => by
    obtain ⟨hH, h⟩ := hG _ i
    exact ⟨hH, rx3_repHalf_mono hH h (rx3_isOpen_preimage_ball W p₀ _)
      (preimage_mono (hmono hjk))⟩
  -- the glued function
  let g : SubspaceSpace W → W.orthogonal := fun x => G (Nat.find (hex x)) x
  have hA : ∀ k : ℕ,
      g =ᵐ[(intrinsicParabolicVolume W).restrict (Metric.ball p₀ ((k : ℝ) + 1))] G k := by
    intro k
    have hall : ∀ᵐ x ∂intrinsicParabolicVolume W, ∀ j : ℕ, j ≤ k →
        x ∈ Metric.ball p₀ ((j : ℝ) + 1) → G j x = G k x := by
      rw [ae_all_iff]
      intro j
      by_cases hj : j ≤ k
      · have h := rx3_ae_eq_of_local_rep W F (G j) (G k) _ (hG j) (hGmono hj)
        rw [Filter.EventuallyEq, ae_restrict_iff' Metric.isOpen_ball.measurableSet] at h
        filter_upwards [h] with x hx _ hxj using hx hxj
      · exact Filter.Eventually.of_forall fun x hjk => absurd hjk hj
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet,
      ae_restrict_of_ae hall] with x hx hx'
    exact hx' _ (Nat.find_min' (hex x) hx) (Nat.find_spec (hex x))
  -- every compact set of Fourier space lies in one set of the exhaustion
  have hcov : ∀ K : Set (FourierSpace (Module.finrank ℝ W)), IsCompact K →
      ∃ k : ℕ, K ⊆ subspaceFourierToParabolic W ⁻¹' Metric.ball p₀ ((k : ℝ) + 1) := by
    intro K hK
    refine hK.elim_directed_cover _ (fun k => rx3_isOpen_preimage_ball W p₀ _) ?_ ?_
    · intro x _
      obtain ⟨k, hk⟩ := hex (subspaceFourierToParabolic W x)
      exact mem_iUnion.2 ⟨k, hk⟩
    · exact Monotone.directed_le fun j k hjk => preimage_mono (hmono hjk)
  -- global representation, componentwise
  have hrepG : RepresentsHalfTimeDerivative W F g := by
    intro i
    obtain ⟨hH, -⟩ := hG 0 i
    refine ⟨hH, rx3_repHalf_univ_of_exhaustion hH
      (fun k : ℕ => subspaceFourierToParabolic W ⁻¹' Metric.ball p₀ ((k : ℝ) + 1))
      (fun k => ?_) hcov⟩
    obtain ⟨hH', hk⟩ := hG k i
    exact (repHalf_congr hH' hH Filter.EventuallyEq.rfl
      (rx3_components_of_ae_eq W _ (hA k).symm i)).1 hk
  -- local integrability, from the components
  have hcompLI : ∀ i, LocallyIntegrable (normalFourierComponent W g i) volume := fun i => by
    obtain ⟨_, h⟩ := hrepG i
    exact locallyIntegrableOn_univ.1 h.2.1
  have hgΦ : ∀ K, IsCompact K →
      IntegrableOn (fun x => g (subspaceFourierToParabolic W x)) K volume := by
    intro K hK
    have hm := rx3_memLp_assemble (μ := volume.restrict K) (p := 1) W
      (fun i => normalFourierComponent W g i)
      (fun i => memLp_one_iff_integrable.2 ((hcompLI i).integrableOn_isCompact hK))
    rw [memLp_one_iff_integrable] at hm
    refine hm.congr (Filter.Eventually.of_forall fun x => ?_)
    exact rx3_assemble_components W _
  have hli : LocallyIntegrable g (intrinsicParabolicVolume W) := by
    intro y
    obtain ⟨K, hK, hsub⟩ :=
      rx3_exists_isCompact_superset_analyticCylinder (subspaceParabolicIsometry W y) 1
    refine ⟨Metric.ball y 1, Metric.ball_mem_nhds y one_pos, ?_⟩
    rw [← (subspaceFourierToParabolic_measurePreserving W).integrableOn_comp_preimage
      (subspaceFourierToParabolic W).measurableEmbedding,
      subspaceFourier_preimage_ball W y 1 one_pos]
    exact (hgΦ K hK).mono_set hsub
  refine ⟨g, hrepG, hli, fun p r hr g' hg' => ?_⟩
  -- uniqueness against an arbitrary local representative
  obtain ⟨k, hk⟩ := exists_nat_gt (dist p p₀ + r)
  have hsub : Metric.ball p r ⊆ Metric.ball p₀ ((k : ℝ) + 1) :=
    Metric.ball_subset_ball' (by linarith)
  have h1 : g =ᵐ[(intrinsicParabolicVolume W).restrict (Metric.ball p r)] G k :=
    ae_restrict_of_ae_restrict_of_subset hsub (hA k)
  have h2 : G k =ᵐ[(intrinsicParabolicVolume W).restrict (Metric.ball p r)] g' :=
    rx3_ae_eq_of_local_rep W F (G k) g' _ (fun i => by
      obtain ⟨hH, h⟩ := hG k i
      exact ⟨hH, rx3_repHalf_mono hH h (rx3_isOpen_preimage_ball W p r)
        (preimage_mono hsub)⟩) hg'
  exact h1.trans h2

end Vector

end ParabolicRectifiability
