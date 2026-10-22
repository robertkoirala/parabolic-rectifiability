import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion
import ParabolicRectifiability.Analysis.RegularExtension.AffineCarlesonBMO
import ParabolicRectifiability.Analysis.RegularExtension.LocalComponent
import ParabolicRectifiability.Analysis.TraceExtension.TracePieces.Transport
import ParabolicRectifiability.Foundations.Proofs.CompactBridge

/-! # The standard-coordinate affine-to-BMO bridge, coordinatewise

Proof of `d1e_standard_affineBMO_proof : d1e_StandardAffineBMOStatement` (`q-affinebmo`).

Route (codimension-one realization).
* `d1ebmo_coordinate`: the coordinate `H · α = proj α ∘ H` keeps compact support, the
  Lipschitz constant and the affine Carleson bound (`rx5_hasAffineCarlesonBound_comp_clm` with
  `affineErrorSq_component_le_proof`, `‖proj α‖ ≤ 1`). Nothing is assumed about the plane in
  which `H` takes values.
* `d1ebmo_scalar`: for a subspace `W ⊆ ℝ^n`, a normal index `i₀` and a scalar `h` on
  `Space (rank W)`, the lift `h̃ = J ∘ h ∘ e` with `e = subspaceParabolicIsometry W` and
  `J t = t • v`, `v` the `i₀`-th normal basis vector (`‖J‖ = 1`, `normalCoordinates W (J t) i₀
  = t`), has the same compact support, Lipschitz constant and affine Carleson bound
  (`hasAffineCarlesonBound_comp_subspaceParabolicIsometry_proof`). The intrinsic theorem
  `halfTimeBMO_of_affineCarleson_proof` gives `g`; the `i₀`-th normal Fourier component of
  `h̃` is exactly `h ∘ fourierToParabolic`, so `RepHalf` is about the standard function itself,
  and `fcond_representsHomogeneous_const_add` with constant `0` gives the homogeneous
  representation by `f = (normalCoordinates W (g ∘ e⁻¹)) i₀`.
* `d1ebmo_bmo_transport`: one normal coordinate of a vector BMO function, read through `e⁻¹`,
  has the same real BMO bound (`e` preserves balls and carries the intrinsic volume to
  `parabolicVolume`; the coordinate functional has norm at most one and commutes with the ball
  average).
* `d1ebmo_of_subspace`: the constant of `halfTimeBMO_of_affineCarleson_proof (rank W)
  (rank Wᗮ)`, for a rank `k` with `rank W = k` (the rank cast is a `subst`).
* `d1ebmo_exists_codimOne`: `W = (span {e_last})ᗮ = ℝ^m × {0} ⊆ ℝ^{m+1}`, `rank W = m`,
  `rank Wᗮ = 1`. Works at `m = 0`.

The constant `C` depends on `m` only (through the fixed `W ⊆ ℝ^{m+1}`), not on `d`, `H`, `L`, `B`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Module
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

open ParabolicRectifiability.Foundations

/-- A Euclidean coordinate functional has operator norm at most one. -/
theorem d1ebmo_norm_proj_le {d : ℕ} (α : Fin d) :
    ‖(EuclideanSpace.proj α : Spatial d →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact PiLp.norm_apply_le x α

/-- **The coordinate keeps the hypotheses.** The Euclidean coordinate `p ↦ H p α` of a compactly
supported `L`-Lipschitz map with affine Carleson bound `B` is compactly supported, `L`-Lipschitz
and has affine Carleson bound `B`. -/
theorem d1ebmo_coordinate {m d : ℕ} (H : Space m → Spatial d) (L : ℝ≥0) (B : ℝ)
    (hc : HasCompactSupport H) (hL : LipschitzWith L H)
    (hcarl : HasAffineCarlesonBound (parabolicVolume m) H B) (α : Fin d) :
    HasCompactSupport (fun p => H p α) ∧ LipschitzWith L (fun p => H p α) ∧
      HasAffineCarlesonBound (parabolicVolume m) (fun p => H p α) B := by
  refine ⟨?_, ?_, ?_⟩
  · exact hc.comp_left (g := fun v : Spatial d => v α) (by simp)
  · exact LipschitzWith.of_dist_le_mul fun p q =>
      (PiLp.dist_apply_le (H p) (H q) α).trans (hL.dist_le_mul p q)
  · exact rx5_hasAffineCarlesonBound_comp_clm (EuclideanSpace.proj α : Spatial d →L[ℝ] ℝ)
      (fun y s => affineErrorSq_component_le_proof _ _ (d1ebmo_norm_proj_le α) _ y s) hcarl

/-- **BMO transport to the standard base.** If `g` has vector parabolic BMO bound `B` on the
intrinsic base `W × Time`, `c` is a functional of norm at most one on `Wᗮ`, and `f` is a real
function on `Space (rank W)` with `f ∘ e = c ∘ g` (`e = subspaceParabolicIsometry W`), then `f`
has real parabolic BMO bound `B` on the standard base. -/
theorem d1ebmo_bmo_transport {n : ℕ} (W : Submodule ℝ (Spatial n))
    {g : SubspaceSpace W → W.orthogonal} {B : ℝ} (hg : HasParabolicBMOBound W g B)
    (c : W.orthogonal →L[ℝ] ℝ) (hc1 : ∀ v, ‖c v‖ ≤ ‖v‖)
    (f : Space (Module.finrank ℝ W) → ℝ)
    (hf : ∀ x, f (subspaceParabolicIsometry W x) = c (g x)) :
    HasStandardParabolicBMOBound (Module.finrank ℝ W) f B := by
  obtain ⟨hB, hloc, hosc⟩ := hg
  have hmp := subspaceParabolic_measurePreserving W
  have hemb := (subspaceParabolicMeasurableEquiv W).measurableEmbedding
  refine ⟨hB, ?_, fun p r hr => ?_⟩
  · have hfe : f ∘ (subspaceParabolicIsometry W).toHomeomorph = fun z => c (g z) := funext hf
    rw [← hmp.map_eq]
    refine (locallyIntegrable_map_homeomorph (subspaceParabolicIsometry W).toHomeomorph).mpr ?_
    rw [hfe]
    exact locallyIntegrable_iff.2 fun K hK => c.integrable_comp (hloc.integrableOn_isCompact hK)
  · obtain ⟨p', rfl⟩ : ∃ p', subspaceParabolicIsometry W p' = p :=
      ⟨(subspaceParabolicIsometry W).symm p, (subspaceParabolicIsometry W).apply_symm_apply p⟩
    have hpre : (subspaceParabolicMeasurableEquiv W) ⁻¹'
        Metric.ball (subspaceParabolicIsometry W p') r = Metric.ball p' r :=
      (subspaceParabolicIsometry W).isometry.preimage_ball p' r
    have hvol : parabolicVolume (Module.finrank ℝ W)
        (Metric.ball (subspaceParabolicIsometry W p') r) =
          intrinsicParabolicVolume W (Metric.ball p' r) := by
      rw [← hpre, hmp.measure_preimage_equiv]
    have hI : ∀ G : Space (Module.finrank ℝ W) → ℝ,
        ∫ q in Metric.ball (subspaceParabolicIsometry W p') r, G q
            ∂parabolicVolume (Module.finrank ℝ W) =
          ∫ x in Metric.ball p' r, G (subspaceParabolicIsometry W x)
            ∂intrinsicParabolicVolume W := by
      intro G
      rw [← hpre]
      exact (hmp.setIntegral_preimage_emb hemb G _).symm
    have hV := intrinsicBall_volume_pos_lt_top W p' hr
    have hgint : IntegrableOn g (Metric.ball p' r) (intrinsicParabolicVolume W) :=
      (hloc.integrableOn_isCompact (isCompact_closedBall p' r)).mono_set
        Metric.ball_subset_closedBall
    have havg : standardBallAverage (Module.finrank ℝ W) f (subspaceParabolicIsometry W p') r =
        c (parabolicBallAverage W g p' r) := by
      rw [standardBallAverage, parabolicBallAverage, hvol, hI, map_smul]
      congr 1
      simp only [hf]
      exact c.integral_comp_comm hgint
    rw [havg, hvol, hI]
    refine le_trans (div_le_div_of_nonneg_right ?_ ENNReal.toReal_nonneg) (hosc p' r hr)
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
      ((hgint.sub (integrableOn_const (C := parabolicBallAverage W g p' r) hV.2.ne
        enorm_ne_top)).norm) (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf]
    rw [← map_sub]
    exact hc1 _

/-- **The scalar transport.** For a subspace `W` and a normal index `i₀`, the intrinsic
affine-to-BMO conclusion `hmain` on `W` (constant `C`) gives the standard-base half-time BMO bound
`C (L + √B)` for every compactly supported `L`-Lipschitz `h : Space (rank W) → ℝ` with affine
Carleson bound `B`. -/
theorem d1ebmo_scalar {n : ℕ} (W : Submodule ℝ (Spatial n))
    (i₀ : Fin (Module.finrank ℝ W.orthogonal)) {C : ℝ}
    (hmain : ∀ (F : SubspaceSpace W → W.orthogonal) (L : ℝ≥0) (B : ℝ),
      HasCompactSupport F → LipschitzWith L F →
      HasAffineCarlesonBound (intrinsicParabolicVolume W) F B →
      ∃ g : SubspaceSpace W → W.orthogonal,
        RepresentsHalfTimeDerivative W F g ∧
          HasParabolicBMOBound W g (C * ((L : ℝ) + Real.sqrt B)))
    (h : Space (Module.finrank ℝ W) → ℝ) (L : ℝ≥0) (B : ℝ) (hc : HasCompactSupport h)
    (hL : LipschitzWith L h)
    (hcarl : HasAffineCarlesonBound (parabolicVolume (Module.finrank ℝ W)) h B) :
    HasHalfTimeBMOBound (Module.finrank ℝ W) h (C * ((L : ℝ) + Real.sqrt B)) := by
  -- the normal-coordinate identification `J : ℝ → Wᗮ`
  obtain ⟨J, hJ, hJv⟩ : ∃ J : ℝ →L[ℝ] W.orthogonal, ‖J‖ ≤ 1 ∧
      ∀ t, normalCoordinates W (J t) i₀ = t :=
    ⟨ContinuousLinearMap.toSpanSingleton ℝ
      ((normalCoordinates W).symm (EuclideanSpace.single i₀ (1 : ℝ))), by simp,
      fun t => by simp⟩
  -- the coordinate functional `c = (normalCoordinates W ·) i₀`
  obtain ⟨c, hcapp⟩ : ∃ c : W.orthogonal →L[ℝ] ℝ, ∀ v, c v = normalCoordinates W v i₀ :=
    ⟨(EuclideanSpace.proj i₀ : Spatial (Module.finrank ℝ W.orthogonal) →L[ℝ] ℝ).comp
      ((normalCoordinates W).toContinuousLinearEquiv :
        W.orthogonal →L[ℝ] Spatial (Module.finrank ℝ W.orthogonal)), fun v => rfl⟩
  have hc1 : ∀ v, ‖c v‖ ≤ ‖v‖ := fun v => by
    rw [hcapp, Real.norm_eq_abs]
    exact subspaceCoordinate_abs_le_norm W.orthogonal v i₀
  have hJ1 : LipschitzWith 1 J := LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    exact (J.le_of_opNorm_le hJ (a - b)).trans_eq (one_mul _)
  -- the lift `h̃ = J ∘ h ∘ e` and its hypotheses
  have hFc : HasCompactSupport (fun z => J (h (subspaceParabolicIsometry W z))) :=
    (hc.comp_left (g := J) J.map_zero).comp_homeomorph (subspaceParabolicIsometry W).toHomeomorph
  have hFL : LipschitzWith L (fun z => J (h (subspaceParabolicIsometry W z))) := by
    have h3 := (hJ1.comp hL).comp (subspaceParabolicIsometry W).isometry.lipschitzWith
    rw [one_mul, mul_one] at h3
    exact h3
  have hJcarl : HasAffineCarlesonBound (parabolicVolume (Module.finrank ℝ W))
      (fun q => J (h q)) B :=
    rx5_hasAffineCarlesonBound_comp_clm J
      (fun y s => affineErrorSq_component_le_proof _ J hJ _ y s) hcarl
  have hFcarl : HasAffineCarlesonBound (intrinsicParabolicVolume W)
      (fun z => J (h (subspaceParabolicIsometry W z))) B :=
    (hasAffineCarlesonBound_comp_subspaceParabolicIsometry_proof W (fun q => J (h q)) B).mp
      hJcarl
  obtain ⟨g, hrep, hbmo⟩ := hmain _ L B hFc hFL hFcarl
  obtain ⟨hH, hR⟩ := hrep i₀
  refine ⟨⟨L, hL⟩, fun p => normalCoordinates W (g ((subspaceParabolicIsometry W).symm p)) i₀,
    d1ebmo_bmo_transport W hbmo c hc1 _ (fun x => by simp [hcapp]), ?_⟩
  -- the representation: the `i₀`-th normal component of `h̃` is `h ∘ fourierToParabolic`
  have h1 : (fun x => (0 : ℝ) + normalFourierComponent W
      (fun z => J (h (subspaceParabolicIsometry W z))) i₀ x) =
        fun x => h (fourierToParabolic (Module.finrank ℝ W) x) := by
    funext x
    simp only [zero_add, normalFourierComponent, hJv]
    rw [rx5_subspaceFourierToParabolic_eq, IsometryEquiv.apply_symm_apply]
  have h2 : normalFourierComponent W g i₀ = fun x => normalCoordinates W
      (g ((subspaceParabolicIsometry W).symm (fourierToParabolic (Module.finrank ℝ W) x))) i₀ := by
    funext x
    rw [normalFourierComponent, rx5_subspaceFourierToParabolic_eq]
  have key := fcond_representsHomogeneous_const_add hH hR 0
  rw [h1, h2] at key
  exact key

/-- **The rank cast.** For a subspace `W` with a normal index and `rank W = k`, the constant of
the intrinsic theorem on `W` works for the coordinatewise standard-base statement in rank `k`. -/
theorem d1ebmo_of_subspace {n : ℕ} (W : Submodule ℝ (Spatial n))
    (i₀ : Fin (Module.finrank ℝ W.orthogonal)) (k : ℕ) (hk : Module.finrank ℝ W = k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (H : Space k → Spatial d) (L : ℝ≥0) (B : ℝ),
      HasCompactSupport H → LipschitzWith L H → HasAffineCarlesonBound (parabolicVolume k) H B →
      ∀ α : Fin d, HasHalfTimeBMOBound k (fun p => H p α) (C * ((L : ℝ) + Real.sqrt B)) := by
  subst hk
  obtain ⟨C, hC, hmain⟩ := halfTimeBMO_of_affineCarleson_proof (Module.finrank ℝ W)
    (Module.finrank ℝ W.orthogonal)
  refine ⟨C, hC, fun d H L B hc hL hcarl α => ?_⟩
  obtain ⟨hc', hL', hcarl'⟩ := d1ebmo_coordinate H L B hc hL hcarl α
  exact d1ebmo_scalar W i₀ (hmain W rfl rfl) _ L B hc' hL' hcarl'

/-- **The codimension-one realization** `W = (span {e_last})ᗮ = ℝ^m × {0} ⊆ ℝ^{m+1}`. -/
theorem d1ebmo_exists_codimOne (m : ℕ) :
    ∃ W : Submodule ℝ (Spatial (m + 1)), Module.finrank ℝ W = m ∧
      Module.finrank ℝ W.orthogonal = 1 := by
  have : Fact (Module.finrank ℝ (Spatial (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hv : (EuclideanSpace.single (Fin.last m) (1 : ℝ) : Spatial (m + 1)) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x : Spatial (m + 1) => x (Fin.last m)) h0
    simp at h1
  obtain ⟨W, hWdef⟩ : ∃ W : Submodule ℝ (Spatial (m + 1)), W = (Submodule.span ℝ
      {(EuclideanSpace.single (Fin.last m) (1 : ℝ) : Spatial (m + 1))}).orthogonal := ⟨_, rfl⟩
  have hW : Module.finrank ℝ W = m := by
    rw [hWdef]
    exact Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := m) hv
  refine ⟨W, hW, ?_⟩
  have hsum := subspace_finrank_add_normal W
  rw [hW] at hsum
  exact Nat.add_left_cancel hsum

/-- **`q-affinebmo` on the standard base** (`d1e_standard_affineBMO`): the type
`d1e_StandardAffineBMOStatement`. -/
theorem d1e_standard_affineBMO_proof : d1e_StandardAffineBMOStatement := by
  intro m
  obtain ⟨W, hW, hWo⟩ := d1ebmo_exists_codimOne m
  exact d1ebmo_of_subspace W ⟨0, by rw [hWo]; exact Nat.one_pos⟩ m hW

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
