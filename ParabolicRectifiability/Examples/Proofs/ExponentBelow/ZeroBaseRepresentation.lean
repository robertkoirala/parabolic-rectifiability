import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements

/-! # Zero-base representation

The scalar representation transports to the zero-base vector representation because each normal
coordinate of the lifted function is a fixed scalar multiple of its scalar time profile. The
representation predicate is homogeneous in that scalar, and `finrank_bot` identifies the base's
Fourier coordinates with `FourierSpace 0`.
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ContDiff

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative

/-- Scaling both entries by a fixed real scalar preserves scalar representation. -/
private theorem e2_representsHomogeneous_smul {m : ℕ} (c : ℝ)
    {G g : FourierSpace m → ℝ}
    (h : RepresentsHomogeneousHalfTimeDerivative G g) :
    RepresentsHomogeneousHalfTimeDerivative (fun x => c * G x) (fun x => c * g x) := by
  have hsmul : LocallyIntegrable (c • g) volume := h.1.smul c
  have hfun : (c • g) = fun x => c * g x := by
    funext x
    simp [smul_eq_mul]
  refine ⟨(by rw [← hfun]; exact hsmul), ?_⟩
  intro φ hφ hc hzero
  obtain ⟨hinner, hbracket, hlim⟩ := h.2 φ hφ hc hzero
  let ψ := realCompactTest φ hφ hc
  have hintegrand (t : ℝ) (u : Spatial m) :
      halfTimeSpatialIntegrand (fun x => c * G x) ψ t u =
        (c : ℂ) * halfTimeSpatialIntegrand G ψ t u := by
    simp [halfTimeSpatialIntegrand, mul_assoc]
  have hbracket_eq (t : ℝ) :
      halfTimeSpatialBracket (fun x => c * G x) ψ t =
        (c : ℂ) * halfTimeSpatialBracket G ψ t := by
    simp only [halfTimeSpatialBracket, hintegrand]
    rw [integral_const_mul]
  have hwindow_eq (R : ℝ) :
      halfTimeWindowPairing (fun x => c * G x) ψ R =
        (c : ℂ) * halfTimeWindowPairing G ψ R := by
    simp only [halfTimeWindowPairing, hbracket_eq]
    rw [integral_const_mul]
  have hwindow_eq' (R : ℝ) :
      halfTimeWindowPairing (fun x => c * G x) (realCompactTest φ hφ hc) R =
        (c : ℂ) * halfTimeWindowPairing G (realCompactTest φ hφ hc) R := by
    simpa only [ψ] using hwindow_eq R
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hinner] with t ht
    have hfun : halfTimeSpatialIntegrand (fun x => c * G x) ψ t =
        fun u => (c : ℂ) * halfTimeSpatialIntegrand G ψ t u := by
      funext u
      exact hintegrand t u
    rw [hfun]
    exact ht.const_mul _
  · intro R
    have hfun : halfTimeSpatialBracket (fun x => c * G x) ψ =
        fun t => (c : ℂ) * halfTimeSpatialBracket G ψ t := by
      funext t
      exact hbracket_eq t
    rw [hfun]
    exact Integrable.const_mul (hbracket R) _
  · have hright :
        (∫ x, ((c * g x : ℝ) : ℂ) * (φ x : ℂ)) =
          (c : ℂ) * ∫ x, (g x : ℂ) * (φ x : ℂ) := by
      calc
        _ = ∫ x, (c : ℂ) * ((g x : ℂ) * (φ x : ℂ)) := by
          apply integral_congr_ae
          filter_upwards with x
          push_cast
          ring
        _ = _ := integral_const_mul _ _
    have hwindow_fun :
        (fun R => halfTimeWindowPairing (fun x => c * G x) (realCompactTest φ hφ hc) R) =
          fun R => (c : ℂ) * halfTimeWindowPairing G (realCompactTest φ hφ hc) R :=
      funext hwindow_eq'
    change Tendsto
      (fun R => halfTimeWindowPairing (fun x => c * G x) (realCompactTest φ hφ hc) R)
      atTop (𝓝 (∫ x, ((c * g x : ℝ) : ℂ) * (φ x : ℂ)))
    rw [hwindow_fun, hright]
    exact hlim.const_mul (c : ℂ)

/-- The canonical unit normal vector above the zero spatial base. -/
private def e2_zeroBaseUnit : zeroDirectionᗮ :=
  ⟨(EuclideanSpace.single 0 (1 : ℝ) : Spatial 1), by simp [zeroDirection]⟩

/-- The zero-base lift is linear in its real value, including in subtype coordinates. -/
private theorem e2_zeroBaseVector_smul (a : ℝ) :
    (⟨(EuclideanSpace.single 0 a : Spatial 1), by simp [zeroDirection]⟩ : zeroDirectionᗮ) =
      a • e2_zeroBaseUnit := by
  apply Subtype.ext
  change (EuclideanSpace.single 0 a : Spatial 1) =
    a • (EuclideanSpace.single 0 (1 : ℝ) : Spatial 1)
  ext j
  fin_cases j
  simp [EuclideanSpace.single]

/-- Each normal coordinate of a zero-base lift is one fixed scalar multiple of its time profile. -/
private theorem e2_normalComponent_zeroBaseLift (F : ℝ → ℝ)
    (i : Fin (Module.finrank ℝ zeroDirectionᗮ)) :
    normalFourierComponent zeroDirection (zeroBaseLift F) i =
      fun x : FourierSpace (Module.finrank ℝ zeroDirection) =>
        (normalCoordinates zeroDirection e2_zeroBaseUnit i) *
          F (timeCoordinate (Module.finrank ℝ zeroDirection) x) := by
  funext x
  have htime :
      (Metric.Snowflaking.toSnowflaking (WithLp.ofLp x).2 : Time).val = (WithLp.ofLp x).2 := rfl
  simp only [normalFourierComponent, zeroBaseLift, subspaceFourierToParabolic_apply,
    timeCoordinate_apply, htime]
  rw [e2_zeroBaseVector_smul]
  rw [(normalCoordinates zeroDirection).map_smul]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- The scalar representation on `FourierSpace 0` gives the normal-vector
representation on the zero vertical base. -/
theorem e2_zeroBase_representation_proof : E2ZeroBaseRepresentationStatement := by
  intro F g h
  have hdim : Module.finrank ℝ zeroDirection = 0 := by
    exact finrank_bot ℝ (Spatial 1)
  have hscalar :
      RepresentsHomogeneousHalfTimeDerivative
        (fun x : FourierSpace (Module.finrank ℝ zeroDirection) =>
          F (timeCoordinate (Module.finrank ℝ zeroDirection) x))
        (fun x => g (timeCoordinate (Module.finrank ℝ zeroDirection) x)) := by
    rw [hdim]
    exact h
  unfold RepresentsGeneralHalfTimeDerivative
  intro i
  rw [e2_normalComponent_zeroBaseLift F i, e2_normalComponent_zeroBaseLift g i]
  exact e2_representsHomogeneous_smul
    (normalCoordinates zeroDirection e2_zeroBaseUnit i) hscalar

end ParabolicRectifiability.Examples
