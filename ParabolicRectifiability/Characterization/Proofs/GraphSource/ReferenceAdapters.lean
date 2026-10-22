import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceAdapterComponents
import ParabolicRectifiability.Characterization.Proofs.GraphSource.SquareFinitenessInputs

/-! # Reference adapters for graph images

The reference adapters assemble typed references from vertical and horizontal graphs; they
rest on the component estimates `b2_whitney_plateau_completion`, `b2_horizontal_chart`,
`b2_halfTime_affine_combination`, … and on the input `b2_input_reference_estimates`.

* `b2_vertical_graph_reference : VerticalGraphReferenceStatement`. The vertical adapter is
  assembled here: in
  the orthonormal coordinates of `subspaceParabolicIsometry W` the chart
  `F(p) = a + ι(p)₁ + G(ι p)` has, in every ambient coordinate `α`, exactly the form
  `c + ℓ(u) + Λ(G ∘ subspaceFourierToParabolic W)` read through `fourierToParabolic`, so the
  vector representation `RepresentsGeneralHalfTimeDerivative W G g` on `W × ℝ` gives the
  scalar `RepresentsStandardHalfTimeDerivative` on `Space (dim W)` required by
  `HasCoordinateHalfTimeBMOBound` (`b2_chart_coordinate_representation`). The constant is
  `L = 1 + ε`.
* `b2_horizontal_graph_reference : HorizontalGraphReferenceStatement`, from the spatial chart,
  the Whitney plateau completion and the trace-in-support fact.
* `b2_reference_adr_square`: every typed `L`-reference is a closed ADR carrier of the
  source-transfer appendix with constants depending on `(n, k, L)`, and its own-type square
  `S^1_{σ,T}` is finite `σ`-a.e. (from `ReferenceEstimatesStatement`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.QuantitativeCharacterization

/-! ## Coordinates of the vertical chart -/

/-- The inverse orthonormal isometry of the vertical base, read through the ordinary
coordinates of `Space (dim W)`, is the Fourier-coordinate map of the base. -/
theorem b2_isometry_symm_fourierToParabolic {n : ℕ} (W : Submodule ℝ (Spatial n))
    (x : FourierSpace (Module.finrank ℝ W)) :
    (subspaceParabolicIsometry W).symm (fourierToParabolic (Module.finrank ℝ W) x) =
      subspaceFourierToParabolic W x := by
  rw [subspaceParabolicIsometry_symm_apply, fourierToParabolic_apply,
    subspaceFourierToParabolic_apply]
  rfl

/-- A continuous linear functional of a normal vector is the corresponding combination of
its orthonormal normal coordinates. -/
theorem b2_normal_functional_sum {n : ℕ} (W : Submodule ℝ (Spatial n))
    (Λ : W.orthogonal →L[ℝ] ℝ) (v : W.orthogonal) :
    Λ v = ∑ i, Λ ((stdOrthonormalBasis ℝ W.orthogonal) i) * normalCoordinates W v i := by
  calc Λ v = Λ (∑ i, (stdOrthonormalBasis ℝ W.orthogonal).repr v i •
        (stdOrthonormalBasis ℝ W.orthogonal) i) := by
          rw [(stdOrthonormalBasis ℝ W.orthogonal).sum_repr v]
    _ = ∑ i, Λ ((stdOrthonormalBasis ℝ W.orthogonal) i) * normalCoordinates W v i := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, smul_eq_mul]
          exact mul_comm _ _

/-- The vector representation on `W × ℝ` gives the scalar representation of
`c + ℓ(u) + Λ(G ∘ subspaceFourierToParabolic W)` by `Λ(g ∘ subspaceFourierToParabolic W)`,
through `b2_halfTime_affine_combination` and the orthonormal expansion of
`Λ`. -/
theorem b2_vertical_coordinate_representation {n : ℕ} (W : Submodule ℝ (Spatial n))
    (Gf g : SubspaceSpace W → W.orthogonal) (hRep : RepresentsGeneralHalfTimeDerivative W Gf g)
    (c : ℝ) (ℓ : Spatial (Module.finrank ℝ W) →L[ℝ] ℝ) (Λ : W.orthogonal →L[ℝ] ℝ) :
    RepresentsHomogeneousHalfTimeDerivative
      (fun x => c + ℓ (WithLp.ofLp x).1 + Λ (Gf (subspaceFourierToParabolic W x)))
      (fun x => Λ (g (subspaceFourierToParabolic W x))) := by
  have h := b2_halfTime_affine_combination (Module.finrank ℝ W)
    (Module.finrank ℝ W.orthogonal) (fun i => normalFourierComponent W Gf i)
    (fun i => normalFourierComponent W g i) hRep c ℓ
    (fun i => Λ ((stdOrthonormalBasis ℝ W.orthogonal) i))
  have e1 : (fun x => c + ℓ (WithLp.ofLp x).1 + Λ (Gf (subspaceFourierToParabolic W x))) =
      (fun x => c + ℓ (WithLp.ofLp x).1 + ∑ i, Λ ((stdOrthonormalBasis ℝ W.orthogonal) i) *
        normalFourierComponent W Gf i x) := by
    funext x
    rw [b2_normal_functional_sum W Λ (Gf (subspaceFourierToParabolic W x))]
    rfl
  have e2 : (fun x => Λ (g (subspaceFourierToParabolic W x))) =
      (fun x => ∑ i, Λ ((stdOrthonormalBasis ℝ W.orthogonal) i) *
        normalFourierComponent W g i x) := by
    funext x
    rw [b2_normal_functional_sum W Λ (g (subspaceFourierToParabolic W x))]
    rfl
  rw [e1, e2]
  exact h

/-- **Representation match.** Every ambient coordinate of the vertical chart
`F(p) = a + ι(p)₁ + G(ι p)` has its half-time derivative represented, on the standard base
`Space (dim W)`, by the same coordinate of `g ∘ ι`, whenever `g` represents the derivative of
`G` on `W × ℝ` in the vector sense. -/
theorem b2_chart_coordinate_representation {n : ℕ} (W : Submodule ℝ (Spatial n))
    (a : Spatial n) (Gf g : SubspaceSpace W → W.orthogonal)
    (hRep : RepresentsGeneralHalfTimeDerivative W Gf g) (α : Fin n) :
    RepresentsStandardHalfTimeDerivative (Module.finrank ℝ W)
      (fun p => (a + (((subspaceParabolicIsometry W).symm p).1 : Spatial n) +
        (Gf ((subspaceParabolicIsometry W).symm p) : Spatial n)) α)
      (fun p => ((g ((subspaceParabolicIsometry W).symm p) : W.orthogonal) : Spatial n) α) := by
  have h := b2_vertical_coordinate_representation W Gf g hRep (a α)
    ((EuclideanSpace.proj α : Spatial n →L[ℝ] ℝ).comp (W.subtypeL.comp
      ((subspaceCoordinates W).symm.toContinuousLinearEquiv :
        Spatial (Module.finrank ℝ W) →L[ℝ] W)))
    ((EuclideanSpace.proj α : Spatial n →L[ℝ] ℝ).comp W.orthogonal.subtypeL)
  unfold RepresentsStandardHalfTimeDerivative
  convert h using 1 <;>
    · funext x
      rfl

/-- The image of the vertical chart is the graph image. -/
theorem b2_range_verticalChart {n : ℕ} (W : Submodule ℝ (Spatial n)) (a : Spatial n)
    (Gf : SubspaceSpace W → W.orthogonal) :
    Set.range (fun p : Space (Module.finrank ℝ W) =>
      ((a + (((subspaceParabolicIsometry W).symm p).1 : Spatial n) +
        (Gf ((subspaceParabolicIsometry W).symm p) : Spatial n), p.2) : Space n)) =
    Set.range (fun q : SubspaceSpace W =>
      ((a + (q.1 : Spatial n) + (Gf q : Spatial n), q.2) : Space n)) := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(subspaceParabolicIsometry W).symm p, rfl⟩
  · rintro ⟨q, rfl⟩
    refine ⟨subspaceParabolicIsometry W q, ?_⟩
    simp only [IsometryEquiv.symm_apply_apply]
    rfl

/-- Assembly of a vertical reference from a time-preserving chart with the bi-Lipschitz,
coordinate BMO and coordinate representation properties. -/
theorem b2_verticalReference_mk {n k m : ℕ} (hk : k < n + 2) (hrank : m + 2 = k)
    (F : Space m → Spatial n) (f : Fin n → Space m → ℝ) (K B L : ℝ)
    (hbil : ∀ p q : Space m, dist p q ≤ dist ((F p, p.2) : Space n) (F q, q.2) ∧
      dist ((F p, p.2) : Space n) (F q, q.2) ≤ (1 + K) * dist p q)
    (hK0 : 0 ≤ K) (hKL : 1 + K ≤ L) (hBL : B ≤ L)
    (hbmo : ∀ α, HasStandardParabolicBMOBound m (f α) B)
    (hrep : ∀ α, RepresentsStandardHalfTimeDerivative m (fun z => F z α) (f α)) :
    ∃ V : VerticalReference n k L,
      Set.range V.map = Set.range (fun p : Space m => ((F p, p.2) : Space n)) := by
  refine ⟨{ spatialRank := m
            rank_eq := hrank
            lt_ambient := hk
            spatialMap := F
            bilipschitz := fun p q => ⟨?_, ?_⟩
            coordinate_bmo := fun α => ?_ }, rfl⟩
  · exact (hbil p q).1.trans (le_mul_of_one_le_left dist_nonneg (by linarith))
  · exact (hbil p q).2.trans (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
  · refine ⟨⟨⟨1 + K, by linarith⟩, ?_⟩, f α, ?_, hrep α⟩
    · refine LipschitzWith.of_dist_le_mul fun p q => ?_
      calc dist (F p α) (F q α) ≤ dist (F p) (F q) := PiLp.dist_apply_le (F p) (F q) α
        _ ≤ dist ((F p, p.2) : Space n) (F q, q.2) := by
            rw [Prod.dist_eq]
            exact le_max_left _ _
        _ ≤ (1 + K) * dist p q := (hbil p q).2
    · exact ⟨(hbmo α).1.trans hBL, (hbmo α).2.1, fun p r hr => ((hbmo α).2.2 p r hr).trans hBL⟩

/-! ## The two adapters -/

/-- **Vertical adapter.** `L = 1 + ε`. -/
theorem b2_vertical_graph_reference : VerticalGraphReferenceStatement := by
  intro n k hk ε G
  obtain ⟨g, K, B, hLip, hBMO, hRep, hKB⟩ := G.regular
  have hK0 : (0 : ℝ) ≤ K := NNReal.coe_nonneg K
  have hB0 : (0 : ℝ) ≤ B := NNReal.coe_nonneg B
  obtain ⟨V, hV⟩ := b2_verticalReference_mk (L := 1 + ε) hk G.rank_eq
    (fun p => G.offset + (((subspaceParabolicIsometry G.direction).symm p).1 : Spatial n) +
      (G.function ((subspaceParabolicIsometry G.direction).symm p) : Spatial n))
    (fun α p => ((g ((subspaceParabolicIsometry G.direction).symm p) :
      G.direction.orthogonal) : Spatial n) α)
    (K : ℝ) (B : ℝ)
    (b2_vertical_chart_bilipschitz n G.direction G.offset G.function K hLip)
    hK0 (by linarith) (by linarith)
    (b2_vertical_coordinate_bmo n G.direction g B hBMO)
    (b2_chart_coordinate_representation G.direction G.offset G.function g hRep)
  refine ⟨V, ?_⟩
  show Set.range V.map = Set.range G.map
  rw [hV]
  exact b2_range_verticalChart G.direction G.offset G.function

/-- **Horizontal adapter.** -/
theorem b2_horizontal_graph_reference : HorizontalGraphReferenceStatement := by
  intro n k hk ε
  obtain ⟨L, hL, hchart⟩ := b2_horizontal_chart n k ε
  refine ⟨L, hL, fun G hne hcpt => ?_⟩
  obtain ⟨F, D, τ, hbil, htr, hDne, hDc, hsub⟩ := hchart G
  have hkn : k ≤ n := by
    have h := Submodule.finrank_le G.direction
    rw [G.rank_eq, finrank_euclideanSpace_fin] at h
    exact h
  obtain ⟨H, hF, hD, hτ⟩ :=
    b2_whitney_plateau_completion n k hk hkn L F hbil D (hDne hne) (hDc hcpt) τ htr
  refine ⟨H, fun z hz => ?_⟩
  obtain ⟨u, hu, rfl⟩ := hsub hz
  have huH : u ∈ H.domain := by rw [hD]; exact hu
  have hmem := b2_horizontalReference_map_mem_carrier n k L H u huH
  have hmap : H.map u = point (F u) (τ u) := by
    show point (H.spatialMap u) (H.height u) = point (F u) (τ u)
    rw [hF, hτ u hu]
  rw [hmap] at hmem
  exact hmem

/-! ## References as ADR carriers with finite own square -/

/-- Every typed `L`-reference is a closed ADR carrier (`IsADRCarrier`) with constants
depending only on `(n, k, L)`, and its own-type square `S^1_{σ,T}` is finite `σ`-a.e.
Input: `ReferenceEstimatesStatement`. -/
theorem b2_reference_adr_square :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ L : ℝ, 1 ≤ L →
    ∃ c C : ℝ, ∀ ρ : Reference n k L,
      IsADRCarrier k c C ρ.carrier ρ.measure ∧
        ∀ᵐ z ∂ρ.measure, squareEnergy ρ.measure k ρ.kind 1 z < ⊤ := by
  intro n hn k hk hkn L hL
  obtain ⟨A, hA, C, -, hest⟩ := b2_input_reference_estimates n hn k hk hkn L hL
  refine ⟨A⁻¹, A, fun ρ => ?_⟩
  obtain ⟨hadr, hen, -⟩ := hest ρ
  obtain ⟨hsupp, hne⟩ := b2_reference_support_carrier n k L ρ
  have hcar : IsADRCarrier k A⁻¹ A ρ.measure.support ρ.measure :=
    b2_isADRCarrier_of_isADR n k A ρ.measure (by omega) (by linarith)
      (by rw [hsupp]; exact hne) hadr
  rw [hsupp] at hcar
  exact ⟨hcar, b2_ae_squareEnergy_lt_top_of_carleson n k ρ.kind ρ.carrier ρ.measure
    hcar.finiteOnCompacts hne (lt_of_le_of_lt hen ENNReal.ofReal_lt_top)⟩

end ParabolicRectifiability.Characterization
