import ParabolicRectifiability.Decomposition.Local
import ParabolicRectifiability.Decomposition.SourceAssembly

/-! # Finite source assembly and the positive-threshold branch

Finite source assembly combines compact typed pieces, metric-content bounds
and packing estimates while retaining the original exceptional-source loss `Γ`.
The positive-threshold theorem then supplies these inputs from the local
decompositions; the main decomposition theorem joins this branch to the zero-threshold case.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ParabolicRectifiability

/-- Assemble restrictions to `region i ∩ A_T i`, not restrictions to the
compact approximants alone. Finite unions preserve all metric estimates;
finite packing implies countable packing by finite partial sums.
The only loss outside the localized good sources is the original `Γ`. -/
theorem assemble_compact_sources {n k N : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (hN : 0 < N) (T : FamilyKind) (μ : Measure (Space n))
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (M Γ Cl Cm Cp : ℝ) (hM : 0 ≤ M) (hΓ : 0 ≤ Γ)
    (hCl : 0 < Cl) (hCm : 0 < Cm) (hCp : 0 < Cp)
    (hbad : μ (Metric.ball (point 0 0) 1 ∩
      {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ)
    (S : GoodSourceLocalization μ k T M N)
    (K : Fin S.count → Set (Space n))
    (pieces : ∀ i, CompactTypedPieces (μ.restrict (S.region i)) k T M Cl (K i))
    (hmetric : ∀ i, HasMetricContentBounds k Cm (K i))
    (hpacking : ∀ i, HasFiniteBallPacking k Cp (K i)) :
    HasFamilyDecomposition k T ((N : ℝ) * (Cl + Cm + Cp)) M Γ μ := by
  exact familyDecomposition_of_compactSources hk hkn hN T μ hμ hreg M Γ Cl Cm Cp hM hΓ
    hCl hCm hCp hbad S K pieces hmetric hpacking

/-- The positive-threshold, positive-codimension branch. The dimensional
constant is fixed before `k`, the testing family, and the source. -/
theorem positive_threshold_family_decomposition (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k < n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 < M → 0 ≤ Γ →
      μ (Metric.ball (point 0 0) 1 ∩
        {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ →
      HasFamilyDecomposition k T C M Γ μ := by
  classical
  obtain ⟨N, hN, hloc⟩ := exists_good_source_localization n hn
  obtain ⟨Cg, hCg, hgeo⟩ := exists_geometric_extraction n hn
  obtain ⟨Cd, hCd, hdensity⟩ := exists_density_refinement n hn
  obtain ⟨Cp, hCp, hpack⟩ := exists_finite_ball_packing_constant n hn
  refine ⟨(N : ℝ) * ((Cg + Cd + 1) + Cd + Cp), by positivity, ?_⟩
  intro k hk hkn T hT μ hμ hreg M Γ hM hΓ hbad
  let S := Classical.choice (hloc k hk hkn.le T hT μ hμ hreg M hM.le)
  let G : ∀ i : Fin S.count, GeometricExtraction (μ.restrict (S.region i)) k T M Cg :=
    fun i => Classical.choice (hgeo k hk hkn T hT _ (S.finite i)
      (S.innerRegular i) (S.center i) (S.support_small i) M hM (S.energy i))
  let D : ∀ i : Fin S.count,
      DensityRefinement (μ.restrict (S.region i)) k M Cd (G i).carrier :=
    fun i => Classical.choice (hdensity k hk hkn T hT _ (S.finite i)
      (S.innerRegular i) (S.center i) (S.support_small i) M hM (S.energy i)
      (G i).carrier (G i).compact (G i).subset_support)
  let A : ∀ i : Fin S.count,
      CompactTypedPieces (μ.restrict (S.region i)) k T M (Cg + Cd + 1) (D i).set :=
    fun i => Classical.choice (exists_compact_typed_pieces hk hkn T hT _
      (S.finite i) (S.innerRegular i) M Cg Cd hM hCg hCd (G i) (D i)
      (fun j ε hε => horizontal_core_graph_cover ((G i).horizontal_certificate j) ε hε)
      (fun j ε hε => vertical_core_graph_cover ((G i).vertical_certificate j) ε hε))
  apply assemble_compact_sources hk hkn.le hN T μ hμ hreg M Γ
    (Cg + Cd + 1) Cd Cp hM.le hΓ (by positivity) hCd hCp hbad S
    (fun i => (D i).set) A (fun i => (D i).content)
  intro i
  exact hpack k hk hkn T hT _ (S.finite i) (S.innerRegular i)
    (S.center i) (S.support_small i) M hM (S.energy i)
    (G i).carrier (G i).compact (G i).subset_support (D i).set (D i).subset
    (D i).lower_mass

end ParabolicRectifiability
