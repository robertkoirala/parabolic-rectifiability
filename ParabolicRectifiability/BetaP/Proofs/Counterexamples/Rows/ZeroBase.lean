import ParabolicRectifiability.BetaP.Proofs.Counterexamples.RowStatements
import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Examples.Lacunary

/-! # A rank-zero graph carries the source (`c2_zeroBase_carried`)

One rank-zero full general regular vertical graph (direction `⊥`, offset `0`, function
`zeroBaseLift g`) has image exactly `{(g(t) e₁, t) : t ∈ ℝ}`; the empty horizontal family and
the single vertical graph then carry every measure concentrated on that set. -/

open MeasureTheory Set

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- Proof of `C2ZeroBaseCarriedStatement`. -/
theorem c2_zeroBase_carried_proof : C2ZeroBaseCarriedStatement := by
  intro g η hreg μ hμ
  let G : GeneralRegularVerticalGraph 1 2 η :=
    { vertical_dimension := le_rfl
      direction := Examples.zeroDirection
      rank_eq := by simp [Examples.zeroDirection]
      offset := 0
      function := Examples.zeroBaseLift g
      regular := hreg }
  have himage : G.image =
      Set.range fun t : ℝ => point (EuclideanSpace.single (0 : Fin 1) (g t)) t := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      have hp : ((p.1 : ↥Examples.zeroDirection) : Spatial 1) = 0 :=
        (Submodule.mem_bot ℝ).1 p.1.2
      refine ⟨p.2.val, ?_⟩
      simp [GeneralRegularVerticalGraph.map, G, hp, Examples.zeroBaseLift, point]
      rfl
    · rintro ⟨t, rfl⟩
      refine ⟨((0 : ↥Examples.zeroDirection), Metric.Snowflaking.toSnowflaking t), ?_⟩
      simp [GeneralRegularVerticalGraph.map, G, Examples.zeroBaseLift, point]
      rfl
  refine ⟨∅, {0}, fun i => 0, fun i => absurd i.2 (Set.notMem_empty _), fun _ => η,
    fun _ => G, ?_⟩
  have hU : ((⋃ i : (∅ : Set ℕ), (absurd i.2 (Set.notMem_empty _) :
      HorizontalGraph 1 2 0).image) ∪ ⋃ j : ({0} : Set ℕ), G.image) =
      Set.range fun t : ℝ => point (EuclideanSpace.single (0 : Fin 1) (g t)) t := by
    ext z
    simp [himage]
  rw [hU]
  exact hμ
