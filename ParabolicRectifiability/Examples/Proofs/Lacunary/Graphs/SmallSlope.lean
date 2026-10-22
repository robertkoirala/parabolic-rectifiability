import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import Mathlib.Data.Fintype.EquivFin

/-! A finite cover is obtained from compactness in the ordinary time metric.
The half-radius balls have diameter less than the supplied local modulus scale,
so extension applies on each intersection with the whole closed interval. -/

noncomputable section
open Set Filter Topology
namespace ParabolicRectifiability.Examples
open ParabolicRectifiability.Foundations

/-- Local little half-Hölder control and full snowflake extension give an exact
finite small-slope cover, including both endpoints of the parameter interval. -/
theorem e2_lacunary_smallSlope_proof :
    E2LittleHolderStatement → E2SnowflakeExtensionStatement → LacunarySmallSlopeStatement := by
  classical
  intro hmod hext ε a N hε _hεmax hd ha η hη
  obtain ⟨h, hh, hlocal⟩ := hmod ε a N hε.le hd ha η hη
  have hhalf : 0 < h / 2 := half_pos hh
  obtain ⟨c, hc⟩ := (isCompact_Icc : IsCompact lacunaryInterval).elim_finite_subcover
    (fun x : ℝ => Metric.ball x (h / 2)) (fun _ => Metric.isOpen_ball)
    (by intro t _; exact mem_iUnion.mpr ⟨t, Metric.mem_ball_self hhalf⟩)
  have extend (x : ℝ) : ∃ G : OrdinaryVerticalGraph 1 2 η,
      lacunaryGraphMap ε a N '' (lacunaryInterval ∩ Metric.ball x (h / 2)) ⊆ G.image := by
    apply hext η hη (lacunaryInterval ∩ Metric.ball x (h / 2)) (lacunaryFunction ε a N)
    intro t ht s hs
    apply hlocal t s
    have ht' : dist t x < h / 2 := ht.2
    have hs' : dist x s < h / 2 := by simpa [dist_comm] using hs.2
    rw [← Real.dist_eq]
    exact (dist_triangle t x s).trans (by linarith)
  choose G hG using extend
  refine ⟨c.card, fun i => G (c.equivFin.symm i), ?_⟩
  rintro z ⟨t, ht, rfl⟩
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hc ht)
  obtain ⟨hxc, htx⟩ := mem_iUnion.mp hx
  refine mem_iUnion.mpr ⟨c.equivFin ⟨x, hxc⟩, ?_⟩
  simpa using hG x (mem_image_of_mem _ ⟨ht, htx⟩)

end ParabolicRectifiability.Examples
