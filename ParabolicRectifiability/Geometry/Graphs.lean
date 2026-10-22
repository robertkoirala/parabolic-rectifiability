import ParabolicRectifiability.Analysis.ParabolicBMO
import ParabolicRectifiability.Metric.Hausdorff

/-! # The graph classes in the rectifiability theorem

Horizontal domains are arbitrary subsets of spatial subspaces. Vertical graphs
are full regular extensions. Covers are modulo Hausdorff outer measure zero;
the original source measure is not used to define their exceptional sets.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability

/-- A graph over an arbitrary subset of a spatial `k`-plane, with normal
and time maps satisfying `max ‖normal u-normal v‖ (sqrt |time u-time v|)
≤ ε * ‖u-v‖`. The domain may be disconnected or empty; no full-domain
extension of the time map is part of this structure. -/
structure HorizontalGraph (n k : ℕ) (ε : ℝ) where
  direction : Submodule ℝ (Spatial n)
  rank_eq : Module.finrank ℝ direction = k
  domain : Set direction
  offset : Spatial n
  normal : domain → direction.orthogonal
  time : domain → ℝ
  small_slope : ∀ u v : domain,
    max ‖normal u - normal v‖ (Real.sqrt |time u - time v|) ≤
      ε * ‖(u.val : Spatial n) - (v.val : Spatial n)‖

/-- Space-time image of the partial horizontal graph, including its spatial
offset, normal displacement and varying time coordinate. -/
def HorizontalGraph.image {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) : Set (Space n) :=
  Set.range fun u : G.domain =>
    point (G.offset + (u.val : Spatial n) + (G.normal u : Spatial n)) (G.time u)

/-- A full regular vertical graph. The guard prevents natural subtraction
from creating a vertical type in dimension one. The full-rank endpoint is
allowed and has zero-dimensional normal space. -/
structure RegularVerticalGraph (n k : ℕ) (ε : ℝ) where
  vertical_dimension : 2 ≤ k
  direction : Submodule ℝ (Spatial n)
  rank_eq : Module.finrank ℝ direction + 2 = k
  offset : Spatial n
  function : SubspaceSpace direction → direction.orthogonal
  regular : IsRegularVerticalFunction direction function ε

/-- Image of the full time-preserving graph over the intrinsic vertical
base; the offset and normal function affect only the spatial coordinate. -/
def RegularVerticalGraph.image {n k : ℕ} {ε : ℝ}
    (G : RegularVerticalGraph n k ε) : Set (Space n) :=
  Set.range fun p : SubspaceSpace G.direction =>
    (G.offset + (p.1 : Spatial n) + (G.function p : Spatial n), p.2)

/-- A countable horizontal cover with a Hausdorff-null exception. A subset of
the naturals permits both finite and empty families without padding graphs. -/
def HasHorizontalGraphCover {n : ℕ} (k : ℕ) (K : Set (Space n)) (ε : ℝ) : Prop :=
  ∃ (I : Set ℕ) (G : I → HorizontalGraph n k ε),
    hausdorffP n k (K \ ⋃ i, (G i).image) = 0

/-- A countable cover by full regular vertical graphs, using the same outer
Hausdorff-null convention, including for nonmeasurable graph images. -/
def HasRegularVerticalGraphCover {n : ℕ} (k : ℕ) (K : Set (Space n)) (ε : ℝ) : Prop :=
  ∃ (I : Set ℕ) (G : I → RegularVerticalGraph n k ε),
    hausdorffP n k (K \ ⋃ i, (G i).image) = 0

end ParabolicRectifiability
