import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Measure.ScaleEnergy
import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.HorizontalClosedExtension

/-! # Compact exhaustion of a horizontal subset graph

Proves `b2_horizontal_compact_cover_proof` (the statement of `b2_horizontal_compact_cover`):
every horizontal subset graph is covered, up to an `H_P^k`-null set, by countably many
horizontal graphs of the same slope bound with nonempty compact domains.

Proof. The closed-domain envelope
`Foundations.fgenv_horizontal_closed_extension_proof : HorizontalClosedEnvelopeStatement`
gives `G'` of the same slope bound with `G.image ⊆ G'.image`
and `IsClosed G'.domain`. For each `N`, `K_N = G'.domain ∩ B̄(0, N+1)` is compact (closed and
bounded in the finite-dimensional `G'.direction`); restrict `G'` to `K_N` (same direction,
offset and slope bound) and index by `J = {N | K_N nonempty}`. Every point of `G'.image` lies
over some `u` with `‖u‖ ≤ N`, so `G.image ⊆ ⋃ (Gc N).image`: the remainder is empty and its
`H_P^k` measure is `0`. No Lusin–Souslin and no inner regularity are used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- The restriction of a horizontal graph to a subset `K` of its domain: same direction, rank,
offset and slope bound; normal and time maps restricted. -/
def b2hcomp_restrict {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) (K : Set G.direction)
    (hK : K ⊆ G.domain) : HorizontalGraph n k ε where
  direction := G.direction
  rank_eq := G.rank_eq
  domain := K
  offset := G.offset
  normal := fun u => G.normal ⟨u.1, hK u.2⟩
  time := fun u => G.time ⟨u.1, hK u.2⟩
  small_slope := fun u v => G.small_slope ⟨u.1, hK u.2⟩ ⟨v.1, hK v.2⟩

/-- A graph point over a domain point `u ∈ K` lies in the image of the restriction to `K`. -/
theorem b2hcomp_mem_restrict_image {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε)
    (K : Set G.direction) (hK : K ⊆ G.domain) (u : G.domain) (hu : u.1 ∈ K) :
    point (G.offset + (u.val : Spatial n) + (G.normal u : Spatial n)) (G.time u) ∈
      (b2hcomp_restrict G K hK).image :=
  mem_range.2 ⟨⟨u.1, hu⟩, rfl⟩

/-- The truncated domains `K_N = D ∩ B̄(0, N+1)` of a closed domain `D` are compact. -/
theorem b2hcomp_isCompact_trunc {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε)
    (hclosed : IsClosed G.domain) (N : ℕ) :
    IsCompact (G.domain ∩ Metric.closedBall (0 : G.direction) ((N : ℝ) + 1)) :=
  (isCompact_closedBall (0 : G.direction) _).inter_left hclosed

/-- Every domain point lies in some truncated domain `K_N`. -/
theorem b2hcomp_exists_trunc {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) (u : G.domain) :
    ∃ N : ℕ, u.1 ∈ G.domain ∩ Metric.closedBall (0 : G.direction) ((N : ℝ) + 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖(u.1 : G.direction)‖
  refine ⟨N, u.2, ?_⟩
  rw [mem_closedBall_zero_iff]
  linarith

/-- **Compact exhaustion** (the statement of `b2_horizontal_compact_cover`): every horizontal subset
graph of slope at most `ε` is covered, modulo `H_P^k`, by countably many horizontal graphs of
the same slope bound with nonempty compact domains. Here the remainder is in fact empty. -/
theorem b2_horizontal_compact_cover_proof :
    ∀ (n k : ℕ) (ε : ℝ) (G : HorizontalGraph n k ε),
      ∃ (J : Set ℕ) (Gc : J → HorizontalGraph n k ε),
        (∀ j, (Gc j).domain.Nonempty ∧ IsCompact (Gc j).domain) ∧
        hausdorffP n k (G.image \ ⋃ j, (Gc j).image) = 0 := by
  intro n k ε G
  obtain ⟨G', hsub, hclosed⟩ := fgenv_horizontal_closed_extension_proof n k ε G
  have hK : ∀ N : ℕ,
      G'.domain ∩ Metric.closedBall (0 : G'.direction) ((N : ℝ) + 1) ⊆ G'.domain :=
    fun _ => inter_subset_left
  refine ⟨{N : ℕ | (G'.domain ∩ Metric.closedBall (0 : G'.direction) ((N : ℝ) + 1)).Nonempty},
    fun j => b2hcomp_restrict G' _ (hK j.1), ?_, ?_⟩
  · rintro ⟨N, hN⟩
    exact ⟨hN, b2hcomp_isCompact_trunc G' hclosed N⟩
  · have hempty : G.image \ ⋃ j : {N : ℕ | (G'.domain ∩
        Metric.closedBall (0 : G'.direction) ((N : ℝ) + 1)).Nonempty},
          (b2hcomp_restrict G' _ (hK j.1)).image = ∅ := by
      rw [sdiff_eq_empty]
      intro p hp
      obtain ⟨u, rfl⟩ := hsub hp
      obtain ⟨N, hu⟩ := b2hcomp_exists_trunc G' u
      exact mem_iUnion.2 ⟨⟨N, ⟨u.1, hu⟩⟩, b2hcomp_mem_restrict_image G' _ (hK N) u hu⟩
    rw [hempty, measure_empty]

end ParabolicRectifiability.Characterization
