import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.Statements

/-! # The closed-domain horizontal envelope

Proves the named statement `HorizontalClosedEnvelopeStatement`, the type of
`fgenv_horizontal_closed_extension`, as `fgenv_horizontal_closed_extension_proof`.

Construction. Given a horizontal graph `G` over `D ⊆ U` (`U = G.direction`), the envelope
keeps `direction`, `rank_eq` and `offset`, takes the domain `closure D` (closure in `U`), and
extends the normal map `g` and the time map `h` along the dense uniform inclusion
`D → closure D` (`IsDenseInducing.extend`). The slope bound gives
`‖g u - g v‖ ≤ |ε| ‖u - v‖` and `|h u - h v| ≤ (|ε| ‖u - v‖)²`, so both maps are uniformly
continuous with complete targets. The exact slope inequality with the original `ε` (not `|ε|`)
is a closed condition on `closure D × closure D` that holds on the dense image of `D × D`, hence
everywhere. No case split on the sign of `ε` is needed: for `ε < 0` the same argument applies
(the domain then has at most one point). The original graph point over `u ∈ D` is the
envelope point over the image of `u` in `closure D`.
-/

noncomputable section

open Set Filter Topology

namespace ParabolicRectifiability.Foundations

/-- The distance of two domain points is the spatial distance of their coordinates. -/
theorem bf1genv1_dist_domain {n : ℕ} {S : Submodule ℝ (Spatial n)} {D : Set S} (u v : D) :
    dist u v = ‖((u.val : S) : Spatial n) - ((v.val : S) : Spatial n)‖ := by
  rw [Subtype.dist_eq, dist_eq_norm]
  rfl

/-- The normal map of a horizontal graph is `|ε|`-Lipschitz. -/
theorem bf1genv1_normal_lipschitz {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) :
    LipschitzWith (Real.toNNReal |ε|) G.normal :=
  LipschitzWith.of_dist_le' fun u v => by
    rw [dist_eq_norm, bf1genv1_dist_domain]
    exact (le_max_left _ _).trans ((G.small_slope u v).trans
      (mul_le_mul_of_nonneg_right (le_abs_self ε) (norm_nonneg _)))

/-- The quadratic modulus of the time map of a horizontal graph. -/
theorem bf1genv1_time_bound {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) (u v : G.domain) :
    |G.time u - G.time v| ≤
      (|ε| * ‖((u.val : G.direction) : Spatial n) - ((v.val : G.direction) : Spatial n)‖) ^ 2 := by
  have h1 : Real.sqrt |G.time u - G.time v| ≤
      |ε| * ‖((u.val : G.direction) : Spatial n) - ((v.val : G.direction) : Spatial n)‖ :=
    (le_max_right _ _).trans ((G.small_slope u v).trans
      (mul_le_mul_of_nonneg_right (le_abs_self ε) (norm_nonneg _)))
  calc |G.time u - G.time v| = Real.sqrt |G.time u - G.time v| ^ 2 :=
        (Real.sq_sqrt (abs_nonneg _)).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

/-- The time map of a horizontal graph is uniformly continuous. -/
theorem bf1genv1_time_uniformContinuous {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) :
    UniformContinuous G.time := by
  rw [Metric.uniformContinuous_iff]
  intro δ hδ
  refine ⟨Real.sqrt δ / (|ε| + 1),
    div_pos (Real.sqrt_pos.2 hδ) (by positivity), ?_⟩
  intro u v huv
  rw [Real.dist_eq]
  rw [bf1genv1_dist_domain] at huv
  have hd0 : 0 ≤ ‖((u.val : G.direction) : Spatial n) - ((v.val : G.direction) : Spatial n)‖ :=
    norm_nonneg _
  have hmul := (lt_div_iff₀ (by positivity : (0 : ℝ) < |ε| + 1)).1 huv
  have h2 : |ε| * ‖((u.val : G.direction) : Spatial n) - ((v.val : G.direction) : Spatial n)‖ <
      Real.sqrt δ := by
    have hring :
        ‖((u.val : G.direction) : Spatial n) - ((v.val : G.direction) : Spatial n)‖ * (|ε| + 1) =
          |ε| * ‖((u.val : G.direction) : Spatial n) - ((v.val : G.direction) : Spatial n)‖ +
            ‖((u.val : G.direction) : Spatial n) - ((v.val : G.direction) : Spatial n)‖ := by
      ring
    linarith
  calc |G.time u - G.time v|
      ≤ (|ε| * ‖((u.val : G.direction) : Spatial n) - ((v.val : G.direction) : Spatial n)‖) ^ 2 :=
        bf1genv1_time_bound G u v
    _ < Real.sqrt δ ^ 2 :=
        pow_lt_pow_left₀ h2 (mul_nonneg (abs_nonneg ε) hd0) two_ne_zero
    _ = δ := Real.sq_sqrt hδ.le

/-- The inclusion of the domain of `G` in its closure. -/
abbrev bf1genv1_incl {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) :
    G.domain → closure G.domain :=
  Set.inclusion subset_closure

theorem bf1genv1_incl_isUniformInducing {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) :
    IsUniformInducing (bf1genv1_incl G) :=
  (isUniformEmbedding_set_inclusion subset_closure).isUniformInducing

theorem bf1genv1_incl_denseRange {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) :
    DenseRange (bf1genv1_incl G) :=
  (denseRange_inclusion_iff subset_closure).2 subset_rfl

/-- The extension of the normal map to the closure of the domain. -/
def bf1genv1_normalExt {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) :
    closure G.domain → G.direction.orthogonal :=
  ((bf1genv1_incl_isUniformInducing G).isDenseInducing (bf1genv1_incl_denseRange G)).extend
    G.normal

/-- The extension of the time map to the closure of the domain. -/
def bf1genv1_timeExt {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) :
    closure G.domain → ℝ :=
  ((bf1genv1_incl_isUniformInducing G).isDenseInducing (bf1genv1_incl_denseRange G)).extend
    G.time

theorem bf1genv1_normalExt_incl {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) (u : G.domain) :
    bf1genv1_normalExt G (bf1genv1_incl G u) = G.normal u :=
  uniformly_extend_of_ind (bf1genv1_incl_isUniformInducing G) (bf1genv1_incl_denseRange G)
    (bf1genv1_normal_lipschitz G).uniformContinuous u

theorem bf1genv1_timeExt_incl {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) (u : G.domain) :
    bf1genv1_timeExt G (bf1genv1_incl G u) = G.time u :=
  uniformly_extend_of_ind (bf1genv1_incl_isUniformInducing G) (bf1genv1_incl_denseRange G)
    (bf1genv1_time_uniformContinuous G) u

theorem bf1genv1_normalExt_continuous {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) :
    Continuous (bf1genv1_normalExt G) :=
  (uniformContinuous_uniformly_extend (bf1genv1_incl_isUniformInducing G)
    (bf1genv1_incl_denseRange G) (bf1genv1_normal_lipschitz G).uniformContinuous).continuous

theorem bf1genv1_timeExt_continuous {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) :
    Continuous (bf1genv1_timeExt G) :=
  (uniformContinuous_uniformly_extend (bf1genv1_incl_isUniformInducing G)
    (bf1genv1_incl_denseRange G) (bf1genv1_time_uniformContinuous G)).continuous

/-- The exact slope bound (with the original `ε`) for the extended maps on the closure. -/
theorem bf1genv1_small_slope_ext {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε)
    (p q : closure G.domain) :
    max ‖bf1genv1_normalExt G p - bf1genv1_normalExt G q‖
        (Real.sqrt |bf1genv1_timeExt G p - bf1genv1_timeExt G q|) ≤
      ε * ‖((p.val : G.direction) : Spatial n) - ((q.val : G.direction) : Spatial n)‖ := by
  have hg := bf1genv1_normalExt_continuous G
  have hh := bf1genv1_timeExt_continuous G
  have hv : Continuous fun p : closure G.domain => ((p.val : G.direction) : Spatial n) :=
    continuous_subtype_val.comp continuous_subtype_val
  refine isClosed_property2 (bf1genv1_incl_denseRange G)
    (p := fun p q : closure G.domain =>
      max ‖bf1genv1_normalExt G p - bf1genv1_normalExt G q‖
          (Real.sqrt |bf1genv1_timeExt G p - bf1genv1_timeExt G q|) ≤
        ε * ‖((p.val : G.direction) : Spatial n) - ((q.val : G.direction) : Spatial n)‖)
    ?_ ?_ p q
  · exact isClosed_le
      (((hg.comp continuous_fst).sub (hg.comp continuous_snd)).norm.max
        (Real.continuous_sqrt.comp
          (continuous_abs.comp ((hh.comp continuous_fst).sub (hh.comp continuous_snd)))))
      (continuous_const.mul ((hv.comp continuous_fst).sub (hv.comp continuous_snd)).norm)
  · intro u v
    simp only [bf1genv1_normalExt_incl, bf1genv1_timeExt_incl]
    exact G.small_slope u v

/-- The closed-domain envelope of a horizontal graph: same direction, rank and offset, domain
`closure G.domain`, normal and time maps extended by uniform continuity. -/
def bf1genv1_envelope {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) : HorizontalGraph n k ε where
  direction := G.direction
  rank_eq := G.rank_eq
  domain := closure G.domain
  offset := G.offset
  normal := bf1genv1_normalExt G
  time := bf1genv1_timeExt G
  small_slope := bf1genv1_small_slope_ext G

/-- **The closed-domain horizontal envelope**: every horizontal graph of slope at most `ε` lies in a
horizontal graph of the same slope bound whose domain is closed. -/
theorem fgenv_horizontal_closed_extension_proof : HorizontalClosedEnvelopeStatement := by
  intro n k ε G
  refine ⟨bf1genv1_envelope G, ?_, isClosed_closure⟩
  rintro _ ⟨u, rfl⟩
  refine ⟨bf1genv1_incl G u, ?_⟩
  show point (G.offset + ((u.val : G.direction) : Spatial n) +
      (bf1genv1_normalExt G (bf1genv1_incl G u) : Spatial n))
      (bf1genv1_timeExt G (bf1genv1_incl G u)) = _
  rw [bf1genv1_normalExt_incl, bf1genv1_timeExt_incl]

end ParabolicRectifiability.Foundations
