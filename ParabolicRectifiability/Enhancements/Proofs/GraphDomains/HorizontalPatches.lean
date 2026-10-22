import ParabolicRectifiability.Foundations.GraphDomainCover
import ParabolicRectifiability.Metric.BaseVolume

/-! # Horizontal patch family: proof, with the shared patch helpers

Proof of `Enhancements.GraphDomainTree.horizontal_patches`, under the name
`horizontal_patches_proof`.

The first part holds helpers shared with `vertical_patches`:

* `gdb9_tsum_le_of_disjoint_charges`, `gdb9_tsum_subtype_le_of_disjoint_charges`: the
  disjoint-charge summation. Charges paid by pairwise
  disjoint measurable sets `S_i ⊆ A`, `c_i ≤ C μ(S_i)`, sum to at most `C μ(A)`, over any index
  type and any subset of it. `C = ⊤` is allowed.
* `gdb9_pairIndex`, `gdb9_pairEquiv`: the countable dependent reindexing of `Σ j : J, L j`
  (`J`, `L j` subsets of `ℕ`) by the codes `Nat.pair j l`, a subset of `ℕ`, with the transport
  of sums, unions and pairwise disjointness (`gdb9_tsum_pairIndex`, `gdb9_iUnion_pairIndex`,
  `gdb9_pairwise_pairIndex`), and `gdb9_pairwise_disjoint_sigma` (disjoint across fibres and
  within each fibre gives disjoint on the sigma type).
* `gdb9_measure_null_of_subset_union`: a set covered by a null set and countably many null
  sets is null.

The second part is the horizontal construction. Patches are `α = (j, l)`, coded
by `Nat.pair`, with centre `p_{j,l}` lifted into the actual domain of `G_j` (`hp`), radius
`ρ_α = 5 r_{j,l} ≤ δ`, and patch `Φ_j(E_j ∩ B(p, ρ_α))`. The paying set of `α` is
`S_α = Φ_j(E_j ∩ B(p, r_{j,l})) ⊆ F_j`, measurable by `hpatchm`. Half density and the lower
comparison give `ρ_α^k ≤ 2·5^k H_P^k(S_α)`; the ball bound and the upper comparison give
`λ(B_α) ≤ v ρ_α^k` and `H_P^k(Q_α) ≤ cU v ρ_α^k`, so `c_α ≤ 2·5^k(1+v+cU v) H_P^k(S_α)`. The
`S_α` are disjoint (disjoint balls and the injective graph map within `j`, disjoint traces
across `j`) and lie in `K`, and for `α ∈ I(q,R)` in `P(q,2R)`, by the `√2` distance bound
(`√2 r ≤ 5 r = ρ_α ≤ R`). Coverage: the uncovered part of `K` lies in `K \ ⋃ F_j` and the
images `Φ_j(E_j \ ⋃_l B(p_{j,l}, 5 r_{j,l}))`, which are null by `hup` (`cU · 0 = 0`, also for
`cU = ⊤`). No case split on `δ` is needed: `hr` makes every patch radius admissible, and for
`δ ≤ 0` the families `L j` are empty.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Enhancements.GraphDomainTree

open ParabolicRectifiability.Foundations

/-! ## Shared helpers (also used by `vertical_patches`) -/

section Shared

/-- **Disjoint-charge summation.** If each charge `c i` is
paid by a measurable set `S i ⊆ A`, `c i ≤ C μ(S i)`, and the `S i` are pairwise disjoint, then
`Σ_i c i ≤ C μ(A)`. Any index type; `C = ⊤` is allowed. -/
theorem gdb9_tsum_le_of_disjoint_charges {X ι : Type*} [MeasurableSpace X] (μ : Measure X)
    {c : ι → ℝ≥0∞} {S : ι → Set X} {A : Set X} {C : ℝ≥0∞}
    (hSm : ∀ i, MeasurableSet (S i)) (hSdisj : Pairwise fun i j => Disjoint (S i) (S j))
    (hSA : ∀ i, S i ⊆ A) (hc : ∀ i, c i ≤ C * μ (S i)) :
    ∑' i, c i ≤ C * μ A :=
  calc ∑' i, c i ≤ ∑' i, C * μ (S i) := ENNReal.tsum_le_tsum hc
    _ = C * ∑' i, μ (S i) := ENNReal.tsum_mul_left
    _ ≤ C * μ (⋃ i, S i) := by
        gcongr
        exact tsum_meas_le_meas_iUnion_of_disjoint μ hSm hSdisj
    _ ≤ C * μ A := by
        gcongr
        exact iUnion_subset hSA

/-- **Disjoint-charge summation over a subfamily** (the local form). The sets need to lie in `A`
only for the indices in `I`. -/
theorem gdb9_tsum_subtype_le_of_disjoint_charges {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (I : Set ι) {c : ι → ℝ≥0∞} {S : ι → Set X} {A : Set X} {C : ℝ≥0∞}
    (hSm : ∀ i, MeasurableSet (S i)) (hSdisj : Pairwise fun i j => Disjoint (S i) (S j))
    (hSA : ∀ i ∈ I, S i ⊆ A) (hc : ∀ i, c i ≤ C * μ (S i)) :
    ∑' i : I, c i ≤ C * μ A :=
  gdb9_tsum_le_of_disjoint_charges μ (S := fun i : I => S i) (fun i => hSm i)
    (hSdisj.comp_of_injective Subtype.val_injective) (fun i => hSA i i.2) (fun i => hc i)

/-- Pairwise disjointness on a sigma type: disjoint within each fibre, and contained in
pairwise disjoint sets indexed by the base. -/
theorem gdb9_pairwise_disjoint_sigma {ι Y : Type*} {κ : ι → Type*} {S : (Σ i, κ i) → Set Y}
    {T : ι → Set Y} (hST : ∀ x, S x ⊆ T x.1) (hT : Pairwise fun i j => Disjoint (T i) (T j))
    (hS : ∀ i, Pairwise fun l l' : κ i => Disjoint (S ⟨i, l⟩) (S ⟨i, l'⟩)) :
    Pairwise fun x y => Disjoint (S x) (S y) := by
  rintro ⟨i, l⟩ ⟨i', l'⟩ hne
  by_cases hi : i = i'
  · subst hi
    exact hS i fun hl => hne (by subst hl; rfl)
  · exact (hT hi).mono (hST _) (hST _)

/-- A set covered by a null set and countably many null sets is null. -/
theorem gdb9_measure_null_of_subset_union {Y κ : Type*} [MeasurableSpace Y] [Countable κ]
    (μ : Measure Y) {s t : Set Y} {N : κ → Set Y} (hsub : s ⊆ t ∪ ⋃ j, N j) (ht : μ t = 0)
    (hN : ∀ j, μ (N j) = 0) : μ s = 0 :=
  measure_mono_null hsub (measure_union_null ht (measure_iUnion_null hN))

/-! ### Countable dependent reindexing by `Nat.pair` -/

/-- The code `Nat.pair j l` of a pair `(j, l)` with `j ∈ J` and `l ∈ L j`. -/
def gdb9_pairCode (J : Set ℕ) (L : J → Set ℕ) (x : Σ j : J, L j) : ℕ :=
  Nat.pair (x.1 : ℕ) (x.2 : ℕ)

theorem gdb9_pairCode_injective (J : Set ℕ) (L : J → Set ℕ) :
    Function.Injective (gdb9_pairCode J L) := by
  intro x y h
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.1 h
  exact Sigma.subtype_ext (Subtype.ext h1) h2

/-- The patch index set: the codes `Nat.pair j l` (`j ∈ J`, `l ∈ L j`), a subset of `ℕ`. -/
def gdb9_pairIndex (J : Set ℕ) (L : J → Set ℕ) : Set ℕ :=
  Set.range (gdb9_pairCode J L)

/-- The dependent pairs `(j, l)` are in bijection with their codes. A sequence with repetitions
would not do: it can destroy pairwise disjointness. -/
def gdb9_pairEquiv (J : Set ℕ) (L : J → Set ℕ) : (Σ j : J, L j) ≃ gdb9_pairIndex J L :=
  Equiv.ofInjective _ (gdb9_pairCode_injective J L)

theorem gdb9_tsum_pairIndex {J : Set ℕ} {L : J → Set ℕ} (f : (Σ j : J, L j) → ℝ≥0∞) :
    ∑' α : gdb9_pairIndex J L, f ((gdb9_pairEquiv J L).symm α) = ∑' x, f x :=
  (gdb9_pairEquiv J L).symm.tsum_eq f

theorem gdb9_tsum_pairIndex_eq_tsum_tsum {J : Set ℕ} {L : J → Set ℕ}
    (f : (Σ j : J, L j) → ℝ≥0∞) :
    ∑' α : gdb9_pairIndex J L, f ((gdb9_pairEquiv J L).symm α) = ∑' j, ∑' l, f ⟨j, l⟩ := by
  rw [gdb9_tsum_pairIndex, ENNReal.tsum_sigma']

theorem gdb9_iUnion_pairIndex {Y : Type*} {J : Set ℕ} {L : J → Set ℕ}
    (f : (Σ j : J, L j) → Set Y) :
    ⋃ α : gdb9_pairIndex J L, f ((gdb9_pairEquiv J L).symm α) = ⋃ x, f x :=
  (gdb9_pairEquiv J L).symm.surjective.iUnion_comp f

theorem gdb9_pairwise_pairIndex {Y : Type*} {J : Set ℕ} {L : J → Set ℕ}
    {S : (Σ j : J, L j) → Set Y} (h : Pairwise fun x y => Disjoint (S x) (S y)) :
    Pairwise fun α β : gdb9_pairIndex J L =>
      Disjoint (S ((gdb9_pairEquiv J L).symm α)) (S ((gdb9_pairEquiv J L).symm β)) :=
  h.comp_of_injective (gdb9_pairEquiv J L).symm.injective

end Shared

/-! ## One horizontal graph -/

section OneGraph

variable {n k : ℕ} {ε : ℝ}

theorem gdb9_mem_horizontalPreimage {G : HorizontalGraph n k ε} {F : Set (Space n)}
    (u : G.domain) :
    (u : G.direction) ∈ horizontalPreimage G F ↔ horizontalGraphMap G u ∈ F :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨u.2, h⟩⟩

theorem gdb9_horizontalPreimage_subset_domain (G : HorizontalGraph n k ε) (F : Set (Space n)) :
    horizontalPreimage G F ⊆ G.domain :=
  fun _ h => Exists.fst h

theorem gdb9_val_image_preimage {G : HorizontalGraph n k ε} {A : Set G.direction}
    (hA : A ⊆ G.domain) :
    Subtype.val '' {u : G.domain | (u : G.direction) ∈ A} = A := by
  rw [show {u : G.domain | (u : G.direction) ∈ A} = Subtype.val ⁻¹' A from rfl,
    Subtype.image_preimage_coe, inter_eq_right.2 hA]

theorem gdb9_horizontalPatch_subset_trace (G : HorizontalGraph n k ε) (F : Set (Space n))
    (p : G.direction) (ρ : ℝ) : horizontalPatch G F p ρ ⊆ F := by
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨hE, -⟩ := hu
  exact (gdb9_mem_horizontalPreimage u).1 hE

theorem gdb9_measurableSet_horizontalPatch {G : HorizontalGraph n k ε} {F : Set (Space n)}
    (hpatchm : ∀ A : Set G.direction, MeasurableSet A →
      MeasurableSet (horizontalGraphMap G '' {u : G.domain | (u : G.direction) ∈ A}))
    (hEm : MeasurableSet (horizontalPreimage G F)) (p : G.direction) (ρ : ℝ) :
    MeasurableSet (horizontalPatch G F p ρ) :=
  hpatchm _ (hEm.inter measurableSet_ball)

theorem gdb9_horizontalGraphMap_injective {G : HorizontalGraph n k ε}
    (hlow : ∀ u w : G.domain, dist (u : G.direction) (w : G.direction) ≤
      dist (horizontalGraphMap G u) (horizontalGraphMap G w)) :
    Function.Injective (horizontalGraphMap G) := by
  intro u w h
  have hd := hlow u w
  rw [h, dist_self] at hd
  exact Subtype.ext (dist_le_zero.1 hd)

theorem gdb9_disjoint_horizontalPatch {G : HorizontalGraph n k ε} {F : Set (Space n)}
    (hinj : Function.Injective (horizontalGraphMap G)) {p p' : G.direction} {ρ ρ' : ℝ}
    (h : Disjoint (Metric.ball p ρ) (Metric.ball p' ρ')) :
    Disjoint (horizontalPatch G F p ρ) (horizontalPatch G F p' ρ') :=
  disjoint_image_of_injective hinj <|
    (h.preimage Subtype.val).mono (preimage_mono inter_subset_right)
      (preimage_mono inter_subset_right)

/-- **The single-patch charge:**
`ρ^k + λ(B(p,ρ)) + H_P^k(Φ(E ∩ B(p,ρ))) ≤ 2·5^k(1+v+cU v) H_P^k(Φ(E ∩ B(p,r)))` for
`ρ = 5r`, from half density, both comparisons and the ball bound. Valid for `cU = ⊤`. -/
theorem gdb9_charge_le {G : HorizontalGraph n k ε} {F : Set (Space n)} {v cU : ℝ≥0∞}
    (hv0 : v ≠ 0) (hvt : v ≠ ⊤)
    (hlow : ∀ A : Set G.domain, volume (Subtype.val '' A : Set G.direction) ≤
      v * hausdorffP n k (horizontalGraphMap G '' A))
    (hup : ∀ A : Set G.domain, hausdorffP n k (horizontalGraphMap G '' A) ≤
      cU * volume (Subtype.val '' A : Set G.direction))
    (hball : ∀ (p : G.direction) (r : ℝ), 0 < r →
      volume (Metric.ball p r) ≤ v * ENNReal.ofReal r ^ k)
    {p : G.direction} {r : ℝ} (hr : 0 < r)
    (hhalf : v * ENNReal.ofReal r ^ k ≤ 2 * volume (horizontalPreimage G F ∩ Metric.ball p r)) :
    ENNReal.ofReal (5 * r) ^ k + volume (Metric.ball p (5 * r)) +
        hausdorffP n k (horizontalPatch G F p (5 * r)) ≤
      2 * 5 ^ k * (1 + v + cU * v) * hausdorffP n k (horizontalPatch G F p r) := by
  have hsub : ∀ ρ, horizontalPreimage G F ∩ Metric.ball p ρ ⊆ G.domain :=
    fun ρ => inter_subset_left.trans (gdb9_horizontalPreimage_subset_domain G F)
  have hvolS : volume (horizontalPreimage G F ∩ Metric.ball p r) ≤
      v * hausdorffP n k (horizontalPatch G F p r) := by
    have h := hlow {u : G.domain | (u : G.direction) ∈ horizontalPreimage G F ∩ Metric.ball p r}
    rwa [gdb9_val_image_preimage (hsub r)] at h
  have ht : ENNReal.ofReal r ^ k ≤ 2 * hausdorffP n k (horizontalPatch G F p r) := by
    have h1 : v * ENNReal.ofReal r ^ k ≤ v * (2 * hausdorffP n k (horizontalPatch G F p r)) :=
      calc v * ENNReal.ofReal r ^ k
          ≤ 2 * volume (horizontalPreimage G F ∩ Metric.ball p r) := hhalf
        _ ≤ 2 * (v * hausdorffP n k (horizontalPatch G F p r)) := by gcongr
        _ = v * (2 * hausdorffP n k (horizontalPatch G F p r)) := mul_left_comm _ _ _
    exact (ENNReal.mul_le_mul_iff_right hv0 hvt).1 h1
  have h5 : ENNReal.ofReal (5 * r) ^ k = 5 ^ k * ENNReal.ofReal r ^ k := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_pow]
  have hB : volume (Metric.ball p (5 * r)) ≤ v * (5 ^ k * ENNReal.ofReal r ^ k) := by
    rw [← h5]
    exact hball p (5 * r) (mul_pos (by norm_num) hr)
  have hP : hausdorffP n k (horizontalPatch G F p (5 * r)) ≤
      cU * (v * (5 ^ k * ENNReal.ofReal r ^ k)) := by
    calc hausdorffP n k (horizontalPatch G F p (5 * r))
        ≤ cU * volume (horizontalPreimage G F ∩ Metric.ball p (5 * r)) := by
          have h := hup
            {u : G.domain | (u : G.direction) ∈ horizontalPreimage G F ∩ Metric.ball p (5 * r)}
          rwa [gdb9_val_image_preimage (hsub _)] at h
      _ ≤ cU * volume (Metric.ball p (5 * r)) := by
          gcongr
          exact inter_subset_right
      _ ≤ cU * (v * (5 ^ k * ENNReal.ofReal r ^ k)) := by gcongr
  calc ENNReal.ofReal (5 * r) ^ k + volume (Metric.ball p (5 * r)) +
          hausdorffP n k (horizontalPatch G F p (5 * r))
      ≤ 5 ^ k * ENNReal.ofReal r ^ k + v * (5 ^ k * ENNReal.ofReal r ^ k) +
          cU * (v * (5 ^ k * ENNReal.ofReal r ^ k)) := by
        rw [h5]
        exact add_le_add (add_le_add le_rfl hB) hP
    _ = (1 + v + cU * v) * 5 ^ k * ENNReal.ofReal r ^ k := by ring
    _ ≤ (1 + v + cU * v) * 5 ^ k * (2 * hausdorffP n k (horizontalPatch G F p r)) := by
        gcongr
    _ = 2 * 5 ^ k * (1 + v + cU * v) * hausdorffP n k (horizontalPatch G F p r) := by ring

/-- **Local containment:** if the patch centre `Φ(c)` lies in
`P(q,R)` and `5r ≤ R`, then `Φ(E ∩ B(c,r)) ⊆ P(q,2R)`, by the `√2` distance bound. -/
theorem gdb9_horizontalPatch_subset_ball {G : HorizontalGraph n k ε} {F : Set (Space n)}
    (hup : ∀ u w : G.domain, dist (horizontalGraphMap G u) (horizontalGraphMap G w) ≤
      Real.sqrt 2 * dist (u : G.direction) (w : G.direction))
    (c : G.domain) {r : ℝ} {q : Space n} {R : ℝ}
    (hc : horizontalGraphMap G c ∈ Metric.ball q R) (hrR : 5 * r ≤ R) :
    horizontalPatch G F (c : G.direction) r ⊆ Metric.ball q (2 * R) := by
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨-, hu2⟩ := hu
  have hu' : dist (u : G.direction) (c : G.direction) < r := Metric.mem_ball.1 hu2
  have h2 : Real.sqrt 2 ≤ 5 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hd0 : 0 ≤ dist (u : G.direction) (c : G.direction) := dist_nonneg
  have h1 := hup u c
  have h3 : Real.sqrt 2 * dist (u : G.direction) (c : G.direction) ≤
      5 * dist (u : G.direction) (c : G.direction) :=
    mul_le_mul_of_nonneg_right h2 hd0
  have hcq : dist (horizontalGraphMap G c) q < R := Metric.mem_ball.1 hc
  have htri := dist_triangle (horizontalGraphMap G u) (horizontalGraphMap G c) q
  rw [Metric.mem_ball]
  linarith

end OneGraph

/-! ## The horizontal family -/

section Family

variable {n k : ℕ} {ε : ℝ}

/-- **Coverage:** the patches `Φ_j(E_j ∩ B(p_{j,l}, ρ_{j,l}))` cover `K`
modulo `H_P^k`, if the traces do and the balls cover each `E_j` modulo base volume. -/
theorem gdb9_horizontal_patch_cover {J : Set ℕ} (G : J → HorizontalGraph n k ε)
    (F : J → Set (Space n)) {K : Set (Space n)} (cU : ℝ≥0∞)
    (hFsub : ∀ j, F j ⊆ K ∩ (G j).image) (hFcov : hausdorffP n k (K \ ⋃ j, F j) = 0)
    (hup : ∀ j (A : Set (G j).domain), hausdorffP n k (horizontalGraphMap (G j) '' A) ≤
      cU * volume (Subtype.val '' A : Set (G j).direction))
    (L : J → Set ℕ) (p : ∀ j, L j → (G j).direction) (ρ : ∀ j, L j → ℝ)
    (hcov : ∀ j, volume (horizontalPreimage (G j) (F j) \
      ⋃ l, Metric.ball (p j l) (ρ j l)) = 0) :
    hausdorffP n k (K \ ⋃ x : (Σ j : J, L j),
      horizontalPatch (G x.1) (F x.1) (p x.1 x.2) (ρ x.1 x.2)) = 0 := by
  refine gdb9_measure_null_of_subset_union (hausdorffP n k)
    (N := fun j => horizontalGraphMap (G j) '' {u : (G j).domain | (u : (G j).direction) ∈
      horizontalPreimage (G j) (F j) \ ⋃ l, Metric.ball (p j l) (ρ j l)}) ?_ hFcov ?_
  · rintro x ⟨hxK, hxP⟩
    by_cases hxF : x ∈ ⋃ j, F j
    · right
      obtain ⟨j, hxj⟩ := mem_iUnion.1 hxF
      obtain ⟨u, hu⟩ := (hFsub j hxj).2
      change horizontalGraphMap (G j) u = x at hu
      subst hu
      have hE : (u : (G j).direction) ∈ horizontalPreimage (G j) (F j) :=
        (gdb9_mem_horizontalPreimage u).2 hxj
      refine mem_iUnion.2 ⟨j, u, ⟨hE, fun hU => hxP ?_⟩, rfl⟩
      obtain ⟨l, hl⟩ := mem_iUnion.1 hU
      exact mem_iUnion.2 ⟨⟨j, l⟩, u, ⟨hE, hl⟩, rfl⟩
    · exact Or.inl ⟨hxK, hxF⟩
  · intro j
    refine le_antisymm ?_ zero_le
    calc hausdorffP n k (horizontalGraphMap (G j) '' {u : (G j).domain |
          (u : (G j).direction) ∈
            horizontalPreimage (G j) (F j) \ ⋃ l, Metric.ball (p j l) (ρ j l)})
        ≤ cU * volume (Subtype.val '' {u : (G j).domain | (u : (G j).direction) ∈
            horizontalPreimage (G j) (F j) \ ⋃ l, Metric.ball (p j l) (ρ j l)} :
              Set (G j).direction) := hup j _
      _ ≤ cU * volume (horizontalPreimage (G j) (F j) \ ⋃ l, Metric.ball (p j l) (ρ j l)) := by
          gcongr
          exact image_preimage_subset _ _
      _ = 0 := by rw [hcov j, mul_zero]

end Family

/-! ## The patch family -/

/-- Proof of `horizontal_patches`. See the module docstring for the construction. -/
theorem horizontal_patches_proof {n k : ℕ} {ε δ : ℝ} (v cU : ℝ≥0∞) (hv0 : v ≠ 0) (hvt : v ≠ ⊤)
    (K : Set (Space n)) (J : Set ℕ) (G : J → HorizontalGraph n k (min ε 1))
    (F : J → Set (Space n)) (hFm : ∀ j, MeasurableSet (F j))
    (hFsub : ∀ j, F j ⊆ K ∩ (G j).image) (hFdisj : Pairwise fun i j => Disjoint (F i) (F j))
    (hFcov : hausdorffP n k (K \ ⋃ j, F j) = 0)
    (hEm : ∀ j, MeasurableSet (horizontalPreimage (G j) (F j)))
    (hpatchm : ∀ j (A : Set (G j).direction), MeasurableSet A →
      MeasurableSet (horizontalGraphMap (G j) '' {u : (G j).domain | (u : (G j).direction) ∈ A}))
    (hlip : ∀ j (u w : (G j).domain),
      dist (u : (G j).direction) (w : (G j).direction) ≤
          dist (horizontalGraphMap (G j) u) (horizontalGraphMap (G j) w) ∧
        dist (horizontalGraphMap (G j) u) (horizontalGraphMap (G j) w) ≤
          Real.sqrt 2 * dist (u : (G j).direction) (w : (G j).direction))
    (hlow : ∀ j (A : Set (G j).domain), volume (Subtype.val '' A : Set (G j).direction) ≤
      v * hausdorffP n k (horizontalGraphMap (G j) '' A))
    (hup : ∀ j (A : Set (G j).domain), hausdorffP n k (horizontalGraphMap (G j) '' A) ≤
      cU * volume (Subtype.val '' A : Set (G j).direction))
    (hball : ∀ j (p : (G j).direction) (r : ℝ), 0 < r →
      volume (Metric.ball p r) ≤ v * ENNReal.ofReal r ^ k)
    (L : J → Set ℕ) (p : ∀ j, L j → (G j).direction) (r : ∀ j, L j → ℝ)
    (hp : ∀ j l, p j l ∈ horizontalPreimage (G j) (F j))
    (hr : ∀ j l, 0 < r j l ∧ 5 * r j l ≤ δ)
    (hdisj : ∀ j, Pairwise fun l l' =>
      Disjoint (Metric.ball (p j l) (r j l)) (Metric.ball (p j l') (r j l')))
    (hhalf : ∀ j l, v * ENNReal.ofReal (r j l) ^ k ≤
      2 * volume (horizontalPreimage (G j) (F j) ∩ Metric.ball (p j l) (r j l)))
    (hcov5 : ∀ j, volume (horizontalPreimage (G j) (F j) \
      ⋃ l, Metric.ball (p j l) (5 * r j l)) = 0) :
    ∃ D : HorizontalDomainData n k ε δ K,
      (∀ U : Set (Space n), D.traceVolume U =
        ∑' j, volume (horizontalPreimage (G j) (F j) ∩ horizontalPreimage (G j) U)) ∧
      D.totalCharge ≤ 2 * 5 ^ k * (1 + v + cU * v) * hausdorffP n k K ∧
      ∀ (q : Space n) (R : ℝ), 0 < R →
        D.localCharge q R ≤
          2 * 5 ^ k * (1 + v + cU * v) * hausdorffP n k (K ∩ Metric.ball q (2 * R)) := by
  classical
  -- the centres lie in the actual domains
  have hdom : ∀ j l, p j l ∈ (G j).domain := fun j l =>
    gdb9_horizontalPreimage_subset_domain (G j) (F j) (hp j l)
  -- coverage, on the sigma type and then on the codes
  have hcover := gdb9_horizontal_patch_cover G F cU hFsub hFcov hup L p
    (fun j l => 5 * r j l) hcov5
  have hpc : hausdorffP n k (K \ ⋃ α : gdb9_pairIndex J L,
      horizontalPatch (G ((gdb9_pairEquiv J L).symm α).1) (F ((gdb9_pairEquiv J L).symm α).1)
        (p ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2)
        (5 * r ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2)) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right (gdb9_iUnion_pairIndex
      (fun x => horizontalPatch (G x.1) (F x.1) (p x.1 x.2) (5 * r x.1 x.2))).ge) hcover
  -- the paying sets `S_{j,l} = Φ_j(E_j ∩ B(p_{j,l}, r_{j,l}))`
  have hSm : ∀ x : (Σ j : J, L j),
      MeasurableSet (horizontalPatch (G x.1) (F x.1) (p x.1 x.2) (r x.1 x.2)) := fun x =>
    gdb9_measurableSet_horizontalPatch (hpatchm x.1) (hEm x.1) _ _
  have hSdisj : Pairwise fun x y : (Σ j : J, L j) =>
      Disjoint (horizontalPatch (G x.1) (F x.1) (p x.1 x.2) (r x.1 x.2))
        (horizontalPatch (G y.1) (F y.1) (p y.1 y.2) (r y.1 y.2)) :=
    gdb9_pairwise_disjoint_sigma (T := F)
      (fun x => gdb9_horizontalPatch_subset_trace _ _ _ _) hFdisj
      (fun j _ _ hne => gdb9_disjoint_horizontalPatch
        (gdb9_horizontalGraphMap_injective fun u w => (hlip j u w).1) (hdisj j hne))
  have hSK : ∀ x : (Σ j : J, L j),
      horizontalPatch (G x.1) (F x.1) (p x.1 x.2) (r x.1 x.2) ⊆ K := fun x =>
    (gdb9_horizontalPatch_subset_trace _ _ _ _).trans fun _ hy => (hFsub x.1 hy).1
  have hcharge : ∀ x : (Σ j : J, L j),
      ENNReal.ofReal (5 * r x.1 x.2) ^ k + volume (Metric.ball (p x.1 x.2) (5 * r x.1 x.2)) +
          hausdorffP n k (horizontalPatch (G x.1) (F x.1) (p x.1 x.2) (5 * r x.1 x.2)) ≤
        2 * 5 ^ k * (1 + v + cU * v) *
          hausdorffP n k (horizontalPatch (G x.1) (F x.1) (p x.1 x.2) (r x.1 x.2)) := fun x =>
    gdb9_charge_le hv0 hvt (hlow x.1) (hup x.1) (hball x.1) (hr x.1 x.2).1 (hhalf x.1 x.2)
  refine ⟨
    { graphIndex := J
      graph := G
      trace := F
      measurableSet_trace := hFm
      trace_subset := hFsub
      pairwise_disjoint_trace := hFdisj
      trace_cover := hFcov
      measurableSet_tracePreimage := hEm
      patchIndex := gdb9_pairIndex J L
      patchGraph := fun α => ((gdb9_pairEquiv J L).symm α).1
      center := fun α => ⟨p ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2,
        hdom _ _⟩
      center_mem_tracePreimage := fun α => hp _ _
      centerPoint_mem := fun α => (hFsub _ ((gdb9_mem_horizontalPreimage
        (⟨p ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2, hdom _ _⟩ :
          (G ((gdb9_pairEquiv J L).symm α).1).domain)).1 (hp _ _))).1
      radius := fun α => 5 * r ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2
      radius_pos := fun α => mul_pos (by norm_num) (hr _ _).1
      radius_le := fun α => (hr _ _).2
      measurableSet_patch := fun α =>
        gdb9_measurableSet_horizontalPatch (hpatchm _) (hEm _) _ _
      patch_cover := hpc }, fun U => rfl, ?_, ?_⟩
  · exact gdb9_tsum_le_of_disjoint_charges (hausdorffP n k)
      (S := fun α : gdb9_pairIndex J L =>
        horizontalPatch (G ((gdb9_pairEquiv J L).symm α).1) (F ((gdb9_pairEquiv J L).symm α).1)
          (p ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2)
          (r ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2))
      (fun α => hSm ((gdb9_pairEquiv J L).symm α)) (gdb9_pairwise_pairIndex hSdisj)
      (fun α => hSK ((gdb9_pairEquiv J L).symm α)) (fun α => hcharge ((gdb9_pairEquiv J L).symm α))
  · intro q R hR
    refine gdb9_tsum_subtype_le_of_disjoint_charges (hausdorffP n k) _
      (S := fun α : gdb9_pairIndex J L =>
        horizontalPatch (G ((gdb9_pairEquiv J L).symm α).1) (F ((gdb9_pairEquiv J L).symm α).1)
          (p ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2)
          (r ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2))
      (fun α => hSm ((gdb9_pairEquiv J L).symm α)) (gdb9_pairwise_pairIndex hSdisj) ?_
      (fun α => hcharge ((gdb9_pairEquiv J L).symm α))
    intro α hα
    obtain ⟨hcα, hρα⟩ := hα
    exact subset_inter (hSK ((gdb9_pairEquiv J L).symm α)) (gdb9_horizontalPatch_subset_ball
      (fun u w => (hlip _ u w).2)
      (⟨p ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2, hdom _ _⟩ :
        (G ((gdb9_pairEquiv J L).symm α).1).domain) hcα hρα)

end ParabolicRectifiability.Enhancements.GraphDomainTree
