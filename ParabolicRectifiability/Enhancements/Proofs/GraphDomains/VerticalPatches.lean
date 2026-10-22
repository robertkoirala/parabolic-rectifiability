import ParabolicRectifiability.Enhancements.Proofs.GraphDomains.HorizontalPatches

/-! # Vertical patch family: proof

Proof of `Enhancements.GraphDomainTree.vertical_patches`, under the name
`vertical_patches_proof`. It reuses the shared helpers of `HorizontalPatches`
(disjoint-charge summation, sigma disjointness, the null cover, and the `Nat.pair` reindexing
`gdb9_pairIndex`). The vertical patch is `Q_α = Φ_j(B_α)`.

Construction. Patches are `α = (j, l)`, coded by `Nat.pair`, with
centre `p_{j,l}` (a point of the full base `W_j × ℝ`), radius `ρ_α = 5 r_{j,l} ≤ δ` and the
**whole** base-ball patch `Φ_j(B(p, ρ_α))`, which may leave the carrier. The charge of `α` is
paid by the localized set `S_α = Φ_j(E_j ∩ B(p, r_{j,l})) ⊆ F_j ⊆ K` (`E_j = Φ_j⁻¹(F_j)`),
measurable by `hpatchm`. Half density and the lower comparison give `ρ_α^k ≤ 2·5^k H_P^k(S_α)`;
the ball bound and the upper comparison on the whole ball give `λ(B_α) ≤ v ρ_α^k` and
`H_P^k(Φ_j(B_α)) ≤ cU λ(B_α) ≤ cU v ρ_α^k`, so `c_α ≤ 2·5^k(1+v+cU v) H_P^k(S_α)`. The `S_α` are
disjoint (disjoint balls and the injective graph map within `j`, disjoint traces across `j`)
and lie in `K`, and for `α ∈ I(q,R)` in `P(q,2R)`, by the `√2` distance bound
(`√2 r ≤ 5 r = ρ_α ≤ R`). Coverage: the uncovered part of `K` lies in `K \ ⋃ F_j` and the
images `Φ_j(E_j \ ⋃_l B(p_{j,l}, 5 r_{j,l}))`, null by `hup` (`cU · 0 = 0`, also for
`cU = ⊤`); the patch of `(j,l)` contains `Φ_j(E_j ∩ B(p_{j,l}, 5 r_{j,l}))`. No case split on
`δ` is needed: `hr` makes every radius admissible, and for `δ ≤ 0` the families `L j` are empty.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Enhancements.GraphDomainTree

open ParabolicRectifiability.Foundations

/-! ## One vertical graph -/

section OneGraph

variable {n k : ℕ} {ε : ℝ}

/-- The paying set `S = Φ(E ∩ B(p,r))` of a vertical patch, with `E = Φ⁻¹(F)`: the image of the
part of the **smaller** ball that lies in the trace preimage. -/
def gdb10_payingSet (G : GeneralRegularVerticalGraph n k ε) (F : Set (Space n))
    (p : SubspaceSpace G.direction) (r : ℝ) : Set (Space n) :=
  G.map '' (G.map ⁻¹' F ∩ Metric.ball p r)

theorem gdb10_payingSet_subset_trace (G : GeneralRegularVerticalGraph n k ε) (F : Set (Space n))
    (p : SubspaceSpace G.direction) (r : ℝ) : gdb10_payingSet G F p r ⊆ F :=
  (image_mono inter_subset_left).trans (image_preimage_subset _ _)

theorem gdb10_measurableSet_payingSet {G : GeneralRegularVerticalGraph n k ε} {F : Set (Space n)}
    (hpatchm : ∀ A : Set (SubspaceSpace G.direction), MeasurableSet A →
      MeasurableSet (G.map '' A))
    (hEm : MeasurableSet (G.map ⁻¹' F)) (p : SubspaceSpace G.direction) (r : ℝ) :
    MeasurableSet (gdb10_payingSet G F p r) :=
  hpatchm _ (hEm.inter measurableSet_ball)

theorem gdb10_map_injective {G : GeneralRegularVerticalGraph n k ε}
    (hlow : ∀ p q : SubspaceSpace G.direction, dist p q ≤ dist (G.map p) (G.map q)) :
    Function.Injective G.map := by
  intro p q h
  have hd := hlow p q
  rw [h, dist_self] at hd
  exact dist_le_zero.1 hd

theorem gdb10_disjoint_payingSet {G : GeneralRegularVerticalGraph n k ε} {F : Set (Space n)}
    (hinj : Function.Injective G.map) {p p' : SubspaceSpace G.direction} {r r' : ℝ}
    (h : Disjoint (Metric.ball p r) (Metric.ball p' r')) :
    Disjoint (gdb10_payingSet G F p r) (gdb10_payingSet G F p' r') :=
  disjoint_image_of_injective hinj (h.mono inter_subset_right inter_subset_right)

/-- **The single-patch charge**, vertical form: `ρ^k + λ(B(p,ρ)) + H_P^k(Φ(B(p,ρ))) ≤ 2·5^k(1+v+cU v) H_P^k(Φ(E ∩ B(p,r)))` for
`ρ = 5r`. The patch term uses the whole ball; the paying set is localized to `E ∩ B(p,r)`.
Valid for `cU = ⊤`. -/
theorem gdb10_charge_le {G : GeneralRegularVerticalGraph n k ε} {F : Set (Space n)}
    {v cU : ℝ≥0∞} (hv0 : v ≠ 0) (hvt : v ≠ ⊤)
    (hlow : ∀ A : Set (SubspaceSpace G.direction),
      intrinsicParabolicVolume G.direction A ≤ v * hausdorffP n k (G.map '' A))
    (hup : ∀ A : Set (SubspaceSpace G.direction),
      hausdorffP n k (G.map '' A) ≤ cU * intrinsicParabolicVolume G.direction A)
    (hball : ∀ (p : SubspaceSpace G.direction) (r : ℝ), 0 < r →
      intrinsicParabolicVolume G.direction (Metric.ball p r) ≤ v * ENNReal.ofReal r ^ k)
    {p : SubspaceSpace G.direction} {r : ℝ} (hr : 0 < r)
    (hhalf : v * ENNReal.ofReal r ^ k ≤
      2 * intrinsicParabolicVolume G.direction (G.map ⁻¹' F ∩ Metric.ball p r)) :
    ENNReal.ofReal (5 * r) ^ k + intrinsicParabolicVolume G.direction (Metric.ball p (5 * r)) +
        hausdorffP n k (verticalPatch G p (5 * r)) ≤
      2 * 5 ^ k * (1 + v + cU * v) * hausdorffP n k (gdb10_payingSet G F p r) := by
  have hvolS : intrinsicParabolicVolume G.direction (G.map ⁻¹' F ∩ Metric.ball p r) ≤
      v * hausdorffP n k (gdb10_payingSet G F p r) :=
    hlow (G.map ⁻¹' F ∩ Metric.ball p r)
  have ht : ENNReal.ofReal r ^ k ≤ 2 * hausdorffP n k (gdb10_payingSet G F p r) := by
    have h1 : v * ENNReal.ofReal r ^ k ≤ v * (2 * hausdorffP n k (gdb10_payingSet G F p r)) :=
      calc v * ENNReal.ofReal r ^ k
          ≤ 2 * intrinsicParabolicVolume G.direction (G.map ⁻¹' F ∩ Metric.ball p r) := hhalf
        _ ≤ 2 * (v * hausdorffP n k (gdb10_payingSet G F p r)) := by gcongr
        _ = v * (2 * hausdorffP n k (gdb10_payingSet G F p r)) := mul_left_comm _ _ _
    exact (ENNReal.mul_le_mul_iff_right hv0 hvt).1 h1
  have h5 : ENNReal.ofReal (5 * r) ^ k = 5 ^ k * ENNReal.ofReal r ^ k := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_pow]
  have hB : intrinsicParabolicVolume G.direction (Metric.ball p (5 * r)) ≤
      v * (5 ^ k * ENNReal.ofReal r ^ k) := by
    rw [← h5]
    exact hball p (5 * r) (mul_pos (by norm_num) hr)
  have hP : hausdorffP n k (verticalPatch G p (5 * r)) ≤
      cU * (v * (5 ^ k * ENNReal.ofReal r ^ k)) :=
    calc hausdorffP n k (G.map '' Metric.ball p (5 * r))
        ≤ cU * intrinsicParabolicVolume G.direction (Metric.ball p (5 * r)) :=
          hup (Metric.ball p (5 * r))
      _ ≤ cU * (v * (5 ^ k * ENNReal.ofReal r ^ k)) := by gcongr
  calc ENNReal.ofReal (5 * r) ^ k + intrinsicParabolicVolume G.direction (Metric.ball p (5 * r)) +
          hausdorffP n k (verticalPatch G p (5 * r))
      ≤ 5 ^ k * ENNReal.ofReal r ^ k + v * (5 ^ k * ENNReal.ofReal r ^ k) +
          cU * (v * (5 ^ k * ENNReal.ofReal r ^ k)) := by
        rw [h5]
        exact add_le_add (add_le_add le_rfl hB) hP
    _ = (1 + v + cU * v) * 5 ^ k * ENNReal.ofReal r ^ k := by ring
    _ ≤ (1 + v + cU * v) * 5 ^ k * (2 * hausdorffP n k (gdb10_payingSet G F p r)) := by
        gcongr
    _ = 2 * 5 ^ k * (1 + v + cU * v) * hausdorffP n k (gdb10_payingSet G F p r) := by ring

/-- **Local containment:** if the patch centre `Φ(c)` lies in
`P(q,R)` and `5r ≤ R`, then the paying set `Φ(E ∩ B(c,r)) ⊆ P(q,2R)`, by the `√2` distance
bound. -/
theorem gdb10_payingSet_subset_ball {G : GeneralRegularVerticalGraph n k ε} {F : Set (Space n)}
    (hup : ∀ u w : SubspaceSpace G.direction,
      dist (G.map u) (G.map w) ≤ Real.sqrt 2 * dist u w)
    (c : SubspaceSpace G.direction) {r : ℝ} {q : Space n} {R : ℝ}
    (hc : G.map c ∈ Metric.ball q R) (hrR : 5 * r ≤ R) :
    gdb10_payingSet G F c r ⊆ Metric.ball q (2 * R) := by
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨-, hu2⟩ := hu
  have hu' : dist u c < r := Metric.mem_ball.1 hu2
  have h2 : Real.sqrt 2 ≤ 5 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hd0 : 0 ≤ dist u c := dist_nonneg
  have h1 := hup u c
  have h3 : Real.sqrt 2 * dist u c ≤ 5 * dist u c := mul_le_mul_of_nonneg_right h2 hd0
  have hcq : dist (G.map c) q < R := Metric.mem_ball.1 hc
  have htri := dist_triangle (G.map u) (G.map c) q
  rw [Metric.mem_ball]
  linarith

end OneGraph

/-! ## The vertical family -/

section Family

variable {n k : ℕ} {ε : ℝ}

/-- **Coverage:** the whole-ball patches `Φ_j(B(p_{j,l}, ρ_{j,l}))` cover
`K` modulo `H_P^k`, if the traces do and the balls cover each `E_j` modulo base volume. -/
theorem gdb10_vertical_patch_cover {J : Set ℕ} (G : J → GeneralRegularVerticalGraph n k ε)
    (F : J → Set (Space n)) {K : Set (Space n)} (cU : ℝ≥0∞)
    (hFsub : ∀ j, F j ⊆ K ∩ (G j).image) (hFcov : hausdorffP n k (K \ ⋃ j, F j) = 0)
    (hup : ∀ j (A : Set (SubspaceSpace (G j).direction)),
      hausdorffP n k ((G j).map '' A) ≤ cU * intrinsicParabolicVolume (G j).direction A)
    (L : J → Set ℕ) (p : ∀ j, L j → SubspaceSpace (G j).direction) (ρ : ∀ j, L j → ℝ)
    (hcov : ∀ j, intrinsicParabolicVolume (G j).direction ((G j).map ⁻¹' F j \
      ⋃ l, Metric.ball (p j l) (ρ j l)) = 0) :
    hausdorffP n k (K \ ⋃ x : (Σ j : J, L j), verticalPatch (G x.1) (p x.1 x.2) (ρ x.1 x.2)) =
      0 := by
  refine gdb9_measure_null_of_subset_union (hausdorffP n k)
    (N := fun j => (G j).map '' ((G j).map ⁻¹' F j \ ⋃ l, Metric.ball (p j l) (ρ j l)))
    ?_ hFcov ?_
  · rintro x ⟨hxK, hxP⟩
    by_cases hxF : x ∈ ⋃ j, F j
    · right
      obtain ⟨j, hxj⟩ := mem_iUnion.1 hxF
      obtain ⟨u, hu⟩ := (hFsub j hxj).2
      change (G j).map u = x at hu
      subst hu
      have hE : u ∈ (G j).map ⁻¹' F j := hxj
      refine mem_iUnion.2 ⟨j, u, ⟨hE, fun hU => hxP ?_⟩, rfl⟩
      obtain ⟨l, hl⟩ := mem_iUnion.1 hU
      exact mem_iUnion.2 ⟨⟨j, l⟩, u, hl, rfl⟩
    · exact Or.inl ⟨hxK, hxF⟩
  · intro j
    refine le_antisymm ?_ zero_le
    calc hausdorffP n k ((G j).map '' ((G j).map ⁻¹' F j \ ⋃ l, Metric.ball (p j l) (ρ j l)))
        ≤ cU * intrinsicParabolicVolume (G j).direction
            ((G j).map ⁻¹' F j \ ⋃ l, Metric.ball (p j l) (ρ j l)) := hup j _
      _ = 0 := by rw [hcov j, mul_zero]

end Family

/-! ## The patch family -/

/-- Proof of `vertical_patches`. See the module docstring for the construction. -/
theorem vertical_patches_proof {n k : ℕ} {ε δ : ℝ} (v cU : ℝ≥0∞) (hv0 : v ≠ 0) (hvt : v ≠ ⊤)
    (K : Set (Space n)) (J : Set ℕ) (G : J → GeneralRegularVerticalGraph n k (min ε 1))
    (F : J → Set (Space n)) (hFm : ∀ j, MeasurableSet (F j))
    (hFsub : ∀ j, F j ⊆ K ∩ (G j).image) (hFdisj : Pairwise fun i j => Disjoint (F i) (F j))
    (hFcov : hausdorffP n k (K \ ⋃ j, F j) = 0)
    (hEm : ∀ j, MeasurableSet ((G j).map ⁻¹' F j))
    (hpatchm : ∀ j (A : Set (SubspaceSpace (G j).direction)), MeasurableSet A →
      MeasurableSet ((G j).map '' A))
    (hlip : ∀ j (p q : SubspaceSpace (G j).direction),
      dist p q ≤ dist ((G j).map p) ((G j).map q) ∧
        dist ((G j).map p) ((G j).map q) ≤ Real.sqrt 2 * dist p q)
    (hlow : ∀ j (A : Set (SubspaceSpace (G j).direction)),
      intrinsicParabolicVolume (G j).direction A ≤ v * hausdorffP n k ((G j).map '' A))
    (hup : ∀ j (A : Set (SubspaceSpace (G j).direction)),
      hausdorffP n k ((G j).map '' A) ≤ cU * intrinsicParabolicVolume (G j).direction A)
    (hball : ∀ j (p : SubspaceSpace (G j).direction) (r : ℝ), 0 < r →
      intrinsicParabolicVolume (G j).direction (Metric.ball p r) ≤ v * ENNReal.ofReal r ^ k)
    (L : J → Set ℕ) (p : ∀ j, L j → SubspaceSpace (G j).direction) (r : ∀ j, L j → ℝ)
    (hp : ∀ j l, p j l ∈ (G j).map ⁻¹' F j)
    (hr : ∀ j l, 0 < r j l ∧ 5 * r j l ≤ δ)
    (hdisj : ∀ j, Pairwise fun l l' =>
      Disjoint (Metric.ball (p j l) (r j l)) (Metric.ball (p j l') (r j l')))
    (hhalf : ∀ j l, v * ENNReal.ofReal (r j l) ^ k ≤
      2 * intrinsicParabolicVolume (G j).direction ((G j).map ⁻¹' F j ∩ Metric.ball (p j l) (r j l)))
    (hcov5 : ∀ j, intrinsicParabolicVolume (G j).direction ((G j).map ⁻¹' F j \
      ⋃ l, Metric.ball (p j l) (5 * r j l)) = 0) :
    ∃ D : VerticalDomainData n k ε δ K,
      (∀ U : Set (Space n), D.traceVolume U =
        ∑' j, intrinsicParabolicVolume (G j).direction ((G j).map ⁻¹' F j ∩ (G j).map ⁻¹' U)) ∧
      D.totalCharge ≤ 2 * 5 ^ k * (1 + v + cU * v) * hausdorffP n k K ∧
      ∀ (q : Space n) (R : ℝ), 0 < R →
        D.localCharge q R ≤
          2 * 5 ^ k * (1 + v + cU * v) * hausdorffP n k (K ∩ Metric.ball q (2 * R)) := by
  classical
  -- the patch centres map into the carrier
  have hpK : ∀ j l, (G j).map (p j l) ∈ K := fun j l => (hFsub j (hp j l)).1
  -- coverage by the whole-ball patches, on the sigma type and then on the codes
  have hcover := gdb10_vertical_patch_cover G F cU hFsub hFcov hup L p
    (fun j l => 5 * r j l) hcov5
  have hpc : hausdorffP n k (K \ ⋃ α : gdb9_pairIndex J L,
      verticalPatch (G ((gdb9_pairEquiv J L).symm α).1)
        (p ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2)
        (5 * r ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2)) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right (gdb9_iUnion_pairIndex
      (fun x => verticalPatch (G x.1) (p x.1 x.2) (5 * r x.1 x.2))).ge) hcover
  -- the paying sets `S_{j,l} = Φ_j(E_j ∩ B(p_{j,l}, r_{j,l}))`
  have hSm : ∀ x : (Σ j : J, L j),
      MeasurableSet (gdb10_payingSet (G x.1) (F x.1) (p x.1 x.2) (r x.1 x.2)) := fun x =>
    gdb10_measurableSet_payingSet (hpatchm x.1) (hEm x.1) _ _
  have hSdisj : Pairwise fun x y : (Σ j : J, L j) =>
      Disjoint (gdb10_payingSet (G x.1) (F x.1) (p x.1 x.2) (r x.1 x.2))
        (gdb10_payingSet (G y.1) (F y.1) (p y.1 y.2) (r y.1 y.2)) :=
    gdb9_pairwise_disjoint_sigma (T := F)
      (fun x => gdb10_payingSet_subset_trace _ _ _ _) hFdisj
      (fun j _ _ hne => gdb10_disjoint_payingSet
        (gdb10_map_injective fun u w => (hlip j u w).1) (hdisj j hne))
  have hSK : ∀ x : (Σ j : J, L j),
      gdb10_payingSet (G x.1) (F x.1) (p x.1 x.2) (r x.1 x.2) ⊆ K := fun x =>
    (gdb10_payingSet_subset_trace _ _ _ _).trans fun _ hy => (hFsub x.1 hy).1
  have hcharge : ∀ x : (Σ j : J, L j),
      ENNReal.ofReal (5 * r x.1 x.2) ^ k +
          intrinsicParabolicVolume (G x.1).direction (Metric.ball (p x.1 x.2) (5 * r x.1 x.2)) +
          hausdorffP n k (verticalPatch (G x.1) (p x.1 x.2) (5 * r x.1 x.2)) ≤
        2 * 5 ^ k * (1 + v + cU * v) *
          hausdorffP n k (gdb10_payingSet (G x.1) (F x.1) (p x.1 x.2) (r x.1 x.2)) := fun x =>
    gdb10_charge_le hv0 hvt (hlow x.1) (hup x.1) (hball x.1) (hr x.1 x.2).1 (hhalf x.1 x.2)
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
      center := fun α => p ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2
      center_mem_tracePreimage := fun α => hp _ _
      centerPoint_mem := fun α => hpK _ _
      radius := fun α => 5 * r ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2
      radius_pos := fun α => mul_pos (by norm_num) (hr _ _).1
      radius_le := fun α => (hr _ _).2
      measurableSet_patch := fun α => hpatchm _ _ measurableSet_ball
      patch_cover := hpc }, fun U => rfl, ?_, ?_⟩
  · exact gdb9_tsum_le_of_disjoint_charges (hausdorffP n k)
      (S := fun α : gdb9_pairIndex J L =>
        gdb10_payingSet (G ((gdb9_pairEquiv J L).symm α).1) (F ((gdb9_pairEquiv J L).symm α).1)
          (p ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2)
          (r ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2))
      (fun α => hSm ((gdb9_pairEquiv J L).symm α)) (gdb9_pairwise_pairIndex hSdisj)
      (fun α => hSK ((gdb9_pairEquiv J L).symm α)) (fun α => hcharge ((gdb9_pairEquiv J L).symm α))
  · intro q R _
    refine gdb9_tsum_subtype_le_of_disjoint_charges (hausdorffP n k) _
      (S := fun α : gdb9_pairIndex J L =>
        gdb10_payingSet (G ((gdb9_pairEquiv J L).symm α).1) (F ((gdb9_pairEquiv J L).symm α).1)
          (p ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2)
          (r ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2))
      (fun α => hSm ((gdb9_pairEquiv J L).symm α)) (gdb9_pairwise_pairIndex hSdisj) ?_
      (fun α => hcharge ((gdb9_pairEquiv J L).symm α))
    intro α hα
    obtain ⟨hcα, hρα⟩ := hα
    exact subset_inter (hSK ((gdb9_pairEquiv J L).symm α)) (gdb10_payingSet_subset_ball
      (fun u w => (hlip _ u w).2)
      (p ((gdb9_pairEquiv J L).symm α).1 ((gdb9_pairEquiv J L).symm α).2) hcα hρα)

end ParabolicRectifiability.Enhancements.GraphDomainTree
