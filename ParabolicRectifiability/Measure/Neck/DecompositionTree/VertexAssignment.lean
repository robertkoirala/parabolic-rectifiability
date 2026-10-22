import ParabolicRectifiability.Measure.Neck.DecompositionTree.ClosureIdentity

/-!
# Assignment of carrier balls to vertex centers and global summation

Proofs of two statements about the decomposition tree:

* `StepTree.exists_vertex_center_proof` (`StepTree.exists_vertex_center`): for
  `0 < η ≤ min{1/200, min(3ρ, 2ε)/200}`, a ball `P(z, r)` with `z ∈ K`, `0 < r ≤ R` is
  assigned to a vertex `v` and an actual center `c` of its neck with `d_P(z, c) < r/50` and
  `r ≤ R_v / η`. Follow `z` down the subtree closure identity (`StepTree.subtreeSet_closure_identity_proof`) while
  `R_v ≥ η r`: a core point gives `c = z`; at the first child `w` with `R_w < η r`, the exact
  radius `R_w ∈ {3ρ d_c, 2ε d_c}` and the closed parent hole give `d_P(z, c) ≤ d_c < r/200`.
  The descent stops because `R_v ≤ R / 2^{|v|}` (`StepTree.depth_content_le_proof`).
* `stepTree_packing_of_assignment_proof` (`stepTree_packing_of_assignment`): disjoint balls give
  `d_P(z_i, z_j) ≥ max(r_i, r_j)`, hence `d_P(c_i, c_j) ≥ (24/25) max(r_i, r_j)` within one
  vertex; regrouping the countable sum by vertex, the per-vertex bound and
  `∑_v R_v^k ≤ 2 R^k` (`StepTree.radius_total_le_proof`) give `C_p = 2 C_v`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-- Disjoint open balls have centers at distance at least the larger radius. -/
theorem ms7_le_dist_of_disjoint_ball {X : Type*} [PseudoMetricSpace X] {x y : X} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h : Disjoint (Metric.ball x a) (Metric.ball y b)) :
    max a b ≤ dist x y := by
  refine max_le ?_ ?_
  · by_contra hlt
    rw [not_le] at hlt
    exact Set.disjoint_left.mp h (Metric.mem_ball.mpr (by rwa [dist_comm]))
      (Metric.mem_ball_self hb)
  · by_contra hlt
    rw [not_le] at hlt
    exact Set.disjoint_left.mp h (Metric.mem_ball_self ha) (Metric.mem_ball.mpr hlt)

namespace StepTree

variable {n k : ℕ} {F : FamilyKind} {S : Set (Space n)} {q : Space n} {R B Eerr ρ ε : ℝ}
  {ν : Measure (Space n)}

/-- **`StepTree.exists_vertex_center`**: assignment of a ball centered in the carrier to a
vertex and an actual center of its neck. -/
theorem exists_vertex_center_proof {n k : ℕ} {F : FamilyKind} {S : Set (Space n)}
    {q : Space n} {R B Eerr ρ ε L : ℝ} {ν : Measure (Space n)}
    (Tr : StepTree ν k F S q R B Eerr ρ ε) (hR : 0 < R) (hB : 0 < B) (hL : 0 < L)
    (hρ : 0 < ρ) (hε : 0 < ε)
    (hcert : ∀ v ∈ Tr.vertices,
      (Tr.vneck v).neck.IsCertified (ν.restrict (Tr.source v)) B B L)
    (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1 / 200) (hη₂ : η ≤ min (3 * ρ) (2 * ε) / 200) :
    ∀ z ∈ Tr.carrier, ∀ r : ℝ, 0 < r → r ≤ R → ∃ v ∈ Tr.vertices,
      ∃ c ∈ (Tr.vneck v).neck.centers, dist z c < r / 50 ∧ r ≤ Tr.radius v / η := by
  intro z hz r hr hrR
  have hid := Tr.subtreeSet_closure_identity_proof hR hB hL hcert
  have hle : ∀ v, η * r ≤ Tr.radius v → r ≤ Tr.radius v / η := fun v h => by
    rw [le_div_iff₀ hη]; linarith
  have hm1 : min (3 * ρ) (2 * ε) ≤ 3 * ρ := min_le_left _ _
  have hm2 : min (3 * ρ) (2 * ε) ≤ 2 * ε := min_le_right _ _
  have hηr : η * r ≤ min (3 * ρ) (2 * ε) / 200 * r := mul_le_mul_of_nonneg_right hη₂ hr.le
  have step : ∀ j : ℕ, (∃ v ∈ Tr.vertices, ∃ c ∈ (Tr.vneck v).neck.centers,
      dist z c < r / 50 ∧ r ≤ Tr.radius v / η) ∨
      ∃ v ∈ Tr.vertices, v.length = j ∧ z ∈ closure (Tr.subtreeSet v) ∧
        η * r ≤ Tr.radius v := by
    intro j
    induction j with
    | zero =>
      right
      refine ⟨[], Tr.root_mem, rfl, Tr.ms7_carrier_subset_closure_subtree hz, ?_⟩
      rw [Tr.radius_root]
      calc η * r ≤ 1 * r := mul_le_mul_of_nonneg_right (by linarith) hr.le
        _ ≤ R := by linarith
    | succ j ih =>
      rcases ih with hG | ⟨v, hv, hlen, hzv, hvr⟩
      · exact Or.inl hG
      rcases hid v hv hzv with hzc | hzc
      · left
        refine ⟨v, hv, z, hzc.1, ?_, hle v hvr⟩
        rw [dist_self]; positivity
      · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzc
        by_cases hsmall : η * r ≤ Tr.radius (v ++ [i])
        · exact Or.inr ⟨v ++ [i], hi, by simp [hlen], hzi, hsmall⟩
        · left
          rw [not_le] at hsmall
          have hiC : i ∈ (Tr.step v).childIndex := (Tr.child_mem_iff v hv i).mp hi
          have hc := (Tr.step v).childParent_mem i hiC
          have hzc' := Metric.mem_closedBall.mp
            (Tr.ms7_closure_subtree_child_subset hB hL hcert hv hi hzi)
          have hrad := (Tr.step v).childRadius_eq i hiC
          rw [← Tr.child_radius v hv i hiC] at hrad
          have hd : (Tr.vneck v).neck.radius ((Tr.step v).childParent i) < r / 200 := by
            rcases hrad with h | h
            · have h3 : 3 * ρ * (Tr.vneck v).neck.radius ((Tr.step v).childParent i) <
                  3 * ρ * (r / 200) := by
                have := mul_le_mul_of_nonneg_right hm1 hr.le
                linarith
              exact lt_of_mul_lt_mul_left h3 (by positivity)
            · have h3 : 2 * ε * (Tr.vneck v).neck.radius ((Tr.step v).childParent i) <
                  2 * ε * (r / 200) := by
                have := mul_le_mul_of_nonneg_right hm2 hr.le
                linarith
              exact lt_of_mul_lt_mul_left h3 (by positivity)
          exact ⟨v, hv, (Tr.step v).childParent i, hc.1, by linarith, hle v hvr⟩
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (R / (η * r)) one_lt_two
  rcases step j with hG | ⟨v, hv, hlen, -, hvr⟩
  · exact hG
  · exfalso
    have h1 := Tr.ms7_radius_le v hv
    rw [hlen] at h1
    have hηr0 : 0 < η * r := mul_pos hη hr
    have h2 : R < 2 ^ j * (η * r) := (div_lt_iff₀ hηr0).mp hj
    have h3 : η * r * 2 ^ j ≤ R := (le_div_iff₀ (by positivity)).mp (hvr.trans h1)
    linarith

end StepTree

/-- **`stepTree_packing_of_assignment`**: with the vertex assignment
(`StepTree.exists_vertex_center`) and the per-vertex bound (`certified_center_packing`) as
hypotheses, `C_p = 2 C_v`. -/
theorem stepTree_packing_of_assignment_proof (n : ℕ) (Eerr ρ ε η Cv : ℝ) (_hη : 0 < η)
    (hCv : 0 < Cv) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ {k : ℕ} {F : FamilyKind} {S : Set (Space n)} {q : Space n}
      {R B : ℝ} {ν : Measure (Space n)} (Tr : StepTree ν k F S q R B Eerr ρ ε),
      1 ≤ k → k < n + 2 → 0 < R → 0 < B →
      (∀ z ∈ Tr.carrier, ∀ r : ℝ, 0 < r → r ≤ R → ∃ v ∈ Tr.vertices,
        ∃ c ∈ (Tr.vneck v).neck.centers, dist z c < r / 50 ∧ r ≤ Tr.radius v / η) →
      (∀ v ∈ Tr.vertices, ∀ (I : Type) [Countable I] (c : I → Space n) (r : I → ℝ),
        (∀ i, c i ∈ (Tr.vneck v).neck.centers) → (∀ i, 0 < r i ∧ r i ≤ Tr.radius v / η) →
        (∀ i j, i ≠ j → 24 / 25 * max (r i) (r j) ≤ dist (c i) (c j)) →
        ∑' i, ENNReal.ofReal (r i) ^ k ≤ ENNReal.ofReal (Cv * Tr.radius v ^ k)) →
      ∀ (I : Type) [Countable I] (z : I → Space n) (r : I → ℝ),
        (∀ i, z i ∈ Tr.carrier) → (∀ i, 0 < r i ∧ r i ≤ R) →
        (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
        ∑' i, ENNReal.ofReal (r i) ^ k ≤ ENNReal.ofReal (Cp * R ^ k) := by
  refine ⟨2 * Cv, by positivity, ?_⟩
  intro k F S q R B ν Tr _hk _hkn hR _hB hassign hpack I _ z r hz hr hdisj
  choose vf hvf c hc hdist hrv using fun i => hassign (z i) (hz i) (r i) (hr i).1 (hr i).2
  obtain ⟨V, hV⟩ : ∃ V : I → Tr.vertices, ∀ i, (V i).1 = vf i :=
    ⟨fun i => ⟨vf i, hvf i⟩, fun _ => rfl⟩
  have hsep : ∀ i j, i ≠ j → 24 / 25 * max (r i) (r j) ≤ dist (c i) (c j) := by
    intro i j hij
    have hzz := ms7_le_dist_of_disjoint_ball (hr i).1 (hr j).1 (hdisj i j hij)
    have hi := hdist i
    have hj := hdist j
    have htri : dist (z i) (z j) ≤ dist (z i) (c i) + dist (c i) (c j) + dist (c j) (z j) :=
      dist_triangle4 _ _ _ _
    rw [dist_comm (c j) (z j)] at htri
    have h1 : r i ≤ max (r i) (r j) := le_max_left _ _
    have h2 : r j ≤ max (r i) (r j) := le_max_right _ _
    linarith
  calc ∑' i, ENNReal.ofReal (r i) ^ k
      = ∑' p : (Σ v : Tr.vertices, {i : I // V i = v}), ENNReal.ofReal (r p.2.1) ^ k :=
        ((Equiv.sigmaFiberEquiv V).tsum_eq (fun i => ENNReal.ofReal (r i) ^ k)).symm
    _ = ∑' (v : Tr.vertices) (i : {i : I // V i = v}), ENNReal.ofReal (r i.1) ^ k :=
        ENNReal.tsum_sigma' (fun p : (Σ v : Tr.vertices, {i : I // V i = v}) =>
          ENNReal.ofReal (r p.2.1) ^ k)
    _ ≤ ∑' v : Tr.vertices, ENNReal.ofReal (Cv * Tr.radius v ^ k) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        have hVi : ∀ i : {i : I // V i = v}, vf i.1 = v.1 :=
          fun i => (hV i.1).symm.trans (congrArg Subtype.val i.2)
        refine hpack v.1 v.2 {i : I // V i = v} (fun i => c i.1) (fun i => r i.1) ?_ ?_ ?_
        · intro i
          have h := hc i.1
          rw [hVi i] at h
          exact h
        · intro i
          refine ⟨(hr i.1).1, ?_⟩
          have h := hrv i.1
          rw [hVi i] at h
          exact h
        · intro i j hij
          exact hsep i.1 j.1 (fun h => hij (Subtype.ext h))
    _ = ENNReal.ofReal Cv * ∑' v : Tr.vertices, ENNReal.ofReal (Tr.radius v ^ k) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun v => ENNReal.ofReal_mul hCv.le
    _ ≤ ENNReal.ofReal Cv * ENNReal.ofReal (2 * R ^ k) := by
        gcongr
        exact StepTree.radius_total_le_proof Tr hR
    _ = ENNReal.ofReal (2 * Cv * R ^ k) := by
        rw [← ENNReal.ofReal_mul hCv.le]
        congr 1
        ring

end ParabolicRectifiability
