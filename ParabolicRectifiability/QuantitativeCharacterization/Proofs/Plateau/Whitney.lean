import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Plateau.Cubes

/-! # Maximal qualifying dyadic cubes 

For a closed nonempty `D ⊆ ℝ^k` (`k ≥ 1`), a dyadic cube `Q` *qualifies* when
`4 diam Q ≤ dist(Q, D)` and is *maximal* when it qualifies and no qualifying dyadic cube of a
strictly higher level contains it. We prove:

* qualifying cubes lie in `Dᶜ`;
* every point of `Dᶜ` lies in a maximal qualifying cube (covering);
* the failed parent gives `dist(Q, D) ≤ 10 diam Q` (upper Whitney inequality);
* two maximal cubes whose (open box, closed cube) meet are equal (hence disjoint interiors,
  and the interior of a maximal cube misses every other maximal cube).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

variable {k : ℕ}

theorem b2plat_setDist_le {Q D : Set (Spatial k)} {x : Spatial k} (hx : x ∈ Q) :
    setDist Q D ≤ Metric.infDist x D := by
  unfold setDist
  exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact Metric.infDist_nonneg⟩ (⟨x, hx⟩ : Q)

theorem b2plat_le_setDist {Q D : Set (Spatial k)} (hQ : Q.Nonempty) {c : ℝ}
    (h : ∀ x ∈ Q, c ≤ Metric.infDist x D) : c ≤ setDist Q D := by
  have := hQ.to_subtype
  unfold setDist
  exact le_ciInf fun x => h x x.2

/-- The qualifying condition `4 diam Q ≤ dist(Q, D)`. -/
def b2plat_qual (D : Set (Spatial k)) (j : ℤ) (m : Fin k → ℤ) : Prop :=
  4 * Metric.diam (b2plat_cube j m) ≤ setDist (b2plat_cube j m) D

/-- A maximal qualifying cube: it qualifies, and no dyadic cube of strictly higher level
containing it qualifies. -/
def b2plat_maximal (D : Set (Spatial k)) (p : ℤ × (Fin k → ℤ)) : Prop :=
  b2plat_qual D p.1 p.2 ∧
    ∀ (j : ℤ) (m : Fin k → ℤ), p.1 < j → b2plat_cube p.1 p.2 ⊆ b2plat_cube j m →
      ¬ b2plat_qual D j m

theorem b2plat_qual_subset_compl {D : Set (Spatial k)} (hk : 1 ≤ k) {j : ℤ} {m : Fin k → ℤ}
    (hq : b2plat_qual D j m) : b2plat_cube j m ⊆ Dᶜ := by
  intro x hx hxD
  have h1 := b2plat_setDist_le (D := D) hx
  rw [Metric.infDist_zero_of_mem hxD] at h1
  have h2 := b2plat_diam_pos hk j m
  unfold b2plat_qual at hq
  linarith

/-- Upper Whitney inequality from the failed parent: `dist(Q, D) ≤ 10 diam Q`. -/
theorem b2plat_upper {D : Set (Spatial k)} {p : ℤ × (Fin k → ℤ)} (hp : b2plat_maximal D p) :
    setDist (b2plat_cube p.1 p.2) D ≤ 10 * Metric.diam (b2plat_cube p.1 p.2) := by
  obtain ⟨j, m⟩ := p
  have hsub := b2plat_subset_parent j m
  have hfail := hp.2 (j + 1) (fun α => m α / 2) (lt_add_one j) hsub
  unfold b2plat_qual at hfail
  rw [not_le] at hfail
  have hdP := b2plat_diam_parent j m
  have hx := b2plat_lo_mem j m
  have h1 : setDist (b2plat_cube j m) D ≤ Metric.infDist (b2plat_lo j m) D :=
    b2plat_setDist_le hx
  have h2 : Metric.infDist (b2plat_lo j m) D -
      Metric.diam (b2plat_cube (j + 1) (fun α => m α / 2)) ≤
      setDist (b2plat_cube (j + 1) (fun α => m α / 2)) D := by
    refine b2plat_le_setDist ⟨_, hsub hx⟩ fun y hy => ?_
    have h3 := Metric.infDist_le_infDist_add_dist (x := b2plat_lo j m) (y := y) (s := D)
    have h4 := Metric.dist_le_diam_of_mem (b2plat_isBounded _ _) (hsub hx) hy
    linarith
  rw [hdP] at h2 hfail
  show setDist (b2plat_cube j m) D ≤ 10 * Metric.diam (b2plat_cube j m)
  linarith

/-- Covering: every point off the closed set `D` lies in a maximal qualifying cube. -/
theorem b2plat_exists_maximal {D : Set (Spatial k)} (hk : 1 ≤ k) (hD : IsClosed D)
    (hDne : D.Nonempty) {x : Spatial k} (hx : x ∉ D) :
    ∃ p : ℤ × (Fin k → ℤ), b2plat_maximal D p ∧ x ∈ b2plat_cube p.1 p.2 := by
  have hδ : 0 < Metric.infDist x D := (hD.notMem_iff_infDist_pos hDne).1 hx
  have hsk : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hk)
  have hbdd : ∃ b : ℤ, ∀ j : ℤ,
      (∃ m, x ∈ b2plat_cube j m ∧ b2plat_qual D j m) → j ≤ b := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Metric.infDist x D) (one_lt_two : (1 : ℝ) < 2)
    refine ⟨n, fun j ⟨m, hxm, hq⟩ => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have h1 : (2 : ℝ) ^ (n : ℤ) ≤ (2 : ℝ) ^ j := zpow_le_zpow_right₀ one_le_two hlt.le
    rw [zpow_natCast] at h1
    have h2 := b2plat_setDist_le (D := D) hxm
    unfold b2plat_qual at hq
    rw [b2plat_diam] at hq
    have hs := b2plat_side_pos j
    have h3 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ j * √(k : ℝ) := le_mul_of_one_le_right hs.le hsk
    linarith
  have hinh : ∃ j : ℤ, ∃ m, x ∈ b2plat_cube j m ∧ b2plat_qual D j m := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (5 * √(k : ℝ) / Metric.infDist x D)
      (one_lt_two : (1 : ℝ) < 2)
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    rw [div_lt_iff₀ hδ] at hn
    have hs : (2 : ℝ) ^ (-(n : ℤ)) * √(k : ℝ) * 5 < Metric.infDist x D := by
      rw [zpow_neg, zpow_natCast, mul_assoc, inv_mul_lt_iff₀ h2n]
      linarith
    refine ⟨-(n : ℤ), _, b2plat_mem_floor_cube _ x, ?_⟩
    unfold b2plat_qual
    rw [b2plat_diam]
    refine b2plat_le_setDist ⟨x, b2plat_mem_floor_cube _ x⟩ fun y hy => ?_
    have h1 := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := D)
    have h2 := b2plat_dist_le (b2plat_mem_floor_cube (-(n : ℤ)) x) hy
    linarith
  obtain ⟨j0, ⟨m0, hxm0, hq0⟩, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
  refine ⟨(j0, m0), ⟨hq0, fun j m hj hsub hq => ?_⟩, hxm0⟩
  exact (not_lt.2 (hmax j ⟨m, hsub hxm0, hq⟩)) hj

/-- Two maximal cubes, the open box of the first meeting the closed second, are equal. -/
theorem b2plat_eq_of_maximal {D : Set (Spatial k)} {p q : ℤ × (Fin k → ℤ)}
    (hp : b2plat_maximal D p) (hq : b2plat_maximal D q) {x : Spatial k}
    (hx : ∀ α, (2 : ℝ) ^ p.1 * (p.2 α : ℝ) < x α ∧ x α < (2 : ℝ) ^ p.1 * ((p.2 α : ℝ) + 1))
    (hxq : x ∈ b2plat_cube q.1 q.2) : p = q := by
  obtain ⟨j1, m1⟩ := p
  obtain ⟨j2, m2⟩ := q
  dsimp only at hx hxq
  rcases lt_trichotomy j1 j2 with h | rfl | h
  · exact absurd hq.1 (hp.2 j2 m2 h (b2plat_subset_of_open_mem_le h.le hx hxq))
  · rw [b2plat_eq_of_open_mem hx hxq]
  · exact absurd hp.1 (hq.2 j1 m1 h (b2plat_subset_of_open_mem_ge h.le hx hxq))

/-- The interior of a maximal cube meets no other maximal cube. -/
theorem b2plat_eq_of_mem_interior {D : Set (Spatial k)} {p q : ℤ × (Fin k → ℤ)}
    (hp : b2plat_maximal D p) (hq : b2plat_maximal D q) {x : Spatial k}
    (hx : x ∈ interior (b2plat_cube p.1 p.2)) (hxq : x ∈ b2plat_cube q.1 q.2) : p = q :=
  b2plat_eq_of_maximal hp hq (b2plat_open_of_mem_interior hx) hxq

end ParabolicRectifiability.QuantitativeCharacterization
