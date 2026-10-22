import ParabolicRectifiability.BetaP.Proofs.Carrier.CarrierStatements

/-! # The loss of the lower-mass carrier

Proves `ccar_loss : CellsPackingStatement → CarrierLossStatement` as `ccar_loss_proof`, in
implication form: the statement `CellsPackingStatement` is a hypothesis.

The proof is the `p`-version of the quadratic `sum_deficient_cells_le` and
`measure_compl_densityCarrier_le`:

* selection (reused unchanged): `ae_largeDimension`, `exists_deficient_radius` (first doubling
  scale, doubling constant `50^(n+3)`, selected radius `r ≤ 1/5`), Mathlib's
  `Vitali.exists_disjoint_subfamily_covering_enlargement` (enlargement `5`), and
  `exists_mem_of_ae_of_measure_ne_zero` for the energy samples;
* for every finite subfamily: barycenter cells `P(g_i, r_i/10)` (`ε = 1/10`), weights
  `m_i = ν(P(g_i,r_i/10))`, `A = 1`, cutoff `ρ_i = r_i/2`, cutoff balls
  `P(c_i,ρ_i) ⊆ P(g_i,r_i) ⊆ P(c,1)` (`1/16 + 1/5 < 1`) pairwise disjoint,
  `m_i < a(5r_i)^k = 10^k a ρ_i^k`; the hypothesis `CellsPackingStatement` with `A = 1`,
  `b = 10^k a`, `R = 1` gives `Σ m_i ≤ Ct (10^k a + 2^{k+p} L^{p/2})`
  (`ccarl_sum_deficient_cells_le`);
* countable summation, doubling `ν(P(g_i,5r_i)) ≤ 50^(n+3) m_i`, and the cover of `(K_a)ᶜ` by
  `(supp ν)ᶜ`, the non-large-dimension null set and the enlarged balls
  (`ccarl_measure_compl_densityCarrier_le`).

Constant (chosen after `n, p, Ct`, before `k, T, ν, L, a`):
`C_l = 50^(n+3) Ct (10^(n+1) + 2^(n+1+p))`.

The countable selection witness (masses, displacement of the barycenters, disjointness,
containment) is constructed inside the proof and is not exported.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP.CarrierTree

open ParabolicRectifiability.Foundations

/-- The finite-subfamily bound for deficient cells (`p`-version of
`sum_deficient_cells_le`): for disjoint deficient balls `P(g_i, r_i)` with `r_i ≤ 1/5` centred in
`P̄(c,1/16)`, `Σ ν(P(g_i,r_i/10)) ≤ Ct (10^k a + 2^{k+p} L^{p/2})`, from
`CellsPackingStatement` with `A = 1`, `b = 10^k a`, `R = 1`. -/
theorem ccarl_sum_deficient_cells_le (hpack : CellsPackingStatement) {n : ℕ} {p Ct : ℝ}
    (hp : 2 ≤ p) (htr : ActiveRadiusPackingTruncatedBound n p Ct)
    {k : ℕ} {T : FamilyKind} (hk : 1 ≤ k) (hkn : k < n + 2) (hT : Nonempty (Models n k T))
    (ν : Measure (Space n)) [IsFiniteMeasure ν] (c : Space n) {L a : ℝ} (hL : 0 ≤ L)
    (ha : 0 < a) (henergy : ∀ᵐ z ∂ν, allScaleEnergyP ν k T p z ≤ ENNReal.ofReal L)
    {l : ℕ} (g : Fin l → Space n) (r : Fin l → ℝ) (hr : ∀ i, 0 < r i) (hr5 : ∀ i, r i ≤ 1 / 5)
    (hg : ∀ i, g i ∈ Metric.closedBall c (1 / 16))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (g i) (r i)) (Metric.ball (g j) (r j)))
    (hpos : ∀ i, 0 < ν (Metric.ball (g i) (r i / 10)))
    (hsmall : ∀ i, ν (Metric.ball (g i) (r i / 10)) < ENNReal.ofReal (a * (5 * r i) ^ k)) :
    ∑ i, ν (Metric.ball (g i) (r i / 10)) ≤
      ENNReal.ofReal (Ct * (10 ^ k * a + 1 * (2 : ℝ) ^ ((k : ℝ) + p) * L ^ (p / 2)) * 1 ^ k) := by
  have hsample : ∀ i, ∃ y ∈ Metric.ball (g i) (r i / 10), allScaleEnergyP ν k T p y ≤
      ENNReal.ofReal L := fun i => exists_mem_of_ae_of_measure_ne_zero henergy (hpos i).ne'
  choose y hy hyE using hsample
  have hdisjc : Pairwise fun i j => Disjoint (Metric.ball (g i) (r i / 10))
      (Metric.ball (g j) (r j / 10)) := fun i j hij =>
    (hdisj i j hij).mono (Metric.ball_subset_ball (by linarith [hr i]))
      (Metric.ball_subset_ball (by linarith [hr j]))
  obtain ⟨D, hDcenter, hDradius, hDε, hDsample, hDweight, hDA⟩ :
      ∃ D : FiniteBarycenterCells ν (Fin l), (∀ i, D.center i = g i) ∧
        (∀ i, D.radius i = r i) ∧ D.ε = 1 / 10 ∧ (∀ i, D.sample i = y i) ∧
        (∀ i, D.weight i = (ν (Metric.ball (g i) (r i / 10))).toReal) ∧ D.A = 1 :=
    ⟨{ cell := fun i => Metric.ball (g i) (r i / 10)
       measurable_cell := fun _ => measurableSet_ball
       disjoint_cell := hdisjc
       mass_ne_zero := fun i => (hpos i).ne'
       mass_ne_top := fun _ => measure_ne_top _ _
       center := g
       radius := r
       radius_pos := hr
       ε := 1 / 10
       ε_pos := by norm_num
       ε_le := le_rfl
       cell_subset := fun i => Metric.ball_subset_closedBall.trans
         (Metric.closedBall_subset_closedBall (le_of_eq (by ring)))
       sample := y
       sample_mem := hy
       weight := fun i => (ν (Metric.ball (g i) (r i / 10))).toReal
       weight_pos := fun i => ENNReal.toReal_pos (hpos i).ne' (measure_ne_top _ _)
       A := 1
       A_nonneg := zero_le_one
       weight_le := fun i => by rw [one_mul] },
      fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  have hbary : ∀ i, dist (D.barycenter i) (g i) ≤ r i / 10 := by
    intro i
    have h := D.barycenter_mem_closedBall i
    rw [hDcenter, hDradius, hDε, Metric.mem_closedBall] at h
    linarith
  have hcut : ∀ i, D.cutoff i = r i / 2 := by
    intro i
    show D.radius i / 2 = r i / 2
    rw [hDradius]
  have hsub : ∀ i, Metric.ball (D.barycenter i) (D.cutoff i) ⊆ Metric.ball (g i) (r i) := by
    intro i w hw
    rw [hcut] at hw
    have h1 : dist w (D.barycenter i) < r i / 2 := hw
    rw [Metric.mem_ball]
    linarith [dist_triangle w (D.barycenter i) (g i), hbary i, hr i]
  have hball : ∀ i, Metric.ball (D.barycenter i) (D.cutoff i) ⊆ Metric.ball c 1 := by
    intro i w hw
    have h1 : dist w (g i) < r i := hsub i hw
    have h2 : dist (g i) c ≤ 1 / 16 := hg i
    rw [Metric.mem_ball]
    linarith [dist_triangle w (g i) c, hr5 i]
  have hdisjb : ∀ i j, i ≠ j → Disjoint (Metric.ball (D.barycenter i) (D.cutoff i))
      (Metric.ball (D.barycenter j) (D.cutoff j)) := fun i j hij =>
    (hdisj i j hij).mono (hsub i) (hsub j)
  have hw : ∀ i, D.weight i ≤ 10 ^ k * a * D.cutoff i ^ k := by
    intro i
    rw [hDweight, hcut]
    have h1 := (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).mp (hsmall i)
    have h2 : a * (5 * r i) ^ k = 10 ^ k * a * (r i / 2) ^ k := by
      rw [show (5 : ℝ) * r i = 10 * (r i / 2) by ring, mul_pow]
      ring
    linarith
  have hsampleE : ∀ i, allScaleEnergyP ν k T p (D.sample i) ≤ ENNReal.ofReal L := by
    intro i
    rw [hDsample]
    exact hyE i
  have key := hpack n p Ct hp htr k T hk hkn hT ν l D L hL hsampleE c 1 (10 ^ k * a) one_pos
    (by positivity) hball hdisjb hw
  simp only [hDweight, hDA, ENNReal.ofReal_toReal (measure_ne_top ν _)] at key
  exact key

/-- The real arithmetic of the constant: `50^(n+3) Ct (10^k a + 2^{k+p} L^{p/2}) ≤
50^(n+3) Ct (10^(n+1) + 2^(n+1+p)) (a + L^{p/2})` for `k ≤ n + 1`. -/
theorem ccarl_arith {n k : ℕ} (hkn : k < n + 2) {p Ct L a : ℝ} (hCt : 0 < Ct) (hL : 0 ≤ L)
    (ha : 0 < a) :
    50 ^ (n + 3) * (Ct * (10 ^ k * a + 1 * (2 : ℝ) ^ ((k : ℝ) + p) * L ^ (p / 2)) * 1 ^ k) ≤
      50 ^ (n + 3) * Ct * (10 ^ (n + 1) + (2 : ℝ) ^ ((n : ℝ) + 1 + p)) * (a + L ^ (p / 2)) := by
  have hk1 : k ≤ n + 1 := by omega
  have hkR : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hk1
  have hLp : 0 ≤ L ^ (p / 2) := Real.rpow_nonneg hL _
  have h10 : (10 : ℝ) ^ k ≤ 10 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) hk1
  have h2 : (2 : ℝ) ^ ((k : ℝ) + p) ≤ (2 : ℝ) ^ ((n : ℝ) + 1 + p) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h10' : (0 : ℝ) ≤ 10 ^ (n + 1) := by positivity
  have h2' : (0 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + 1 + p) := Real.rpow_nonneg (by norm_num) _
  have hinner : 10 ^ k * a + 1 * (2 : ℝ) ^ ((k : ℝ) + p) * L ^ (p / 2) ≤
      (10 ^ (n + 1) + (2 : ℝ) ^ ((n : ℝ) + 1 + p)) * (a + L ^ (p / 2)) := by
    nlinarith [mul_le_mul_of_nonneg_right h10 ha.le, mul_le_mul_of_nonneg_right h2 hLp,
      mul_nonneg h10' hLp, mul_nonneg h2' ha.le]
  rw [one_pow, mul_one]
  have h50 : (0 : ℝ) ≤ 50 ^ (n + 3) := by positivity
  calc 50 ^ (n + 3) * (Ct * (10 ^ k * a + 1 * (2 : ℝ) ^ ((k : ℝ) + p) * L ^ (p / 2)))
      ≤ 50 ^ (n + 3) * (Ct * ((10 ^ (n + 1) + (2 : ℝ) ^ ((n : ℝ) + 1 + p)) *
          (a + L ^ (p / 2)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hCt.le) h50
    _ = _ := by ring

/-- The loss of the lower-mass carrier (`p`-version of `measure_compl_densityCarrier_le`):
`ν(X ∖ K_a) ≤ 50^(n+3) Ct (10^(n+1) + 2^(n+1+p)) (a + L^{p/2})`. The countable selection
(deficient radii, Vitali subfamily) is constructed here and not exported. -/
theorem ccarl_measure_compl_densityCarrier_le (hpack : CellsPackingStatement) {n : ℕ}
    {p Ct : ℝ} (hp : 2 ≤ p) (htr : ActiveRadiusPackingTruncatedBound n p Ct) (hCt : 0 < Ct)
    {k : ℕ} {T : FamilyKind} (hk : 1 ≤ k) (hkn : k < n + 2) (hT : Nonempty (Models n k T))
    (ν : Measure (Space n)) [IsFiniteMeasure ν] (c : Space n)
    (hsupp : ν.support ⊆ Metric.closedBall c (1 / 16)) {L a : ℝ} (hL : 0 ≤ L) (ha : 0 < a)
    (henergy : ∀ᵐ z ∂ν, allScaleEnergyP ν k T p z ≤ ENNReal.ofReal L) :
    ν (densityCarrier ν k a)ᶜ ≤
      ENNReal.ofReal (50 ^ (n + 3) * Ct * (10 ^ (n + 1) + (2 : ℝ) ^ ((n : ℝ) + 1 + p)) *
        (a + L ^ (p / 2))) := by
  classical
  have hLD : ∀ᵐ z ∂ν, HasLargeDimension ν z := ae_largeDimension ν c
    (hsupp.trans (Metric.closedBall_subset_closedBall (by norm_num)))
  obtain ⟨G, hG⟩ : ∃ G : Set (Space n), G = {z | z ∈ ν.support ∧
      z ∉ densityCarrier ν k a ∧ HasLargeDimension ν z} := ⟨_, rfl⟩
  have hmemG : ∀ z, z ∈ G ↔ z ∈ ν.support ∧ z ∉ densityCarrier ν k a ∧ HasLargeDimension ν z := by
    intro z
    rw [hG]
    rfl
  have hrad : ∀ z : G, ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 5 ∧
      ν (Metric.ball (z : Space n) (5 * r)) ≤
        ENNReal.ofReal (50 ^ (n + 3)) * ν (Metric.ball (z : Space n) (r / 10)) ∧
      ν (Metric.ball (z : Space n) (r / 10)) < ENNReal.ofReal (a * (5 * r) ^ k) ∧
      0 < ν (Metric.ball (z : Space n) (r / 10)) := by
    intro z
    have hz := (hmemG z).mp z.2
    exact exists_deficient_radius ν (by omega) ha hz.1 hz.2.1 hz.2.2
  choose rad hrad0 hrad1 hdoub hsmall hpos using hrad
  obtain ⟨u, -, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun z : G => Metric.ball (z : Space n) (rad z)) univ rad 2 one_lt_two
    (fun z _ => (hrad0 z).le) (1 / 5) (fun z _ => hrad1 z)
    (fun z _ => ⟨z, Metric.mem_ball_self (hrad0 z)⟩)
  have hucount : u.Countable := hudisj.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
    (fun z _ => ⟨z, Metric.mem_ball_self (hrad0 z)⟩)
  -- finite subfamilies
  have hfin : ∀ s : Finset u, ∑ x ∈ s, ν (Metric.ball ((x : G) : Space n) (rad x / 10)) ≤
      ENNReal.ofReal (Ct * (10 ^ k * a + 1 * (2 : ℝ) ^ ((k : ℝ) + p) * L ^ (p / 2)) * 1 ^ k) := by
    intro s
    obtain ⟨e, -⟩ : ∃ e : Fin s.card ≃ s, True := ⟨s.equivFin.symm, trivial⟩
    have hinj : ∀ i j, i ≠ j → ((e i : u) : G) ≠ ((e j : u) : G) := by
      intro i j hij h
      exact hij (e.injective (Subtype.ext (Subtype.ext h)))
    have hsum := ccarl_sum_deficient_cells_le hpack hp htr hk hkn hT ν c hL ha henergy
      (fun i => (((e i : u) : G) : Space n)) (fun i => rad ((e i : u) : G))
      (fun i => hrad0 _) (fun i => hrad1 _)
      (fun i => hsupp ((hmemG _).mp ((e i : u) : G).2).1)
      (fun i j hij => hudisj (e i : u).2 (e j : u).2 (hinj i j hij))
      (fun i => hpos _) (fun i => hsmall _)
    rw [← Finset.sum_coe_sort s, ← Equiv.sum_comp e]
    exact hsum
  have htsum : ∑' x : u, ν (Metric.ball ((x : G) : Space n) (rad x / 10)) ≤
      ENNReal.ofReal (Ct * (10 ^ k * a + 1 * (2 : ℝ) ^ ((k : ℝ) + p) * L ^ (p / 2)) * 1 ^ k) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le hfin
  -- the cover
  have hcover : (densityCarrier ν k a)ᶜ ⊆ (ν.supportᶜ ∪ {z | ¬ HasLargeDimension ν z}) ∪
      ⋃ x ∈ u, Metric.ball ((x : G) : Space n) (5 * rad x) := by
    intro z hz
    by_cases hzs : z ∈ ν.support
    swap
    · exact Or.inl (Or.inl hzs)
    by_cases hzl : HasLargeDimension ν z
    swap
    · exact Or.inl (Or.inr hzl)
    right
    have hzG : z ∈ G := (hmemG z).mpr ⟨hzs, hz, hzl⟩
    obtain ⟨b, hbu, ⟨w, hw1, hw2⟩, hrb⟩ := hucov ⟨z, hzG⟩ (mem_univ _)
    refine mem_iUnion₂.mpr ⟨b, hbu, ?_⟩
    have h1 : dist w z < rad ⟨z, hzG⟩ := hw1
    have h2 : dist w ((b : G) : Space n) < rad b := hw2
    rw [Metric.mem_ball]
    linarith [dist_triangle z w ((b : G) : Space n), dist_comm w z, hrad0 b]
  have hbad : ν {z | ¬ HasLargeDimension ν z} = 0 := ae_iff.mp hLD
  calc ν (densityCarrier ν k a)ᶜ
      ≤ ν ((ν.supportᶜ ∪ {z | ¬ HasLargeDimension ν z}) ∪
          ⋃ x ∈ u, Metric.ball ((x : G) : Space n) (5 * rad x)) := measure_mono hcover
    _ ≤ ν (ν.supportᶜ ∪ {z | ¬ HasLargeDimension ν z}) +
          ν (⋃ x ∈ u, Metric.ball ((x : G) : Space n) (5 * rad x)) := measure_union_le _ _
    _ = ν (⋃ x ∈ u, Metric.ball ((x : G) : Space n) (5 * rad x)) := by
        rw [measure_union_null Measure.measure_compl_support hbad, zero_add]
    _ ≤ ∑' x : u, ν (Metric.ball ((x : G) : Space n) (5 * rad x)) :=
        measure_biUnion_le ν hucount _
    _ ≤ ∑' x : u, ENNReal.ofReal (50 ^ (n + 3)) *
          ν (Metric.ball ((x : G) : Space n) (rad x / 10)) :=
        ENNReal.tsum_le_tsum fun x => hdoub x
    _ = ENNReal.ofReal (50 ^ (n + 3)) *
          ∑' x : u, ν (Metric.ball ((x : G) : Space n) (rad x / 10)) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (50 ^ (n + 3)) *
          ENNReal.ofReal (Ct * (10 ^ k * a + 1 * (2 : ℝ) ^ ((k : ℝ) + p) * L ^ (p / 2)) *
            1 ^ k) :=
        mul_le_mul_right htsum _
    _ = ENNReal.ofReal (50 ^ (n + 3) *
          (Ct * (10 ^ k * a + 1 * (2 : ℝ) ^ ((k : ℝ) + p) * L ^ (p / 2)) * 1 ^ k)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (ccarl_arith hkn hCt hL ha)

/-- **Loss of the lower-mass carrier** (`ccar_loss`): the loss of the lower-mass carrier from the
cells packing statement, with `C_l = 50^(n+3) Ct (10^(n+1) + 2^(n+1+p))`. -/
theorem ccar_loss_proof : CellsPackingStatement → CarrierLossStatement := by
  intro hpack n _hn p hp Ct hCt htr
  refine ⟨50 ^ (n + 3) * Ct * (10 ^ (n + 1) + (2 : ℝ) ^ ((n : ℝ) + 1 + p)),
    mul_pos (mul_pos (by positivity) hCt)
      (add_pos (by positivity) (Real.rpow_pos_of_pos (by norm_num) _)), ?_⟩
  intro k hk hkn T hT ν hfin c hsupp L a hL ha henergy
  have := hfin
  exact ccarl_measure_compl_densityCarrier_le hpack hp htr hCt hk hkn hT ν c hsupp hL ha henergy

end ParabolicRectifiability.BetaP.CarrierTree
