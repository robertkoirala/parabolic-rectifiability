import ParabolicRectifiability.BetaP.Proofs.Carrier.CarrierStatements

/-! # Separated subsets of a lower-mass set

Proves `ccar_separated : CellsPackingStatement → CarrierSeparatedStatement` as
`ccar_separated_proof`, in implication form: the statement `CellsPackingStatement` is a
hypothesis.

The proof is the `p`-version of the quadratic `localNet_arith` and
`card_le_of_separated_densityCarrier`, on a general set `K` with the all-radius lower mass
`HasUniformLowerMass ν k a K`. For a finite `r`-separated `F ⊆ K ∩ P(q,R)`, `0 < r ≤ R ≤ 1`:

* `ρ = r/20`; closed cells `P̄(z_i,ρ)` (pairwise disjoint, since `2ρ < r`) of mass `≥ a ρ^k`;
  energy samples by `exists_mem_of_ae_of_measure_ne_zero`;
* barycenter cells with `radius = 10ρ = r/2`, `ε = 1/10`, cutoff `5ρ = r/4` for every index,
  synthetic weights `(5ρ)^k = (r/4)^k`, `A = 5^k/a` (`weight ≤ A ν(cell)` by the lower mass);
* the barycenters lie within `ρ` of the `z_i`, so the cutoff balls are pairwise disjoint
  (`r - 2ρ ≥ 10ρ`) and lie in `P(q,3R)`;
* `CellsPackingStatement` with `b = 1`, parent `P(q,3R)` gives
  `#F (r/4)^k ≤ Ct (1 + 5^k 2^{k+p} L^{p/2}/a) (3R)^k`;
* arithmetic (`ccarn_localNet_arith`): `5^k 2^{k+p} = 10^k 2^p`, `(3R)/(r/4) = 12 (R/r)`,
  `120^k ≤ 120^{n+2}`.

Constant (chosen after `n, p, Ct`, before `k, T, ν, L, a, K`): `C_s = Ct 2^p 120^(n+2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP.CarrierTree

open ParabolicRectifiability.Foundations

/-- The arithmetic of the separated-set bound (`p`-version of `localNet_arith`): from
`N (5(r/20))^k ≤ Ct (1 + 5^k/a · (2^k P₂) · M) (3R)^k` with `P₂ ≥ 1` (later `P₂ = 2^p`,
`M = L^{p/2}`), `N ≤ Ct P₂ 120^(n+2) (1 + M/a) (R/r)^k`. -/
theorem ccarn_localNet_arith {n k : ℕ} (hk : k ≤ n + 2) {Ct a M P2 R r N : ℝ} (hCt : 0 < Ct)
    (ha : 0 < a) (hM : 0 ≤ M) (hP2 : 1 ≤ P2) (hr : 0 < r) (hR : 0 < R)
    (hN : N * (5 * (r / 20)) ^ k ≤ Ct * (1 + 5 ^ k / a * (2 ^ k * P2) * M) * (3 * R) ^ k) :
    N ≤ Ct * P2 * 120 ^ (n + 2) * (1 + M / a) * (R / r) ^ k := by
  have h5 : 5 * (r / 20) = r / 4 := by ring
  rw [h5] at hN
  have hpos : 0 < (r / 4) ^ k := by positivity
  have hN' : N ≤ Ct * (1 + 5 ^ k / a * (2 ^ k * P2) * M) * (3 * R) ^ k / (r / 4) ^ k :=
    (le_div_iff₀ hpos).mpr hN
  have e1 : 3 * R / (r / 4) = 12 * (R / r) := by
    rw [div_eq_iff (by positivity), show 12 * (R / r) * (r / 4) = 3 * R * (r / r) by ring,
      div_self hr.ne', mul_one]
  have hP0 : 0 ≤ P2 := zero_le_one.trans hP2
  have hMa : 0 ≤ M / a := div_nonneg hM ha.le
  have hX : 1 + 5 ^ k / a * (2 ^ k * P2) * M ≤ 10 ^ k * P2 * (1 + M / a) := by
    have h10 : (1 : ℝ) ≤ 10 ^ k * P2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hP2
    have e10 : (10 : ℝ) ^ k = 5 ^ k * 2 ^ k := by
      rw [← mul_pow]
      norm_num
    have e : (5 : ℝ) ^ k / a * (2 ^ k * P2) * M = 10 ^ k * P2 * (M / a) := by
      rw [e10]
      ring
    rw [e, mul_add, mul_one]
    linarith
  have hRr : 0 ≤ (R / r) ^ k := pow_nonneg (div_nonneg hR.le hr.le) k
  have hLa : 0 ≤ 1 + M / a := by linarith
  have h120 : (120 : ℝ) ^ k ≤ 120 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) hk
  calc N ≤ Ct * (1 + 5 ^ k / a * (2 ^ k * P2) * M) * (3 * R) ^ k / (r / 4) ^ k := hN'
    _ = Ct * (1 + 5 ^ k / a * (2 ^ k * P2) * M) * (3 * R / (r / 4)) ^ k := by
        rw [div_pow (3 * R) (r / 4) k, mul_div_assoc]
    _ = Ct * (1 + 5 ^ k / a * (2 ^ k * P2) * M) * 12 ^ k * (R / r) ^ k := by
        rw [e1, mul_pow]; ring
    _ ≤ Ct * (10 ^ k * P2 * (1 + M / a)) * 12 ^ k * (R / r) ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hX hCt.le) (by positivity)) hRr
    _ = Ct * P2 * ((10 : ℝ) ^ k * 12 ^ k) * (1 + M / a) * (R / r) ^ k := by ring
    _ = Ct * P2 * 120 ^ k * (1 + M / a) * (R / r) ^ k := by
        rw [← mul_pow]
        norm_num
    _ ≤ Ct * P2 * 120 ^ (n + 2) * (1 + M / a) * (R / r) ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h120 (mul_nonneg hCt.le hP0)) hLa) hRr

/-- `2^{k+p} = 2^k 2^p` (real power with natural `k`). -/
theorem ccarn_two_rpow_add (k : ℕ) (p : ℝ) :
    (2 : ℝ) ^ ((k : ℝ) + p) = 2 ^ k * (2 : ℝ) ^ p := by
  rw [Real.rpow_add two_pos, Real.rpow_natCast]

/-- The separated-set bound on one lower-mass set (`p`-version of
`card_le_of_separated_densityCarrier`): a finite `r`-separated subset of
`K ∩ P(q,R)` has at most `Ct 2^p 120^(n+2) (1 + L^{p/2}/a) (R/r)^k` points. -/
theorem ccarn_card_le_of_separated (hcp : CellsPackingStatement) {n : ℕ} {p Ct : ℝ}
    (hp : 2 ≤ p) (hCt : 0 < Ct) (htrunc : ActiveRadiusPackingTruncatedBound n p Ct)
    {k : ℕ} {T : FamilyKind} (hk : 1 ≤ k) (hkn : k < n + 2) (hT : Nonempty (Models n k T))
    (ν : Measure (Space n)) [IsFiniteMeasure ν] {L a : ℝ} (hL : 0 ≤ L) (ha : 0 < a)
    (hae : ∀ᵐ z ∂ν, allScaleEnergyP ν k T p z ≤ ENNReal.ofReal L)
    {K : Set (Space n)} (hlow : HasUniformLowerMass ν k a K)
    (q : Space n) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hR1 : R ≤ 1) (F : Finset (Space n))
    (hF : (↑F : Set (Space n)) ⊆ K ∩ Metric.ball q R)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → r ≤ dist x y) :
    (F.card : ℝ) ≤ Ct * (2 : ℝ) ^ p * 120 ^ (n + 2) * (1 + L ^ (p / 2) / a) * (R / r) ^ k := by
  classical
  have hR : 0 < R := hr.trans_le hrR
  obtain ⟨zz, hzz_inj, hzzF⟩ : ∃ zz : Fin F.card → Space n, Function.Injective zz ∧
      ∀ i, zz i ∈ F :=
    ⟨fun i => (F.equivFin.symm i : Space n),
      fun i j h => F.equivFin.symm.injective (Subtype.ext h), fun i => (F.equivFin.symm i).2⟩
  set ρ := r / 20 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρdef]; linarith
  have hzzK : ∀ i, zz i ∈ K := fun i => (hF (hzzF i)).1
  have hzzq : ∀ i, zz i ∈ Metric.ball q R := fun i => (hF (hzzF i)).2
  have hsepz : ∀ i j, i ≠ j → r ≤ dist (zz i) (zz j) :=
    fun i j hij => hsep _ (hzzF i) _ (hzzF j) (hzz_inj.ne hij)
  have hmass : ∀ i, ENNReal.ofReal (a * ρ ^ k) ≤ ν (Metric.closedBall (zz i) ρ) :=
    fun i => hlow (zz i) (hzzK i) ρ hρ hρ1
  have hne0 : ∀ i, ν (Metric.closedBall (zz i) ρ) ≠ 0 := fun i =>
    (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) (hmass i)).ne'
  have htoReal : ∀ i, a * ρ ^ k ≤ (ν (Metric.closedBall (zz i) ρ)).toReal := fun i =>
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp (hmass i)
  have hsample : ∀ i, ∃ y ∈ Metric.closedBall (zz i) ρ, allScaleEnergyP ν k T p y ≤
      ENNReal.ofReal L := fun i => exists_mem_of_ae_of_measure_ne_zero hae (hne0 i)
  choose y hy hyE using hsample
  obtain ⟨D, hDcenter, hDradius, hDε, hDsample, hDweight, hDA⟩ :
      ∃ D : FiniteBarycenterCells ν (Fin F.card), (∀ i, D.center i = zz i) ∧
        (∀ i, D.radius i = 10 * ρ) ∧ D.ε = 1 / 10 ∧ (∀ i, D.sample i = y i) ∧
        (∀ i, D.weight i = (5 * ρ) ^ k) ∧ D.A = 5 ^ k / a :=
    ⟨{ cell := fun i => Metric.closedBall (zz i) ρ
       measurable_cell := fun _ => measurableSet_closedBall
       disjoint_cell := fun i j hij => Metric.closedBall_disjoint_closedBall (by
         have := hsepz i j hij
         rw [hρdef]
         linarith)
       mass_ne_zero := hne0
       mass_ne_top := fun _ => measure_ne_top _ _
       center := zz
       radius := fun _ => 10 * ρ
       radius_pos := fun _ => by positivity
       ε := 1 / 10
       ε_pos := by norm_num
       ε_le := le_rfl
       cell_subset := fun _ => Metric.closedBall_subset_closedBall (le_of_eq (by ring))
       sample := y
       sample_mem := hy
       weight := fun _ => (5 * ρ) ^ k
       weight_pos := fun _ => by positivity
       A := 5 ^ k / a
       A_nonneg := by positivity
       weight_le := fun i => by
         calc (5 * ρ) ^ k = 5 ^ k / a * (a * ρ ^ k) := by
               rw [div_mul_eq_mul_div, eq_div_iff ha.ne', mul_pow]
               ring
           _ ≤ 5 ^ k / a * (ν (Metric.closedBall (zz i) ρ)).toReal :=
               mul_le_mul_of_nonneg_left (htoReal i) (by positivity) },
      fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  have hbary : ∀ i, dist (D.barycenter i) (zz i) ≤ ρ := by
    intro i
    have h := D.barycenter_mem_closedBall i
    rw [hDcenter, hDradius, hDε, Metric.mem_closedBall] at h
    linarith
  have hcut : ∀ i, D.cutoff i = 5 * ρ := by
    intro i
    show D.radius i / 2 = 5 * ρ
    rw [hDradius]
    ring
  have hball : ∀ i, Metric.ball (D.barycenter i) (D.cutoff i) ⊆ Metric.ball q (3 * R) := by
    intro i w hw
    rw [hcut] at hw
    have h0 : dist w (D.barycenter i) < 5 * ρ := hw
    have h1 := hbary i
    have h2 : dist (zz i) q < R := hzzq i
    rw [Metric.mem_ball]
    have := dist_triangle4 w (D.barycenter i) (zz i) q
    rw [hρdef] at h0 h1
    linarith
  have hdisjb : ∀ i j, i ≠ j → Disjoint (Metric.ball (D.barycenter i) (D.cutoff i))
      (Metric.ball (D.barycenter j) (D.cutoff j)) := by
    intro i j hij
    rw [hcut, hcut]
    apply Metric.ball_disjoint_ball
    have h1 := hbary i
    have h2 := hbary j
    have h3 := hsepz i j hij
    have h4 := dist_triangle4 (zz i) (D.barycenter i) (D.barycenter j) (zz j)
    rw [dist_comm (zz i) (D.barycenter i)] at h4
    rw [hρdef] at h1 h2 ⊢
    linarith
  have hw : ∀ i, D.weight i ≤ 1 * D.cutoff i ^ k := by
    intro i
    rw [hDweight, hcut, one_mul]
  have hsampleE : ∀ i, allScaleEnergyP ν k T p (D.sample i) ≤ ENNReal.ofReal L := by
    intro i
    rw [hDsample]
    exact hyE i
  have key := hcp n p Ct hp htrunc k T hk hkn hT ν F.card D L hL hsampleE q (3 * R) 1
    (by positivity) one_pos hball hdisjb hw
  simp only [hDweight, hDA] at key
  have hM : 0 ≤ L ^ (p / 2) := Real.rpow_nonneg hL _
  have hP2 : (1 : ℝ) ≤ (2 : ℝ) ^ p := Real.one_le_rpow (by norm_num) (by linarith)
  rw [ccarn_two_rpow_add] at key
  rw [ofReal_sum_const_fin, ENNReal.ofReal_le_ofReal_iff (by positivity :
    (0 : ℝ) ≤ Ct * (1 + 5 ^ k / a * (2 ^ k * (2 : ℝ) ^ p) * L ^ (p / 2)) * (3 * R) ^ k)] at key
  exact ccarn_localNet_arith (by omega) hCt ha hM hP2 hr hR key

/-- **Separated subsets of a lower-mass set** (`ccar_separated`), with the
constant `C_s = Ct 2^p 120^(n+2)`. -/
theorem ccar_separated_proof : CellsPackingStatement → CarrierSeparatedStatement := by
  intro hcp n _hn p hp Ct hCt htrunc
  refine ⟨Ct * (2 : ℝ) ^ p * 120 ^ (n + 2), by positivity, ?_⟩
  intro k hk hkn T hT ν hfin L a hL ha hae K hlow q R r _hR hR1 hr hrR F hF hsep
  exact ccarn_card_le_of_separated hcp hp hCt htrunc hk hkn hT ν hL ha hae hlow q hr hrR hR1
    F hF hsep

end ParabolicRectifiability.BetaP.CarrierTree
