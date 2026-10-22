import ParabolicRectifiability.Measure.Neck.RegionCore.KeptSets

/-!
# Core lower mass and core domination

Proofs of two statements about the core of the source construction:

* `core_lower_of_construction_proof` (`core_lower_of_construction`):
  for `0 < r ≤ R` choose the stage `j ≥ 1` with `6 r_j ≤ r < 60 r_j`; a core point lies within
  `r_j` of a continuing candidate `g` of stage `j`, whose noncollapse test gives
  `ν(P(g, 5 r_j)) ≥ a (5 r_j)^k` (`measure_ball_ge_of_rankEigenvalue` at
  positive rank; the mass test itself at vertical rank zero, where `k = 2`). Hence
  `ν(P(z,r)) ≥ a (r/12)^k ≥ a r^k / L` for `L ≥ 12^{n+2}`. The bound is for the original
  source.
* `core_domination_of_construction_proof` (`core_domination_of_construction`):
  the general comparison `ms4_hausdorffP_restrict_le_of_lower` (Vitali's five-times covering
  lemma for closed balls, countability of disjoint open balls, Hausdorff measure as a limit of
  coverings with vanishing diameter, outer regularity of the finite source) turns the lower
  mass bound into `H^k_P ⌞ C₀ ≤ (L/a) ν` for `L ≥ 10^{n+2} C_16`, where `C_16` is the constant of the lower mass bound.

Helper names carry the prefix `ms4_`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace NeckType

theorem ms4_four_le_rootRadius (T : NeckType) {R : ℝ} (hR : 0 < R) : 4 * R ≤ T.rootRadius R := by
  cases T
  · show 4 * R ≤ 8 * R
    linarith
  · show 4 * R ≤ 4 * R
    exact le_rfl

/-- At vertical rank zero an available type has `k = 2`. -/
theorem ms4_eq_two_of_rank_eq_zero {T : NeckType} {n k : ℕ} (hT : T.Available n k)
    (h0 : T.rank k = 0) : k = 2 := by
  cases T with
  | horizontal =>
    have h1 : 1 ≤ k := hT.1
    have h2 : k = 0 := h0
    omega
  | vertical =>
    have h1 : 2 ≤ k := hT.1
    have h2 : k - 2 = 0 := h0
    omega

end NeckType

namespace SourceSetup

variable {n : ℕ} (P : SourceSetup n) (T : NeckType)

/-- For `0 < r ≤ R` there is a stage `j ≥ 1` with `6 r_j ≤ r < 60 r_j`. -/
theorem ms4_exists_stage (hR : 0 < P.R) {r : ℝ} (hr : 0 < r) (hrR : r ≤ P.R) :
    ∃ j, 1 ≤ j ∧ 6 * P.scale T j ≤ r ∧ r < 60 * P.scale T j := by
  classical
  have hex : ∃ j, 6 * P.scale T j ≤ r := by
    obtain ⟨m, hm⟩ := ((P.ms4_tendsto_scale T).eventually
      (gt_mem_nhds (show (0 : ℝ) < r / 6 by positivity))).exists
    exact ⟨m + 1, by linarith⟩
  have hpj : 6 * P.scale T (Nat.find hex) ≤ r := Nat.find_spec hex
  have hj0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, ms4_scale_zero] at hpj
    have := T.ms4_four_le_rootRadius hR
    linarith
  refine ⟨Nat.find hex, Nat.one_le_iff_ne_zero.2 hj0, hpj, ?_⟩
  have hmin : ¬ 6 * P.scale T (Nat.find hex - 1) ≤ r := Nat.find_min hex (by omega)
  have hsucc : P.scale T (Nat.find hex) = P.scale T (Nat.find hex - 1) / 10 := by
    rw [← ms4_scale_succ]
    congr 1
    omega
  rw [hsucc]
  have hmin' := not_le.1 hmin
  linarith

end SourceSetup

namespace ConstructionData

variable {n k : ℕ} {T : NeckType} {D : ConstructionData n k T} {P : SourceSetup n}

/-- The noncollapse test of a continuing candidate gives `ν(P(g, 5 r_j)) ≥ a (5 r_j)^k`. -/
theorem ms4_mass_of_continuing (hT : T.Available n k) {j i : ℕ}
    (hcont : D.IsContinuing P j i) :
    ENNReal.ofReal (P.a * (5 * P.scale T j) ^ k) ≤
      P.ν (Metric.ball (D.cand j i) (5 * P.scale T j)) := by
  rcases hcont with ⟨_, hρ, hlam⟩ | ⟨h0, hm⟩
  · have := P.finite
    exact SpatialSource.measure_ball_ge_of_rankEigenvalue P.ν (D.cand j i) hρ hlam
  · obtain rfl := NeckType.ms4_eq_two_of_rank_eq_zero hT h0
    exact hm

end ConstructionData

/-- **`core_lower_of_construction`**: lower mass of the original source at the core,
with `C = 12^{n+2}`. -/
theorem core_lower_of_construction_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T),
      T.Available n k → k < n + 2 → P.IsAdmissible → D.IsSourceConstruction P →
      ∀ L : ℝ, C ≤ L → ∀ z ∈ D.core P, ∀ r : ℝ, 0 < r → r ≤ P.R →
        ENNReal.ofReal (P.a * r ^ k / L) ≤ P.ν (Metric.ball z r) := by
  refine ⟨12 ^ (n + 2), by positivity, ?_⟩
  intro k T P D hT hk hP hD L hL z hz r hr hrR
  have hR := hP.R_pos
  have hz' : z ∈ D.coreLimit P := by
    rw [← ConstructionData.ms4_core_eq_coreLimit hD hR]
    exact hz
  obtain ⟨j, hj1, h6, h60⟩ := P.ms4_exists_stage T hR hr hrR
  obtain ⟨i, -, hcont, hdist⟩ :=
    ConstructionData.ms4_exists_cont_near hj1 (mem_iInter.1 hz' j)
  have hrj := P.scale_pos T hR j
  have hdist' : dist z (D.cand j i) ≤ P.scale T j :=
    hdist.trans (mul_le_of_le_one_left hrj.le T.sourceSeparation_le_one)
  have hsub : Metric.ball (D.cand j i) (5 * P.scale T j) ⊆ Metric.ball z r := by
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    have := dist_triangle y (D.cand j i) z
    rw [dist_comm (D.cand j i) z] at this
    linarith
  refine le_trans ?_ ((ConstructionData.ms4_mass_of_continuing hT hcont).trans (measure_mono hsub))
  apply ENNReal.ofReal_le_ofReal
  have h12 : (12 : ℝ) ^ k ≤ L :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by omega : k ≤ n + 2)) hL
  have hpos12 : (0 : ℝ) < 12 ^ k := by positivity
  have hrk : (r / 12) ^ k ≤ (5 * P.scale T j) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  have ha := hP.a_pos
  calc P.a * r ^ k / L ≤ P.a * r ^ k / 12 ^ k :=
        div_le_div_of_nonneg_left (by positivity) hpos12 h12
    _ = P.a * (r / 12) ^ k := by rw [div_pow]; ring
    _ ≤ P.a * (5 * P.scale T j) ^ k := mul_le_mul_of_nonneg_left hrk ha.le

/-! ## Lower mass bounds dominate Hausdorff measure -/

/-- Covering half of `core_domination_of_construction`: if `ν(P(z,r)) ≥ c r^k` for `z ∈ K` and `0 < r ≤ R`,
then `H^k_P(E) ≤ (10^k / c) ν(U)` for `E ⊆ K ∩ U`, `U` open. Vitali's covering lemma at every
scale `δ_m = R/(m+1)` gives disjoint balls `P(z_i, ρ_i) ⊆ U` with `E ⊆ ⋃ closedBall(z_i, 5ρ_i)`,
and `(10 ρ_i)^k ≤ (10^k/c) ν(P(z_i, ρ_i))`. -/
theorem ms4_hausdorffP_le_of_lower_of_isOpen {n k : ℕ} (ν : Measure (Space n))
    (K : Set (Space n)) {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hlow : ∀ z ∈ K, ∀ r : ℝ, 0 < r → r ≤ R → ENNReal.ofReal (c * r ^ k) ≤ ν (Metric.ball z r))
    {E U : Set (Space n)} (hEK : E ⊆ K) (hEU : E ⊆ U) (hU : IsOpen U) :
    hausdorffP n k E ≤ ENNReal.ofReal (10 ^ k / c) * ν U := by
  have hc0 : c ≠ 0 := hc.ne'
  have hε : ∀ z ∈ E, ∃ ε > 0, Metric.ball z ε ⊆ U := fun z hz =>
    Metric.isOpen_iff.1 hU z (hEU hz)
  choose! ε hεpos hεU using hε
  set δ : ℕ → ℝ := fun m => R * (1 / ((m : ℝ) + 1)) with hδ
  have hδpos : ∀ m, 0 < δ m := fun m => mul_pos hR (by positivity)
  have hδR : ∀ m, δ m ≤ R := fun m => by
    have h1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    calc δ m = R * (1 / ((m : ℝ) + 1)) := rfl
      _ ≤ R * 1 := mul_le_mul_of_nonneg_left h1 hR.le
      _ = R := mul_one R
  set ρ : ℕ → Space n → ℝ := fun m z => min (δ m) (ε z / 2) with hρ
  have hρpos : ∀ m, ∀ z ∈ E, 0 < ρ m z := fun m z hz =>
    lt_min (hδpos m) (half_pos (hεpos z hz))
  have hρδ : ∀ m z, ρ m z ≤ δ m := fun m z => min_le_left _ _
  have hρU : ∀ m, ∀ z ∈ E, Metric.ball z (ρ m z) ⊆ U := fun m z hz =>
    (Metric.ball_subset_ball ((min_le_right _ _).trans (half_le_self (hεpos z hz).le))).trans
      (hεU z hz)
  have hV := fun m : ℕ =>
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall E id (ρ m) (δ m)
      (fun a _ => hρδ m a) 5 (by norm_num)
  choose u hut hudisj hucover using hV
  have hdisjball : ∀ m, (u m).PairwiseDisjoint fun z => Metric.ball z (ρ m z) := fun m =>
    (hudisj m).mono fun z => Metric.ball_subset_closedBall
  have hcount : ∀ m, (u m).Countable := fun m =>
    (hdisjball m).countable_of_isOpen (fun z _ => Metric.isOpen_ball)
      fun z hz => ⟨z, Metric.mem_ball_self (hρpos m z (hut m hz))⟩
  have : ∀ m, Countable (u m) := fun m => (hcount m).to_subtype
  -- the per-scale covering sums
  have hsum : ∀ m, ∑' i : u m, Metric.ediam (Metric.closedBall (i : Space n) (5 * ρ m i)) ^ (k : ℝ)
      ≤ ENNReal.ofReal (10 ^ k / c) * ν U := by
    intro m
    have hterm : ∀ i : u m, Metric.ediam (Metric.closedBall (i : Space n) (5 * ρ m i)) ^ (k : ℝ)
        ≤ ENNReal.ofReal (10 ^ k / c) * ν (Metric.ball (i : Space n) (ρ m i)) := by
      intro i
      have hiE : (i : Space n) ∈ E := hut m i.2
      have hpos := hρpos m i hiE
      have hdiam : Metric.ediam (Metric.closedBall (i : Space n) (5 * ρ m i)) ≤
          ENNReal.ofReal (10 * ρ m i) := by
        refine Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_
        simp only [Metric.mem_closedBall] at hx hy
        have := dist_triangle x (i : Space n) y
        rw [dist_comm (i : Space n) y] at this
        linarith
      have hle := hlow i (hEK hiE) (ρ m i) hpos ((hρδ m i).trans (hδR m))
      have hpow : (10 * ρ m i) ^ k = 10 ^ k / c * (c * ρ m i ^ k) := by
        rw [mul_pow, ← mul_assoc, div_mul_cancel₀ _ hc0]
      calc Metric.ediam (Metric.closedBall (i : Space n) (5 * ρ m i)) ^ (k : ℝ)
          ≤ ENNReal.ofReal (10 * ρ m i) ^ (k : ℝ) := ENNReal.rpow_le_rpow hdiam (by positivity)
        _ = ENNReal.ofReal ((10 * ρ m i) ^ k) := by
          rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (show (0 : ℝ) ≤ 10 * ρ m i by linarith)]
        _ = ENNReal.ofReal (10 ^ k / c) * ENNReal.ofReal (c * ρ m i ^ k) := by
          rw [hpow, ENNReal.ofReal_mul (show (0 : ℝ) ≤ 10 ^ k / c by positivity)]
        _ ≤ ENNReal.ofReal (10 ^ k / c) * ν (Metric.ball (i : Space n) (ρ m i)) :=
          mul_le_mul_right hle _
    have hunion : ν (⋃ z ∈ u m, Metric.ball z (ρ m z)) =
        ∑' i : u m, ν (Metric.ball (i : Space n) (ρ m i)) :=
      measure_biUnion (hcount m) (hdisjball m) fun z _ => measurableSet_ball
    have hsubU : (⋃ z ∈ u m, Metric.ball z (ρ m z)) ⊆ U :=
      iUnion₂_subset fun z hz => hρU m z (hut m hz)
    calc ∑' i : u m, Metric.ediam (Metric.closedBall (i : Space n) (5 * ρ m i)) ^ (k : ℝ)
        ≤ ∑' i : u m, ENNReal.ofReal (10 ^ k / c) * ν (Metric.ball (i : Space n) (ρ m i)) :=
          ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (10 ^ k / c) * ∑' i : u m, ν (Metric.ball (i : Space n) (ρ m i)) :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (10 ^ k / c) * ν (⋃ z ∈ u m, Metric.ball z (ρ m z)) := by
          rw [hunion]
      _ ≤ ENNReal.ofReal (10 ^ k / c) * ν U := mul_le_mul_right (measure_mono hsubU) _
  -- Hausdorff measure from coverings of vanishing diameter
  have hr : Tendsto (fun m : ℕ => ENNReal.ofReal (10 * δ m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => 10 * δ m) atTop (𝓝 (10 * (R * 0))) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul R).const_mul 10
    rw [mul_zero, mul_zero] at h1
    have h2 := ENNReal.tendsto_ofReal h1
    rwa [ENNReal.ofReal_zero] at h2
  have hmain := Measure.hausdorffMeasure_le_liminf_tsum (k : ℝ) E
    (fun m : ℕ => ENNReal.ofReal (10 * δ m)) hr
    (fun m (i : u m) => Metric.closedBall (i : Space n) (5 * ρ m i))
    (Eventually.of_forall fun m i => by
      refine Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_
      simp only [Metric.mem_closedBall] at hx hy
      have := dist_triangle x (i : Space n) y
      rw [dist_comm (i : Space n) y] at this
      have := hρδ m i
      linarith)
    (Eventually.of_forall fun m => by
      intro z hz
      obtain ⟨b, hb, hsub⟩ := hucover m z hz
      exact mem_iUnion.2 ⟨⟨b, hb⟩, hsub (Metric.mem_closedBall_self (hρpos m z hz).le)⟩)
  rw [hausdorffP_eq]
  exact hmain.trans (liminf_le_of_frequently_le' (Frequently.of_forall hsum))

/-- **Domination by a lower mass bound.** If `ν(P(z,r)) ≥ c r^k` for every `z ∈ K` and
`0 < r ≤ R`, then `H^k_P ⌞ K ≤ M ν` for every `M ≥ 10^k / c` (the finite source `ν` is outer
regular). -/
theorem ms4_hausdorffP_restrict_le_of_lower {n k : ℕ} (ν : Measure (Space n)) [IsFiniteMeasure ν]
    (K : Set (Space n)) {c R M : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hlow : ∀ z ∈ K, ∀ r : ℝ, 0 < r → r ≤ R → ENNReal.ofReal (c * r ^ k) ≤ ν (Metric.ball z r))
    (hM : 10 ^ k / c ≤ M) :
    (hausdorffP n k).restrict K ≤ ENNReal.ofReal M • ν := by
  rw [Measure.le_iff]
  intro s hs
  have : (ENNReal.ofReal M • ν).OuterRegular :=
    Measure.OuterRegular.smul ν ENNReal.ofReal_ne_top
  rw [Measure.restrict_apply hs, Set.measure_eq_iInf_isOpen s (ENNReal.ofReal M • ν)]
  refine le_iInf₂ fun U hsU => le_iInf fun hU => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  calc hausdorffP n k (s ∩ K) ≤ ENNReal.ofReal (10 ^ k / c) * ν U :=
        ms4_hausdorffP_le_of_lower_of_isOpen ν K hc hR hlow inter_subset_right
          (inter_subset_left.trans hsU) hU
    _ ≤ ENNReal.ofReal M * ν U := mul_le_mul_left (ENNReal.ofReal_le_ofReal hM) _

/-- **`core_domination_of_construction`**: `H^k_P ⌞ C₀ ≤ (L/a) ν` for every
`L ≥ 10^{n+2} C_16`. -/
theorem core_domination_of_construction_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T),
      T.Available n k → k < n + 2 → P.IsAdmissible → D.IsSourceConstruction P →
      ∀ L : ℝ, C ≤ L →
        (hausdorffP n k).restrict (D.core P) ≤ ENNReal.ofReal (L / P.a) • P.ν := by
  obtain ⟨C₁, hC₁, hlow⟩ := core_lower_of_construction_proof n
  refine ⟨10 ^ (n + 2) * C₁, by positivity, ?_⟩
  intro k T P D hT hk hP hD L hL
  have := P.finite
  have ha := hP.a_pos
  have hlow' : ∀ z ∈ D.core P, ∀ r : ℝ, 0 < r → r ≤ P.R →
      ENNReal.ofReal (P.a / C₁ * r ^ k) ≤ P.ν (Metric.ball z r) := by
    intro z hz r hr hrR
    have := hlow P D hT hk hP hD C₁ le_rfl z hz r hr hrR
    rwa [show P.a * r ^ k / C₁ = P.a / C₁ * r ^ k by ring] at this
  refine ms4_hausdorffP_restrict_le_of_lower P.ν (D.core P) (by positivity) hP.R_pos hlow' ?_
  rw [div_div_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ ha.le
  calc (10 : ℝ) ^ k * C₁ ≤ 10 ^ (n + 2) * C₁ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hC₁.le
    _ ≤ L := hL

end ParabolicRectifiability
