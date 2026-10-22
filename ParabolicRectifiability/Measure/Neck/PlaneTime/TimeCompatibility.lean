import ParabolicRectifiability.Measure.Neck.PlaneTime.ConstructionFacts

/-!
# Horizontal time compatibility of the construction

Proofs of the three parts of `recordsTimeCompatible_of_construction`.

* **Fitted-time comparison** `fittedTime_comparison_of_construction_proof`: for horizontal fits `L × {τ}` and
  `L' × {τ'}` compared on the common original-source ball `P(g, 5r)` of the finer
  continuing candidate, `ν(P(g,5r)) |τ - τ'| ≤ ∫_{P(g,5r)} (|t - τ| + |t - τ'|) dν`, which is
  at most the two fitting errors. Noncollapse gives `ν(P(g,5r)) ≥ a (5r)^k` and the node
  beta bound (`nodeBeta_le`, taken as a hypothesis) bounds the
  errors, so `|τ - τ'| ≤ 80^{n+3} C_β (B/a) r_j²`.
* **Genuine records** `genuineRecords_timeCompatible_proof`: for two genuine records put
  `b = max{d_P(z,w), s_z, s_w}`. At the deepest positive level `ℓ` with `r_ℓ ≥ 10 b` both
  points are kept (stage of a record `≥ ℓ + 1`), so they lie in the `θ r_ℓ`-tubes of their
  continuing parents, which are within `20 r_ℓ` of each other; the fitted-time comparison
  gives `|t_z - t_w| ≤ (2θ² + K) r_ℓ² ≤ 10⁴ (2θ² + K) b²`. Without such a level the initial
  tube gives the same bound. With `γ₀ = 10⁴ (2θ² + K) ≤ 1/2` (thresholds `θ ≤ 1/300`,
  `a ≥ 4·10⁴ C₀ B`) this is `T₀ ≤ γ₀ max{X, T₀}`, hence `T₀ ≤ γ₀ X ≤ γ X`.
* **All records** `recordsTimeCompatible_of_genuine_proof`: every record lies in the closure of the
  initial tube, so `|t - τ_*| ≤ θ² R² ≤ γ r_0²`, which handles the artificial root
  (`r_0 = 8R`); a core point is a limit of continuing candidates `g_m` of level `m + 1`
  with recorded radii `r_{m+1} → 0`, and continuity passes the genuine inequality to the
  core record (recorded radius `0`), also for two core points.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-! ## Elementary inequalities -/

/-- Mass times the difference of two horizontal time levels is at most the sum of the two
squared-distance integrals on the same set. -/
theorem ms3_time_diff_mass {n m : ℕ} (ν : Measure (Space n)) (s : Set (Space n))
    (L₁ L₂ : AffineSpatialPlane n m) (τ₁ τ₂ : ℝ) :
    ν s * ENNReal.ofReal |τ₁ - τ₂| ≤
      ∫⁻ z in s, Metric.infEDist z (NeckType.horizontal.lowerModelSet L₁ τ₁) ^ 2 ∂ν +
        ∫⁻ z in s, Metric.infEDist z (NeckType.horizontal.lowerModelSet L₂ τ₂) ^ 2 ∂ν := by
  calc ν s * ENNReal.ofReal |τ₁ - τ₂| = ∫⁻ _ in s, ENNReal.ofReal |τ₁ - τ₂| ∂ν := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ z in s, (Metric.infEDist z (NeckType.horizontal.lowerModelSet L₁ τ₁) ^ 2 +
          Metric.infEDist z (NeckType.horizontal.lowerModelSet L₂ τ₂) ^ 2) ∂ν := by
        refine lintegral_mono fun z => ?_
        calc ENNReal.ofReal |τ₁ - τ₂| ≤ ENNReal.ofReal (|z.2.val - τ₁| + |z.2.val - τ₂|) := by
              apply ENNReal.ofReal_le_ofReal
              calc |τ₁ - τ₂| ≤ |τ₁ - z.2.val| + |z.2.val - τ₂| := abs_sub_le _ _ _
                _ = |z.2.val - τ₁| + |z.2.val - τ₂| := by rw [abs_sub_comm τ₁]
          _ = ENNReal.ofReal |z.2.val - τ₁| + ENNReal.ofReal |z.2.val - τ₂| :=
              ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
          _ ≤ _ := add_le_add (ms3_ofReal_abs_time_le_sq L₁ τ₁ z)
              (ms3_ofReal_abs_time_le_sq L₂ τ₂ z)
    _ = _ := lintegral_add_left (Metric.continuous_infEDist.measurable.pow_const 2) _

/-- The real arithmetic of 12a. -/
theorem ms3_time_bound {n k : ℕ} (hk : k < n + 2) {a B Cβ r ρ R₁ R₂ Δ : ℝ} (ha : 0 < a)
    (hB : 0 ≤ B) (hCβ : 0 ≤ Cβ) (hr : 0 < r) (hρ : r / 2 ≤ ρ) (hR₁ : 0 ≤ R₁)
    (hR₁' : R₁ ≤ 40 * r) (hR₂ : 0 ≤ R₂) (hR₂' : R₂ ≤ 40 * r)
    (h : a * ρ ^ k * Δ ≤ R₁ ^ (k + 2) * (Cβ * B) + R₂ ^ (k + 2) * (Cβ * B)) :
    Δ ≤ 80 ^ (n + 3) * Cβ * (B / a) * r ^ 2 := by
  have hr2 : 0 < r / 2 := by linarith
  have hCB : 0 ≤ Cβ * B := mul_nonneg hCβ hB
  have h1 : R₁ ^ (k + 2) ≤ (40 * r) ^ (k + 2) := pow_le_pow_left₀ hR₁ hR₁' _
  have h2 : R₂ ^ (k + 2) ≤ (40 * r) ^ (k + 2) := pow_le_pow_left₀ hR₂ hR₂' _
  have hpk : 0 < (r / 2) ^ k := pow_pos hr2 k
  have hρk : (r / 2) ^ k ≤ ρ ^ k := pow_le_pow_left₀ hr2.le hρ k
  rcases le_or_gt Δ 0 with hΔ | hΔ
  · exact hΔ.trans (by positivity)
  have h3 : a * (r / 2) ^ k * Δ ≤ 2 * (40 * r) ^ (k + 2) * (Cβ * B) := by
    calc a * (r / 2) ^ k * Δ ≤ a * ρ ^ k * Δ := by gcongr
      _ ≤ R₁ ^ (k + 2) * (Cβ * B) + R₂ ^ (k + 2) * (Cβ * B) := h
      _ ≤ (40 * r) ^ (k + 2) * (Cβ * B) + (40 * r) ^ (k + 2) * (Cβ * B) := by gcongr
      _ = 2 * (40 * r) ^ (k + 2) * (Cβ * B) := by ring
  have e : (40 * r) ^ (k + 2) = 1600 * (80 ^ k * (r / 2) ^ k) * r ^ 2 := by
    rw [← mul_pow, show (80 : ℝ) * (r / 2) = 40 * r by ring, pow_add]
    ring
  have h4 : a * Δ ≤ 3200 * 80 ^ k * r ^ 2 * (Cβ * B) := by
    have h5 : (r / 2) ^ k * (a * Δ) ≤ (r / 2) ^ k * (3200 * 80 ^ k * r ^ 2 * (Cβ * B)) := by
      calc (r / 2) ^ k * (a * Δ) = a * (r / 2) ^ k * Δ := by ring
        _ ≤ 2 * (40 * r) ^ (k + 2) * (Cβ * B) := h3
        _ = (r / 2) ^ k * (3200 * 80 ^ k * r ^ 2 * (Cβ * B)) := by rw [e]; ring
    exact le_of_mul_le_mul_left h5 hpk
  have h80 : (3200 : ℝ) * 80 ^ k ≤ 80 ^ (n + 3) := by
    calc (3200 : ℝ) * 80 ^ k ≤ 6400 * 80 ^ k := by gcongr; norm_num
      _ = 80 ^ (k + 2) := by ring
      _ ≤ 80 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [show 80 ^ (n + 3) * Cβ * (B / a) * r ^ 2 = 80 ^ (n + 3) * r ^ 2 * (Cβ * B) / a by ring,
    le_div_iff₀ ha]
  calc Δ * a = a * Δ := mul_comm _ _
    _ ≤ 3200 * 80 ^ k * r ^ 2 * (Cβ * B) := h4
    _ ≤ 80 ^ (n + 3) * r ^ 2 * (Cβ * B) := by gcongr

/-- Absorption of the time term: `T₀ ≤ γ₀ max{X, T₀}` with `γ₀ ≤ 1/2` gives `T₀ ≤ γ X`
for every `γ ≥ γ₀`. -/
theorem ms3_absorb {T₀ X γ₀ γ : ℝ} (hT₀ : 0 ≤ T₀) (hX : 0 ≤ X) (hγ₀ : 0 ≤ γ₀)
    (hγ₀1 : γ₀ ≤ 1 / 2) (hγ : γ₀ ≤ γ) (h : T₀ ≤ γ₀ * max X T₀) : T₀ ≤ γ * X := by
  rcases le_total T₀ X with hle | hle
  · rw [max_eq_left hle] at h
    exact h.trans (mul_le_mul_of_nonneg_right hγ hX)
  · rw [max_eq_right hle] at h
    have hT0 : T₀ = 0 := le_antisymm (by nlinarith) hT₀
    rw [hT0]
    exact mul_nonneg (hγ₀.trans hγ) hX

theorem ms3_sq_max_le {d u v X T₀ : ℝ} (hd2 : d ^ 2 ≤ max X T₀) (hu2 : u ^ 2 ≤ X)
    (hv2 : v ^ 2 ≤ X) : max d (max u v) ^ 2 ≤ max X T₀ := by
  rcases le_total d (max u v) with h | h
  · rw [max_eq_right h]
    rcases le_total u v with h' | h'
    · rw [max_eq_right h']
      exact hv2.trans (le_max_left _ _)
    · rw [max_eq_left h']
      exact hu2.trans (le_max_left _ _)
  · rw [max_eq_left h]
    exact hd2

/-- Symmetry of the record inequality. -/
theorem ms3_tc_symm {n : ℕ} {γ : ℝ} {p q : Space n} {s t : ℝ}
    (h : |p.2.val - q.2.val| ≤ γ * max (‖p.1 - q.1‖ ^ 2) (max (s ^ 2) (t ^ 2))) :
    |q.2.val - p.2.val| ≤ γ * max (‖q.1 - p.1‖ ^ 2) (max (t ^ 2) (s ^ 2)) := by
  rwa [abs_sub_comm, norm_sub_rev, max_comm (t ^ 2)]

/-- Passage of the record inequality to a limit point with recorded radius zero. -/
theorem ms3_tc_limit {n : ℕ} {γ : ℝ} {z q : Space n} {t : ℝ} {g : ℕ → Space n}
    {s : ℕ → ℝ} (hg : Tendsto g atTop (𝓝 z)) (hs : Tendsto s atTop (𝓝 0))
    (h : ∀ m, |(g m).2.val - q.2.val| ≤
      γ * max (‖(g m).1 - q.1‖ ^ 2) (max (s m ^ 2) (t ^ 2))) :
    |z.2.val - q.2.val| ≤ γ * max (‖z.1 - q.1‖ ^ 2) (max (0 ^ 2) (t ^ 2)) := by
  have hL : Tendsto (fun m => |(g m).2.val - q.2.val|) atTop (𝓝 |z.2.val - q.2.val|) :=
    ((continuous_abs.comp (continuous_time.sub continuous_const)).tendsto z).comp hg
  have hX : Tendsto (fun m => ‖(g m).1 - q.1‖ ^ 2) atTop (𝓝 (‖z.1 - q.1‖ ^ 2)) :=
    (((continuous_spatial.sub continuous_const).norm.pow 2).tendsto z).comp hg
  have hS : Tendsto (fun m => s m ^ 2) atTop (𝓝 (0 ^ 2)) := hs.pow 2
  have hRt : Tendsto (fun m => γ * max (‖(g m).1 - q.1‖ ^ 2) (max (s m ^ 2) (t ^ 2))) atTop
      (𝓝 (γ * max (‖z.1 - q.1‖ ^ 2) (max (0 ^ 2) (t ^ 2)))) :=
    (hX.max (hS.max tendsto_const_nhds)).const_mul γ
  exact le_of_tendsto_of_tendsto' hL hRt h

/-! ## Construction facts used by the time compatibility statements -/

namespace ConstructionData

variable {n k : ℕ} {T : NeckType} (D : ConstructionData n k T) (P : SourceSetup n)

theorem ms3_mem_kept_pos {j : ℕ} (hj : 1 ≤ j) {z : Space n} (hz : z ∈ D.kept P j) :
    ∃ i ∈ D.contIndex P j, dist z (D.cand j i) < T.sourceSeparation * P.scale T j ∧
      Metric.infEDist z (D.modelSet j i) ≤ ENNReal.ofReal (P.θ * P.scale T j) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact D.ms3_mem_kept_succ P hz

/-- Noncollapse gives the mass lower bound `ν(P(g, 5 r_j)) ≥ a (5 r_j)^k` (at vertical rank
zero, `k = 2`, this is the test itself). -/
theorem ms3_mass_of_continuing (hT : T.Available n k) {j i : ℕ} (h : D.IsContinuing P j i) :
    ENNReal.ofReal (P.a * (5 * P.scale T j) ^ k) ≤
      P.ν (Metric.ball (D.cand j i) (5 * P.scale T j)) := by
  have := P.finite
  rcases h with ⟨-, hρ, hle⟩ | ⟨hm, hmass⟩
  · exact SpatialSource.measure_ball_ge_of_rankEigenvalue P.ν (D.cand j i) hρ hle
  · have hk2 : k = 2 := by
      cases T <;> simp only [NeckType.rank, NeckType.Available] at hT hm <;> omega
    subst hk2
    exact hmass

theorem ms3_radius_pos (hD : D.IsSourceConstruction P) (hR : 0 < P.R) {c : Space n}
    (hc : D.IsTermCenter c ∨ D.IsCollCenter P c) : 0 < D.radius P c := by
  unfold radius
  split_ifs with h1 h2
  · obtain ⟨j, hj, i, hi, rfl⟩ := h1
    exact lt_of_lt_of_le (P.scale_pos T hR j) (hD.term_large j hj i hi)
  · have := P.scale_pos T hR (D.collStage P c)
    linarith
  · exact hc.elim (fun h => absurd h h1) (fun h => absurd h h2)

/-- A genuine record (occurrence of a positive level, or stopping center) lies in `S_{j-1}`
for a stage `j ≥ 1` with `r_j ≤` its recorded scale. -/
theorem ms3_genuine_stage (hD : D.IsSourceConstruction P) (hR : 0 < P.R)
    {z : NeckRecord n ℕ} (hz : NeckRecord.IsRecord (D.family P hR) (D.centers P) z)
    (hg : D.IsGenuineRecord P z) :
    ∃ j, 1 ≤ j ∧ NeckRecord.position (D.family P hR) z ∈ D.kept P (j - 1) ∧
      P.scale T j ≤ NeckRecord.scale (D.family P hR) (D.radius P) z := by
  rcases z with ⟨j, a⟩ | c
  · have hj : 1 ≤ j := hg
    have hj0 : j ≠ 0 := by omega
    have ha' : a ∈ (D.family P hR).index j := hz
    rw [D.ms3_family_index_pos P hR hj0] at ha'
    refine ⟨j, hj, ?_, le_rfl⟩
    show (D.family P hR).center j a ∈ D.kept P (j - 1)
    rw [D.ms3_family_center_pos P hR hj0]
    exact D.ms3_cand_mem_kept P hD hj ((D.ms3_mem_contIndex P).1 ha').1
  · have hg' : c ∈ D.centers P ∧ 0 < D.radius P c := hg
    show ∃ j, 1 ≤ j ∧ c ∈ D.kept P (j - 1) ∧ P.scale T j ≤ D.radius P c
    by_cases ht : D.IsTermCenter c
    · have hrad : D.radius P c = P.f c := by
        unfold radius
        rw [ite_eq_left ht]
      obtain ⟨j, hj, i, hi, hji⟩ := ht
      have hmem := D.ms3_term_mem_kept P hD hj hi
      rw [hji] at hmem
      refine ⟨j, hj, hmem, ?_⟩
      rw [hrad, ← hji]
      exact hD.term_large j hj i hi
    · have hcoll : D.IsCollCenter P c := by
        by_contra hcoll
        have h0 : D.radius P c = 0 := by
          unfold radius
          rw [ite_eq_right ht, ite_eq_right hcoll]
        linarith [hg'.2]
      have hrad : D.radius P c = 5 * P.scale T (D.collStage P c) := by
        unfold radius
        rw [ite_eq_right ht, ite_eq_left hcoll]
      have hstage : D.collStage P c = Classical.choose hcoll := by
        unfold collStage
        rw [dite_eq_left hcoll]
      obtain ⟨hj, i, hi, -, hci, -⟩ := Classical.choose_spec hcoll
      have hmem := D.ms3_cand_mem_kept P hD hj hi
      rw [hci] at hmem
      refine ⟨D.collStage P c, by rw [hstage]; exact hj, by rw [hstage]; exact hmem, ?_⟩
      rw [hrad]
      have := P.scale_pos T hR (D.collStage P c)
      linarith

/-- Every record is genuine, the artificial root, or a core point with recorded radius
zero. -/
theorem ms3_record_cases (hD : D.IsSourceConstruction P) (hR : 0 < P.R)
    {z : NeckRecord n ℕ} (hz : NeckRecord.IsRecord (D.family P hR) (D.centers P) z) :
    D.IsGenuineRecord P z ∨
      (NeckRecord.position (D.family P hR) z = D.rootCenter ∧
        NeckRecord.scale (D.family P hR) (D.radius P) z = P.scale T 0) ∨
      (NeckRecord.position (D.family P hR) z ∈ D.coreLimit P ∧
        NeckRecord.scale (D.family P hR) (D.radius P) z = 0) := by
  rcases z with ⟨j, a⟩ | c
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact Or.inr (Or.inl ⟨D.ms3_family_center_zero P hR a, rfl⟩)
    · exact Or.inl hj
  · by_cases hpos : 0 < D.radius P c
    · exact Or.inl (show c ∈ D.centers P ∧ 0 < D.radius P c from ⟨hz, hpos⟩)
    · right
      right
      have hc : c ∈ D.centers P := hz
      have hnot : ¬ (D.IsTermCenter c ∨ D.IsCollCenter P c) :=
        fun h => hpos (D.ms3_radius_pos P hD hR h)
      have hcore : c ∈ D.coreLimit P := by
        rcases hc with hc | hc
        · exact hc
        · exact absurd hc hnot
      refine ⟨hcore, ?_⟩
      show D.radius P c = 0
      obtain ⟨hn1, hn2⟩ := not_or.1 hnot
      unfold radius
      rw [ite_eq_right hn1, ite_eq_right hn2]

theorem ms3_position_inl (hR : 0 < P.R) {j : ℕ} (hj : j ≠ 0) (a : ℕ) :
    NeckRecord.position (D.family P hR) (Sum.inl (j, a)) = D.cand j a :=
  D.ms3_family_center_pos P hR hj a

theorem ms3_scale_inl (hR : 0 < P.R) (d : Space n → ℝ) (j a : ℕ) :
    NeckRecord.scale (D.family P hR) d (Sum.inl (j, a)) = P.scale T j := rfl

/-- A point of the core limit is the limit of continuing candidates `g_{m+1, idx m}`. -/
theorem ms3_core_approx (hR : 0 < P.R) {c : Space n} (hc : c ∈ D.coreLimit P) :
    ∃ idx : ℕ → ℕ, (∀ m, idx m ∈ D.contIndex P (m + 1)) ∧
      Tendsto (fun m => D.cand (m + 1) (idx m)) atTop (𝓝 c) := by
  have h : ∀ m : ℕ, ∃ i ∈ D.contIndex P (m + 1),
      dist c (D.cand (m + 1) i) < 2 * P.scale T (m + 1) := by
    intro m
    have hcl : c ∈ closure (D.kept P (m + 1)) := mem_iInter.1 hc (m + 1)
    obtain ⟨y, hy, hcy⟩ := Metric.mem_closure_iff.1 hcl (P.scale T (m + 1)) (P.scale_pos T hR _)
    obtain ⟨i, hi, hyi, -⟩ := D.ms3_mem_kept_succ P hy
    refine ⟨i, hi, ?_⟩
    have hκ := T.sourceSeparation_le_one
    have hr := P.scale_pos T hR (m + 1)
    calc dist c (D.cand (m + 1) i) ≤ dist c y + dist y (D.cand (m + 1) i) :=
          dist_triangle _ _ _
      _ < P.scale T (m + 1) + T.sourceSeparation * P.scale T (m + 1) := add_lt_add hcy hyi
      _ ≤ 2 * P.scale T (m + 1) := by nlinarith
  choose idx hidx hdist using h
  refine ⟨idx, hidx, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun m => 2 * P.scale T (m + 1)) atTop (𝓝 0) := by
    simpa using (P.ms3_scale_tendsto T).const_mul 2
  refine squeeze_zero (fun m => dist_nonneg) (fun m => ?_) hlim
  rw [dist_comm]
  exact (hdist m).le

end ConstructionData

/-- Points of the closure of the initial tube have time within `(θR)²` of `τ_*`. -/
theorem ConstructionData.ms3_closure_kept_zero_time {n k : ℕ}
    (D : ConstructionData n k .horizontal) (P : SourceSetup n) (hθ : 0 ≤ P.θ) (hR : 0 ≤ P.R)
    {z : Space n} (hz : z ∈ closure (D.kept P 0)) :
    |z.2.val - D.rootTime| ≤ (P.θ * P.R) ^ 2 := by
  have hsub : D.kept P 0 ⊆ {y : Space n | |y.2.val - D.rootTime| ≤ (P.θ * P.R) ^ 2} :=
    fun y hy => ms3_abs_time_sub_le D.rootPlane D.rootTime y (mul_nonneg hθ hR)
      (D.ms3_kept_zero_infEDist P hy)
  have hcl : IsClosed {y : Space n | |y.2.val - D.rootTime| ≤ (P.θ * P.R) ^ 2} :=
    isClosed_le (continuous_abs.comp (continuous_time.sub continuous_const)) continuous_const
  exact closure_minimal hsub hcl hz

/-- The time fit of a horizontal candidate on a subset of its fitting ball. -/
theorem ConstructionData.ms3_timeFit_le {n k : ℕ} (D : ConstructionData n k .horizontal)
    (P : SourceSetup n) (hD : D.IsSourceConstruction P) (hR : 0 < P.R) {j : ℕ} (hj : 1 ≤ j)
    {i : ℕ} (hi : i < D.candCount j) {s : Set (Space n)}
    (hs : s ⊆ Metric.ball (D.cand j i) (40 * P.scale .horizontal j)) :
    ∫⁻ z in s, Metric.infEDist z
        (NeckType.horizontal.lowerModelSet (D.plane j i) (D.time j i)) ^ 2 ∂P.ν ≤
      ENNReal.ofReal (40 * P.scale .horizontal j) ^ (k + 2) *
        betaSq P.ν k NeckType.horizontal.toFamilyKind (D.cand j i)
          (40 * P.scale .horizontal j) := by
  have hr : 0 < 40 * P.scale .horizontal j := by
    have := P.scale_pos .horizontal hR j
    linarith
  rw [← ms3_typeFittingError_eq _ _ _ _ hr]
  exact (lintegral_mono_set hs).trans (hD.fit_minimal j hj i hi)

/-- The two-record estimate of 12b: `|t_z - t_w| ≤ 10⁴ (2θ² + K) b²` with
`b = max{d_P(z,w), s_z, s_w}`. -/
theorem ConstructionData.ms3_genuine_pair {n k : ℕ} (D : ConstructionData n k .horizontal)
    (P : SourceSetup n) (hR : 0 < P.R) {K : ℝ} (hK : 0 ≤ K) (hθ : 0 < P.θ)
    (hfit : ∀ j, 1 ≤ j → ∀ i ∈ D.contIndex P j, ∀ l ∈ D.contIndex P j,
      dist (D.cand j i) (D.cand j l) ≤ 20 * P.scale .horizontal j →
      |D.time j i - D.time j l| ≤ K * P.scale .horizontal j ^ 2)
    {pz pw : Space n} {sz sw : ℝ} {jz jw : ℕ} (hjz : 1 ≤ jz) (hjw : 1 ≤ jw)
    (hpz : pz ∈ D.kept P (jz - 1)) (hpw : pw ∈ D.kept P (jw - 1))
    (hsz : P.scale .horizontal jz ≤ sz) (hsw : P.scale .horizontal jw ≤ sw) :
    |pz.2.val - pw.2.val| ≤ 10000 * (2 * P.θ ^ 2 + K) * max (dist pz pw) (max sz sw) ^ 2 := by
  classical
  have hrz : 0 < P.scale .horizontal jz := P.scale_pos _ hR jz
  have hszb : sz ≤ max (dist pz pw) (max sz sw) := (le_max_left sz sw).trans (le_max_right _ _)
  have hswb : sw ≤ max (dist pz pw) (max sz sw) := (le_max_right sz sw).trans (le_max_right _ _)
  have hdb : dist pz pw ≤ max (dist pz pw) (max sz sw) := le_max_left _ _
  set b := max (dist pz pw) (max sz sw) with hb
  have hb_pos : 0 < b := lt_of_lt_of_le hrz (hsz.trans hszb)
  have hθ0 := hθ.le
  have hex : ∃ m, P.scale .horizontal (m + 1) < 10 * b :=
    ((P.ms3_scale_tendsto .horizontal).eventually (gt_mem_nhds (by linarith))).exists
  have hℓspec : P.scale .horizontal (Nat.find hex + 1) < 10 * b := Nat.find_spec hex
  have hz0 : pz ∈ D.kept P 0 := D.ms3_kept_anti P (Nat.zero_le _) hpz
  have hw0 : pw ∈ D.kept P 0 := D.ms3_kept_anti P (Nat.zero_le _) hpw
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · -- no positive level with `r_ℓ ≥ 10 b`: the initial tube
    rw [h0] at hℓspec
    have hr1 : P.scale .horizontal (0 + 1) = 8 * P.R / 10 := by
      show NeckType.horizontal.rootRadius P.R / 10 ^ (0 + 1) = 8 * P.R / 10
      norm_num [NeckType.rootRadius]
    rw [hr1] at hℓspec
    have htz := ms3_abs_time_sub_le D.rootPlane D.rootTime pz (mul_nonneg hθ0 hR.le)
      (D.ms3_kept_zero_infEDist P hz0)
    have htw := ms3_abs_time_sub_le D.rootPlane D.rootTime pw (mul_nonneg hθ0 hR.le)
      (D.ms3_kept_zero_infEDist P hw0)
    have hRb : P.R ≤ 13 * b := by linarith
    have hR2 : P.R ^ 2 ≤ 169 * b ^ 2 := by nlinarith
    calc |pz.2.val - pw.2.val| ≤ |pz.2.val - D.rootTime| + |D.rootTime - pw.2.val| :=
          abs_sub_le _ _ _
      _ ≤ (P.θ * P.R) ^ 2 + (P.θ * P.R) ^ 2 := by
          rw [abs_sub_comm D.rootTime]
          exact add_le_add htz htw
      _ = 2 * P.θ ^ 2 * P.R ^ 2 := by ring
      _ ≤ 2 * P.θ ^ 2 * (169 * b ^ 2) := by gcongr
      _ ≤ 10000 * (2 * P.θ ^ 2 + K) * b ^ 2 := by
          nlinarith [mul_nonneg (sq_nonneg P.θ) (sq_nonneg b), mul_nonneg hK (sq_nonneg b)]
  · -- the deepest positive level `ℓ` with `r_ℓ ≥ 10 b`
    set ℓ := Nat.find hex with hℓ
    have hℓmin : 10 * b ≤ P.scale .horizontal ℓ := by
      have h1 := Nat.find_min hex (show ℓ - 1 < ℓ by omega)
      rw [not_lt, show ℓ - 1 + 1 = ℓ by omega] at h1
      exact h1
    have hrℓ : P.scale .horizontal ℓ < 100 * b := by
      rw [P.ms3_scale_succ] at hℓspec
      linarith
    have hℓz : ℓ ≤ jz - 1 := by
      by_contra hcon
      have h1 := P.ms3_scale_anti .horizontal hR (show jz ≤ ℓ by omega)
      linarith
    have hℓw : ℓ ≤ jw - 1 := by
      by_contra hcon
      have h1 := P.ms3_scale_anti .horizontal hR (show jw ≤ ℓ by omega)
      linarith
    have hzℓ : pz ∈ D.kept P ℓ := D.ms3_kept_anti P hℓz hpz
    have hwℓ : pw ∈ D.kept P ℓ := D.ms3_kept_anti P hℓw hpw
    obtain ⟨i, hi, hdi, hmi⟩ := D.ms3_mem_kept_pos P hpos hzℓ
    obtain ⟨i', hi', hdi', hmi'⟩ := D.ms3_mem_kept_pos P hpos hwℓ
    have hκ : NeckType.horizontal.sourceSeparation = 1 / 4 := rfl
    rw [hκ] at hdi hdi'
    have hr := P.scale_pos .horizontal hR ℓ
    have hgg : dist (D.cand ℓ i) (D.cand ℓ i') ≤ 20 * P.scale .horizontal ℓ := by
      have h1 := dist_triangle4 (D.cand ℓ i) pz pw (D.cand ℓ i')
      rw [dist_comm (D.cand ℓ i) pz] at h1
      linarith
    have hτ := hfit ℓ hpos i hi i' hi' hgg
    have htz := ms3_abs_time_sub_le (D.plane ℓ i) (D.time ℓ i) pz
      (mul_nonneg hθ0 hr.le) hmi
    have htw := ms3_abs_time_sub_le (D.plane ℓ i') (D.time ℓ i') pw
      (mul_nonneg hθ0 hr.le) hmi'
    have hr2 : P.scale .horizontal ℓ ^ 2 ≤ 10000 * b ^ 2 := by nlinarith
    have h3 : |pz.2.val - pw.2.val| ≤ |pz.2.val - D.time ℓ i| + |D.time ℓ i - D.time ℓ i'| +
        |pw.2.val - D.time ℓ i'| := by
      have h4 := abs_sub_le pz.2.val (D.time ℓ i) pw.2.val
      have h5 := abs_sub_le (D.time ℓ i) (D.time ℓ i') pw.2.val
      rw [abs_sub_comm (D.time ℓ i') pw.2.val] at h5
      linarith
    calc |pz.2.val - pw.2.val| ≤ |pz.2.val - D.time ℓ i| + |D.time ℓ i - D.time ℓ i'| +
          |pw.2.val - D.time ℓ i'| := h3
      _ ≤ (P.θ * P.scale .horizontal ℓ) ^ 2 + K * P.scale .horizontal ℓ ^ 2 +
          (P.θ * P.scale .horizontal ℓ) ^ 2 := by linarith
      _ = (2 * P.θ ^ 2 + K) * P.scale .horizontal ℓ ^ 2 := by ring
      _ ≤ (2 * P.θ ^ 2 + K) * (10000 * b ^ 2) := by gcongr
      _ = 10000 * (2 * P.θ ^ 2 + K) * b ^ 2 := by ring

/-! ## Fitted-time comparison -/

/-- **`fittedTime_comparison_of_construction`**, from `nodeBeta_le` (hypothesis `hβ`). The constant is `80^{n+3} C_β`. -/
theorem fittedTime_comparison_of_construction_proof (n : ℕ)
    (hβ : ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T)
      (B : ℝ), T.Available n k → k < n + 2 → P.IsAdmissible → 0 < B → P.TailBound k T B →
      D.IsSourceConstruction P →
      (∀ j, 1 ≤ j → ∀ i, i < D.candCount j →
        betaSq P.ν k T.toFamilyKind (D.cand j i) (40 * P.scale T j) ≤
          ENNReal.ofReal (C * B)) ∧
      ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν ≤ ENNReal.ofReal (C * B * P.R ^ (k + 2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
      (D : ConstructionData n k T) (B : ℝ), T.Available n k → k < n + 2 →
      P.IsAdmissible → 0 < B → P.TailBound k T B → D.IsSourceConstruction P →
      T = .horizontal → D.FittedTimeComparison P (C * (B / P.a)) := by
  obtain ⟨Cβ, hCβ, hβ'⟩ := hβ
  refine ⟨80 ^ (n + 3) * Cβ, by positivity, ?_⟩
  intro k T P D B hT hk hP hB htail hD hH
  subst hH
  have := P.finite
  have hR := hP.R_pos
  have ha := hP.a_pos
  obtain ⟨hnode, -⟩ := hβ' P D B hT hk hP hB htail hD
  -- the comparison of two fitted times on the covariance ball of the finer candidate
  have key : ∀ {j₁ i₁ j₂ i₂ : ℕ} (r : ℝ), 1 ≤ j₁ → 1 ≤ j₂ → i₁ ∈ D.contIndex P j₁ →
      i₂ < D.candCount j₂ → 0 < r → r / 2 ≤ 5 * P.scale .horizontal j₁ →
      P.scale .horizontal j₁ ≤ r → P.scale .horizontal j₂ ≤ r →
      Metric.ball (D.cand j₁ i₁) (5 * P.scale .horizontal j₁) ⊆
        Metric.ball (D.cand j₂ i₂) (40 * P.scale .horizontal j₂) →
      |D.time j₁ i₁ - D.time j₂ i₂| ≤ 80 ^ (n + 3) * Cβ * (B / P.a) * r ^ 2 := by
    intro j₁ i₁ j₂ i₂ r hj₁ hj₂ hi₁ hi₂ hr hρr hr₁ hr₂ hball
    obtain ⟨hi₁c, hcont⟩ := (D.ms3_mem_contIndex P).1 hi₁
    have hs₁ : 0 < P.scale .horizontal j₁ := P.scale_pos _ hR j₁
    have hs₂ : 0 < P.scale .horizontal j₂ := P.scale_pos _ hR j₂
    have hmass := D.ms3_mass_of_continuing P hT hcont
    have hdiff := ms3_time_diff_mass P.ν (Metric.ball (D.cand j₁ i₁) (5 * P.scale .horizontal j₁))
      (D.plane j₁ i₁) (D.plane j₂ i₂) (D.time j₁ i₁) (D.time j₂ i₂)
    have hf₁ := D.ms3_timeFit_le P hD hR hj₁ hi₁c
      (Metric.ball_subset_ball (by linarith) : Metric.ball (D.cand j₁ i₁)
        (5 * P.scale .horizontal j₁) ⊆ Metric.ball (D.cand j₁ i₁) (40 * P.scale .horizontal j₁))
    have hf₂ := D.ms3_timeFit_le P hD hR hj₂ hi₂ hball
    have hb₁ := hnode j₁ hj₁ i₁ hi₁c
    have hb₂ := hnode j₂ hj₂ i₂ hi₂
    have hCB : 0 ≤ Cβ * B := by positivity
    have hX₁ : ∀ {s : ℝ}, 0 < s →
        ENNReal.ofReal (40 * s) ^ (k + 2) * ENNReal.ofReal (Cβ * B) =
          ENNReal.ofReal ((40 * s) ^ (k + 2) * (Cβ * B)) := by
      intro s hs
      have h40 : (0 : ℝ) ≤ 40 * s := by linarith
      rw [← ENNReal.ofReal_pow h40, ← ENNReal.ofReal_mul (pow_nonneg h40 _)]
    have hmain : ENNReal.ofReal (P.a * (5 * P.scale .horizontal j₁) ^ k *
        |D.time j₁ i₁ - D.time j₂ i₂|) ≤
        ENNReal.ofReal ((40 * P.scale .horizontal j₁) ^ (k + 2) * (Cβ * B) +
          (40 * P.scale .horizontal j₂) ^ (k + 2) * (Cβ * B)) := by
      have hp1 : 0 ≤ P.a * (5 * P.scale .horizontal j₁) ^ k := by positivity
      have hq1 : 0 ≤ (40 * P.scale .horizontal j₁) ^ (k + 2) * (Cβ * B) := by positivity
      have hq2 : 0 ≤ (40 * P.scale .horizontal j₂) ^ (k + 2) * (Cβ * B) := by positivity
      rw [ENNReal.ofReal_mul hp1, ENNReal.ofReal_add hq1 hq2, ← hX₁ hs₁, ← hX₁ hs₂]
      calc ENNReal.ofReal (P.a * (5 * P.scale .horizontal j₁) ^ k) *
            ENNReal.ofReal |D.time j₁ i₁ - D.time j₂ i₂|
          ≤ P.ν (Metric.ball (D.cand j₁ i₁) (5 * P.scale .horizontal j₁)) *
            ENNReal.ofReal |D.time j₁ i₁ - D.time j₂ i₂| := by gcongr
        _ ≤ _ := hdiff
        _ ≤ _ := add_le_add (hf₁.trans (by gcongr)) (hf₂.trans (by gcongr))
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmain
    exact ms3_time_bound hk ha hB.le hCβ.le hr hρr (by positivity) (by linarith)
      (by positivity) (by linarith) hmain
  refine ⟨?_, ?_⟩
  · intro j hj i hi l hl hd
    have hr := P.scale_pos .horizontal hR j
    exact key (P.scale .horizontal j) hj hj hi ((D.ms3_mem_contIndex P).1 hl).1 hr
      (by linarith) le_rfl le_rfl (Metric.ball_subset_ball' (by linarith))
  · intro j hj i hi l hl hd
    have hr := P.scale_pos .horizontal hR j
    have hr1 := P.ms3_scale_succ .horizontal j
    exact key (P.scale .horizontal j) (by omega) hj hi ((D.ms3_mem_contIndex P).1 hl).1 hr
      (by rw [hr1]; linarith) (by rw [hr1]; linarith) le_rfl
      (Metric.ball_subset_ball' (by rw [hr1]; linarith))

/-! ## Genuine records -/

/-- **`genuineRecords_timeCompatible`**. Constants `C = 20000 + 10⁴ C₀`,
`θ₁ = 1/300`, `A₁ = 4·10⁴ C₀`. -/
theorem genuineRecords_timeCompatible_proof (n : ℕ) :
    ∀ C₀ : ℝ, 0 < C₀ → ∃ C θ₁ A₁ : ℝ, 0 < C ∧ 0 < θ₁ ∧ 0 < A₁ ∧
      ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T) (B : ℝ),
        T.Available n k → k < n + 2 → ∀ hP : P.IsAdmissible, 0 < B →
        P.TailBound k T B → D.IsSourceConstruction P → P.θ ≤ θ₁ → A₁ * B ≤ P.a →
        T = .horizontal → D.FittedTimeComparison P (C₀ * (B / P.a)) →
        ∀ γ : ℝ, C * (P.θ ^ 2 + B / P.a) ≤ γ → D.GenuineTimeCompatible P hP.R_pos γ := by
  intro C₀ hC₀
  refine ⟨20000 + 10000 * C₀, 1 / 300, 40000 * C₀, by positivity, by norm_num, by positivity,
    ?_⟩
  intro k T P D B hT hk hP hB htail hD hθ hA hH hfit γ hγ
  subst hH
  have ha := hP.a_pos
  have hθ0 := hP.θ_pos
  have hBa : 0 ≤ B / P.a := div_nonneg hB.le ha.le
  have hK0 : 0 ≤ C₀ * (B / P.a) := mul_nonneg hC₀.le hBa
  have hθ2 : P.θ ^ 2 ≤ 1 / 90000 := by
    have := pow_le_pow_left₀ hθ0.le hθ 2
    norm_num at this
    linarith
  have hK1 : C₀ * (B / P.a) ≤ 1 / 40000 := by
    rw [← mul_div_assoc, div_le_iff₀ ha]
    linarith
  have hγ₀1 : 10000 * (2 * P.θ ^ 2 + C₀ * (B / P.a)) ≤ 1 / 2 := by linarith
  have hγ₀γ : 10000 * (2 * P.θ ^ 2 + C₀ * (B / P.a)) ≤ γ := by
    refine le_trans ?_ hγ
    nlinarith [sq_nonneg P.θ, mul_nonneg hC₀.le (sq_nonneg P.θ)]
  intro z w hz hw hgz hgw
  obtain ⟨jz, hjz, hpz, hsz⟩ := D.ms3_genuine_stage P hD hP.R_pos hz hgz
  obtain ⟨jw, hjw, hpw, hsw⟩ := D.ms3_genuine_stage P hD hP.R_pos hw hgw
  obtain ⟨hfit1, -⟩ := hfit
  have hpair := D.ms3_genuine_pair P hP.R_pos hK0 hθ0 hfit1 hjz hjw hpz hpw hsz hsw
  have hsz0 : 0 ≤ NeckRecord.scale (D.family P hP.R_pos) (D.radius P) z :=
    (P.scale_pos _ hP.R_pos jz).le.trans hsz
  have hsw0 : 0 ≤ NeckRecord.scale (D.family P hP.R_pos) (D.radius P) w :=
    (P.scale_pos _ hP.R_pos jw).le.trans hsw
  set pz := NeckRecord.position (D.family P hP.R_pos) z
  set pw := NeckRecord.position (D.family P hP.R_pos) w
  set sz := NeckRecord.scale (D.family P hP.R_pos) (D.radius P) z
  set sw := NeckRecord.scale (D.family P hP.R_pos) (D.radius P) w
  have hX : 0 ≤ max (‖pz.1 - pw.1‖ ^ 2) (max (sz ^ 2) (sw ^ 2)) :=
    (sq_nonneg _).trans (le_max_left _ _)
  have hb2 : max (dist pz pw) (max sz sw) ^ 2 ≤
      max (max (‖pz.1 - pw.1‖ ^ 2) (max (sz ^ 2) (sw ^ 2))) |pz.2.val - pw.2.val| := by
    refine ms3_sq_max_le ?_ ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
    rw [ms3_dist_sq_eq]
    exact max_le_max (le_max_left _ _) le_rfl
  exact ms3_absorb (abs_nonneg _) hX (by positivity) hγ₀1 hγ₀γ
    (hpair.trans (mul_le_mul_of_nonneg_left hb2 (by positivity)))

/-! ## All records -/

/-- **`recordsTimeCompatible_of_genuine`**, with `C = 1`. -/
theorem recordsTimeCompatible_of_genuine_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n)
      (D : ConstructionData n k T) (B : ℝ), T.Available n k → k < n + 2 →
      ∀ hP : P.IsAdmissible, 0 < B → D.IsSourceConstruction P → T = .horizontal →
      ∀ γ : ℝ, C * (P.θ ^ 2 + B / P.a) ≤ γ → D.GenuineTimeCompatible P hP.R_pos γ →
      RecordsTimeCompatible (D.family P hP.R_pos) (D.centers P) (D.radius P) γ := by
  refine ⟨1, one_pos, ?_⟩
  intro k T P D B hT hk hP hB hD hH γ hγ hgen
  subst hH
  have hθ0 := hP.θ_pos.le
  have hR0 := hP.R_pos.le
  have hθγ : P.θ ^ 2 ≤ γ := by
    have : 0 ≤ B / P.a := div_nonneg hB.le hP.a_pos.le
    linarith
  have hγ0 : 0 ≤ γ := (sq_nonneg _).trans hθγ
  -- every record has time within `(θR)²` of `τ_*`
  have hband : ∀ z, NeckRecord.IsRecord (D.family P hP.R_pos) (D.centers P) z →
      |(NeckRecord.position (D.family P hP.R_pos) z).2.val - D.rootTime| ≤ (P.θ * P.R) ^ 2 := by
    intro z hz
    rcases D.ms3_record_cases P hD hP.R_pos hz with hg | ⟨hpos, -⟩ | ⟨hcore, -⟩
    · obtain ⟨j, -, hmem, -⟩ := D.ms3_genuine_stage P hD hP.R_pos hz hg
      exact ms3_abs_time_sub_le D.rootPlane D.rootTime _ (mul_nonneg hθ0 hR0)
        (D.ms3_kept_zero_infEDist P (D.ms3_kept_anti P (Nat.zero_le _) hmem))
    · rw [hpos, hD.root_time rfl, sub_self, abs_zero]
      positivity
    · exact D.ms3_closure_kept_zero_time P hθ0 hR0 (mem_iInter.1 hcore 0)
  have hroot : (P.θ * P.R) ^ 2 ≤ γ * P.scale .horizontal 0 ^ 2 := by
    rw [P.ms3_scale_zero]
    show (P.θ * P.R) ^ 2 ≤ γ * (8 * P.R) ^ 2
    have h1 : P.θ ^ 2 * P.R ^ 2 ≤ γ * P.R ^ 2 := mul_le_mul_of_nonneg_right hθγ (sq_nonneg _)
    nlinarith [mul_nonneg hγ0 (sq_nonneg P.R)]
  -- a core point against a genuine record
  have hcoreGen : ∀ c ∈ D.coreLimit P, ∀ w, NeckRecord.IsRecord (D.family P hP.R_pos) (D.centers P) w →
      D.IsGenuineRecord P w →
      |c.2.val - (NeckRecord.position (D.family P hP.R_pos) w).2.val| ≤
        γ * max (‖c.1 - (NeckRecord.position (D.family P hP.R_pos) w).1‖ ^ 2)
          (max (0 ^ 2) (NeckRecord.scale (D.family P hP.R_pos) (D.radius P) w ^ 2)) := by
    intro c hc w hw hgw
    obtain ⟨idx, hidx, hlim⟩ := D.ms3_core_approx P hP.R_pos hc
    refine ms3_tc_limit hlim (P.ms3_scale_tendsto .horizontal) fun m => ?_
    have hrec : NeckRecord.IsRecord (D.family P hP.R_pos) (D.centers P) (Sum.inl (m + 1, idx m)) :=
      show idx m ∈ (D.family P hP.R_pos).index (m + 1) by
        rw [D.ms3_family_index_pos P hP.R_pos (by omega : m + 1 ≠ 0)]
        exact hidx m
    have h := hgen (Sum.inl (m + 1, idx m)) w hrec hw (show 1 ≤ m + 1 by omega) hgw
    rw [D.ms3_position_inl P hP.R_pos (by omega : m + 1 ≠ 0), D.ms3_scale_inl] at h
    exact h
  -- two core points
  have hcoreCore : ∀ c ∈ D.coreLimit P, ∀ c' ∈ D.coreLimit P,
      |c.2.val - c'.2.val| ≤ γ * max (‖c.1 - c'.1‖ ^ 2) (max (0 ^ 2) (0 ^ 2)) := by
    intro c hc c' hc'
    obtain ⟨idx, hidx, hlim⟩ := D.ms3_core_approx P hP.R_pos hc
    refine ms3_tc_limit hlim (P.ms3_scale_tendsto .horizontal) fun m => ?_
    have hrec : NeckRecord.IsRecord (D.family P hP.R_pos) (D.centers P) (Sum.inl (m + 1, idx m)) :=
      show idx m ∈ (D.family P hP.R_pos).index (m + 1) by
        rw [D.ms3_family_index_pos P hP.R_pos (by omega : m + 1 ≠ 0)]
        exact hidx m
    have h := hcoreGen c' hc' (Sum.inl (m + 1, idx m)) hrec (show 1 ≤ m + 1 by omega)
    rw [D.ms3_position_inl P hP.R_pos (by omega : m + 1 ≠ 0), D.ms3_scale_inl] at h
    exact ms3_tc_symm h
  -- assembly over the kinds of the two records
  have hrootRec : ∀ z w, NeckRecord.IsRecord (D.family P hP.R_pos) (D.centers P) w →
      NeckRecord.position (D.family P hP.R_pos) z = D.rootCenter →
      NeckRecord.scale (D.family P hP.R_pos) (D.radius P) z = P.scale .horizontal 0 →
      |(NeckRecord.position (D.family P hP.R_pos) z).2.val -
          (NeckRecord.position (D.family P hP.R_pos) w).2.val| ≤
        γ * max (‖(NeckRecord.position (D.family P hP.R_pos) z).1 -
            (NeckRecord.position (D.family P hP.R_pos) w).1‖ ^ 2)
          (max (NeckRecord.scale (D.family P hP.R_pos) (D.radius P) z ^ 2)
            (NeckRecord.scale (D.family P hP.R_pos) (D.radius P) w ^ 2)) := by
    intro z w hw hpz hsz
    rw [hpz, hsz, hD.root_time rfl, abs_sub_comm]
    calc |(NeckRecord.position (D.family P hP.R_pos) w).2.val - D.rootTime|
        ≤ (P.θ * P.R) ^ 2 := hband w hw
      _ ≤ γ * P.scale .horizontal 0 ^ 2 := hroot
      _ ≤ _ := mul_le_mul_of_nonneg_left
          ((le_max_left _ _).trans (le_max_right _ _)) hγ0
  intro z w hz hw
  rcases D.ms3_record_cases P hD hP.R_pos hz with hgz | ⟨hpz, hsz⟩ | ⟨hcz, hsz⟩
  · rcases D.ms3_record_cases P hD hP.R_pos hw with hgw | ⟨hpw, hsw⟩ | ⟨hcw, hsw⟩
    · exact hgen z w hz hw hgz hgw
    · exact ms3_tc_symm (hrootRec w z hz hpw hsw)
    · rw [hsw]
      exact ms3_tc_symm (hcoreGen _ hcw z hz hgz)
  · exact hrootRec z w hw hpz hsz
  · rcases D.ms3_record_cases P hD hP.R_pos hw with hgw | ⟨hpw, hsw⟩ | ⟨hcw, hsw⟩
    · rw [hsz]
      exact hcoreGen _ hcz w hw hgw
    · exact ms3_tc_symm (hrootRec w z hz hpw hsw)
    · rw [hsz, hsw]
      exact hcoreCore _ hcz _ hcw

end ParabolicRectifiability
