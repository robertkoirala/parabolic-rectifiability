import ParabolicRectifiability.Enhancements.Assembly.MainTheorem
import ParabolicRectifiability.Enhancements.Statements.GraphDomains

/-! # Assembly of the graph-domain statements

Main theorems:

* `fixed_carrier_graph_domain_skeleton : FixedCarrierGraphDomainStatement`, from
  `exists_fixedCarrier_graphDomainCover` (the relative cover) and the elementary growth
  substitution;
* `graph_enhanced_of_main_and_fixedCarrier : RectifiableReifenbergTheoremStatement →
  FixedCarrierGraphDomainStatement → GraphEnhancedRectifiableReifenbergStatement`: apply the
  fixed-carrier theorem to each available retained type, combine the two typed families
  (factor two, no cross-type disjointness), use the local growth of the supports up to radius
  `2` (local bound up to radius `1`, global bound above), and empty families for unavailable
  types;
* `graph_enhanced_rectifiable_reifenberg_of_providers : CompactBridgeCoverStatement →
  GraphEnhancedRectifiableReifenbergStatement`, the composition with the proof of the parabolic rectifiable Reifenberg theorem.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Enhancements

open ParabolicRectifiability.Foundations

/-! ## Elementary facts about graph-domain covers -/

/-- Increasing the bound of a graph-domain cover; the data are unchanged. -/
def graphDomainCoverMono {n k : ℕ} {C C' ε δ : ℝ} {KH KV : Set (Space n)}
    (G : GraphDomainCover n k C ε δ KH KV) (hC : C ≤ C') :
    GraphDomainCover n k C' ε δ KH KV where
  horizontal := G.horizontal
  vertical := G.vertical
  trace_le := fun U hU =>
    (G.trace_le U hU).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC) le_rfl)
  totalCharge_le := G.totalCharge_le.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC) le_rfl)
  horizontal_totalCharge_le :=
    G.horizontal_totalCharge_le.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC) le_rfl)
  vertical_totalCharge_le :=
    G.vertical_totalCharge_le.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC) le_rfl)
  localCharge_le := fun q R hR =>
    (G.localCharge_le q R hR).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC) le_rfl)
  horizontal_localCharge_le := fun q R hR =>
    (G.horizontal_localCharge_le q R hR).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC) le_rfl)
  vertical_localCharge_le := fun q R hR =>
    (G.vertical_localCharge_le q R hR).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC) le_rfl)

/-- The singleton carrier pair of a fixed type has union `K`. -/
theorem singleton_carrier_union {α : Type*} (T : FamilyKind) (hT : T ≠ .mixed) (K : Set α) :
    ((if T = .horizontal then K else ∅) ∪ (if T = .vertical then K else ∅)) = K := by
  cases T with
  | horizontal => simp
  | vertical => simp
  | mixed => exact absurd rfl hT

/-- The empty horizontal data of the empty carrier (an unavailable or absent type). -/
def emptyHorizontalDomainData (n k : ℕ) (ε δ : ℝ) : HorizontalDomainData n k ε δ ∅ where
  graphIndex := ∅
  graph := fun j => (Set.notMem_empty _ j.2).elim
  trace := fun _ => ∅
  measurableSet_trace := fun _ => MeasurableSet.empty
  trace_subset := fun _ => empty_subset _
  pairwise_disjoint_trace := fun _ _ _ => Set.empty_disjoint _
  trace_cover := by simp
  measurableSet_tracePreimage := fun j => (Set.notMem_empty _ j.2).elim
  patchIndex := ∅
  patchGraph := fun α => (Set.notMem_empty _ α.2).elim
  center := fun α => (Set.notMem_empty _ α.2).elim
  center_mem_tracePreimage := fun α => (Set.notMem_empty _ α.2).elim
  centerPoint_mem := fun α => (Set.notMem_empty _ α.2).elim
  radius := fun _ => 1
  radius_pos := fun _ => one_pos
  radius_le := fun α => (Set.notMem_empty _ α.2).elim
  measurableSet_patch := fun α => (Set.notMem_empty _ α.2).elim
  patch_cover := by simp

/-- The empty vertical data of the empty carrier (an unavailable or absent type). -/
def emptyVerticalDomainData (n k : ℕ) (ε δ : ℝ) : VerticalDomainData n k ε δ ∅ where
  graphIndex := ∅
  graph := fun j => (Set.notMem_empty _ j.2).elim
  trace := fun _ => ∅
  measurableSet_trace := fun _ => MeasurableSet.empty
  trace_subset := fun _ => empty_subset _
  pairwise_disjoint_trace := fun _ _ _ => Set.empty_disjoint _
  trace_cover := by simp
  measurableSet_tracePreimage := fun j => (Set.notMem_empty _ j.2).elim
  patchIndex := ∅
  patchGraph := fun α => (Set.notMem_empty _ α.2).elim
  center := fun α => (Set.notMem_empty _ α.2).elim
  center_mem_tracePreimage := fun α => (Set.notMem_empty _ α.2).elim
  centerPoint_mem := fun α => (Set.notMem_empty _ α.2).elim
  radius := fun _ => 1
  radius_pos := fun _ => one_pos
  radius_le := fun α => (Set.notMem_empty _ α.2).elim
  measurableSet_patch := fun α => (Set.notMem_empty _ α.2).elim
  patch_cover := by simp

/-- `c + c ≤ C` in the form used for combining the two typed families. -/
theorem two_mul_le_of_le {x y z : ℝ≥0∞} {c C : ℝ} (h : 2 * c ≤ C)
    (hx : x ≤ ENNReal.ofReal c * z) (hy : y ≤ ENNReal.ofReal c * z) :
    x + y ≤ ENNReal.ofReal C * z := by
  have hc2 : ENNReal.ofReal c * z + ENNReal.ofReal c * z = ENNReal.ofReal (2 * c) * z := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, two_mul, add_mul]
  calc x + y ≤ ENNReal.ofReal c * z + ENNReal.ofReal c * z := add_le_add hx hy
    _ = ENNReal.ofReal (2 * c) * z := hc2
    _ ≤ ENNReal.ofReal C * z := mul_le_mul' (ENNReal.ofReal_le_ofReal h) le_rfl

/-- `x, y ≤ c` gives `x + y ≤ C` when `2 c ≤ C`. -/
theorem add_le_ofReal_of_le {x y : ℝ≥0∞} {c C : ℝ} (hc : 0 ≤ c) (h : 2 * c ≤ C)
    (hx : x ≤ ENNReal.ofReal c) (hy : y ≤ ENNReal.ofReal c) : x + y ≤ ENNReal.ofReal C := by
  calc x + y ≤ ENNReal.ofReal c + ENNReal.ofReal c := add_le_add hx hy
    _ = ENNReal.ofReal (2 * c) := by rw [← ENNReal.ofReal_add hc hc, two_mul]
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal h

/-! ## The fixed-carrier statement -/

/-- **Graph domains on a fixed carrier.**

The relative cover is `exists_fixedCarrier_graphDomainCover`. The growth clause is the
elementary substitution
`C H_P^k(K ∩ P(q,2R)) ≤ C A (2R)^k ≤ (C 2^{n+2}) A R^k` for `2R ≤ R_*`, with one enlarged
constant `C 2^{n+2}` for both clauses. -/
theorem fixed_carrier_graph_domain_skeleton : FixedCarrierGraphDomainStatement := by
  intro n hn
  obtain ⟨C, hC, hdom⟩ := exists_fixedCarrier_graphDomainCover n hn
  have hCC : C ≤ C * 2 ^ (n + 2) := le_mul_of_one_le_right hC.le (one_le_pow₀ (by norm_num))
  refine ⟨C * 2 ^ (n + 2), by positivity, ?_⟩
  intro k hk hkn T hTm hT K hK hKfin hcov ε δ hε hδ
  obtain ⟨G⟩ := hdom k hk hkn T hTm hT K hK hKfin hcov ε δ hε hδ
  refine ⟨graphDomainCoverMono G hCC, ?_⟩
  intro A Rs hA hRs hgrowth q R hR h2R
  have hloc := G.localCharge_le q R hR
  rw [singleton_carrier_union T hTm K] at hloc
  have hg := hgrowth q (2 * R) (by linarith) h2R
  have h2k : (2 : ℝ) ^ k ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) hkn
  have hAR : 0 ≤ C * A * R ^ k := by positivity
  calc (graphDomainCoverMono G hCC).horizontal.localCharge q R +
        (graphDomainCoverMono G hCC).vertical.localCharge q R
      = G.horizontal.localCharge q R + G.vertical.localCharge q R := rfl
    _ ≤ ENNReal.ofReal C * hausdorffP n k (K ∩ Metric.ball q (2 * R)) := hloc
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (A * (2 * R) ^ k) := mul_le_mul' le_rfl hg
    _ = ENNReal.ofReal (C * (A * (2 * R) ^ k)) := (ENNReal.ofReal_mul hC.le).symm
    _ ≤ ENNReal.ofReal (C * 2 ^ (n + 2) * A * R ^ k) := by
      apply ENNReal.ofReal_le_ofReal
      calc C * (A * (2 * R) ^ k) = (C * A * R ^ k) * 2 ^ k := by ring
        _ ≤ (C * A * R ^ k) * 2 ^ (n + 2) := mul_le_mul_of_nonneg_left h2k hAR
        _ = C * 2 ^ (n + 2) * A * R ^ k := by ring

/-! ## The graph enhancement on the supports of the parabolic rectifiable Reifenberg theorem -/

/-- The two typed halves for the supports of a unit support bundle with constant `A`:
for each type, domain data with the relative trace, global and local bounds (constant
`Cd` of the fixed-carrier statement) and the absolute local bound `Cd A s^k` for
`0 < s ≤ 1`. An available type uses `FixedCarrierGraphDomainStatement` on its own support
(whose local growth holds up to radius `2`: the local bound up to radius `1`, the global
bound `H_P^k(K) ≤ A ≤ A s^k` for `1 < s ≤ 2`); an unavailable type has empty support and
empty data. -/
theorem exists_typed_halves (hdom : FixedCarrierGraphDomainStatement) (n : ℕ) (hn : 1 ≤ n) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ A : ℝ, 0 ≤ A →
      ∀ KH KV : Set (Space n), HasRegularSupportBounds k A (point 0 0) 1 KH KV →
      ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      (∃ Dh : HorizontalDomainData n k ε δ KH,
        (∀ U, MeasurableSet U →
          Dh.traceVolume U ≤ ENNReal.ofReal Cd * hausdorffP n k (KH ∩ U)) ∧
        Dh.totalCharge ≤ ENNReal.ofReal Cd * hausdorffP n k KH ∧
        (∀ (q : Space n) (R : ℝ), 0 < R →
          Dh.localCharge q R ≤
            ENNReal.ofReal Cd * hausdorffP n k (KH ∩ Metric.ball q (2 * R))) ∧
        (∀ (q : Space n) (s : ℝ), 0 < s → s ≤ 1 →
          Dh.localCharge q s ≤ ENNReal.ofReal (Cd * A * s ^ k))) ∧
      (∃ Dv : VerticalDomainData n k ε δ KV,
        (∀ U, MeasurableSet U →
          Dv.traceVolume U ≤ ENNReal.ofReal Cd * hausdorffP n k (KV ∩ U)) ∧
        Dv.totalCharge ≤ ENNReal.ofReal Cd * hausdorffP n k KV ∧
        (∀ (q : Space n) (R : ℝ), 0 < R →
          Dv.localCharge q R ≤
            ENNReal.ofReal Cd * hausdorffP n k (KV ∩ Metric.ball q (2 * R))) ∧
        (∀ (q : Space n) (s : ℝ), 0 < s → s ≤ 1 →
          Dv.localCharge q s ≤ ENNReal.ofReal (Cd * A * s ^ k))) := by
  obtain ⟨Cd, hCd, hfix⟩ := hdom n hn
  refine ⟨Cd, hCd, ?_⟩
  intro k hk hkn A hA KH KV hS ε δ hε hδ
  have hKA : hausdorffP n k (KH ∪ KV) ≤ ENNReal.ofReal A := by
    simpa only [one_pow, mul_one] using hS.hausdorff_total
  -- local growth of any subset of the supports up to radius `2`
  have hgrow : ∀ K' ⊆ KH ∪ KV, ∀ (q : Space n) (s : ℝ), 0 < s → s ≤ 2 →
      hausdorffP n k (K' ∩ Metric.ball q s) ≤ ENNReal.ofReal (A * s ^ k) := by
    intro K' hK' q s hs hs2
    by_cases hs1 : s ≤ 1
    · exact (measure_mono (inter_subset_inter_left _ hK')).trans
        (hS.hausdorff_local q s hs hs1)
    · rw [not_le] at hs1
      calc hausdorffP n k (K' ∩ Metric.ball q s) ≤ hausdorffP n k (KH ∪ KV) :=
            measure_mono (inter_subset_left.trans hK')
        _ ≤ ENNReal.ofReal A := hKA
        _ = ENNReal.ofReal (A * 1 ^ k) := by rw [one_pow, mul_one]
        _ ≤ ENNReal.ofReal (A * s ^ k) := ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le_one hs1.le k) hA)
  have hfin : ∀ K' ⊆ KH ∪ KV, hausdorffP n k K' < ⊤ := fun K' hK' =>
    (measure_mono hK').trans_lt (hKA.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨?_, ?_⟩
  · by_cases hav : Nonempty (Models n k .horizontal)
    · have e1 : (if (FamilyKind.horizontal : FamilyKind) = .horizontal then KH else ∅) = KH := by
        simp
      have e2 : (if (FamilyKind.horizontal : FamilyKind) = .vertical then KH else ∅) = ∅ := by
        simp
      have h := hfix k hk hkn .horizontal (by decide) hav KH hS.horizontal_compact
        (hfin KH subset_union_left) (fun η hη => hS.horizontal_graphs η hη) ε δ hε hδ
      rw [e1, e2] at h
      obtain ⟨G, hGg⟩ := h
      refine ⟨G.horizontal, fun U hU => ?_, ?_, fun q R hR => ?_, fun q s hs hs1 => ?_⟩
      · have := G.trace_le U hU
        rw [union_empty] at this
        exact le_self_add.trans this
      · have := G.horizontal_totalCharge_le
        rwa [union_empty] at this
      · have := G.horizontal_localCharge_le q R hR
        rwa [union_empty] at this
      · exact le_self_add.trans (hGg A 2 hA two_pos (hgrow KH subset_union_left) q s hs
          (by linarith))
    · have hKH : KH = ∅ :=
        hS.horizontal_unavailable fun h => hav (HorizontalModel.nonempty_iff.mpr h)
      subst hKH
      refine ⟨emptyHorizontalDomainData n k ε δ, fun U _ => ?_, ?_, fun q R _ => ?_,
        fun q s _ _ => ?_⟩
      · exact (le_of_eq (ENNReal.tsum_eq_zero.mpr fun j => (Set.notMem_empty _ j.2).elim)).trans
          zero_le
      · exact (le_of_eq (ENNReal.tsum_eq_zero.mpr fun α => (Set.notMem_empty _ α.2).elim)).trans
          zero_le
      · exact (le_of_eq (ENNReal.tsum_eq_zero.mpr fun α =>
          (Set.notMem_empty _ α.1.2).elim)).trans zero_le
      · exact (le_of_eq (ENNReal.tsum_eq_zero.mpr fun α =>
          (Set.notMem_empty _ α.1.2).elim)).trans zero_le
  · by_cases hav : Nonempty (Models n k .vertical)
    · have e1 : (if (FamilyKind.vertical : FamilyKind) = .horizontal then KV else ∅) = ∅ := by
        simp
      have e2 : (if (FamilyKind.vertical : FamilyKind) = .vertical then KV else ∅) = KV := by
        simp
      have h := hfix k hk hkn .vertical (by decide) hav KV hS.vertical_compact
        (hfin KV subset_union_right) (fun η hη => hS.vertical_graphs η hη) ε δ hε hδ
      rw [e1, e2] at h
      obtain ⟨G, hGg⟩ := h
      refine ⟨G.vertical, fun U hU => ?_, ?_, fun q R hR => ?_, fun q s hs hs1 => ?_⟩
      · have := G.trace_le U hU
        rw [empty_union] at this
        exact le_add_self.trans this
      · have := G.vertical_totalCharge_le
        rwa [empty_union] at this
      · have := G.vertical_localCharge_le q R hR
        rwa [empty_union] at this
      · exact le_add_self.trans (hGg A 2 hA two_pos (hgrow KV subset_union_right) q s hs
          (by linarith))
    · have hKV : KV = ∅ :=
        hS.vertical_unavailable fun h => hav (VerticalModel.nonempty_iff.mpr h)
      subst hKV
      refine ⟨emptyVerticalDomainData n k ε δ, fun U _ => ?_, ?_, fun q R _ => ?_,
        fun q s _ _ => ?_⟩
      · exact (le_of_eq (ENNReal.tsum_eq_zero.mpr fun j => (Set.notMem_empty _ j.2).elim)).trans
          zero_le
      · exact (le_of_eq (ENNReal.tsum_eq_zero.mpr fun α => (Set.notMem_empty _ α.2).elim)).trans
          zero_le
      · exact (le_of_eq (ENNReal.tsum_eq_zero.mpr fun α =>
          (Set.notMem_empty _ α.1.2).elim)).trans zero_le
      · exact (le_of_eq (ENNReal.tsum_eq_zero.mpr fun α =>
          (Set.notMem_empty _ α.1.2).elim)).trans zero_le

/-- Combining the two typed halves into one graph-domain cover of `(K_H, K_V)` with bound
`Cfin` and the absolute charge bounds at scale `1` (`Σ_T H_P^k(K_T ∩ U) ≤ 2 H_P^k(K ∩ U)`;
the global absolute bound from `H_P^k(K) ≤ A`). -/
theorem hasScaledGraphDomainCover_of_halves {n k : ℕ} {Cd A Cfin ε δ : ℝ}
    {KH KV : Set (Space n)} (hCd : 0 ≤ Cd) (hA : 0 ≤ A) (h2 : 2 * Cd ≤ Cfin)
    (h2A : 2 * (Cd * A) ≤ Cfin) (hK : hausdorffP n k (KH ∪ KV) ≤ ENNReal.ofReal A)
    (Dh : HorizontalDomainData n k ε δ KH) (Dv : VerticalDomainData n k ε δ KV)
    (hHt : ∀ U, MeasurableSet U →
      Dh.traceVolume U ≤ ENNReal.ofReal Cd * hausdorffP n k (KH ∩ U))
    (hHc : Dh.totalCharge ≤ ENNReal.ofReal Cd * hausdorffP n k KH)
    (hHl : ∀ (q : Space n) (R : ℝ), 0 < R →
      Dh.localCharge q R ≤ ENNReal.ofReal Cd * hausdorffP n k (KH ∩ Metric.ball q (2 * R)))
    (hHg : ∀ (q : Space n) (s : ℝ), 0 < s → s ≤ 1 →
      Dh.localCharge q s ≤ ENNReal.ofReal (Cd * A * s ^ k))
    (hVt : ∀ U, MeasurableSet U →
      Dv.traceVolume U ≤ ENNReal.ofReal Cd * hausdorffP n k (KV ∩ U))
    (hVc : Dv.totalCharge ≤ ENNReal.ofReal Cd * hausdorffP n k KV)
    (hVl : ∀ (q : Space n) (R : ℝ), 0 < R →
      Dv.localCharge q R ≤ ENNReal.ofReal Cd * hausdorffP n k (KV ∩ Metric.ball q (2 * R)))
    (hVg : ∀ (q : Space n) (s : ℝ), 0 < s → s ≤ 1 →
      Dv.localCharge q s ≤ ENNReal.ofReal (Cd * A * s ^ k)) :
    HasScaledGraphDomainCover k KH KV Cfin ε δ 1 := by
  have hCdC : Cd ≤ Cfin := by linarith
  have hHK : ∀ S : Set (Space n), hausdorffP n k (KH ∩ S) ≤ hausdorffP n k ((KH ∪ KV) ∩ S) :=
    fun S => measure_mono (inter_subset_inter_left _ subset_union_left)
  have hVK : ∀ S : Set (Space n), hausdorffP n k (KV ∩ S) ≤ hausdorffP n k ((KH ∪ KV) ∩ S) :=
    fun S => measure_mono (inter_subset_inter_left _ subset_union_right)
  have hHK' : hausdorffP n k KH ≤ hausdorffP n k (KH ∪ KV) := measure_mono subset_union_left
  have hVK' : hausdorffP n k KV ≤ hausdorffP n k (KH ∪ KV) := measure_mono subset_union_right
  have hmono : ∀ {x y : ℝ≥0∞}, x ≤ y → ENNReal.ofReal Cd * x ≤ ENNReal.ofReal Cfin * y :=
    fun hxy => mul_le_mul' (ENNReal.ofReal_le_ofReal hCdC) hxy
  have hHc' : Dh.totalCharge ≤ ENNReal.ofReal (Cd * A) := by
    rw [ENNReal.ofReal_mul hCd]
    exact hHc.trans (mul_le_mul' le_rfl (hHK'.trans hK))
  have hVc' : Dv.totalCharge ≤ ENNReal.ofReal (Cd * A) := by
    rw [ENNReal.ofReal_mul hCd]
    exact hVc.trans (mul_le_mul' le_rfl (hVK'.trans hK))
  have hCdA : 0 ≤ Cd * A := mul_nonneg hCd hA
  let G : GraphDomainCover n k Cfin ε δ KH KV :=
    { horizontal := Dh
      vertical := Dv
      trace_le := fun U hU => two_mul_le_of_le h2
        ((hHt U hU).trans (mul_le_mul' le_rfl (hHK U)))
        ((hVt U hU).trans (mul_le_mul' le_rfl (hVK U)))
      totalCharge_le := two_mul_le_of_le h2
        (hHc.trans (mul_le_mul' le_rfl hHK')) (hVc.trans (mul_le_mul' le_rfl hVK'))
      horizontal_totalCharge_le := hHc.trans (hmono hHK')
      vertical_totalCharge_le := hVc.trans (hmono hVK')
      localCharge_le := fun q R hR => two_mul_le_of_le h2
        ((hHl q R hR).trans (mul_le_mul' le_rfl (hHK _)))
        ((hVl q R hR).trans (mul_le_mul' le_rfl (hVK _)))
      horizontal_localCharge_le := fun q R hR => (hHl q R hR).trans (hmono (hHK _))
      vertical_localCharge_le := fun q R hR => (hVl q R hR).trans (hmono (hVK _)) }
  refine ⟨G, ?_, ?_, ?_, fun q s hs hs1 => ⟨?_, ?_, ?_⟩⟩
  · rw [one_pow, mul_one]
    exact add_le_ofReal_of_le hCdA h2A hHc' hVc'
  · rw [one_pow, mul_one]
    exact hHc'.trans (ENNReal.ofReal_le_ofReal (by linarith))
  · rw [one_pow, mul_one]
    exact hVc'.trans (ENNReal.ofReal_le_ofReal (by linarith))
  · have hsk : 0 ≤ s ^ k := pow_nonneg hs.le k
    have h2' : 2 * (Cd * A * s ^ k) ≤ Cfin * s ^ k := by nlinarith
    exact add_le_ofReal_of_le (by positivity) h2' (hHg q s hs hs1) (hVg q s hs hs1)
  · have hsk : 0 ≤ s ^ k := pow_nonneg hs.le k
    exact (hHg q s hs hs1).trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  · have hsk : 0 ≤ s ^ k := pow_nonneg hs.le k
    exact (hVg q s hs hs1).trans (ENNReal.ofReal_le_ofReal (by nlinarith))

/-- **Graph-domain enhancement.** From the parabolic rectifiable Reifenberg theorem and the
fixed-carrier statement. The same retained sets `D` (hence the same measures, supports
and remainder bound) serve every tolerance and mesh; the final constant is
`(1 + C)(1 + 2 Cd)`. -/
theorem graph_enhanced_of_main_and_fixedCarrier (hmain : RectifiableReifenbergTheoremStatement)
    (hdom : FixedCarrierGraphDomainStatement) : GraphEnhancedRectifiableReifenbergStatement := by
  intro n hn
  obtain ⟨C, hC, hmix, hfix, hamb⟩ := hmain n hn
  obtain ⟨Cd, hCd, hhalves⟩ := exists_typed_halves hdom n hn
  have hCCd : 0 < C * Cd := mul_pos hC hCd
  have hCC : C ≤ (1 + C) * (1 + 2 * Cd) := by nlinarith
  have h2 : 2 * Cd ≤ (1 + C) * (1 + 2 * Cd) := by nlinarith
  have h2A : 2 * (Cd * C) ≤ (1 + C) * (1 + 2 * Cd) := by nlinarith
  have hcov : ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ KH KV : Set (Space n),
      HasRegularSupportBounds k C (point 0 0) 1 KH KV →
      ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        HasScaledGraphDomainCover k KH KV ((1 + C) * (1 + 2 * Cd)) ε δ 1 := by
    intro k hk hkn KH KV hS ε δ hε hδ
    obtain ⟨⟨Dh, hHt, hHc, hHl, hHg⟩, ⟨Dv, hVt, hVc, hVl, hVg⟩⟩ :=
      hhalves k hk hkn C hC.le KH KV hS ε δ hε hδ
    exact hasScaledGraphDomainCover_of_halves hCd.le hC.le h2 h2A
      (by simpa only [one_pow, mul_one] using hS.hausdorff_total)
      Dh Dv hHt hHc hHl hHg hVt hVc hVl hVg
  refine ⟨(1 + C) * (1 + 2 * Cd), by positivity, ?_, ?_, ?_⟩
  · intro k hk hkn μ hμ hreg M Γ hM hΓ hbad
    obtain ⟨D, hD⟩ := hmix k hk hkn μ hμ hreg M Γ hM hΓ hbad
    exact ⟨D, rectifiableReifenbergDecomposition_mono_constant hD hCC hM,
      hcov k hk hkn _ _ hD.supports⟩
  · intro k hk hkn T hTm hT μ hμ hreg M Γ hM hΓ hbad
    obtain ⟨D, hD, hH, hV⟩ := hfix k hk hkn T hTm hT μ hμ hreg M Γ hM hΓ hbad
    exact ⟨D, rectifiableReifenbergDecomposition_mono_constant hD hCC hM, hH, hV,
      hcov k hk hkn _ _ hD.supports⟩
  · intro μ hμ hreg
    obtain ⟨D, hD, hrem⟩ := hamb μ hμ hreg
    exact ⟨D, rectifiableReifenbergDecomposition_mono_constant hD hCC le_rfl, hrem,
      hcov (n + 2) (by omega) le_rfl _ _ hD.supports⟩

/-- **Graph-domain enhancement over the hypotheses.** The only auxiliary
statement used is `CompactBridgeCoverStatement` (through the parabolic rectifiable Reifenberg theorem). -/
theorem graph_enhanced_rectifiable_reifenberg_of_providers (hbridge : CompactBridgeCoverStatement) :
    GraphEnhancedRectifiableReifenbergStatement :=
  graph_enhanced_of_main_and_fixedCarrier (rectifiable_reifenberg_theorem_of_providers hbridge)
    fixed_carrier_graph_domain_skeleton

end ParabolicRectifiability.Enhancements
