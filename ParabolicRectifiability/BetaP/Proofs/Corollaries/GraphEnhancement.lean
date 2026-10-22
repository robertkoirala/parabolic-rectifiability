import ParabolicRectifiability.BetaP.Proofs.Support.SupportTheorem
import ParabolicRectifiability.BetaP.Statements.Corollaries
import ParabolicRectifiability.Enhancements.Statements.GraphDomains

/-! # Graph-domain enhancement of the beta-`p` support theorem

The proof applies the fixed-carrier graph-domain statement
(`Enhancements.FixedCarrierGraphDomainStatement`, a hypothesis) separately to the two typed
compact supports produced by the support theorem (`BetaPSupportStatement`), combines the two singleton covers (bound `2C_D`), and converts the relative
charge bounds into the absolute ones: `H_P^k(K) ≤ C R^k` for the total charge and, for
`0 < s ≤ R`, `H_P^k(K ∩ P(q,2s)) ≤ C (2s)^k` when `2s ≤ R` and `≤ H_P^k(K) ≤ C R^k < C (2s)^k`
otherwise. The measures and supports are not changed.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- A graph-domain cover is one for every larger bound (same data). -/
def graphDomainCoverMono {n k : ℕ} {C C' ε δ : ℝ} {KH KV : Set (Space n)}
    (G : GraphDomainCover n k C ε δ KH KV) (hC : C ≤ C') : GraphDomainCover n k C' ε δ KH KV where
  horizontal := G.horizontal
  vertical := G.vertical
  trace_le := fun U hU =>
    (G.trace_le U hU).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hC) _)
  totalCharge_le := G.totalCharge_le.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hC) _)
  horizontal_totalCharge_le :=
    G.horizontal_totalCharge_le.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hC) _)
  vertical_totalCharge_le :=
    G.vertical_totalCharge_le.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hC) _)
  localCharge_le := fun q R hR =>
    (G.localCharge_le q R hR).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hC) _)
  horizontal_localCharge_le := fun q R hR =>
    (G.horizontal_localCharge_le q R hR).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hC) _)
  vertical_localCharge_le := fun q R hR =>
    (G.vertical_localCharge_le q R hR).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hC) _)

theorem ofReal_two_mul_eq (C : ℝ) (x : ℝ≥0∞) :
    ENNReal.ofReal C * x + ENNReal.ofReal C * x = ENNReal.ofReal (2 * C) * x := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, two_mul, add_mul]

/-- Two singleton graph-domain covers, of `(K_H, ∅)` and `(∅, K_V)`, combine into one cover of
`(K_H, K_V)` with bound `2C`: each typed family keeps its own relative bounds, and
`H_P^k` of each typed piece is at most `H_P^k` of the union. -/
def graphDomainCoverCombine {n k : ℕ} {C ε δ : ℝ} {KH KV : Set (Space n)} (hC : 0 ≤ C)
    (GH : GraphDomainCover n k C ε δ KH ∅) (GV : GraphDomainCover n k C ε δ ∅ KV) :
    GraphDomainCover n k (2 * C) ε δ KH KV where
  horizontal := GH.horizontal
  vertical := GV.vertical
  trace_le := fun U hU => by
    have h1 : GH.horizontal.traceVolume U ≤ ENNReal.ofReal C * hausdorffP n k ((KH ∪ KV) ∩ U) :=
      (le_self_add.trans (GH.trace_le U hU)).trans (mul_le_mul_right (measure_mono
        (inter_subset_inter_left U (union_subset_union_right KH (empty_subset KV)))) _)
    have h2 : GV.vertical.traceVolume U ≤ ENNReal.ofReal C * hausdorffP n k ((KH ∪ KV) ∩ U) :=
      (le_add_self.trans (GV.trace_le U hU)).trans (mul_le_mul_right (measure_mono
        (inter_subset_inter_left U (union_subset_union_left KV (empty_subset KH)))) _)
    exact (add_le_add h1 h2).trans_eq (ofReal_two_mul_eq C _)
  totalCharge_le := by
    have h1 : GH.horizontal.totalCharge ≤ ENNReal.ofReal C * hausdorffP n k (KH ∪ KV) :=
      (le_self_add.trans GH.totalCharge_le).trans (mul_le_mul_right (measure_mono
        (union_subset_union_right KH (empty_subset KV))) _)
    have h2 : GV.vertical.totalCharge ≤ ENNReal.ofReal C * hausdorffP n k (KH ∪ KV) :=
      (le_add_self.trans GV.totalCharge_le).trans (mul_le_mul_right (measure_mono
        (union_subset_union_left KV (empty_subset KH))) _)
    exact (add_le_add h1 h2).trans_eq (ofReal_two_mul_eq C _)
  horizontal_totalCharge_le :=
    (le_self_add.trans GH.totalCharge_le).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (by linarith)) (measure_mono (union_subset_union_right KH (empty_subset KV))))
  vertical_totalCharge_le :=
    (le_add_self.trans GV.totalCharge_le).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (by linarith)) (measure_mono (union_subset_union_left KV (empty_subset KH))))
  localCharge_le := fun q R hR => by
    have h1 : GH.horizontal.localCharge q R ≤
        ENNReal.ofReal C * hausdorffP n k ((KH ∪ KV) ∩ Metric.ball q (2 * R)) :=
      (le_self_add.trans (GH.localCharge_le q R hR)).trans (mul_le_mul_right (measure_mono
        (inter_subset_inter_left _ (union_subset_union_right KH (empty_subset KV)))) _)
    have h2 : GV.vertical.localCharge q R ≤
        ENNReal.ofReal C * hausdorffP n k ((KH ∪ KV) ∩ Metric.ball q (2 * R)) :=
      (le_add_self.trans (GV.localCharge_le q R hR)).trans (mul_le_mul_right (measure_mono
        (inter_subset_inter_left _ (union_subset_union_left KV (empty_subset KH)))) _)
    exact (add_le_add h1 h2).trans_eq (ofReal_two_mul_eq C _)
  horizontal_localCharge_le := fun q R hR =>
    (le_self_add.trans (GH.localCharge_le q R hR)).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (by linarith)) (measure_mono
        (inter_subset_inter_left _ (union_subset_union_right KH (empty_subset KV)))))
  vertical_localCharge_le := fun q R hR =>
    (le_add_self.trans (GV.localCharge_le q R hR)).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (by linarith)) (measure_mono
        (inter_subset_inter_left _ (union_subset_union_left KV (empty_subset KH)))))

/-- The fixed-carrier statement, applied to each available type of a support bundle,
gives one graph-domain cover of `(K_H, K_V)` with bound `C_D = 2C_A` for every `ε, δ > 0`.
An unavailable type has an empty support and uses the other type's cover. -/
theorem graphDomainCover_of_supportBounds (hFC : Enhancements.FixedCarrierGraphDomainStatement)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ CD : ℝ, 0 < CD ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ (Cs : ℝ) (a : Space n) (R : ℝ) (KH KV : Set (Space n)),
      HasRegularSupportBounds k Cs a R KH KV → ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        Nonempty (GraphDomainCover n k CD ε δ KH KV) := by
  obtain ⟨C, hC, h⟩ := hFC n hn
  refine ⟨2 * C, by positivity, ?_⟩
  intro k hk hkn Cs a R KH KV hS ε δ hε hδ
  have hfin : hausdorffP n k (KH ∪ KV) < ⊤ := hS.hausdorff_total.trans_lt ENNReal.ofReal_lt_top
  have hH : 1 ≤ k ∧ k ≤ n → Nonempty (GraphDomainCover n k C ε δ KH ∅) := fun hav => by
    obtain ⟨G, -⟩ := h k hk hkn .horizontal (by decide) (HorizontalModel.nonempty_iff.mpr hav) KH
      hS.horizontal_compact ((measure_mono subset_union_left).trans_lt hfin)
      (fun η hη => hS.horizontal_graphs η hη) ε δ hε hδ
    exact ⟨G⟩
  have hV : 2 ≤ k ∧ k ≤ n + 2 → Nonempty (GraphDomainCover n k C ε δ ∅ KV) := fun hav => by
    obtain ⟨G, -⟩ := h k hk hkn .vertical (by decide) (VerticalModel.nonempty_iff.mpr hav) KV
      hS.vertical_compact ((measure_mono subset_union_right).trans_lt hfin)
      (fun η hη => hS.vertical_graphs η hη) ε δ hε hδ
    exact ⟨G⟩
  by_cases hav : 1 ≤ k ∧ k ≤ n
  · by_cases hvav : 2 ≤ k ∧ k ≤ n + 2
    · exact ⟨graphDomainCoverCombine hC.le (hH hav).some (hV hvav).some⟩
    · obtain ⟨G⟩ := hH hav
      rw [hS.vertical_unavailable hvav]
      exact ⟨graphDomainCoverMono G (by linarith)⟩
  · have hvav : 2 ≤ k ∧ k ≤ n + 2 := by omega
    obtain ⟨G⟩ := hV hvav
    rw [hS.horizontal_unavailable hav]
    exact ⟨graphDomainCoverMono G (by linarith)⟩

/-- The relative local bound `H_P^k(K ∩ P(q,2s))` is at most `C 2^{n+2} s^k` for `0 < s ≤ R`. -/
theorem hausdorff_double_ball_le {n k : ℕ} (hkn : k ≤ n + 2) {Cs R s : ℝ} {a q : Space n}
    {KH KV : Set (Space n)} (hCs : 0 < Cs) (hS : HasRegularSupportBounds k Cs a R KH KV)
    (hs : 0 < s) (hsR : s ≤ R) :
    hausdorffP n k ((KH ∪ KV) ∩ Metric.ball q (2 * s)) ≤
      ENNReal.ofReal (Cs * 2 ^ (n + 2) * s ^ k) := by
  have h2k : (2 : ℝ) ^ k ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) hkn
  have hsk : 0 ≤ s ^ k := pow_nonneg hs.le k
  by_cases h2s : 2 * s ≤ R
  · refine (hS.hausdorff_local q (2 * s) (by positivity) h2s).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2k hCs.le) hsk
  · refine (measure_mono inter_subset_left).trans (hS.hausdorff_total.trans
      (ENNReal.ofReal_le_ofReal ?_))
    have hR : R ^ k ≤ (2 * s) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    rw [mul_pow] at hR
    calc Cs * R ^ k ≤ Cs * (2 ^ k * s ^ k) := mul_le_mul_of_nonneg_left hR hCs.le
      _ ≤ Cs * 2 ^ (n + 2) * s ^ k := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2k hCs.le) hsk

theorem ofReal_mul_le_ofReal {x : ℝ≥0∞} {a b : ℝ} (ha : 0 ≤ a) (hx : x ≤ ENNReal.ofReal b) :
    ENNReal.ofReal a * x ≤ ENNReal.ofReal (a * b) := by
  rw [ENNReal.ofReal_mul ha]
  exact mul_le_mul_right hx _

/-- Absolute charge bounds at scale `R`: from a support bundle with constant `C_s` and a cover
with bound `C_D`, the cost bounds hold with `C_D + C_D C_s 2^{n+2}`. -/
theorem costBounds_of_cover {n k : ℕ} (hkn : k ≤ n + 2) {Cs CD R : ℝ} {a : Space n}
    {KH KV : Set (Space n)} (hCs : 0 < Cs) (hCD : 0 < CD) (hR : 0 < R)
    (hS : HasRegularSupportBounds k Cs a R KH KV)
    (hG : ∀ ε δ : ℝ, 0 < ε → 0 < δ → Nonempty (GraphDomainCover n k CD ε δ KH KV)) :
    HasGraphDomainCostBounds k (CD + CD * Cs * 2 ^ (n + 2)) R KH KV := by
  intro ε δ hε δpos
  obtain ⟨G⟩ := hG ε δ hε δpos
  have hC1 : 0 ≤ CD * Cs * 2 ^ (n + 2) := by positivity
  have hle : CD * Cs * 2 ^ (n + 2) ≤ CD + CD * Cs * 2 ^ (n + 2) := by linarith
  have h2 : (1 : ℝ) ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
  have htot : ∀ x : ℝ≥0∞, x ≤ ENNReal.ofReal CD * hausdorffP n k (KH ∪ KV) →
      x ≤ ENNReal.ofReal ((CD + CD * Cs * 2 ^ (n + 2)) * R ^ k) := by
    intro x hx
    refine (hx.trans (ofReal_mul_le_ofReal hCD.le hS.hausdorff_total)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hRk : 0 ≤ R ^ k := pow_nonneg hR.le k
    have : CD * (Cs * R ^ k) ≤ CD * Cs * 2 ^ (n + 2) * R ^ k := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) h2) hRk
    exact this.trans (mul_le_mul_of_nonneg_right hle hRk)
  have hloc : ∀ (q : Space n) (s : ℝ), 0 < s → s ≤ R → ∀ x : ℝ≥0∞,
      x ≤ ENNReal.ofReal CD * hausdorffP n k ((KH ∪ KV) ∩ Metric.ball q (2 * s)) →
      x ≤ ENNReal.ofReal ((CD + CD * Cs * 2 ^ (n + 2)) * s ^ k) := by
    intro q s hs hsR x hx
    refine (hx.trans (ofReal_mul_le_ofReal hCD.le
      (hausdorff_double_ball_le hkn hCs hS hs hsR))).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← mul_assoc, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hle (pow_nonneg hs.le k)
  refine ⟨graphDomainCoverMono G (by linarith), htot _ G.totalCharge_le,
    htot _ G.horizontal_totalCharge_le, htot _ G.vertical_totalCharge_le,
    fun q s hs hsR => ⟨hloc q s hs hsR _ (G.localCharge_le q s hs),
      hloc q s hs hsR _ (G.horizontal_localCharge_le q s hs),
      hloc q s hs hsR _ (G.vertical_localCharge_le q s hs)⟩⟩

/-- Cost bounds are monotone in the constant (nonnegative parent radius). -/
theorem costBounds_mono {n k : ℕ} {C C' R : ℝ} {KH KV : Set (Space n)}
    (h : HasGraphDomainCostBounds k C R KH KV) (hC : C ≤ C') (hR : 0 ≤ R) :
    HasGraphDomainCostBounds k C' R KH KV := by
  intro ε δ hε hδ
  obtain ⟨G, h1, h2, h3, h4⟩ := h ε δ hε hδ
  have hRk : ∀ s : ℝ, 0 ≤ s → ENNReal.ofReal (C * s ^ k) ≤ ENNReal.ofReal (C' * s ^ k) :=
    fun s hs => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hs k))
  exact ⟨graphDomainCoverMono G hC, h1.trans (hRk R hR), h2.trans (hRk R hR), h3.trans (hRk R hR),
    fun q s hs hsR => ⟨(h4 q s hs hsR).1.trans (hRk s hs.le), (h4 q s hs hsR).2.1.trans
      (hRk s hs.le), (h4 q s hs hsR).2.2.trans (hRk s hs.le)⟩⟩

/-- Graph-domain enhancement from the support theorem and the fixed-carrier statement. -/
theorem betaPGraphEnhancement_of_support (hMT3 : BetaPSupportStatement)
    (hFC : Enhancements.FixedCarrierGraphDomainStatement) : BetaPGraphEnhancementStatement := by
  intro n hn p hp
  obtain ⟨Cs, hCs, hS⟩ := hMT3 n hn p hp
  obtain ⟨CD, hCD, hG⟩ := graphDomainCover_of_supportBounds hFC n hn
  have hCs_le : Cs ≤ Cs + (CD + CD * Cs * 2 ^ (n + 2)) := by
    have : 0 ≤ CD * Cs * 2 ^ (n + 2) := by positivity
    linarith
  have hCD_le : CD + CD * Cs * 2 ^ (n + 2) ≤ Cs + (CD + CD * Cs * 2 ^ (n + 2)) := by linarith
  have hcost : ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ (a : Space n) (R : ℝ), 0 < R →
      ∀ KH KV : Set (Space n), HasRegularSupportBounds k Cs a R KH KV →
      HasGraphDomainCostBounds k (Cs + (CD + CD * Cs * 2 ^ (n + 2))) R KH KV :=
    fun k hk hkn a R hR KH KV hB => costBounds_mono
      (costBounds_of_cover hkn hCs hCD hR hB (hG k hk hkn Cs a R KH KV hB)) hCD_le hR.le
  refine ⟨Cs + (CD + CD * Cs * 2 ^ (n + 2)), by positivity, ?_⟩
  intro k hk hkn T hT μ hμ hreg
  obtain ⟨hunit, hloc, hamb⟩ := hS k hk hkn T hT μ hμ hreg
  refine ⟨fun M Γ hM hΓ => ⟨fun hp2 hthr => ?_, fun hp2 hthr => ?_⟩,
    fun q R₀ hR₀ M Γ hM hΓ => ⟨fun hp2 hthr => ?_, fun hp2 hthr => ?_⟩, fun hk2 => ?_⟩
  · obtain ⟨μplus, μH, μV, hD⟩ := (hunit M Γ hM hΓ).1 hp2 hthr
    exact ⟨μplus, μH, μV, hD.mono hCs_le zero_le_one (add_le_add_left
      (mul_le_mul_of_nonneg_right hCs_le (Real.rpow_nonneg hM _)) Γ),
      hcost k hk hkn _ 1 one_pos _ _ hD.supports⟩
  · obtain ⟨μplus, μH, μV, hD⟩ := (hunit M Γ hM hΓ).2 hp2 hthr
    exact ⟨μplus, μH, μV, hD.mono hCs_le zero_le_one (add_le_add_left
      (mul_le_mul_of_nonneg_right hCs_le hM) Γ), hcost k hk hkn _ 1 one_pos _ _ hD.supports⟩
  · obtain ⟨μplus, μH, μV, hD⟩ := (hloc q R₀ hR₀ M Γ hM hΓ).1 hp2 hthr
    exact ⟨μplus, μH, μV, hD.mono hCs_le hR₀.le (add_le_add_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCs_le (Real.rpow_nonneg hM _)) (pow_nonneg hR₀.le k)) Γ),
      hcost k hk hkn _ R₀ hR₀ _ _ hD.supports⟩
  · obtain ⟨μplus, μH, μV, hD⟩ := (hloc q R₀ hR₀ M Γ hM hΓ).2 hp2 hthr
    exact ⟨μplus, μH, μV, hD.mono hCs_le hR₀.le (add_le_add_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCs_le hM) (pow_nonneg hR₀.le k)) Γ),
      hcost k hk hkn _ R₀ hR₀ _ _ hD.supports⟩
  · obtain ⟨μplus, μH, μV, hD⟩ := hamb hk2
    exact ⟨μplus, μH, μV, hD.mono hCs_le zero_le_one le_rfl,
      hcost k hk hkn _ 1 one_pos _ _ hD.supports⟩

/-- **Graph-domain enhancement.** Inputs: those of `betaPSupport_of_providers` and
`Enhancements.FixedCarrierGraphDomainStatement`. -/
theorem betaPGraphEnhancement_of_providers (hMT1 : Enhancements.RectifiableReifenbergTheoremStatement)
    (hAmb : AmbientLocalCoreStatement) (hB2 : BetaPowTwoStatement)
    (hFH : Characterization.FiniteHausdorffCriterionStatement)
    (hTR : Characterization.TypedRefinementSetStatement)
    (hFC : Enhancements.FixedCarrierGraphDomainStatement) :
    BetaPGraphEnhancementStatement :=
  betaPGraphEnhancement_of_support (betaPSupport_of_providers hMT1 hAmb hB2 hFH hTR) hFC

end ParabolicRectifiability.BetaP
