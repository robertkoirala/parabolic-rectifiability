import ParabolicRectifiability.QuantitativeCharacterization.Assembly.CarlesonEnergy
import ParabolicRectifiability.QuantitativeCharacterization.Assembly.Monotonicity
import ParabolicRectifiability.QuantitativeCharacterization.Assembly.TypedReferenceCovers

/-! # Covering supplies and the constants `L₀, C, B_loc`

Three predicates name what the forward and reverse covering results supply for fixed `n, k, A`:
* `LocalCoveringSupply`: under the local hypotheses at buffer `B_loc`, every `K' ≥ C₀(1+M)`
  admits a `(K',L₀)` covering of the root (from `exists_local_forward_covering` for `k < n + 2`,
  from `ambient_root_covering` at `k = n + 2`);
* `BoundedCoveringSupply`: on the bounded-support class with `M_β < ∞`, every
  `K' ≥ C₀(1+M_β)` admits at every root a `(K',L₀)` covering with a typed trace split, the
  measure identity and the relative tail `2^k + A²` (from `exists_bounded_forward_approximants`,
  resp. `ambient_root_covering`);
* `GlobalReverseBound`: under upper growth, the `(K,L₀)` property gives `M_β ≤ C_rev K` (from
  `exists_local_reverse_bound` through `global_reverse`).

The two supplies are monotone in `L₀, C₀, B_loc`; the reverse bound is not monotone in `L₀`, so it
is always taken **at the final `L₀`** and only then is `C` enlarged.
The assembly lemmas turn supplies into the bodies `MainTheoremBounds`, `LocalForwardBounds` and
`BoundedSupportBounds` of the statement layer. Each theorem then uses only the
results it needs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- Local chosen coverings at buffer `B_loc` with parameter `L₀` and forward constant `C₀`. -/
def LocalCoveringSupply (n k : ℕ) (A L₀ C₀ Bloc : ℝ) : Prop :=
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ M : ℝ, 0 ≤ M →
    (∀ b ∈ μ.support ∩ Metric.ball a (Bloc * R), ∀ s : ℝ, 0 < s → s ≤ Bloc * R →
      ENNReal.ofReal (A⁻¹ * s ^ k) ≤ μ (Metric.ball b s) ∧
        μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k) ∧
        (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) ≤
          ENNReal.ofReal (M * s ^ k)) →
    ∀ K' : ℝ, C₀ * (1 + M) ≤ K' → Nonempty (RegularMixedCovering k K' L₀ μ a R)

/-- Bounded-support chosen coverings with approximants and the relative tail. -/
def BoundedCoveringSupply (n k : ℕ) (A L₀ C₀ : ℝ) : Prop :=
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular → μ ≠ 0 →
    Bornology.IsBounded μ.support → 0 < Metric.diam μ.support →
    (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) →
    (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → r ≤ Metric.diam μ.support →
      ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball z r)) →
    carlesonEnergy μ k < ⊤ → ∀ K' : ℝ, C₀ * (1 + (carlesonEnergy μ k).toReal) ≤ K' →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R →
    ∃ 𝒞 : RegularMixedCovering k K' L₀ μ a R, ∃ FH FV : Set (Space n),
      𝒞.IsTypedTraceSplit FH FV ∧ 𝒞.MeasureIdentity FH FV ∧
      𝒞.RelativeTail ((2 : ℝ) ^ k + A ^ 2)

/-- The global reverse bound at the parameter `L₀`. -/
def GlobalReverseBound (n k : ℕ) (A L₀ Crev : ℝ) : Prop :=
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) →
    ∀ K : ℝ, 1 ≤ K → IsQuantitativelyMixedRectifiable k K L₀ μ →
      carlesonEnergy μ k ≤ ENNReal.ofReal (Crev * K)

theorem LocalCoveringSupply.mono {n k : ℕ} {A L₀ C₀ Bloc L₀' C₀' Bloc' : ℝ}
    (h : LocalCoveringSupply n k A L₀ C₀ Bloc) (hL : 1 ≤ L₀) (hLL : L₀ ≤ L₀')
    (hCC : C₀ ≤ C₀') (hBB : Bloc ≤ Bloc') : LocalCoveringSupply n k A L₀' C₀' Bloc' := by
  intro μ hfin hreg a ha R hR M hM hl K' hK'
  have hBR : Bloc * R ≤ Bloc' * R := mul_le_mul_of_nonneg_right hBB hR.le
  obtain ⟨𝒞⟩ := h μ hfin hreg a ha R hR M hM
    (fun b hb s hs hsle => hl b ⟨hb.1, Metric.ball_subset_ball hBR hb.2⟩ s hs (hsle.trans hBR))
    K' ((mul_le_mul_of_nonneg_right hCC (by linarith)).trans hK')
  exact ⟨𝒞.mono hR.le (by linarith) le_rfl hLL⟩

theorem BoundedCoveringSupply.mono {n k : ℕ} {A L₀ C₀ L₀' C₀' : ℝ}
    (h : BoundedCoveringSupply n k A L₀ C₀) (hL : 1 ≤ L₀) (hC : 0 < C₀) (hLL : L₀ ≤ L₀')
    (hCC : C₀ ≤ C₀') : BoundedCoveringSupply n k A L₀' C₀' := by
  intro μ hfin hreg hμ hbd hdiam hup hlow hM K' hK' a ha R hR
  have hM0 : 0 ≤ (carlesonEnergy μ k).toReal := ENNReal.toReal_nonneg
  have hK1 : C₀ * (1 + (carlesonEnergy μ k).toReal) ≤ K' :=
    (mul_le_mul_of_nonneg_right hCC (by linarith)).trans hK'
  have hK0 : 0 < K' := lt_of_lt_of_le (mul_pos hC (by linarith)) hK1
  obtain ⟨𝒞, FH, FV, hs, hid, ht⟩ := h μ hfin hreg hμ hbd hdiam hup hlow hM K' hK1 a ha R hR
  exact ⟨𝒞.mono hR.le (by linarith) le_rfl hLL, FH, FV, hs.mono, hid.mono,
    ht.mono (by positivity) hK0⟩

/-- The local covering supply: `exists_local_forward_covering` for `k < n + 2`,
`ambient_root_covering` at `k = n + 2`. -/
theorem exists_localCoveringSupply (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (A : ℝ) (hA : 1 ≤ A) :
    ∃ L₀ C₀ Bloc : ℝ, 1 ≤ L₀ ∧ 1 ≤ C₀ ∧ 1 ≤ Bloc ∧ LocalCoveringSupply n k A L₀ C₀ Bloc := by
  rcases lt_or_eq_of_le hkn with hlt | heq
  · obtain ⟨Bloc, hB, L₀, hL₀, C₀, hC₀, hloc⟩ :=
      exists_local_forward_covering n hn k hk hlt A hA
    refine ⟨L₀, C₀, Bloc, hL₀, hC₀, hB, fun μ hfin hreg a ha R hR M hM hl K' hK' => ?_⟩
    obtain ⟨𝒞⟩ := hloc μ hfin hreg a ha R hR M hM hl
    exact ⟨𝒞.mono hR.le (by linarith) hK' le_rfl⟩
  · subst heq
    refine ⟨2, 2 ^ (n + 2), 1, one_le_two, one_le_pow₀ one_le_two, le_rfl,
      fun μ hfin hreg a ha R hR M hM _ K' hK' => ?_⟩
    obtain ⟨𝒞, -⟩ := ambient_root_covering n hn μ hfin hreg a ha R hR
    have hKK : (2 : ℝ) ^ (n + 2) ≤ K' :=
      (le_mul_of_one_le_right (by positivity) (by linarith)).trans hK'
    exact ⟨𝒞.mono hR.le two_pos hKK le_rfl⟩

/-- The bounded covering supply: `exists_bounded_forward_approximants` for `k < n + 2`,
`ambient_root_covering` at `k = n + 2` (multiplicity one gives the tail for every constant). -/
theorem exists_boundedCoveringSupply (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) (A : ℝ) (hA : 1 ≤ A) :
    ∃ L₀ C₀ : ℝ, 1 ≤ L₀ ∧ 1 ≤ C₀ ∧ BoundedCoveringSupply n k A L₀ C₀ := by
  rcases lt_or_eq_of_le hkn with hlt | heq
  · obtain ⟨L₀, hL₀, C₀, hC₀, hbdd⟩ := exists_bounded_forward_approximants n hn k hk hlt A hA
    refine ⟨L₀, C₀, hL₀, hC₀, fun μ hfin hreg hμ hbd hdiam hup hlow hM K' hK' a ha R hR => ?_⟩
    obtain ⟨𝒞, FH, FV, hs, hid, ht⟩ := hbdd μ hfin hreg hμ hbd hdiam hup hlow hM a ha R hR
    have hM0 : 0 ≤ (carlesonEnergy μ k).toReal := ENNReal.toReal_nonneg
    exact ⟨𝒞.mono hR.le (by linarith) hK' le_rfl, FH, FV, hs.mono, hid.mono,
      ht.mono (by positivity) (mul_pos (by linarith) (by linarith))⟩
  · subst heq
    refine ⟨2, 2 ^ (n + 2), one_le_two, one_le_pow₀ one_le_two,
      fun μ hfin hreg _ _ _ _ _ _ K' hK' a ha R hR => ?_⟩
    obtain ⟨𝒞, -, -, hs, hid, ht, -⟩ := ambient_root_covering n hn μ hfin hreg a ha R hR
    have hM0 : 0 ≤ (carlesonEnergy μ (n + 2)).toReal := ENNReal.toReal_nonneg
    have hKK : (2 : ℝ) ^ (n + 2) ≤ K' :=
      (le_mul_of_one_le_right (by positivity) (by linarith)).trans hK'
    exact ⟨𝒞.mono hR.le two_pos hKK le_rfl, ∅, Metric.ball a R, hs.mono, hid.mono,
      (ht _).mono (by positivity) (by positivity)⟩

/-- **Assembly of `MainTheoremBounds`.** Forward clause: absolute continuity from the ADR upper
bound (`absolutelyContinuous_of_upper_growth`) and a covering at every root from the local supply
with `M = M_β`; reverse clause from the reverse bound at `L₀`; the equivalence from both. -/
theorem mainTheoremBounds_of_supply {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    {A L₀ C₀ Bloc Crev C : ℝ} (hloc : LocalCoveringSupply n k A L₀ C₀ Bloc)
    (hrev : GlobalReverseBound n k A L₀ Crev) (hC1 : 1 ≤ C) (hCC₀ : C₀ ≤ C)
    (hCrevC : Crev ≤ C) : MainTheoremBounds n k A L₀ C := by
  intro μ hfin hreg _ _ hADR
  have hup : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r →
      μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k) := fun z hz r hr => (hADR z hz r hr).2
  have hM0 : 0 ≤ (carlesonEnergy μ k).toReal := ENNReal.toReal_nonneg
  have hfwd : carlesonEnergy μ k < ⊤ →
      IsQuantitativelyMixedRectifiable k (C * (1 + (carlesonEnergy μ k).toReal)) L₀ μ := by
    intro hM
    refine ⟨absolutelyContinuous_of_upper_growth n hn k hk hkn μ hfin hreg A hup,
      fun a ha R hR => ?_⟩
    exact hloc μ hfin hreg a ha R hR _ hM0 (localHyps_of_isADR hADR hM.ne a Bloc R) _
      (mul_le_mul_of_nonneg_right hCC₀ (by linarith))
  have hrev' : ∀ K : ℝ, 1 ≤ K → IsQuantitativelyMixedRectifiable k K L₀ μ →
      carlesonEnergy μ k ≤ ENNReal.ofReal (C * K) := fun K hK hQ =>
    (hrev μ hfin hreg hup K hK hQ).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCrevC (by linarith)))
  exact ⟨⟨fun hM => ⟨_, one_le_mul_of_one_le_of_one_le hC1 (by linarith), hfwd hM⟩,
    fun ⟨K, hK, hQ⟩ => (hrev' K hK hQ).trans_lt ENNReal.ofReal_lt_top⟩, hfwd, hrev'⟩

/-- **Assembly of `LocalForwardBounds`.** The local supply gives the covering at `K = C(1+M)`;
`exists_root_approximants` on it gives the split, the identity, typed rectifiable approximants
(given the typed reference covers) and the relative tail from the root lower bound at `s = R`.
The growth buffer `2 L₀ R` lies inside `B_loc R`. -/
theorem localForwardBounds_of_supply {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    {A L₀ C Bloc : ℝ} (hA : 1 ≤ A) (hL₀ : 1 ≤ L₀) (hC1 : 1 ≤ C) (hB : 1 ≤ Bloc)
    (h2L : 2 * L₀ ≤ Bloc) (hloc : LocalCoveringSupply n k A L₀ C Bloc)
    (hcov : ∀ ρ : Reference n k L₀, ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover ρ.kind k ρ.measure ε) :
    LocalForwardBounds n k A Bloc L₀ C := by
  intro μ hfin hreg a ha R hR M hM hl
  obtain ⟨𝒞⟩ := hloc μ hfin hreg a ha R hR M hM hl (C * (1 + M)) le_rfl
  have hBR : 2 * L₀ * R ≤ Bloc * R := mul_le_mul_of_nonneg_right h2L hR.le
  have hRB : R ≤ Bloc * R := le_mul_of_one_le_left hR.le hB
  obtain ⟨FH, FV, hsplit, hid, hrect, htail, -⟩ :=
    exists_root_approximants n hn k hk hkn A hA L₀ hL₀ hcov (C * (1 + M))
      (one_le_mul_of_one_le_of_one_le hC1 (by linarith)) μ hfin hreg a ha R hR 𝒞
      fun b hb s hs hsle => (hl b ⟨hb.1, Metric.ball_subset_ball hBR hb.2⟩ s hs
        (hsle.trans hBR)).2.1
  exact ⟨𝒞, FH, FV, hsplit, hid,
    htail (hl a ⟨ha, Metric.mem_ball_self (mul_pos (by linarith) hR)⟩ R hR hRB).1, hrect⟩

/-- **Assembly of `BoundedSupportBounds`**, with `C(A,k) = max(2A, 2^k + 1)`. Clause 1 as for
the quantitative characterization (bounded supply, absolute continuity, reverse bound); clause 2 from
`exists_root_approximants` and `approximant_canonical_limits` with the canonical
decomposition (density hypothesis from growth below `D_E`); clause 3 from the bounded supply;
clause 4 from the reverse bound `M_β ≤ C_rev K` and the bounded supply at `K' = CK`. -/
theorem boundedSupportBounds_of_supply (hIS : Characterization.IntrinsicSufficiencyStatement)
    (hCan : IntegralCanonical.CanonicalDecompositionStatement) {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hkn : k ≤ n + 2) {A L₀ C₀ Crev C : ℝ} (hA : 1 ≤ A) (hC₀ : 1 ≤ C₀)
    (hCrev : 0 < Crev) (hbdd : BoundedCoveringSupply n k A L₀ C₀)
    (hrev : GlobalReverseBound n k A L₀ Crev) (hC1 : 1 ≤ C) (hCC₀ : C₀ ≤ C)
    (hCC : C₀ * (1 + Crev) ≤ C) (hCrevC : Crev ≤ C) :
    BoundedSupportBounds n k A (max (2 * A) ((2 : ℝ) ^ k + 1)) L₀ C := by
  intro μ hfin hreg hμ hbd hdiam hup hlow
  have hA0 : 0 < A := by linarith
  have hM0 : 0 ≤ (carlesonEnergy μ k).toReal := ENNReal.toReal_nonneg
  have hfwd : carlesonEnergy μ k < ⊤ →
      IsQuantitativelyMixedRectifiable k (C * (1 + (carlesonEnergy μ k).toReal)) L₀ μ := by
    intro hM
    refine ⟨absolutelyContinuous_of_upper_growth n hn k hk hkn μ hfin hreg A hup,
      fun a ha R hR => ?_⟩
    obtain ⟨𝒞, -⟩ := hbdd μ hfin hreg hμ hbd hdiam hup hlow hM _
      (mul_le_mul_of_nonneg_right hCC₀ (by linarith)) a ha R hR
    exact ⟨𝒞⟩
  have hrev' : ∀ K : ℝ, 1 ≤ K → IsQuantitativelyMixedRectifiable k K L₀ μ →
      carlesonEnergy μ k ≤ ENNReal.ofReal (C * K) := fun K hK hQ =>
    (hrev μ hfin hreg hup K hK hQ).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCrevC (by linarith)))
  refine ⟨⟨⟨fun hM => ⟨_, one_le_mul_of_one_le_of_one_le hC1 (by linarith), hfwd hM⟩,
    fun ⟨K, hK, hQ⟩ => (hrev' K hK hQ).trans_lt ENNReal.ofReal_lt_top⟩, hfwd, hrev'⟩,
    ?_, ?_, ?_⟩
  · -- prescribed coverings: approximants, tails and canonical limits
    intro L hL K hK a ha R hR 𝒞
    obtain ⟨FH, FV, hs, hid, hrect, htail, habs⟩ :=
      exists_root_approximants n hn k hk hkn A hA L hL (reference_typed_covers hIS hn hk hkn hL)
        K hK μ hfin hreg a ha R hR 𝒞 fun b hb s hs _ => hup b hb.1 s hs
    have hdens : HasPositiveFiniteUpperDensity k μ :=
      hasPositiveFiniteUpperDensity_of_growth hreg hA0 hdiam
        fun z hz r hr hrD => ⟨hlow z hz r hr hrD, hup z hz r hr⟩
    exact ⟨FH, FV, hs, hid, fun hRD => htail (hlow a ha R hR hRD), habs,
      approximant_canonical_limits n hn k hk hkn A L K hL hK μ hfin hreg
        (hCan n hn k hk hkn μ hfin hreg (Or.inr hdens) 1 one_pos) hup a ha R hR 𝒞 FH FV hs
        hrect⟩
  · -- chosen coverings from `M_β < ∞`
    intro hM a ha R hR
    exact hbdd μ hfin hreg hμ hbd hdiam hup hlow hM _
      (mul_le_mul_of_nonneg_right hCC₀ (by linarith)) a ha R hR
  · -- chosen coverings from a uniform `(K,L₀)` property
    intro K hK hQ a ha R hR
    have hMK := hrev μ hfin hreg hup K hK hQ
    have hMr : (carlesonEnergy μ k).toReal ≤ Crev * K :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCrev.le (by linarith)) hMK
    refine hbdd μ hfin hreg hμ hbd hdiam hup hlow (hMK.trans_lt ENNReal.ofReal_lt_top) (C * K)
      ?_ a ha R hR
    calc C₀ * (1 + (carlesonEnergy μ k).toReal) ≤ C₀ * (1 + Crev * K) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ ≤ C₀ * ((1 + Crev) * K) := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
      _ = C₀ * (1 + Crev) * K := by ring
      _ ≤ C * K := mul_le_mul_of_nonneg_right hCC (by linarith)

/-- One choice `L₀, C` for the body of part 1 of the quantitative characterization, from the local supply and the
reverse bound at its `L₀` only (no outside input). -/
theorem exists_mainTheoremBounds (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (A : ℝ) (hA : 1 ≤ A) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∃ C : ℝ, 1 ≤ C ∧ MainTheoremBounds n k A L₀ C := by
  obtain ⟨L₀, C₀, Bloc, hL₀, hC₀, -, hloc⟩ := exists_localCoveringSupply n hn k hk hkn A hA
  obtain ⟨Crev, hCrev, hrev⟩ := global_reverse n hn k hk hkn L₀ hL₀ A hA
  exact ⟨L₀, hL₀, C₀ + Crev, by linarith,
    mainTheoremBounds_of_supply hn hk hkn hloc hrev (by linarith) (by linarith) (by linarith)⟩

end ParabolicRectifiability.QuantitativeCharacterization
