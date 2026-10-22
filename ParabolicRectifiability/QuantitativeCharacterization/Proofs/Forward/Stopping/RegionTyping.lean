import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Stopping

/-! # Typed good regions with exact optimal models (`d1b_regionTyping`)

Proof of
`PartitionTreeStatement → ExactModelStatement → MixedAttainmentStatement →
  AdjacentTypeStatement → RegionTypingStatement`.
The four hypotheses are the preceding statements of the stopping construction.

Part (a): the optimizer/normalization bridges and the type induction.
* `d1btyping_fit_toMixed`: a typed model and its mixed embedding have the same fit.
* `d1btyping_modelCoeff_eq_coeff`: a typed model whose fit on the coefficient ball is at most that
  of every mixed model has normalized error equal to the coefficient `a_Q` (`betaSq_of_pos`).
* `d1btyping_attains_of_optimal`: an exact `T`-minimizer attains the mixed infimum as soon as a
  `T`-model does.
* `d1btyping_type_eq`: adjacent-type rigidity at one parent/child pair forces equal types.
* `d1btyping_scale_le`, `d1btyping_buffer`: `ℓ_Q ≤ R` and the buffer
  `P(z_Q, 4 ℓ_Q) ⊆ P(a, ρ)`, `4 ℓ_Q ≤ ρ` for every member (`z_Q ∈ P(a, 5R)`, `9R ≤ ρ`).
* `d1btyping_typeInduction`: by induction on `Q.1 - S.1`, every member's exact `T`-minimizer
  attains the mixed infimum on its coefficient ball; `d1btyping_minimizer_attains` states it for
  every exact `T`-minimizer.

Part (b): the `GoodRegion` with root `S` and members `F.members S`; `model_optimal` is exact
(the normalized error of the chosen minimizer equals the coefficient) and `budget` is the
chain budget rewritten term by term.
* `d1btyping_budget`: `chain_budget` rewritten by `model_optimal` (`tsum_congr`).
* `d1btyping_goodRegion`: the `GoodRegion` from the forest data, the type and the models.
* `d1b_regionTyping_proof`: the statement `RegionTypingStatement`.

Helper prefix `d1btyping_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

open ParabolicRectifiability.Foundations

/-! ## Optimizer and normalization bridges -/

/-- The mixed embedding of a model of the type `T`: `Sum.inl` horizontally, `Sum.inr`
vertically. -/
def d1btyping_toMixed {n k : ℕ} : (T : NeckType) → Models n k T.toFamilyKind → Models n k .mixed
  | .horizontal, L => (Sum.inl L : AdmissibleModel n k)
  | .vertical, L => (Sum.inr L : AdmissibleModel n k)

/-- A typed model and its mixed embedding have the same fit on every ball. -/
theorem d1btyping_fit_toMixed {n k : ℕ} (μ : Measure (Space n)) (T : NeckType)
    (L : Models n k T.toFamilyKind) (z : Space n) (r : ℝ) :
    fit μ (d1btyping_toMixed T L) z r = fit μ L z r := by
  cases T <;> rfl

/-- A typed model whose fit is at most that of every mixed model attains the mixed infimum. -/
theorem d1btyping_fit_eq_iInf {n k : ℕ} (μ : Measure (Space n)) (T : NeckType)
    (L : Models n k T.toFamilyKind) (z : Space n) (r : ℝ)
    (hL : ∀ L' : Models n k .mixed, fit μ L z r ≤ fit μ L' z r) :
    fit μ L z r = ⨅ L' : Models n k .mixed, fit μ L' z r :=
  le_antisymm (le_iInf hL)
    ((iInf_le (fun L' : Models n k .mixed => fit μ L' z r) (d1btyping_toMixed T L)).trans_eq
      (d1btyping_fit_toMixed μ T L z r))

/-- **Normalization bridge.** A typed model whose fit on the coefficient ball `P(z_Q, Λ ℓ_Q)`,
`Λ ℓ_Q > 0`, is at most that of every mixed model has normalized error equal to the coefficient:
`modelCoeff = a_Q = β_μ(z_Q, Λ ℓ_Q)²`. -/
theorem d1btyping_modelCoeff_eq_coeff {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}
    (P : DirectPartition E ℓ₀) (μ : Measure (Space n)) {k : ℕ} (Λ : ℝ) (T : NeckType)
    (L : Models n k T.toFamilyKind) (Q : ℕ × Space n) (hr : 0 < Λ * P.scale Q.1)
    (hL : ∀ L' : Models n k .mixed,
      fit μ L Q.2 (Λ * P.scale Q.1) ≤ fit μ L' Q.2 (Λ * P.scale Q.1)) :
    P.modelCoeff μ Λ L Q = P.coeff μ k Λ Q := by
  unfold DirectPartition.modelCoeff DirectPartition.coeff
  rw [betaSq_of_pos μ k .mixed Q.2 hr, d1btyping_fit_eq_iInf μ T L Q.2 _ hL]

/-- **Optimizer bridge.** An exact `T`-minimizer on a ball attains the mixed infimum there as
soon as some model of the same type does. -/
theorem d1btyping_attains_of_optimal {n k : ℕ} (μ : Measure (Space n)) {T T' : NeckType}
    (h : T' = T) {L : Models n k T.toFamilyKind} {z : Space n} {r : ℝ}
    (hopt : ∀ L'' : Models n k T.toFamilyKind, fit μ L z r ≤ fit μ L'' z r)
    (L₁ : Models n k T'.toFamilyKind)
    (hL₁ : ∀ L' : Models n k .mixed, fit μ L₁ z r ≤ fit μ L' z r) :
    ∀ L' : Models n k .mixed, fit μ L z r ≤ fit μ L' z r := by
  subst h
  exact fun L' => (hopt L₁).trans (hL₁ L')

/-- **Type rigidity at one pair.** If no horizontal/vertical pair of models on the cells `Q`
(child) and `Q'` (parent) has both normalized errors `≤ b/2`, then a `T`-model on `Q'` and a
`T'`-model on `Q`, both with normalized error `≤ b/2`, have the same type. -/
theorem d1btyping_type_eq {n k : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {Λ b : ℝ} {Q Q' : ℕ × Space n}
    (hadj : ∀ (H : Models n k .horizontal) (V : Models n k .vertical),
      ¬ ((P.modelCoeff μ Λ H Q ≤ ENNReal.ofReal (b / 2) ∧
            P.modelCoeff μ Λ V Q' ≤ ENNReal.ofReal (b / 2)) ∨
          (P.modelCoeff μ Λ V Q ≤ ENNReal.ofReal (b / 2) ∧
            P.modelCoeff μ Λ H Q' ≤ ENNReal.ofReal (b / 2))))
    (T T' : NeckType) (L : Models n k T.toFamilyKind) (L₁ : Models n k T'.toFamilyKind)
    (hL : P.modelCoeff μ Λ L Q' ≤ ENNReal.ofReal (b / 2))
    (hL₁ : P.modelCoeff μ Λ L₁ Q ≤ ENNReal.ofReal (b / 2)) : T' = T := by
  cases T <;> cases T'
  · rfl
  · exact (hadj L L₁ (Or.inr ⟨hL₁, hL⟩)).elim
  · exact (hadj L₁ L (Or.inl ⟨hL₁, hL⟩)).elim
  · rfl

/-! ## The buffer of a member -/

/-- Every side is at most the top side: `ℓ_j = R / 10^j ≤ R`. -/
theorem d1btyping_scale_le {n : ℕ} {E : Set (Space n)} {R : ℝ} (hR : 0 < R)
    (P : DirectPartition E R) (j : ℕ) : P.scale j ≤ R := by
  show R / 10 ^ j ≤ R
  exact div_le_self hR.le (one_le_pow₀ (by norm_num))

/-- **The buffer of a member.** For a member `Q` of the region of a root `S`, `z_Q ∈ P(a, 5R)`
and `4 ℓ_Q ≤ 4R`, so `P(z_Q, 4 ℓ_Q) ⊆ P(a, 9R) ⊆ P(a, ρ)` and `4 ℓ_Q ≤ ρ`. -/
theorem d1btyping_buffer {n k : ℕ} {E : Set (Space n)} {μ : Measure (Space n)} {Λ b : ℝ}
    {a : Space n} {R ρ : ℝ} (hR : 0 < R) (h9R : 9 * R ≤ ρ) {P : DirectPartition E R}
    (hP : PartitionTree P) (F : StoppingForest P μ k Λ b a R) {S : ℕ × Space n}
    (hS : S ∈ F.roots) {Q : ℕ × Space n} (hQ : Q ∈ F.members S) :
    Metric.ball Q.2 (4 * P.scale Q.1) ⊆ Metric.ball a ρ ∧ 4 * P.scale Q.1 ≤ ρ := by
  have hQS : P.IsBelow Q S := F.below_root S hS Q hQ
  have hQf : P.InForest a R Q := hP.inForest_of_isBelow a R Q S (F.roots_forest S hS) hQS
  have hz : Q.2 ∈ Metric.ball a (R + 4 * R) :=
    hP.inForest_subset a R Q hQf (hP.center_mem_cell Q hQS.1)
  have hd : dist Q.2 a < R + 4 * R := Metric.mem_ball.mp hz
  have hs : P.scale Q.1 ≤ R := d1btyping_scale_le hR P Q.1
  refine ⟨Metric.ball_subset_ball' ?_, ?_⟩ <;> linarith

/-! ## The type induction -/

/-- **The type induction.** Let `T` be a type and `model Q` an exact `T`-minimizer
on the coefficient ball `P(z_Q, Λ ℓ_Q)` of every cell, and suppose `model S` attains the mixed
infimum at the root `S`. If adjacent-type rigidity holds for every parent/child pair whose child
has its buffer in `P(a, ρ)`, then `model Q` attains the mixed infimum at every member `Q` of the
region of `S`. Induction on `Q.1 - S.1`: the parent `Q⁺` of `Q ≠ S` is a member (heredity), its
model attains the mixed infimum, so its normalized error is `a_{Q⁺} ≤ b/2`; a mixed optimizer at
`Q` (`MixedAttainmentStatement`) has normalized error `a_Q ≤ b/2`, so by rigidity it has type
`T`, and the exact `T`-minimizer `model Q` does at least as well. -/
theorem d1btyping_typeInduction {n k : ℕ} (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hk2 : k < n + 2)
    (hMix : MixedAttainmentStatement) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) {Λ b : ℝ} (hΛ : 0 < Λ) {a : Space n} {R ρ : ℝ}
    (hR : 0 < R) (h9R : 9 * R ≤ ρ) {P : DirectPartition μ.support R} (hP : PartitionTree P)
    (hadj : ∀ (Q Q' : ℕ × Space n), P.IsCell Q' → P.IsBelow Q Q' → Q'.1 + 1 = Q.1 →
      Metric.ball Q.2 (4 * P.scale Q.1) ⊆ Metric.ball a ρ → 4 * P.scale Q.1 ≤ ρ →
      ∀ (H : Models n k .horizontal) (V : Models n k .vertical),
        ¬ ((P.modelCoeff μ Λ H Q ≤ ENNReal.ofReal (b / 2) ∧
              P.modelCoeff μ Λ V Q' ≤ ENNReal.ofReal (b / 2)) ∨
            (P.modelCoeff μ Λ V Q ≤ ENNReal.ofReal (b / 2) ∧
              P.modelCoeff μ Λ H Q' ≤ ENNReal.ofReal (b / 2))))
    (F : StoppingForest P μ k Λ b a R) {S : ℕ × Space n} (hS : S ∈ F.roots)
    (T : NeckType) (model : ℕ × Space n → Models n k T.toFamilyKind)
    (hopt : ∀ (Q : ℕ × Space n) (L : Models n k T.toFamilyKind),
      fit μ (model Q) Q.2 (Λ * P.scale Q.1) ≤ fit μ L Q.2 (Λ * P.scale Q.1))
    (hroot : ∀ L' : Models n k .mixed,
      fit μ (model S) S.2 (Λ * P.scale S.1) ≤ fit μ L' S.2 (Λ * P.scale S.1)) :
    ∀ Q ∈ F.members S, ∀ L' : Models n k .mixed,
      fit μ (model Q) Q.2 (Λ * P.scale Q.1) ≤ fit μ L' Q.2 (Λ * P.scale Q.1) := by
  have hpos : ∀ Q : ℕ × Space n, 0 < Λ * P.scale Q.1 := fun Q => mul_pos hΛ (hP.scale_pos Q.1)
  have hScell : P.IsCell S := (F.below_root S hS S (F.root_mem S hS)).1
  have key : ∀ d : ℕ, ∀ Q ∈ F.members S, Q.1 = S.1 + d → ∀ L' : Models n k .mixed,
      fit μ (model Q) Q.2 (Λ * P.scale Q.1) ≤ fit μ L' Q.2 (Λ * P.scale Q.1) := by
    intro d
    induction d with
    | zero =>
      intro Q hQ hlev
      have hQS : Q = S :=
        hP.eq_of_isBelow Q S hScell (F.below_root S hS Q hQ) (by omega)
      rw [hQS]
      exact hroot
    | succ d ih =>
      intro Q hQ hlev
      have hQb : P.IsBelow Q S := F.below_root S hS Q hQ
      obtain ⟨Qp, hQpcell, hQplev, hQQp⟩ := hP.exists_ancestor Q hQb.1 (S.1 + d) (by omega)
      have hQpS : P.IsBelow Qp S :=
        hP.isBelow_of_common Q S Qp hScell hQpcell hQb hQQp (by omega)
      have hQpmem : Qp ∈ F.members S := F.hereditary S hS Q hQ Qp hQQp hQpS
      have hQpb : P.modelCoeff μ Λ (model Qp) Qp ≤ ENNReal.ofReal (b / 2) := by
        rw [d1btyping_modelCoeff_eq_coeff P μ Λ T (model Qp) Qp (hpos Qp)
          (ih Qp hQpmem hQplev)]
        exact F.member_coeff S hS Qp hQpmem
      obtain ⟨T', -, L₁, hL₁⟩ := hMix n hn k hk1 hk2 μ hμ Q.2 (Λ * P.scale Q.1)
      have hL₁b : P.modelCoeff μ Λ L₁ Q ≤ ENNReal.ofReal (b / 2) := by
        rw [d1btyping_modelCoeff_eq_coeff P μ Λ T' L₁ Q (hpos Q) hL₁]
        exact F.member_coeff S hS Q hQ
      obtain ⟨hball, h4⟩ := d1btyping_buffer hR h9R hP F hS hQ
      have hlv : Qp.1 + 1 = Q.1 := by omega
      have hTT : T' = T :=
        d1btyping_type_eq (hadj Q Qp hQpcell hQQp hlv hball h4) T T' (model Qp) L₁ hQpb hL₁b
      exact d1btyping_attains_of_optimal μ hTT (hopt Q) L₁ hL₁
  intro Q hQ
  have hle : S.1 ≤ Q.1 := (F.below_root S hS Q hQ).2.1
  exact key (Q.1 - S.1) Q hQ (by omega)

/-- **Every exact `T`-minimizer attains the mixed value** at every member: under the
hypotheses of the type induction, any `L` with `fit L ≤ fit L''` for every `T`-model `L''` on the
coefficient ball of a member `Q` has fit at most that of every mixed model there. -/
theorem d1btyping_minimizer_attains {n k : ℕ} (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hk2 : k < n + 2)
    (hMix : MixedAttainmentStatement) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) {Λ b : ℝ} (hΛ : 0 < Λ) {a : Space n} {R ρ : ℝ}
    (hR : 0 < R) (h9R : 9 * R ≤ ρ) {P : DirectPartition μ.support R} (hP : PartitionTree P)
    (hadj : ∀ (Q Q' : ℕ × Space n), P.IsCell Q' → P.IsBelow Q Q' → Q'.1 + 1 = Q.1 →
      Metric.ball Q.2 (4 * P.scale Q.1) ⊆ Metric.ball a ρ → 4 * P.scale Q.1 ≤ ρ →
      ∀ (H : Models n k .horizontal) (V : Models n k .vertical),
        ¬ ((P.modelCoeff μ Λ H Q ≤ ENNReal.ofReal (b / 2) ∧
              P.modelCoeff μ Λ V Q' ≤ ENNReal.ofReal (b / 2)) ∨
            (P.modelCoeff μ Λ V Q ≤ ENNReal.ofReal (b / 2) ∧
              P.modelCoeff μ Λ H Q' ≤ ENNReal.ofReal (b / 2))))
    (F : StoppingForest P μ k Λ b a R) {S : ℕ × Space n} (hS : S ∈ F.roots)
    (T : NeckType) (model : ℕ × Space n → Models n k T.toFamilyKind)
    (hopt : ∀ (Q : ℕ × Space n) (L : Models n k T.toFamilyKind),
      fit μ (model Q) Q.2 (Λ * P.scale Q.1) ≤ fit μ L Q.2 (Λ * P.scale Q.1))
    (hroot : ∀ L' : Models n k .mixed,
      fit μ (model S) S.2 (Λ * P.scale S.1) ≤ fit μ L' S.2 (Λ * P.scale S.1))
    {Q : ℕ × Space n} (hQ : Q ∈ F.members S) (L : Models n k T.toFamilyKind)
    (hL : ∀ L'' : Models n k T.toFamilyKind,
      fit μ L Q.2 (Λ * P.scale Q.1) ≤ fit μ L'' Q.2 (Λ * P.scale Q.1)) :
    ∀ L' : Models n k .mixed,
      fit μ L Q.2 (Λ * P.scale Q.1) ≤ fit μ L' Q.2 (Λ * P.scale Q.1) :=
  d1btyping_attains_of_optimal μ rfl hL (model Q)
    (d1btyping_typeInduction hn hk1 hk2 hMix hμ hΛ hR h9R hP hadj F hS T model hopt hroot Q hQ)

/-! ## The good region -/

/-- **Budget bridge.** If every member's model has normalized error equal to its coefficient, the
model chain sum of a member is its chain sum, hence at most `b` by `chain_budget`. -/
theorem d1btyping_budget {n k : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {Λ b : ℝ} {a : Space n} {R : ℝ} (F : StoppingForest P μ k Λ b a R)
    {S : ℕ × Space n} (hS : S ∈ F.roots) {T : NeckType}
    (model : ℕ × Space n → Models n k T.toFamilyKind)
    (hmo : ∀ Q ∈ F.members S, P.modelCoeff μ Λ (model Q) Q = P.coeff μ k Λ Q) :
    ∀ Q ∈ F.members S,
      (∑' Q' : {Q' : ℕ × Space n // Q' ∈ F.members S ∧ P.IsBelow Q Q'},
        P.modelCoeff μ Λ (model Q'.1) Q'.1) ≤ ENNReal.ofReal b := by
  intro Q hQ
  have h : chainSum P μ k Λ (F.members S) Q ≤ ENNReal.ofReal b := F.chain_budget S hS Q hQ
  unfold chainSum at h
  refine le_trans (le_of_eq ?_) h
  exact tsum_congr fun Q' : {Q' : ℕ × Space n // Q' ∈ F.members S ∧ P.IsBelow Q Q'} =>
    hmo Q'.1 Q'.2.1

/-- The good region of a root `S` with members `F.members S`, type `T` and models `model`, once
`model_optimal` is known. -/
def d1btyping_goodRegion {n k : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {Λ b : ℝ} {a : Space n} {R : ℝ} (F : StoppingForest P μ k Λ b a R)
    {S : ℕ × Space n} (hS : S ∈ F.roots) (T : NeckType) (hT : NeckType.Available n k T)
    (model : ℕ × Space n → Models n k T.toFamilyKind)
    (hmo : ∀ Q ∈ F.members S, P.modelCoeff μ Λ (model Q) Q = P.coeff μ k Λ Q) :
    GoodRegion P μ k Λ b where
  root := S
  root_isCell := (F.below_root S hS S (F.root_mem S hS)).1
  members := F.members S
  root_mem := F.root_mem S hS
  below_root := F.below_root S hS
  hereditary := F.hereditary S hS
  type := T
  type_available := hT
  model := model
  model_optimal := hmo
  budget := d1btyping_budget F hS model hmo

/-- **Typed good regions with exact optimal models** (`RegionTypingStatement`).
`b₀` is that of `AdjacentTypeStatement`; the type `T` is that of a
mixed optimizer at the root (`MixedAttainmentStatement`); `model Q` is an exact `T`-minimizer on
`P(z_Q, Λ ℓ_Q)` (`ExactModelStatement`); by the type induction every member's model attains the
mixed infimum, so `model_optimal` holds exactly (`betaSq_of_pos`, `Λ ℓ_Q > 0`) and `budget` is
`chain_budget` rewritten term by term. -/
theorem d1b_regionTyping_proof :
    PartitionTreeStatement → ExactModelStatement → MixedAttainmentStatement →
      AdjacentTypeStatement → RegionTypingStatement := by
  intro hTree hExact hMix hAdj n hn k hk1 hk2 A hA Λ hΛ
  obtain ⟨b₀, hb₀, hb⟩ := hAdj n hn k hk1 hk2 A hA Λ hΛ
  refine ⟨b₀, hb₀, ?_⟩
  intro b hbpos hbb₀ μ hμ a R ρ hR h9R hADR P F S hS
  have hP : PartitionTree P := hTree n μ.support R P
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (by norm_num) hΛ
  have hadj := hb b hbpos hbb₀ μ a ρ R hADR P
  obtain ⟨T, hT, L₀, hL₀⟩ := hMix n hn k hk1 hk2 μ hμ S.2 (Λ * P.scale S.1)
  obtain ⟨model, hopt⟩ : ∃ model : ℕ × Space n → Models n k T.toFamilyKind,
      ∀ (Q : ℕ × Space n) (L : Models n k T.toFamilyKind),
        fit μ (model Q) Q.2 (Λ * P.scale Q.1) ≤ fit μ L Q.2 (Λ * P.scale Q.1) :=
    ⟨fun Q => Classical.choose (hExact n k μ hμ T hT Q.2 (Λ * P.scale Q.1)),
      fun Q => Classical.choose_spec (hExact n k μ hμ T hT Q.2 (Λ * P.scale Q.1))⟩
  have hroot : ∀ L' : Models n k .mixed,
      fit μ (model S) S.2 (Λ * P.scale S.1) ≤ fit μ L' S.2 (Λ * P.scale S.1) :=
    fun L' => (hopt S L₀).trans (hL₀ L')
  have hind : ∀ Q ∈ F.members S, ∀ L' : Models n k .mixed,
      fit μ (model Q) Q.2 (Λ * P.scale Q.1) ≤ fit μ L' Q.2 (Λ * P.scale Q.1) :=
    d1btyping_typeInduction hn hk1 hk2 hMix hμ hΛ0 hR h9R hP hadj F hS T model hopt hroot
  have hmo : ∀ Q ∈ F.members S, P.modelCoeff μ Λ (model Q) Q = P.coeff μ k Λ Q :=
    fun Q hQ => d1btyping_modelCoeff_eq_coeff P μ Λ T (model Q) Q
      (mul_pos hΛ0 (hP.scale_pos Q.1)) (hind Q hQ)
  exact ⟨d1btyping_goodRegion F hS T hT model hmo, rfl, rfl⟩

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
