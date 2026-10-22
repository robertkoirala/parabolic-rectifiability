import ParabolicRectifiability.Metric.Measure

/-!
# Separated sets and Minkowski neighborhoods from packing

Proof of `separated_minkowski_of_packing`, as `separated_minkowski_of_packing_proof`.

An `r`-separated finite subset of `K` carries disjoint balls of radius `r/2`, so the
variable-radius packing bound gives at most `2^k C_p (R/r)^k` points. Hence finite
`r`-separated subsets of `K` have bounded cardinality and one of maximal cardinality is a
maximal separated set: every point of `K` is within `r` of it. The `r`-neighborhood of `K`
then lies in the union of the radius-`2r` balls about its points, whose total ambient
volume is at most `2^k C_p (R/r)^k · 2 ω_n (2r)^{n+2} ≤ C C_p R^k r^{n+2-k}`. No
compactness of `K` is used; `C_p = 0` and `k = 0` are allowed.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-- **`separated_minkowski_of_packing`**, with
`C = 2^{n+2} (1 + 2 ω_n 2^{n+2})`. -/
theorem separated_minkowski_of_packing_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), k ≤ n + 2 → ∀ (K : Set (Space n)) (R Cp : ℝ), 0 < R → 0 ≤ Cp →
      (∀ (I : Type) [Countable I] (z : I → Space n) (r : I → ℝ),
        (∀ i, z i ∈ K) → (∀ i, 0 < r i ∧ r i ≤ R) →
        (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
        ∑' i, ENNReal.ofReal (r i) ^ k ≤ ENNReal.ofReal (Cp * R ^ k)) →
      (∀ r : ℝ, 0 < r → r ≤ R → ∀ P : Finset (Space n), (↑P : Set (Space n)) ⊆ K →
        (∀ x ∈ P, ∀ y ∈ P, x ≠ y → r ≤ dist x y) → (P.card : ℝ) ≤ C * Cp * (R / r) ^ k) ∧
      (∀ r : ℝ, 0 < r → r ≤ R →
        parabolicVolume n {z | Metric.infEDist z K < ENNReal.ofReal r} ≤
          ENNReal.ofReal (C * Cp * R ^ k * r ^ (n + 2 - k))) := by
  have hw : 0 ≤ (omega n).toReal := ENNReal.toReal_nonneg
  have hA : 0 ≤ 2 * (omega n).toReal * 2 ^ (n + 2) := by positivity
  refine ⟨2 ^ (n + 2) * (1 + 2 * (omega n).toReal * 2 ^ (n + 2)), by positivity, ?_⟩
  intro k hk K R Cp hR hCp hpack
  have h2k : (2 : ℝ) ^ k ≤ 2 ^ (n + 2) := pow_le_pow_right₀ one_le_two hk
  -- the separated-set bound with the sharp constant `2^k`
  have hcard : ∀ r : ℝ, 0 < r → r ≤ R → ∀ P : Finset (Space n), (↑P : Set (Space n)) ⊆ K →
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → r ≤ dist x y) →
      (P.card : ℝ) ≤ 2 ^ k * Cp * (R / r) ^ k := by
    intro r hr hrR P hPK hPsep
    have hr0 : r ≠ 0 := hr.ne'
    have h := hpack P (fun x => (x : Space n)) (fun _ => r / 2) (fun x => hPK x.2)
      (fun _ => ⟨half_pos hr, by show r / 2 ≤ R; linarith⟩) (by
        intro x y hxy
        show Disjoint (Metric.ball (x : Space n) (r / 2)) (Metric.ball (y : Space n) (r / 2))
        apply Metric.ball_disjoint_ball
        have := hPsep x x.2 y y.2 (fun h => hxy (Subtype.ext h))
        linarith)
    have hsum : ENNReal.ofReal ((P.card : ℝ) * (r / 2) ^ k) =
        ∑' x : P, ENNReal.ofReal (r / 2) ^ k := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ r / 2)]
    have h' := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCp (pow_nonneg hR.le k))).mp
      (hsum.trans_le h)
    have hpos : 0 < (r / 2) ^ k := by positivity
    calc (P.card : ℝ) ≤ Cp * R ^ k / (r / 2) ^ k := (le_div_iff₀ hpos).mpr h'
      _ = 2 ^ k * Cp * (R / r) ^ k := by
          rw [div_pow, div_pow, div_div_eq_mul_div]
          ring
  have hC : 2 ^ (n + 2) * (2 * (omega n).toReal * 2 ^ (n + 2)) ≤
      2 ^ (n + 2) * (1 + 2 * (omega n).toReal * 2 ^ (n + 2)) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hC2 : (2 : ℝ) ^ k ≤ 2 ^ (n + 2) * (1 + 2 * (omega n).toReal * 2 ^ (n + 2)) := by
    calc (2 : ℝ) ^ k ≤ 2 ^ (n + 2) := h2k
      _ ≤ 2 ^ (n + 2) * (1 + 2 * (omega n).toReal * 2 ^ (n + 2)) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
  refine ⟨fun r hr hrR P hPK hPsep => ?_, fun r hr hrR => ?_⟩
  · calc (P.card : ℝ) ≤ 2 ^ k * Cp * (R / r) ^ k := hcard r hr hrR P hPK hPsep
      _ ≤ 2 ^ (n + 2) * (1 + 2 * (omega n).toReal * 2 ^ (n + 2)) * Cp * (R / r) ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hCp) (by positivity)
  · -- a maximal `r`-separated finite subset of `K`
    classical
    obtain ⟨P, ⟨hPK, hPsep⟩, hPmax⟩ : ∃ P : Finset (Space n),
        ((↑P : Set (Space n)) ⊆ K ∧ ∀ x ∈ P, ∀ y ∈ P, x ≠ y → r ≤ dist x y) ∧
          ∀ y ∈ K, ∃ x ∈ P, dist y x < r := by
      obtain ⟨cards, hcards⟩ : ∃ cards : Set ℕ, ∀ m, m ∈ cards ↔
          ∃ P : Finset (Space n), ((↑P : Set (Space n)) ⊆ K ∧
            ∀ x ∈ P, ∀ y ∈ P, x ≠ y → r ≤ dist x y) ∧ P.card = m :=
        ⟨_, fun _ => Iff.rfl⟩
      have hne : cards.Nonempty :=
        ⟨0, (hcards 0).mpr ⟨∅, ⟨by simp, by simp⟩, Finset.card_empty⟩⟩
      have hbdd : BddAbove cards := by
        refine ⟨⌈2 ^ k * Cp * (R / r) ^ k⌉₊, fun m hm => ?_⟩
        obtain ⟨P, ⟨hPK, hPs⟩, rfl⟩ := (hcards m).mp hm
        have := (hcard r hr hrR P hPK hPs).trans (Nat.le_ceil _)
        exact_mod_cast this
      obtain ⟨P, hPS, hPc⟩ := (hcards _).mp (Nat.sSup_mem hne hbdd)
      refine ⟨P, hPS, fun y hy => ?_⟩
      by_contra hfar
      simp only [not_exists, not_and, not_lt] at hfar
      have hyP : y ∉ P := fun hyP => by
        have := hfar y hyP
        rw [dist_self] at this
        linarith
      have hS' : ((↑(insert y P) : Set (Space n)) ⊆ K ∧
          ∀ x ∈ insert y P, ∀ y' ∈ insert y P, x ≠ y' → r ≤ dist x y') := by
        refine ⟨?_, ?_⟩
        · rw [Finset.coe_insert]
          exact Set.insert_subset hy hPS.1
        · intro a ha b hb hab
          rw [Finset.mem_insert] at ha hb
          rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · exact absurd rfl hab
          · exact hfar b hb
          · rw [dist_comm]; exact hfar a ha
          · exact hPS.2 a ha b hb hab
      have hmem : (insert y P).card ∈ cards := (hcards _).mpr ⟨insert y P, hS', rfl⟩
      have hle := le_csSup hbdd hmem
      rw [Finset.card_insert_of_notMem hyP, ← hPc] at hle
      omega
    -- the neighborhood is covered by the radius-`2r` balls about `P`
    have hcov : {z | Metric.infEDist z K < ENNReal.ofReal r} ⊆ ⋃ x ∈ P, Metric.ball x (2 * r) := by
      intro z hz
      obtain ⟨y, hyK, hzy⟩ := Metric.infEDist_lt_iff.mp hz
      obtain ⟨x, hxP, hyx⟩ := hPmax y hyK
      rw [edist_lt_ofReal] at hzy
      exact mem_iUnion₂.mpr ⟨x, hxP, Metric.mem_ball.mpr (by linarith [dist_triangle z y x])⟩
    have hvol : parabolicVolume n {z | Metric.infEDist z K < ENNReal.ofReal r} ≤
        ENNReal.ofReal ((P.card : ℝ) * (2 * (omega n).toReal * (2 * r) ^ (n + 2))) := by
      calc parabolicVolume n {z | Metric.infEDist z K < ENNReal.ofReal r}
          ≤ parabolicVolume n (⋃ x ∈ P, Metric.ball x (2 * r)) := measure_mono hcov
        _ ≤ ∑ x ∈ P, parabolicVolume n (Metric.ball x (2 * r)) := measure_biUnion_finset_le P _
        _ = ∑ _x ∈ P, 2 * omega n * ENNReal.ofReal (2 * r) ^ (n + 2) :=
            Finset.sum_congr rfl fun x _ => parabolicVolume_ball x _ (by positivity)
        _ = ENNReal.ofReal ((P.card : ℝ) * (2 * (omega n).toReal * (2 * r) ^ (n + 2))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            have h1 : ENNReal.ofReal ((P.card : ℝ) * (2 * (omega n).toReal * (2 * r) ^ (n + 2))) =
                (P.card : ℝ≥0∞) * (ENNReal.ofReal 2 * ENNReal.ofReal (omega n).toReal *
                  ENNReal.ofReal ((2 * r) ^ (n + 2))) := by
              rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
                ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (omega n).toReal),
                ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            rw [h1, ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal (omega_lt_top n).ne,
              ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * r)]
    refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
    have hcardP := hcard r hr hrR P hPK hPsep
    have hid : (R / r) ^ k * r ^ (n + 2) = R ^ k * r ^ (n + 2 - k) := by
      have h1 : r ^ (n + 2) = r ^ k * r ^ (n + 2 - k) := by
        rw [← pow_add, Nat.add_sub_of_le hk]
      rw [h1, div_pow, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero k hr.ne')]
    have hX : 0 ≤ 2 * (omega n).toReal * (2 * r) ^ (n + 2) := by positivity
    have hY : 0 ≤ R ^ k * r ^ (n + 2 - k) := by positivity
    calc (P.card : ℝ) * (2 * (omega n).toReal * (2 * r) ^ (n + 2))
        ≤ 2 ^ k * Cp * (R / r) ^ k * (2 * (omega n).toReal * (2 * r) ^ (n + 2)) :=
          mul_le_mul_of_nonneg_right hcardP hX
      _ = 2 ^ k * (2 * (omega n).toReal * 2 ^ (n + 2)) * Cp * ((R / r) ^ k * r ^ (n + 2)) := by
          rw [mul_pow]; ring
      _ = 2 ^ k * (2 * (omega n).toReal * 2 ^ (n + 2)) * Cp * (R ^ k * r ^ (n + 2 - k)) := by
          rw [hid]
      _ ≤ 2 ^ (n + 2) * (2 * (omega n).toReal * 2 ^ (n + 2)) * Cp * (R ^ k * r ^ (n + 2 - k)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h2k hA) hCp) hY
      _ ≤ 2 ^ (n + 2) * (1 + 2 * (omega n).toReal * 2 ^ (n + 2)) * Cp *
            (R ^ k * r ^ (n + 2 - k)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hCp) hY
      _ = 2 ^ (n + 2) * (1 + 2 * (omega n).toReal * 2 ^ (n + 2)) * Cp * R ^ k *
            r ^ (n + 2 - k) := by ring

end ParabolicRectifiability
