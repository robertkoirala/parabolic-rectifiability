import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements

/-! # Divergence below the square-summability threshold

For `0 < p < 2`, choose `s` strictly between `p / 2` and `1`. A small-power
bound for the logarithm shows that the amplitude powers dominate a positive
multiple of the shifted `p`-series with exponent `s`, which diverges.
-/

noncomputable section

open Filter Topology

namespace ParabolicRectifiability.Examples

private def e2_ampb_shiftedPower (s : ℝ) (n : ℕ) : ℝ :=
  (((n : ℝ) + 1) ^ s)⁻¹

private theorem e2_ampb_amplitude_rpow_eq {c₀ p : ℝ} (hc₀ : 0 < c₀) (n : ℕ) :
    exponentAmplitude c₀ n ^ p =
      c₀ ^ p / (((n : ℝ) + 1) ^ (p / 2) * (Real.log ((n : ℝ) + 2)) ^ p) := by
  have hlog : 0 < Real.log ((n : ℝ) + 2) :=
    Real.log_pos (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  have hsqrt : 0 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
  have hlog' : 0 ≤ Real.log ((n : ℝ) + 2) := le_of_lt hlog
  have hbase : 0 ≤ (n : ℝ) + 1 := by positivity
  change (c₀ / (Real.sqrt ((n : ℝ) + 1) * Real.log ((n : ℝ) + 2))) ^ p = _
  rw [Real.div_rpow (le_of_lt hc₀) (mul_nonneg hsqrt hlog') p,
    Real.mul_rpow hsqrt hlog', Real.sqrt_eq_rpow,
    ← Real.rpow_mul hbase (1 / 2) p]
  have hexp : (1 / 2 : ℝ) * p = p / 2 := by ring
  rw [hexp]

private theorem e2_ampb_logPow_eventually_le (p δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log ((n : ℝ) + 2) ^ p ≤ ((n : ℝ) + 2) ^ δ := by
  have hlittle : (fun x : ℝ => Real.log x ^ p) =o[atTop] fun x => x ^ δ :=
    isLittleO_log_rpow_rpow_atTop p hδ
  have hnorm : ∀ᶠ x : ℝ in atTop, ‖Real.log x ^ p‖ ≤ ‖x ^ δ‖ :=
    hlittle.eventuallyLE
  have htend : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually hnorm] with n hn
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) :=
    (Real.log_pos (by have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)).le
  have hpow : 0 ≤ ((n : ℝ) + 2) ^ δ :=
    le_of_lt (Real.rpow_pos_of_pos (by positivity) δ)
  simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hlog p),
    Real.norm_of_nonneg hpow] using hn

/-- Every positive power below two fails to be summable. -/
theorem e2_exponentAmplitude_not_summable_proof : E2ExponentNotSummableStatement := by
  intro c₀ hc₀ p hp hp2 hsum
  let s : ℝ := (p / 2 + 1) / 2
  let δ : ℝ := s - p / 2
  have hδ : 0 < δ := by dsimp [δ, s]; linarith
  have hspos : 0 < s := by dsimp [s]; linarith
  have hslt : s < 1 := by dsimp [s]; linarith
  have hexp : p / 2 + δ = s := by dsimp [δ]; ring
  have hC : 0 < c₀ ^ p / (2 : ℝ) ^ δ :=
    div_pos (Real.rpow_pos_of_pos hc₀ p) (Real.rpow_pos_of_pos (by norm_num) δ)
  have hlog_event := e2_ampb_logPow_eventually_le p δ hδ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hlog_event
  have hden_bound (m : ℕ) (hm : N ≤ m) :
      ((m : ℝ) + 1) ^ (p / 2) * (Real.log ((m : ℝ) + 2)) ^ p ≤
        (2 : ℝ) ^ δ * ((m : ℝ) + 1) ^ s := by
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hbase : 0 < (m : ℝ) + 1 := by linarith
    have hlogpos : 0 < Real.log ((m : ℝ) + 2) := Real.log_pos (by linarith)
    have hindex : (m : ℝ) + 2 ≤ 2 * ((m : ℝ) + 1) := by nlinarith
    have hindexpow := Real.rpow_le_rpow (by positivity) hindex (le_of_lt hδ)
    rw [Real.mul_rpow (by norm_num) (le_of_lt hbase)] at hindexpow
    have hlogle : Real.log ((m : ℝ) + 2) ^ p ≤
        (2 : ℝ) ^ δ * ((m : ℝ) + 1) ^ δ := by
      calc
        Real.log ((m : ℝ) + 2) ^ p ≤ ((m : ℝ) + 2) ^ δ := hN m hm
        _ ≤ (2 : ℝ) ^ δ * ((m : ℝ) + 1) ^ δ := hindexpow
    calc
      ((m : ℝ) + 1) ^ (p / 2) * (Real.log ((m : ℝ) + 2)) ^ p ≤
          ((m : ℝ) + 1) ^ (p / 2) * ((2 : ℝ) ^ δ * ((m : ℝ) + 1) ^ δ) :=
        mul_le_mul_of_nonneg_left hlogle (le_of_lt (Real.rpow_pos_of_pos hbase _))
      _ = (2 : ℝ) ^ δ * (((m : ℝ) + 1) ^ (p / 2) * ((m : ℝ) + 1) ^ δ) := by ring
      _ = (2 : ℝ) ^ δ * ((m : ℝ) + 1) ^ (p / 2 + δ) := by
        rw [← Real.rpow_add hbase]
      _ = (2 : ℝ) ^ δ * ((m : ℝ) + 1) ^ s := by rw [hexp]
  have hlarge (m : ℕ) (hm : N ≤ m) :
      (c₀ ^ p / (2 : ℝ) ^ δ) * e2_ampb_shiftedPower s m ≤ exponentAmplitude c₀ m ^ p := by
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hlogpos : 0 < Real.log ((m : ℝ) + 2) := Real.log_pos (by linarith)
    have hdenpos : 0 < ((m : ℝ) + 1) ^ (p / 2) * (Real.log ((m : ℝ) + 2)) ^ p := by
      positivity [hlogpos]
    have htargetpos : 0 < (2 : ℝ) ^ δ * ((m : ℝ) + 1) ^ s := by positivity
    have hrecip : ((2 : ℝ) ^ δ * ((m : ℝ) + 1) ^ s)⁻¹ ≤
        (((m : ℝ) + 1) ^ (p / 2) * (Real.log ((m : ℝ) + 2)) ^ p)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hdenpos (hden_bound m hm)
    have hcoeff : (c₀ ^ p / (2 : ℝ) ^ δ) * e2_ampb_shiftedPower s m =
        c₀ ^ p * ((2 : ℝ) ^ δ * ((m : ℝ) + 1) ^ s)⁻¹ := by
      dsimp [e2_ampb_shiftedPower]
      field_simp
    calc
      (c₀ ^ p / (2 : ℝ) ^ δ) * e2_ampb_shiftedPower s m =
          c₀ ^ p * ((2 : ℝ) ^ δ * ((m : ℝ) + 1) ^ s)⁻¹ := hcoeff
      _ ≤ c₀ ^ p * (((m : ℝ) + 1) ^ (p / 2) * (Real.log ((m : ℝ) + 2)) ^ p)⁻¹ :=
        mul_le_mul_of_nonneg_left hrecip (le_of_lt (Real.rpow_pos_of_pos hc₀ p))
      _ = exponentAmplitude c₀ m ^ p := by
        rw [e2_ampb_amplitude_rpow_eq hc₀ m]
        rfl
  have hamp_shift : Summable (fun n : ℕ => exponentAmplitude c₀ (n + N) ^ p) :=
    (summable_nat_add_iff (f := fun n : ℕ => exponentAmplitude c₀ n ^ p) N).mpr hsum
  have hpower_shift : Summable (fun n : ℕ => e2_ampb_shiftedPower s (n + N)) :=
    Summable.of_nonneg_of_le (fun n => by
      unfold e2_ampb_shiftedPower
      exact le_of_lt (inv_pos.mpr (Real.rpow_pos_of_pos (by positivity) s)))
      (fun n => by
        calc
          e2_ampb_shiftedPower s (n + N) =
              ((c₀ ^ p / (2 : ℝ) ^ δ)⁻¹) *
                ((c₀ ^ p / (2 : ℝ) ^ δ) * e2_ampb_shiftedPower s (n + N)) := by
                  rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
          _ ≤ ((c₀ ^ p / (2 : ℝ) ^ δ)⁻¹) * exponentAmplitude c₀ (n + N) ^ p :=
              mul_le_mul_of_nonneg_left (hlarge (n + N) (Nat.le_add_left N n))
                (inv_nonneg.mpr hC.le))
      (hamp_shift.mul_left ((c₀ ^ p / (2 : ℝ) ^ δ)⁻¹))
  have hpower : Summable (e2_ampb_shiftedPower s) := by
    apply (summable_nat_add_iff (f := e2_ampb_shiftedPower s) N).mp
    simpa [e2_ampb_shiftedPower] using hpower_shift
  have hpower' : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ s)⁻¹) := by
    exact hpower
  have hpseries : Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) := by
    apply (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ s)⁻¹) 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hpower'
  have hscrit : 1 < s := (Real.summable_nat_rpow_inv (p := s)).1 hpseries
  linarith

end ParabolicRectifiability.Examples

end
