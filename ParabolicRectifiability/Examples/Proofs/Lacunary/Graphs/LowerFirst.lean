import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements

/-! # Restriction-stable lower energy from disjoint plateau bands

The occupancy index is chosen before the exponent. The closed bands have strict gaps,
so countable additivity of the nonnegative integral applies without assuming that the
energy or amplitude series is finite.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

private theorem e2_lowerFirst_radius_pos {a : ℕ → ℝ} {N : ℕ → ℕ}
    (hd : IsLacunaryData a N) (j : ℕ) : 0 < e2_plateauRadius N j := by
  exact Real.sqrt_pos.2 (div_pos Real.pi_pos (by exact_mod_cast hd.frequency_pos j))

private theorem e2_lowerFirst_radius_decay (hdec : E2InvSqrtDecayStatement)
    {a : ℕ → ℝ} {N : ℕ → ℕ} (hd : IsLacunaryData a N) (j : ℕ) :
    e2_plateauRadius N (j + 1) ≤ e2_plateauRadius N j / 4 := by
  unfold e2_plateauRadius
  rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_div Real.pi_pos.le]
  calc
    Real.sqrt Real.pi / Real.sqrt (N (j + 1)) =
        Real.sqrt Real.pi * (Real.sqrt (N (j + 1)))⁻¹ := div_eq_mul_inv _ _
    _ ≤ Real.sqrt Real.pi * ((Real.sqrt (N j))⁻¹ / 4) :=
      mul_le_mul_of_nonneg_left (hdec a N hd j) (Real.sqrt_nonneg _)
    _ = Real.sqrt Real.pi / Real.sqrt (N j) / 4 := by ring

/-- The first lower-energy clause, with one coefficient function and a tail index
independent of every positive exponent. -/
theorem e2_lacunary_lowerFirst_proof :
    E2PlateauBetaStatement → E2BandStatement → E2OccupancyStatement →
      E2InvSqrtDecayStatement → E2LowerEnergyFirstStatement := by
  intro hbeta hband hocc hdec
  let c : ℝ → ℝ := fun q =>
    Real.log 2 * (2 : ℝ) ^ (-(2 + q)) * (1 / 2) *
      Real.pi ^ (-(q / 2)) * (12 / 25 : ℝ) ^ q
  have hc : ∀ q : ℝ, 0 < q → 0 < c q := by
    intro q hq
    dsimp [c]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨c, hc, ?_⟩
  intro ε a N hε hεupper hd E hE hEJ t ht hdt R hR
  obtain ⟨j₀, hj₀⟩ := hocc a N hd E t hdt R hR
  refine ⟨j₀, ?_⟩
  intro q hq
  let r : ℕ → ℝ := e2_plateauRadius N
  let bands : ℕ → Set ℝ := fun j => Icc (r (j + j₀)) (2 * r (j + j₀))
  let B : ℝ → ℝ≥0∞ := betaPow (lacunarySource ε a N E) 2 .mixed q
    (lacunaryGraphMap ε a N t)
  have hr : ∀ j, 0 < r j := e2_lowerFirst_radius_pos hd
  have hstep : ∀ j, r (j + 1) ≤ r j / 4 := e2_lowerFirst_radius_decay hdec hd
  have hmono : Antitone r := antitone_nat_of_succ_le fun j => by
    have h := hstep j
    have hp := hr j
    linarith
  have hgap : ∀ i j : ℕ, i < j → 2 * r (j + j₀) < r (i + j₀) := by
    intro i j hij
    have hle := hmono (show i + j₀ + 1 ≤ j + j₀ by omega)
    have h := hstep (i + j₀)
    have hp := hr (i + j₀)
    linarith
  have hdisj : Pairwise (fun i j => Disjoint (bands i) (bands j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    change r (i + j₀) ≤ x ∧ x ≤ 2 * r (i + j₀) at hxi
    change r (j + j₀) ≤ x ∧ x ≤ 2 * r (j + j₀) at hxj
    rcases lt_or_gt_of_ne hij with hij | hij
    · have := hgap i j hij
      linarith [hxi.1, hxj.2]
    · have := hgap j i hij
      linarith [hxj.1, hxi.2]
  have hsub : (⋃ j, bands j) ⊆ Ioo 0 R := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have htop := (hj₀ (j + j₀) (by omega)).2
    exact ⟨(hr _).trans_le hj.1, hj.2.trans_lt htop⟩
  have hcoef (j : ℕ) :
      ENNReal.ofReal (c q * ε ^ q) * ENNReal.ofReal (a (j + j₀) ^ q) =
        ENNReal.ofReal (Real.log 2) * ((2 : ℝ≥0∞) ^ ((2 : ℝ) + q))⁻¹ *
          ENNReal.ofReal (1 / 2 * Real.pi ^ (-(q / 2)) * (12 / 25 : ℝ) ^ q *
            ε ^ q * a (j + j₀) ^ q) := by
    have hpow : ((2 : ℝ≥0∞) ^ ((2 : ℝ) + q))⁻¹ =
        ENNReal.ofReal ((2 : ℝ) ^ (-(2 + q))) := by
      rw [← ENNReal.rpow_neg]
      simpa using (ENNReal.ofReal_rpow_of_pos (x := 2) (p := -(2 + q)) (by norm_num))
    have hnonneg : 0 ≤ c q * ε ^ q := mul_nonneg (hc q hq).le (Real.rpow_nonneg hε.le _)
    rw [hpow, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp [c]
    ring
  have hlocal (j : ℕ) :
      ENNReal.ofReal (c q * ε ^ q) * ENNReal.ofReal (a (j + j₀) ^ q) ≤
        ∫⁻ s in bands j, B s ∂scaleMeasure := by
    rw [hcoef j]
    exact (mul_le_mul_right (hbeta ε a N hε hεupper hd E hE (j + j₀) t
      (hj₀ (j + j₀) (by omega)).1 q hq) _).trans
      (hband 1 (lacunarySource ε a N E) 2 .mixed q hq.le
        (lacunaryGraphMap ε a N t) (r (j + j₀)) (hr _))
  calc
    ENNReal.ofReal (c q * ε ^ q) * ∑' j, ENNReal.ofReal (a (j + j₀) ^ q) =
        ∑' j, ENNReal.ofReal (c q * ε ^ q) * ENNReal.ofReal (a (j + j₀) ^ q) :=
      ENNReal.tsum_mul_left.symm
    _ ≤ ∑' j, ∫⁻ s in bands j, B s ∂scaleMeasure := ENNReal.tsum_le_tsum hlocal
    _ = ∫⁻ s in ⋃ j, bands j, B s ∂scaleMeasure :=
      (lintegral_iUnion (fun _ => measurableSet_Icc) hdisj B).symm
    _ ≤ energyT (lacunarySource ε a N E) 2 .mixed q R (lacunaryGraphMap ε a N t) :=
      lintegral_mono_set hsub

end ParabolicRectifiability.Examples
