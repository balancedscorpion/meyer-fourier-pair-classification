module

public import MeyerGeneralProblem.Distribution.Strassmann
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

@[expose] public section

/-!
# A power series for normalized p-adic unit powers

The term of order `k` in the binomial interpolation is a polynomial of
degree at most `k`. Its coefficient norms decay geometrically. Joint
summability justifies turning the polynomial series into a power series
on the entire closed unit ball.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set Polynomial
open scoped Topology BigOperators

section PolynomialSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem polynomial_eval_eq_tsum_coeff_mul_pow (P : Polynomial K) (x : K) :
    P.eval x = ∑' j : ℕ, P.coeff j * x ^ j := by
  rw [tsum_eq_sum (s := Finset.range (P.natDegree + 1))]
  · exact P.eval_eq_sum_range x
  · intro j hj
    rw [coeff_eq_zero_of_natDegree_lt (by
      have h : P.natDegree + 1 ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
      omega), zero_mul]

private theorem exists_powerSeries_of_polynomialSeries
    (P : ℕ → Polynomial K) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hzero : ∀ k j, k < j → (P k).coeff j = 0)
    (hcoeff : ∀ k j, ‖(P k).coeff j‖ ≤ ρ ^ k) :
    ∃ a : ℕ → K, Tendsto a atTop (𝓝 0) ∧ ∀ x : K, ‖x‖ ≤ 1 →
      closedUnitBallPowerSeriesEval a x = ∑' k : ℕ, (P k).eval x := by
  let a (j : ℕ) := ∑' k : ℕ, (P k).coeff j
  have hρt := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have hcolumn (j : ℕ) : Summable (fun k : ℕ => (P k).coeff j) := by
    apply ultrametric_summable_of_tendsto_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hcoeff k j) hρt
  have habound (j : ℕ) : ‖a j‖ ≤ ρ ^ j := by
    apply ultrametric_norm_tsum_le_of_forall_le _ (hcolumn j) _ (pow_nonneg hρ0 _)
    intro k
    by_cases h : k < j
    · rw [hzero k j h, norm_zero]
      exact pow_nonneg hρ0 _
    · exact (hcoeff k j).trans (pow_le_pow_of_le_one hρ0 hρ1.le (le_of_not_gt h))
  refine ⟨a, ?_, ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) habound hρt
  · intro x hx
    let f (k j : ℕ) := (P k).coeff j * x ^ j
    have hfx (k j : ℕ) : ‖f k j‖ ≤ ρ ^ k := by
      have hpow : ‖x ^ j‖ ≤ 1 := by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg x) hx
      exact (norm_mul _ _).le.trans
        ((mul_le_of_le_one_right (norm_nonneg _) hpow).trans (hcoeff k j))
    have hfj : Summable (Function.uncurry f) := by
      apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hρt ε hε
      have hnear (k : ℕ) (hk : N ≤ k) : ρ ^ k < ε := by
        simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hρ0 _)] using hN k hk
      have hfinite : (Set.Iio N ×ˢ Set.Iio N).Finite :=
        (Set.finite_lt_nat N).prod (Set.finite_lt_nat N)
      have houtside : ∀ᶠ z : ℕ × ℕ in cofinite, z ∉ Set.Iio N ×ˢ Set.Iio N :=
        hfinite.compl_mem_cofinite
      refine houtside.mono ?_
      rintro ⟨k, j⟩ hk
      change ¬(k < N ∧ j < N) at hk
      change dist (f k j) 0 < ε
      rw [dist_zero_right]
      by_cases hj : k < j
      · simp only [f, hzero k j hj, zero_mul, norm_zero, hε]
      · exact (hfx k j).trans_lt (hnear k (by omega))
    have hrow (k : ℕ) : Summable (f k) := by
      apply summable_of_ne_finset_zero (s := Finset.range (k + 1))
      intro j hj
      have hj' : k < j := by simpa [Finset.mem_range, not_lt] using hj
      simp only [f, hzero k j hj', zero_mul]
    have hcol (j : ℕ) : Summable (fun k => f k j) := (hcolumn j).mul_right _
    calc
      closedUnitBallPowerSeriesEval a x = ∑' j : ℕ, ∑' k : ℕ, f k j := by
        unfold closedUnitBallPowerSeriesEval
        apply tsum_congr
        intro j
        exact tsum_mul_right.symm
      _ = ∑' k : ℕ, ∑' j : ℕ, f k j := hfj.tsum_comm' hrow hcol
      _ = ∑' k : ℕ, (P k).eval x := by
        apply tsum_congr
        intro k
        exact (polynomial_eval_eq_tsum_coeff_mul_pow (P k) x).symm

end PolynomialSeries

section Padic

variable (p : ℕ) [hp : Fact p.Prime]

private theorem padic_norm_inv_factorial_le (k : ℕ) :
    ‖(k.factorial : ℚ_[p])⁻¹‖ ≤ (p : ℝ) ^ k := by
  have hn : (k.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation hn, Padic.valuation_natCast,
    ← zpow_neg, neg_neg, zpow_natCast]
  exact pow_le_pow_right₀ hp' (padicValNat_factorial_le p k)

private theorem padic_norm_coeff_descPochhammer_le_one (k j : ℕ) :
    ‖(descPochhammer ℚ_[p] k).coeff j‖ ≤ 1 := by
  have he := congrArg (fun P : Polynomial ℚ_[p] => P.coeff j)
    (descPochhammer_map (Int.castRingHom ℚ_[p]) k)
  rw [coeff_map, Int.coe_castRingHom] at he
  rw [← he]
  exact Padic.norm_int_le_one _

/-- A p-adic base sufficiently close to one has a convergent power-series
interpolation on the closed unit ball, with its exact original natural powers. -/
theorem exists_padic_powerSeries_of_small_increment
    (d : ℚ_[p]) (hd : ‖d‖ ≤ ((p : ℝ)⁻¹) ^ 2) :
    ∃ a : ℕ → ℚ_[p], Tendsto a atTop (𝓝 0) ∧
      ∀ n : ℕ, closedUnitBallPowerSeriesEval a (n : ℚ_[p]) = (1 + d) ^ n := by
  let P (k : ℕ) := C (d ^ k * (k.factorial : ℚ_[p])⁻¹) * descPochhammer ℚ_[p] k
  let ρ := (p : ℝ)⁻¹
  have hpos : 0 < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hρ0 : 0 ≤ ρ := inv_nonneg.mpr hpos.le
  have hρ1 : ρ < 1 := (inv_lt_one₀ hpos).mpr (by exact_mod_cast hp.out.one_lt)
  have hzero (k j : ℕ) (hj : k < j) : (P k).coeff j = 0 := by
    unfold P
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by rwa [descPochhammer_natDegree]), mul_zero]
  have hbound (k j : ℕ) : ‖(P k).coeff j‖ ≤ ρ ^ k := by
    unfold P
    rw [coeff_C_mul, norm_mul, norm_mul, norm_pow]
    calc
      _ ≤ (‖d‖ ^ k) * ‖(k.factorial : ℚ_[p])⁻¹‖ :=
        mul_le_of_le_one_right (by positivity) (padic_norm_coeff_descPochhammer_le_one p k j)
      _ ≤ (ρ ^ 2) ^ k * (p : ℝ) ^ k :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hd _) (padic_norm_inv_factorial_le p k)
          (norm_nonneg _) (pow_nonneg (pow_nonneg hρ0 _) _)
      _ = ρ ^ k := by
        rw [← mul_pow]
        congr 1
        dsimp [ρ]
        field_simp
  obtain ⟨a, ha, he⟩ := exists_powerSeries_of_polynomialSeries P ρ hρ0 hρ1 hzero hbound
  refine ⟨a, ha, fun n => ?_⟩
  rw [he _ (by simpa only [Int.cast_natCast] using Padic.norm_int_le_one (p := p) (n : ℤ))]
  have hEval (k : ℕ) : (P k).eval (n : ℚ_[p]) = d ^ k * (n.choose k : ℚ_[p]) := by
    unfold P
    rw [eval_mul, eval_C, Nat.cast_choose_eq_descPochhammer_div, div_eq_mul_inv]
    ring
  simp_rw [hEval]
  rw [tsum_eq_sum (s := Finset.range (n + 1))]
  · rw [show (1 : ℚ_[p]) + d = d + 1 from add_comm _ _, add_pow]
    simp
  · intro k hk
    have hk' : n < k := by simpa [Finset.mem_range, not_lt] using hk
    simp [Nat.choose_eq_zero_of_lt hk']

end Padic

end
end MeyerGeneralProblem
