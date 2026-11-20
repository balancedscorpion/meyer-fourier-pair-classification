module

public import MeyerGeneralProblem.Distribution.FiniteFourierMotif
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Exact isolation of coefficients in a finite exponential sum by
long averages along the original real frequency line. -/

namespace MeyerGeneralProblem

private theorem norm_integral_modulationCharacter_le (a : ℝ) (ha : a ≠ 0) (T : ℝ) :
    ‖∫ x : ℝ in 0..T, combModulationCharacter a x‖ ≤
      2 / ‖(2 * Real.pi * Complex.I * (a : ℂ))‖ := by
  let k : ℂ := 2 * Real.pi * Complex.I * (a : ℂ)
  have hk : k ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero) ha'
  simp only [combModulationCharacter_eq_exp]
  rw [integral_exp_mul_complex hk, norm_div]
  refine div_le_div_of_nonneg_right ((norm_sub_le _ _).trans_eq ?_) (norm_nonneg _)
  simp only [k, ← combModulationCharacter_eq_exp, norm_combModulationCharacter]
  norm_num

/-- Each coefficient of a finite exponential sum with distinct original
frequencies is bounded by any global uniform bound for the entire sum. -/
theorem norm_coefficient_le_of_finiteExponentialSum_bound {ι : Type*}
    (S : Finset ι) (a : ι → ℝ) (c : ι → ℂ) (ha : Set.InjOn a S)
    (B : ℝ) (hB : ∀ x : ℝ, ‖∑ j ∈ S, c j * combModulationCharacter (a j) x‖ ≤ B)
    (i : ι) (hi : i ∈ S) : ‖c i‖ ≤ B := by
  classical
  let F (j : ι) (x : ℝ) := c j * combModulationCharacter (a j - a i) x
  let D (j : ι) := ‖c j‖ * (2 / ‖(2 * Real.pi * Complex.I * ((a j - a i : ℝ) : ℂ))‖)
  let C := ∑ j ∈ S.erase i, D j
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => by dsimp [D]; positivity
  have hF (x : ℝ) : ‖∑ j ∈ S, F j x‖ ≤ B := by
    have he : (∑ j ∈ S, F j x) = (∑ j ∈ S, c j * combModulationCharacter (a j) x) *
        combModulationCharacter (-a i) x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      change c j * combModulationCharacter (a j - a i) x =
        (c j * combModulationCharacter (a j) x) * combModulationCharacter (-a i) x
      rw [mul_assoc, ← combModulationCharacter_add_left, sub_eq_add_neg]
    rw [he, norm_mul, norm_combModulationCharacter, mul_one]
    exact hB x
  have hbound (T : ℝ) (hT : 0 < T) : ‖c i‖ * T ≤ B * T + C := by
    let J (j : ι) := ∫ x : ℝ in 0..T, F j x
    have hsum : (∫ x : ℝ in 0..T, ∑ j ∈ S, F j x) = ∑ j ∈ S, J j := by
      apply intervalIntegral.integral_finsetSum
      intro j _
      apply Continuous.intervalIntegrable
      exact continuous_const.mul (contDiff_combModulationCharacter _ 0).continuous
    have hj (j : ι) (hj : j ∈ S.erase i) : ‖J j‖ ≤ D j := by
      have hj' := Finset.mem_erase.mp hj
      have hne : a j - a i ≠ 0 := sub_ne_zero.mpr (fun h => hj'.1 (ha hj'.2 hi h))
      change ‖∫ x : ℝ in 0..T, c j * combModulationCharacter (a j - a i) x‖ ≤ D j
      rw [intervalIntegral.integral_const_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_integral_modulationCharacter_le _ hne T) (norm_nonneg _)
    have hJ : J i = c i * (T : ℂ) := by
      change (∫ x : ℝ in 0..T, F i x) = _
      simp [F, combModulationCharacter_zero_left, mul_comm]
    have hi' : J i = (∑ j ∈ S, J j) - ∑ j ∈ S.erase i, J j := by
      rw [← Finset.sum_erase_add S J hi, add_sub_cancel_left]
    have htotal : ‖∑ j ∈ S, J j‖ ≤ B * T := by
      rw [← hsum]
      simpa only [sub_zero, abs_of_pos hT, mul_comm] using
        (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := B)
          (fun x _ => hF x))
    calc
      ‖c i‖ * T = ‖J i‖ := by rw [hJ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
      _ ≤ ‖∑ j ∈ S, J j‖ + ‖∑ j ∈ S.erase i, J j‖ := by rw [hi']; exact norm_sub_le _ _
      _ ≤ B * T + C := add_le_add htotal ((norm_sum_le _ _).trans (Finset.sum_le_sum hj))
  by_contra! h
  let T := C / (‖c i‖ - B) + 1
  have hT : 0 < T := by positivity
  have hprod : (‖c i‖ - B) * (C / (‖c i‖ - B)) = C := by
    rw [mul_div_cancel₀ _ (sub_ne_zero.mpr h.ne')]
  have hx := hbound T hT
  dsimp [T] at hx
  nlinarith [sub_pos.mpr h]

end MeyerGeneralProblem
