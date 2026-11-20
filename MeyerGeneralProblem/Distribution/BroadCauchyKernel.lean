module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

/-!
# The broad higher-order Cauchy kernel

The same actual kernel is differentiated in the real test variable
and the complex pole variable. The bounds record the polynomial
weight and the precise power of the distance to the real axis.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter
open scoped Topology

/-- The uncut test kernel for the broad Cauchy pairing. -/
def broadCauchyKernel (m : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  ((x : ℂ) - z)⁻¹ ^ m

private theorem sub_pole_ne_zero (x : ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    (x : ℂ) - z ≠ 0 := by
  intro h
  exact hz (by simpa only [Complex.ofReal_im, Complex.zero_im, Complex.sub_im, zero_sub,
    neg_eq_zero] using congrArg Complex.im h)

private theorem hasDerivAt_inversePower {d : ℂ → ℂ} {d' x : ℂ}
    (hd : HasDerivAt d d' x) (hn : d x ≠ 0) (m : ℕ) :
    HasDerivAt (fun y => (d y)⁻¹ ^ m)
      (-(m : ℂ) * d' * (d x)⁻¹ ^ (m + 1)) x := by
  cases m with
  | zero =>
    simpa only [pow_zero, Nat.cast_zero, neg_zero, zero_mul] using (hasDerivAt_const x (1 : ℂ))
  | succ m =>
    have h := (hd.fun_inv hn).fun_pow (m + 1)
    have he : ((m + 1 : ℕ) : ℂ) * (d x)⁻¹ ^ m * (-d' / (d x) ^ 2) =
        -((m + 1 : ℕ) : ℂ) * d' * (d x)⁻¹ ^ (m + 1 + 1) := by
      rw [show m + 1 + 1 = m + 2 by omega, pow_add (d x)⁻¹ m 2, inv_pow, div_eq_mul_inv]
      ring
    simpa only [Nat.add_sub_cancel, he] using h

/-- Increasing the pole order gives the derivative in the real test variable. -/
theorem hasDerivAt_broadCauchyKernel_test_of_sub_ne_zero (m : ℕ) (z : ℂ) (x : ℝ)
    (hx : (x : ℂ) - z ≠ 0) :
    HasDerivAt (broadCauchyKernel m z) (-(m : ℂ) * broadCauchyKernel (m + 1) z x) x := by
  have hd : HasDerivAt (fun y : ℂ => y - z) (1 : ℂ) (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).sub_const z
  have h := (hasDerivAt_inversePower hd hx m).comp_ofReal
  change HasDerivAt (fun y : ℝ => ((y : ℂ) - z)⁻¹ ^ m)
    (-(m : ℂ) * ((x : ℂ) - z)⁻¹ ^ (m + 1)) x
  simpa only [mul_one] using h

/-- In the complex pole variable the derivative has the opposite sign. -/
theorem hasDerivAt_broadCauchyKernel_pole_of_sub_ne_zero (m : ℕ) (z : ℂ) (x : ℝ)
    (hx : (x : ℂ) - z ≠ 0) :
    HasDerivAt (fun w => broadCauchyKernel m w x) ((m : ℂ) * broadCauchyKernel (m + 1) z x) z := by
  have hd : HasDerivAt (fun w : ℂ => (x : ℂ) - w) (-1 : ℂ) z := by
    simpa only [id_eq] using (hasDerivAt_id z).const_sub (x : ℂ)
  simpa only [broadCauchyKernel, mul_neg, mul_one, neg_neg] using
    hasDerivAt_inversePower hd hx m

/-- All real derivatives retain the literal rising factorial. -/
theorem iteratedDeriv_broadCauchyKernel_test_of_sub_ne_zero (m j : ℕ) (z : ℂ) (x : ℝ)
    (hx : (x : ℂ) - z ≠ 0) :
    iteratedDeriv j (broadCauchyKernel m z) x =
      (-1 : ℂ) ^ j * (m.ascFactorial j : ℂ) * broadCauchyKernel (m + j) z x := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    have he : iteratedDeriv j (broadCauchyKernel m z) =ᶠ[𝓝 x]
        fun y => (-1 : ℂ) ^ j * (m.ascFactorial j : ℂ) * broadCauchyKernel (m + j) z y := by
      have hOpen : IsOpen {y : ℝ | (y : ℂ) - z ≠ 0} :=
        isOpen_ne_fun (Complex.continuous_ofReal.sub continuous_const) continuous_const
      filter_upwards [hOpen.mem_nhds hx] with y hy using ih y hy
    rw [iteratedDeriv_succ, he.deriv_eq, deriv_const_mul_field,
      (hasDerivAt_broadCauchyKernel_test_of_sub_ne_zero (m + j) z x hx).deriv]
    push_cast [Nat.ascFactorial_succ]
    rw [pow_succ, ← Nat.add_assoc]
    ring

theorem hasDerivAt_broadCauchyKernel_test (m : ℕ) (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    HasDerivAt (broadCauchyKernel m z) (-(m : ℂ) * broadCauchyKernel (m + 1) z x) x :=
  hasDerivAt_broadCauchyKernel_test_of_sub_ne_zero m z x (sub_pole_ne_zero x z hz)

theorem hasDerivAt_broadCauchyKernel_pole (m : ℕ) (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    HasDerivAt (fun w => broadCauchyKernel m w x) ((m : ℂ) * broadCauchyKernel (m + 1) z x) z :=
  hasDerivAt_broadCauchyKernel_pole_of_sub_ne_zero m z x (sub_pole_ne_zero x z hz)

theorem iteratedDeriv_broadCauchyKernel_test (m j : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    iteratedDeriv j (broadCauchyKernel m z) =
      fun x => (-1 : ℂ) ^ j * (m.ascFactorial j : ℂ) * broadCauchyKernel (m + j) z x :=
  funext fun x => iteratedDeriv_broadCauchyKernel_test_of_sub_ne_zero m j z x (sub_pole_ne_zero x z hz)

/-- The weight of every derivative is determined by the true distance
from the test point to the complex pole. -/
theorem norm_iteratedDeriv_broadCauchyKernel_test (m j : ℕ) (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    ‖iteratedDeriv j (broadCauchyKernel m z) x‖ =
      (m.ascFactorial j : ℝ) / ‖(x : ℂ) - z‖ ^ (m + j) := by
  simp only [iteratedDeriv_broadCauchyKernel_test m j z hz, broadCauchyKernel, norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_natCast, norm_inv, inv_pow,
    div_eq_mul_inv]

/-- The derivative decays at infinity with the full power of the pole.
The estimate is independent of the imaginary part once the test
variable is outside twice the modulus of the pole. -/
theorem norm_iteratedDeriv_broadCauchyKernel_test_tail_of_far (m j : ℕ)
    (z : ℂ) (x : ℝ) (hx : 0 < |x|) (hfar : 2 * ‖z‖ ≤ |x|) :
    ‖iteratedDeriv j (broadCauchyKernel m z) x‖ ≤
      (m.ascFactorial j : ℝ) * 2 ^ (m + j) / |x| ^ (m + j) := by
  have hnorm : |x| / 2 ≤ ‖(x : ℂ) - z‖ := by
    have h := norm_sub_norm_le (x : ℂ) z
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have hne := norm_pos_iff.mp ((half_pos hx).trans_le hnorm)
  have he : ‖iteratedDeriv j (broadCauchyKernel m z) x‖ =
      (m.ascFactorial j : ℝ) / ‖(x : ℂ) - z‖ ^ (m + j) := by
    simp only [iteratedDeriv_broadCauchyKernel_test_of_sub_ne_zero m j z x hne,
      broadCauchyKernel, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_natCast, norm_inv, inv_pow, div_eq_mul_inv]
  rw [he]
  calc
    _ ≤ (m.ascFactorial j : ℝ) / (|x| / 2) ^ (m + j) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (pow_le_pow_left₀ (by positivity) hnorm _)
    _ = _ := by
      rw [div_pow, div_eq_mul_inv, inv_div]
      ring

theorem norm_iteratedDeriv_broadCauchyKernel_test_tail (m j : ℕ)
    (z : ℂ) (_hz : z.im ≠ 0) (x : ℝ) (hx : 0 < |x|) (hfar : 2 * ‖z‖ ≤ |x|) :
    ‖iteratedDeriv j (broadCauchyKernel m z) x‖ ≤
      (m.ascFactorial j : ℝ) * 2 ^ (m + j) / |x| ^ (m + j) :=
  norm_iteratedDeriv_broadCauchyKernel_test_tail_of_far m j z x hx hfar

theorem contDiffAt_broadCauchyKernel_test_of_sub_ne_zero (m : ℕ) (z : ℂ) (x : ℝ)
    (hx : (x : ℂ) - z ≠ 0) (n : ℕ∞) :
    ContDiffAt ℝ n (broadCauchyKernel m z) x := by
  have hd : ContDiff ℝ n (fun y : ℝ => (y : ℂ) - z) :=
    Complex.ofRealCLM.contDiff.sub contDiff_const
  exact (hd.contDiffAt.inv hx).pow m

/-- All pole orders are smooth on the real test line when the pole
is off that line. -/
theorem contDiff_broadCauchyKernel_test (m : ℕ) (z : ℂ) (hz : z.im ≠ 0) (n : ℕ∞) :
    ContDiff ℝ n (broadCauchyKernel m z) := by
  have hd : ContDiff ℝ n (fun x : ℝ => (x : ℂ) - z) :=
    Complex.ofRealCLM.contDiff.sub contDiff_const
  exact (hd.inv (fun x => sub_pole_ne_zero x z hz)).pow m

/-- Global finite-order bound in the real test variable. Only the actual
distance of the pole from the real line appears in the singular factor. -/
theorem norm_weighted_iteratedDeriv_broadCauchyKernel_test_le (m k j : ℕ)
    (hk : k ≤ m + j) (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    |x| ^ k * ‖iteratedDeriv j (broadCauchyKernel m z) x‖ ≤
      (m.ascFactorial j : ℝ) * (1 + ‖z‖) ^ k * (max 1 (|z.im|)⁻¹) ^ (m + j) := by
  let d := ‖(x : ℂ) - z‖
  let a := 1 + ‖z‖
  let b := max 1 (|z.im|)⁻¹
  let n := m + j
  have hd0 : 0 < d := norm_pos_iff.mpr (sub_pole_ne_zero x z hz)
  have hb : 1 ≤ b := le_max_left _ _
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have him : |z.im| ≤ d := by
    have h := Complex.abs_im_le_norm ((x : ℂ) - z)
    simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] using h
  have hx : |x| ≤ d + ‖z‖ := by
    have h := norm_sub_norm_le (x : ℂ) z
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have hquot : |x| ^ k / d ^ n ≤ a ^ k * b ^ n := by
    by_cases hd : 1 ≤ d
    · have hxa : |x| ≤ a * d := by
        dsimp only [a]
        nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hd)]
      have hsmall : |x| ^ k / d ^ n ≤ a ^ k := by
        apply (div_le_iff₀ (pow_pos hd0 _)).mpr
        calc
          _ ≤ (a * d) ^ k := pow_le_pow_left₀ (abs_nonneg x) hxa _
          _ ≤ _ := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd hk) (pow_nonneg ha _)
      exact hsmall.trans (le_mul_of_one_le_right (pow_nonneg ha _) (one_le_pow₀ hb))
    · have hxa : |x| ≤ a := by dsimp [a]; linarith
      have hinv : d⁻¹ ≤ b := (inv_anti₀ (abs_pos.mpr hz) him).trans (le_max_right _ _)
      rw [div_eq_mul_inv, ← inv_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hxa _) (pow_le_pow_left₀
        (inv_nonneg.mpr hd0.le) hinv _) (by positivity) (pow_nonneg ha _)
  rw [norm_iteratedDeriv_broadCauchyKernel_test m j z hz]
  change |x| ^ k * ((m.ascFactorial j : ℝ) / d ^ n) ≤ (m.ascFactorial j : ℝ) * a ^ k * b ^ n
  calc
    _ = (m.ascFactorial j : ℝ) * (|x| ^ k / d ^ n) := by ring
    _ ≤ (m.ascFactorial j : ℝ) * (a ^ k * b ^ n) :=
      mul_le_mul_of_nonneg_left hquot (Nat.cast_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

end

end MeyerGeneralProblem
