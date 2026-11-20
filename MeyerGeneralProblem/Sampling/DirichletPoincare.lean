module

public import MeyerGeneralProblem.Sampling.PeriodicPoincare

@[expose] public section

/-!
# Sharp complex Dirichlet Poincare--Wirtinger inequality

The actual odd reflection of a function vanishing at zero is C1. Its derivative
is the original derivative evaluated at the absolute value, including zero.
This supplies the sharp Dirichlet constant without a spectral assumption.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff

/-- Actual odd reflection of the positive half-line, with its original value at zero. -/
def dirichletOddExtension (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  if x < 0 then -f (-x) else f x

/-- The reflected derivative has no sign change, including the joining point. -/
theorem hasDerivAt_dirichletOddExtension (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hzero : f 0 = 0) (x : ℝ) :
    HasDerivAt (dirichletOddExtension f) (deriv f |x|) x := by
  have hfd (t : ℝ) : HasDerivAt f (deriv f t) t :=
    (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hnegative (t : ℝ) : HasDerivAt (fun y : ℝ => -f (-y)) (deriv f (-t)) t := by
    convert ((hfd (-t)).scomp t (hasDerivAt_neg t)).neg using 1 <;>
      norm_num [Function.comp_def] <;> rfl
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [abs_of_neg hx]
    apply (hnegative x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    change y < (0 : ℝ) at hy
    simp [dirichletOddExtension,hy]
  · subst x
    simp only [abs_zero]
    have hl : HasDerivWithinAt (dirichletOddExtension f) (deriv f 0) (Iic 0) 0 := by
      apply (show HasDerivAt (fun y : ℝ => -f (-y)) (deriv f 0) 0 by
        simpa using hnegative 0).hasDerivWithinAt.congr
      · intro y hy
        change y ≤ (0 : ℝ) at hy
        rcases lt_or_eq_of_le hy with hy | hy
        · simp [dirichletOddExtension,hy]
        · subst y; simp [dirichletOddExtension,hzero]
      · simp [dirichletOddExtension,hzero]
    have hr : HasDerivWithinAt (dirichletOddExtension f) (deriv f 0) (Ici 0) 0 := by
      apply (hfd 0).hasDerivWithinAt.congr
      · intro y hy
        change (0 : ℝ) ≤ y at hy
        simp [dirichletOddExtension,not_lt.mpr hy]
      · simp [dirichletOddExtension]
    have hu := hl.union hr
    rw [Iic_union_Ici] at hu
    exact hu.hasDerivAt (by simp)
  · rw [abs_of_pos hx]
    apply (hfd x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    change (0 : ℝ) < y at hy
    simp [dirichletOddExtension,not_lt.mpr hy.le]

/-- Exact derivative of the actual odd reflection. -/
theorem deriv_dirichletOddExtension (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hzero : f 0 = 0) :
    deriv (dirichletOddExtension f) = fun x => deriv f |x| := by
  funext x
  exact (hasDerivAt_dirichletOddExtension f hf hzero x).deriv

/-- Odd reflection is genuinely C1 across zero under the endpoint condition. -/
theorem contDiff_dirichletOddExtension (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hzero : f 0 = 0) : ContDiff ℝ 1 (dirichletOddExtension f) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_dirichletOddExtension f hf hzero x).differentiableAt, ?_⟩
  rw [deriv_dirichletOddExtension f hf hzero]
  exact (contDiff_one_iff_deriv.mp hf).2.comp continuous_abs

/-- The reflected function is odd, including its zero value. -/
theorem dirichletOddExtension_neg (f : ℝ → ℂ) (hzero : f 0 = 0) (x : ℝ) :
    dirichletOddExtension f (-x) = -dirichletOddExtension f x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [dirichletOddExtension,hx,show ¬ -x < 0 by linarith]
  · subst x; simp [dirichletOddExtension,hzero]
  · simp [dirichletOddExtension,show -x < 0 by linarith,not_lt.mpr hx.le]

/-- The actual reflected value has the original absolute-coordinate norm. -/
theorem norm_dirichletOddExtension (f : ℝ → ℂ) (x : ℝ) :
    ‖dirichletOddExtension f x‖ = ‖f |x|‖ := by
  by_cases hx : x < 0
  · simp [dirichletOddExtension,hx,abs_of_neg hx]
  · simp [dirichletOddExtension,hx,abs_of_nonneg (le_of_not_gt hx)]

/-- Integrating an actual absolute-coordinate function over the reflected
interval doubles its positive-half integral. -/
theorem integral_comp_abs_symmetric (g : ℝ → ℝ) (hg : Continuous g)
    {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, g |x|) = 2*(∫ x in 0..L, g x) := by
  have hpos : (∫ x in 0..L, g |x|) = ∫ x in 0..L, g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hL] at hx
    change g |x| = g x
    rw [abs_of_nonneg hx.1]
  have hneg := intervalIntegral.integral_comp_neg (fun x => g |x|) (a := 0) (b := L)
  simp only [neg_zero, abs_neg, hpos] at hneg
  have hsum : (∫ x in -L..0, g |x|) + (∫ x in 0..L, g |x|) =
      ∫ x in -L..L, g |x| := intervalIntegral.integral_add_adjacent_intervals
        ((hg.comp continuous_abs).intervalIntegrable (-L) 0)
        ((hg.comp continuous_abs).intervalIntegrable 0 L)
  rw [← hsum, ← hneg, hpos]
  ring

/-- The mean of the actual odd reflection vanishes on every symmetric interval. -/
theorem integral_dirichletOddExtension_eq_zero (f : ℝ → ℂ) (hzero : f 0 = 0)
    (L : ℝ) : (∫ x in -L..L, dirichletOddExtension f x) = 0 := by
  have heq := intervalIntegral.integral_comp_neg (dirichletOddExtension f) (a := -L) (b := L)
  simp only [neg_neg, dirichletOddExtension_neg f hzero, intervalIntegral.integral_neg] at heq
  have hr := congrArg Complex.re heq
  have hi := congrArg Complex.im heq
  apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im]
  · simp only [Complex.neg_re] at hr
    linarith
  · simp only [Complex.neg_im] at hi
    linarith

/-- Sharp complex Dirichlet Poincare--Wirtinger on a positive interval
starting at zero, obtained from the genuine C1 odd reflection. -/
theorem complex_dirichlet_poincare_wirtinger_zero {L : ℝ} (hL : 0 < L)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hzero : f 0 = 0) (hendpoint : f L = 0) :
    Real.pi^2 * (∫ x in 0..L, ‖f x‖^2) ≤
      L^2 * (∫ x in 0..L, ‖deriv f x‖^2) := by
  have he := complex_periodic_poincare_wirtinger (a := -L) (b := L) (by linarith)
    (dirichletOddExtension f) (contDiff_dirichletOddExtension f hf hzero)
    (by simp [dirichletOddExtension, show -L < 0 by linarith, not_lt.mpr hL.le, hendpoint])
    (integral_dirichletOddExtension_eq_zero f hzero L)
  simp only [norm_dirichletOddExtension, deriv_dirichletOddExtension f hf hzero] at he
  rw [integral_comp_abs_symmetric (fun x => ‖f x‖^2) (hf.continuous.norm.pow 2) hL.le,
    integral_comp_abs_symmetric (fun x => ‖deriv f x‖^2)
      ((contDiff_one_iff_deriv.mp hf).2.norm.pow 2) hL.le] at he
  nlinarith

/-- The sharp complex interval Poincare--Wirtinger inequality with both
Dirichlet endpoint conditions and the exact pi-squared constant. -/
theorem complex_dirichlet_poincare_wirtinger {a b : ℝ} (hab : a < b)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hfa : f a = 0) (hfb : f b = 0) :
    Real.pi^2 * (∫ x in a..b, ‖f x‖^2) ≤
      (b-a)^2 * (∫ x in a..b, ‖deriv f x‖^2) := by
  let g : ℝ → ℂ := fun x => f (a+x)
  have hg : ContDiff ℝ 1 g := hf.comp (contDiff_const.add contDiff_id)
  have hderiv : deriv g = fun x => deriv f (a+x) := by
    funext x
    have hd : HasDerivAt f (deriv f (a+x)) (a+x) :=
      (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt
    simpa only [g, Function.comp_def, one_smul] using
      (hd.scomp x ((hasDerivAt_id x).const_add a)).deriv
  have he := complex_dirichlet_poincare_wirtinger_zero (sub_pos.mpr hab) g hg
    (by simpa [g] using hfa) (by simpa [g] using hfb)
  rw [hderiv] at he
  dsimp only [g] at he
  rw [intervalIntegral.integral_comp_add_left (fun x => ‖f x‖^2) a,
    intervalIntegral.integral_comp_add_left (fun x => ‖deriv f x‖^2) a] at he
  simpa only [add_zero, add_sub_cancel] using he

/-- The same sharp inequality on the standard closed-set integral, matching
the pointwise interval geometry used by the endpoint bootstrap. -/
theorem complex_dirichlet_poincare_wirtinger_Icc {a b : ℝ} (hab : a < b)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hfa : f a = 0) (hfb : f b = 0) :
    Real.pi^2 * (∫ x in Icc a b, ‖f x‖^2) ≤
      (b-a)^2 * (∫ x in Icc a b, ‖deriv f x‖^2) := by
  have h := complex_dirichlet_poincare_wirtinger hab f hf hfa hfb
  simpa only [intervalIntegral.integral_of_le hab.le, integral_Icc_eq_integral_Ioc] using h

/-- Weighted local tail contraction with the larger absolute endpoint and
the exact Fourier normalization. Finite exceptional intervals are not removed. -/
theorem complex_dirichlet_weighted_poincare {a b ρ : ℝ} (hab : a < b)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hfa : f a = 0) (hfb : f b = 0)
    (hgap : max |a| |b| * (b-a) ≤ ρ) :
    Real.pi^2 * (∫ x in a..b, x^2 * ‖f x‖^2) ≤
      ρ^2 * (∫ x in a..b, ‖deriv f x‖^2) := by
  let M := max |a| |b|
  have hM : 0 ≤ M := (abs_nonneg a).trans (le_max_left _ _)
  have hT : 0 < b-a := sub_pos.mpr hab
  have hρ : 0 ≤ ρ := (mul_nonneg hM hT.le).trans hgap
  have hi : (∫ x in a..b, x^2*‖f x‖^2) ≤ M^2*(∫ x in a..b, ‖f x‖^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab.le
      (((continuous_id.pow 2).mul (hf.continuous.norm.pow 2)).intervalIntegrable a b)
      ((continuous_const.mul (hf.continuous.norm.pow 2)).intervalIntegrable a b)
    intro x hx
    have hxM : |x| ≤ M := abs_le_max_abs_abs hx.1 hx.2
    have hx2 : x^2 ≤ M^2 := by nlinarith [sq_abs x,abs_nonneg x]
    exact mul_le_mul_of_nonneg_right hx2 (sq_nonneg _)
  have hp := complex_dirichlet_poincare_wirtinger hab f hf hfa hfb
  have hnonneg : 0 ≤ ∫ x in a..b, ‖deriv f x‖^2 :=
    intervalIntegral.integral_nonneg hab.le (by intro x _; positivity)
  have hs : M^2*(b-a)^2 ≤ ρ^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (mul_nonneg hM hT.le) hρ).mpr hgap
  calc
    _ ≤ M^2*(Real.pi^2*(∫ x in a..b, ‖f x‖^2)) := by
      simpa only [mul_assoc,mul_left_comm,mul_comm] using
        mul_le_mul_of_nonneg_left hi (sq_nonneg Real.pi)
    _ ≤ M^2*((b-a)^2*(∫ x in a..b, ‖deriv f x‖^2)) :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg M)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hs hnonneg

end

end MeyerGeneralProblem
