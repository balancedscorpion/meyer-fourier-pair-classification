module

public import MeyerGeneralProblem.Distribution.FourierGapRealPrimitive
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Truncated powers as the weak primitives of a point mass

The normalized truncated power of degree n has the point mass at the
knot as its weak derivative of order n plus one. Its classical
derivatives through order n minus one are continuous.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter LineDeriv MeasureTheory Set
open scoped ContDiff Topology

/-- Normalized positive-side power at a knot. Degree zero is the step
function, with value zero at the knot. -/
def splineAtomPrimitive (a : ℝ) (n : ℕ) : ℝ → ℝ :=
  (Ioi a).indicator (fun x => (x - a) ^ n / (n.factorial : ℝ))

private theorem hasDerivAt_normalizedPower (a x : ℝ) (n : ℕ) :
    HasDerivAt (fun t : ℝ => (t - a) ^ (n + 1) / ((n + 1).factorial : ℝ))
      ((x - a) ^ n / (n.factorial : ℝ)) x := by
  have hShift : HasDerivAt (fun t : ℝ => t - a) 1 x := (hasDerivAt_id x).sub_const a
  have hp : HasDerivAt (fun t : ℝ => (t - a) ^ (n + 1))
      (((n + 1 : ℕ) : ℝ) * (x - a) ^ n) x := by
    simpa only [Function.comp_def, Nat.succ_sub_one, mul_one] using
      (hasDerivAt_pow (n + 1) (x - a)).comp x hShift
  have he : ((n + 1 : ℕ) : ℝ) * (x - a) ^ n / ((n + 1).factorial : ℝ) =
      (x - a) ^ n / (n.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hF : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
    field_simp [hn, hF]
  rw [← he]
  exact hp.div_const _

private theorem isZero_splineAtomPrimitive_on_left (a : ℝ) (n : ℕ) :
    EqOn (splineAtomPrimitive a n) 0 (Iic a) := by
  intro x hx
  exact indicator_of_notMem (not_lt_of_ge hx) _

private theorem eq_normalizedPower_splineAtomPrimitive_on_right
    (a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    EqOn (splineAtomPrimitive a n) (fun t : ℝ => (t - a) ^ n / (n.factorial : ℝ)) (Ici a) := by
  intro t ht
  change a ≤ t at ht
  rcases lt_or_eq_of_le ht with hx | rfl
  · exact indicator_of_mem hx _
  · simp [splineAtomPrimitive, hn]

/-- Differentiating a positive-degree atom primitive away from its knot
reduces its normalized degree by one. -/
theorem hasDerivAt_splineAtomPrimitive_succ_of_ne
    (a x : ℝ) (n : ℕ) (hx : x ≠ a) :
    HasDerivAt (splineAtomPrimitive a (n + 1)) (splineAtomPrimitive a n x) x := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [show splineAtomPrimitive a n x = 0 from isZero_splineAtomPrimitive_on_left a n h.le]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with y hy
    exact isZero_splineAtomPrimitive_on_left a (n + 1) (show y < a from hy).le
  · rw [show splineAtomPrimitive a n x = (x - a) ^ n / (n.factorial : ℝ) from indicator_of_mem h _]
    apply (hasDerivAt_normalizedPower a x n).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with y hy
    exact indicator_of_mem hy _

/-- At strictly positive derivative degree the two branches also
differentiate through the knot. -/
theorem hasDerivAt_splineAtomPrimitive_succ
    (a x : ℝ) (n : ℕ) (hn : n ≠ 0) :
    HasDerivAt (splineAtomPrimitive a (n + 1)) (splineAtomPrimitive a n x) x := by
  by_cases hx : x = a
  · subst x
    rw [show splineAtomPrimitive a n a = 0 from isZero_splineAtomPrimitive_on_left a n self_mem_Iic]
    have hl : HasDerivWithinAt (splineAtomPrimitive a (n + 1)) 0 (Iic a) a := by
      apply (hasDerivAt_const a (0 : ℝ)).hasDerivWithinAt.congr
      · exact isZero_splineAtomPrimitive_on_left a (n + 1)
      · exact isZero_splineAtomPrimitive_on_left a (n + 1) self_mem_Iic
    have hr : HasDerivWithinAt (splineAtomPrimitive a (n + 1)) 0 (Ici a) a := by
      have h := (hasDerivAt_normalizedPower a a n).hasDerivWithinAt (s := Ici a)
      rw [sub_self, zero_pow hn, zero_div] at h
      apply h.congr
      · exact eq_normalizedPower_splineAtomPrimitive_on_right a (Nat.succ_ne_zero _)
      · exact eq_normalizedPower_splineAtomPrimitive_on_right a (Nat.succ_ne_zero _) self_mem_Ici
    have hUnion := hl.union hr
    rw [Iic_union_Ici] at hUnion
    exact hUnion.hasDerivAt (by simp)
  · exact hasDerivAt_splineAtomPrimitive_succ_of_ne a x n hx

/-- The normalized atom power is continuous through every order below
its degree. -/
theorem contDiff_splineAtomPrimitive (a : ℝ) (n k : ℕ) (hk : k < n) :
    ContDiff ℝ k (splineAtomPrimitive a n) := by
  induction k generalizing n with
  | zero =>
    have hn : n ≠ 0 := Nat.ne_of_gt hk
    apply contDiff_zero.mpr
    have he : splineAtomPrimitive a n = fun x : ℝ => (max (x - a) 0) ^ n / (n.factorial : ℝ) := by
      funext x
      by_cases hx : a < x
      · simp [splineAtomPrimitive, hx, max_eq_left (sub_nonneg.mpr hx.le)]
      · simp [splineAtomPrimitive, hx, max_eq_right (sub_nonpos.mpr (le_of_not_gt hx)), hn]
    rw [he]
    fun_prop
  | succ k ih =>
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hk))
    have hn' : k < n' := Nat.lt_of_succ_lt_succ hk
    have hD (x : ℝ) := hasDerivAt_splineAtomPrimitive_succ a x n' (Nat.ne_of_gt (Nat.zero_lt_of_lt hn'))
    rw [Nat.cast_succ]
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨fun x => (hD x).differentiableAt, by simp, ?_⟩
    rw [show deriv (splineAtomPrimitive a (n' + 1)) = splineAtomPrimitive a n' from funext (fun x => (hD x).deriv)]
    exact ih n' hn'

/-- The iterated Schwartz derivative of a compactly supported test has compact support. -/
theorem hasCompactSupport_schwartz_iterate_lineDeriv_one
    (m : ℕ) (φ : SchwartzMap ℝ ℂ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (((lineDerivOp (1 : ℝ))^[m]) φ : SchwartzMap ℝ ℂ) := by
  induction m generalizing φ with
  | zero => exact hφ
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    have he : (lineDerivOp (1 : ℝ) φ : ℝ → ℂ) = deriv φ := by
      funext x
      simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change HasCompactSupport (lineDerivOp (1 : ℝ) φ : ℝ → ℂ)
    rw [he]
    exact hφ.deriv

private theorem integral_Ioi_normalizedPower_mul_schwartz_derivative
    (a : ℝ) (n : ℕ) (φ : SchwartzMap ℝ ℂ) (hφ : HasCompactSupport φ) :
    (∫ x in Ioi a, ((x - a) ^ n / (n.factorial : ℝ) : ℝ) *
      (((lineDerivOp (1 : ℝ))^[n + 1]) φ : SchwartzMap ℝ ℂ) x) =
      (-1 : ℂ) ^ (n + 1) * φ a := by
  induction n with
  | zero =>
    calc
      _ = ∫ x in Ioi a, deriv φ x := by
        simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      _ = -φ a := hφ.integral_Ioi_deriv_eq (φ.smooth 1) a
      _ = _ := by simp
  | succ n ih =>
    let ψ := ((lineDerivOp (1 : ℝ))^[n + 1]) φ
    let P (x : ℝ) : ℂ := ((x - a) ^ (n + 1) / ((n + 1).factorial : ℝ) : ℝ)
    let Q (x : ℝ) : ℂ := ((x - a) ^ n / (n.factorial : ℝ) : ℝ)
    have hψ : HasCompactSupport ψ := hasCompactSupport_schwartz_iterate_lineDeriv_one _ φ hφ
    have hP (x : ℝ) : HasDerivAt P (Q x) x := by
      have hA := hasDerivAt_normalizedPower a x n
      have h := (Complex.ofRealCLM.hasFDerivAt (x := (x - a) ^ (n + 1) /
        ((n + 1).factorial : ℝ))).comp_hasDerivAt x hA
      exact h
    have hCont : ContDiff ℝ 1 (P * (ψ : ℝ → ℂ)) := by
      apply ContDiff.mul _ (ψ.smooth 1)
      exact Complex.ofRealCLM.contDiff.comp
        (((contDiff_id.sub contDiff_const).pow (n + 1)).div_const _)
    have hAt : (P * (ψ : ℝ → ℂ)) a = 0 := by simp [P]
    have hInt := hψ.mul_left.integral_Ioi_deriv_eq hCont a
    have hDeriv : deriv (P * (ψ : ℝ → ℂ)) =
        fun x => Q x * ψ x + P x * (lineDerivOp (1 : ℝ) ψ) x := by
      funext x
      have hh := ((hP x).mul (ψ.hasDerivAt x)).deriv
      simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv] using hh
    rw [hDeriv, hAt, neg_zero] at hInt
    have hContQ : Continuous Q := Complex.ofRealCLM.continuous.comp
      (((continuous_id.sub continuous_const).pow n).div_const _)
    have hIntQ : Integrable (fun x : ℝ => Q x * ψ x) :=
      (hContQ.mul ψ.continuous).integrable_of_hasCompactSupport hψ.mul_left
    have hψ' : HasCompactSupport (lineDerivOp (1 : ℝ) ψ : SchwartzMap ℝ ℂ) :=
      hasCompactSupport_schwartz_iterate_lineDeriv_one 1 ψ hψ
    have hContP : Continuous P := Complex.ofRealCLM.continuous.comp
      (((continuous_id.sub continuous_const).pow (n + 1)).div_const _)
    have hIntP : Integrable (fun x : ℝ => P x * (lineDerivOp (1 : ℝ) ψ) x) :=
      (hContP.mul (lineDerivOp (1 : ℝ) ψ : SchwartzMap ℝ ℂ).continuous).integrable_of_hasCompactSupport hψ'.mul_left
    rw [integral_add hIntQ.integrableOn hIntP.integrableOn] at hInt
    rw [Function.iterate_succ_apply']
    change (∫ x in Ioi a, P x * (lineDerivOp (1 : ℝ) ψ) x) = _
    rw [eq_neg_of_add_eq_zero_right hInt, show (∫ x in Ioi a, Q x * ψ x) = _ from ih, pow_succ]
    ring

/-- With the sign for weak differentiation, the truncated power test
identity recovers evaluation at the knot. -/
theorem weak_iteratedDeriv_splineAtomPrimitive
    (a : ℝ) (n : ℕ) (φ : SchwartzMap ℝ ℂ) (hφ : HasCompactSupport φ) :
    (-1 : ℂ) ^ (n + 1) *
      (∫ x : ℝ, iteratedDeriv (n + 1) φ x * (splineAtomPrimitive a n x : ℂ)) =
        φ a := by
  have hEq : (∫ x : ℝ, iteratedDeriv (n + 1) φ x * (splineAtomPrimitive a n x : ℂ)) =
      (∫ x in Ioi a, ((x - a) ^ n / (n.factorial : ℝ) : ℝ) *
        (((lineDerivOp (1 : ℝ))^[n + 1]) φ : SchwartzMap ℝ ℂ) x) := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ioi a
    · rw [indicator_of_mem hx, schwartz_iterate_lineDeriv_one_apply]
      simp only [splineAtomPrimitive, indicator_of_mem hx, mul_comm]
    · simp only [splineAtomPrimitive, indicator_of_notMem hx, Complex.ofReal_zero, mul_zero]
  rw [hEq, integral_Ioi_normalizedPower_mul_schwartz_derivative a n φ hφ, ← mul_assoc,
    ← mul_pow]
  norm_num

end
end MeyerGeneralProblem
