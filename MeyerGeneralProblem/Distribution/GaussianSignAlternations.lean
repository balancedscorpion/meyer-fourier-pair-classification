module

public import MeyerGeneralProblem.Distribution.SignAlternationCut
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# Sign alternations under Gaussian smoothing

Differentiation of a compactly supported Laplace integral produces
the linear factor at its first sign cut. Rolle's theorem and induction
then control the sign alternations of the real Gaussian convolution.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

private def shiftedRealLaplace (f : ℝ → ℝ) (a y : ℝ) : ℝ :=
  ∫ x : ℝ, f x * Real.exp (y * (x - a))

private theorem abs_sub_le_bound_add_abs {x a B : ℝ} (hx : |x| ≤ B) :
    |x - a| ≤ B + |a| := by
  calc
    |x - a| ≤ |x| + |a| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-a)
    _ ≤ _ := add_le_add hx le_rfl

private theorem exp_mul_sub_le_of_abs_le {x a B y K : ℝ}
    (hx : |x| ≤ B) (hy : |y| ≤ K) (hK : 0 ≤ K) :
    Real.exp (y * (x - a)) ≤ Real.exp (K * (B + |a|)) := by
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |y * (x - a)| := le_abs_self _
    _ = |y| * |x - a| := abs_mul _ _
    _ ≤ _ :=
      mul_le_mul hy (abs_sub_le_bound_add_abs hx) (abs_nonneg _) hK

private theorem integrable_shiftedRealLaplace_integrand {f : ℝ → ℝ}
    (hf : Integrable f) {B : ℝ} (hSupp : ∀ x, B < |x| → f x = 0)
    (a y : ℝ) : Integrable (fun x : ℝ => f x * Real.exp (y * (x - a))) := by
  have hW : Continuous (fun x : ℝ => Real.exp (y * (x - a))) := by fun_prop
  refine (hf.norm.const_mul (Real.exp (|y| * (B + |a|)))).mono'
    (hf.aestronglyMeasurable.mul hW.aestronglyMeasurable) ?_
  filter_upwards with x
  by_cases hx : |x| ≤ B
  · rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _), mul_comm ‖f x‖]
    exact mul_le_mul_of_nonneg_right
      (exp_mul_sub_le_of_abs_le hx le_rfl (abs_nonneg y)) (norm_nonneg _)
  · simp [hSupp x (lt_of_not_ge hx)]

private theorem integrable_sub_mul_of_bounded_support {f : ℝ → ℝ}
    (hf : Integrable f) {B : ℝ} (hSupp : ∀ x, B < |x| → f x = 0)
    (a : ℝ) : Integrable (fun x : ℝ => (x - a) * f x) := by
  have hW : Continuous (fun x : ℝ => x - a) := by fun_prop
  refine (hf.norm.const_mul (B + |a|)).mono'
    (hW.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards with x
  by_cases hx : |x| ≤ B
  · rw [norm_mul, Real.norm_eq_abs (x - a)]
    exact mul_le_mul_of_nonneg_right (abs_sub_le_bound_add_abs hx) (norm_nonneg _)
  · simp [hSupp x (lt_of_not_ge hx)]

private theorem hasDerivAt_shiftedRealLaplace
    {f : ℝ → ℝ} (hf : Integrable f) {B : ℝ}
    (hSupp : ∀ x, B < |x| → f x = 0) (a y : ℝ) :
    HasDerivAt (shiftedRealLaplace f a)
      (shiftedRealLaplace (fun x => (x - a) * f x) a y) y := by
  let F (z x : ℝ) := f x * Real.exp (z * (x - a))
  let D (z x : ℝ) := f x * (Real.exp (z * (x - a)) * (x - a))
  let K := B + |a|
  let C := Real.exp ((|y| + 1) * K) * K
  have hFi (z : ℝ) : Integrable (F z) := integrable_shiftedRealLaplace_integrand hf hSupp a z
  have hDMeas : AEStronglyMeasurable (D y) volume := by
    have hW : Continuous (fun x : ℝ => Real.exp (y * (x - a)) * (x - a)) := by fun_prop
    exact hf.aestronglyMeasurable.mul hW.aestronglyMeasurable
  have hDom : ∀ᵐ x : ℝ ∂volume, ∀ z ∈ Metric.ball y 1, ‖D z x‖ ≤ C * ‖f x‖ := by
    filter_upwards with x z hz
    by_cases hx : |x| ≤ B
    · have hzy : |z - y| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
      have hzBound : |z| ≤ |y| + 1 := by
        calc
          |z| = |(z - y) + y| := by rw [sub_add_cancel]
          _ ≤ |z - y| + |y| := abs_add_le _ _
          _ ≤ _ := by linarith
      have hE : Real.exp (z * (x - a)) ≤ Real.exp ((|y| + 1) * K) :=
        exp_mul_sub_le_of_abs_le hx hzBound (by positivity)
      change ‖f x * (Real.exp (z * (x - a)) * (x - a))‖ ≤ C * ‖f x‖
      rw [norm_mul, norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _),
        Real.norm_eq_abs (x - a), mul_comm ‖f x‖]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hE (abs_sub_le_bound_add_abs hx) (abs_nonneg _) (Real.exp_pos _).le)
        (norm_nonneg _)
    · simp [D, hSupp x (lt_of_not_ge hx)]
  have hDiff : ∀ᵐ x : ℝ ∂volume, ∀ z ∈ Metric.ball y 1,
      HasDerivAt (fun t => F t x) (D z x) z := by
    filter_upwards with x z _
    simpa only [F, D, id_eq, one_mul] using
      ((hasDerivAt_id z).mul_const (x - a)).exp.const_mul (f x)
  have hD := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds y zero_lt_one)
    (Eventually.of_forall fun z => (hFi z).aestronglyMeasurable)
    (hFi y) hDMeas hDom (hf.norm.const_mul C) hDiff).2
  have hIntegral : (∫ x : ℝ, D y x) = shiftedRealLaplace (fun x => (x - a) * f x) a y := by
    apply integral_congr_ae
    filter_upwards with x
    change f x * (Real.exp (y * (x - a)) * (x - a)) = (x - a) * f x * Real.exp (y * (x - a))
    ring
  rw [hIntegral] at hD
  exact hD

private theorem shiftedRealLaplace_eq_mul (f : ℝ → ℝ) (a y : ℝ) :
    shiftedRealLaplace f a y = Real.exp (-(y * a)) * shiftedRealLaplace f 0 y := by
  unfold shiftedRealLaplace
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [sub_zero, show y * (x - a) = -(y * a) + y * x by ring, Real.exp_add]
  ring

private theorem hasSignAlternations_derivative_univ {f g : ℝ → ℝ} {n : ℕ}
    (h : HasSignAlternations f univ (n + 1)) (hD : ∀ x, HasDerivAt f (g x) x) :
    HasSignAlternations g univ n := by
  obtain ⟨x, hx, _, hAlt⟩ := h
  have hI : HasSignAlternations f (Icc (x 0) (x (Fin.last (n + 1)))) (n + 1) :=
    ⟨x, hx, fun i => ⟨hx.monotone (Fin.zero_le i), hx.monotone (Fin.le_last i)⟩, hAlt⟩
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun y => (hD y).continuousAt
  exact (hI.derivative_off_knots (s := ∅) hf.continuousOn (fun y _ _ => hD y)).mono (subset_univ _)

private theorem shiftedRealLaplace_zero_no_extra_signAlternations {B : ℝ}
    (n : ℕ) (f : ℝ → ℝ) (hf : Integrable f) (hSupp : ∀ x, B < |x| → f x = 0)
    (h : ¬ HasSignAlternations f univ (n + 1)) :
    ¬ HasSignAlternations (shiftedRealLaplace f 0) univ (n + 1) := by
  induction n generalizing f with
  | zero =>
    rintro ⟨x, _, _, hAlt⟩
    rcases forall_nonneg_or_forall_nonpos_of_no_signAlternations h with hPos | hNeg
    · have hF (y : ℝ) : 0 ≤ shiftedRealLaplace f 0 y :=
        integral_nonneg fun s => mul_nonneg (hPos s) (Real.exp_pos _).le
      exact (not_lt_of_ge (mul_nonneg (hF _) (hF _))) (hAlt 0)
    · have hF (y : ℝ) : shiftedRealLaplace f 0 y ≤ 0 :=
        integral_nonpos fun s => mul_nonpos_of_nonpos_of_nonneg (hNeg s) (Real.exp_pos _).le
      exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos (hF _) (hF _))) (hAlt 0)
  | succ n ih =>
    intro hOut
    by_cases hIn : HasSignAlternations f univ (n + 1)
    · obtain ⟨a, hCut⟩ := exists_sub_mul_removes_first_sign_change f n hIn h
      let g (x : ℝ) := (x - a) * f x
      have hGInt : Integrable g := integrable_sub_mul_of_bounded_support hf hSupp a
      have hGSupp (x : ℝ) (hx : B < |x|) : g x = 0 := by simp [g, hSupp x hx]
      have hW (y : ℝ) (_ : y ∈ (univ : Set ℝ)) : 0 < Real.exp (-(y * a)) := Real.exp_pos _
      have hShifted : HasSignAlternations (shiftedRealLaplace f a) univ (n + 2) := by
        rw [funext (shiftedRealLaplace_eq_mul f a)]
        exact (hasSignAlternations_pos_mul_iff hW).mpr hOut
      have hD (y : ℝ) : HasDerivAt (shiftedRealLaplace f a) (shiftedRealLaplace g a y) y :=
        hasDerivAt_shiftedRealLaplace hf hSupp a y
      have hShiftedG := hasSignAlternations_derivative_univ hShifted hD
      rw [funext (shiftedRealLaplace_eq_mul g a)] at hShiftedG
      exact ih g hGInt hGSupp hCut ((hasSignAlternations_pos_mul_iff hW).mp hShiftedG)
    · exact ih f hf hSupp hIn hOut.drop_first

/-- Convolution with the normalized real Gaussian of heat parameter `t`
in the convention `exp (-(x-y)^2/t)`. -/
def realGaussianSmoothing (t : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  (Real.sqrt (Real.pi * t))⁻¹ * ∫ x : ℝ, f x * Real.exp (-((x - y) ^ 2) / t)

private theorem realGaussianSmoothing_eq_shiftedRealLaplace
    (t : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    realGaussianSmoothing t f y =
      ((Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-(y ^ 2) / t)) *
        shiftedRealLaplace (fun x => Real.exp (-(x ^ 2) / t) * f x) 0 (2 * y / t) := by
  unfold realGaussianSmoothing shiftedRealLaplace
  rw [mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [sub_zero, show -((x - y) ^ 2) / t = -(y ^ 2) / t + -(x ^ 2) / t + (2 * y / t) * x by ring,
    Real.exp_add, Real.exp_add]
  ring

/-- Every sign-alternation count witnessed after Gaussian smoothing of a
compactly supported real integrable density is also witnessed by the
original density. -/
theorem hasSignAlternations_of_realGaussianSmoothing_of_hasCompactSupport
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Integrable f) (hfComp : HasCompactSupport f)
    {n : ℕ} (h : HasSignAlternations (realGaussianSmoothing t f) univ n) :
    HasSignAlternations f univ n := by
  cases n with
  | zero => exact hasSignAlternations_zero_of_nonempty ⟨0, mem_univ _⟩
  | succ n =>
    obtain ⟨B, hB⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hfComp.isBounded
    have hSupp (x : ℝ) (hx : B < |x|) : f x = 0 := by
      by_contra hz
      have hBall := hB (subset_tsupport f hz)
      have hx' : |x| ≤ B := by
        simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hBall
      exact (not_lt_of_ge hx') hx
    let g (x : ℝ) := Real.exp (-(x ^ 2) / t) * f x
    have hgMeas : AEStronglyMeasurable g volume := by
      have hExp : Continuous (fun x : ℝ => Real.exp (-(x ^ 2) / t)) := by fun_prop
      exact hExp.aestronglyMeasurable.mul hf.aestronglyMeasurable
    have hgInt : Integrable g := by
      apply hf.norm.mono' hgMeas
      filter_upwards with x
      change ‖Real.exp (-(x ^ 2) / t) * f x‖ ≤ ‖f x‖
      rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
      have hle : Real.exp (-(x ^ 2) / t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) ht.le)
      exact mul_le_of_le_one_left (norm_nonneg _) hle
    have hgSupp (x : ℝ) (hx : B < |x|) : g x = 0 := by simp [g, hSupp x hx]
    have hEq : realGaussianSmoothing t f = fun y =>
        ((Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-(y ^ 2) / t)) * shiftedRealLaplace g 0 (2 * y / t) :=
      funext (realGaussianSmoothing_eq_shiftedRealLaplace t f)
    have hC (y : ℝ) (_ : y ∈ (univ : Set ℝ)) :
        0 < (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-(y ^ 2) / t) := by positivity
    rw [hEq] at h
    obtain ⟨x, hMono, _, hAlt⟩ := (hasSignAlternations_pos_mul_iff hC).mp h
    have hScale : StrictMono (fun u : ℝ => 2 * u / t) := fun u v hlt =>
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hlt (by norm_num)) ht
    have hLaplace : HasSignAlternations (shiftedRealLaplace g 0) univ (n + 1) :=
      ⟨fun i => 2 * x i / t, hScale.comp hMono, fun _ => mem_univ _, hAlt⟩
    have hg : HasSignAlternations g univ (n + 1) := by
      by_contra hNo
      exact shiftedRealLaplace_zero_no_extra_signAlternations n g hgInt hgSupp hNo hLaplace
    exact (hasSignAlternations_pos_mul_iff
      (fun x (_ : x ∈ (univ : Set ℝ)) => Real.exp_pos (-(x ^ 2) / t))).mp hg

/-- Every count witnessed after Gaussian smoothing of an interval
restriction is witnessed by the original density inside the interval. -/
theorem hasSignAlternations_on_Icc_of_realGaussianSmoothing_indicator
    {t : ℝ} (ht : 0 < t) {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc a b)) {n : ℕ}
    (h : HasSignAlternations (realGaussianSmoothing t ((Icc a b).indicator f)) univ n) :
    HasSignAlternations f (Icc a b) n := by
  let g := (Icc a b).indicator f
  have hgi : Integrable g := hf.integrable_indicator measurableSet_Icc
  have hgS : tsupport g ⊆ Icc a b := closure_minimal
    (fun x hx => by_contra fun hOut => hx (indicator_of_notMem hOut _)) isClosed_Icc
  have hgC : HasCompactSupport g := isCompact_Icc.of_isClosed_subset isClosed_closure hgS
  cases n with
  | zero => exact hasSignAlternations_zero_of_nonempty ⟨a, le_rfl, hab⟩
  | succ n =>
    obtain ⟨x, hMono, _, hAlt⟩ :=
      hasSignAlternations_of_realGaussianSmoothing_of_hasCompactSupport ht hgi hgC h
    have hMem (i : Fin (n + 2)) : x i ∈ Icc a b := by
      apply hgS
      apply subset_tsupport g
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (mul_ne_zero_iff.mp (ne_of_lt (hAlt 0))).1
      · exact (mul_ne_zero_iff.mp (ne_of_lt (hAlt j))).2
    refine ⟨x, hMono, hMem, fun i => ?_⟩
    simpa only [g, indicator_of_mem (hMem i.castSucc), indicator_of_mem (hMem i.succ)] using hAlt i

end
end MeyerGeneralProblem
