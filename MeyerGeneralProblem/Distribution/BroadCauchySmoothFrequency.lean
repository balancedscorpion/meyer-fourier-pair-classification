module

public import MeyerGeneralProblem.Distribution.BroadCauchyHalfLineFourier
public import MeyerGeneralProblem.Distribution.BroadCauchyCutoffConvolution
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Schwartz regularity of the Cauchy frequencies away from zero

After a fixed smooth mask removes a neighborhood of zero, the exact
half-line inverse Fourier formula is a Schwartz function.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set Polynomial
open scoped FourierTransform Topology ContDiff

private theorem pow_mul_exp_neg_mul_le (s : ℝ) (hs : 0 < s) (j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x ^ j * Real.exp (-s * x) ≤ (j.factorial : ℝ) / s ^ j := by
  have he := Real.pow_div_factorial_le_exp (s * x) (mul_nonneg hs.le hx) j
  have hfact : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  apply (le_div_iff₀ (pow_pos hs _)).mpr
  rw [mul_right_comm, ← mul_pow, mul_comm x s, show -s * x = -(s * x) by ring, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  simpa only [mul_comm (Real.exp (s * x))] using (div_le_iff₀ hfact).mp he

private theorem norm_polynomial_mul_laplaceExp_weighted_le (s : ℂ) (hs : 0 < s.re)
    (P : Polynomial ℂ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      |x| ^ k * ‖P.eval (x : ℂ) * Complex.exp (-s * (x : ℂ))‖ ≤ C := by
  let C := ∑ i ∈ P.support, ‖P.coeff i‖ * (((k + i).factorial : ℝ) / s.re ^ (k + i))
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨C, hC, fun x hx => ?_⟩
  have he : ‖Complex.exp (-s * (x : ℂ))‖ = Real.exp (-s.re * x) := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  rw [norm_mul, he, Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc
    _ ≤ |x| ^ k * ((∑ i ∈ P.support, ‖P.coeff i * (x : ℂ) ^ i‖) * Real.exp (-s.re * x)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le) (by positivity)
    _ = ∑ i ∈ P.support, ‖P.coeff i‖ * (x ^ (k + i) * Real.exp (-s.re * x)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx, pow_add]
      ring
    _ ≤ C := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (pow_mul_exp_neg_mul_le s.re hs _ x hx) (norm_nonneg _)

private theorem exists_polynomial_iteratedDeriv_mul_laplaceExp (s : ℂ)
    (P : Polynomial ℂ) (j : ℕ) :
    ∃ Q : Polynomial ℂ, iteratedDeriv j (fun x : ℝ => P.eval (x : ℂ) * Complex.exp (-s * (x : ℂ))) =
      fun x : ℝ => Q.eval (x : ℂ) * Complex.exp (-s * (x : ℂ)) := by
  induction j with
  | zero => exact ⟨P, rfl⟩
  | succ j ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨Q.derivative - C s * Q, ?_⟩
    rw [iteratedDeriv_succ, hQ]
    funext x
    have hQ' : HasDerivAt (fun t : ℝ => Q.eval (t : ℂ)) (Q.derivative.eval (x : ℂ)) x :=
      (Q.hasDerivAt (x : ℂ)).comp_ofReal
    rw [(hQ'.fun_mul (hasDerivAt_laplaceExp s x)).deriv,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    ring

private theorem norm_iteratedDeriv_polynomial_mul_laplaceExp_weighted_le (s : ℂ) (hs : 0 < s.re)
    (P : Polynomial ℂ) (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      |x| ^ k * ‖iteratedDeriv j (fun t : ℝ => P.eval (t : ℂ) *
        Complex.exp (-s * (t : ℂ))) x‖ ≤ C := by
  obtain ⟨Q, hQ⟩ := exists_polynomial_iteratedDeriv_mul_laplaceExp s P j
  rw [hQ]
  exact norm_polynomial_mul_laplaceExp_weighted_le s hs Q k

private theorem exists_maskedUpperPolynomialSchwartz (s : ℂ) (hs : 0 < s.re)
    (P : Polynomial ℂ) (χ : SchwartzMap ℝ ℂ)
    (hχ : ∀ᶠ t in 𝓝 (0 : ℝ), χ t = 1) :
    ∃ H : SchwartzMap ℝ ℂ, ∀ t : ℝ,
      H t = (1 - χ t) * (Ioi (0 : ℝ)).indicator
        (fun x => P.eval (x : ℂ) * Complex.exp (-s * (x : ℂ))) t := by
  let F (x : ℝ) := P.eval (x : ℂ) * Complex.exp (-s * (x : ℂ))
  let θ (x : ℝ) := 1 - χ x
  let f (x : ℝ) := θ x * (Ioi (0 : ℝ)).indicator F x
  have hpos (x : ℝ) (hx : 0 < x) : f =ᶠ[𝓝 x] (θ * F) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [f, Pi.mul_apply, indicator_of_mem hy]
  have hnonpos (x : ℝ) (hx : x ≤ 0) : f =ᶠ[𝓝 x] (fun _ => 0) := by
    rcases lt_or_eq_of_le hx with hx | rfl
    · filter_upwards [Iio_mem_nhds hx] with y hy
      have h : y ∉ Ioi (0 : ℝ) := fun h => (not_lt_of_gt (mem_Iio.mp hy)) (mem_Ioi.mp h)
      simp only [f, indicator_of_notMem h, mul_zero]
    · filter_upwards [hχ] with y hy
      simp only [f, θ, hy, sub_self, zero_mul]
  have hF : ContDiff ℝ ∞ F := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro i _
    obtain ⟨Q, hQ⟩ := exists_polynomial_iteratedDeriv_mul_laplaceExp s P i
    rw [show iteratedDeriv i F = _ from hQ]
    intro t
    exact (((Q.hasDerivAt (t : ℂ)).comp_ofReal).fun_mul (hasDerivAt_laplaceExp s t)).differentiableAt
  have hθ : ContDiff ℝ ∞ θ := contDiff_const.sub (χ.smooth ⊤)
  refine ⟨⟨f, contDiff_iff_contDiffAt.mpr (fun x => ?_), fun k j => ?_⟩, fun t => rfl⟩
  · by_cases hx : 0 < x
    · exact (hθ.mul hF).contDiffAt.congr_of_eventuallyEq (hpos x hx)
    · exact contDiffAt_const.congr_of_eventuallyEq (hnonpos x (le_of_not_gt hx))
  · have hbound (i : ℕ) := norm_iteratedDeriv_polynomial_mul_laplaceExp_weighted_le s hs P k i
    choose D hD hDval using hbound
    let B (i : ℕ) := (j.choose i : ℝ) * (1 + SchwartzMap.seminorm ℂ 0 i χ) * D (j - i)
    let C := ∑ i ∈ Finset.range (j + 1), B i
    have hC : 0 ≤ C := Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (hD _)
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    by_cases hx : 0 < x
    · rw [(hpos x hx).iteratedDeriv_eq j, iteratedDeriv_mul
        (contDiffAt_const.sub (χ.smooth j).contDiffAt) ((hF.of_le (by simp)).contDiffAt)]
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hi := norm_iteratedDeriv_one_sub_schwartz_le χ i x
      have ht := hDval (j - i) x hx.le
      simp only [norm_mul, norm_natCast]
      calc
        _ = (j.choose i : ℝ) * ‖iteratedDeriv i θ x‖ * (|x| ^ k * ‖iteratedDeriv (j - i) F x‖) := by ring
        _ ≤ B i := mul_le_mul (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)) ht (by positivity) (by positivity)
    · rw [(hnonpos x (le_of_not_gt hx)).iteratedDeriv_eq j]
      simpa only [iteratedDeriv_const, ite_self, norm_zero, mul_zero] using hC

private theorem exists_maskedUpperCauchyFrequencySchwartz
    (χ : SchwartzMap ℝ ℂ) (hχ : ∀ᶠ t in 𝓝 (0 : ℝ), χ t = 1)
    (n : ℕ) (z : ℂ) (hz : 0 < z.im) :
    ∃ H : SchwartzMap ℝ ℂ, ∀ t : ℝ, H t = (1 - χ t) * upperCauchyFrequency n z t := by
  let s : ℂ := -(((2 * Real.pi : ℝ) : ℂ) * Complex.I * z)
  have hs : 0 < s.re := by
    dsimp only [s]
    simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one,
      zero_sub, neg_neg]
    positivity
  let P : Polynomial ℂ := C (broadCauchyFourierFactor n) * X ^ n
  obtain ⟨H, hH⟩ := exists_maskedUpperPolynomialSchwartz s hs P χ hχ
  refine ⟨H, fun t => ?_⟩
  rw [hH t, upperCauchyFrequency]
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem ht, P, eval_mul, eval_C, eval_pow, eval_X]
    congr 3
    dsimp only [s]
    ring
  · simp only [indicator_of_notMem ht]

/-- Removing a neighborhood of zero turns the exact Cauchy frequency
function into a Schwartz test on either half-plane. -/
theorem exists_maskedCauchyFrequencySchwartz
    (χ : SchwartzMap ℝ ℂ) (hχ : ∀ᶠ t in 𝓝 (0 : ℝ), χ t = 1)
    (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    ∃ H : SchwartzMap ℝ ℂ, ∀ t : ℝ, H t = (1 - χ t) * broadCauchyFrequency n z t := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · let χ' := combSchwartzDilation (-1) (by norm_num) χ
    have hn : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      simpa only [neg_zero] using (continuous_neg : Continuous (fun t : ℝ => -t)).tendsto 0
    have hχ' : ∀ᶠ t in 𝓝 (0 : ℝ), χ' t = 1 := by
      filter_upwards [hn.eventually hχ] with t ht
      simpa only [χ', combSchwartzDilation_apply, neg_mul, one_mul] using ht
    have hpos' : 0 < (-z).im := by simpa only [Complex.neg_im] using neg_pos.mpr hneg
    obtain ⟨H, hH⟩ := exists_maskedUpperCauchyFrequencySchwartz χ' hχ' n (-z) hpos'
    refine ⟨(-1 : ℂ) ^ (n + 1) • combSchwartzDilation (-1) (by norm_num) H, fun t => ?_⟩
    rw [broadCauchyFrequency, ite_eq_right hneg.not_gt, lowerCauchyFrequency_eq_reflection]
    rw [smul_apply, combSchwartzDilation_apply, neg_mul, one_mul, hH]
    simp only [χ', combSchwartzDilation_apply, neg_mul, one_mul, neg_neg,
      Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    change _ = (1 - χ t) * ((-1 : ℂ) ^ (n + 1) * upperCauchyFrequency n (-z) (-t))
    ring
  · simpa only [broadCauchyFrequency, ite_eq_left hpos] using
      exists_maskedUpperCauchyFrequencySchwartz χ hχ n z hpos

private theorem iteratedDeriv_laplaceExp (s : ℂ) (j : ℕ) :
    iteratedDeriv j (fun x : ℝ => Complex.exp (-s * (x : ℂ))) =
      fun x : ℝ => (-s) ^ j * Complex.exp (-s * (x : ℂ)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, (hasDerivAt_laplaceExp s x).deriv, pow_succ, mul_assoc]

private theorem norm_iteratedDeriv_polynomial_mul_realLaplaceExp_uniform
    (P : Polynomial ℂ) (a : ℝ) (ha : 0 ≤ a) (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s x : ℝ, 1 ≤ s → a ≤ x →
      |x| ^ k * ‖iteratedDeriv j (fun t : ℝ => P.eval (t : ℂ) *
        Complex.exp (-(s : ℂ) * (t : ℂ))) x‖ ≤ C * s ^ j * Real.exp (-s * a) := by
  have hpoly (i : ℕ) :
      ∃ Q : Polynomial ℂ, iteratedDeriv i (fun x : ℝ => P.eval (x : ℂ)) =
        fun x : ℝ => Q.eval (x : ℂ) := by
    simpa only [neg_zero, zero_mul, Complex.exp_zero, mul_one] using
      exists_polynomial_iteratedDeriv_mul_laplaceExp 0 P i
  choose Q hQ using hpoly
  have hbound (i : ℕ) := norm_polynomial_mul_laplaceExp_weighted_le 1 (by norm_num) (Q i) k
  choose D hD hDval using hbound
  let B (i : ℕ) := (j.choose i : ℝ) * D i * Real.exp a
  let C := ∑ i ∈ Finset.range (j + 1), B i
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hD i)) (Real.exp_pos _).le
  refine ⟨C, hC, fun s x hs hx => ?_⟩
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hx0 : 0 ≤ x := ha.trans hx
  have hP : ContDiff ℝ (↑j : ℕ∞ω) (fun t : ℝ => P.eval (t : ℂ)) := by
    apply contDiff_of_differentiable_iteratedDeriv (n := (j : ℕ∞))
    intro i _
    rw [hQ]
    exact fun t => ((Q i).hasDerivAt (t : ℂ)).comp_ofReal.differentiableAt
  have hE : ContDiff ℝ (↑j : ℕ∞ω) (fun t : ℝ => Complex.exp (-(s : ℂ) * (t : ℂ))) := by
    apply contDiff_of_differentiable_iteratedDeriv (n := (j : ℕ∞))
    intro i _
    rw [iteratedDeriv_laplaceExp]
    exact fun t => ((hasDerivAt_laplaceExp (s : ℂ) t).const_mul _).differentiableAt
  have hexp : Real.exp (-s * x) ≤ Real.exp (-x) * Real.exp a * Real.exp (-s * a) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hx)])
  change |x| ^ k * ‖iteratedDeriv j ((fun t : ℝ => P.eval (t : ℂ)) *
    (fun t : ℝ => Complex.exp (-(s : ℂ) * (t : ℂ)))) x‖ ≤ _
  rw [iteratedDeriv_mul hP.contDiffAt hE.contDiffAt]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  rw [Finset.mul_sum, show C = ∑ i ∈ Finset.range (j + 1), B i from rfl,
    Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hQx : |x| ^ k * ‖(Q i).eval (x : ℂ)‖ * Real.exp (-x) ≤ D i := by
    simpa only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, one_mul, mul_zero,
      sub_zero, neg_one_mul, mul_assoc] using hDval i x hx0
  have hpow : s ^ (j - i) ≤ s ^ j := pow_le_pow_right₀ hs (Nat.sub_le _ _)
  rw [hQ, iteratedDeriv_laplaceExp]
  simp only [norm_mul, norm_pow, norm_natCast, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hs0, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, mul_zero, sub_zero]
  calc
    _ = (j.choose i : ℝ) * (|x| ^ k * ‖(Q i).eval (x : ℂ)‖) *
        (s ^ (j - i) * Real.exp (-s * x)) := by ring
    _ ≤ (j.choose i : ℝ) * (|x| ^ k * ‖(Q i).eval (x : ℂ)‖) *
        (s ^ j * (Real.exp (-x) * Real.exp a * Real.exp (-s * a))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)) (by positivity)
    _ = (j.choose i : ℝ) * (|x| ^ k * ‖(Q i).eval (x : ℂ)‖ * Real.exp (-x)) *
        Real.exp a * s ^ j * Real.exp (-s * a) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQx (Nat.cast_nonneg _)) (Real.exp_pos _).le)
        (by positivity)) (Real.exp_pos _).le

private theorem seminorm_maskedUpperCauchyFrequency_vertical_le
    (χ : SchwartzMap ℝ ℂ) (a : ℝ) (ha : 0 < a) (hχ : ∀ x : ℝ, |x| < a → χ x = 1)
    (n k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : ℝ), 1 ≤ y → ∀ H : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, H x = (1 - χ x) * upperCauchyFrequency n ((y : ℂ) * Complex.I) x) →
      SchwartzMap.seminorm ℂ k j H ≤
        C * (2 * Real.pi * y) ^ j * Real.exp (-(2 * Real.pi * y) * a) := by
  let P : Polynomial ℂ := C (broadCauchyFourierFactor n) * X ^ n
  have hbound (i : ℕ) := norm_iteratedDeriv_polynomial_mul_realLaplaceExp_uniform P a ha.le k i
  choose D hD hDval using hbound
  let B (i : ℕ) := (j.choose i : ℝ) * (1 + SchwartzMap.seminorm ℂ 0 i χ) * D (j - i)
  let A := ∑ i ∈ Finset.range (j + 1), B i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (hD _)
  refine ⟨A, hA, fun y hy H hH => ?_⟩
  let s := 2 * Real.pi * y
  have hs : 1 ≤ s := by
    dsimp only [s]
    nlinarith [Real.pi_gt_three, mul_nonneg (sub_nonneg.mpr hy) (Real.pi_pos.le)]
  have hs₀ : 0 ≤ s := zero_le_one.trans hs
  let E (x : ℝ) := P.eval (x : ℂ) * Complex.exp (-(s : ℂ) * (x : ℂ))
  let θ (x : ℝ) := 1 - χ x
  have hE : ContDiff ℝ (↑j : ℕ∞ω) E := by
    apply contDiff_of_differentiable_iteratedDeriv (n := (j : ℕ∞))
    intro i _
    obtain ⟨Q, hQ⟩ := exists_polynomial_iteratedDeriv_mul_laplaceExp (s : ℂ) P i
    rw [show iteratedDeriv i E = _ from hQ]
    intro t
    exact (((Q.hasDerivAt (t : ℂ)).comp_ofReal).fun_mul (hasDerivAt_laplaceExp (s : ℂ) t)).differentiableAt
  have hraw (x : ℝ) (hx : 0 < x) : upperCauchyFrequency n ((y : ℂ) * Complex.I) x = E x := by
    rw [upperCauchyFrequency, indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    dsimp only [E, P]
    rw [eval_mul, eval_C, eval_pow, eval_X]
    have he : ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (x : ℂ) * ((y : ℂ) * Complex.I) =
        -(s : ℂ) * (x : ℂ) := by
      dsimp only [s]
      push_cast
      calc
        _ = 2 * (Real.pi : ℂ) * (y : ℂ) * (x : ℂ) * Complex.I ^ 2 := by ring
        _ = _ := by rw [Complex.I_sq]; ring
    rw [he]
  refine SchwartzMap.seminorm_le_bound' ℂ k j _
    (show 0 ≤ A * s ^ j * Real.exp (-s * a) from by positivity) fun x => ?_
  change |x| ^ k * ‖iteratedDeriv j (H : ℝ → ℂ) x‖ ≤ A * s ^ j * Real.exp (-s * a)
  by_cases hx : a ≤ x
  · have hpos : (H : ℝ → ℂ) =ᶠ[𝓝 x] θ * E := by
      filter_upwards [Ioi_mem_nhds (ha.trans_le hx)] with t ht
      rw [hH t, hraw t ht]
      rfl
    rw [hpos.iteratedDeriv_eq j, iteratedDeriv_mul
      (contDiffAt_const.sub (χ.smooth j).contDiffAt) hE.contDiffAt]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.mul_sum, show A = ∑ i ∈ Finset.range (j + 1), B i from rfl,
      Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi := norm_iteratedDeriv_one_sub_schwartz_le χ i x
    have ht := hDval (j - i) s x hs hx
    have hp := pow_le_pow_right₀ hs (Nat.sub_le j i)
    simp only [norm_mul, norm_natCast]
    calc
      _ = (j.choose i : ℝ) * ‖iteratedDeriv i θ x‖ * (|x| ^ k * ‖iteratedDeriv (j - i) E x‖) := by ring
      _ ≤ (j.choose i : ℝ) * (1 + SchwartzMap.seminorm ℂ 0 i χ) *
          (D (j - i) * s ^ (j - i) * Real.exp (-s * a)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)) ht (by positivity) (by positivity)
      _ ≤ (j.choose i : ℝ) * (1 + SchwartzMap.seminorm ℂ 0 i χ) *
          (D (j - i) * s ^ j * Real.exp (-s * a)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (hD _)) (Real.exp_pos _).le)
        (by positivity)
      _ = _ := by dsimp only [B]; ring
  · have he : (H : ℝ → ℂ) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds (lt_of_not_ge hx)] with t ht
      rw [hH t]
      by_cases ht₀ : 0 < t
      · rw [hχ t (by rwa [abs_of_pos ht₀]), sub_self, zero_mul]
      · rw [upperCauchyFrequency, indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht₀), mul_zero]
    rw [he.iteratedDeriv_eq j]
    simp only [iteratedDeriv_const, ite_self, norm_zero, mul_zero]
    positivity

private theorem seminorm_le_of_unit_reflection (c : ℂ) (hc : ‖c‖ = 1)
    (f g : SchwartzMap ℝ ℂ) (hg : ∀ x : ℝ, g x = c * f (-x)) (k j : ℕ) :
    SchwartzMap.seminorm ℂ k j f ≤ SchwartzMap.seminorm ℂ k j g := by
  refine SchwartzMap.seminorm_le_bound' ℂ k j _ (apply_nonneg _ _) fun x => ?_
  have hf := SchwartzMap.le_seminorm' ℂ k j g (-x)
  have he : (g : ℝ → ℂ) = fun t => c * f (-t) := funext hg
  rw [he, iteratedDeriv_const_mul_field, iteratedDeriv_comp_neg, norm_mul, norm_smul,
    norm_pow, norm_neg, norm_one, one_pow, hc, one_mul, one_mul, neg_neg, abs_neg] at hf
  exact hf

/-- Both original masked half-line formulas decay at the exponent given
by the inner mask radius. The remaining factor has degree j in y,
uniformly for y at least one. -/
theorem seminorm_maskedCauchyFrequency_vertical_le
    (χ : SchwartzMap ℝ ℂ) (a : ℝ) (ha : 0 < a) (hχ : ∀ x : ℝ, |x| < a → χ x = 1)
    (n k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : ℝ), 1 ≤ y → ∀ Hplus Hminus : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, Hplus x = (1 - χ x) * broadCauchyFrequency n ((y : ℂ) * Complex.I) x) →
      (∀ x : ℝ, Hminus x = (1 - χ x) * broadCauchyFrequency n (-((y : ℂ) * Complex.I)) x) →
      SchwartzMap.seminorm ℂ k j Hplus + SchwartzMap.seminorm ℂ k j Hminus ≤
        C * (2 * Real.pi * y) ^ j * Real.exp (-(2 * Real.pi * y) * a) := by
  obtain ⟨A, hA, hpos⟩ := seminorm_maskedUpperCauchyFrequency_vertical_le χ a ha hχ n k j
  let χ' := combSchwartzDilation (-1) (by norm_num) χ
  have hχ'e (x : ℝ) : χ' x = χ (-x) := by
    simp only [χ', combSchwartzDilation_apply, neg_mul, one_mul]
  have hχ' (x : ℝ) (hx : |x| < a) : χ' x = 1 := by rw [hχ'e]; exact hχ (-x) (by simpa only [abs_neg])
  obtain ⟨B, hB, hneg⟩ := seminorm_maskedUpperCauchyFrequency_vertical_le χ' a ha hχ' n k j
  refine ⟨A + B, add_nonneg hA hB, fun y hy Hplus Hminus hPlusEq hMinusEq => ?_⟩
  let z := (y : ℂ) * Complex.I
  have hz : 0 < z.im := by
    simpa only [z, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero] using (zero_lt_one.trans_le hy)
  have hz' : ¬0 < (-z).im := by simpa only [Complex.neg_im, not_lt] using (neg_nonpos.mpr hz.le)
  have hplus := hpos y hy Hplus (fun x => by
    have h := hPlusEq x
    change Hplus x = (1 - χ x) * broadCauchyFrequency n z x at h
    rw [broadCauchyFrequency, ite_eq_left hz] at h
    exact h)
  let c : ℂ := (-1 : ℂ) ^ (n + 1)
  have hc : ‖c‖ = 1 := by simp only [c, norm_pow, norm_neg, norm_one, one_pow]
  have hc₂ : c * c = 1 := by dsimp only [c]; rw [← mul_pow]; norm_num
  let H' := c • combSchwartzDilation (-1) (by norm_num) Hminus
  have hH'e (x : ℝ) : H' x = c * Hminus (-x) := by simp only [H', smul_apply,
    combSchwartzDilation_apply, neg_mul, one_mul, smul_eq_mul]
  have hH' (x : ℝ) : H' x = (1 - χ' x) * upperCauchyFrequency n z x := by
    have h := hMinusEq (-x)
    change Hminus (-x) = (1 - χ (-x)) * broadCauchyFrequency n (-z) (-x) at h
    rw [hH'e, h, broadCauchyFrequency, ite_eq_right hz',
      lowerCauchyFrequency_eq_reflection, hχ'e]
    simp only [neg_neg, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    have hn : (LinearIsometryEquiv.neg ℝ (E := ℝ)) (-x) = x := by
      change -(-x) = x
      exact neg_neg x
    rw [hn]
    change c * ((1 - χ (-x)) * (c * upperCauchyFrequency n z x)) = _
    calc
      _ = (c * c) * ((1 - χ (-x)) * upperCauchyFrequency n z x) := by ring
      _ = _ := by rw [hc₂, one_mul]
  have hminus := (seminorm_le_of_unit_reflection c hc Hminus H' hH'e k j).trans (hneg y hy H' hH')
  exact (add_le_add hplus hminus).trans_eq (by ring)

end

end MeyerGeneralProblem
