module

public import MeyerGeneralProblem.Sampling.BernsteinJensen
public import MeyerGeneralProblem.Sampling.LocalSelectedZeroJensen

@[expose] public section

/-!
# The local Jensen step for the quadratic KNS argument

The logarithmic mean on a circle with real center retains the exact coefficient
`2 * a * r` from an actual boundary bound `M * exp (a * π * |Im z|)`.
Finite selected real zeros contribute their actual distance-to-radius product,
with the zero-center case included. The hypotheses concern an analytic
neighborhood of the closed disk; no sector principle, indicator bound, or
zero-density estimate is supplied by this module.
-/

noncomputable section

open Set Complex MeasureTheory Metric Real

namespace MeyerGeneralProblem

/-- Translating a circle along the real axis does not change the mean absolute
imaginary part. The exact factor is `2 / π`, including a signed radius. -/
theorem circleAverage_abs_im_realCenter (x r : ℝ) :
    Real.circleAverage (fun z : ℂ => |z.im|) (x : ℂ) r = 2 * |r| / π := by
  rw [← Real.circleAverage_map_add_const]
  simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using
    circleAverage_abs_im_zero r

/-- A genuine local analytic boundary estimate gives the sharp logarithmic
circle mean. The nonnegative rate and `M ≥ 1` also dominate the totalized real
logarithm at boundary zeros, which need not be excluded. -/
theorem circleAverage_log_norm_le_of_localSectorGrowth
    {F : ℂ → ℂ} {x r a M : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hM : 1 ≤ M)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall (x : ℂ) r))
    (hboundary : ∀ z ∈ Metric.sphere (x : ℂ) r,
      ‖F z‖ ≤ M * Real.exp (a * Real.pi * |z.im|)) :
    Real.circleAverage (fun z => Real.log ‖F z‖) (x : ℂ) r ≤
      Real.log M + 2 * a * r := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hA : AnalyticOnNhd ℂ F (Metric.closedBall (x : ℂ) |r|) := by
    simpa only [abs_of_pos hr] using hF
  have hlog : CircleIntegrable (fun z => Real.log ‖F z‖) (x : ℂ) r :=
    (hA.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hmajor : ∀ z ∈ Metric.sphere (x : ℂ) |r|,
      Real.log ‖F z‖ ≤ Real.log M + a * π * |z.im| := by
    intro z hz
    rw [abs_of_pos hr] at hz
    by_cases hz0 : F z = 0
    · simp only [hz0, norm_zero, Real.log_zero]
      exact add_nonneg (Real.log_nonneg hM) (by positivity)
    · calc
        Real.log ‖F z‖ ≤ Real.log (M * Real.exp (a * π * |z.im|)) :=
          Real.log_le_log (norm_pos_iff.mpr hz0) (hboundary z hz)
        _ = Real.log M + a * π * |z.im| := by
          rw [Real.log_mul hMpos.ne' (Real.exp_ne_zero _), Real.log_exp]
  calc
    _ ≤ Real.circleAverage (fun z : ℂ => Real.log M + a * π * |z.im|) (x : ℂ) r :=
      Real.circleAverage_mono hlog (by fun_prop) hmajor
    _ = Real.log M + 2 * a * r := by
      rw [Real.circleAverage_fun_add (by fun_prop) (by fun_prop),
        Real.circleAverage_const]
      change Real.log M + Real.circleAverage (fun z : ℂ => (a * π) • |z.im|)
        (x : ℂ) r = _
      rw [Real.circleAverage_fun_smul, circleAverage_abs_im_realCenter, abs_of_pos hr]
      simp only [smul_eq_mul]
      field_simp

/-- The zero-safe finite selected-zero Jensen estimate used in KNS Claim 3.
Only actual local analyticity, circle bounds and selected zeros are inputs;
neither an exhaustive zero list nor a sector principle is assumed. -/
theorem norm_center_le_sectorGrowth_mul_selectedZeroProduct
    {F : ℂ → ℂ} {x r a M : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hM : 1 ≤ M)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall (x : ℂ) r))
    (hboundary : ∀ z ∈ Metric.sphere (x : ℂ) r,
      ‖F z‖ ≤ M * Real.exp (a * Real.pi * |z.im|))
    (Z : Finset ℝ) (hzero : ∀ z ∈ Z, F (z : ℂ) = 0)
    (hinside : ∀ z ∈ Z, |z - x| < r) :
    ‖F (x : ℂ)‖ ≤ M * Real.exp (2 * a * r) *
      ∏ z ∈ Z, (|x - z| / r) := by
  classical
  let Zc : Finset ℂ := Z.image (fun z : ℝ => (z : ℂ))
  have hzeros : ∀ z ∈ Zc, F z = 0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact hzero w hw
  have hnodes : ∀ z ∈ Zc, ‖(x : ℂ) - z‖ ≤ r := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_sub_comm] using (hinside w hw).le
  have hprod : (∏ z ∈ Zc, ‖(x : ℂ) - z‖ / r) =
      ∏ z ∈ Z, (|x - z| / r) := by
    dsimp only [Zc]
    rw [Finset.prod_image (fun _ _ _ _ h => Complex.ofReal_injective h)]
    apply Finset.prod_congr rfl
    intro z hz
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hbase := norm_le_exp_circleAverage_mul_prod_of_selected_zeros
    hr hF Zc hzeros hnodes
  rw [hprod] at hbase
  have havg := circleAverage_log_norm_le_of_localSectorGrowth hr ha hM hF hboundary
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  calc
    _ ≤ Real.exp (Real.circleAverage (fun z => Real.log ‖F z‖) (x : ℂ) r) *
        ∏ z ∈ Z, (|x - z| / r) := hbase
    _ ≤ Real.exp (Real.log M + 2 * a * r) * ∏ z ∈ Z, (|x - z| / r) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr havg)
        (Finset.prod_nonneg fun z _ => div_nonneg (abs_nonneg _) hr.le)
    _ = _ := by rw [Real.exp_add, Real.exp_log hMpos]

end MeyerGeneralProblem
