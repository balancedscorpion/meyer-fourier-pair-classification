module

public import MeyerGeneralProblem.Hermite.MehlerFormula
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

@[expose] public section

/-!
# The complex bilinear Hermite Mehler formula

This module analytically continues the real bilinear Hermite Mehler formula
to the complex unit disc.  The continuation is obtained from the compiled
real formula by the identity theorem; the power series radius and analyticity
of the closed expression are proved explicitly.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- The bilinear Hermite coefficients, promoted to a complex formal
multilinear series. -/
def complexHermiteBilinearSeriesFMS (x y : ℝ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n ↦ (hermiteBilinearCoeff x y n : ℂ))

/-- The complex bilinear Hermite power series. -/
def complexHermiteBilinearSeries (x y : ℝ) (z : ℂ) : ℂ :=
  (complexHermiteBilinearSeriesFMS x y).sum z

theorem complexHermiteBilinearSeries_eq_tsum (x y : ℝ) (z : ℂ) :
    complexHermiteBilinearSeries x y z =
      ∑' n : ℕ, (hermiteBilinearCoeff x y n : ℂ) * z ^ n := by
  rw [complexHermiteBilinearSeries,
    FormalMultilinearSeries.sum, tsum_congr]
  intro n
  simp [complexHermiteBilinearSeriesFMS]
  ring

/-- The complex bilinear Hermite series converges throughout the open unit
disc. -/
theorem complexHermiteBilinearSeriesFMS_radius_ge_one (x y : ℝ) :
    (1 : ENNReal) ≤ (complexHermiteBilinearSeriesFMS x y).radius := by
  refine ENNReal.le_of_forall_nnreal_lt (fun r hr ↦ ?_)
  have hr0 : 0 ≤ (r : ℝ) := r.coe_nonneg
  have hr1 : (r : ℝ) < 1 := by
    exact_mod_cast hr
  have hsreal :=
    (summable_hermiteBilinearCoeff_mul_pow
      (r := (r : ℝ)) (by simpa [abs_of_nonneg hr0] using hr1) x y).norm
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  simpa only [complexHermiteBilinearSeriesFMS,
    FormalMultilinearSeries.ofScalars_norm, Complex.norm_real,
    Real.norm_eq_abs, norm_mul, abs_pow, abs_of_nonneg hr0] using hsreal

theorem analyticOnNhd_complexHermiteBilinearSeries (x y : ℝ) :
    AnalyticOnNhd ℂ (complexHermiteBilinearSeries x y)
      (Metric.ball 0 1) := by
  intro z hz
  apply (complexHermiteBilinearSeriesFMS x y).analyticOnNhd
  rw [Metric.mem_eball, edist_dist]
  have hz1 : dist z 0 < 1 := by simpa using hz
  calc
    ENNReal.ofReal (dist z 0) < 1 := ENNReal.ofReal_lt_one.mpr hz1
    _ ≤ (complexHermiteBilinearSeriesFMS x y).radius :=
      complexHermiteBilinearSeriesFMS_radius_ge_one x y

/-- The closed complex Gaussian candidate for the bilinear Hermite series. -/
def complexHermiteBilinearClosed (x y : ℝ) (z : ℂ) : ℂ :=
  (1 - z ^ 2) ^ (-(1 / 2 : ℂ)) *
    Complex.exp
      ((2 * z * x * y - z ^ 2 * (x ^ 2 + y ^ 2)) /
        (2 * (1 - z ^ 2)))

theorem analyticOnNhd_complexHermiteBilinearClosed (x y : ℝ) :
    AnalyticOnNhd ℂ (complexHermiteBilinearClosed x y)
      (Metric.ball 0 1) := by
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have hsq : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  have hslit : 1 - z ^ 2 ∈ Complex.slitPlane := by
    rw [sub_eq_add_neg]
    apply Complex.mem_slitPlane_of_norm_lt_one
    simpa using hsq
  unfold complexHermiteBilinearClosed
  apply AnalyticAt.mul
  · have hbase : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w ^ 2) z := by
      fun_prop
    have hexponent : AnalyticAt ℂ (fun _w : ℂ ↦ (-(1 / 2 : ℂ))) z := by
      fun_prop
    exact hbase.cpow hexponent hslit
  · apply AnalyticAt.cexp
    apply AnalyticAt.div (by fun_prop) (by fun_prop)
    exact mul_ne_zero (by norm_num) (Complex.slitPlane_ne_zero hslit)

theorem complexHermiteBilinearSeries_ofReal (r x y : ℝ) :
    complexHermiteBilinearSeries x y (r : ℂ) =
      (hermiteBilinearSeries x y r : ℂ) := by
  rw [complexHermiteBilinearSeries_eq_tsum,
    hermiteBilinearSeries, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  push_cast
  ring

theorem complexHermiteBilinearClosed_ofReal
    {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    complexHermiteBilinearClosed x y (r : ℂ) =
      (hermiteBilinearClosed x y r : ℂ) := by
  have hr2 : r ^ 2 < 1 := by
    rw [← sq_abs]
    simpa only [pow_two, one_mul] using
      mul_self_lt_mul_self (abs_nonneg r) hr
  have hqpos : 0 < 1 - r ^ 2 := by linarith
  have hexponent : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by
    norm_num
  have hcpow : (((1 - r ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) =
      (((Real.sqrt (1 - r ^ 2))⁻¹ : ℝ) : ℂ) := by
    rw [hexponent, ← Complex.ofReal_cpow hqpos.le (-(1 / 2 : ℝ)),
      Real.rpow_neg hqpos.le, ← Real.sqrt_eq_rpow]
  have hbase : (1 - (r : ℂ) ^ 2) = ((1 - r ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  unfold complexHermiteBilinearClosed hermiteBilinearClosed
  push_cast
  rw [hbase, hcpow]
  push_cast
  rfl

/-- Complex Mehler formula on the open unit disc, obtained from the real
formula by analytic continuation. -/
theorem complexHermiteBilinearSeries_eq_closed
    {z : ℂ} (hz : ‖z‖ < 1) (x y : ℝ) :
    complexHermiteBilinearSeries x y z =
      complexHermiteBilinearClosed x y z := by
  let q : ℂ := (1 / 2 : ℂ)
  let u : ℕ → ℂ := fun n ↦ q ^ (n + 1)
  have hqnorm : ‖q‖ < 1 := by
    norm_num [q]
  have hu_mem : ∀ n : ℕ,
      u n ∈ {w | complexHermiteBilinearSeries x y w =
        complexHermiteBilinearClosed x y w} \ {0} := by
    intro n
    have hqpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 1) := by positivity
    have hqreal : |(1 / 2 : ℝ) ^ (n + 1)| < 1 := by
      rw [abs_of_pos hqpos]
      exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)
    have hu_eq : u n = (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) := by
      dsimp [u, q]
      push_cast
      rfl
    rw [hu_eq]
    constructor
    · change complexHermiteBilinearSeries x y
          (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) = _
      rw [complexHermiteBilinearSeries_ofReal,
        hermiteBilinearSeries_eq_closed hqreal,
        complexHermiteBilinearClosed_ofReal hqreal]
    · simp only [Set.mem_singleton_iff]
      change (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) ≠ 0
      exact_mod_cast hqpos.ne'
  have hu_tendsto : Filter.Tendsto u Filter.atTop (nhds 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hqnorm
    simpa only [u, pow_succ, zero_mul] using hpow.mul_const q
  have hclosure : (0 : ℂ) ∈ closure
      ({w | complexHermiteBilinearSeries x y w =
        complexHermiteBilinearClosed x y w} \ {0}) := by
    exact (mem_closure_iff_seq_limit.mpr ⟨u, hu_mem, hu_tendsto⟩)
  have heq :=
    (analyticOnNhd_complexHermiteBilinearSeries x y).eqOn_of_preconnected_of_mem_closure
      (analyticOnNhd_complexHermiteBilinearClosed x y)
      (convex_ball (0 : ℂ) 1).isPreconnected
      (by simp) hclosure
  exact heq (by simpa using hz)

end

end MeyerGeneralProblem
