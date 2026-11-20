module

public import MeyerGeneralProblem.Gram.HermiteUniversalLimit
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

/-!
# Identification of the universal Fourier kernel with the Mehler limit integral

This module supplies the remaining exact Fourier/Gamma calculation in the
local Hermite-to-universal comparison.  It deliberately keeps the raw
rational-density transform and its normalization separate, so every constant
cancels at displacement zero.
-/

namespace MeyerGeneralProblem

open Filter MeasureTheory

noncomputable section

/-- Gamma/Laplace representation of the raw rational density, with the exact
integer factorial used by the Hermite resolvent. -/
theorem integral_gammaDensity_eq_factorial_mul_rawGramDensity
    (m : ℕ) (hm : 1 ≤ m) (η : ℝ) :
    (∫ v : ℝ in Set.Ioi 0,
        v ^ ((2 * m : ℕ) - 1) *
          Real.exp (-((1 + 4 * η ^ 2) * v))) =
      ((2 * m - 1).factorial : ℝ) * rawGramDensity m η := by
  have hmpos : 0 < (2 * m : ℝ) := by positivity
  have hapos : 0 < 1 + 4 * η ^ 2 := by nlinarith [sq_nonneg η]
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi hmpos hapos
  have hGamma : Real.Gamma (2 * m : ℝ) =
      ((2 * m - 1).factorial : ℝ) := by
    rw [show (2 * m : ℝ) = ((2 * m - 1 : ℕ) : ℝ) + 1 by
      norm_cast
      omega]
    exact Real.Gamma_nat_eq_factorial (2 * m - 1)
  have hweight : (1 / (1 + 4 * η ^ 2)) ^ (2 * m : ℝ) =
      rawGramDensity m η := by
    rw [show (2 * m : ℝ) = ((2 * m : ℕ) : ℝ) by norm_cast,
      Real.rpow_natCast, one_div, rawGramDensity_eq_inv_pow]
  have hcast : ((2 * m - 1 : ℕ) : ℝ) = (2 * m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    norm_num
  calc
    (∫ v : ℝ in Set.Ioi 0,
        v ^ ((2 * m : ℕ) - 1) *
          Real.exp (-((1 + 4 * η ^ 2) * v))) =
        ∫ v : ℝ in Set.Ioi 0,
          v ^ ((2 * m : ℝ) - 1) *
            Real.exp (-((1 + 4 * η ^ 2) * v)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [← hcast, Real.rpow_natCast]
    _ = (1 / (1 + 4 * η ^ 2)) ^ (2 * m : ℝ) *
        Real.Gamma (2 * m : ℝ) := hgamma
    _ = ((2 * m - 1).factorial : ℝ) * rawGramDensity m η := by
      rw [hGamma, hweight]
      ring

/-- Fourier transform of one positive Gaussian slice in the repository's
positive `2π` phase convention. -/
theorem integral_exp_neg_four_mul_sq_mul_gramPhase
    {v : ℝ} (hv : 0 < v) (δ : ℝ) :
    (∫ η : ℝ,
        ((Real.exp (-(4 * v * η ^ 2)) : ℝ) : ℂ) * gramPhase δ η) =
      ((Real.sqrt (Real.pi / (4 * v)) *
        Real.exp (-(Real.pi ^ 2 * δ ^ 2 / (4 * v))) : ℝ) : ℂ) := by
  have hb : 0 < (((4 * v : ℝ) : ℂ)).re := by
    norm_num
    positivity
  have hgauss := fourierIntegral_gaussian hb (((2 * Real.pi * δ : ℝ) : ℂ))
  have hlhs :
      (∫ η : ℝ,
          ((Real.exp (-(4 * v * η ^ 2)) : ℝ) : ℂ) * gramPhase δ η) =
        ∫ η : ℝ,
          Complex.exp (Complex.I * ((2 * Real.pi * δ : ℝ) : ℂ) * η) *
            Complex.exp (-(((4 * v : ℝ) : ℂ)) * η ^ 2) := by
    apply integral_congr_ae
    filter_upwards with η
    calc
      ((Real.exp (-(4 * v * η ^ 2)) : ℝ) : ℂ) * gramPhase δ η =
          gramPhase δ η *
            ((Real.exp (-(4 * v * η ^ 2)) : ℝ) : ℂ) := by ring
      _ = Complex.exp (Complex.I * ((2 * Real.pi * δ : ℝ) : ℂ) * η) *
          Complex.exp (-(((4 * v : ℝ) : ℂ)) * η ^ 2) := by
        rw [Complex.ofReal_exp]
        unfold gramPhase
        congr 1 <;> push_cast <;> ring
  rw [hlhs, hgauss]
  have hbase : 0 ≤ Real.pi / (4 * v) := by positivity
  have hsqrt :
      ((((Real.pi : ℂ) / ((4 * v : ℝ) : ℂ)) ^ (1 / 2 : ℂ))) =
        ((Real.sqrt (Real.pi / (4 * v)) : ℝ) : ℂ) := by
    rw [show (Real.pi : ℂ) / ((4 * v : ℝ) : ℂ) =
        ((Real.pi / (4 * v) : ℝ) : ℂ) by norm_cast,
      show (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℂ)) by norm_num,
      ← Complex.ofReal_cpow hbase, ← Real.sqrt_eq_rpow]
  have harg :
      -(((2 * Real.pi * δ : ℝ) : ℂ)) ^ 2 /
          (4 * (((4 * v : ℝ) : ℂ))) =
        ((-(Real.pi ^ 2 * δ ^ 2 / (4 * v)) : ℝ) : ℂ) := by
    push_cast
    field_simp [hv.ne']
    ring
  rw [hsqrt, harg, ← Complex.ofReal_exp]
  norm_cast

/-- The two-variable Gamma/Gaussian integrand whose two iterated integrals
produce respectively the raw rational Fourier transform and the Mehler limit
integral. -/
def rationalGammaFourierIntegrand
    (m : ℕ) (δ v η : ℝ) : ℂ :=
  ((v ^ ((2 * m : ℕ) - 1) * Real.exp (-v) *
      Real.exp (-(4 * v * η ^ 2)) : ℝ) : ℂ) * gramPhase δ η

theorem integral_norm_rationalGammaFourierIntegrand
    (m : ℕ) (δ : ℝ) {v : ℝ} (hv : 0 < v) :
    (∫ η : ℝ, ‖rationalGammaFourierIntegrand m δ v η‖) =
      v ^ ((2 * m : ℕ) - 1) * Real.exp (-v) *
        Real.sqrt (Real.pi / (4 * v)) := by
  have hconst : 0 ≤ v ^ ((2 * m : ℕ) - 1) * Real.exp (-v) :=
    mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le
  calc
    (∫ η : ℝ, ‖rationalGammaFourierIntegrand m δ v η‖) =
        ∫ η : ℝ,
          (v ^ ((2 * m : ℕ) - 1) * Real.exp (-v)) *
            Real.exp (-(4 * v * η ^ 2)) := by
      apply integral_congr_ae
      filter_upwards with η
      unfold rationalGammaFourierIntegrand
      rw [norm_mul, norm_gramPhase, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg hconst (Real.exp_pos _).le
    _ = (v ^ ((2 * m : ℕ) - 1) * Real.exp (-v)) *
        ∫ η : ℝ, Real.exp (-(4 * v * η ^ 2)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = v ^ ((2 * m : ℕ) - 1) * Real.exp (-v) *
        Real.sqrt (Real.pi / (4 * v)) := by
      have hgauss :
          (∫ η : ℝ, Real.exp (-(4 * v * η ^ 2))) =
            Real.sqrt (Real.pi / (4 * v)) := by
        rw [← integral_gaussian (4 * v)]
        apply integral_congr_ae
        filter_upwards with η
        congr 1
        ring
      rw [hgauss]

theorem integrableOn_integral_norm_rationalGammaFourierIntegrand
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) :
    MeasureTheory.IntegrableOn
      (fun v : ℝ => ∫ η : ℝ,
        ‖rationalGammaFourierIntegrand m δ v η‖) (Set.Ioi 0) := by
  let C : ℝ := Real.sqrt Real.pi / 2
  have hs : (-1 : ℝ) < 2 * (m : ℝ) - 3 / 2 := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have href := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := 2 * (m : ℝ) - 3 / 2)
    (b := (1 : ℝ)) hs zero_lt_one zero_lt_one
  have href' : MeasureTheory.IntegrableOn
      (fun v : ℝ => C *
        (v ^ (2 * (m : ℝ) - 3 / 2) * Real.exp (-v)))
      (Set.Ioi 0) := by
    change MeasureTheory.Integrable
      (fun v : ℝ => C *
        (v ^ (2 * (m : ℝ) - 3 / 2) * Real.exp (-v)))
      (MeasureTheory.volume.restrict (Set.Ioi 0))
    convert href.const_mul C using 1
    ext v
    rw [Real.rpow_one]
    congr 3
    ring
  refine href'.congr_fun ?_ measurableSet_Ioi
  intro v hv
  change C * (v ^ (2 * (m : ℝ) - 3 / 2) * Real.exp (-v)) =
    ∫ η : ℝ, ‖rationalGammaFourierIntegrand m δ v η‖
  rw [integral_norm_rationalGammaFourierIntegrand m δ hv]
  have hsqrt : Real.sqrt (Real.pi / (4 * v)) =
      C * (1 / Real.sqrt v) := by
    dsimp only [C]
    have hsqrtFour : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    rw [Real.sqrt_div Real.pi_pos.le,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrtFour]
    field_simp [Real.sqrt_ne_zero'.mpr hv]
  have hpow :
      v ^ ((2 * m : ℕ) - 1) * (1 / Real.sqrt v) =
        v ^ (2 * (m : ℝ) - 3 / 2) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hv.le,
      ← Real.rpow_natCast, ← Real.rpow_add hv]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    norm_num
    ring
  rw [hsqrt]
  dsimp only [C]
  rw [← hpow]
  ring

theorem integrable_rationalGammaFourierIntegrand
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) :
    MeasureTheory.Integrable
      (Function.uncurry (rationalGammaFourierIntegrand m δ))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        MeasureTheory.volume) := by
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (rationalGammaFourierIntegrand m δ))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        MeasureTheory.volume) := by
    apply Continuous.aestronglyMeasurable
    unfold rationalGammaFourierIntegrand gramPhase
    fun_prop
  apply (MeasureTheory.integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ioi] with v hv
    have hv' : 0 < v := hv
    have hgauss : MeasureTheory.Integrable
        (fun η : ℝ =>
          ((Real.exp (-(4 * v * η ^ 2)) : ℝ) : ℂ) * gramPhase δ η) := by
      have hbase : MeasureTheory.Integrable
          (fun η : ℝ =>
            ((Real.exp (-(4 * v) * η ^ 2) : ℝ) : ℂ) * gramPhase δ η) := by
        apply (integrable_exp_neg_mul_sq
          (b := 4 * v) (mul_pos (by norm_num) hv')).ofReal.mul_bdd
        · apply Continuous.aestronglyMeasurable
          unfold gramPhase
          fun_prop
        · exact Filter.Eventually.of_forall (fun η => by
            rw [norm_gramPhase])
      apply hbase.congr
      filter_upwards with η
      congr 2
      ring
    have hconst := hgauss.const_mul
      ((v ^ ((2 * m : ℕ) - 1) * Real.exp (-v) : ℝ) : ℂ)
    apply hconst.congr
    filter_upwards with η
    change
      (((v ^ ((2 * m : ℕ) - 1) * Real.exp (-v) : ℝ) : ℂ) *
          (((Real.exp (-(4 * v * η ^ 2)) : ℝ) : ℂ) * gramPhase δ η)) =
        rationalGammaFourierIntegrand m δ v η
    unfold rationalGammaFourierIntegrand
    push_cast
    ring
  · exact integrableOn_integral_norm_rationalGammaFourierIntegrand m hm δ

/-- Integrating the auxiliary two-variable kernel first in frequency gives
the Gaussian slice that will become the Mehler limit integral. -/
theorem integral_rationalGammaFourierIntegrand_eta
    (m : ℕ) (δ : ℝ) {v : ℝ} (hv : 0 < v) :
    (∫ η : ℝ, rationalGammaFourierIntegrand m δ v η) =
      ((v ^ ((2 * m : ℕ) - 1) * Real.exp (-v) *
        Real.sqrt (Real.pi / (4 * v)) *
        Real.exp (-(Real.pi ^ 2 * δ ^ 2 / (4 * v))) : ℝ) : ℂ) := by
  let A : ℝ := v ^ ((2 * m : ℕ) - 1) * Real.exp (-v)
  calc
    (∫ η : ℝ, rationalGammaFourierIntegrand m δ v η) =
        ∫ η : ℝ, (A : ℂ) *
          (((Real.exp (-(4 * v * η ^ 2)) : ℝ) : ℂ) *
            gramPhase δ η) := by
      apply integral_congr_ae
      filter_upwards with η
      unfold rationalGammaFourierIntegrand A
      push_cast
      ring
    _ = (A : ℂ) * ∫ η : ℝ,
          ((Real.exp (-(4 * v * η ^ 2)) : ℝ) : ℂ) *
            gramPhase δ η := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := by
      rw [integral_exp_neg_four_mul_sq_mul_gramPhase hv δ]
      unfold A
      push_cast
      ring

/-- Integrating the auxiliary kernel first in the Gamma variable recovers the
raw rational density with its exact factorial. -/
theorem integral_rationalGammaFourierIntegrand_v
    (m : ℕ) (hm : 1 ≤ m) (δ η : ℝ) :
    (∫ v : ℝ in Set.Ioi 0,
        rationalGammaFourierIntegrand m δ v η) =
      (((2 * m - 1).factorial : ℂ) *
        (rawGramDensity m η : ℂ)) * gramPhase δ η := by
  have hreal := integral_gammaDensity_eq_factorial_mul_rawGramDensity m hm η
  calc
    (∫ v : ℝ in Set.Ioi 0,
        rationalGammaFourierIntegrand m δ v η) =
        (∫ v : ℝ in Set.Ioi 0,
          ((v ^ ((2 * m : ℕ) - 1) *
            Real.exp (-((1 + 4 * η ^ 2) * v)) : ℝ) : ℂ)) *
            gramPhase δ η := by
      rw [← MeasureTheory.integral_mul_const]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      unfold rationalGammaFourierIntegrand
      change
        ((v ^ ((2 * m : ℕ) - 1) * Real.exp (-v) *
          Real.exp (-(4 * v * η ^ 2)) : ℝ) : ℂ) * gramPhase δ η =
        ((v ^ ((2 * m : ℕ) - 1) *
          Real.exp (-((1 + 4 * η ^ 2) * v)) : ℝ) : ℂ) * gramPhase δ η
      have hexp : Real.exp (-v) * Real.exp (-(4 * v * η ^ 2)) =
          Real.exp (-((1 + 4 * η ^ 2) * v)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      congr 1
      norm_cast
      rw [mul_assoc, hexp]
    _ = (((2 * m - 1).factorial : ℂ) *
        (rawGramDensity m η : ℂ)) * gramPhase δ η := by
      rw [integral_complex_ofReal, hreal]
      push_cast
      ring

/-- Fubini identity equating the Gamma-first and Fourier-first evaluations. -/
theorem integral_integral_rationalGammaFourierIntegrand_swap
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) :
    (∫ v : ℝ in Set.Ioi 0,
        ∫ η : ℝ, rationalGammaFourierIntegrand m δ v η) =
      ∫ η : ℝ,
        ∫ v : ℝ in Set.Ioi 0,
          rationalGammaFourierIntegrand m δ v η := by
  exact MeasureTheory.integral_integral_swap
    (integrable_rationalGammaFourierIntegrand m hm δ)

/-- Real Gaussian slice obtained after the frequency integral. -/
def gammaGaussianSlice (m : ℕ) (δ v : ℝ) : ℝ :=
  v ^ ((2 * m : ℕ) - 1) * Real.exp (-v) *
    Real.sqrt (Real.pi / (4 * v)) *
    Real.exp (-(Real.pi ^ 2 * δ ^ 2 / (4 * v)))

/-- Pointwise form of the exact substitution `v = πu/4`. -/
theorem gammaGaussianSlice_pi_div_four_mul
    (m : ℕ) (δ : ℝ) {u : ℝ} (hu : 0 < u) :
    gammaGaussianSlice m δ ((Real.pi / 4) * u) =
      (Real.pi / 4) ^ ((2 * m : ℕ) - 1) *
        mehlerUniversalLimitIntegrand m δ u := by
  let b : ℝ := Real.pi / 4
  have hb : 0 < b := by dsimp only [b]; positivity
  have hsqrt : Real.sqrt (Real.pi / (4 * (b * u))) =
      1 / Real.sqrt u := by
    have hquot : Real.pi / (4 * (b * u)) = 1 / u := by
      dsimp only [b]
      field_simp [Real.pi_ne_zero, hu.ne']
    rw [hquot, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
      Real.sqrt_one]
  have hexp :
      Real.exp (-(b * u)) *
          Real.exp (-(Real.pi ^ 2 * δ ^ 2 / (4 * (b * u)))) =
        Real.exp (-Real.pi * (u / 4 + (1 / u) * δ ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [b]
    field_simp [Real.pi_ne_zero, hu.ne']
    ring
  change gammaGaussianSlice m δ (b * u) = _
  unfold gammaGaussianSlice mehlerUniversalLimitIntegrand
  rw [mul_pow, hsqrt]
  calc
    (b ^ ((2 * m : ℕ) - 1) * u ^ ((2 * m : ℕ) - 1) *
          Real.exp (-(b * u)) * (1 / Real.sqrt u) *
          Real.exp (-(Real.pi ^ 2 * δ ^ 2 / (4 * (b * u))))) =
        b ^ ((2 * m : ℕ) - 1) *
          (u ^ ((2 * m : ℕ) - 1) * (1 / Real.sqrt u) *
            (Real.exp (-(b * u)) *
              Real.exp (-(Real.pi ^ 2 * δ ^ 2 / (4 * (b * u)))))) := by
      ring
    _ = _ := by rw [hexp]

/-- The Fourier-first iterated integral is exactly `(π/4)^(2m)` times the
Mehler universal limit integral. -/
theorem integral_gammaGaussianSlice_eq_limitIntegral
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) :
    (∫ v : ℝ in Set.Ioi 0, gammaGaussianSlice m δ v) =
      (Real.pi / 4) ^ (2 * m) * hermiteUniversalLimitIntegral m δ := by
  let b : ℝ := Real.pi / 4
  have hb : 0 < b := by dsimp only [b]; positivity
  have hchange := MeasureTheory.integral_comp_mul_left_Ioi'
    (gammaGaussianSlice m δ) 0 hb
  calc
    (∫ v : ℝ in Set.Ioi 0, gammaGaussianSlice m δ v) =
        b * ∫ u : ℝ in Set.Ioi 0,
          gammaGaussianSlice m δ (b * u) := by
      simpa only [smul_eq_mul, mul_zero] using hchange.symm
    _ = b * ∫ u : ℝ in Set.Ioi 0,
          b ^ ((2 * m : ℕ) - 1) *
            mehlerUniversalLimitIntegrand m δ u := by
      congr 1
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      simpa only [b] using
        gammaGaussianSlice_pi_div_four_mul m δ hu
    _ = b * (b ^ ((2 * m : ℕ) - 1) *
          hermiteUniversalLimitIntegral m δ) := by
      rw [MeasureTheory.integral_const_mul]
      rfl
    _ = (Real.pi / 4) ^ (2 * m) *
          hermiteUniversalLimitIntegral m δ := by
      dsimp only [b]
      rw [← mul_assoc, ← pow_succ']
      congr 2
      omega

/-- Positive-phase raw Fourier integral, before division by its value at zero. -/
def rawGramFourierIntegral (m : ℕ) (δ : ℝ) : ℂ :=
  ∫ η : ℝ, (rawGramDensity m η : ℂ) * gramPhase δ η

/-- Exact Gamma/Gaussian evaluation of the raw Fourier integral.  The common
factor on the right will cancel against the identity at displacement zero. -/
theorem factorial_mul_rawGramFourierIntegral_eq_limitIntegral
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) :
    (((2 * m - 1).factorial : ℂ) * rawGramFourierIntegral m δ) =
      (((Real.pi / 4) ^ (2 * m) *
        hermiteUniversalLimitIntegral m δ : ℝ) : ℂ) := by
  have hswap := integral_integral_rationalGammaFourierIntegrand_swap m hm δ
  have hleft :
      (∫ v : ℝ in Set.Ioi 0,
          ∫ η : ℝ, rationalGammaFourierIntegrand m δ v η) =
        (((Real.pi / 4) ^ (2 * m) *
          hermiteUniversalLimitIntegral m δ : ℝ) : ℂ) := by
    calc
      (∫ v : ℝ in Set.Ioi 0,
          ∫ η : ℝ, rationalGammaFourierIntegrand m δ v η) =
          ∫ v : ℝ in Set.Ioi 0,
            (gammaGaussianSlice m δ v : ℂ) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro v hv
        simpa only [gammaGaussianSlice] using
          integral_rationalGammaFourierIntegrand_eta m δ hv
      _ = ((∫ v : ℝ in Set.Ioi 0,
          gammaGaussianSlice m δ v : ℝ) : ℂ) := by
        rw [integral_complex_ofReal]
      _ = _ := by rw [integral_gammaGaussianSlice_eq_limitIntegral m hm δ]
  have hright :
      (∫ η : ℝ,
          ∫ v : ℝ in Set.Ioi 0,
            rationalGammaFourierIntegrand m δ v η) =
        ((2 * m - 1).factorial : ℂ) * rawGramFourierIntegral m δ := by
    calc
      (∫ η : ℝ,
          ∫ v : ℝ in Set.Ioi 0,
            rationalGammaFourierIntegrand m δ v η) =
          ∫ η : ℝ,
            (((2 * m - 1).factorial : ℂ) *
              (rawGramDensity m η : ℂ)) * gramPhase δ η := by
        apply integral_congr_ae
        filter_upwards with η
        exact integral_rationalGammaFourierIntegrand_v m hm δ η
      _ = ((2 * m - 1).factorial : ℂ) *
          ∫ η : ℝ, (rawGramDensity m η : ℂ) * gramPhase δ η := by
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards with η
        ring
      _ = _ := rfl
  calc
    ((2 * m - 1).factorial : ℂ) * rawGramFourierIntegral m δ =
        ∫ η : ℝ,
          ∫ v : ℝ in Set.Ioi 0,
            rationalGammaFourierIntegrand m δ v η := hright.symm
    _ = ∫ v : ℝ in Set.Ioi 0,
          ∫ η : ℝ, rationalGammaFourierIntegrand m δ v η := hswap.symm
    _ = _ := hleft

@[simp]
theorem rawGramFourierIntegral_zero (m : ℕ) :
    rawGramFourierIntegral m 0 = (rawGramMass m : ℂ) := by
  unfold rawGramFourierIntegral rawGramMass
  simp only [gramPhase_zero_left, mul_one, integral_complex_ofReal]

/-- The normalized universal kernel is the raw positive-phase transform
divided by its total mass. -/
theorem universalGramKernel_eq_rawGramFourierIntegral_div_mass
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) :
    universalGramKernel m δ =
      rawGramFourierIntegral m δ / (rawGramMass m : ℂ) := by
  have hmass : (rawGramMass m : ℂ) ≠ 0 := by
    exact_mod_cast (rawGramMass_pos hm).ne'
  calc
    universalGramKernel m δ =
        ∫ η : ℝ,
          ((2 * gramNormalization m : ℝ) : ℂ) *
            ((rawGramDensity m η : ℂ) * gramPhase δ η) := by
      unfold universalGramKernel gramDensity
      apply integral_congr_ae
      filter_upwards with η
      push_cast
      ring
    _ = ((2 * gramNormalization m : ℝ) : ℂ) *
        rawGramFourierIntegral m δ := by
      rw [MeasureTheory.integral_const_mul]
      rfl
    _ = rawGramFourierIntegral m δ / (rawGramMass m : ℂ) := by
      unfold gramNormalization
      push_cast
      field_simp

/-- Exact identification required by the Hermite scaling limit: the
repository's universal Fourier kernel is the normalized Mehler limit
integral. -/
theorem universalGramKernel_eq_limitIntegral_ratio
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) :
    universalGramKernel m δ =
      ((hermiteUniversalLimitIntegral m δ /
        hermiteUniversalLimitIntegral m 0 : ℝ) : ℂ) := by
  rw [universalGramKernel_eq_rawGramFourierIntegral_div_mass m hm δ]
  push_cast
  have hmass : (rawGramMass m : ℂ) ≠ 0 := by
    exact_mod_cast (rawGramMass_pos hm).ne'
  have hJzero : (hermiteUniversalLimitIntegral m 0 : ℂ) ≠ 0 := by
    exact_mod_cast (hermiteUniversalLimitIntegral_zero_pos m hm).ne'
  rw [div_eq_div_iff hmass hJzero]
  let F : ℂ := ((2 * m - 1).factorial : ℂ)
  let B : ℂ := (((Real.pi / 4) ^ (2 * m) : ℝ) : ℂ)
  have hF : F ≠ 0 := by
    dsimp only [F]
    exact_mod_cast (Nat.factorial_ne_zero (2 * m - 1))
  have hδ : F * rawGramFourierIntegral m δ =
      B * (hermiteUniversalLimitIntegral m δ : ℂ) := by
    simpa only [F, B, Complex.ofReal_mul] using
      factorial_mul_rawGramFourierIntegral_eq_limitIntegral m hm δ
  have hzero : F * (rawGramMass m : ℂ) =
      B * (hermiteUniversalLimitIntegral m 0 : ℂ) := by
    simpa only [F, B, rawGramFourierIntegral_zero, Complex.ofReal_mul] using
      factorial_mul_rawGramFourierIntegral_eq_limitIntegral m hm 0
  calc
    rawGramFourierIntegral m δ *
        (hermiteUniversalLimitIntegral m 0 : ℂ) =
        (F * rawGramFourierIntegral m δ *
          (hermiteUniversalLimitIntegral m 0 : ℂ)) / F := by
      field_simp

    _ = (B * (hermiteUniversalLimitIntegral m δ : ℂ) *
          (hermiteUniversalLimitIntegral m 0 : ℂ)) / F := by rw [hδ]
    _ = ((hermiteUniversalLimitIntegral m δ : ℂ) *
          (B * (hermiteUniversalLimitIntegral m 0 : ℂ))) / F := by ring
    _ = ((hermiteUniversalLimitIntegral m δ : ℂ) *
          (F * (rawGramMass m : ℂ))) / F := by rw [hzero]
    _ = (hermiteUniversalLimitIntegral m δ : ℂ) *
          (rawGramMass m : ℂ) := by
      field_simp

/-- Sequence-level Hermite convergence with the exact universal kernel as
the target, obtained by discharging the former integral-identification gap. -/
theorem tendsto_normalizedHermiteGramKernel_of_scaled_sequences_to_universal
    (m : ℕ) (hm : 1 ≤ m)
    {x y qxy qxx qyy : ℕ → ℝ} {δ₀ : ℝ}
    (hqxyPos : ∀ n, 0 < qxy n)
    (hqxxPos : ∀ n, 0 < qxx n)
    (hqyyPos : ∀ n, 0 < qyy n)
    (hqxyOne : ∀ᶠ n in atTop, qxy n ≤ 1)
    (hqxxOne : ∀ᶠ n in atTop, qxx n ≤ 1)
    (hqyyOne : ∀ᶠ n in atTop, qyy n ≤ 1)
    (hsame : ∀ n, 0 ≤ x n * y n)
    (hqxyScale : ∀ n, qxy n * (|x n| + |y n|) ^ 2 = 1)
    (hqxxScale : ∀ n, qxx n * (|x n| + |x n|) ^ 2 = 1)
    (hqyyScale : ∀ n, qyy n * (|y n| + |y n|) ^ 2 = 1)
    (hqxyLim : Tendsto qxy atTop (nhdsWithin 0 (Set.Ioi 0)))
    (hqxxLim : Tendsto qxx atTop (nhdsWithin 0 (Set.Ioi 0)))
    (hqyyLim : Tendsto qyy atTop (nhdsWithin 0 (Set.Ioi 0)))
    (hδ : Tendsto (fun n => signedSquare (y n) - signedSquare (x n))
      atTop (nhds δ₀))
    (hscaleRatio : Tendsto
      (fun n => hermiteResolventScale m (qxy n) /
        Real.sqrt (hermiteResolventScale m (qxx n) *
          hermiteResolventScale m (qyy n)))
      atTop (nhds 1)) :
    Tendsto (fun n => normalizedHermiteGramKernel m hm (x n) (y n))
      atTop (nhds (universalGramKernel m δ₀)) := by
  rw [universalGramKernel_eq_limitIntegral_ratio m hm δ₀]
  exact tendsto_normalizedHermiteGramKernel_of_scaled_sequences
    m hm hqxyPos hqxxPos hqyyPos hqxyOne hqxxOne hqyyOne
      hsame hqxyScale hqxxScale hqyyScale hqxyLim hqxxLim hqyyLim
      hδ hscaleRatio

end

end MeyerGeneralProblem
