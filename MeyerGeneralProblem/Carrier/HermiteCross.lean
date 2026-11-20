module

public import MeyerGeneralProblem.Carrier.HermiteSynthesis
public import MeyerGeneralProblem.Hermite.ComplexMehlerFormula

@[expose] public section

/-!
# Genuine Hermite physical/Fourier cross kernel

This module gives the concrete raw physical/Fourier cross matrix an exact
spectral kernel.  The `n`th negative-scale resolvent term acquires precisely
the Hermite Fourier eigenvalue `(-i)^n`; diagonal normalization is then
performed with the genuine point-mass norms.

This is the non-asymptotic kernel to which the later all-ratio cross-Mehler
expansion and compact-remainder estimates apply.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- The exact phase-weighted spectral term in the physical/Fourier Hermite
cross kernel. -/
def hermiteCrossResolventTerm (m : ℕ) (x y : ℝ) (n : ℕ) : ℂ :=
  hermiteFourierPhase n * hermiteResolventTerm m x y n

/-- The unnormalized physical/Fourier resolvent kernel on the negative
Hermite scale. -/
def hermiteCrossResolventKernel (m : ℕ) (x y : ℝ) : ℂ :=
  ∑' n : ℕ, hermiteCrossResolventTerm m x y n

/-- The phase-weighted Mehler heat term appearing in the cross resolvent's
Laplace representation. -/
def hermiteCrossHeatTerm (t x y : ℝ) (n : ℕ) : ℂ :=
  hermiteFourierPhase n *
    hermiteMehlerTerm (Real.exp (-t)) x y n

/-- The genuine phase-weighted Mehler heat kernel. -/
def hermiteCrossHeatKernel (t x y : ℝ) : ℂ :=
  ∑' n : ℕ, hermiteCrossHeatTerm t x y n

theorem summable_hermiteCrossHeatTerm
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (hermiteCrossHeatTerm t x y) := by
  apply Summable.of_norm
  simpa only [hermiteCrossHeatTerm, norm_mul,
    norm_hermiteFourierPhase, one_mul] using
    (summable_hermiteHeatKernel_term ht x y).norm

/-- The phase-weighted heat kernel is the complex bilinear Hermite series at
the Fourier-rotated heat parameter. -/
theorem hermiteCrossHeatKernel_eq_bilinearSeries
    (t X Y : ℝ) :
    hermiteCrossHeatKernel t X Y =
      ((Real.sqrt 2 * Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) : ℝ) : ℂ) *
        complexHermiteBilinearSeries
          (2 * Real.sqrt Real.pi * X)
          (2 * Real.sqrt Real.pi * Y)
          (-Complex.I * (Real.exp (-t) : ℂ)) := by
  rw [hermiteCrossHeatKernel]
  calc
    (∑' n : ℕ, hermiteCrossHeatTerm t X Y n) =
        ∑' n : ℕ,
          ((Real.sqrt 2 * Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) : ℝ) : ℂ) *
            ((hermiteBilinearCoeff
              (2 * Real.sqrt Real.pi * X)
              (2 * Real.sqrt Real.pi * Y) n : ℝ) : ℂ) *
              (-Complex.I * (Real.exp (-t) : ℂ)) ^ n := by
      apply tsum_congr
      intro n
      rw [hermiteCrossHeatTerm, hermiteMehlerTerm,
        hermiteFourierPhase,
        show ((Real.exp (-t) ^ n : ℝ) : ℂ) *
              starRingEnd ℂ (normalizedHermiteSchwartz n X) *
              normalizedHermiteSchwartz n Y =
            ((Real.exp (-t) ^ n : ℝ) : ℂ) *
              (starRingEnd ℂ (normalizedHermiteSchwartz n X) *
                normalizedHermiteSchwartz n Y) by ring,
        star_normalizedHermiteSchwartz_mul_eq_bilinearCoeff]
      push_cast
      rw [mul_pow]
      ring
    _ = ((Real.sqrt 2 * Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) : ℝ) : ℂ) *
        ∑' n : ℕ,
          ((hermiteBilinearCoeff
            (2 * Real.sqrt Real.pi * X)
            (2 * Real.sqrt Real.pi * Y) n : ℝ) : ℂ) *
            (-Complex.I * (Real.exp (-t) : ℂ)) ^ n := by
      calc
        (∑' n : ℕ,
            ((Real.sqrt 2 * Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) : ℝ) : ℂ) *
              ((hermiteBilinearCoeff
                (2 * Real.sqrt Real.pi * X)
                (2 * Real.sqrt Real.pi * Y) n : ℝ) : ℂ) *
                (-Complex.I * (Real.exp (-t) : ℂ)) ^ n) =
            ∑' n : ℕ,
              ((Real.sqrt 2 * Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) : ℝ) : ℂ) *
                (((hermiteBilinearCoeff
                  (2 * Real.sqrt Real.pi * X)
                  (2 * Real.sqrt Real.pi * Y) n : ℝ) : ℂ) *
                  (-Complex.I * (Real.exp (-t) : ℂ)) ^ n) := by
              apply tsum_congr
              intro n
              ring
        _ = _ := tsum_mul_left
    _ = _ := by
      rw [complexHermiteBilinearSeries_eq_tsum]

/-- The phase-weighted heat kernel is the complex closed Mehler expression
at the Fourier-rotated heat parameter. -/
theorem hermiteCrossHeatKernel_eq_complexClosed
    {t : ℝ} (ht : 0 < t) (X Y : ℝ) :
    hermiteCrossHeatKernel t X Y =
      ((Real.sqrt 2 * Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) : ℝ) : ℂ) *
        complexHermiteBilinearClosed
          (2 * Real.sqrt Real.pi * X)
          (2 * Real.sqrt Real.pi * Y)
          (-Complex.I * (Real.exp (-t) : ℂ)) := by
  rw [hermiteCrossHeatKernel_eq_bilinearSeries]
  congr 1
  apply complexHermiteBilinearSeries_eq_closed
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [Real.exp_lt_one_iff]
  linarith

/-- Closed complex Gaussian for the phase-weighted Mehler kernel. -/
def normalizedHermiteCrossMehlerClosed (r X Y : ℝ) : ℂ :=
  ((Real.sqrt 2 / Real.sqrt (1 + r ^ 2) : ℝ) : ℂ) *
    Complex.exp
      (-Real.pi * ((1 - r ^ 2) / (1 + r ^ 2)) * (X ^ 2 + Y ^ 2) -
        4 * Real.pi * Complex.I * r * X * Y / (1 + r ^ 2))

/-- Multiplying the complex bilinear Mehler formula by the normalized
Hermite Gaussian gives the closed cross-Mehler Gaussian. -/
theorem common_mul_complexHermiteBilinearClosed_eq_crossClosed
    (r X Y : ℝ) :
    ((Real.sqrt 2 * Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) : ℝ) : ℂ) *
        complexHermiteBilinearClosed
          (2 * Real.sqrt Real.pi * X)
          (2 * Real.sqrt Real.pi * Y)
          (-Complex.I * (r : ℂ)) =
      normalizedHermiteCrossMehlerClosed r X Y := by
  have hqpos : 0 < 1 + r ^ 2 := by positivity
  have hqne : (1 + (r : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast hqpos.ne'
  have hbase : 1 - (-Complex.I * (r : ℂ)) ^ 2 =
      ((1 + r ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> norm_num [pow_two]
  have hexponent : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by
    norm_num
  have hcpow : (((1 + r ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) =
      (((Real.sqrt (1 + r ^ 2))⁻¹ : ℝ) : ℂ) := by
    rw [hexponent, ← Complex.ofReal_cpow hqpos.le (-(1 / 2 : ℝ)),
      Real.rpow_neg hqpos.le, ← Real.sqrt_eq_rpow]
  have hsqrtpi : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  have hsqrtpiC : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 =
      (Real.pi : ℂ) := by
    exact_mod_cast hsqrtpi
  let A : ℂ := -Real.pi * (X ^ 2 + Y ^ 2)
  let B : ℂ :=
    (2 * (-Complex.I * (r : ℂ)) *
          (2 * Real.sqrt Real.pi * X) *
          (2 * Real.sqrt Real.pi * Y) -
        (-Complex.I * (r : ℂ)) ^ 2 *
          ((2 * Real.sqrt Real.pi * X) ^ 2 +
            (2 * Real.sqrt Real.pi * Y) ^ 2)) /
      (2 * (1 + r ^ 2))
  let C : ℂ :=
    -Real.pi * ((1 - r ^ 2) / (1 + r ^ 2)) * (X ^ 2 + Y ^ 2) -
      4 * Real.pi * Complex.I * r * X * Y / (1 + r ^ 2)
  have hphase : (-Complex.I * (r : ℂ)) ^ 2 = -(r : ℂ) ^ 2 := by
    rw [mul_pow, neg_sq, Complex.I_sq, neg_one_mul]
  have hABC : A + B = C := by
    dsimp [A, B, C]
    rw [hphase]
    field_simp [hqne]
    rw [hsqrtpiC]
    ring
  unfold complexHermiteBilinearClosed normalizedHermiteCrossMehlerClosed
  rw [hbase, hcpow]
  push_cast
  change (Real.sqrt 2 : ℂ) * Complex.exp A *
      (((Real.sqrt (1 + r ^ 2) : ℝ) : ℂ)⁻¹ * Complex.exp B) =
    ((Real.sqrt 2 : ℝ) : ℂ) /
      ((Real.sqrt (1 + r ^ 2) : ℝ) : ℂ) * Complex.exp C
  calc
    (Real.sqrt 2 : ℂ) * Complex.exp A *
          (((Real.sqrt (1 + r ^ 2) : ℝ) : ℂ)⁻¹ * Complex.exp B) =
        ((Real.sqrt 2 : ℝ) : ℂ) /
          ((Real.sqrt (1 + r ^ 2) : ℝ) : ℂ) *
            (Complex.exp A * Complex.exp B) := by
      rw [div_eq_mul_inv]
      ring
    _ = ((Real.sqrt 2 : ℝ) : ℂ) /
          ((Real.sqrt (1 + r ^ 2) : ℝ) : ℂ) *
            Complex.exp (A + B) := by rw [Complex.exp_add]
    _ = _ := by rw [hABC]

/-- Closed complex Gaussian formula for the genuine phase-weighted Hermite
heat kernel. -/
theorem hermiteCrossHeatKernel_eq_closed
    {t : ℝ} (ht : 0 < t) (X Y : ℝ) :
    hermiteCrossHeatKernel t X Y =
      normalizedHermiteCrossMehlerClosed (Real.exp (-t)) X Y := by
  rw [hermiteCrossHeatKernel_eq_complexClosed ht]
  exact common_mul_complexHermiteBilinearClosed_eq_crossClosed
    (Real.exp (-t)) X Y

/-- The phase-weighted resolvent kernel is exactly the inner product of a
genuine Hermite point mass with the Hermite Fourier transform of another. -/
theorem inner_hermitePointMass_hermiteFourier_eq_crossResolventKernel
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    inner ℂ (hermitePointMass m hm x)
        (hermiteFourier (-(m : ℤ)) (hermitePointMass m hm y)) =
      hermiteCrossResolventKernel m x y := by
  rw [lp.inner_eq_tsum, hermiteCrossResolventKernel]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply, hermiteFourier_apply,
    hermitePointMass_apply, hermiteCrossResolventTerm]
  rw [← star_hermiteDiracCoefficients_mul_eq_resolventTerm m x y n]
  ring

/-- Phase-weighted termwise Laplace integrand for the cross resolvent. -/
def hermiteCrossResolventLaplaceTerm
    (m : ℕ) (x y : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  hermiteFourierPhase n *
    hermiteResolventLaplaceTerm m x y n t

theorem integrableOn_hermiteCrossResolventLaplaceTerm
    (m : ℕ) (x y : ℝ) (n : ℕ) :
    MeasureTheory.IntegrableOn
      (hermiteCrossResolventLaplaceTerm m x y n) (Set.Ioi 0) := by
  exact (integrableOn_hermiteResolventLaplaceTerm m x y n).const_mul _

theorem integral_hermiteCrossResolventLaplaceTerm
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) (n : ℕ) :
    ∫ t : ℝ in Set.Ioi 0,
        hermiteCrossResolventLaplaceTerm m x y n t =
      (((2 * m - 1).factorial : ℝ) : ℂ) *
        hermiteCrossResolventTerm m x y n := by
  change (∫ t : ℝ in Set.Ioi 0,
    hermiteFourierPhase n * hermiteResolventLaplaceTerm m x y n t) = _
  rw [MeasureTheory.integral_const_mul,
    integral_hermiteResolventLaplaceTerm m hm]
  unfold hermiteCrossResolventTerm
  ring

theorem integral_norm_hermiteCrossResolventLaplaceTerm
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) (n : ℕ) :
    ∫ t : ℝ in Set.Ioi 0,
        ‖hermiteCrossResolventLaplaceTerm m x y n t‖ =
      ((2 * m - 1).factorial : ℝ) *
        (((n : ℝ) + 1)⁻¹) ^ (2 * m) *
          ‖starRingEnd ℂ (normalizedHermiteSchwartz n x) *
            normalizedHermiteSchwartz n y‖ := by
  simpa only [hermiteCrossResolventLaplaceTerm, norm_mul,
    norm_hermiteFourierPhase, one_mul] using
    integral_norm_hermiteResolventLaplaceTerm m hm x y n

theorem summable_integral_norm_hermiteCrossResolventLaplaceTerm
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    Summable (fun n : ℕ ↦
      ∫ t : ℝ in Set.Ioi 0,
        ‖hermiteCrossResolventLaplaceTerm m x y n t‖) := by
  apply (summable_integral_norm_hermiteResolventLaplaceTerm m hm x y).congr
  intro n
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [hermiteCrossResolventLaplaceTerm, norm_mul,
    norm_hermiteFourierPhase, one_mul]

theorem hermiteCrossResolventLaplaceTerm_eq_crossHeatTerm
    (m : ℕ) (x y : ℝ) (n : ℕ) (t : ℝ) :
    hermiteCrossResolventLaplaceTerm m x y n t =
      (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
        hermiteCrossHeatTerm t x y n := by
  rw [hermiteCrossResolventLaplaceTerm,
    hermiteResolventLaplaceTerm_eq_mehlerTerm]
  unfold hermiteCrossHeatTerm
  ring

theorem tsum_hermiteCrossResolventLaplaceTerm_eq_crossHeatKernel
    (m : ℕ) (x y t : ℝ) :
    ∑' n : ℕ, hermiteCrossResolventLaplaceTerm m x y n t =
      (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
        hermiteCrossHeatKernel t x y := by
  simp_rw [hermiteCrossResolventLaplaceTerm_eq_crossHeatTerm]
  rw [tsum_mul_left]
  rfl

/-- Closed complex-Gaussian integrand for the cross resolvent. -/
def hermiteCrossResolventClosedIntegrand
    (m : ℕ) (X Y t : ℝ) : ℂ :=
  (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
    normalizedHermiteCrossMehlerClosed (Real.exp (-t)) X Y

/-- The phase-weighted Laplace integrand equals its closed complex-Gaussian
form at every positive heat time. -/
theorem hermiteCrossResolventLaplaceIntegrand_eq_closed
    (m : ℕ) (X Y : ℝ) {t : ℝ} (ht : 0 < t) :
    (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
        hermiteCrossHeatKernel t X Y =
      hermiteCrossResolventClosedIntegrand m X Y t := by
  rw [hermiteCrossResolventClosedIntegrand,
    hermiteCrossHeatKernel_eq_closed ht]

/-- Closed complex-Gaussian integral for the unnormalized cross resolvent. -/
def hermiteCrossClosedResolventIntegral
    (m : ℕ) (X Y : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0,
    hermiteCrossResolventClosedIntegrand m X Y t

/-- The genuine phase-weighted cross resolvent has a fully justified
Laplace/Mehler representation, including the borderline order `m = 1`. -/
theorem factorial_mul_hermiteCrossResolventKernel_eq_laplaceIntegral
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    (((2 * m - 1).factorial : ℝ) : ℂ) *
        hermiteCrossResolventKernel m x y =
      ∫ t : ℝ in Set.Ioi 0,
        (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
          hermiteCrossHeatKernel t x y := by
  have hexchange :=
    MeasureTheory.integral_tsum_of_summable_integral_norm
      (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
      (fun n ↦ integrableOn_hermiteCrossResolventLaplaceTerm m x y n)
      (summable_integral_norm_hermiteCrossResolventLaplaceTerm m hm x y)
  calc
    (((2 * m - 1).factorial : ℝ) : ℂ) *
        hermiteCrossResolventKernel m x y =
      ∑' n : ℕ, (((2 * m - 1).factorial : ℝ) : ℂ) *
        hermiteCrossResolventTerm m x y n := by
          rw [hermiteCrossResolventKernel, tsum_mul_left]
    _ = ∑' n : ℕ,
        ∫ t : ℝ in Set.Ioi 0,
          hermiteCrossResolventLaplaceTerm m x y n t := by
      apply tsum_congr
      intro n
      exact (integral_hermiteCrossResolventLaplaceTerm m hm x y n).symm
    _ = ∫ t : ℝ in Set.Ioi 0,
        ∑' n : ℕ, hermiteCrossResolventLaplaceTerm m x y n t := hexchange
    _ = ∫ t : ℝ in Set.Ioi 0,
        (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
          hermiteCrossHeatKernel t x y := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t _
      exact
        tsum_hermiteCrossResolventLaplaceTerm_eq_crossHeatKernel m x y t

/-- The justified spectral/Laplace representation is exactly the closed
complex-Gaussian cross-resolvent integral. -/
theorem factorial_mul_hermiteCrossResolventKernel_eq_closedIntegral
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    (((2 * m - 1).factorial : ℝ) : ℂ) *
        hermiteCrossResolventKernel m X Y =
      hermiteCrossClosedResolventIntegral m X Y := by
  rw [factorial_mul_hermiteCrossResolventKernel_eq_laplaceIntegral
    m hm X Y]
  unfold hermiteCrossClosedResolventIntegral
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact hermiteCrossResolventLaplaceIntegrand_eq_closed m X Y ht

/-- Conventional divided form of the phase-weighted resolvent
Laplace/Mehler representation. -/
theorem hermiteCrossResolventKernel_eq_laplaceIntegral
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    hermiteCrossResolventKernel m x y =
      ((((2 * m - 1).factorial : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ t : ℝ in Set.Ioi 0,
          (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
            hermiteCrossHeatKernel t x y := by
  have hfact : (((2 * m - 1).factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * m - 1)
  have hfact' : (((2 * m - 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * m - 1)
  have h :=
    factorial_mul_hermiteCrossResolventKernel_eq_laplaceIntegral
      m hm x y
  rw [← h]
  push_cast
  field_simp [hfact']

/-- The genuine diagonally normalized physical/Fourier Hermite cross
kernel. -/
def normalizedHermiteCrossKernel
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) : ℂ :=
  (((‖hermitePointMass m hm x‖⁻¹ *
      ‖hermitePointMass m hm y‖⁻¹ : ℝ) : ℂ) *
    hermiteCrossResolventKernel m x y)

/-- The exact normalized cross kernel as a genuine phase-weighted
Laplace/Mehler integral. -/
theorem normalizedHermiteCrossKernel_eq_laplaceIntegral
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    normalizedHermiteCrossKernel m hm x y =
      (((‖hermitePointMass m hm x‖⁻¹ *
          ‖hermitePointMass m hm y‖⁻¹ : ℝ) : ℂ) *
        ((((2 * m - 1).factorial : ℝ)⁻¹ : ℝ) : ℂ)) *
          ∫ t : ℝ in Set.Ioi 0,
            (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
              hermiteCrossHeatKernel t x y := by
  rw [normalizedHermiteCrossKernel,
    hermiteCrossResolventKernel_eq_laplaceIntegral m hm]
  ring

/-- Exact normalization identity for the genuine physical/Fourier Hermite
cross kernel. -/
theorem inner_normalizedHermitePointMass_hermiteFourier_eq_crossKernel
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    inner ℂ (normalizedHermitePointMass m hm x)
        (hermiteFourier (-(m : ℤ))
          (normalizedHermitePointMass m hm y)) =
      normalizedHermiteCrossKernel m hm x y := by
  unfold normalizedHermitePointMass normalizedHermiteCrossKernel
  rw [map_smul, inner_smul_left, inner_smul_right,
    inner_hermitePointMass_hermiteFourier_eq_crossResolventKernel]
  have hx : starRingEnd ℂ
      (((‖hermitePointMass m hm x‖⁻¹ : ℝ) : ℂ)) =
      (((‖hermitePointMass m hm x‖⁻¹ : ℝ) : ℂ)) := by
    change star (((‖hermitePointMass m hm x‖⁻¹ : ℝ) : ℂ)) = _
    apply Complex.ext <;> simp
  rw [hx]
  push_cast
  ring

/-- Every raw carrier cross entry is an evaluation of the exact genuine
normalized physical/Fourier Hermite cross kernel. -/
theorem inner_carrierHermitePointMass_hermiteFourier_eq_crossKernel
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) (i j : ℤ) :
    inner ℂ (carrierHermitePointMass m hm Λ i)
        (hermiteFourier (-(m : ℤ))
          (carrierHermitePointMass m hm Λ j)) =
      normalizedHermiteCrossKernel m hm (Λ i) (Λ j) := by
  exact
    inner_normalizedHermitePointMass_hermiteFourier_eq_crossKernel
      m hm (Λ i) (Λ j)

end

end MeyerGeneralProblem
