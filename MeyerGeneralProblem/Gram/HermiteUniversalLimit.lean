module

public import MeyerGeneralProblem.Carrier.HermiteSynthesis
public import MeyerGeneralProblem.Gram.UniversalKernel

@[expose] public section

/-!
# Local Hermite-to-universal scaling limit

This module develops the analytic core of the same-side compact comparison.
The heat time is rescaled by the square of the sum of spatial magnitudes.  The
elementary coefficient limits below retain the exact constants needed for the
universal rational Fourier kernel.
-/

namespace MeyerGeneralProblem

open Filter

noncomputable section

/-- Slow sum-coordinate coefficient after the heat-time substitution
`t = q * u`.  It tends to `u / 4` as `q →0+`. -/
def mehlerSlowScaledRate (q u : ℝ) : ℝ :=
  (1 - Real.exp (-(u * q))) /
    (2 * q * (1 + Real.exp (-(u * q))))

/-- Fast difference-coordinate coefficient after the heat-time substitution
`t = q * u`.  It tends to `u⁻¹` as `q →0+`. -/
def mehlerFastScaledRate (q u : ℝ) : ℝ :=
  q * (1 + Real.exp (-(u * q))) /
    (2 * (1 - Real.exp (-(u * q))))

/-- Mehler square-root prefactor with the singular inverse-square-root factor
in `q` removed.  It tends to `u⁻¹ᐟ²` as `q →0+`. -/
def mehlerScaledPrefactor (q u : ℝ) : ℝ :=
  Real.sqrt (2 * q) /
    Real.sqrt (1 - Real.exp (-(u * q)) ^ 2)

/-- The elementary exponential difference quotient in the exact orientation
used by both rescaled Mehler coefficients. -/
theorem tendsto_one_sub_exp_neg_mul_div
    {u : ℝ} :
    Tendsto (fun q : ℝ => (1 - Real.exp (-(u * q))) / q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds u) := by
  have hderiv : HasDerivAt (fun q : ℝ => Real.exp (-(u * q))) (-u) 0 := by
    simpa using ((hasDerivAt_id 0).const_mul u).neg.exp
  have hslope := hderiv.tendsto_slope_zero_right
  convert hslope.neg using 1
  · ext q
    simp only [zero_add, mul_zero, neg_zero, Real.exp_zero, smul_eq_mul]
    rw [div_eq_mul_inv]
    ring
  · ring

/-- The nonsingular exponential factor under the same one-sided scaling. -/
theorem tendsto_exp_neg_mul
    {u : ℝ} :
    Tendsto (fun q : ℝ => Real.exp (-(u * q)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hq : Tendsto (fun q : ℝ => q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have harg : Tendsto (fun q : ℝ => -(u * q))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [mul_zero, neg_zero] using (hq.const_mul u).neg
  simpa only [Function.comp_def, Real.exp_zero] using
    (Real.continuous_exp.tendsto 0).comp harg

/-- Pointwise slow-coordinate scaling limit. -/
theorem tendsto_mehlerSlowScaledRate
    {u : ℝ} :
    Tendsto (fun q : ℝ => mehlerSlowScaledRate q u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (u / 4)) := by
  have hnum := tendsto_one_sub_exp_neg_mul_div (u := u)
  have hexp := tendsto_exp_neg_mul (u := u)
  have hden : Tendsto
      (fun q : ℝ => 2 * (1 + Real.exp (-(u * q))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 4) := by
    convert (tendsto_const_nhds.mul (tendsto_const_nhds.add hexp)) using 1 <;>
      norm_num
  have hquot := hnum.div hden (by norm_num : (4 : ℝ) ≠ 0)
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 : q ≠ 0 := ne_of_gt hq
  change
    ((1 - Real.exp (-(u * q))) / q) /
        (2 * (1 + Real.exp (-(u * q)))) =
      mehlerSlowScaledRate q u
  unfold mehlerSlowScaledRate
  field_simp [hq0]

/-- Pointwise fast-coordinate scaling limit. -/
theorem tendsto_mehlerFastScaledRate
    {u : ℝ} (hu : 0 < u) :
    Tendsto (fun q : ℝ => mehlerFastScaledRate q u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / u)) := by
  have hnum : Tendsto (fun q : ℝ => 1 + Real.exp (-(u * q)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := by
    convert tendsto_const_nhds.add (tendsto_exp_neg_mul (u := u)) using 1 <;>
      norm_num
  have hden : Tendsto
      (fun q : ℝ => 2 * ((1 - Real.exp (-(u * q))) / q))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * u)) :=
    tendsto_const_nhds.mul tendsto_one_sub_exp_neg_mul_div
  have hquot := hnum.div hden (mul_ne_zero two_ne_zero hu.ne')
  have hlimit : (2 : ℝ) / (2 * u) = 1 / u := by
    field_simp
  rw [hlimit] at hquot
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 : q ≠ 0 := ne_of_gt hq
  change
    (1 + Real.exp (-(u * q))) /
        (2 * ((1 - Real.exp (-(u * q))) / q)) =
      mehlerFastScaledRate q u
  unfold mehlerFastScaledRate
  field_simp [hq0]

/-- Pointwise square-root-prefactor scaling limit. -/
theorem tendsto_mehlerScaledPrefactor
    {u : ℝ} (hu : 0 < u) :
    Tendsto (fun q : ℝ => mehlerScaledPrefactor q u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / Real.sqrt u)) := by
  have hraw := tendsto_one_sub_exp_neg_mul_div (u := 2 * u)
  have hratio : Tendsto
      (fun q : ℝ => (1 - Real.exp (-((2 * u) * q))) / (2 * q))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds u) := by
    have h := hraw.div_const 2
    convert h using 1 <;> ring
  have hsqrt : Tendsto
      (fun q : ℝ => Real.sqrt
        ((1 - Real.exp (-((2 * u) * q))) / (2 * q)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt u)) := by
    simpa only [Function.comp_def] using
      (Real.continuous_sqrt.tendsto u).comp hratio
  have hinv := hsqrt.inv₀ (Real.sqrt_ne_zero'.mpr hu)
  change Tendsto (fun q : ℝ => (Real.sqrt
      ((1 - Real.exp (-((2 * u) * q))) / (2 * q)))⁻¹)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt u)⁻¹) at hinv
  simpa only [one_div] using hinv.congr' (by
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq0 : q ≠ 0 := ne_of_gt hq
    have hden : 0 < 1 - Real.exp (-(u * q)) ^ 2 := by
      have he0 := Real.exp_pos (-(u * q))
      have he1 : Real.exp (-(u * q)) < 1 := by
        rw [Real.exp_lt_one_iff]
        exact neg_lt_zero.mpr (mul_pos hu hq)
      nlinarith
    have hexpSq : Real.exp (-(u * q)) ^ 2 =
        Real.exp (-((2 * u) * q)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hden' : 0 ≤ 1 - Real.exp (-((2 * u) * q)) := by
      rw [← hexpSq]
      exact hden.le
    rw [mehlerScaledPrefactor, hexpSq, Real.sqrt_div hden']
    field_simp [Real.sqrt_ne_zero'.mpr (mul_pos two_pos hq),
      Real.sqrt_ne_zero'.mpr hden])

/-- Rescaled real Mehler/Laplace integrand.  The power and the removed
square-root singularity give the sharp common factor
`q ^ (2m - 1/2)` in the unscaled resolvent kernel. -/
def mehlerRescaledIntegrand (m : ℕ) (q δ u : ℝ) : ℝ :=
  u ^ ((2 * m : ℕ) - 1) * Real.exp (-(u * q)) *
    mehlerScaledPrefactor q u *
      Real.exp (-Real.pi *
        (mehlerSlowScaledRate q u + mehlerFastScaledRate q u * δ ^ 2))

/-- Limiting Bessel-type integrand.  Its exponent and power are the exact
ones obtained from the Mehler formula under signed-square displacement
`δ`. -/
def mehlerUniversalLimitIntegrand (m : ℕ) (δ u : ℝ) : ℝ :=
  u ^ ((2 * m : ℕ) - 1) * (1 / Real.sqrt u) *
    Real.exp (-Real.pi * (u / 4 + (1 / u) * δ ^ 2))

/-- Pointwise convergence of the complete rescaled Mehler integrand at every
positive integration point. -/
theorem tendsto_mehlerRescaledIntegrand
    (m : ℕ) (δ : ℝ) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun q : ℝ => mehlerRescaledIntegrand m q δ u)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (mehlerUniversalLimitIntegrand m δ u)) := by
  have hweight := tendsto_exp_neg_mul (u := u)
  have hpref := tendsto_mehlerScaledPrefactor hu
  have hslow := tendsto_mehlerSlowScaledRate (u := u)
  have hfast := tendsto_mehlerFastScaledRate hu
  have hpow : Tendsto (fun _q : ℝ => u ^ ((2 * m : ℕ) - 1))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (u ^ ((2 * m : ℕ) - 1))) := tendsto_const_nhds
  have hfastδ : Tendsto
      (fun q : ℝ => mehlerFastScaledRate q u * δ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1 / u) * δ ^ 2)) :=
    hfast.mul_const (δ ^ 2)
  have hrate := hslow.add hfastδ
  have hexponent : Tendsto
      (fun q : ℝ => Real.exp (-Real.pi *
        (mehlerSlowScaledRate q u + mehlerFastScaledRate q u * δ ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.exp (-Real.pi * (u / 4 + (1 / u) * δ ^ 2)))) := by
    have harg := hrate.const_mul (-Real.pi)
    simpa only [Function.comp_def] using
      (Real.continuous_exp.tendsto
        (-Real.pi * (u / 4 + (1 / u) * δ ^ 2))).comp harg
  simpa only [mehlerRescaledIntegrand, mehlerUniversalLimitIntegrand,
    Function.comp_def, one_mul, mul_one] using
    (((hpow.mul hweight).mul hpref).mul hexponent)

/-- Joint sequential version of the pointwise scaling limit, allowing the
signed-square displacement to vary while the pair scale tends to zero. -/
theorem tendsto_mehlerRescaledIntegrand_of_tendsto
    (m : ℕ) {q δ : ℕ → ℝ} {δ₀ u : ℝ} (hu : 0 < u)
    (hq : Tendsto q atTop (nhdsWithin 0 (Set.Ioi 0)))
    (hδ : Tendsto δ atTop (nhds δ₀)) :
    Tendsto (fun n => mehlerRescaledIntegrand m (q n) (δ n) u)
      atTop (nhds (mehlerUniversalLimitIntegrand m δ₀ u)) := by
  have hweight : Tendsto (fun n => Real.exp (-(u * q n))) atTop
      (nhds 1) := by
    apply ((tendsto_exp_neg_mul (u := u)).comp hq).congr'
    exact Filter.Eventually.of_forall (fun _n => rfl)
  have hpref : Tendsto (fun n => mehlerScaledPrefactor (q n) u) atTop
      (nhds (1 / Real.sqrt u)) := by
    apply ((tendsto_mehlerScaledPrefactor hu).comp hq).congr'
    exact Filter.Eventually.of_forall (fun _n => rfl)
  have hslow : Tendsto (fun n => mehlerSlowScaledRate (q n) u) atTop
      (nhds (u / 4)) := by
    apply ((tendsto_mehlerSlowScaledRate (u := u)).comp hq).congr'
    exact Filter.Eventually.of_forall (fun _n => rfl)
  have hfast : Tendsto (fun n => mehlerFastScaledRate (q n) u) atTop
      (nhds (1 / u)) := by
    apply ((tendsto_mehlerFastScaledRate hu).comp hq).congr'
    exact Filter.Eventually.of_forall (fun _n => rfl)
  have hpow : Tendsto (fun _n : ℕ => u ^ ((2 * m : ℕ) - 1)) atTop
      (nhds (u ^ ((2 * m : ℕ) - 1))) := tendsto_const_nhds
  have hδsq : Tendsto (fun n => δ n ^ 2) atTop (nhds (δ₀ ^ 2)) :=
    hδ.pow 2
  have hfastδ : Tendsto
      (fun n => mehlerFastScaledRate (q n) u * δ n ^ 2) atTop
      (nhds ((1 / u) * δ₀ ^ 2)) := hfast.mul hδsq
  have hrate := hslow.add hfastδ
  have hexponent : Tendsto
      (fun n => Real.exp (-Real.pi *
        (mehlerSlowScaledRate (q n) u +
          mehlerFastScaledRate (q n) u * δ n ^ 2))) atTop
      (nhds (Real.exp (-Real.pi * (u / 4 + (1 / u) * δ₀ ^ 2)))) := by
    have harg := hrate.const_mul (-Real.pi)
    simpa only [Function.comp_def] using
      (Real.continuous_exp.tendsto
        (-Real.pi * (u / 4 + (1 / u) * δ₀ ^ 2))).comp harg
  simpa only [mehlerRescaledIntegrand, mehlerUniversalLimitIntegrand,
    one_mul, mul_one] using
    (((hpow.mul hweight).mul hpref).mul hexponent)

/-- Exact signed-square geometry identity behind the rescaled integrand.  If
`q` is the inverse square of the sum of magnitudes, multiplying the closed
Mehler kernel by `sqrt q` produces precisely the two scaled rates above. -/
theorem sqrt_mul_normalizedHermiteMehlerClosed_eq_scaled
    {q u x y : ℝ} (hq : 0 < q) (hu : 0 < u)
    (hxy : 0 ≤ x * y)
    (hqScale : q * (|x| + |y|) ^ 2 = 1) :
    Real.sqrt q *
        normalizedHermiteMehlerClosed (Real.exp (-(u * q))) x y =
      mehlerScaledPrefactor q u *
        Real.exp (-Real.pi *
          (mehlerSlowScaledRate q u +
            mehlerFastScaledRate q u *
              (signedSquare y - signedSquare x) ^ 2)) := by
  let r := Real.exp (-(u * q))
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    dsimp only [r]
    rw [Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr (mul_pos hu hq)
  have hr : |r| < 1 := by simpa only [abs_of_pos hr0] using hr1
  have hplus : 1 + r ≠ 0 := by positivity
  have hminus : 1 - r ≠ 0 := by linarith
  have hsumSq : (x + y) ^ 2 = (|x| + |y|) ^ 2 :=
    add_sq_eq_abs_add_sq_of_mul_nonneg hxy
  have hdeltaSq : (signedSquare y - signedSquare x) ^ 2 =
      (y - x) ^ 2 * (|x| + |y|) ^ 2 :=
    signedSquare_sub_sq_eq_sub_sq_mul_abs_add_sq_of_mul_nonneg hxy
  have hslow :
      (1 - r) / (2 * (1 + r)) * (x + y) ^ 2 =
        (1 - r) / (2 * q * (1 + r)) := by
    rw [hsumSq]
    field_simp [hq.ne', hplus]
    nlinarith [hqScale]
  have hfast :
      (1 + r) / (2 * (1 - r)) * (x - y) ^ 2 =
        (q * (1 + r) / (2 * (1 - r))) *
          (signedSquare y - signedSquare x) ^ 2 := by
    rw [hdeltaSq]
    field_simp [hminus]
    have hsubSq : (x - y) ^ 2 = (y - x) ^ 2 := by ring
    rw [hsubSq]
    nlinarith [hqScale]
  have hpref :
      Real.sqrt q * Real.sqrt 2 = Real.sqrt (2 * q) := by
    rw [show 2 * q = q * 2 by ring, Real.sqrt_mul hq.le]
  rw [normalizedHermiteMehlerClosed_eq_sumDiff hr]
  change Real.sqrt q *
      (Real.sqrt 2 / Real.sqrt (1 - r ^ 2) *
        Real.exp (-Real.pi *
          ((1 - r) / (2 * (1 + r)) * (x + y) ^ 2 +
            (1 + r) / (2 * (1 - r)) * (x - y) ^ 2))) = _
  rw [hslow, hfast]
  unfold mehlerScaledPrefactor mehlerSlowScaledRate mehlerFastScaledRate
  dsimp only [r]
  rw [← hpref]
  ring

/-- Real closed-form Laplace integrand for an off-diagonal Hermite resolvent
entry. -/
def hermiteResolventClosedIntegrand
    (m : ℕ) (x y t : ℝ) : ℝ :=
  t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) *
    normalizedHermiteMehlerClosed (Real.exp (-t)) x y

/-- On positive heat time, the complex resolvent integrand is the coercion of
the real closed-form integrand. -/
theorem hermiteResolventLaplaceIntegrand_eq_closed
    (m : ℕ) (x y : ℝ) {t : ℝ} (ht : 0 < t) :
    (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
        hermiteHeatKernel t x y =
      (hermiteResolventClosedIntegrand m x y t : ℂ) := by
  rw [hermiteHeatKernel_eq_closed ht]
  norm_cast

/-- The closed real integrand is positive and hence equals the heat-kernel
norm integrand used by the existing small/large-time estimates. -/
theorem hermiteResolventClosedIntegrand_eq_heatNorm
    (m : ℕ) (x y : ℝ) {t : ℝ} (ht : 0 < t) :
    hermiteResolventClosedIntegrand m x y t =
      hermiteResolventHeatNormIntegrand m x y t := by
  have hr0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hr1 : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hpref : 0 < Real.sqrt 2 /
      Real.sqrt (1 - Real.exp (-t) ^ 2) := by
    have hden : 0 < 1 - Real.exp (-t) ^ 2 := by nlinarith
    positivity
  have hclosed : 0 ≤
      normalizedHermiteMehlerClosed (Real.exp (-t)) x y := by
    unfold normalizedHermiteMehlerClosed
    exact mul_nonneg hpref.le (Real.exp_pos _).le
  unfold hermiteResolventClosedIntegrand hermiteResolventHeatNormIntegrand
  rw [hermiteHeatKernel_eq_closed ht, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hclosed]

/-- Exact change-of-scale identity for the full Laplace integrand.  The
factor `q^(2m) / sqrt q` is independent of the displacement and therefore
cancels against the two diagonal normalizations. -/
theorem mul_hermiteResolventClosedIntegrand_scaled
    (m : ℕ) (hm : 1 ≤ m)
    {q u x y : ℝ} (hq : 0 < q) (hu : 0 < u)
    (hxy : 0 ≤ x * y)
    (hqScale : q * (|x| + |y|) ^ 2 = 1) :
    q * hermiteResolventClosedIntegrand m x y (q * u) =
      (q ^ (2 * m) / Real.sqrt q) *
        mehlerRescaledIntegrand m q
          (signedSquare y - signedSquare x) u := by
  have hclosed := sqrt_mul_normalizedHermiteMehlerClosed_eq_scaled
    hq hu hxy hqScale
  have hsqrt : Real.sqrt q ≠ 0 := Real.sqrt_ne_zero'.mpr hq
  have hheat :
      normalizedHermiteMehlerClosed (Real.exp (-(u * q))) x y =
        (Real.sqrt q)⁻¹ *
          (mehlerScaledPrefactor q u *
            Real.exp (-Real.pi *
              (mehlerSlowScaledRate q u +
                mehlerFastScaledRate q u *
                  (signedSquare y - signedSquare x) ^ 2))) := by
    calc
      normalizedHermiteMehlerClosed (Real.exp (-(u * q))) x y =
          (Real.sqrt q)⁻¹ *
            (Real.sqrt q *
              normalizedHermiteMehlerClosed (Real.exp (-(u * q))) x y) := by
        field_simp
      _ = (Real.sqrt q)⁻¹ *
          (mehlerScaledPrefactor q u *
            Real.exp (-Real.pi *
              (mehlerSlowScaledRate q u +
                mehlerFastScaledRate q u *
                  (signedSquare y - signedSquare x) ^ 2))) := by rw [hclosed]
  have hpow :
      q * (q * u) ^ ((2 * m : ℕ) - 1) =
        q ^ (2 * m) * u ^ ((2 * m : ℕ) - 1) := by
    rw [mul_pow]
    have hsucc : 2 * m = (2 * m - 1) + 1 := by omega
    calc
      q * (q ^ (2 * m - 1) * u ^ (2 * m - 1)) =
          (q * q ^ (2 * m - 1)) * u ^ (2 * m - 1) := by ring
      _ = q ^ ((2 * m - 1) + 1) * u ^ (2 * m - 1) := by
        rw [pow_succ']
      _ = q ^ (2 * m) * u ^ (2 * m - 1) := by rw [← hsucc]
  unfold hermiteResolventClosedIntegrand mehlerRescaledIntegrand
  rw [show -(q * u) = -(u * q) by ring, hheat]
  calc
    q * ((q * u) ^ (2 * m - 1) * Real.exp (-(u * q)) *
        ((Real.sqrt q)⁻¹ *
          (mehlerScaledPrefactor q u *
            Real.exp (-Real.pi *
              (mehlerSlowScaledRate q u +
                mehlerFastScaledRate q u *
                  (signedSquare y - signedSquare x) ^ 2))))) =
      (q * (q * u) ^ (2 * m - 1)) * Real.exp (-(u * q)) *
        (Real.sqrt q)⁻¹ * mehlerScaledPrefactor q u *
          Real.exp (-Real.pi *
            (mehlerSlowScaledRate q u +
              mehlerFastScaledRate q u *
                (signedSquare y - signedSquare x) ^ 2)) := by ring
    _ = (q ^ (2 * m) / Real.sqrt q) *
        (u ^ (2 * m - 1) * Real.exp (-(u * q)) *
          mehlerScaledPrefactor q u *
            Real.exp (-Real.pi *
              (mehlerSlowScaledRate q u +
                mehlerFastScaledRate q u *
                  (signedSquare y - signedSquare x) ^ 2))) := by
      rw [hpow]
      field_simp [hsqrt]

/-- Exact rescaling of the whole positive-time resolvent integral. -/
theorem integral_hermiteResolventClosedIntegrand_eq_scaled
    (m : ℕ) (hm : 1 ≤ m)
    {q x y : ℝ} (hq : 0 < q)
    (hxy : 0 ≤ x * y)
    (hqScale : q * (|x| + |y|) ^ 2 = 1) :
    (∫ t : ℝ in Set.Ioi 0,
        hermiteResolventClosedIntegrand m x y t) =
      (q ^ (2 * m) / Real.sqrt q) *
        ∫ u : ℝ in Set.Ioi 0,
          mehlerRescaledIntegrand m q
            (signedSquare y - signedSquare x) u := by
  let g : ℝ → ℝ := hermiteResolventClosedIntegrand m x y
  let C : ℝ := q ^ (2 * m) / Real.sqrt q
  calc
    (∫ t : ℝ in Set.Ioi 0,
        hermiteResolventClosedIntegrand m x y t) =
        q • ∫ u : ℝ in Set.Ioi 0, g (q * u) := by
      simpa only [g, mul_zero] using
        (MeasureTheory.integral_comp_mul_left_Ioi' g 0 hq).symm
    _ = ∫ u : ℝ in Set.Ioi 0, q • g (q * u) := by
      rw [MeasureTheory.integral_smul]
    _ = ∫ u : ℝ in Set.Ioi 0,
        C * mehlerRescaledIntegrand m q
          (signedSquare y - signedSquare x) u := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      simpa only [smul_eq_mul, g, C] using
        mul_hermiteResolventClosedIntegrand_scaled
          m hm hq hu hxy hqScale
    _ = C * ∫ u : ℝ in Set.Ioi 0,
        mehlerRescaledIntegrand m q
          (signedSquare y - signedSquare x) u := by
      rw [MeasureTheory.integral_const_mul]
    _ = (q ^ (2 * m) / Real.sqrt q) *
        ∫ u : ℝ in Set.Ioi 0,
          mehlerRescaledIntegrand m q
            (signedSquare y - signedSquare x) u := by rfl

/-- Real closed-form integral for the unnormalized resolvent numerator. -/
def hermiteClosedResolventIntegral (m : ℕ) (x y : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0, hermiteResolventClosedIntegrand m x y t

/-- The justified complex Laplace representation is exactly the coercion of
the real closed-form integral. -/
theorem factorial_mul_hermiteResolventKernel_eq_closedIntegral
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    (((2 * m - 1).factorial : ℝ) : ℂ) *
        hermiteResolventKernel m x y =
      (hermiteClosedResolventIntegral m x y : ℂ) := by
  rw [factorial_mul_hermiteResolventKernel_eq_laplaceIntegral m hm x y]
  calc
    (∫ t : ℝ in Set.Ioi 0,
        (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
          hermiteHeatKernel t x y) =
        ∫ t : ℝ in Set.Ioi 0,
          (hermiteResolventClosedIntegrand m x y t : ℂ) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact hermiteResolventLaplaceIntegrand_eq_closed m x y ht
    _ = (hermiteClosedResolventIntegral m x y : ℂ) := by
      unfold hermiteClosedResolventIntegral
      exact integral_ofReal

theorem hermiteResolventClosedIntegrand_self_eq_diagonal
    (m : ℕ) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    hermiteResolventClosedIntegrand m x x t =
      hermiteResolventDiagonalIntegrand m x t := by
  have hclosed := hermiteResolventLaplaceIntegrand_eq_closed m x x ht
  have hdiag := hermiteResolventLaplaceIntegrand_self_eq_ofReal m x ht
  exact_mod_cast hclosed.symm.trans hdiag

/-- The squared point-evaluation norm uses the same real closed integral as
the off-diagonal numerator. -/
theorem norm_hermitePointMass_sq_eq_closedIntegral
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    ‖hermitePointMass m hm x‖ ^ 2 =
      ((2 * m - 1).factorial : ℝ)⁻¹ *
        hermiteClosedResolventIntegral m x x := by
  rw [norm_hermitePointMass_sq_eq_realIntegral m hm x]
  congr 1
  unfold hermiteClosedResolventIntegral
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (hermiteResolventClosedIntegrand_self_eq_diagonal m x ht).symm

theorem hermiteClosedResolventIntegral_self_pos
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    0 < hermiteClosedResolventIntegral m x x := by
  have hnorm := norm_hermitePointMass_sq_eq_closedIntegral m hm x
  have hF : 0 < ((2 * m - 1).factorial : ℝ) := by positivity
  have hpoint : 0 < ‖hermitePointMass m hm x‖ :=
    norm_pos_iff.mpr (hermitePointMass_ne_zero m hm x)
  have hmul : 0 < ((2 * m - 1).factorial : ℝ)⁻¹ *
      hermiteClosedResolventIntegral m x x := by
    rw [← hnorm]
    positivity
  exact pos_of_mul_pos_right hmul (inv_nonneg.mpr hF.le)

/-- Exact normalized-kernel formula in terms of three positive real closed
integrals.  The Gamma factor cancels before taking any limit. -/
theorem normalizedHermiteGramKernel_eq_closedIntegral_ratio
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    normalizedHermiteGramKernel m hm x y =
      ((hermiteClosedResolventIntegral m x y /
          Real.sqrt (hermiteClosedResolventIntegral m x x *
            hermiteClosedResolventIntegral m y y) : ℝ) : ℂ) := by
  let F : ℝ := ((2 * m - 1).factorial : ℝ)
  let nx : ℝ := ‖hermitePointMass m hm x‖
  let ny : ℝ := ‖hermitePointMass m hm y‖
  let Ixy : ℝ := hermiteClosedResolventIntegral m x y
  let Ixx : ℝ := hermiteClosedResolventIntegral m x x
  let Iyy : ℝ := hermiteClosedResolventIntegral m y y
  have hF : 0 < F := by
    dsimp only [F]
    positivity
  have hnx : 0 < nx := by
    dsimp only [nx]
    exact norm_pos_iff.mpr (hermitePointMass_ne_zero m hm x)
  have hny : 0 < ny := by
    dsimp only [ny]
    exact norm_pos_iff.mpr (hermitePointMass_ne_zero m hm y)
  have hnormX : nx ^ 2 = F⁻¹ * Ixx := by
    simpa only [nx, F, Ixx] using
      norm_hermitePointMass_sq_eq_closedIntegral m hm x
  have hnormY : ny ^ 2 = F⁻¹ * Iyy := by
    simpa only [ny, F, Iyy] using
      norm_hermitePointMass_sq_eq_closedIntegral m hm y
  have hIxx : Ixx = F * nx ^ 2 := by
    calc
      Ixx = F * (F⁻¹ * Ixx) := by field_simp [hF.ne']
      _ = F * nx ^ 2 := by rw [← hnormX]
  have hIyy : Iyy = F * ny ^ 2 := by
    calc
      Iyy = F * (F⁻¹ * Iyy) := by field_simp [hF.ne']
      _ = F * ny ^ 2 := by rw [← hnormY]
  have hsqrt : Real.sqrt (Ixx * Iyy) = F * nx * ny := by
    rw [hIxx, hIyy]
    rw [show (F * nx ^ 2) * (F * ny ^ 2) =
        (F * nx * ny) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos (mul_pos hF hnx) hny)]
  have hraw := factorial_mul_hermiteResolventKernel_eq_closedIntegral
    m hm x y
  have hresolvent : hermiteResolventKernel m x y =
      ((F⁻¹ * Ixy : ℝ) : ℂ) := by
    change (F : ℂ) * hermiteResolventKernel m x y = (Ixy : ℂ) at hraw
    calc
      hermiteResolventKernel m x y =
          (F : ℂ)⁻¹ * ((F : ℂ) * hermiteResolventKernel m x y) := by
        field_simp [hF.ne']
      _ = (F : ℂ)⁻¹ * (Ixy : ℂ) := by rw [hraw]
      _ = ((F⁻¹ * Ixy : ℝ) : ℂ) := by norm_cast
  rw [normalizedHermiteGramKernel_eq_resolventKernel m hm x y,
    hresolvent]
  change (((nx⁻¹ * ny⁻¹ : ℝ) : ℂ) *
      ((F⁻¹ * Ixy : ℝ) : ℂ)) = _
  rw [show hermiteClosedResolventIntegral m x y = Ixy by rfl,
    show hermiteClosedResolventIntegral m x x = Ixx by rfl,
    show hermiteClosedResolventIntegral m y y = Iyy by rfl, hsqrt]
  norm_cast
  field_simp [hF.ne', hnx.ne', hny.ne']

/-- Common singular scale removed by the Mehler substitution. -/
def hermiteResolventScale (m : ℕ) (q : ℝ) : ℝ :=
  q ^ (2 * m) / Real.sqrt q

theorem hermiteResolventScale_pos
    (m : ℕ) {q : ℝ} (hq : 0 < q) :
    0 < hermiteResolventScale m q := by
  unfold hermiteResolventScale
  positivity

theorem hermiteClosedResolventIntegral_eq_scaled
    (m : ℕ) (hm : 1 ≤ m)
    {q x y : ℝ} (hq : 0 < q)
    (hxy : 0 ≤ x * y)
    (hqScale : q * (|x| + |y|) ^ 2 = 1) :
    hermiteClosedResolventIntegral m x y =
      hermiteResolventScale m q *
        ∫ u : ℝ in Set.Ioi 0,
          mehlerRescaledIntegrand m q
            (signedSquare y - signedSquare x) u := by
  simpa only [hermiteClosedResolventIntegral, hermiteResolventScale] using
    integral_hermiteResolventClosedIntegrand_eq_scaled
      m hm hq hxy hqScale

theorem closedIntegral_ratio_scale_identity
    {Ixy Ixx Iyy Cxy Cxx Cyy Jxy Jxx Jyy : ℝ}
    (hCxx : 0 < Cxx) (hCyy : 0 < Cyy)
    (hJxx : 0 < Jxx) (hJyy : 0 < Jyy)
    (hxy : Ixy = Cxy * Jxy)
    (hxx : Ixx = Cxx * Jxx)
    (hyy : Iyy = Cyy * Jyy) :
    Ixy / Real.sqrt (Ixx * Iyy) =
      (Cxy / Real.sqrt (Cxx * Cyy)) *
        (Jxy / Real.sqrt (Jxx * Jyy)) := by
  rw [hxy, hxx, hyy]
  have hC : 0 < Cxx * Cyy := mul_pos hCxx hCyy
  have hJ : 0 < Jxx * Jyy := mul_pos hJxx hJyy
  rw [show (Cxx * Jxx) * (Cyy * Jyy) =
      (Cxx * Cyy) * (Jxx * Jyy) by ring,
    Real.sqrt_mul hC.le]
  field_simp [Real.sqrt_ne_zero'.mpr hC, Real.sqrt_ne_zero'.mpr hJ]

/-- Integrable limiting envelope, with the exact half-power supplied by the
Mehler prefactor. -/
def mehlerLimitMajorant (m : ℕ) (u : ℝ) : ℝ :=
  u ^ ((2 * (m : ℝ)) - 3 / 2) *
    Real.exp (-((Real.pi / 4) * u))

theorem integrableOn_mehlerLimitMajorant
    (m : ℕ) (hm : 1 ≤ m) :
    MeasureTheory.IntegrableOn (mehlerLimitMajorant m) (Set.Ioi 0) := by
  have hs : (-1 : ℝ) < 2 * (m : ℝ) - 3 / 2 := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have href := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := 2 * (m : ℝ) - 3 / 2)
    (b := Real.pi / 4) hs (by norm_num : (0 : ℝ) < 1) (by positivity)
  convert href using 1
  ext u
  unfold mehlerLimitMajorant
  rw [Real.rpow_one]
  congr 2
  ring

/-- The limiting integral which appears before diagonal normalization. -/
def hermiteUniversalLimitIntegral (m : ℕ) (δ : ℝ) : ℝ :=
  ∫ u : ℝ in Set.Ioi 0, mehlerUniversalLimitIntegrand m δ u

theorem mehlerUniversalLimitIntegrand_zero_eq_majorant
    (m : ℕ) (hm : 1 ≤ m) {u : ℝ} (hu : 0 < u) :
    mehlerUniversalLimitIntegrand m 0 u = mehlerLimitMajorant m u := by
  have hpow :
      u ^ ((2 * m : ℕ) - 1) * (1 / Real.sqrt u) =
        u ^ (2 * (m : ℝ) - 3 / 2) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hu.le,
      ← Real.rpow_natCast]
    rw [← Real.rpow_add hu]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    norm_num
    ring
  rw [mehlerUniversalLimitIntegrand, hpow, zero_pow two_ne_zero,
    mul_zero, add_zero]
  unfold mehlerLimitMajorant
  congr 2
  ring

theorem integrableOn_mehlerUniversalLimitIntegrand_zero
    (m : ℕ) (hm : 1 ≤ m) :
    MeasureTheory.IntegrableOn
      (mehlerUniversalLimitIntegrand m 0) (Set.Ioi 0) := by
  exact (integrableOn_mehlerLimitMajorant m hm).congr_fun
    (fun _u hu => (mehlerUniversalLimitIntegrand_zero_eq_majorant m hm hu).symm)
    measurableSet_Ioi

theorem hermiteUniversalLimitIntegral_zero_pos
    (m : ℕ) (hm : 1 ≤ m) :
    0 < hermiteUniversalLimitIntegral m 0 := by
  unfold hermiteUniversalLimitIntegral
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      mehlerUniversalLimitIntegrand m 0 := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ioi] with u hu
    rw [mehlerUniversalLimitIntegrand_zero_eq_majorant m hm hu]
    unfold mehlerLimitMajorant
    exact mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le
  apply (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
    (s := Set.Ioi (0 : ℝ))
    (f := mehlerUniversalLimitIntegrand m 0) hnonneg
    (integrableOn_mehlerUniversalLimitIntegrand_zero m hm)).2
  have hsupp : Set.Ioi (0 : ℝ) ⊆
      Function.support (mehlerUniversalLimitIntegrand m 0) := by
    intro u hu
    rw [Function.mem_support]
    rw [mehlerUniversalLimitIntegrand_zero_eq_majorant m hm hu]
    unfold mehlerLimitMajorant
    exact ne_of_gt (mul_pos (Real.rpow_pos_of_pos hu _)
      (Real.exp_pos _))
  have hmeasure : 0 < MeasureTheory.volume (Set.Ioi (0 : ℝ)) := by simp
  exact hmeasure.trans_le (MeasureTheory.measure_mono (by
    intro u hu
    exact ⟨hsupp hu, hu⟩))

/-- The Bessel-type limit integrand is dominated by the integrable diagonal
envelope, uniformly in the displacement. -/
theorem norm_mehlerUniversalLimitIntegrand_le_majorant
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖mehlerUniversalLimitIntegrand m δ u‖ ≤
      mehlerLimitMajorant m u := by
  have hpow :
      u ^ ((2 * m : ℕ) - 1) * (1 / Real.sqrt u) =
        u ^ (2 * (m : ℝ) - 3 / 2) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hu.le,
      ← Real.rpow_natCast]
    rw [← Real.rpow_add hu]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    norm_num
    ring
  have hextra :
      Real.exp (-Real.pi * (u / 4 + (1 / u) * δ ^ 2)) ≤
        Real.exp (-((Real.pi / 4) * u)) := by
    apply Real.exp_le_exp.mpr
    have hinv : 0 ≤ 1 / u := by positivity
    have hsquare : 0 ≤ (1 / u) * δ ^ 2 :=
      mul_nonneg hinv (sq_nonneg δ)
    nlinarith [Real.pi_pos]
  rw [mehlerUniversalLimitIntegrand, hpow, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.le _)
      (Real.exp_pos _).le)]
  unfold mehlerLimitMajorant
  exact mul_le_mul_of_nonneg_left hextra (Real.rpow_nonneg hu.le _)

/-- Fixed Gamma envelope for the rescaled small-time region. -/
def mehlerScaledSmallTimeMajorant (m : ℕ) (u : ℝ) : ℝ :=
  smallTimeMehlerPrefactorConstant *
    (u ^ (hermiteResolventHalfShape m - 1) *
      Real.exp (-((mehlerSpatialDamping / 2) * u)))

theorem integrableOn_mehlerScaledSmallTimeMajorant
    (m : ℕ) (hm : 1 ≤ m) :
    MeasureTheory.IntegrableOn
      (mehlerScaledSmallTimeMajorant m) (Set.Ioi 0) := by
  have hs : (-1 : ℝ) < hermiteResolventHalfShape m - 1 := by
    linarith [hermiteResolventHalfShape_pos hm]
  have href := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := hermiteResolventHalfShape m - 1)
    (b := mehlerSpatialDamping / 2) hs
    (by norm_num : (0 : ℝ) < 1)
    (div_pos mehlerSpatialDamping_pos two_pos)
  have href' : MeasureTheory.IntegrableOn
      (fun u : ℝ =>
        u ^ (hermiteResolventHalfShape m - 1) *
          Real.exp (-((mehlerSpatialDamping / 2) * u)))
      (Set.Ioi 0) := by
    convert href using 1
    ext u
    rw [Real.rpow_one]
    congr 2
    ring
  exact href'.const_mul smallTimeMehlerPrefactorConstant

/-- Fixed stretched-exponential envelope for the rescaled region
corresponding to original heat time at least one. -/
def mehlerScaledLargeTimeMajorant (m : ℕ) (u : ℝ) : ℝ :=
  largeTimeMehlerPrefactorConstant *
    (u ^ (((2 * m : ℕ) - 1 : ℕ) : ℝ) *
      Real.exp (-(2 * Real.sqrt (mehlerSpatialDamping / 2) *
        u ^ (1 / 2 : ℝ))))

theorem integrableOn_mehlerScaledLargeTimeMajorant
    (m : ℕ) (_hm : 1 ≤ m) :
    MeasureTheory.IntegrableOn
      (mehlerScaledLargeTimeMajorant m) (Set.Ioi 0) := by
  have hs : (-1 : ℝ) < (((2 * m : ℕ) - 1 : ℕ) : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ (((2 * m : ℕ) - 1 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hb : 0 < 2 * Real.sqrt (mehlerSpatialDamping / 2) := by
    exact mul_pos two_pos (Real.sqrt_pos.2
      (div_pos mehlerSpatialDamping_pos two_pos))
  have href := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 / 2 : ℝ)) (s := (((2 * m : ℕ) - 1 : ℕ) : ℝ))
    (b := 2 * Real.sqrt (mehlerSpatialDamping / 2)) hs
    (by norm_num : (0 : ℝ) < 1 / 2) hb
  change MeasureTheory.Integrable (mehlerScaledLargeTimeMajorant m)
    (MeasureTheory.volume.restrict (Set.Ioi 0))
  convert href.const_mul largeTimeMehlerPrefactorConstant using 1
  ext u
  unfold mehlerScaledLargeTimeMajorant
  congr 3
  ring

/-- Sum of the small- and large-time envelopes. -/
def mehlerScaledGlobalMajorant (m : ℕ) (u : ℝ) : ℝ :=
  mehlerScaledSmallTimeMajorant m u +
    mehlerScaledLargeTimeMajorant m u

theorem integrableOn_mehlerScaledGlobalMajorant
    (m : ℕ) (hm : 1 ≤ m) :
    MeasureTheory.IntegrableOn
      (mehlerScaledGlobalMajorant m) (Set.Ioi 0) := by
  exact (integrableOn_mehlerScaledSmallTimeMajorant m hm).add
    (integrableOn_mehlerScaledLargeTimeMajorant m hm)

theorem mehlerRescaledIntegrand_nonneg
    (m : ℕ) (δ : ℝ) {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    0 ≤ mehlerRescaledIntegrand m q δ u := by
  have he0 : 0 < Real.exp (-(u * q)) := Real.exp_pos _
  have he1 : Real.exp (-(u * q)) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr (mul_pos hu hq)
  have hden : 0 < 1 - Real.exp (-(u * q)) ^ 2 := by nlinarith
  have hpref : 0 < mehlerScaledPrefactor q u := by
    unfold mehlerScaledPrefactor
    positivity
  unfold mehlerRescaledIntegrand
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (pow_nonneg hu.le _) (Real.exp_pos _).le)
      hpref.le)
    (Real.exp_pos _).le

/-- On the rescaled region corresponding to original heat time at most one,
the existing refined Mehler estimate becomes a fixed integrable Gamma
majorant, independent of the spatial points and of `q`. -/
theorem norm_mehlerRescaledIntegrand_le_smallTimeMajorant
    (m : ℕ) (hm : 1 ≤ m)
    {q u x y : ℝ} (hq : 0 < q) (hu : 0 < u)
    (hqu : q * u ≤ 1) (hxy : 0 ≤ x * y)
    (hqScale : q * (|x| + |y|) ^ 2 = 1) :
    ‖mehlerRescaledIntegrand m q
        (signedSquare y - signedSquare x) u‖ ≤
      mehlerScaledSmallTimeMajorant m u := by
  let C : ℝ := q ^ (2 * m) / Real.sqrt q
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hres : 0 ≤ mehlerRescaledIntegrand m q
      (signedSquare y - signedSquare x) u :=
    mehlerRescaledIntegrand_nonneg m _ hq hu
  rw [Real.norm_eq_abs, abs_of_nonneg hres]
  apply le_of_mul_le_mul_left ?_ hC
  have hscaled := mul_hermiteResolventClosedIntegrand_scaled
    m hm hq hu hxy hqScale
  have hclosed := hermiteResolventClosedIntegrand_eq_heatNorm
    m x y (mul_pos hq hu)
  have hsmall := hermiteResolventHeatNormIntegrand_le_smallTimeGamma
    m hm (mul_pos hq hu) hqu x y
  have hsumLe : (|x| + |y|) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    have hs := sq_nonneg (|x| - |y|)
    rw [sub_sq, sq_abs, sq_abs] at hs
    rw [add_sq, sq_abs, sq_abs]
    nlinarith
  have hqSumLe := mul_le_mul_of_nonneg_left hsumLe hq.le
  have hqSquares : (1 / 2 : ℝ) ≤ q * (x ^ 2 + y ^ 2) := by
    nlinarith [hqScale]
  have hdeltaExp :
      Real.exp (-(Real.pi / 2) *
        |x * abs x - y * abs y|) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (by positivity)) (abs_nonneg _)
  have hcoef :
      (mehlerSpatialDamping / 2) * u ≤
        (1 + mehlerSpatialDamping * (x ^ 2 + y ^ 2)) * (q * u) := by
    have hdamp := mehlerSpatialDamping_pos.le
    have hmul := mul_le_mul_of_nonneg_left hqSquares hdamp
    have hqu0 : 0 ≤ q * u := (mul_pos hq hu).le
    nlinarith
  have hexp :
      Real.exp (-((1 + mehlerSpatialDamping * (x ^ 2 + y ^ 2)) *
          (q * u))) ≤
        Real.exp (-((mehlerSpatialDamping / 2) * u)) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hcoef)
  have hCeq : C = q ^ hermiteResolventHalfShape m := by
    dsimp only [C]
    convert natPow_div_sqrt_eq_rpow_sub_half (2 * m) hq using 1
    simp only [hermiteResolventHalfShape, Nat.cast_mul, Nat.cast_ofNat]
  have hscale :
      q * (q * u) ^ (hermiteResolventHalfShape m - 1) =
        C * u ^ (hermiteResolventHalfShape m - 1) := by
    rw [Real.mul_rpow hq.le hu.le]
    calc
      q * (q ^ (hermiteResolventHalfShape m - 1) *
          u ^ (hermiteResolventHalfShape m - 1)) =
        (q * q ^ (hermiteResolventHalfShape m - 1)) *
          u ^ (hermiteResolventHalfShape m - 1) := by ring
      _ = q ^ hermiteResolventHalfShape m *
          u ^ (hermiteResolventHalfShape m - 1) := by
        conv_lhs =>
          enter [1, 1]
          rw [← Real.rpow_one q]
        rw [← Real.rpow_add hq]
        congr 2
        ring
      _ = C * u ^ (hermiteResolventHalfShape m - 1) := by rw [← hCeq]
  calc
    C * mehlerRescaledIntegrand m q
        (signedSquare y - signedSquare x) u =
      q * hermiteResolventClosedIntegrand m x y (q * u) := hscaled.symm
    _ = q * hermiteResolventHeatNormIntegrand m x y (q * u) := by rw [hclosed]
    _ ≤ q * (smallTimeMehlerPrefactorConstant *
        Real.exp (-(Real.pi / 2) * |x * abs x - y * abs y|) *
        ((q * u) ^ (hermiteResolventHalfShape m - 1) *
          Real.exp (-((1 + mehlerSpatialDamping * (x ^ 2 + y ^ 2)) *
            (q * u))))) := mul_le_mul_of_nonneg_left hsmall hq.le
    _ = smallTimeMehlerPrefactorConstant *
        Real.exp (-(Real.pi / 2) * |x * abs x - y * abs y|) *
        (q * (q * u) ^ (hermiteResolventHalfShape m - 1)) *
        Real.exp (-((1 + mehlerSpatialDamping * (x ^ 2 + y ^ 2)) *
          (q * u))) := by ring
    _ = C * (smallTimeMehlerPrefactorConstant *
        Real.exp (-(Real.pi / 2) * |x * abs x - y * abs y|) *
        (u ^ (hermiteResolventHalfShape m - 1) *
          Real.exp (-((1 + mehlerSpatialDamping * (x ^ 2 + y ^ 2)) *
            (q * u))))) := by rw [hscale]; ring
    _ ≤ C * (smallTimeMehlerPrefactorConstant *
        (u ^ (hermiteResolventHalfShape m - 1) *
          Real.exp (-((mehlerSpatialDamping / 2) * u)))) := by
      have hsmallC : 0 ≤ smallTimeMehlerPrefactorConstant :=
        smallTimeMehlerPrefactorConstant_pos.le
      have huPow : 0 ≤ u ^ (hermiteResolventHalfShape m - 1) :=
        Real.rpow_nonneg hu.le _
      have hdeltaScaled :
          smallTimeMehlerPrefactorConstant *
              Real.exp (-(Real.pi / 2) * |x * abs x - y * abs y|) ≤
            smallTimeMehlerPrefactorConstant :=
        by simpa using mul_le_mul_of_nonneg_left hdeltaExp hsmallC
      gcongr
    _ = C * mehlerScaledSmallTimeMajorant m u := by rfl

/-- On the rescaled region corresponding to original heat time at least one,
the spatial Gaussian and the Laplace factor combine by AM--GM into a fixed
stretched-exponential majorant. -/
theorem norm_mehlerRescaledIntegrand_le_largeTimeMajorant
    (m : ℕ) (hm : 1 ≤ m)
    {q u x y : ℝ} (hq : 0 < q) (hqOne : q ≤ 1) (hu : 0 < u)
    (hqu : 1 ≤ q * u) (hxy : 0 ≤ x * y)
    (hqScale : q * (|x| + |y|) ^ 2 = 1) :
    ‖mehlerRescaledIntegrand m q
        (signedSquare y - signedSquare x) u‖ ≤
      mehlerScaledLargeTimeMajorant m u := by
  let C : ℝ := q ^ (2 * m) / Real.sqrt q
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hres : 0 ≤ mehlerRescaledIntegrand m q
      (signedSquare y - signedSquare x) u :=
    mehlerRescaledIntegrand_nonneg m _ hq hu
  rw [Real.norm_eq_abs, abs_of_nonneg hres]
  apply le_of_mul_le_mul_left ?_ hC
  have hscaled := mul_hermiteResolventClosedIntegrand_scaled
    m hm hq hu hxy hqScale
  have hclosed := hermiteResolventClosedIntegrand_eq_heatNorm
    m x y (mul_pos hq hu)
  have hlarge := hermiteResolventHeatNormIntegrand_le_largeTime
    m hqu x y
  have hsumLe : (|x| + |y|) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    have hs := sq_nonneg (|x| - |y|)
    rw [sub_sq, sq_abs, sq_abs] at hs
    rw [add_sq, sq_abs, sq_abs]
    nlinarith
  have hqSumLe := mul_le_mul_of_nonneg_left hsumLe hq.le
  have hqSquares : (1 / 2 : ℝ) ≤ q * (x ^ 2 + y ^ 2) := by
    nlinarith [hqScale]
  have hspatial :
      mehlerSpatialDamping / (2 * q) ≤
        mehlerSpatialDamping * (x ^ 2 + y ^ 2) := by
    apply (mul_le_mul_iff_of_pos_right hq).mp
    have hdamp := mehlerSpatialDamping_pos.le
    have hmul := mul_le_mul_of_nonneg_left hqSquares hdamp
    field_simp [hq.ne']
    nlinarith
  have hsqrtU : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu.le
  have hsqrtD : (Real.sqrt (mehlerSpatialDamping / 2)) ^ 2 =
      mehlerSpatialDamping / 2 := Real.sq_sqrt
        (div_nonneg mehlerSpatialDamping_pos.le zero_le_two)
  have hAMGM :
      2 * Real.sqrt (mehlerSpatialDamping / 2) * Real.sqrt u ≤
        q * u + mehlerSpatialDamping / (2 * q) := by
    apply (mul_le_mul_iff_of_pos_right hq).mp
    have hs := sq_nonneg
      (q * Real.sqrt u - Real.sqrt (mehlerSpatialDamping / 2))
    field_simp [hq.ne']
    nlinarith
  have hdecay :
      Real.exp (-mehlerSpatialDamping * (x ^ 2 + y ^ 2)) *
          Real.exp (-(q * u)) ≤
        Real.exp (-(2 * Real.sqrt (mehlerSpatialDamping / 2) *
          Real.sqrt u)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htotalSpatial := add_le_add_left hspatial (q * u)
    nlinarith [hAMGM]
  have hsqrtQ : Real.sqrt q ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hqOne
  have hCscale :
      q * (q * u) ^ ((2 * m : ℕ) - 1) =
        C * (Real.sqrt q * u ^ ((2 * m : ℕ) - 1)) := by
    have hpow :
        q * (q * u) ^ ((2 * m : ℕ) - 1) =
          q ^ (2 * m) * u ^ ((2 * m : ℕ) - 1) := by
      rw [mul_pow]
      have hsucc : 2 * m = (2 * m - 1) + 1 := by omega
      calc
        q * (q ^ (2 * m - 1) * u ^ (2 * m - 1)) =
            (q * q ^ (2 * m - 1)) * u ^ (2 * m - 1) := by ring
        _ = q ^ ((2 * m - 1) + 1) * u ^ (2 * m - 1) := by
          rw [pow_succ']
        _ = q ^ (2 * m) * u ^ (2 * m - 1) := by rw [← hsucc]
    rw [hpow]
    dsimp only [C]
    field_simp [Real.sqrt_ne_zero'.mpr hq]
  have hdeltaExp :
      Real.exp (-(Real.pi / 2) *
        |x * abs x - y * abs y|) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (by positivity)) (abs_nonneg _)
  calc
    C * mehlerRescaledIntegrand m q
        (signedSquare y - signedSquare x) u =
      q * hermiteResolventClosedIntegrand m x y (q * u) := hscaled.symm
    _ = q * hermiteResolventHeatNormIntegrand m x y (q * u) := by rw [hclosed]
    _ ≤ q * (largeTimeMehlerPrefactorConstant *
        Real.exp (-(Real.pi / 2) * |x * abs x - y * abs y|) *
        Real.exp (-mehlerSpatialDamping * (x ^ 2 + y ^ 2)) *
        ((q * u) ^ ((2 * m : ℕ) - 1) * Real.exp (-(q * u)))) :=
      mul_le_mul_of_nonneg_left hlarge hq.le
    _ = largeTimeMehlerPrefactorConstant *
        Real.exp (-(Real.pi / 2) * |x * abs x - y * abs y|) *
        (q * (q * u) ^ ((2 * m : ℕ) - 1)) *
        (Real.exp (-mehlerSpatialDamping * (x ^ 2 + y ^ 2)) *
          Real.exp (-(q * u))) := by ring
    _ = C * (largeTimeMehlerPrefactorConstant *
        Real.exp (-(Real.pi / 2) * |x * abs x - y * abs y|) *
        (Real.sqrt q * u ^ ((2 * m : ℕ) - 1)) *
        (Real.exp (-mehlerSpatialDamping * (x ^ 2 + y ^ 2)) *
          Real.exp (-(q * u)))) := by rw [hCscale]; ring
    _ ≤ C * (largeTimeMehlerPrefactorConstant *
        (u ^ ((2 * m : ℕ) - 1) *
          Real.exp (-(2 * Real.sqrt (mehlerSpatialDamping / 2) *
            Real.sqrt u)))) := by
      have hlargeC : 0 ≤ largeTimeMehlerPrefactorConstant :=
        largeTimeMehlerPrefactorConstant_pos.le
      have huPow : 0 ≤ u ^ ((2 * m : ℕ) - 1) := pow_nonneg hu.le _
      have hsqrtQ0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
      have hdeltaScaled :
          largeTimeMehlerPrefactorConstant *
              Real.exp (-(Real.pi / 2) * |x * abs x - y * abs y|) ≤
            largeTimeMehlerPrefactorConstant := by
        simpa using mul_le_mul_of_nonneg_left hdeltaExp hlargeC
      have hsqrtScaled :
          Real.sqrt q * u ^ ((2 * m : ℕ) - 1) ≤
            u ^ ((2 * m : ℕ) - 1) := by
        simpa using mul_le_mul_of_nonneg_right hsqrtQ huPow
      have hpre :
          (largeTimeMehlerPrefactorConstant *
              Real.exp (-(Real.pi / 2) * |x * abs x - y * abs y|)) *
              (Real.sqrt q * u ^ ((2 * m : ℕ) - 1)) ≤
            largeTimeMehlerPrefactorConstant *
              u ^ ((2 * m : ℕ) - 1) :=
        mul_le_mul hdeltaScaled hsqrtScaled
          (mul_nonneg hsqrtQ0 huPow) hlargeC
      have hpre0 : 0 ≤
          (largeTimeMehlerPrefactorConstant *
              Real.exp (-(Real.pi / 2) * |x * abs x - y * abs y|)) *
              (Real.sqrt q * u ^ ((2 * m : ℕ) - 1)) := by positivity
      have htarget0 : 0 ≤ Real.exp
          (-(2 * Real.sqrt (mehlerSpatialDamping / 2) * Real.sqrt u)) :=
        (Real.exp_pos _).le
      have hinner := mul_le_mul hpre hdecay
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        (mul_nonneg hlargeC huPow)
      exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hinner) hC.le
    _ = C * mehlerScaledLargeTimeMajorant m u := by
      simp only [mehlerScaledLargeTimeMajorant, Real.sqrt_eq_rpow,
        Real.rpow_natCast]

/-- The two regional estimates combine into one integrable envelope for every
pair scale at most one. -/
theorem norm_mehlerRescaledIntegrand_le_globalMajorant
    (m : ℕ) (hm : 1 ≤ m)
    {q u x y : ℝ} (hq : 0 < q) (hqOne : q ≤ 1) (hu : 0 < u)
    (hxy : 0 ≤ x * y)
    (hqScale : q * (|x| + |y|) ^ 2 = 1) :
    ‖mehlerRescaledIntegrand m q
        (signedSquare y - signedSquare x) u‖ ≤
      mehlerScaledGlobalMajorant m u := by
  rcases le_total (q * u) 1 with hsmall | hlarge
  · have hbound := norm_mehlerRescaledIntegrand_le_smallTimeMajorant
      m hm hq hu hsmall hxy hqScale
    have hlarge0 : 0 ≤ mehlerScaledLargeTimeMajorant m u := by
      unfold mehlerScaledLargeTimeMajorant
      exact mul_nonneg largeTimeMehlerPrefactorConstant_pos.le
        (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le)
    exact hbound.trans (by
      unfold mehlerScaledGlobalMajorant
      linarith)
  · have hbound := norm_mehlerRescaledIntegrand_le_largeTimeMajorant
      m hm hq hqOne hu hlarge hxy hqScale
    have hsmall0 : 0 ≤ mehlerScaledSmallTimeMajorant m u := by
      unfold mehlerScaledSmallTimeMajorant
      exact mul_nonneg smallTimeMehlerPrefactorConstant_pos.le
        (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le)
    exact hbound.trans (by
      unfold mehlerScaledGlobalMajorant
      linarith)

/-- Dominated convergence for the exact common-pair scaling.  This is the
integral-level analytic core needed by the later normalized-kernel limit. -/
theorem tendsto_integral_mehlerRescaledIntegrand_of_sequences
    (m : ℕ) (hm : 1 ≤ m)
    {q x y : ℕ → ℝ} {δ₀ : ℝ}
    (hqPos : ∀ n, 0 < q n)
    (hqOne : ∀ᶠ n in atTop, q n ≤ 1)
    (hxy : ∀ n, 0 ≤ x n * y n)
    (hqScale : ∀ n, q n * (|x n| + |y n|) ^ 2 = 1)
    (hqLim : Tendsto q atTop (nhdsWithin 0 (Set.Ioi 0)))
    (hδ : Tendsto (fun n => signedSquare (y n) - signedSquare (x n))
      atTop (nhds δ₀)) :
    Tendsto
      (fun n => ∫ u : ℝ in Set.Ioi 0,
        mehlerRescaledIntegrand m (q n)
          (signedSquare (y n) - signedSquare (x n)) u)
      atTop
      (nhds (∫ u : ℝ in Set.Ioi 0,
        mehlerUniversalLimitIntegrand m δ₀ u)) := by
  let F : ℕ → ℝ → ℝ := fun n u =>
    mehlerRescaledIntegrand m (q n)
      (signedSquare (y n) - signedSquare (x n)) u
  let f : ℝ → ℝ := mehlerUniversalLimitIntegrand m δ₀
  have hmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (F n)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro n
    apply Measurable.aestronglyMeasurable
    unfold F mehlerRescaledIntegrand mehlerScaledPrefactor
      mehlerSlowScaledRate mehlerFastScaledRate
    fun_prop
  have hbound : ∀ᶠ n in atTop, ∀ᵐ u ∂
      (MeasureTheory.volume.restrict (Set.Ioi 0)),
      ‖F n u‖ ≤ mehlerScaledGlobalMajorant m u := by
    filter_upwards [hqOne] with n hn
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ioi] with u hu
    exact norm_mehlerRescaledIntegrand_le_globalMajorant
      m hm (hqPos n) hn hu (hxy n) (hqScale n)
  have hlim : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Tendsto (fun n => F n u) atTop (nhds (f u)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ioi] with u hu
    exact tendsto_mehlerRescaledIntegrand_of_tendsto m hu hqLim hδ
  simpa only [F, f] using
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (mehlerScaledGlobalMajorant m)
      (Filter.Eventually.of_forall hmeas) hbound
      (integrableOn_mehlerScaledGlobalMajorant m hm) hlim

/-- Sequence-level limit of the genuine normalized Hermite Gram kernel under
explicit same-ray, exact-scale, and scale-ratio hypotheses.  The displayed
limit-integral ratio is identified with `universalGramKernel` downstream. -/
theorem tendsto_normalizedHermiteGramKernel_of_scaled_sequences
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
      atTop (nhds ((hermiteUniversalLimitIntegral m δ₀ /
        hermiteUniversalLimitIntegral m 0 : ℝ) : ℂ)) := by
  let Axy : ℕ → ℝ := fun n => ∫ u : ℝ in Set.Ioi 0,
    mehlerRescaledIntegrand m (qxy n)
      (signedSquare (y n) - signedSquare (x n)) u
  let Axx : ℕ → ℝ := fun n => ∫ u : ℝ in Set.Ioi 0,
    mehlerRescaledIntegrand m (qxx n) 0 u
  let Ayy : ℕ → ℝ := fun n => ∫ u : ℝ in Set.Ioi 0,
    mehlerRescaledIntegrand m (qyy n) 0 u
  let Jδ : ℝ := hermiteUniversalLimitIntegral m δ₀
  let J0 : ℝ := hermiteUniversalLimitIntegral m 0
  have hAxy : Tendsto Axy atTop (nhds Jδ) := by
    simpa only [Axy, Jδ, hermiteUniversalLimitIntegral] using
      tendsto_integral_mehlerRescaledIntegrand_of_sequences
        m hm hqxyPos hqxyOne hsame hqxyScale hqxyLim hδ
  have hzeroX : Tendsto
      (fun n => signedSquare (x n) - signedSquare (x n))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ℝ))
      atTop (nhds 0))
  have hzeroY : Tendsto
      (fun n => signedSquare (y n) - signedSquare (y n))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ℝ))
      atTop (nhds 0))
  have hAxx : Tendsto Axx atTop (nhds J0) := by
    simpa only [Axx, J0, hermiteUniversalLimitIntegral, sub_self] using
      tendsto_integral_mehlerRescaledIntegrand_of_sequences
        m hm hqxxPos hqxxOne (fun n => mul_self_nonneg (x n))
          hqxxScale hqxxLim hzeroX
  have hAyy : Tendsto Ayy atTop (nhds J0) := by
    simpa only [Ayy, J0, hermiteUniversalLimitIntegral, sub_self] using
      tendsto_integral_mehlerRescaledIntegrand_of_sequences
        m hm hqyyPos hqyyOne (fun n => mul_self_nonneg (y n))
          hqyyScale hqyyLim hzeroY
  have hJ0 : 0 < J0 := by
    simpa only [J0] using hermiteUniversalLimitIntegral_zero_pos m hm
  have hIxy (n : ℕ) :
      hermiteClosedResolventIntegral m (x n) (y n) =
        hermiteResolventScale m (qxy n) * Axy n := by
    simpa only [Axy] using hermiteClosedResolventIntegral_eq_scaled
      m hm (hqxyPos n) (hsame n) (hqxyScale n)
  have hIxx (n : ℕ) :
      hermiteClosedResolventIntegral m (x n) (x n) =
        hermiteResolventScale m (qxx n) * Axx n := by
    simpa only [Axx, sub_self] using hermiteClosedResolventIntegral_eq_scaled
      m hm (hqxxPos n) (mul_self_nonneg (x n)) (hqxxScale n)
  have hIyy (n : ℕ) :
      hermiteClosedResolventIntegral m (y n) (y n) =
        hermiteResolventScale m (qyy n) * Ayy n := by
    simpa only [Ayy, sub_self] using hermiteClosedResolventIntegral_eq_scaled
      m hm (hqyyPos n) (mul_self_nonneg (y n)) (hqyyScale n)
  have hAxxPos (n : ℕ) : 0 < Axx n := by
    have hi := hermiteClosedResolventIntegral_self_pos m hm (x n)
    rw [hIxx n] at hi
    exact pos_of_mul_pos_right hi
      (hermiteResolventScale_pos m (hqxxPos n)).le
  have hAyyPos (n : ℕ) : 0 < Ayy n := by
    have hi := hermiteClosedResolventIntegral_self_pos m hm (y n)
    rw [hIyy n] at hi
    exact pos_of_mul_pos_right hi
      (hermiteResolventScale_pos m (hqyyPos n)).le
  have hkernel (n : ℕ) :
      normalizedHermiteGramKernel m hm (x n) (y n) =
        (((hermiteResolventScale m (qxy n) /
            Real.sqrt (hermiteResolventScale m (qxx n) *
              hermiteResolventScale m (qyy n))) *
          (Axy n / Real.sqrt (Axx n * Ayy n)) : ℝ) : ℂ) := by
    rw [normalizedHermiteGramKernel_eq_closedIntegral_ratio]
    apply congrArg (fun r : ℝ => (r : ℂ))
    exact closedIntegral_ratio_scale_identity
      (hermiteResolventScale_pos m (hqxxPos n))
      (hermiteResolventScale_pos m (hqyyPos n))
      (hAxxPos n) (hAyyPos n) (hIxy n) (hIxx n) (hIyy n)
  have hprod : Tendsto (fun n => Axx n * Ayy n) atTop
      (nhds (J0 * J0)) := hAxx.mul hAyy
  have hsqrtRaw := (Real.continuous_sqrt.tendsto (J0 * J0)).comp hprod
  have hsqrt : Tendsto (fun n => Real.sqrt (Axx n * Ayy n)) atTop
      (nhds J0) := by
    have hsq : Real.sqrt (J0 * J0) = J0 := by
      rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos hJ0]
    rw [hsq] at hsqrtRaw
    apply hsqrtRaw.congr'
    exact Filter.Eventually.of_forall (fun _n => rfl)
  have hshape : Tendsto
      (fun n => Axy n / Real.sqrt (Axx n * Ayy n)) atTop
      (nhds (Jδ / J0)) := hAxy.div hsqrt hJ0.ne'
  have hreal : Tendsto
      (fun n =>
        (hermiteResolventScale m (qxy n) /
          Real.sqrt (hermiteResolventScale m (qxx n) *
            hermiteResolventScale m (qyy n))) *
          (Axy n / Real.sqrt (Axx n * Ayy n)))
      atTop (nhds (Jδ / J0)) := by
    simpa only [one_mul] using hscaleRatio.mul hshape
  have hcomplex := hreal.ofReal
  apply hcomplex.congr'
  filter_upwards with n
  simpa only [Jδ, J0] using (hkernel n).symm

end

end MeyerGeneralProblem
