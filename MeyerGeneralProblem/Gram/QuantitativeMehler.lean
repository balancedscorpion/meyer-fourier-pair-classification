module

public import MeyerGeneralProblem.Cross.QuantitativeMehler

@[expose] public section

/-!
# Quantitative diagonal Mehler estimate

This module upgrades the same-side diagonal scaling limit to an explicit
first-order integral bound.  The bound is uniform for positive scales at
most one and uses a fixed integrable majorant.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- The diagonal Mehler prefactor combined with its rescaled Laplace weight. -/
def mehlerDiagonalScaledAmplitude (q u : ℝ) : ℝ :=
  Real.exp (-(u * q)) * mehlerScaledPrefactor q u

/-- The scaled diagonal prefactor retains the limiting inverse square root. -/
theorem one_div_sqrt_le_mehlerScaledPrefactor
    {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    1 / Real.sqrt u ≤ mehlerScaledPrefactor q u := by
  have hz : 0 < u * q := mul_pos hu hq
  have hraw := one_div_sqrt_le_mehlerPrefactor hz
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsqrtu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsqrtz : Real.sqrt (u * q) = Real.sqrt u * Real.sqrt q := by
    rw [Real.sqrt_mul hu.le]
  have hsqrt2q : Real.sqrt (2 * q) = Real.sqrt 2 * Real.sqrt q := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  unfold mehlerScaledPrefactor
  rw [hsqrt2q]
  have hmul := mul_le_mul_of_nonneg_left hraw (Real.sqrt_nonneg q)
  rw [hsqrtz] at hmul
  calc
    1 / Real.sqrt u = Real.sqrt q * (1 / (Real.sqrt u * Real.sqrt q)) := by
      field_simp
    _ ≤ Real.sqrt q *
        (Real.sqrt 2 / Real.sqrt (1 - Real.exp (-(u * q)) ^ 2)) := hmul
    _ = Real.sqrt 2 * Real.sqrt q /
        Real.sqrt (1 - Real.exp (-(u * q)) ^ 2) := by ring

/-- The Laplace-weighted scaled prefactor is at most its limiting value. -/
theorem mehlerDiagonalScaledAmplitude_le
    {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    mehlerDiagonalScaledAmplitude q u ≤ 1 / Real.sqrt u := by
  let z : ℝ := u * q
  let e : ℝ := Real.exp (-(2 * z))
  have hz : 0 < z := mul_pos hu hq
  have he0 : 0 < e := by dsimp only [e]; positivity
  have he1 : e < 1 := by
    dsimp only [e]
    rw [Real.exp_lt_one_iff]
    linarith
  have hd : 0 < 1 - Real.exp (-(u * q)) ^ 2 := by
    have heRaw0 : 0 < Real.exp (-(u * q)) := Real.exp_pos _
    have heRaw1 : Real.exp (-(u * q)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    nlinarith
  have heq : Real.exp (-(u * q)) ^ 2 = e := by
    dsimp only [e, z]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hbase := Real.add_one_le_exp (2 * z)
  have hmul := mul_le_mul_of_nonneg_right hbase he0.le
  have hexpCancel : Real.exp (2 * z) * e = 1 := by
    dsimp only [e]
    rw [← Real.exp_add]
    norm_num
  have hze : 2 * z * e ≤ 1 - e := by
    rw [add_mul, hexpCancel] at hmul
    linarith
  have hA0 : 0 ≤ mehlerDiagonalScaledAmplitude q u := by
    unfold mehlerDiagonalScaledAmplitude mehlerScaledPrefactor
    positivity
  have hR0 : 0 ≤ 1 / Real.sqrt u := by positivity
  have hAsq : (mehlerDiagonalScaledAmplitude q u) ^ 2 =
      2 * q * e / (1 - e) := by
    unfold mehlerDiagonalScaledAmplitude mehlerScaledPrefactor
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * q),
      Real.sq_sqrt hd.le, heq]
    ring
  have hRsq : (1 / Real.sqrt u) ^ 2 = 1 / u := by
    rw [div_pow, one_pow, Real.sq_sqrt hu.le]
  have hsq : (mehlerDiagonalScaledAmplitude q u) ^ 2 ≤
      (1 / Real.sqrt u) ^ 2 := by
    rw [hAsq, hRsq]
    rw [div_le_div_iff₀ (sub_pos.mpr he1) hu]
    dsimp only [z] at hze
    nlinarith
  nlinarith

/-- Global first-order estimate for the Laplace-weighted diagonal prefactor. -/
theorem abs_mehlerDiagonalScaledAmplitude_sub_le
    {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    |mehlerDiagonalScaledAmplitude q u - 1 / Real.sqrt u| ≤
      q * Real.sqrt u := by
  have hupper := mehlerDiagonalScaledAmplitude_le hq hu
  have hlowerPref := one_div_sqrt_le_mehlerScaledPrefactor hq hu
  have hexp0 : 0 < Real.exp (-(u * q)) := Real.exp_pos _
  have hlower : Real.exp (-(u * q)) * (1 / Real.sqrt u) ≤
      mehlerDiagonalScaledAmplitude q u := by
    unfold mehlerDiagonalScaledAmplitude
    exact mul_le_mul_of_nonneg_left hlowerPref hexp0.le
  have hone : 1 - Real.exp (-(u * q)) ≤ u * q := by
    linarith [Real.add_one_le_exp (-(u * q))]
  have hsqrtu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsqrtSq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  rw [abs_of_nonpos (sub_nonpos.mpr hupper), neg_sub]
  calc
    1 / Real.sqrt u - mehlerDiagonalScaledAmplitude q u ≤
        1 / Real.sqrt u - Real.exp (-(u * q)) * (1 / Real.sqrt u) := by
      linarith
    _ = (1 - Real.exp (-(u * q))) / Real.sqrt u := by ring
    _ ≤ (u * q) / Real.sqrt u := by
      exact div_le_div_of_nonneg_right hone hsqrtu.le
    _ = q * Real.sqrt u := by
      field_simp
      nlinarith

/-- The diagonal slow rate is half the cross decay rate at half the time. -/
theorem mehlerSlowScaledRate_eq_half_cross
    {q : ℝ} (hq : q ≠ 0) (u : ℝ) :
    mehlerSlowScaledRate q u =
      (1 / 2 : ℝ) * crossMehlerScaledDecayRate q (u / 2) := by
  unfold mehlerSlowScaledRate crossMehlerScaledDecayRate
  field_simp [hq]

/-- Global first-order estimate for the diagonal slow spatial rate. -/
theorem abs_mehlerSlowScaledRate_sub_le
    {q u : ℝ} (hq : 0 < q) (hu : 0 ≤ u) :
    |mehlerSlowScaledRate q u - u / 4| ≤
      (3 / 4 : ℝ) * q * u ^ 2 := by
  have hcross := abs_crossMehlerScaledDecayRate_sub_le
    hq (div_nonneg hu zero_le_two : 0 ≤ u / 2)
  rw [mehlerSlowScaledRate_eq_half_cross hq.ne' u]
  have heq :
      (1 / 2 : ℝ) * crossMehlerScaledDecayRate q (u / 2) - u / 4 =
        (1 / 2 : ℝ) *
          (crossMehlerScaledDecayRate q (u / 2) - u / 2) := by ring
  rw [heq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2 : ℝ) *
        |crossMehlerScaledDecayRate q (u / 2) - u / 2| ≤
      (1 / 2 : ℝ) * (6 * q * (u / 2) ^ 2) := by gcongr
    _ = (3 / 4 : ℝ) * q * u ^ 2 := by ring

/-- The diagonal slow rate is nonnegative at positive scale and time. -/
theorem mehlerSlowScaledRate_nonneg
    {q u : ℝ} (hq : 0 < q) (hu : 0 ≤ u) :
    0 ≤ mehlerSlowScaledRate q u := by
  have hz : 0 ≤ u * q := mul_nonneg hu hq.le
  have he : Real.exp (-(u * q)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  unfold mehlerSlowScaledRate
  positivity

/-- On the local region `q*u ≤ 1`, the slow rate retains fixed linear decay. -/
theorem mehlerSlowScaledRate_lower_of_mul_le_one
    {q u : ℝ} (hq : 0 < q) (hu : 0 < u) (hqu : q * u ≤ 1) :
    Real.exp (-1) / 4 * u ≤ mehlerSlowScaledRate q u := by
  let z : ℝ := u * q
  let e : ℝ := Real.exp (-z)
  have hz : 0 < z := mul_pos hu hq
  have he0 : 0 < e := by dsimp only [e]; positivity
  have he1 : e ≤ 1 := by
    dsimp only [e]
    rw [Real.exp_le_one_iff]
    linarith
  have hze : z * e ≤ 1 - e := by
    dsimp only [e]
    exact mul_exp_neg_le_one_sub_exp_neg z
  have heLower : Real.exp (-1) ≤ e := by
    dsimp only [e, z]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hden : 0 < 2 * q * (1 + e) := by positivity
  unfold mehlerSlowScaledRate
  change Real.exp (-1) / 4 * u ≤ (1 - e) / (2 * q * (1 + e))
  rw [le_div_iff₀ hden]
  have hdenLe : 1 + e ≤ 2 := by linarith
  calc
    Real.exp (-1) / 4 * u * (2 * q * (1 + e)) =
        (Real.exp (-1) * (1 + e) / 2) * z := by
      dsimp only [z]
      ring
    _ ≤ e * z := by
      have : Real.exp (-1) * (1 + e) / 2 ≤ e := by
        have hm := mul_le_mul heLower hdenLe (by positivity : 0 ≤ 1 + e) he0.le
        nlinarith
      exact mul_le_mul_of_nonneg_right this hz.le
    _ ≤ 1 - e := by simpa only [mul_comm] using hze

private theorem abs_exp_neg_sub_exp_neg_le (a b : ℝ) :
    |Real.exp (-a) - Real.exp (-b)| ≤
      |a - b| * (Real.exp (-a) + Real.exp (-b)) := by
  by_cases hab : a ≤ b
  · have hexp : Real.exp (-b) ≤ Real.exp (-a) :=
      Real.exp_le_exp.mpr (by linarith)
    have heq : Real.exp (-a) - Real.exp (-b) =
        Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
      rw [show Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring
    have hone : 1 - Real.exp (-(b - a)) ≤ b - a := by
      linarith [Real.add_one_le_exp (-(b - a))]
    rw [abs_of_nonneg (sub_nonneg.mpr hexp),
      abs_of_nonpos (sub_nonpos.mpr hab), neg_sub, heq]
    calc
      Real.exp (-a) * (1 - Real.exp (-(b - a))) ≤
          Real.exp (-a) * (b - a) :=
        mul_le_mul_of_nonneg_left hone (Real.exp_pos _).le
      _ ≤ (b - a) * (Real.exp (-a) + Real.exp (-b)) := by
        nlinarith [Real.exp_pos (-b)]
  · have hba : b ≤ a := le_of_not_ge hab
    have hexp : Real.exp (-a) ≤ Real.exp (-b) :=
      Real.exp_le_exp.mpr (by linarith)
    have heq : Real.exp (-b) - Real.exp (-a) =
        Real.exp (-b) * (1 - Real.exp (-(a - b))) := by
      rw [show Real.exp (-a) = Real.exp (-b) * Real.exp (-(a - b)) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring
    have hone : 1 - Real.exp (-(a - b)) ≤ a - b := by
      linarith [Real.add_one_le_exp (-(a - b))]
    rw [abs_of_nonpos (sub_nonpos.mpr hexp), neg_sub,
      abs_of_nonneg (sub_nonneg.mpr hba), heq]
    calc
      Real.exp (-b) * (1 - Real.exp (-(a - b))) ≤
          Real.exp (-b) * (a - b) :=
        mul_le_mul_of_nonneg_left hone (Real.exp_pos _).le
      _ ≤ (a - b) * (Real.exp (-a) + Real.exp (-b)) := by
        nlinarith [Real.exp_pos (-a)]

/-- First-order diagonal scalar bound on the local rescaled-time region. -/
theorem abs_mehlerDiagonalScalar_sub_le_of_mul_le_one
    {q u : ℝ} (hq : 0 < q) (hu : 0 < u) (hqu : q * u ≤ 1) :
    |mehlerDiagonalScaledAmplitude q u *
          Real.exp (-Real.pi * mehlerSlowScaledRate q u) -
        (1 / Real.sqrt u) * Real.exp (-Real.pi * (u / 4))| ≤
      q * ((1 + u) + (3 * Real.pi / 2) * (u + u ^ 2)) *
        Real.exp (-(Real.pi * (Real.exp (-1) / 4)) * u) := by
  let A := mehlerDiagonalScaledAmplitude q u
  let R := 1 / Real.sqrt u
  let S := mehlerSlowScaledRate q u
  let c := Real.pi * (Real.exp (-1) / 4)
  have hA := abs_mehlerDiagonalScaledAmplitude_sub_le hq hu
  have hS := abs_mehlerSlowScaledRate_sub_le hq hu.le
  have hSlowLower := mehlerSlowScaledRate_lower_of_mul_le_one
    hq hu (by simpa [mul_comm] using hqu)
  have hcpos : 0 < c := by dsimp only [c]; positivity
  have hES : Real.exp (-Real.pi * S) ≤ Real.exp (-c * u) := by
    apply Real.exp_le_exp.mpr
    dsimp only [S, c]
    have h := neg_le_neg (mul_le_mul_of_nonneg_left hSlowLower Real.pi_pos.le)
    nlinarith
  have hEU : Real.exp (-Real.pi * (u / 4)) ≤ Real.exp (-c * u) := by
    apply Real.exp_le_exp.mpr
    have he1 : Real.exp (-1) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      norm_num
    have hcoef : Real.pi * (Real.exp (-1) / 4) ≤ Real.pi / 4 := by
      calc
        Real.pi * (Real.exp (-1) / 4) = (Real.pi / 4) * Real.exp (-1) := by ring
        _ ≤ (Real.pi / 4) * 1 :=
          mul_le_mul_of_nonneg_left he1 (by positivity)
        _ = Real.pi / 4 := by ring
    have h := neg_le_neg (mul_le_mul_of_nonneg_right hcoef hu.le)
    dsimp only [c]
    nlinarith
  have hExp := abs_exp_neg_sub_exp_neg_le (Real.pi * S) (Real.pi * (u / 4))
  have hExpBound :
      |Real.exp (-Real.pi * S) - Real.exp (-Real.pi * (u / 4))| ≤
        (3 * Real.pi / 2) * q * u ^ 2 * Real.exp (-c * u) := by
    calc
      |Real.exp (-Real.pi * S) - Real.exp (-Real.pi * (u / 4))| ≤
          |Real.pi * S - Real.pi * (u / 4)| *
            (Real.exp (-Real.pi * S) + Real.exp (-Real.pi * (u / 4))) := by
        simpa only [neg_mul] using hExp
      _ = Real.pi * |S - u / 4| *
            (Real.exp (-Real.pi * S) + Real.exp (-Real.pi * (u / 4))) := by
        rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos]
      _ ≤ Real.pi * ((3 / 4 : ℝ) * q * u ^ 2) *
            (2 * Real.exp (-c * u)) := by
        gcongr
        simpa only [two_mul] using add_le_add hES hEU
      _ = (3 * Real.pi / 2) * q * u ^ 2 * Real.exp (-c * u) := by ring
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have htri :
      |A * Real.exp (-Real.pi * S) - R * Real.exp (-Real.pi * (u / 4))| ≤
        |A - R| * Real.exp (-Real.pi * S) +
          R * |Real.exp (-Real.pi * S) - Real.exp (-Real.pi * (u / 4))| := by
    rw [show A * Real.exp (-Real.pi * S) - R * Real.exp (-Real.pi * (u / 4)) =
      (A - R) * Real.exp (-Real.pi * S) +
        R * (Real.exp (-Real.pi * S) - Real.exp (-Real.pi * (u / 4))) by ring]
    calc
      |(A - R) * Real.exp (-Real.pi * S) +
          R * (Real.exp (-Real.pi * S) - Real.exp (-Real.pi * (u / 4)))| ≤
        |(A - R) * Real.exp (-Real.pi * S)| +
          |R * (Real.exp (-Real.pi * S) - Real.exp (-Real.pi * (u / 4)))| := abs_add_le _ _
      _ = |A - R| * Real.exp (-Real.pi * S) +
          R * |Real.exp (-Real.pi * S) - Real.exp (-Real.pi * (u / 4))| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_nonneg hR0]
  have hsqrtLe : Real.sqrt u ≤ 1 + u := by nlinarith [Real.sq_sqrt hu.le]
  have huDiv : u ^ 2 / Real.sqrt u = u * Real.sqrt u := by
    have hsqrtu := Real.sqrt_pos.2 hu
    have hsqrtSq := Real.sq_sqrt hu.le
    field_simp
    nlinarith
  calc
    |A * Real.exp (-Real.pi * S) - R * Real.exp (-Real.pi * (u / 4))| ≤
        |A - R| * Real.exp (-Real.pi * S) +
          R * |Real.exp (-Real.pi * S) - Real.exp (-Real.pi * (u / 4))| := htri
    _ ≤ (q * Real.sqrt u) * Real.exp (-c * u) +
          R * ((3 * Real.pi / 2) * q * u ^ 2 * Real.exp (-c * u)) := by
      gcongr
    _ = q * (Real.sqrt u + (3 * Real.pi / 2) * (u ^ 2 / Real.sqrt u)) *
          Real.exp (-c * u) := by
      dsimp only [R]
      field_simp
    _ = q * (Real.sqrt u + (3 * Real.pi / 2) * (u * Real.sqrt u)) *
          Real.exp (-c * u) := by rw [huDiv]
    _ ≤ q * ((1 + u) + (3 * Real.pi / 2) * (u + u ^ 2)) *
          Real.exp (-c * u) := by
      have hqu0 : 0 ≤ q := hq.le
      have hcoef0 : 0 ≤ 3 * Real.pi / 2 := by positivity
      have huSqrt : u * Real.sqrt u ≤ u + u ^ 2 := by
        simpa only [mul_add, mul_one, pow_two] using
          mul_le_mul_of_nonneg_left hsqrtLe hu.le
      gcongr

/-- Fixed integrable density controlling the diagonal first-order remainder. -/
def mehlerDiagonalQuantitativeMajorant (m : ℕ) (u : ℝ) : ℝ :=
  u ^ ((2 * m : ℕ) - 1) *
      (((1 + u) + (3 * Real.pi / 2) * (u + u ^ 2)) *
        Real.exp (-(Real.pi * (Real.exp (-1) / 4)) * u)) +
    u * (mehlerScaledGlobalMajorant m u + mehlerLimitMajorant m u)

/-- The existing global Mehler envelope applies to the zero-displacement diagonal. -/
theorem norm_mehlerRescaledIntegrand_zero_le_globalMajorant
    (m : ℕ) (hm : 1 ≤ m) {q u : ℝ}
    (hq : 0 < q) (hqOne : q ≤ 1) (hu : 0 < u) :
    ‖mehlerRescaledIntegrand m q 0 u‖ ≤
      mehlerScaledGlobalMajorant m u := by
  let x : ℝ := 1 / (2 * Real.sqrt q)
  have hx : 0 < x := by dsimp only [x]; positivity
  have hscale : q * (|x| + |x|) ^ 2 = 1 := by
    rw [abs_of_pos hx]
    dsimp only [x]
    have hsqrtSq := Real.sq_sqrt hq.le
    field_simp
    nlinarith
  simpa only [sub_self] using
    norm_mehlerRescaledIntegrand_le_globalMajorant
      m hm hq hqOne hu (mul_self_nonneg x) hscale

/-- Pointwise diagonal error bounded by scale times a fixed density. -/
theorem abs_mehlerRescaledIntegrand_zero_sub_le
    (m : ℕ) (hm : 1 ≤ m) {q u : ℝ}
    (hq : 0 < q) (hqOne : q ≤ 1) (hu : 0 < u) :
    |mehlerRescaledIntegrand m q 0 u -
        mehlerUniversalLimitIntegrand m 0 u| ≤
      q * mehlerDiagonalQuantitativeMajorant m u := by
  have hpow0 : 0 ≤ u ^ ((2 * m : ℕ) - 1) := pow_nonneg hu.le _
  have hG0 : 0 ≤ mehlerScaledGlobalMajorant m u := by
    have hs0 : 0 ≤ mehlerScaledSmallTimeMajorant m u := by
      unfold mehlerScaledSmallTimeMajorant
      exact mul_nonneg smallTimeMehlerPrefactorConstant_pos.le
        (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le)
    have hl0 : 0 ≤ mehlerScaledLargeTimeMajorant m u := by
      unfold mehlerScaledLargeTimeMajorant
      exact mul_nonneg largeTimeMehlerPrefactorConstant_pos.le
        (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le)
    exact add_nonneg hs0 hl0
  have hM0 : 0 ≤ mehlerLimitMajorant m u := by
    unfold mehlerLimitMajorant
    positivity
  rcases le_total (q * u) 1 with hsmall | hlarge
  · have hs := abs_mehlerDiagonalScalar_sub_le_of_mul_le_one
      hq hu (by simpa [mul_comm] using hsmall)
    have hformula :
        mehlerRescaledIntegrand m q 0 u -
            mehlerUniversalLimitIntegrand m 0 u =
          u ^ ((2 * m : ℕ) - 1) *
            (mehlerDiagonalScaledAmplitude q u *
                Real.exp (-Real.pi * mehlerSlowScaledRate q u) -
              (1 / Real.sqrt u) * Real.exp (-Real.pi * (u / 4))) := by
      unfold mehlerRescaledIntegrand mehlerUniversalLimitIntegrand
        mehlerDiagonalScaledAmplitude
      ring_nf
    rw [hformula, abs_mul, abs_of_nonneg hpow0]
    calc
      u ^ ((2 * m : ℕ) - 1) *
          |mehlerDiagonalScaledAmplitude q u *
                Real.exp (-Real.pi * mehlerSlowScaledRate q u) -
            1 / Real.sqrt u * Real.exp (-Real.pi * (u / 4))| ≤
        u ^ ((2 * m : ℕ) - 1) *
          (q * ((1 + u) + (3 * Real.pi / 2) * (u + u ^ 2)) *
            Real.exp (-(Real.pi * (Real.exp (-1) / 4)) * u)) := by gcongr
      _ ≤ q * mehlerDiagonalQuantitativeMajorant m u := by
        unfold mehlerDiagonalQuantitativeMajorant
        have hlarge0 : 0 ≤ u *
            (mehlerScaledGlobalMajorant m u + mehlerLimitMajorant m u) := by
          positivity
        nlinarith
  · have hF := norm_mehlerRescaledIntegrand_zero_le_globalMajorant
      m hm hq hqOne hu
    have hL := norm_mehlerUniversalLimitIntegrand_le_majorant m hm 0 hu
    have hraw : |mehlerRescaledIntegrand m q 0 u -
        mehlerUniversalLimitIntegrand m 0 u| ≤
        mehlerScaledGlobalMajorant m u + mehlerLimitMajorant m u := by
      rw [← Real.norm_eq_abs]
      exact (norm_sub_le _ _).trans (add_le_add hF hL)
    have hfirst0 : 0 ≤ u ^ ((2 * m : ℕ) - 1) *
        (((1 + u) + (3 * Real.pi / 2) * (u + u ^ 2)) *
          Real.exp (-(Real.pi * (Real.exp (-1) / 4)) * u)) := by
      positivity
    calc
      |mehlerRescaledIntegrand m q 0 u -
          mehlerUniversalLimitIntegrand m 0 u| ≤
        mehlerScaledGlobalMajorant m u + mehlerLimitMajorant m u := hraw
      _ ≤ q * u *
          (mehlerScaledGlobalMajorant m u + mehlerLimitMajorant m u) := by
        have hsum0 : 0 ≤ mehlerScaledGlobalMajorant m u +
            mehlerLimitMajorant m u := add_nonneg hG0 hM0
        nlinarith
      _ ≤ q * mehlerDiagonalQuantitativeMajorant m u := by
        unfold mehlerDiagonalQuantitativeMajorant
        nlinarith

private theorem integrableOn_natPow_exp_linear
    (k : ℕ) {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ k * Real.exp (-b * u)) (Set.Ioi 0) := by
  have hs : (-1 : ℝ) < (k : ℝ) :=
    (by norm_num : (-1 : ℝ) < 0).trans_le (Nat.cast_nonneg k)
  have href := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (k : ℝ)) (b := b)
    hs (by norm_num : (0 : ℝ) < 1) hb
  convert href using 1
  ext u
  simp only [Real.rpow_natCast, Real.rpow_one]

private theorem integrableOn_rpow_exp_linear
    {s b : ℝ} (hs : -1 < s) (hb : 0 < b) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ s * Real.exp (-b * u)) (Set.Ioi 0) := by
  have href := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := s) (b := b)
    hs (by norm_num : (0 : ℝ) < 1) hb
  convert href using 1
  ext u
  rw [Real.rpow_one]

private theorem integrableOn_rpow_exp_sqrt
    {s b : ℝ} (hs : -1 < s) (hb : 0 < b) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ s * Real.exp (-b * Real.sqrt u)) (Set.Ioi 0) := by
  have href := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 / 2 : ℝ)) (s := s) (b := b)
    hs (by norm_num : (0 : ℝ) < 1 / 2) hb
  convert href using 1
  ext u
  rw [Real.sqrt_eq_rpow]

/-- The explicit diagonal first-order majorant is integrable. -/
theorem integrableOn_mehlerDiagonalQuantitativeMajorant
    (m : ℕ) (hm : 1 ≤ m) :
    MeasureTheory.IntegrableOn
      (mehlerDiagonalQuantitativeMajorant m) (Set.Ioi 0) := by
  let k : ℕ := (2 * m : ℕ) - 1
  let c : ℝ := Real.pi * (Real.exp (-1) / 4)
  let C : ℝ := 3 * Real.pi / 2
  have hc : 0 < c := by dsimp only [c]; positivity
  have h0 := integrableOn_natPow_exp_linear k hc
  have h1 := integrableOn_natPow_exp_linear (k + 1) hc
  have h2 := integrableOn_natPow_exp_linear (k + 2) hc
  have hsmallRaw := (h0.add h1).add ((h1.add h2).const_mul C)
  have hsmall : MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ k *
        (((1 + u) + C * (u + u ^ 2)) * Real.exp (-c * u)))
      (Set.Ioi 0) := by
    apply hsmallRaw.congr_fun
    · intro u hu
      have hu0 : 0 < u := hu
      change
        (u ^ k * Real.exp (-c * u) +
              u ^ (k + 1) * Real.exp (-c * u)) +
            C * (u ^ (k + 1) * Real.exp (-c * u) +
              u ^ (k + 2) * Real.exp (-c * u)) =
          u ^ k * (((1 + u) + C * (u + u ^ 2)) * Real.exp (-c * u))
      rw [pow_succ, show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring
    · exact measurableSet_Ioi
  have hhalfShape : -1 < hermiteResolventHalfShape m :=
    (by norm_num : (-1 : ℝ) < 0).trans (hermiteResolventHalfShape_pos hm)
  have hsmallTailRaw := integrableOn_rpow_exp_linear hhalfShape
    (div_pos mehlerSpatialDamping_pos two_pos)
  have hsmallTail : MeasureTheory.IntegrableOn
      (fun u : ℝ => u * mehlerScaledSmallTimeMajorant m u)
      (Set.Ioi 0) := by
    have href : MeasureTheory.IntegrableOn
        (fun u : ℝ => smallTimeMehlerPrefactorConstant *
          (u ^ hermiteResolventHalfShape m *
            Real.exp (-(mehlerSpatialDamping / 2) * u))) (Set.Ioi 0) :=
      hsmallTailRaw.const_mul smallTimeMehlerPrefactorConstant
    apply href.congr_fun
    · intro u hu
      have hu0 : 0 < u := hu
      simp only [mehlerScaledSmallTimeMajorant]
      change smallTimeMehlerPrefactorConstant *
          (u ^ hermiteResolventHalfShape m *
            Real.exp (-(mehlerSpatialDamping / 2) * u)) =
        u * (smallTimeMehlerPrefactorConstant *
          (u ^ (hermiteResolventHalfShape m - 1) *
            Real.exp (-(mehlerSpatialDamping / 2 * u))))
      have hp : u * u ^ (hermiteResolventHalfShape m - 1) =
          u ^ hermiteResolventHalfShape m := by
        conv_lhs =>
          enter [1]
          rw [show u = u ^ (1 : ℝ) by simp]
        rw [← Real.rpow_add hu0]
        congr 1
        ring
      calc
        smallTimeMehlerPrefactorConstant *
            (u ^ hermiteResolventHalfShape m *
              Real.exp (-(mehlerSpatialDamping / 2) * u)) =
          smallTimeMehlerPrefactorConstant *
            ((u * u ^ (hermiteResolventHalfShape m - 1)) *
              Real.exp (-(mehlerSpatialDamping / 2) * u)) := by rw [hp]
        _ = u * (smallTimeMehlerPrefactorConstant *
            (u ^ (hermiteResolventHalfShape m - 1) *
              Real.exp (-(mehlerSpatialDamping / 2 * u)))) := by
          rw [show -(mehlerSpatialDamping / 2) * u =
            -(mehlerSpatialDamping / 2 * u) by ring]
          ring
    · exact measurableSet_Ioi
  have hk : (-1 : ℝ) < (((2 * m : ℕ) - 1 : ℕ) : ℝ) + 1 := by
    have hnonneg : (0 : ℝ) ≤ (((2 * m : ℕ) - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hlargeTailRaw := integrableOn_rpow_exp_sqrt hk
    (mul_pos two_pos (Real.sqrt_pos.2
      (div_pos mehlerSpatialDamping_pos two_pos)))
  have hlargeTail : MeasureTheory.IntegrableOn
      (fun u : ℝ => u * mehlerScaledLargeTimeMajorant m u)
      (Set.Ioi 0) := by
    have href : MeasureTheory.IntegrableOn
        (fun u : ℝ => largeTimeMehlerPrefactorConstant *
          (u ^ ((((2 * m : ℕ) - 1 : ℕ) : ℝ) + 1) *
            Real.exp (-(2 * Real.sqrt (mehlerSpatialDamping / 2)) *
              Real.sqrt u))) (Set.Ioi 0) :=
      hlargeTailRaw.const_mul largeTimeMehlerPrefactorConstant
    apply href.congr_fun
    · intro u hu
      have hu0 : 0 < u := hu
      simp only [mehlerScaledLargeTimeMajorant]
      change largeTimeMehlerPrefactorConstant *
          (u ^ ((((2 * m : ℕ) - 1 : ℕ) : ℝ) + 1) *
            Real.exp (-(2 * Real.sqrt (mehlerSpatialDamping / 2)) *
              Real.sqrt u)) =
        u * (largeTimeMehlerPrefactorConstant *
          (u ^ (((2 * m : ℕ) - 1 : ℕ) : ℝ) *
            Real.exp (-(2 * Real.sqrt (mehlerSpatialDamping / 2) *
              u ^ (1 / 2 : ℝ)))))
      have hp : u * u ^ (((2 * m : ℕ) - 1 : ℕ) : ℝ) =
          u ^ ((((2 * m : ℕ) - 1 : ℕ) : ℝ) + 1) := by
        conv_lhs =>
          enter [1]
          rw [show u = u ^ (1 : ℝ) by simp]
        rw [← Real.rpow_add hu0]
        congr 1
        ring
      rw [show Real.sqrt u = u ^ (1 / 2 : ℝ) by
        exact Real.sqrt_eq_rpow u]
      calc
        largeTimeMehlerPrefactorConstant *
            (u ^ ((((2 * m : ℕ) - 1 : ℕ) : ℝ) + 1) *
              Real.exp (-(2 * Real.sqrt (mehlerSpatialDamping / 2)) *
                u ^ (1 / 2 : ℝ))) =
          largeTimeMehlerPrefactorConstant *
            ((u * u ^ (((2 * m : ℕ) - 1 : ℕ) : ℝ)) *
              Real.exp (-(2 * Real.sqrt (mehlerSpatialDamping / 2)) *
                u ^ (1 / 2 : ℝ))) := by rw [hp]
        _ = u * (largeTimeMehlerPrefactorConstant *
            (u ^ (((2 * m : ℕ) - 1 : ℕ) : ℝ) *
              Real.exp (-(2 * Real.sqrt (mehlerSpatialDamping / 2) *
                u ^ (1 / 2 : ℝ))))) := by
          rw [show -(2 * Real.sqrt (mehlerSpatialDamping / 2)) *
              u ^ (1 / 2 : ℝ) =
            -(2 * Real.sqrt (mehlerSpatialDamping / 2) *
              u ^ (1 / 2 : ℝ)) by ring]
          ring
    · exact measurableSet_Ioi
  have hlimitExponent :
      (-1 : ℝ) < 2 * (m : ℝ) - 1 / 2 := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hlimitTailRaw := integrableOn_rpow_exp_linear hlimitExponent
    (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 4))
  have hlimitTail : MeasureTheory.IntegrableOn
      (fun u : ℝ => u * mehlerLimitMajorant m u) (Set.Ioi 0) := by
    apply hlimitTailRaw.congr_fun
    · intro u hu
      have hu0 : 0 < u := hu
      change u ^ (2 * (m : ℝ) - 1 / 2) *
          Real.exp (-(Real.pi / 4) * u) =
        u * (u ^ (2 * (m : ℝ) - 3 / 2) *
          Real.exp (-((Real.pi / 4) * u)))
      have hp : u * u ^ (2 * (m : ℝ) - 3 / 2) =
          u ^ (2 * (m : ℝ) - 1 / 2) := by
        conv_lhs =>
          enter [1]
          rw [show u = u ^ (1 : ℝ) by simp]
        rw [← Real.rpow_add hu0]
        congr 1
        ring
      calc
        u ^ (2 * (m : ℝ) - 1 / 2) *
            Real.exp (-(Real.pi / 4) * u) =
          (u * u ^ (2 * (m : ℝ) - 3 / 2)) *
            Real.exp (-(Real.pi / 4) * u) := by rw [hp]
        _ = u * (u ^ (2 * (m : ℝ) - 3 / 2) *
            Real.exp (-((Real.pi / 4) * u))) := by ring
    · exact measurableSet_Ioi
  have htailRaw := (hsmallTail.add hlargeTail).add hlimitTail
  have htail : MeasureTheory.IntegrableOn
      (fun u : ℝ => u *
        (mehlerScaledGlobalMajorant m u + mehlerLimitMajorant m u))
      (Set.Ioi 0) := by
    apply htailRaw.congr_fun
    · intro u _hu
      change (u * mehlerScaledSmallTimeMajorant m u +
          u * mehlerScaledLargeTimeMajorant m u) +
          u * mehlerLimitMajorant m u =
        u * ((mehlerScaledSmallTimeMajorant m u +
          mehlerScaledLargeTimeMajorant m u) + mehlerLimitMajorant m u)
      ring
    · exact measurableSet_Ioi
  have htotal := hsmall.add htail
  apply htotal.congr_fun
  · intro u _hu
    change
      u ^ k * (((1 + u) + C * (u + u ^ 2)) * Real.exp (-c * u)) +
          u * (mehlerScaledGlobalMajorant m u + mehlerLimitMajorant m u) =
        mehlerDiagonalQuantitativeMajorant m u
    rfl
  · exact measurableSet_Ioi

/-- Explicit first-order bound for the rescaled diagonal integral. -/
theorem abs_integral_mehlerRescaled_zero_sub_le
    (m : ℕ) (hm : 1 ≤ m) {q : ℝ} (hq : 0 < q) (hqOne : q ≤ 1) :
    |(∫ u : ℝ in Set.Ioi 0, mehlerRescaledIntegrand m q 0 u) -
        hermiteUniversalLimitIntegral m 0| ≤
      q * ∫ u : ℝ in Set.Ioi 0,
        mehlerDiagonalQuantitativeMajorant m u := by
  let F : ℝ → ℝ := fun u => mehlerRescaledIntegrand m q 0 u
  let L : ℝ → ℝ := mehlerUniversalLimitIntegrand m 0
  let G : ℝ → ℝ := mehlerDiagonalQuantitativeMajorant m
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have hFmeas : MeasureTheory.AEStronglyMeasurable F μ := by
    apply Measurable.aestronglyMeasurable
    unfold F mehlerRescaledIntegrand mehlerScaledPrefactor
      mehlerSlowScaledRate mehlerFastScaledRate
    fun_prop
  have hLmeas : MeasureTheory.AEStronglyMeasurable L μ := by
    apply Measurable.aestronglyMeasurable
    unfold L mehlerUniversalLimitIntegrand
    fun_prop
  have hFbound : ∀ᵐ u ∂μ, ‖F u‖ ≤ mehlerScaledGlobalMajorant m u := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ioi] with u hu
    exact norm_mehlerRescaledIntegrand_zero_le_globalMajorant
      m hm hq hqOne hu
  have hFint : MeasureTheory.Integrable F μ :=
    (integrableOn_mehlerScaledGlobalMajorant m hm).mono' hFmeas hFbound
  have hLint : MeasureTheory.Integrable L μ := by
    have hbase := integrableOn_mehlerUniversalLimitIntegrand_zero m hm
    change MeasureTheory.Integrable (mehlerUniversalLimitIntegrand m 0)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) at hbase
    simpa only [L, μ] using hbase
  have hGint : MeasureTheory.Integrable G μ := by
    have hbase := integrableOn_mehlerDiagonalQuantitativeMajorant m hm
    change MeasureTheory.Integrable (mehlerDiagonalQuantitativeMajorant m)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) at hbase
    simpa only [G, μ] using hbase
  have hqGint : MeasureTheory.Integrable (fun u => q * G u) μ :=
    hGint.const_mul q
  have hbound : ∀ᵐ u ∂μ, ‖F u - L u‖ ≤ q * G u := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs]
    exact abs_mehlerRescaledIntegrand_zero_sub_le m hm hq hqOne hu
  have hnormInt : MeasureTheory.Integrable (fun u => ‖F u - L u‖) μ := by
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun u => ‖F u - L u‖) μ := by
      simpa only [Pi.sub_apply] using (hFmeas.sub hLmeas).norm
    apply hqGint.mono' hmeas
    filter_upwards [hbound] with u hu
    simpa only [Real.norm_eq_abs, abs_abs] using hu
  change |(∫ u, F u ∂μ) - ∫ u, L u ∂μ| ≤ q * ∫ u, G u ∂μ
  rw [← MeasureTheory.integral_sub hFint hLint, ← Real.norm_eq_abs]
  calc
    ‖∫ u, F u - L u ∂μ‖ ≤ ∫ u, ‖F u - L u‖ ∂μ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ u, q * G u ∂μ :=
      MeasureTheory.integral_mono_ae hnormInt hqGint hbound
    _ = q * ∫ u, G u ∂μ := by
      rw [MeasureTheory.integral_const_mul]

end

end MeyerGeneralProblem
