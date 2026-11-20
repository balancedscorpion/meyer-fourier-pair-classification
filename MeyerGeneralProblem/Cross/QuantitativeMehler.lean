module

public import MeyerGeneralProblem.Cross.AllRatioMehler
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Quantitative all-ratio cross-Mehler estimate

This module upgrades qualitative dominated convergence to an explicit
first-order bound in the exact pair scale, uniformly over the full geometric
ratio interval.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- The residual oscillatory phase rate is globally first order in `q`. -/
theorem abs_crossMehlerScaledPhaseRate_le
    {q u : ℝ} (hq : 0 < q) (hu : 0 ≤ u) :
    |crossMehlerScaledPhaseRate q u| ≤ q * u ^ 2 := by
  have hz : 0 ≤ u * q := mul_nonneg hu hq.le
  have hexp0 : 0 < Real.exp (-(u * q)) := Real.exp_pos _
  have hexp1 : Real.exp (-(u * q)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hnum0 : 0 ≤ 1 - Real.exp (-(u * q)) := sub_nonneg.mpr hexp1
  have hnumLe : 1 - Real.exp (-(u * q)) ≤ u * q := by
    linarith [Real.add_one_le_exp (-(u * q))]
  have hslope0 : 0 ≤ (1 - Real.exp (-(u * q))) / q :=
    div_nonneg hnum0 hq.le
  have hslopeLe : (1 - Real.exp (-(u * q))) / q ≤ u := by
    rw [div_le_iff₀ hq]
    simpa only [mul_comm] using hnumLe
  rw [crossMehlerScaledPhaseRate_eq hq.ne' u, abs_mul, abs_neg,
    abs_of_pos hq, abs_div, abs_sq,
    abs_of_pos (by positivity : 0 < 1 + Real.exp (-(u * q)) ^ 2)]
  have hsq : ((1 - Real.exp (-(u * q))) / q) ^ 2 ≤ u ^ 2 := by
    nlinarith
  calc
    q * (((1 - Real.exp (-(u * q))) / q) ^ 2 /
          (1 + Real.exp (-(u * q)) ^ 2)) =
        q * ((1 - Real.exp (-(u * q))) / q) ^ 2 /
          (1 + Real.exp (-(u * q)) ^ 2) := by ring
    _ ≤ q * ((1 - Real.exp (-(u * q))) / q) ^ 2 := by
      exact div_le_self (mul_nonneg hq.le (sq_nonneg _))
        (by nlinarith [sq_nonneg (Real.exp (-(u * q)))])
    _ ≤ q * u ^ 2 := mul_le_mul_of_nonneg_left hsq hq.le

/-- The nonsingular cross-Mehler prefactor differs from one by at most its
first-order heat-scale bound. -/
theorem abs_crossMehlerScaledPrefactor_sub_one_le
    {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u) :
    |crossMehlerScaledPrefactor q u - 1| ≤ 2 * q * u := by
  let r : ℝ := Real.exp (-(u * q))
  have hz : 0 ≤ u * q := mul_nonneg hu hq
  have hr0 : 0 < r := by dsimp only [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp only [r]
    rw [Real.exp_le_one_iff]
    linarith
  have hrSq : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r]
  let P : ℝ := crossMehlerScaledPrefactor q u
  have hP0 : 0 ≤ P := crossMehlerScaledPrefactor_nonneg q u
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hden0 : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hdenSq : (Real.sqrt (1 + r ^ 2)) ^ 2 = 1 + r ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hnumDen : r * Real.sqrt 2 ≤ Real.sqrt (1 + r ^ 2) := by
    have hnum0 : 0 ≤ r * Real.sqrt 2 := mul_nonneg hr0.le (Real.sqrt_nonneg _)
    nlinarith [sq_nonneg (Real.sqrt (1 + r ^ 2) - r * Real.sqrt 2)]
  have hP1 : P ≤ 1 := by
    unfold P crossMehlerScaledPrefactor
    change r * Real.sqrt 2 / Real.sqrt (1 + r ^ 2) ≤ 1
    rw [div_le_one hden0]
    exact hnumDen
  have hPFormula : P ^ 2 = 2 * r ^ 2 / (1 + r ^ 2) := by
    unfold P crossMehlerScaledPrefactor
    change (r * Real.sqrt 2 / Real.sqrt (1 + r ^ 2)) ^ 2 = _
    rw [div_pow, mul_pow, hsqrt2, hdenSq]
    ring
  have hPdiff : 1 - P ≤ 1 - P ^ 2 := by
    nlinarith [mul_self_le_mul_self hP0 hP1]
  have hratio : 1 - P ^ 2 ≤ 1 - r ^ 2 := by
    rw [hPFormula]
    have hden : 0 < 1 + r ^ 2 := by positivity
    rw [show 1 - 2 * r ^ 2 / (1 + r ^ 2) =
        (1 - r ^ 2) / (1 + r ^ 2) by field_simp; ring]
    exact div_le_self (sub_nonneg.mpr hrSq)
      (by nlinarith [sq_nonneg r])
  have hrExp : r ^ 2 = Real.exp (-2 * (u * q)) := by
    dsimp only [r]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [abs_of_nonpos (sub_nonpos.mpr hP1), neg_sub]
  calc
    1 - P ≤ 1 - P ^ 2 := hPdiff
    _ ≤ 1 - r ^ 2 := hratio
    _ = 1 - Real.exp (-2 * (u * q)) := by rw [hrExp]
    _ ≤ 2 * (u * q) := one_sub_exp_neg_two_mul_le (u * q)
    _ = 2 * q * u := by ring

/-- The scaled spatial decay differs from its limiting rate by a global
first-order bound with polynomial weight in `u`. -/
theorem abs_crossMehlerScaledDecayRate_sub_le
    {q u : ℝ} (hq : 0 < q) (hu : 0 ≤ u) :
    |crossMehlerScaledDecayRate q u - u| ≤ 6 * q * u ^ 2 := by
  rcases hu.eq_or_lt with rfl | hu
  · simp [crossMehlerScaledDecayRate]
  let z : ℝ := u * q
  let e : ℝ := Real.exp (-(2 * z))
  have hz : 0 < z := mul_pos hu hq
  have he0 : 0 < e := by dsimp only [e]; positivity
  have he1 : e ≤ 1 := by
    dsimp only [e]
    rw [Real.exp_le_one_iff]
    linarith
  have hden : 0 < q * (1 + e) := mul_pos hq (by positivity)
  have hformula : crossMehlerScaledDecayRate q u - u =
      ((1 - e) - z * (1 + e)) / (q * (1 + e)) := by
    unfold crossMehlerScaledDecayRate
    dsimp only [e, z]
    field_simp
  rw [hformula, abs_div, abs_of_pos hden]
  by_cases hsmall : 2 * z ≤ 1
  · have hxabs : |-(2 * z)| ≤ 1 := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have htaylor := Real.abs_exp_sub_one_sub_id_le hxabs
    have htaylor' : |e - 1 + 2 * z| ≤ (2 * z) ^ 2 := by
      dsimp only [e]
      convert htaylor using 1 <;> ring
    have honeSub0 : 0 ≤ 1 - e := sub_nonneg.mpr he1
    have honeSubLe : 1 - e ≤ 2 * z := by
      dsimp only [e]
      linarith [Real.add_one_le_exp (-(2 * z))]
    have hnum : |(1 - e) - z * (1 + e)| ≤ 6 * z ^ 2 := by
      rw [show (1 - e) - z * (1 + e) =
          -(e - 1 + 2 * z) + z * (1 - e) by ring]
      calc
        |-(e - 1 + 2 * z) + z * (1 - e)| ≤
            |-(e - 1 + 2 * z)| + |z * (1 - e)| := abs_add_le _ _
        _ = |e - 1 + 2 * z| + z * (1 - e) := by
          rw [abs_neg, abs_mul, abs_of_pos hz, abs_of_nonneg honeSub0]
        _ ≤ (2 * z) ^ 2 + z * (2 * z) := by gcongr
        _ = 6 * z ^ 2 := by ring
    calc
      |(1 - e) - z * (1 + e)| / (q * (1 + e)) ≤
          (6 * z ^ 2) / (q * (1 + e)) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ ≤ (6 * z ^ 2) / q := by
        have hqden : q ≤ q * (1 + e) := by
          nlinarith [mul_pos hq he0]
        rw [div_le_div_iff₀ hden hq]
        exact mul_le_mul_of_nonneg_left hqden (by positivity)
      _ = 6 * q * u ^ 2 := by
        dsimp only [z]
        field_simp
  · have hlarge : 1 < 2 * z := lt_of_not_ge hsmall
    have hnum0 : 0 ≤ 1 - e := sub_nonneg.mpr he1
    have hD0 : 0 ≤ (1 - e) / (q * (1 + e)) := div_nonneg hnum0 hden.le
    have hDle : (1 - e) / (q * (1 + e)) ≤ 1 / q := by
      rw [div_le_div_iff₀ hden hq]
      nlinarith
    have hInv : 1 / q ≤ 2 * u := by
      rw [div_le_iff₀ hq]
      dsimp only [z] at hlarge
      linarith
    have habs : |(1 - e) / (q * (1 + e)) - u| ≤
        (1 - e) / (q * (1 + e)) + u := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hD0,
        abs_of_pos hu] using
        (abs_sub_le ((1 - e) / (q * (1 + e))) 0 u)
    have halg : ((1 - e) - z * (1 + e)) / (q * (1 + e)) =
        (1 - e) / (q * (1 + e)) - u := by
      dsimp only [z]
      field_simp
    calc
      |(1 - e) - z * (1 + e)| / (q * (1 + e)) =
          |((1 - e) - z * (1 + e)) / (q * (1 + e))| := by
        rw [abs_div, abs_of_pos hden]
      _ = |(1 - e) / (q * (1 + e)) - u| := by rw [halg]
      _ ≤ (1 - e) / (q * (1 + e)) + u := habs
      _ ≤ 3 * u := by linarith
      _ ≤ 6 * q * u ^ 2 := by
        dsimp only [z] at hlarge
        nlinarith

private theorem abs_exp_neg_sub_exp_neg_le (a b : ℝ) :
    |Real.exp (-a) - Real.exp (-b)| ≤
      |a - b| * (Real.exp (-a) + Real.exp (-b)) := by
  by_cases hab : a ≤ b
  · have hexp : Real.exp (-b) ≤ Real.exp (-a) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hdiff : 0 ≤ b - a := sub_nonneg.mpr hab
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
    have hexp : Real.exp (-a) ≤ Real.exp (-b) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hdiff : 0 ≤ a - b := sub_nonneg.mpr hba
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

/-- Explicit integrable density controlling the first-order all-ratio cross
Mehler error. -/
def crossMehlerQuantitativeMajorant (m : ℕ) (u : ℝ) : ℝ :=
  7 * Real.pi * (Real.sqrt 2 * Real.exp crossMehlerDecayConstant) *
      u ^ (((2 * m : ℕ) - 1) + 2) *
        Real.exp (-crossMehlerDecayConstant * Real.sqrt u) +
    6 * Real.pi * Real.sqrt 2 *
      u ^ (((2 * m : ℕ) - 1) + 2) * Real.exp (-Real.pi * u) +
    2 * u ^ (((2 * m : ℕ) - 1) + 1) * Real.exp (-Real.pi * u)

/-- The quantitative cross-Mehler error majorant is nonnegative on the
positive half-line. -/
theorem crossMehlerQuantitativeMajorant_nonneg
    (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ crossMehlerQuantitativeMajorant m u := by
  unfold crossMehlerQuantitativeMajorant
  positivity

private theorem integrableOn_natPow_mul_exp_neg_sqrt
    (k : ℕ) {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ k * Real.exp (-b * Real.sqrt u)) (Set.Ioi 0) := by
  have hs : (-1 : ℝ) < (k : ℝ) :=
    (by norm_num : (-1 : ℝ) < 0).trans_le (Nat.cast_nonneg k)
  have href := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 / 2 : ℝ)) (s := (k : ℝ)) (b := b)
    hs (by norm_num : (0 : ℝ) < 1 / 2) hb
  convert href using 1
  ext u
  simp only [Real.rpow_natCast, Real.sqrt_eq_rpow]

private theorem integrableOn_natPow_mul_exp_neg_mul
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

/-- The explicit first-order cross-Mehler error majorant is integrable. -/
theorem integrableOn_crossMehlerQuantitativeMajorant (m : ℕ) :
    MeasureTheory.IntegrableOn (crossMehlerQuantitativeMajorant m)
      (Set.Ioi 0) := by
  change MeasureTheory.Integrable (crossMehlerQuantitativeMajorant m)
    (MeasureTheory.volume.restrict (Set.Ioi 0))
  have hstretch := integrableOn_natPow_mul_exp_neg_sqrt
    (((2 * m : ℕ) - 1) + 2) crossMehlerDecayConstant_pos
  have hexp2 := integrableOn_natPow_mul_exp_neg_mul
    (((2 * m : ℕ) - 1) + 2) Real.pi_pos
  have hexp1 := integrableOn_natPow_mul_exp_neg_mul
    (((2 * m : ℕ) - 1) + 1) Real.pi_pos
  have h1 : MeasureTheory.Integrable
      (fun u : ℝ =>
        7 * Real.pi * (Real.sqrt 2 * Real.exp crossMehlerDecayConstant) *
          u ^ (((2 * m : ℕ) - 1) + 2) *
            Real.exp (-crossMehlerDecayConstant * Real.sqrt u))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using
      hstretch.const_mul
        (7 * Real.pi * (Real.sqrt 2 * Real.exp crossMehlerDecayConstant))
  have h2 : MeasureTheory.Integrable
      (fun u : ℝ => 6 * Real.pi * Real.sqrt 2 *
        u ^ (((2 * m : ℕ) - 1) + 2) * Real.exp (-Real.pi * u))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using
      hexp2.const_mul (6 * Real.pi * Real.sqrt 2)
  have h3 : MeasureTheory.Integrable
      (fun u : ℝ => 2 * u ^ (((2 * m : ℕ) - 1) + 1) *
        Real.exp (-Real.pi * u))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using
      hexp1.const_mul 2
  unfold crossMehlerQuantitativeMajorant
  exact (h1.add h2).add h3

/-- The exact prefactor times the scaled Gaussian decay retains the common
stretched-exponential envelope. -/
theorem crossMehlerPrefactor_mul_decay_le
    {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    crossMehlerScaledPrefactor q u *
        Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) ≤
      (Real.sqrt 2 * Real.exp crossMehlerDecayConstant) *
        Real.exp (-crossMehlerDecayConstant * Real.sqrt u) := by
  have hpref := crossMehlerScaledPrefactor_le_exp_mul_sqrt_two q u
  have hcombined := crossMehlerCombinedExp_le hq hu
  calc
    crossMehlerScaledPrefactor q u *
        Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) ≤
      (Real.exp (-(u * q)) * Real.sqrt 2) *
        Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) :=
      mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
    _ = Real.sqrt 2 * Real.exp
        (-(u * q + Real.pi * crossMehlerScaledDecayRate q u)) := by
      rw [show Real.exp (-(u * q)) * Real.sqrt 2 *
          Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) =
          Real.sqrt 2 * (Real.exp (-(u * q)) *
            Real.exp (-Real.pi * crossMehlerScaledDecayRate q u)) by ring,
        show Real.exp (-(u * q)) *
          Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) =
          Real.exp (-(u * q + Real.pi *
            crossMehlerScaledDecayRate q u)) by
        rw [← Real.exp_add]
        congr 1
        ring]
    _ ≤ Real.sqrt 2 *
        (Real.exp crossMehlerDecayConstant *
          Real.exp (-crossMehlerDecayConstant * Real.sqrt u)) :=
      mul_le_mul_of_nonneg_left hcombined (Real.sqrt_nonneg _)
    _ = (Real.sqrt 2 * Real.exp crossMehlerDecayConstant) *
        Real.exp (-crossMehlerDecayConstant * Real.sqrt u) := by ring

/-- First-order bound for the real scalar amplitude before the residual
oscillatory phase is restored. -/
theorem abs_crossMehlerScalarAmplitude_sub_le
    {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    |crossMehlerScaledPrefactor q u *
          Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) -
        Real.exp (-Real.pi * u)| ≤
      q * (6 * Real.pi * u ^ 2 *
          ((Real.sqrt 2 * Real.exp crossMehlerDecayConstant) *
              Real.exp (-crossMehlerDecayConstant * Real.sqrt u) +
            Real.sqrt 2 * Real.exp (-Real.pi * u)) +
        2 * u * Real.exp (-Real.pi * u)) := by
  let P := crossMehlerScaledPrefactor q u
  let D := crossMehlerScaledDecayRate q u
  let eD := Real.exp (-Real.pi * D)
  let eu := Real.exp (-Real.pi * u)
  let C := Real.sqrt 2 * Real.exp crossMehlerDecayConstant
  let s := Real.exp (-crossMehlerDecayConstant * Real.sqrt u)
  have hP0 : 0 ≤ P := crossMehlerScaledPrefactor_nonneg q u
  have hP1 : P ≤ Real.sqrt 2 := crossMehlerScaledPrefactor_le_sqrt_two hq hu
  have hPD : P * eD ≤ C * s := by
    simpa only [P, D, eD, C, s] using crossMehlerPrefactor_mul_decay_le hq hu
  have hPdiff : |P - 1| ≤ 2 * q * u := by
    simpa only [P] using
      abs_crossMehlerScaledPrefactor_sub_one_le hq.le hu.le
  have hDdiff : |D - u| ≤ 6 * q * u ^ 2 := by
    simpa only [D] using abs_crossMehlerScaledDecayRate_sub_le hq hu.le
  have harg : |Real.pi * D - Real.pi * u| ≤
      6 * Real.pi * q * u ^ 2 := by
    rw [show Real.pi * D - Real.pi * u = Real.pi * (D - u) by ring,
      abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hExpRaw := abs_exp_neg_sub_exp_neg_le (Real.pi * D) (Real.pi * u)
  have hExp : |eD - eu| ≤
      6 * Real.pi * q * u ^ 2 * (eD + eu) := by
    simpa only [eD, eu, neg_mul] using hExpRaw.trans
      (mul_le_mul_of_nonneg_right harg
        (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
  have hPExp : P * |eD - eu| ≤
      6 * Real.pi * q * u ^ 2 * (C * s + Real.sqrt 2 * eu) := by
    calc
      P * |eD - eu| ≤
          P * (6 * Real.pi * q * u ^ 2 * (eD + eu)) :=
        mul_le_mul_of_nonneg_left hExp hP0
      _ = 6 * Real.pi * q * u ^ 2 * (P * eD + P * eu) := by ring
      _ ≤ 6 * Real.pi * q * u ^ 2 *
          (C * s + Real.sqrt 2 * eu) := by
        gcongr
  have hPref : |P - 1| * eu ≤ 2 * q * u * eu :=
    mul_le_mul_of_nonneg_right hPdiff (Real.exp_pos _).le
  change |P * eD - eu| ≤ _
  rw [show P * eD - eu = P * (eD - eu) + (P - 1) * eu by ring]
  calc
    |P * (eD - eu) + (P - 1) * eu| ≤
        |P * (eD - eu)| + |(P - 1) * eu| := abs_add_le _ _
    _ = P * |eD - eu| + |P - 1| * eu := by
      rw [abs_mul, abs_mul, abs_of_nonneg hP0,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ 6 * Real.pi * q * u ^ 2 *
          (C * s + Real.sqrt 2 * eu) + 2 * q * u * eu :=
      add_le_add hPExp hPref
    _ = q * (6 * Real.pi * u ^ 2 *
          (C * s + Real.sqrt 2 * eu) + 2 * u * eu) := by ring

/-- Uniform first-order norm bound for the residual complex phase. -/
theorem norm_crossMehlerResidualPhase_sub_one_le
    {q ω u : ℝ} (hq : 0 < q) (hu : 0 ≤ u) (hω : |ω| ≤ 1 / 2) :
    ‖Complex.exp
        (-2 * Real.pi * Complex.I * ω * crossMehlerScaledPhaseRate q u) -
        1‖ ≤ Real.pi * q * u ^ 2 := by
  let R := crossMehlerScaledPhaseRate q u
  have hR : |R| ≤ q * u ^ 2 := by
    simpa only [R] using abs_crossMehlerScaledPhaseRate_le hq hu
  have heq : -2 * Real.pi * Complex.I * ω * R =
      Complex.I * ((-2 * Real.pi * ω * R : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq]
  calc
    ‖Complex.exp (Complex.I * ((-2 * Real.pi * ω * R : ℝ) : ℂ)) - 1‖ ≤
        ‖-2 * Real.pi * ω * R‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |ω| * |R| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg,
        abs_of_pos Real.pi_pos]
      norm_num
    _ ≤ 2 * Real.pi * (1 / 2) * (q * u ^ 2) := by gcongr
    _ = Real.pi * q * u ^ 2 := by ring

/-- Pointwise explicit `O(q)` error bound for the full rescaled integrand,
uniformly over the geometric ratio interval. -/
theorem norm_crossMehlerRescaledIntegrand_sub_leading_le
    (m : ℕ) {q ω u : ℝ} (hq : 0 < q) (hu : 0 < u)
    (hω : |ω| ≤ 1 / 2) :
    ‖crossMehlerRescaledIntegrand m q ω u -
        crossMehlerLeadingIntegrand m u‖ ≤
      q * crossMehlerQuantitativeMajorant m u := by
  let p : ℕ := (2 * m : ℕ) - 1
  let U : ℝ := u ^ p
  let P : ℝ := crossMehlerScaledPrefactor q u
  let D : ℝ := crossMehlerScaledDecayRate q u
  let R : ℝ := crossMehlerScaledPhaseRate q u
  let eD : ℝ := Real.exp (-Real.pi * D)
  let eu : ℝ := Real.exp (-Real.pi * u)
  let C : ℝ := Real.sqrt 2 * Real.exp crossMehlerDecayConstant
  let s : ℝ := Real.exp (-crossMehlerDecayConstant * Real.sqrt u)
  let A : ℝ := U * P * eD
  let B : ℝ := U * eu
  let E : ℂ := Complex.exp (-2 * Real.pi * Complex.I * ω * R)
  have hU0 : 0 ≤ U := pow_nonneg hu.le _
  have hP0 : 0 ≤ P := crossMehlerScaledPrefactor_nonneg q u
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hPD : P * eD ≤ C * s := by
    simpa only [P, D, eD, C, s] using
      crossMehlerPrefactor_mul_decay_le hq hu
  have hphase : ‖E - 1‖ ≤ Real.pi * q * u ^ 2 := by
    simpa only [E, R] using
      norm_crossMehlerResidualPhase_sub_one_le hq hu.le hω
  have hampScalar : |P * eD - eu| ≤
      q * (6 * Real.pi * u ^ 2 *
          (C * s + Real.sqrt 2 * eu) + 2 * u * eu) := by
    simpa only [P, D, eD, eu, C, s] using
      abs_crossMehlerScalarAmplitude_sub_le hq hu
  have hphasePart : A * ‖E - 1‖ ≤
      q * (Real.pi * C * u ^ (p + 2) * s) := by
    calc
      A * ‖E - 1‖ = U * (P * eD) * ‖E - 1‖ := by
        dsimp only [A]
        ring
      _ ≤ U * (C * s) * (Real.pi * q * u ^ 2) := by gcongr
      _ = q * (Real.pi * C * u ^ (p + 2) * s) := by
        dsimp only [U]
        rw [pow_add]
        ring
  have hampPart : |A - B| ≤
      q * (6 * Real.pi * C * u ^ (p + 2) * s +
        6 * Real.pi * Real.sqrt 2 * u ^ (p + 2) * eu +
        2 * u ^ (p + 1) * eu) := by
    have heq : |A - B| = U * |P * eD - eu| := by
      dsimp only [A, B]
      rw [show U * P * eD - U * eu = U * (P * eD - eu) by ring,
        abs_mul, abs_of_nonneg hU0]
    rw [heq]
    calc
      U * |P * eD - eu| ≤ U *
          (q * (6 * Real.pi * u ^ 2 *
            (C * s + Real.sqrt 2 * eu) + 2 * u * eu)) :=
        mul_le_mul_of_nonneg_left hampScalar hU0
      _ = q * (6 * Real.pi * C * u ^ (p + 2) * s +
          6 * Real.pi * Real.sqrt 2 * u ^ (p + 2) * eu +
          2 * u ^ (p + 1) * eu) := by
        dsimp only [U]
        rw [pow_add, pow_add]
        ring
  change ‖(A : ℂ) * E - (B : ℂ)‖ ≤ _
  rw [show (A : ℂ) * E - (B : ℂ) =
      (A : ℂ) * (E - 1) + ((A - B : ℝ) : ℂ) by
    push_cast
    ring]
  calc
    ‖(A : ℂ) * (E - 1) + ((A - B : ℝ) : ℂ)‖ ≤
        ‖(A : ℂ) * (E - 1)‖ + ‖((A - B : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = A * ‖E - 1‖ + |A - B| := by
      rw [Complex.norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hA0]
    _ ≤ q * (Real.pi * C * u ^ (p + 2) * s) +
        q * (6 * Real.pi * C * u ^ (p + 2) * s +
          6 * Real.pi * Real.sqrt 2 * u ^ (p + 2) * eu +
          2 * u ^ (p + 1) * eu) := add_le_add hphasePart hampPart
    _ = q * crossMehlerQuantitativeMajorant m u := by
      unfold crossMehlerQuantitativeMajorant
      dsimp only [p, C, s, eu]
      ring

/-- Explicit first-order all-ratio bound for the rescaled cross integral. -/
theorem norm_integral_crossMehlerRescaled_sub_leading_le
    (m : ℕ) (hm : 1 ≤ m) {q ω : ℝ} (hq : 0 < q)
    (hω : |ω| ≤ 1 / 2) :
    ‖(∫ u : ℝ in Set.Ioi 0,
          crossMehlerRescaledIntegrand m q ω u) -
        ∫ u : ℝ in Set.Ioi 0, crossMehlerLeadingIntegrand m u‖ ≤
      q * ∫ u : ℝ in Set.Ioi 0, crossMehlerQuantitativeMajorant m u := by
  let F : ℝ → ℂ := fun u => crossMehlerRescaledIntegrand m q ω u
  let L : ℝ → ℂ := crossMehlerLeadingIntegrand m
  let G : ℝ → ℝ := crossMehlerQuantitativeMajorant m
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have hFmeas : MeasureTheory.AEStronglyMeasurable F μ := by
    apply Measurable.aestronglyMeasurable
    unfold F crossMehlerRescaledIntegrand crossMehlerScaledPrefactor
      crossMehlerScaledDecayRate crossMehlerScaledPhaseRate
    fun_prop
  have hLmeas : MeasureTheory.AEStronglyMeasurable L μ := by
    apply Measurable.aestronglyMeasurable
    unfold L crossMehlerLeadingIntegrand
    fun_prop
  have hFbound : ∀ᵐ u ∂μ, ‖F u‖ ≤ crossMehlerGlobalMajorant m u := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ioi] with u hu
    exact norm_crossMehlerRescaledIntegrand_le_globalMajorant m hq hu
  have hFint : MeasureTheory.Integrable F μ :=
    (integrableOn_crossMehlerGlobalMajorant m hm).mono' hFmeas hFbound
  have hLreal := integrableOn_natPow_mul_exp_neg_mul
    ((2 * m : ℕ) - 1) Real.pi_pos
  have hLint : MeasureTheory.Integrable L μ := by
    have hbase : MeasureTheory.Integrable
      (fun u : ℝ => ((u ^ ((2 * m : ℕ) - 1) *
        Real.exp (-Real.pi * u) : ℝ) : ℂ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hLreal.ofReal
    change MeasureTheory.Integrable
      (fun u : ℝ => ((u ^ ((2 * m : ℕ) - 1) *
        Real.exp (-Real.pi * u) : ℝ) : ℂ))
      (MeasureTheory.volume.restrict (Set.Ioi 0))
    exact hbase
  have hGint : MeasureTheory.Integrable G μ := by
    have hbase := integrableOn_crossMehlerQuantitativeMajorant m
    change MeasureTheory.Integrable (crossMehlerQuantitativeMajorant m)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) at hbase
    simpa only [G, μ] using hbase
  have hqGint : MeasureTheory.Integrable (fun u => q * G u) μ :=
    hGint.const_mul q
  have hbound : ∀ᵐ u ∂μ, ‖F u - L u‖ ≤ q * G u := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ioi] with u hu
    exact norm_crossMehlerRescaledIntegrand_sub_leading_le m hq hu hω
  have hnormInt : MeasureTheory.Integrable (fun u => ‖F u - L u‖) μ := by
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun u => ‖F u - L u‖) μ := by
      simpa only [Pi.sub_apply] using (hFmeas.sub hLmeas).norm
    apply hqGint.mono' hmeas
    filter_upwards [hbound] with u hu
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hu
  change ‖(∫ u, F u ∂μ) - ∫ u, L u ∂μ‖ ≤ q * ∫ u, G u ∂μ
  rw [← MeasureTheory.integral_sub hFint hLint]
  calc
    ‖∫ u, F u - L u ∂μ‖ ≤ ∫ u, ‖F u - L u‖ ∂μ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ u, q * G u ∂μ :=
      MeasureTheory.integral_mono_ae hnormInt hqGint hbound
    _ = q * ∫ u, G u ∂μ := by
      rw [MeasureTheory.integral_const_mul]

end

end MeyerGeneralProblem
