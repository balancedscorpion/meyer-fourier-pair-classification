module

public import MeyerGeneralProblem.Gram.QuantitativeMehler
public import MeyerGeneralProblem.Gram.HermiteUniversalUniform

@[expose] public section

/-!
# Quantitative normalized cross remainder

This module combines the uniform cross-shape remainder with the two diagonal
normalization remainders.  It proves an explicit corrected two-ended error
bound for the genuinely normalized cross kernel, then rewrites the exact
natural scales into the Gram-normalized spatial-power leading model.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- Linear perturbation bound for a geometric-mean denominator near `J`. -/
theorem abs_sqrt_mul_sub_le
    {a b J ex ey : ℝ} (hJ : 0 < J)
    (hax : |a - J| ≤ ex) (hby : |b - J| ≤ ey)
    (hex : ex ≤ J / 2) (hey : ey ≤ J / 2) :
    |Real.sqrt (a * b) - J| ≤ 2 * (ex + ey) := by
  have hex0 : 0 ≤ ex := (abs_nonneg _).trans hax
  have hey0 : 0 ≤ ey := (abs_nonneg _).trans hby
  have haxb := abs_le.mp hax
  have hbyb := abs_le.mp hby
  have haLower : J / 2 ≤ a := by linarith
  have hbLower : J / 2 ≤ b := by linarith
  have haUpper : a ≤ 3 * J / 2 := by linarith
  have hbUpper : b ≤ 3 * J / 2 := by linarith
  have ha0 : 0 ≤ a := le_trans (by linarith : 0 ≤ J / 2) haLower
  have hb0 : 0 ≤ b := le_trans (by linarith : 0 ≤ J / 2) hbLower
  let D := Real.sqrt (a * b)
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hDsq : D ^ 2 = a * b := by
    dsimp only [D]
    rw [Real.sq_sqrt (mul_nonneg ha0 hb0)]
  have hprod : |a * b - J ^ 2| ≤ a * ey + J * ex := by
    rw [show a * b - J ^ 2 = a * (b - J) + J * (a - J) by ring]
    calc
      |a * (b - J) + J * (a - J)| ≤
          |a * (b - J)| + |J * (a - J)| := abs_add_le _ _
      _ = a * |b - J| + J * |a - J| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_pos hJ]
      _ ≤ a * ey + J * ex := by gcongr
  have hprod' : |a * b - J ^ 2| ≤ J * (2 * (ex + ey)) := by
    calc
      |a * b - J ^ 2| ≤ a * ey + J * ex := hprod
      _ ≤ (3 * J / 2) * ey + J * ex := by gcongr
      _ = J * (ex + (3 / 2 : ℝ) * ey) := by ring
      _ ≤ J * (2 * (ex + ey)) := by
        apply mul_le_mul_of_nonneg_left _ hJ.le
        linarith
  have hfactor : |D - J| * (D + J) = |a * b - J ^ 2| := by
    calc
      |D - J| * (D + J) = |D - J| * |D + J| := by
        rw [abs_of_nonneg (add_nonneg hD0 hJ.le)]
      _ = |(D - J) * (D + J)| := (abs_mul _ _).symm
      _ = |a * b - J ^ 2| := by
        congr 1
        calc
          (D - J) * (D + J) = D ^ 2 - J ^ 2 := by ring
          _ = a * b - J ^ 2 := by rw [hDsq]
  have hDJ : |D - J| * J ≤ |a * b - J ^ 2| := by
    rw [← hfactor]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hmul : |D - J| * J ≤ (2 * (ex + ey)) * J := by
    calc
      |D - J| * J ≤ |a * b - J ^ 2| := hDJ
      _ ≤ J * (2 * (ex + ey)) := hprod'
      _ = (2 * (ex + ey)) * J := by ring
  exact (mul_le_mul_iff_of_pos_right hJ).mp hmul

/-- Quotient perturbation bound with two independently perturbed real factors. -/
theorem norm_complex_geometricQuotient_sub_le
    {z L : ℂ} {a b J e ex ey : ℝ} (hJ : 0 < J)
    (hz : ‖z - L‖ ≤ e)
    (hax : |a - J| ≤ ex) (hby : |b - J| ≤ ey)
    (hex : ex ≤ J / 2) (hey : ey ≤ J / 2) :
    ‖z / (Real.sqrt (a * b) : ℂ) - L / (J : ℂ)‖ ≤
      2 * e / J + 4 * ‖L‖ * (ex + ey) / J ^ 2 := by
  have hex0 : 0 ≤ ex := (abs_nonneg _).trans hax
  have hey0 : 0 ≤ ey := (abs_nonneg _).trans hby
  have he0 : 0 ≤ e := (norm_nonneg _).trans hz
  have haxb := abs_le.mp hax
  have hbyb := abs_le.mp hby
  have haLower : J / 2 ≤ a := by linarith
  have hbLower : J / 2 ≤ b := by linarith
  have ha0 : 0 ≤ a := le_trans (by linarith : 0 ≤ J / 2) haLower
  have hb0 : 0 ≤ b := le_trans (by linarith : 0 ≤ J / 2) hbLower
  let D := Real.sqrt (a * b)
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hDsq : D ^ 2 = a * b := by
    dsimp only [D]
    rw [Real.sq_sqrt (mul_nonneg ha0 hb0)]
  have hDLower : J / 2 ≤ D := by
    have habLower : (J / 2) * (J / 2) ≤ a * b :=
      mul_le_mul haLower hbLower (by linarith) ha0
    nlinarith [habLower]
  have hD : 0 < D := lt_of_lt_of_le (half_pos hJ) hDLower
  have hDs := abs_sqrt_mul_sub_le hJ hax hby hex hey
  change |D - J| ≤ 2 * (ex + ey) at hDs
  change ‖z / (D : ℂ) - L / (J : ℂ)‖ ≤ _
  have halg : z / (D : ℂ) - L / (J : ℂ) =
      (z - L) / (D : ℂ) +
        L * (((J - D : ℝ) : ℂ) / ((D * J : ℝ) : ℂ)) := by
    push_cast
    field_simp [hD.ne', hJ.ne']
    ring
  rw [halg]
  have hfirst : ‖(z - L) / (D : ℂ)‖ ≤ 2 * e / J := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    rw [div_le_iff₀ hD]
    calc
      ‖z - L‖ ≤ e := hz
      _ = (2 * e / J) * (J / 2) := by field_simp
      _ ≤ (2 * e / J) * D :=
        mul_le_mul_of_nonneg_left hDLower (by positivity)
  have hsecond :
      ‖L * (((J - D : ℝ) : ℂ) / ((D * J : ℝ) : ℂ))‖ ≤
        4 * ‖L‖ * (ex + ey) / J ^ 2 := by
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (mul_pos hD hJ)]
    rw [abs_sub_comm]
    have hsum0 : 0 ≤ ex + ey := add_nonneg hex0 hey0
    have hnum : ‖L‖ * |D - J| ≤ ‖L‖ * (2 * (ex + ey)) := by gcongr
    rw [← mul_div_assoc, div_le_iff₀ (mul_pos hD hJ)]
    calc
      ‖L‖ * |D - J| ≤ ‖L‖ * (2 * (ex + ey)) := hnum
      _ ≤ (4 * ‖L‖ * (ex + ey) / J ^ 2) * (D * J) := by
        have hden : J ^ 2 / 2 ≤ D * J := by
          have hm := mul_le_mul_of_nonneg_right hDLower hJ.le
          nlinarith
        rw [show ‖L‖ * (2 * (ex + ey)) =
            (4 * ‖L‖ * (ex + ey) / J ^ 2) * (J ^ 2 / 2) by
          field_simp; ring]
        exact mul_le_mul_of_nonneg_left hden (by positivity)
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

/-- Integrated constant in the cross-shape first-order estimate. -/
def crossMehlerQuantitativeIntegral (m : ℕ) : ℝ :=
  ∫ u : ℝ in Set.Ioi 0, crossMehlerQuantitativeMajorant m u

/-- Integrated constant in each diagonal first-order estimate. -/
def mehlerDiagonalQuantitativeIntegral (m : ℕ) : ℝ :=
  ∫ u : ℝ in Set.Ioi 0, mehlerDiagonalQuantitativeMajorant m u

/-- Explicit cross-plus-two-diagonal error for the normalized shape quotient. -/
theorem norm_crossMehlerNormalizedShape_sub_le
    (m : ℕ) (hm : 1 ≤ m)
    {qxy qxx qyy ω : ℝ}
    (hqxy : 0 < qxy) (hqxx : 0 < qxx) (hqyy : 0 < qyy)
    (hqxxOne : qxx ≤ 1) (hqyyOne : qyy ≤ 1)
    (hω : |ω| ≤ 1 / 2)
    (hxxSmall : qxx * mehlerDiagonalQuantitativeIntegral m ≤
      hermiteUniversalLimitIntegral m 0 / 2)
    (hyySmall : qyy * mehlerDiagonalQuantitativeIntegral m ≤
      hermiteUniversalLimitIntegral m 0 / 2) :
    ‖((∫ u : ℝ in Set.Ioi 0,
          crossMehlerRescaledIntegrand m qxy ω u) /
        ((Real.sqrt
          ((∫ u : ℝ in Set.Ioi 0,
              mehlerRescaledIntegrand m qxx 0 u) *
            ∫ u : ℝ in Set.Ioi 0,
              mehlerRescaledIntegrand m qyy 0 u) : ℝ) : ℂ)) -
      (∫ u : ℝ in Set.Ioi 0, crossMehlerLeadingIntegrand m u) /
        (hermiteUniversalLimitIntegral m 0 : ℂ)‖ ≤
      2 * (qxy * crossMehlerQuantitativeIntegral m) /
          hermiteUniversalLimitIntegral m 0 +
        4 * ‖∫ u : ℝ in Set.Ioi 0, crossMehlerLeadingIntegrand m u‖ *
            (qxx * mehlerDiagonalQuantitativeIntegral m +
              qyy * mehlerDiagonalQuantitativeIntegral m) /
          (hermiteUniversalLimitIntegral m 0) ^ 2 := by
  let z : ℂ := ∫ u : ℝ in Set.Ioi 0,
    crossMehlerRescaledIntegrand m qxy ω u
  let L : ℂ := ∫ u : ℝ in Set.Ioi 0, crossMehlerLeadingIntegrand m u
  let a : ℝ := ∫ u : ℝ in Set.Ioi 0,
    mehlerRescaledIntegrand m qxx 0 u
  let b : ℝ := ∫ u : ℝ in Set.Ioi 0,
    mehlerRescaledIntegrand m qyy 0 u
  let J : ℝ := hermiteUniversalLimitIntegral m 0
  let Cx : ℝ := crossMehlerQuantitativeIntegral m
  let Cd : ℝ := mehlerDiagonalQuantitativeIntegral m
  have hJ : 0 < J := by
    simpa only [J] using hermiteUniversalLimitIntegral_zero_pos m hm
  have hz : ‖z - L‖ ≤ qxy * Cx := by
    simpa only [z, L, Cx, crossMehlerQuantitativeIntegral] using
      norm_integral_crossMehlerRescaled_sub_leading_le m hm hqxy hω
  have ha : |a - J| ≤ qxx * Cd := by
    simpa only [a, J, Cd, mehlerDiagonalQuantitativeIntegral] using
      abs_integral_mehlerRescaled_zero_sub_le m hm hqxx hqxxOne
  have hb : |b - J| ≤ qyy * Cd := by
    simpa only [b, J, Cd, mehlerDiagonalQuantitativeIntegral] using
      abs_integral_mehlerRescaled_zero_sub_le m hm hqyy hqyyOne
  have hquot := norm_complex_geometricQuotient_sub_le hJ hz ha hb
    (by simpa only [J, Cd] using hxxSmall)
    (by simpa only [J, Cd] using hyySmall)
  simpa only [z, L, a, b, J, Cx, Cd] using hquot

/-- The integrated cross error constant is nonnegative. -/
theorem crossMehlerQuantitativeIntegral_nonneg (m : ℕ) :
    0 ≤ crossMehlerQuantitativeIntegral m := by
  unfold crossMehlerQuantitativeIntegral
  exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    (fun _u hu => crossMehlerQuantitativeMajorant_nonneg m hu.le)

/-- The integrated diagonal error constant is nonnegative. -/
theorem mehlerDiagonalQuantitativeIntegral_nonneg (m : ℕ) :
    0 ≤ mehlerDiagonalQuantitativeIntegral m := by
  unfold mehlerDiagonalQuantitativeIntegral
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro u hu
  have hu0 : 0 < u := hu
  unfold mehlerDiagonalQuantitativeMajorant
  have hG0 : 0 ≤ mehlerScaledGlobalMajorant m u := by
    unfold mehlerScaledGlobalMajorant mehlerScaledSmallTimeMajorant
      mehlerScaledLargeTimeMajorant
    exact add_nonneg
      (mul_nonneg smallTimeMehlerPrefactorConstant_pos.le
        (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le))
      (mul_nonneg largeTimeMehlerPrefactorConstant_pos.le
        (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le))
  have hM0 : 0 ≤ mehlerLimitMajorant m u := by
    unfold mehlerLimitMajorant
    exact mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le
  have hpoly : 0 ≤ (1 + u) +
      (3 * Real.pi / 2) * (u + u ^ 2) := by
    exact add_nonneg (by linarith)
      (mul_nonneg (by positivity) (add_nonneg hu0.le (sq_nonneg u)))
  exact add_nonneg
    (mul_nonneg (pow_nonneg hu.le _)
      (mul_nonneg hpoly (Real.exp_pos _).le))
    (mul_nonneg hu0.le (add_nonneg hG0 hM0))

/-- One fixed coefficient for the sum of the three scale errors. -/
def normalizedCrossShapeErrorConstant (m : ℕ) : ℝ :=
  2 * crossMehlerQuantitativeIntegral m / hermiteUniversalLimitIntegral m 0 +
    4 * ‖∫ u : ℝ in Set.Ioi 0, crossMehlerLeadingIntegrand m u‖ *
      mehlerDiagonalQuantitativeIntegral m /
        (hermiteUniversalLimitIntegral m 0) ^ 2

/-- Corrected two-ended normalized shape remainder in summed scale form. -/
theorem norm_crossMehlerNormalizedShape_sub_le_sum
    (m : ℕ) (hm : 1 ≤ m)
    {qxy qxx qyy ω : ℝ}
    (hqxy : 0 < qxy) (hqxx : 0 < qxx) (hqyy : 0 < qyy)
    (hqxxOne : qxx ≤ 1) (hqyyOne : qyy ≤ 1)
    (hω : |ω| ≤ 1 / 2)
    (hxxSmall : qxx * mehlerDiagonalQuantitativeIntegral m ≤
      hermiteUniversalLimitIntegral m 0 / 2)
    (hyySmall : qyy * mehlerDiagonalQuantitativeIntegral m ≤
      hermiteUniversalLimitIntegral m 0 / 2) :
    ‖((∫ u : ℝ in Set.Ioi 0,
          crossMehlerRescaledIntegrand m qxy ω u) /
        ((Real.sqrt
          ((∫ u : ℝ in Set.Ioi 0,
              mehlerRescaledIntegrand m qxx 0 u) *
            ∫ u : ℝ in Set.Ioi 0,
              mehlerRescaledIntegrand m qyy 0 u) : ℝ) : ℂ)) -
      (∫ u : ℝ in Set.Ioi 0, crossMehlerLeadingIntegrand m u) /
        (hermiteUniversalLimitIntegral m 0 : ℂ)‖ ≤
      normalizedCrossShapeErrorConstant m * (qxy + qxx + qyy) := by
  have hbase := norm_crossMehlerNormalizedShape_sub_le
    m hm hqxy hqxx hqyy
    hqxxOne hqyyOne hω hxxSmall hyySmall
  refine hbase.trans ?_
  let Cx := crossMehlerQuantitativeIntegral m
  let Cd := mehlerDiagonalQuantitativeIntegral m
  let J := hermiteUniversalLimitIntegral m 0
  let L : ℂ := ∫ u : ℝ in Set.Ioi 0, crossMehlerLeadingIntegrand m u
  have hJ : 0 < J := by
    simpa only [J] using hermiteUniversalLimitIntegral_zero_pos m hm
  have hCx : 0 ≤ Cx := by
    simpa only [Cx] using crossMehlerQuantitativeIntegral_nonneg m
  have hCd : 0 ≤ Cd := by
    simpa only [Cd] using mehlerDiagonalQuantitativeIntegral_nonneg m
  have hA : 0 ≤ 2 * Cx / J := by positivity
  have hB : 0 ≤ 4 * ‖L‖ * Cd / J ^ 2 := by positivity
  have hqsum1 : qxy ≤ qxy + qxx + qyy := by linarith
  have hqsum2 : qxx + qyy ≤ qxy + qxx + qyy := by linarith
  change 2 * (qxy * Cx) / J +
      4 * ‖L‖ * (qxx * Cd + qyy * Cd) / J ^ 2 ≤
    (2 * Cx / J + 4 * ‖L‖ * Cd / J ^ 2) * (qxy + qxx + qyy)
  calc
    2 * (qxy * Cx) / J +
        4 * ‖L‖ * (qxx * Cd + qyy * Cd) / J ^ 2 =
      (2 * Cx / J) * qxy +
        (4 * ‖L‖ * Cd / J ^ 2) * (qxx + qyy) := by ring
    _ ≤ (2 * Cx / J) * (qxy + qxx + qyy) +
        (4 * ‖L‖ * Cd / J ^ 2) * (qxy + qxx + qyy) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hqsum1 hA)
        (mul_le_mul_of_nonneg_left hqsum2 hB)
    _ = (2 * Cx / J + 4 * ‖L‖ * Cd / J ^ 2) *
        (qxy + qxx + qyy) := by ring

/-- Exact geometric and oscillatory factor outside the normalized shape ratio. -/
def normalizedCrossScaleFactor
    (m : ℕ) (qxy qxx qyy x y : ℝ) : ℂ :=
  ((qxy : ℂ) ^ (2 * m) * crossMehlerLeadingPhase x y) /
    ((Real.sqrt (hermiteResolventScale m qxx *
      hermiteResolventScale m qyy) : ℝ) : ℂ)

/-- Exact-scale leading term for the genuinely normalized cross kernel. -/
def normalizedCrossLeadingTerm
    (m : ℕ) (qxy qxx qyy x y : ℝ) : ℂ :=
  normalizedCrossScaleFactor m qxy qxx qyy x y *
    ((∫ u : ℝ in Set.Ioi 0, crossMehlerLeadingIntegrand m u) /
      (hermiteUniversalLimitIntegral m 0 : ℂ))

/-- Corrected quantitative remainder for the genuine normalized cross kernel. -/
theorem norm_normalizedHermiteCrossKernel_sub_leadingTerm_le
    (m : ℕ) (hm : 1 ≤ m)
    {qxy qxx qyy x y : ℝ}
    (hqxy : 0 < qxy) (hqxx : 0 < qxx) (hqyy : 0 < qyy)
    (hqxxOne : qxx ≤ 1) (hqyyOne : qyy ≤ 1)
    (hqxyScale : qxy * (x ^ 2 + y ^ 2) = 1)
    (hqxxScale : qxx * (|x| + |x|) ^ 2 = 1)
    (hqyyScale : qyy * (|y| + |y|) ^ 2 = 1)
    (hxxSmall : qxx * mehlerDiagonalQuantitativeIntegral m ≤
      hermiteUniversalLimitIntegral m 0 / 2)
    (hyySmall : qyy * mehlerDiagonalQuantitativeIntegral m ≤
      hermiteUniversalLimitIntegral m 0 / 2) :
    ‖normalizedHermiteCrossKernel m hm x y -
        normalizedCrossLeadingTerm m qxy qxx qyy x y‖ ≤
      ‖normalizedCrossScaleFactor m qxy qxx qyy x y‖ *
        (normalizedCrossShapeErrorConstant m * (qxy + qxx + qyy)) := by
  have hω := abs_pairRatio_le_half hqxy hqxyScale
  have hshape := norm_crossMehlerNormalizedShape_sub_le_sum m hm
    hqxy hqxx hqyy hqxxOne hqyyOne hω hxxSmall hyySmall
  rw [normalizedHermiteCrossKernel_eq_scaledIntegralRatio m hm
    hqxy hqxx hqyy hqxyScale hqxxScale hqyyScale]
  unfold normalizedCrossLeadingTerm normalizedCrossScaleFactor
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left hshape (norm_nonneg _)

/-- The limiting normalized shape constant in terms of `gramNormalization`. -/
theorem crossMehlerLeadingShape_eq_gramNormalization
    (m : ℕ) (hm : 1 ≤ m) :
    (∫ u : ℝ in Set.Ioi 0, crossMehlerLeadingIntegrand m u) /
        (hermiteUniversalLimitIntegral m 0 : ℂ) =
      ((2 * gramNormalization m / (4 : ℝ) ^ (2 * m) : ℝ) : ℂ) := by
  rw [integral_crossMehlerLeadingIntegrand m hm]
  have hrel := factorial_mul_rawGramFourierIntegral_eq_limitIntegral m hm 0
  rw [rawGramFourierIntegral_zero] at hrel
  have hF : (((2 * m - 1).factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * m - 1)
  have hJ : (hermiteUniversalLimitIntegral m 0 : ℂ) ≠ 0 := by
    exact_mod_cast (hermiteUniversalLimitIntegral_zero_pos m hm).ne'
  have hM : (rawGramMass m : ℂ) ≠ 0 := by
    exact_mod_cast (rawGramMass_pos hm).ne'
  unfold gramNormalization
  push_cast
  field_simp [hF, hJ, hM]
  push_cast at hrel
  calc
    ((2 * m - 1).factorial : ℂ) * (1 / (Real.pi : ℂ)) ^ (2 * m) *
        (rawGramMass m : ℂ) * 4 ^ (2 * m) =
      (((2 * m - 1).factorial : ℂ) * (rawGramMass m : ℂ)) *
        ((1 / (Real.pi : ℂ)) ^ (2 * m) * 4 ^ (2 * m)) := by ring
    _ = (((Real.pi : ℂ) / 4) ^ (2 * m)) *
          (hermiteUniversalLimitIntegral m 0 : ℂ) *
        ((1 / (Real.pi : ℂ)) ^ (2 * m) * 4 ^ (2 * m)) := by rw [hrel]
    _ = (hermiteUniversalLimitIntegral m 0 : ℂ) := by
      rw [div_pow]
      field_simp [Real.pi_ne_zero]
      rw [← mul_pow]
      field_simp [Real.pi_ne_zero]
      simp

/-- The dyadic factor produced by the two diagonal square roots. -/
theorem four_rpow_sub_quarter_mul_two (m : ℕ) :
    (16 : ℝ) ^ ((m : ℝ) - 1 / 4) * 2 = (4 : ℝ) ^ (2 * m) := by
  have h16 : (16 : ℝ) = (4 : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    norm_num
  have h2 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc
    (16 : ℝ) ^ ((m : ℝ) - 1 / 4) * 2 =
        ((4 : ℝ) ^ (2 : ℝ)) ^ ((m : ℝ) - 1 / 4) *
          (4 : ℝ) ^ (1 / 2 : ℝ) := by rw [h16, h2]
    _ = (4 : ℝ) ^ ((2 : ℝ) * ((m : ℝ) - 1 / 4)) *
          (4 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    _ = (4 : ℝ) ^ ((2 : ℝ) * ((m : ℝ) - 1 / 4) + 1 / 2) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
    _ = (4 : ℝ) ^ (((2 * m : ℕ) : ℝ)) := by
      congr 1
      push_cast
      ring
    _ = (4 : ℝ) ^ (2 * m) := by rw [Real.rpow_natCast]

/-- The Hermite diagonal resolvent scale as a single real power. -/
theorem hermiteResolventScale_eq_rpow_sub_half
    (m : ℕ) {q : ℝ} (hq : 0 < q) :
    hermiteResolventScale m q = q ^ ((2 * m : ℝ) - 1 / 2) := by
  unfold hermiteResolventScale
  convert natPow_div_sqrt_eq_rpow_sub_half (2 * m) hq using 1
  norm_num

/-- Exact product of the two natural diagonal resolvent scales. -/
theorem sqrt_naturalDiagonalResolventScale_product
    (m : ℕ) {S T : ℝ} (hS : 0 < S) (hT : 0 < T) :
    Real.sqrt
        (hermiteResolventScale m (1 / (4 * S)) *
          hermiteResolventScale m (1 / (4 * T))) =
      (1 / (16 * S * T)) ^ ((m : ℝ) - 1 / 4) := by
  have hqS : 0 < 1 / (4 * S) := by positivity
  have hqT : 0 < 1 / (4 * T) := by positivity
  rw [hermiteResolventScale_eq_rpow_sub_half m hqS,
    hermiteResolventScale_eq_rpow_sub_half m hqT]
  rw [← Real.mul_rpow hqS.le hqT.le]
  rw [Real.sqrt_eq_rpow,
    ← Real.rpow_mul (mul_nonneg hqS.le hqT.le)]
  congr 1
  · field_simp
    ring
  · ring

/-- The real coefficient at natural cross and diagonal scales. -/
theorem normalizedCrossNaturalScale_real
    (m : ℕ) (g : ℝ) {S T : ℝ} (hS : 0 < S) (hT : 0 < T) :
    (1 / (S + T)) ^ (2 * m) /
          Real.sqrt
            (hermiteResolventScale m (1 / (4 * S)) *
              hermiteResolventScale m (1 / (4 * T))) *
        (2 * g / (4 : ℝ) ^ (2 * m)) =
      g * (S * T) ^ ((m : ℝ) - 1 / 4) /
        (S + T) ^ (2 * m) := by
  have hST : 0 < S * T := mul_pos hS hT
  have hsum : 0 < S + T := add_pos hS hT
  rw [sqrt_naturalDiagonalResolventScale_product m hS hT]
  have hbase : 0 < 16 * S * T := by positivity
  have hinv :
      (1 / (16 * S * T)) ^ ((m : ℝ) - 1 / 4) =
        ((16 * S * T) ^ ((m : ℝ) - 1 / 4))⁻¹ := by
    rw [one_div]
    exact Real.inv_rpow hbase.le _
  rw [hinv, one_div]
  rw [inv_pow]
  have hfactor :
      (16 * S * T) ^ ((m : ℝ) - 1 / 4) * 2 =
        (4 : ℝ) ^ (2 * m) *
          (S * T) ^ ((m : ℝ) - 1 / 4) := by
    rw [show 16 * S * T = 16 * (S * T) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) hST.le]
    rw [show (16 : ℝ) ^ ((m : ℝ) - 1 / 4) *
          (S * T) ^ ((m : ℝ) - 1 / 4) * 2 =
        ((16 : ℝ) ^ ((m : ℝ) - 1 / 4) * 2) *
          (S * T) ^ ((m : ℝ) - 1 / 4) by ring,
      four_rpow_sub_quarter_mul_two m]
  field_simp
  rw [show (S * T * 16) = 16 * S * T by ring,
    show ((m : ℝ) * 4 - 1) / 4 = (m : ℝ) - 1 / 4 by ring,
    hfactor]
  ring

/-- The Gram-normalized leading cross model at positive squared radii. -/
def gramNormalizedCrossLeadingTerm
    (m : ℕ) (S T x y : ℝ) : ℂ :=
  ((gramNormalization m *
      (S * T) ^ ((m : ℝ) - 1 / 4) /
        (S + T) ^ (2 * m) : ℝ) : ℂ) *
    crossMehlerLeadingPhase x y

/-- At natural scales, the exact-scale leading term is the Gram model. -/
theorem normalizedCrossLeadingTerm_natural_eq_gram
    (m : ℕ) (hm : 1 ≤ m) {S T x y : ℝ}
    (hS : 0 < S) (hT : 0 < T) :
    normalizedCrossLeadingTerm m
        (1 / (S + T)) (1 / (4 * S)) (1 / (4 * T)) x y =
      gramNormalizedCrossLeadingTerm m S T x y := by
  rw [normalizedCrossLeadingTerm,
    crossMehlerLeadingShape_eq_gramNormalization m hm]
  unfold normalizedCrossScaleFactor gramNormalizedCrossLeadingTerm
  let R : ℝ :=
    (1 / (S + T)) ^ (2 * m) /
      Real.sqrt
        (hermiteResolventScale m (1 / (4 * S)) *
          hermiteResolventScale m (1 / (4 * T)))
  have hreal := normalizedCrossNaturalScale_real
    m (gramNormalization m) hS hT
  have hR :
      ((((1 / (S + T) : ℝ) : ℂ) ^ (2 * m)) *
          crossMehlerLeadingPhase x y /
        ((Real.sqrt
          (hermiteResolventScale m (1 / (4 * S)) *
            hermiteResolventScale m (1 / (4 * T))) : ℝ) : ℂ)) =
        (R : ℂ) * crossMehlerLeadingPhase x y := by
    dsimp only [R]
    push_cast
    ring
  rw [hR]
  change ((R : ℂ) * crossMehlerLeadingPhase x y) *
      ((2 * gramNormalization m / (4 : ℝ) ^ (2 * m) : ℝ) : ℂ) = _
  rw [show ((R : ℂ) * crossMehlerLeadingPhase x y) *
        ((2 * gramNormalization m / (4 : ℝ) ^ (2 * m) : ℝ) : ℂ) =
      ((R * (2 * gramNormalization m / (4 : ℝ) ^ (2 * m)) : ℝ) : ℂ) *
        crossMehlerLeadingPhase x y by
    push_cast
    ring]
  rw [hreal]

/-- The Gram-normalized spatial leading model for the cross kernel. -/
def normalizedCrossSpatialLeadingTerm (m : ℕ) (x y : ℝ) : ℂ :=
  gramNormalizedCrossLeadingTerm m (x ^ 2) (y ^ 2) x y

/-- Exact magnitude of the Gram-normalized spatial leading kernel away from
the two zero endpoints. -/
theorem norm_normalizedCrossSpatialLeadingTerm
    (m : ℕ) (hm : 1 ≤ m) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖normalizedCrossSpatialLeadingTerm m x y‖ =
      gramNormalization m *
        (x ^ 2 * y ^ 2) ^ ((m : ℝ) - 1 / 4) /
          (x ^ 2 + y ^ 2) ^ (2 * m) := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hcoefficient : 0 <
      gramNormalization m *
        (x ^ 2 * y ^ 2) ^ ((m : ℝ) - 1 / 4) /
          (x ^ 2 + y ^ 2) ^ (2 * m) := by
    exact div_pos
      (mul_pos (gramNormalization_pos hm)
        (Real.rpow_pos_of_pos (mul_pos hx2 hy2) _))
      (pow_pos (add_pos hx2 hy2) _)
  rw [normalizedCrossSpatialLeadingTerm,
    gramNormalizedCrossLeadingTerm, norm_mul,
    norm_crossMehlerLeadingPhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hcoefficient]

/-- At natural scales, the scale-factor norm times its limiting coefficient is
exactly the norm of the Gram-normalized spatial leading term. -/
theorem norm_normalizedCrossScaleFactor_natural_mul_coefficient
    (m : ℕ) (hm : 1 ≤ m) {S T x y : ℝ}
    (hS : 0 < S) (hT : 0 < T) :
    ‖normalizedCrossScaleFactor m
        (1 / (S + T)) (1 / (4 * S)) (1 / (4 * T)) x y‖ *
        (2 * gramNormalization m / (4 : ℝ) ^ (2 * m)) =
      ‖gramNormalizedCrossLeadingTerm m S T x y‖ := by
  have hbridge := normalizedCrossLeadingTerm_natural_eq_gram
    m hm hS hT (x := x) (y := y)
  unfold normalizedCrossLeadingTerm at hbridge
  rw [crossMehlerLeadingShape_eq_gramNormalization m hm] at hbridge
  have hnorm := congrArg norm hbridge
  have hcoef : 0 < 2 * gramNormalization m / (4 : ℝ) ^ (2 * m) := by
    exact div_pos (mul_pos (by norm_num) (gramNormalization_pos hm))
      (pow_pos (by norm_num) _)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hcoef] using hnorm

/-- At signed-square parameters, the normalization error is the two endpoint inverse sum. -/
theorem normalizationError_signedSquare (m : ℕ) (x y : ℝ) :
    normalizationError m (signedSquare x) (signedSquare y) =
      (x ^ 2)⁻¹ + (y ^ 2)⁻¹ := by
  unfold normalizationError
  rw [abs_signedSquare, abs_signedSquare, sq_abs, sq_abs]

/-- The normalized cross-shape error coefficient is nonnegative. -/
theorem normalizedCrossShapeErrorConstant_nonneg
    (m : ℕ) (hm : 1 ≤ m) :
    0 ≤ normalizedCrossShapeErrorConstant m := by
  unfold normalizedCrossShapeErrorConstant
  have hJ := hermiteUniversalLimitIntegral_zero_pos m hm
  exact add_nonneg
    (div_nonneg
      (mul_nonneg (by norm_num) (crossMehlerQuantitativeIntegral_nonneg m)) hJ.le)
    (div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (norm_nonneg _))
        (mehlerDiagonalQuantitativeIntegral_nonneg m))
      (sq_nonneg _))

/-- Fixed relative error coefficient for the spatial Gram leading model. -/
def normalizedCrossSpatialErrorConstant (m : ℕ) : ℝ :=
  normalizedCrossShapeErrorConstant m * (4 : ℝ) ^ (2 * m) /
    gramNormalization m

/-- The relative spatial error coefficient is nonnegative. -/
theorem normalizedCrossSpatialErrorConstant_nonneg
    (m : ℕ) (hm : 1 ≤ m) :
    0 ≤ normalizedCrossSpatialErrorConstant m := by
  unfold normalizedCrossSpatialErrorConstant
  exact div_nonneg
    (mul_nonneg (normalizedCrossShapeErrorConstant_nonneg m hm)
      (pow_nonneg (by norm_num) _))
    (gramNormalization_pos hm).le

/-- One squared-endpoint threshold implying all diagonal small-scale
hypotheses in the natural-scale remainder theorem. -/
def normalizedCrossNaturalScaleThreshold (m : ℕ) : ℝ :=
  max (1 / 4)
    (mehlerDiagonalQuantitativeIntegral m /
      (2 * hermiteUniversalLimitIntegral m 0))

/-- The packaged natural-scale threshold is nonnegative. -/
theorem normalizedCrossNaturalScaleThreshold_nonneg
    (m : ℕ) :
    0 ≤ normalizedCrossNaturalScaleThreshold m := by
  unfold normalizedCrossNaturalScaleThreshold
  exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 4) (le_max_left _ _)

/-- A squared endpoint beyond the packaged threshold satisfies both diagonal
conditions required by the quantitative normalized-kernel estimate. -/
theorem naturalDiagonalScale_hypotheses_of_threshold
    (m : ℕ) (hm : 1 ≤ m) {x : ℝ}
    (hx : normalizedCrossNaturalScaleThreshold m ≤ x ^ 2) :
    1 / (4 * x ^ 2) ≤ 1 ∧
      (1 / (4 * x ^ 2)) * mehlerDiagonalQuantitativeIntegral m ≤
        hermiteUniversalLimitIntegral m 0 / 2 := by
  have hJ : 0 < hermiteUniversalLimitIntegral m 0 :=
    hermiteUniversalLimitIntegral_zero_pos m hm
  have hquarter : (1 / 4 : ℝ) ≤ x ^ 2 := by
    exact (le_max_left _ _).trans hx
  have hratio :
      mehlerDiagonalQuantitativeIntegral m /
          (2 * hermiteUniversalLimitIntegral m 0) ≤ x ^ 2 := by
    exact (le_max_right _ _).trans hx
  have hx2 : 0 < x ^ 2 := lt_of_lt_of_le (by norm_num) hquarter
  constructor
  · rw [div_le_one (by positivity : 0 < 4 * x ^ 2)]
    nlinarith
  · rw [one_div_mul_eq_div,
      div_le_iff₀ (by positivity : 0 < 4 * x ^ 2)]
    have hden : 0 < 2 * hermiteUniversalLimitIntegral m 0 := by
      positivity
    have hbound : mehlerDiagonalQuantitativeIntegral m ≤
        x ^ 2 * (2 * hermiteUniversalLimitIntegral m 0) :=
      (div_le_iff₀ hden).mp hratio
    calc
      mehlerDiagonalQuantitativeIntegral m ≤
          x ^ 2 * (2 * hermiteUniversalLimitIntegral m 0) := hbound
      _ = hermiteUniversalLimitIntegral m 0 / 2 * (4 * x ^ 2) := by
        ring

/-- The three natural scale parameters are controlled by both endpoint inverses. -/
theorem naturalScaleSum_le_two_endpointInverse
    {S T : ℝ} (hS : 0 < S) (hT : 0 < T) :
    1 / (S + T) + 1 / (4 * S) + 1 / (4 * T) ≤
      2 * (S⁻¹ + T⁻¹) := by
  have hpair : 1 / (S + T) ≤ 1 / S :=
    one_div_le_one_div_of_le hS (by linarith)
  have hx : 1 / (4 * S) ≤ 1 / S :=
    one_div_le_one_div_of_le hS (by linarith)
  have hy : 1 / (4 * T) ≤ 1 / T :=
    one_div_le_one_div_of_le hT (by linarith)
  simp only [one_div] at hpair hx hy ⊢
  have hSinv : 0 ≤ S⁻¹ := inv_nonneg.mpr hS.le
  have hTinv : 0 ≤ T⁻¹ := inv_nonneg.mpr hT.le
  linarith

/-- Natural spatial-scale remainder with the exact scale factor exposed. -/
theorem norm_normalizedHermiteCrossKernel_sub_gramLeading_le_scale
    (m : ℕ) (hm : 1 ≤ m) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hxxOne : 1 / (4 * x ^ 2) ≤ 1)
    (hyyOne : 1 / (4 * y ^ 2) ≤ 1)
    (hxxSmall : (1 / (4 * x ^ 2)) *
        mehlerDiagonalQuantitativeIntegral m ≤
      hermiteUniversalLimitIntegral m 0 / 2)
    (hyySmall : (1 / (4 * y ^ 2)) *
        mehlerDiagonalQuantitativeIntegral m ≤
      hermiteUniversalLimitIntegral m 0 / 2) :
    ‖normalizedHermiteCrossKernel m hm x y -
        normalizedCrossSpatialLeadingTerm m x y‖ ≤
      ‖normalizedCrossScaleFactor m
        (1 / (x ^ 2 + y ^ 2))
        (1 / (4 * x ^ 2)) (1 / (4 * y ^ 2)) x y‖ *
        (2 * normalizedCrossShapeErrorConstant m *
          normalizationError m (signedSquare x) (signedSquare y)) := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hsum : 0 < x ^ 2 + y ^ 2 := add_pos hx2 hy2
  have hqxy : 0 < 1 / (x ^ 2 + y ^ 2) := by positivity
  have hqxx : 0 < 1 / (4 * x ^ 2) := by positivity
  have hqyy : 0 < 1 / (4 * y ^ 2) := by positivity
  have hqxyScale : (1 / (x ^ 2 + y ^ 2)) *
      (x ^ 2 + y ^ 2) = 1 := by field_simp
  have hqxxScale : (1 / (4 * x ^ 2)) * (|x| + |x|) ^ 2 = 1 := by
    rw [show |x| + |x| = 2 * |x| by ring, mul_pow, sq_abs]
    field_simp
    ring
  have hqyyScale : (1 / (4 * y ^ 2)) * (|y| + |y|) ^ 2 = 1 := by
    rw [show |y| + |y| = 2 * |y| by ring, mul_pow, sq_abs]
    field_simp
    ring
  have hbase := norm_normalizedHermiteCrossKernel_sub_leadingTerm_le
    m hm hqxy hqxx hqyy hxxOne hyyOne hqxyScale hqxxScale hqyyScale
      hxxSmall hyySmall
  rw [normalizedCrossLeadingTerm_natural_eq_gram m hm hx2 hy2] at hbase
  change ‖normalizedHermiteCrossKernel m hm x y -
      normalizedCrossSpatialLeadingTerm m x y‖ ≤ _
  refine hbase.trans ?_
  have hC := normalizedCrossShapeErrorConstant_nonneg m hm
  have hsumScale := naturalScaleSum_le_two_endpointInverse hx2 hy2
  have hinside :
      normalizedCrossShapeErrorConstant m *
          (1 / (x ^ 2 + y ^ 2) + 1 / (4 * x ^ 2) + 1 / (4 * y ^ 2)) ≤
        2 * normalizedCrossShapeErrorConstant m *
          ((x ^ 2)⁻¹ + (y ^ 2)⁻¹) := by
    rw [show 2 * normalizedCrossShapeErrorConstant m *
        ((x ^ 2)⁻¹ + (y ^ 2)⁻¹) =
      normalizedCrossShapeErrorConstant m *
        (2 * ((x ^ 2)⁻¹ + (y ^ 2)⁻¹)) by ring]
    exact mul_le_mul_of_nonneg_left hsumScale hC
  rw [normalizationError_signedSquare]
  exact mul_le_mul_of_nonneg_left hinside (norm_nonneg _)

/-- Corrected natural-scale remainder relative to the Gram spatial leading model. -/
theorem norm_normalizedHermiteCrossKernel_sub_gramLeading_le
    (m : ℕ) (hm : 1 ≤ m) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hxxOne : 1 / (4 * x ^ 2) ≤ 1)
    (hyyOne : 1 / (4 * y ^ 2) ≤ 1)
    (hxxSmall : (1 / (4 * x ^ 2)) *
        mehlerDiagonalQuantitativeIntegral m ≤
      hermiteUniversalLimitIntegral m 0 / 2)
    (hyySmall : (1 / (4 * y ^ 2)) *
        mehlerDiagonalQuantitativeIntegral m ≤
      hermiteUniversalLimitIntegral m 0 / 2) :
    ‖normalizedHermiteCrossKernel m hm x y -
        normalizedCrossSpatialLeadingTerm m x y‖ ≤
      normalizedCrossSpatialErrorConstant m *
        ‖normalizedCrossSpatialLeadingTerm m x y‖ *
          normalizationError m (signedSquare x) (signedSquare y) := by
  have hbase := norm_normalizedHermiteCrossKernel_sub_gramLeading_le_scale
    m hm hx hy hxxOne hyyOne hxxSmall hyySmall
  refine hbase.trans_eq ?_
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hnorm := norm_normalizedCrossScaleFactor_natural_mul_coefficient
    m hm hx2 hy2 (x := x) (y := y)
  change
    ‖normalizedCrossScaleFactor m
        (1 / (x ^ 2 + y ^ 2))
        (1 / (4 * x ^ 2)) (1 / (4 * y ^ 2)) x y‖ *
          (2 * normalizedCrossShapeErrorConstant m *
            normalizationError m (signedSquare x) (signedSquare y)) = _
  unfold normalizedCrossSpatialErrorConstant normalizedCrossSpatialLeadingTerm
  rw [← hnorm]
  have hg : gramNormalization m ≠ 0 := (gramNormalization_pos hm).ne'
  field_simp [hg]

/-- Corrected spatial remainder with all diagonal small-scale conditions
discharged by one explicit lower threshold at each endpoint. -/
theorem norm_normalizedHermiteCrossKernel_sub_gramLeading_le_of_threshold
    (m : ℕ) (hm : 1 ≤ m) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hxLarge : normalizedCrossNaturalScaleThreshold m ≤ x ^ 2)
    (hyLarge : normalizedCrossNaturalScaleThreshold m ≤ y ^ 2) :
    ‖normalizedHermiteCrossKernel m hm x y -
        normalizedCrossSpatialLeadingTerm m x y‖ ≤
      normalizedCrossSpatialErrorConstant m *
        ‖normalizedCrossSpatialLeadingTerm m x y‖ *
          normalizationError m (signedSquare x) (signedSquare y) := by
  have hxx := naturalDiagonalScale_hypotheses_of_threshold m hm hxLarge
  have hyy := naturalDiagonalScale_hypotheses_of_threshold m hm hyLarge
  exact norm_normalizedHermiteCrossKernel_sub_gramLeading_le
    m hm hx hy hxx.1 hyy.1 hxx.2 hyy.2

/-- Thresholded remainder estimate with the complete positive spatial
coefficient and both inverse-endpoint factors exposed. -/
theorem norm_normalizedHermiteCrossKernel_sub_gramLeading_le_explicit
    (m : ℕ) (hm : 1 ≤ m) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hxLarge : normalizedCrossNaturalScaleThreshold m ≤ x ^ 2)
    (hyLarge : normalizedCrossNaturalScaleThreshold m ≤ y ^ 2) :
    ‖normalizedHermiteCrossKernel m hm x y -
        normalizedCrossSpatialLeadingTerm m x y‖ ≤
      normalizedCrossSpatialErrorConstant m *
        (gramNormalization m *
          (x ^ 2 * y ^ 2) ^ ((m : ℝ) - 1 / 4) /
            (x ^ 2 + y ^ 2) ^ (2 * m)) *
          ((x ^ 2)⁻¹ + (y ^ 2)⁻¹) := by
  have h :=
    norm_normalizedHermiteCrossKernel_sub_gramLeading_le_of_threshold
      m hm hx hy hxLarge hyLarge
  rw [norm_normalizedCrossSpatialLeadingTerm m hm hx hy,
    normalizationError_signedSquare] at h
  exact h

/-- The inverse three-quarter power of a signed-square coordinate.  Its
square is the summable inverse-three-halves weight used below. -/
def inverseThreeQuarterSignedSquareWeight (x : ℝ) : ℝ :=
  |signedSquare x| ^ (-(3 / 4 : ℝ))

/-- Product of the two fixed positive constants in the explicit spatial
remainder estimate. -/
def normalizedCrossSquareSummableConstant (m : ℕ) : ℝ :=
  normalizedCrossSpatialErrorConstant m * gramNormalization m

theorem normalizedCrossSquareSummableConstant_nonneg
    (m : ℕ) (hm : 1 ≤ m) :
    0 ≤ normalizedCrossSquareSummableConstant m := by
  exact mul_nonneg
    (normalizedCrossSpatialErrorConstant_nonneg m hm)
    (gramNormalization_pos hm).le

/-- The positive spatial power and the two endpoint inverses are bounded by
the separable inverse-three-quarter weights.  This is the algebraic step
that makes the squared remainder matrix summable. -/
theorem spatialRemainderKernel_le_inverseThreeQuarter
    (n : ℕ) {S T : ℝ} (hS : 0 < S) (hT : 0 < T) :
    (S * T) ^ (((n + 1 : ℕ) : ℝ) - 1 / 4) /
          (S + T) ^ (2 * (n + 1)) * (S⁻¹ + T⁻¹) ≤
      S ^ (-(3 / 4 : ℝ)) * T ^ (-(3 / 4 : ℝ)) := by
  let A := S * T
  let B := S + T
  have hA : 0 < A := by simpa only [A] using mul_pos hS hT
  have hB : 0 < B := by simpa only [B] using add_pos hS hT
  have hAB : A ≤ B ^ 2 := by
    dsimp only [A, B]
    nlinarith [sq_nonneg S, sq_nonneg T]
  have hpow : A ^ n ≤ B ^ (2 * n) := by
    calc
      A ^ n ≤ (B ^ 2) ^ n := pow_le_pow_left₀ hA.le hAB n
      _ = B ^ (2 * n) := by rw [← pow_mul]
  have hratio : A ^ n / B ^ (2 * n) ≤ 1 := by
    rw [div_le_one (pow_pos hB _)]
    exact hpow
  have hsqrt : A ^ (1 / 2 : ℝ) ≤ B := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
    exact ⟨hB.le, hAB⟩
  have htail : A ^ (-(1 / 4 : ℝ)) / B ≤
      A ^ (-(3 / 4 : ℝ)) := by
    rw [div_le_iff₀ hB]
    have hsplit : A ^ (-(1 / 4 : ℝ)) =
        A ^ (-(3 / 4 : ℝ)) * A ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hA]
      congr 1
      ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hsqrt
      (Real.rpow_nonneg hA.le _)
  have hratio0 : 0 ≤ A ^ n / B ^ (2 * n) := by positivity
  have htail0 : 0 ≤ A ^ (-(1 / 4 : ℝ)) / B := by positivity
  have hfact :
      (S * T) ^ (((n + 1 : ℕ) : ℝ) - 1 / 4) /
            (S + T) ^ (2 * (n + 1)) * (S⁻¹ + T⁻¹) =
        (A ^ n / B ^ (2 * n)) * (A ^ (-(1 / 4 : ℝ)) / B) := by
    have hexponent : (((n + 1 : ℕ) : ℝ) - 1 / 4) =
        (n : ℝ) + 3 / 4 := by push_cast; ring
    have hthree : A ^ (3 / 4 : ℝ) / A =
        A ^ (-(1 / 4 : ℝ)) := by
      calc
        A ^ (3 / 4 : ℝ) / A = A ^ (3 / 4 : ℝ) / A ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = A ^ ((3 / 4 : ℝ) - 1) := (Real.rpow_sub hA _ _).symm
        _ = A ^ (-(1 / 4 : ℝ)) := by
          congr 1
          ring
    rw [show S⁻¹ + T⁻¹ = B / A by
      simpa only [A, B] using inv_add_inv hS.ne' hT.ne',
      hexponent, Real.rpow_add hA, Real.rpow_natCast]
    rw [show (S + T) ^ (2 * (n + 1)) =
        B ^ (2 * n) * B ^ 2 by
      simp only [B]
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]]
    rw [show A ^ n * A ^ (3 / 4 : ℝ) /
          (B ^ (2 * n) * B ^ 2) * (B / A) =
        (A ^ n / B ^ (2 * n)) * ((A ^ (3 / 4 : ℝ) / A) / B) by
      field_simp [hA.ne', hB.ne']]
    rw [hthree]
  rw [hfact, ← Real.mul_rpow hS.le hT.le]
  calc
    A ^ n / B ^ (2 * n) * (A ^ (-(1 / 4 : ℝ)) / B) ≤
        1 * (A ^ (-(1 / 4 : ℝ)) / B) :=
      mul_le_mul_of_nonneg_right hratio htail0
    _ ≤ A ^ (-(3 / 4 : ℝ)) := by simpa using htail

/-- Thresholded normalized-kernel remainder bound in a separable form whose
square is summable on every separated carrier tail. -/
theorem norm_normalizedHermiteCrossKernel_sub_gramLeading_le_separable
    (m : ℕ) (hm : 1 ≤ m) {x y : ℝ}
    (hxLarge : normalizedCrossNaturalScaleThreshold m ≤ x ^ 2)
    (hyLarge : normalizedCrossNaturalScaleThreshold m ≤ y ^ 2) :
    ‖normalizedHermiteCrossKernel m hm x y -
        normalizedCrossSpatialLeadingTerm m x y‖ ≤
      normalizedCrossSquareSummableConstant m *
        inverseThreeQuarterSignedSquareWeight x *
          inverseThreeQuarterSignedSquareWeight y := by
  have hx2 : 0 < x ^ 2 := lt_of_lt_of_le (by norm_num)
    ((le_max_left (1 / 4 : ℝ) _).trans hxLarge)
  have hy2 : 0 < y ^ 2 := lt_of_lt_of_le (by norm_num)
    ((le_max_left (1 / 4 : ℝ) _).trans hyLarge)
  have hx : x ≠ 0 := (sq_pos_iff).mp hx2
  have hy : y ≠ 0 := (sq_pos_iff).mp hy2
  have hbase :=
    norm_normalizedHermiteCrossKernel_sub_gramLeading_le_explicit
      m hm hx hy hxLarge hyLarge
  have hkernel := spatialRemainderKernel_le_inverseThreeQuarter
    (m - 1) hx2 hy2
  have hmRewrite : m - 1 + 1 = m := by omega
  rw [hmRewrite] at hkernel
  refine hbase.trans ?_
  rw [normalizedCrossSquareSummableConstant,
    inverseThreeQuarterSignedSquareWeight,
    inverseThreeQuarterSignedSquareWeight,
    abs_signedSquare, abs_signedSquare, sq_abs, sq_abs]
  have hC : 0 ≤ normalizedCrossSpatialErrorConstant m *
      gramNormalization m :=
    normalizedCrossSquareSummableConstant_nonneg m hm
  calc
    normalizedCrossSpatialErrorConstant m *
          (gramNormalization m *
            (x ^ 2 * y ^ 2) ^ ((m : ℝ) - 1 / 4) /
              (x ^ 2 + y ^ 2) ^ (2 * m)) *
            ((x ^ 2)⁻¹ + (y ^ 2)⁻¹) =
        (normalizedCrossSpatialErrorConstant m * gramNormalization m) *
          ((x ^ 2 * y ^ 2) ^ ((m : ℝ) - 1 / 4) /
            (x ^ 2 + y ^ 2) ^ (2 * m) *
              ((x ^ 2)⁻¹ + (y ^ 2)⁻¹)) := by ring
    _ ≤ (normalizedCrossSpatialErrorConstant m * gramNormalization m) *
          ((x ^ 2) ^ (-(3 / 4 : ℝ)) *
            (y ^ 2) ^ (-(3 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left hkernel hC
    _ = (normalizedCrossSpatialErrorConstant m * gramNormalization m) *
          (x ^ 2) ^ (-(3 / 4 : ℝ)) *
            (y ^ 2) ^ (-(3 / 4 : ℝ)) := by ring

end

end MeyerGeneralProblem
