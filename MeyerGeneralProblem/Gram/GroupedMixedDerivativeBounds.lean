module

public import MeyerGeneralProblem.Gram.GroupedDerivativeBounds
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# First mixed derivatives of the actual Hermite resolvent

The Gaussian here is the already proved Mehler closed formula. Its
derivatives are integrated against the exact resolvent Laplace weight.
Signed-square pullbacks are stated separately on rays away from zero.
Gaussian absorption and neighboring-order interpolation yield a uniform
same-order weighted bound for the genuine derivative pair `(1,1)`.
Higher derivative pairs and differentiated asymptotic remainders remain
separate obligations.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Filter
open scoped Topology

/-- Actual logarithmic derivative of the Mehler Gaussian in its first
physical coordinate. -/
def groupedMehlerLogDerivative (r x y : ℝ) : ℝ :=
  -Real.pi * (2 * (1+r^2) * x - 4*r*y) / (1-r^2)

/-- The actual first physical derivative of the closed Mehler kernel. -/
def groupedMehlerDerivative (r x y : ℝ) : ℝ :=
  groupedMehlerLogDerivative r x y * normalizedHermiteMehlerClosed r x y

/-- The actual `(1,1)` physical derivative of the closed Mehler kernel. -/
def groupedMehlerMixedDerivative (r x y : ℝ) : ℝ :=
  (groupedMehlerLogDerivative r x y * groupedMehlerLogDerivative r y x +
    4*Real.pi*r/(1-r^2)) * normalizedHermiteMehlerClosed r x y

theorem normalizedHermiteMehlerClosed_comm (r x y : ℝ) :
    normalizedHermiteMehlerClosed r x y = normalizedHermiteMehlerClosed r y x := by
  unfold normalizedHermiteMehlerClosed
  congr 3
  ring

theorem hasDerivAt_normalizedHermiteMehlerClosed_left (r x y : ℝ) :
    HasDerivAt (fun z => normalizedHermiteMehlerClosed r z y)
      (groupedMehlerDerivative r x y) x := by
  have hq := ((((hasDerivAt_id x).pow 2).add_const (y^2)).const_mul (1+r^2)).sub
    (((hasDerivAt_id x).const_mul (4*r)).mul_const y)
  have h := (((hq.div_const (1-r^2)).const_mul (-Real.pi)).exp).const_mul
    (Real.sqrt 2 / Real.sqrt (1-r^2))
  apply h.congr_deriv
  dsimp [groupedMehlerDerivative, groupedMehlerLogDerivative, normalizedHermiteMehlerClosed]
  ring

theorem hasDerivAt_normalizedHermiteMehlerClosed_right (r x y : ℝ) :
    HasDerivAt (fun z => normalizedHermiteMehlerClosed r x z)
      (groupedMehlerDerivative r y x) y := by
  simpa only [normalizedHermiteMehlerClosed_comm r x] using
    hasDerivAt_normalizedHermiteMehlerClosed_left r y x

theorem hasDerivAt_groupedMehlerDerivative_right (r x y : ℝ) :
    HasDerivAt (fun z => groupedMehlerDerivative r x z)
      (groupedMehlerMixedDerivative r x y) y := by
  have hl := ((((hasDerivAt_id y).const_mul (4*r)).const_sub
    (2*(1+r^2)*x)).const_mul (-Real.pi)).div_const (1-r^2)
  have h := hl.mul (hasDerivAt_normalizedHermiteMehlerClosed_right r x y)
  apply h.congr_deriv
  dsimp [groupedMehlerMixedDerivative, groupedMehlerDerivative, groupedMehlerLogDerivative]
  rw [normalizedHermiteMehlerClosed_comm r y x]
  ring

theorem deriv_deriv_normalizedHermiteMehlerClosed (r x y : ℝ) :
    deriv (fun v => deriv (fun u => normalizedHermiteMehlerClosed r u v) x) y =
      groupedMehlerMixedDerivative r x y := by
  simp_rw [(hasDerivAt_normalizedHermiteMehlerClosed_left r x _).deriv]
  exact (hasDerivAt_groupedMehlerDerivative_right r x y).deriv

theorem normalizedHermiteMehlerClosed_nonneg (r x y : ℝ) :
    0 ≤ normalizedHermiteMehlerClosed r x y := by
  unfold normalizedHermiteMehlerClosed
  positivity

theorem normalizedHermiteMehlerClosed_le_prefactor
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x y : ℝ) :
    normalizedHermiteMehlerClosed r x y ≤ Real.sqrt 2 / Real.sqrt (1-r^2) := by
  have hq := mehlerSpatialRate_mul_sq_add_sq_le_quadratic hr0 hr1 x y
  have hnonneg : 0 ≤ ((1+r^2)*(x^2+y^2)-4*r*x*y)/(1-r^2) := by
    refine le_trans ?_ hq
    positivity
  apply mul_le_of_le_one_right (by positivity)
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) hnonneg)

theorem abs_groupedMehlerLogDerivative_le
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x y : ℝ) :
    |groupedMehlerLogDerivative r x y| ≤
      (4*Real.pi*(|x|+|y|))/(1-r^2) := by
  have hd : 0 < 1-r^2 := by nlinarith
  unfold groupedMehlerLogDerivative
  rw [abs_div, abs_mul, abs_neg, abs_of_pos Real.pi_pos, abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  calc
    _ ≤ Real.pi * (|2*(1+r^2)*x| + |4*r*y|) := by
      gcongr
      exact abs_sub _ _
    _ = Real.pi * (2*(1+r^2)*|x| + 4*r*|y|) := by
      simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2:ℝ)),
        abs_of_nonneg (by positivity : 0 ≤ 1+r^2),
        abs_of_nonneg (by positivity : 0 ≤ (4:ℝ)), abs_of_nonneg hr0]
    _ ≤ Real.pi * (4*|x| + 4*|y|) := by
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (abs_nonneg x)
        nlinarith
      · exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg y)
    _ = _ := by ring

/-- A polynomial spatial factor, with no node-gap denominator. -/
def groupedMehlerMixedBound (x y : ℝ) : ℝ :=
  (4*Real.pi*(|x|+|y|))^2 + 4*Real.pi

theorem groupedMehlerMixedBound_pos (x y : ℝ) : 0 < groupedMehlerMixedBound x y := by
  unfold groupedMehlerMixedBound
  positivity

theorem abs_groupedMehlerMixedDerivative_le_prefactor
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x y : ℝ) :
    |groupedMehlerMixedDerivative r x y| ≤
      (groupedMehlerMixedBound x y / (1-r^2)^2) *
        (Real.sqrt 2 / Real.sqrt (1-r^2)) := by
  have hd : 0 < 1-r^2 := by nlinarith
  have hx := abs_groupedMehlerLogDerivative_le hr0 hr1 x y
  have hy := abs_groupedMehlerLogDerivative_le hr0 hr1 y x
  rw [add_comm (|y|)] at hy
  have hcross : |4*Real.pi*r/(1-r^2)| ≤ 4*Real.pi/(1-r^2)^2 := by
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_div_iff₀ hd (pow_pos hd 2)).mpr
    have hrd : r*(1-r^2) ≤ 1 := by
      nlinarith [mul_nonneg hr0 (sq_nonneg r)]
    nlinarith [mul_nonneg (show 0 ≤ 4*Real.pi*(1-r^2) by positivity)
      (sub_nonneg.mpr hrd)]
  have hcoef : |groupedMehlerLogDerivative r x y * groupedMehlerLogDerivative r y x +
      4*Real.pi*r/(1-r^2)| ≤ groupedMehlerMixedBound x y/(1-r^2)^2 := by
    calc
      _ ≤ |groupedMehlerLogDerivative r x y| * |groupedMehlerLogDerivative r y x| +
          |4*Real.pi*r/(1-r^2)| := by
        simpa only [abs_mul] using abs_add_le
          (groupedMehlerLogDerivative r x y * groupedMehlerLogDerivative r y x)
          (4*Real.pi*r/(1-r^2))
      _ ≤ (4*Real.pi*(|x|+|y|)/(1-r^2))^2 + 4*Real.pi/(1-r^2)^2 := by
        apply add_le_add _ hcross
        calc
          _ ≤ (4*Real.pi*(|x|+|y|)/(1-r^2)) *
              (4*Real.pi*(|x|+|y|)/(1-r^2)) :=
            mul_le_mul hx hy (abs_nonneg _) (by positivity)
          _ = _ := (pow_two _).symm
      _ = _ := by unfold groupedMehlerMixedBound; rw [div_pow, ← add_div]
  rw [groupedMehlerMixedDerivative, abs_mul,
    abs_of_nonneg (normalizedHermiteMehlerClosed_nonneg r x y)]
  exact mul_le_mul hcoef (normalizedHermiteMehlerClosed_le_prefactor hr0 hr1 x y)
    (normalizedHermiteMehlerClosed_nonneg r x y)
    (div_nonneg (groupedMehlerMixedBound_pos x y).le (sq_nonneg _))

theorem inv_mehlerHeatDenominator_le {t : ℝ} (ht : 0 < t) :
    (1-Real.exp (-t)^2)⁻¹ ≤ (1+t)/t := by
  have he : Real.exp (-t)^2 = Real.exp (-(2*t)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have he0 : 0 < Real.exp (-(2*t)) := Real.exp_pos _
  have he1 : Real.exp (-(2*t)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := mul_exp_neg_le_one_sub_exp_neg (2*t)
  rw [he, inv_eq_one_div]
  apply (div_le_div_iff₀ (sub_pos.mpr he1) ht).mpr
  nlinarith

/-- Two physical derivatives cost at most one integer Hermite order in
the elementary local majorant. No reciprocal node gap occurs. -/
theorem mehlerHeatDenominator_sq_inv_mul_diagonalIntegrand_le
    (m : ℕ) (hm : 2 ≤ m) {t : ℝ} (ht : 0 < t) :
    (1-Real.exp (-t)^2)⁻¹^2 * hermiteResolventDiagonalIntegrand m 0 t ≤
      2 * (hermiteResolventDiagonalIntegrand m 0 t +
        hermiteResolventDiagonalIntegrand (m-1) 0 t) := by
  have he1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  have hd : 0 < 1-Real.exp (-t)^2 := by nlinarith [Real.exp_pos (-t)]
  have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hd.le) (inv_mehlerHeatDenominator_le ht) 2
  have hquot : ((1+t)/t)^2 ≤ 2*(1+(t⁻¹)^2) := by
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos ht 2)).mpr
    field_simp
    nlinarith [sq_nonneg (t-1)]
  have hbase := hermiteResolventDiagonalIntegrand_nonneg m 0 ht
  have hidentity : (t⁻¹)^2 * hermiteResolventDiagonalIntegrand m 0 t =
      hermiteResolventDiagonalIntegrand (m-1) 0 t := by
    unfold hermiteResolventDiagonalIntegrand
    rw [show 2*m-1 = (2*(m-1)-1)+2 by omega, pow_add]
    field_simp
  calc
    _ ≤ 2*(1+(t⁻¹)^2) * hermiteResolventDiagonalIntegrand m 0 t :=
      mul_le_mul_of_nonneg_right (hpow.trans hquot) hbase
    _ = _ := by rw [mul_assoc, add_mul, one_mul, hidentity]

/-- The real Mehler kernel with the exact order-`m` resolvent Laplace weight. -/
def groupedRawMehlerIntegrand (m : ℕ) (x y t : ℝ) : ℝ :=
  t^(2*m-1) * Real.exp (-t) * normalizedHermiteMehlerClosed (Real.exp (-t)) x y

/-- The first physical derivative with the same resolvent Laplace weight. -/
def groupedRawMehlerDerivativeIntegrand (m : ℕ) (x y t : ℝ) : ℝ :=
  t^(2*m-1) * Real.exp (-t) * groupedMehlerDerivative (Real.exp (-t)) x y

/-- The first mixed physical derivative with the exact Laplace weight. -/
def groupedRawMehlerMixedIntegrand (m : ℕ) (x y t : ℝ) : ℝ :=
  t^(2*m-1) * Real.exp (-t) * groupedMehlerMixedDerivative (Real.exp (-t)) x y

theorem norm_groupedRawMehlerIntegrand_le (m : ℕ) (x y : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖groupedRawMehlerIntegrand m x y t‖ ≤ hermiteResolventDiagonalIntegrand m 0 t := by
  have hr0 := (Real.exp_pos (-t)).le
  have hr1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  rw [groupedRawMehlerIntegrand, norm_mul, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (normalizedHermiteMehlerClosed_nonneg _ _ _)]
  simpa only [hermiteResolventDiagonalIntegrand, hermiteHeatDiagonalReal,
    zero_pow (by norm_num : 2 ≠ 0), mul_zero, Real.exp_zero, mul_one] using
    mul_le_mul_of_nonneg_left (normalizedHermiteMehlerClosed_le_prefactor hr0 hr1 x y)
      (show 0 ≤ t^(2*m-1)*Real.exp (-t) by positivity)

theorem norm_groupedRawMehlerMixedIntegrand_le
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖groupedRawMehlerMixedIntegrand m x y t‖ ≤
      (2*groupedMehlerMixedBound x y) *
        (hermiteResolventDiagonalIntegrand m 0 t +
          hermiteResolventDiagonalIntegrand (m-1) 0 t) := by
  have hr0 := (Real.exp_pos (-t)).le
  have hr1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  have h := abs_groupedMehlerMixedDerivative_le_prefactor hr0 hr1 x y
  rw [groupedRawMehlerMixedIntegrand, norm_mul, Real.norm_of_nonneg (by positivity),
    Real.norm_eq_abs]
  calc
    _ ≤ (t^(2*m-1)*Real.exp (-t)) *
        ((groupedMehlerMixedBound x y/(1-Real.exp (-t)^2)^2) *
          (Real.sqrt 2/Real.sqrt (1-Real.exp (-t)^2))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = groupedMehlerMixedBound x y * ((1-Real.exp (-t)^2)⁻¹^2 *
        hermiteResolventDiagonalIntegrand m 0 t) := by
      simp only [hermiteResolventDiagonalIntegrand, hermiteHeatDiagonalReal,
        zero_pow (by norm_num : 2 ≠ 0), mul_zero, Real.exp_zero, mul_one,
        div_eq_mul_inv, inv_pow]
      ring
    _ ≤ groupedMehlerMixedBound x y * (2 *
        (hermiteResolventDiagonalIntegrand m 0 t +
          hermiteResolventDiagonalIntegrand (m-1) 0 t)) :=
      mul_le_mul_of_nonneg_left
        (mehlerHeatDenominator_sq_inv_mul_diagonalIntegrand_le m hm ht)
        (groupedMehlerMixedBound_pos x y).le
    _ = _ := by ring

theorem integrable_groupedRawMehlerMixedIntegrand
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) :
    IntegrableOn (groupedRawMehlerMixedIntegrand m x y) (Set.Ioi 0) := by
  apply (((integrableOn_hermiteResolventDiagonalIntegrand m (by omega) 0).add
    (integrableOn_hermiteResolventDiagonalIntegrand (m-1) (by omega) 0)).const_mul
      (2*groupedMehlerMixedBound x y)).mono'
  · have hmeas : Measurable (groupedRawMehlerMixedIntegrand m x y) := by
      unfold groupedRawMehlerMixedIntegrand groupedMehlerMixedDerivative
        groupedMehlerLogDerivative normalizedHermiteMehlerClosed
      fun_prop
    exact hmeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_groupedRawMehlerMixedIntegrand_le m hm x y ht

theorem norm_groupedRawMehlerDerivativeIntegrand_le
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖groupedRawMehlerDerivativeIntegrand m x y t‖ ≤
      (8*Real.pi*(|x|+|y|)) *
        (hermiteResolventDiagonalIntegrand m 0 t +
          hermiteResolventDiagonalIntegrand (m-1) 0 t) := by
  have hr0 := (Real.exp_pos (-t)).le
  have hr1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  have hd : 0 < 1-Real.exp (-t)^2 := by nlinarith [Real.exp_pos (-t)]
  have hinv : 1 ≤ (1-Real.exp (-t)^2)⁻¹ := by
    apply (one_le_inv₀ hd).mpr
    nlinarith
  have hpow : (1-Real.exp (-t)^2)⁻¹ ≤ (1-Real.exp (-t)^2)⁻¹^2 := by
    nlinarith
  have h := norm_groupedRawMehlerIntegrand_le m x y ht
  have hlog := abs_groupedMehlerLogDerivative_le hr0 hr1 x y
  have hrewrite : groupedRawMehlerDerivativeIntegrand m x y t =
      groupedMehlerLogDerivative (Real.exp (-t)) x y * groupedRawMehlerIntegrand m x y t := by
    unfold groupedRawMehlerDerivativeIntegrand groupedRawMehlerIntegrand groupedMehlerDerivative
    ring
  rw [hrewrite, norm_mul, Real.norm_eq_abs]
  calc
    _ ≤ (4*Real.pi*(|x|+|y|)/(1-Real.exp (-t)^2)) *
        hermiteResolventDiagonalIntegrand m 0 t :=
      mul_le_mul hlog h (norm_nonneg _) (by positivity)
    _ ≤ (4*Real.pi*(|x|+|y|)) * ((1-Real.exp (-t)^2)⁻¹^2 *
        hermiteResolventDiagonalIntegrand m 0 t) := by
      rw [div_eq_mul_inv, mul_assoc]
      gcongr
      exact hermiteResolventDiagonalIntegrand_nonneg m 0 ht
    _ ≤ (4*Real.pi*(|x|+|y|)) * (2 *
        (hermiteResolventDiagonalIntegrand m 0 t +
          hermiteResolventDiagonalIntegrand (m-1) 0 t)) :=
      mul_le_mul_of_nonneg_left
        (mehlerHeatDenominator_sq_inv_mul_diagonalIntegrand_le m hm ht) (by positivity)
    _ = _ := by ring

theorem integrable_groupedRawMehlerIntegrand
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    IntegrableOn (groupedRawMehlerIntegrand m x y) (Set.Ioi 0) := by
  apply (integrableOn_hermiteResolventDiagonalIntegrand m hm 0).mono'
  · have hmeas : Measurable (groupedRawMehlerIntegrand m x y) := by
      unfold groupedRawMehlerIntegrand normalizedHermiteMehlerClosed
      fun_prop
    exact hmeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_groupedRawMehlerIntegrand_le m x y ht

theorem integrable_groupedRawMehlerDerivativeIntegrand
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) :
    IntegrableOn (groupedRawMehlerDerivativeIntegrand m x y) (Set.Ioi 0) := by
  apply (((integrableOn_hermiteResolventDiagonalIntegrand m (by omega) 0).add
    (integrableOn_hermiteResolventDiagonalIntegrand (m-1) (by omega) 0)).const_mul
      (8*Real.pi*(|x|+|y|))).mono'
  · have hmeas : Measurable (groupedRawMehlerDerivativeIntegrand m x y) := by
      unfold groupedRawMehlerDerivativeIntegrand groupedMehlerDerivative
        groupedMehlerLogDerivative normalizedHermiteMehlerClosed
      fun_prop
    exact hmeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_groupedRawMehlerDerivativeIntegrand_le m hm x y ht

/-- The real resolvent integral with its exact reciprocal factorial. -/
def groupedRawMehlerIntegral (m : ℕ) (x y : ℝ) : ℝ :=
  ((2*m-1).factorial : ℝ)⁻¹ *
    ∫ t : ℝ in Set.Ioi 0, groupedRawMehlerIntegrand m x y t

/-- The normalized integral representing the first physical derivative. -/
def groupedRawMehlerDerivativeIntegral (m : ℕ) (x y : ℝ) : ℝ :=
  ((2*m-1).factorial : ℝ)⁻¹ *
    ∫ t : ℝ in Set.Ioi 0, groupedRawMehlerDerivativeIntegrand m x y t

/-- The normalized integral representing the first mixed physical derivative. -/
def groupedRawMehlerMixedIntegral (m : ℕ) (x y : ℝ) : ℝ :=
  ((2*m-1).factorial : ℝ)⁻¹ *
    ∫ t : ℝ in Set.Ioi 0, groupedRawMehlerMixedIntegrand m x y t

/-- Exact correspondence with the pre-existing spectral resolvent kernel.
The integral family is not a replacement definition of that kernel. -/
theorem hermiteResolventKernel_eq_groupedRawMehlerIntegral
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    hermiteResolventKernel m x y = (groupedRawMehlerIntegral m x y : ℂ) := by
  rw [hermiteResolventKernel_eq_laplaceIntegral m hm x y]
  unfold groupedRawMehlerIntegral
  rw [Complex.ofReal_mul]
  congr 1
  calc
    _ = ∫ t : ℝ in Set.Ioi 0, (groupedRawMehlerIntegrand m x y t : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [hermiteHeatKernel_eq_closed ht]
      simp only [groupedRawMehlerIntegrand, Complex.ofReal_mul]
    _ = _ := integral_ofReal

theorem hasDerivAt_groupedRawMehlerIntegral_left
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) :
    HasDerivAt (fun z => groupedRawMehlerIntegral m z y)
      (groupedRawMehlerDerivativeIntegral m x y) x := by
  let C : ℝ := 8*Real.pi*(|x|+1+|y|)
  let B : ℝ → ℝ := fun t => C * (hermiteResolventDiagonalIntegrand m 0 t +
    hermiteResolventDiagonalIntegrand (m-1) 0 t)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => groupedRawMehlerIntegrand m z y t)
    (F' := fun z t => groupedRawMehlerDerivativeIntegrand m z y t)
    (bound := B) (μ := volume.restrict (Set.Ioi 0))
    (s := Metric.ball x 1) (x₀ := x) (Metric.ball_mem_nhds x (by norm_num))
    (Eventually.of_forall (fun z =>
      (integrable_groupedRawMehlerIntegrand m (by omega) z y).aestronglyMeasurable))
    (integrable_groupedRawMehlerIntegrand m (by omega) x y)
    (integrable_groupedRawMehlerDerivativeIntegrand m hm x y).aestronglyMeasurable
    ?_ (((integrableOn_hermiteResolventDiagonalIntegrand m (by omega) 0).add
      (integrableOn_hermiteResolventDiagonalIntegrand (m-1) (by omega) 0)).const_mul C)
    (Eventually.of_forall (fun t z hz =>
      (hasDerivAt_normalizedHermiteMehlerClosed_left (Real.exp (-t)) z y).const_mul
        (t^(2*m-1)*Real.exp (-t))))).2
  · exact h.const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hzabs : |z| ≤ |x|+1 := by
      have hd : |z-x| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hz
      have htriangle := abs_add_le (z-x) x
      rw [sub_add_cancel] at htriangle
      linarith
    refine (norm_groupedRawMehlerDerivativeIntegrand_le m hm z y ht).trans ?_
    dsimp [B, C]
    gcongr
    exact add_nonneg (hermiteResolventDiagonalIntegrand_nonneg m 0 ht)
      (hermiteResolventDiagonalIntegrand_nonneg (m-1) 0 ht)

theorem hasDerivAt_groupedRawMehlerDerivativeIntegral_right
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) :
    HasDerivAt (fun z => groupedRawMehlerDerivativeIntegral m x z)
      (groupedRawMehlerMixedIntegral m x y) y := by
  let C : ℝ := 2*((4*Real.pi*(|x|+|y|+1))^2+4*Real.pi)
  let B : ℝ → ℝ := fun t => C * (hermiteResolventDiagonalIntegrand m 0 t +
    hermiteResolventDiagonalIntegrand (m-1) 0 t)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => groupedRawMehlerDerivativeIntegrand m x z t)
    (F' := fun z t => groupedRawMehlerMixedIntegrand m x z t)
    (bound := B) (μ := volume.restrict (Set.Ioi 0))
    (s := Metric.ball y 1) (x₀ := y) (Metric.ball_mem_nhds y (by norm_num))
    (Eventually.of_forall (fun z =>
      (integrable_groupedRawMehlerDerivativeIntegrand m hm x z).aestronglyMeasurable))
    (integrable_groupedRawMehlerDerivativeIntegrand m hm x y)
    (integrable_groupedRawMehlerMixedIntegrand m hm x y).aestronglyMeasurable
    ?_ (((integrableOn_hermiteResolventDiagonalIntegrand m (by omega) 0).add
      (integrableOn_hermiteResolventDiagonalIntegrand (m-1) (by omega) 0)).const_mul C)
    (Eventually.of_forall (fun t z hz =>
      (hasDerivAt_groupedMehlerDerivative_right (Real.exp (-t)) x z).const_mul
        (t^(2*m-1)*Real.exp (-t))))).2
  · exact h.const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hzabs : |z| ≤ |y|+1 := by
      have hd : |z-y| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hz
      have htriangle := abs_add_le (z-y) y
      rw [sub_add_cancel] at htriangle
      linarith
    refine (norm_groupedRawMehlerMixedIntegrand_le m hm x z ht).trans ?_
    dsimp [B, C, groupedMehlerMixedBound]
    apply mul_le_mul_of_nonneg_right _
      (add_nonneg (hermiteResolventDiagonalIntegrand_nonneg m 0 ht)
        (hermiteResolventDiagonalIntegrand_nonneg (m-1) 0 ht))
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine add_le_add ?_ le_rfl
    apply pow_le_pow_left₀ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith

/-- The actual spectral kernel has this first mixed derivative, obtained
by two justified differentiations of its exact Laplace representation. -/
theorem deriv_deriv_hermiteResolventKernel
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) :
    deriv (fun v => deriv (fun u => hermiteResolventKernel m u v) x) y =
      (groupedRawMehlerMixedIntegral m x y : ℂ) := by
  simp_rw [hermiteResolventKernel_eq_groupedRawMehlerIntegral m (by omega)]
  have hfirst : ∀ v, deriv (fun u => (groupedRawMehlerIntegral m u v : ℂ)) x =
      (groupedRawMehlerDerivativeIntegral m x v : ℂ) := fun v =>
    (hasDerivAt_groupedRawMehlerIntegral_left m hm x v).ofReal_comp.deriv
  simp_rw [hfirst]
  exact (hasDerivAt_groupedRawMehlerDerivativeIntegral_right m hm x y).ofReal_comp.deriv

/-- An explicit finite-order constant for the local mixed-derivative
majorant. The spatial polynomial is kept separate. -/
def groupedRawMehlerMixedIntegralConstant (m : ℕ) : ℝ :=
  2 * ((2*m-1).factorial : ℝ)⁻¹ *
    ((∫ t : ℝ in Set.Ioi 0, hermiteResolventDiagonalIntegrand m 0 t) +
      ∫ t : ℝ in Set.Ioi 0, hermiteResolventDiagonalIntegrand (m-1) 0 t)

theorem groupedRawMehlerMixedIntegralConstant_nonneg (m : ℕ) :
    0 ≤ groupedRawMehlerMixedIntegralConstant m := by
  unfold groupedRawMehlerMixedIntegralConstant
  apply mul_nonneg (by positivity)
  apply add_nonneg <;> apply integral_nonneg_of_ae <;>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  · exact hermiteResolventDiagonalIntegrand_nonneg m 0 ht
  · exact hermiteResolventDiagonalIntegrand_nonneg (m-1) 0 ht

theorem norm_groupedRawMehlerMixedIntegral_le
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) :
    ‖groupedRawMehlerMixedIntegral m x y‖ ≤
      groupedRawMehlerMixedIntegralConstant m * groupedMehlerMixedBound x y := by
  unfold groupedRawMehlerMixedIntegral
  rw [norm_mul, Real.norm_of_nonneg (by positivity)]
  have hi := (integrableOn_hermiteResolventDiagonalIntegrand m (by omega) 0).add
    (integrableOn_hermiteResolventDiagonalIntegrand (m-1) (by omega) 0)
  calc
    _ ≤ ((2*m-1).factorial : ℝ)⁻¹ *
        ∫ t : ℝ in Set.Ioi 0, ‖groupedRawMehlerMixedIntegrand m x y t‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ ((2*m-1).factorial : ℝ)⁻¹ *
        ∫ t : ℝ in Set.Ioi 0, (2*groupedMehlerMixedBound x y) *
          (hermiteResolventDiagonalIntegrand m 0 t +
            hermiteResolventDiagonalIntegrand (m-1) 0 t) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_mono_ae (integrable_groupedRawMehlerMixedIntegrand m hm x y).norm
        (hi.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_groupedRawMehlerMixedIntegrand_le m hm x y ht
    _ = _ := by
      rw [integral_const_mul, integral_add
        (integrableOn_hermiteResolventDiagonalIntegrand m (by omega) 0)
        (integrableOn_hermiteResolventDiagonalIntegrand (m-1) (by omega) 0)]
      unfold groupedRawMehlerMixedIntegralConstant
      ring

theorem norm_deriv_deriv_hermiteResolventKernel_le
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) :
    ‖deriv (fun v => deriv (fun u => hermiteResolventKernel m u v) x) y‖ ≤
      groupedRawMehlerMixedIntegralConstant m * groupedMehlerMixedBound x y := by
  rw [deriv_deriv_hermiteResolventKernel m hm x y, Complex.norm_real]
  exact norm_groupedRawMehlerMixedIntegral_le m hm x y

/-- The inverse signed-square coordinate on a specified ray. Here
`ε² = 1` and `ε*s > 0`; thus `ε = -1` uses the actual increasing negative
signed-square coordinate, not an outward enumeration. -/
def groupedSignedSquareRayPoint (ε s : ℝ) : ℝ := ε * Real.sqrt (ε*s)

theorem hasDerivAt_groupedSignedSquareRayPoint
    {ε s : ℝ} (hε : ε^2 = 1) (hs : 0 < ε*s) :
    HasDerivAt (groupedSignedSquareRayPoint ε) (1/(2*Real.sqrt (ε*s))) s := by
  have h := ((((hasDerivAt_id s).const_mul ε).sqrt hs.ne').const_mul ε)
  apply h.congr_deriv
  dsimp
  rw [mul_one, ← mul_div_assoc, ← pow_two, hε]

theorem abs_groupedSignedSquareRayPoint
    {ε : ℝ} (hε : ε^2 = 1) (s : ℝ) :
    |groupedSignedSquareRayPoint ε s| = Real.sqrt (ε*s) := by
  have habs : |ε| = 1 := by nlinarith [sq_abs ε, abs_nonneg ε]
  simp only [groupedSignedSquareRayPoint, abs_mul, habs,
    abs_of_nonneg (Real.sqrt_nonneg _), one_mul]

theorem signedSquare_groupedSignedSquareRayPoint
    {ε s : ℝ} (hε : ε^2 = 1) (hs : 0 ≤ ε*s) :
    signedSquare (groupedSignedSquareRayPoint ε s) = s := by
  unfold signedSquare
  rw [abs_groupedSignedSquareRayPoint hε]
  unfold groupedSignedSquareRayPoint
  rw [mul_assoc, ← pow_two, Real.sq_sqrt hs, ← mul_assoc, ← pow_two, hε, one_mul]

/-- Exact first mixed derivative of the actual spectral kernel in
signed-square ray coordinates. Both coordinate derivatives have positive
Jacobian, including on the negative ray. -/
theorem deriv_deriv_hermiteResolventKernel_signedSquareRay
    (m : ℕ) (hm : 2 ≤ m) {ε η s t : ℝ}
    (hε : ε^2 = 1) (hη : η^2 = 1) (hs : 0 < ε*s) (ht : 0 < η*t) :
    deriv (fun v => deriv (fun u => hermiteResolventKernel m
      (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) s) t =
      ((groupedRawMehlerMixedIntegral m (groupedSignedSquareRayPoint ε s)
        (groupedSignedSquareRayPoint η t) /
          (4*Real.sqrt (ε*s)*Real.sqrt (η*t)) : ℝ) : ℂ) := by
  simp_rw [hermiteResolventKernel_eq_groupedRawMehlerIntegral m (by omega)]
  have hfirst (v : ℝ) :
      deriv (fun u => (groupedRawMehlerIntegral m (groupedSignedSquareRayPoint ε u)
        (groupedSignedSquareRayPoint η v) : ℂ)) s =
        ((groupedRawMehlerDerivativeIntegral m (groupedSignedSquareRayPoint ε s)
          (groupedSignedSquareRayPoint η v) / (2*Real.sqrt (ε*s)) : ℝ) : ℂ) := by
    have h := (hasDerivAt_groupedRawMehlerIntegral_left m hm
      (groupedSignedSquareRayPoint ε s) (groupedSignedSquareRayPoint η v)).comp s
        (hasDerivAt_groupedSignedSquareRayPoint hε hs)
    simpa only [Function.comp_def, mul_one_div] using h.ofReal_comp.deriv
  simp_rw [hfirst]
  have h := ((hasDerivAt_groupedRawMehlerDerivativeIntegral_right m hm
    (groupedSignedSquareRayPoint ε s) (groupedSignedSquareRayPoint η t)).comp t
      (hasDerivAt_groupedSignedSquareRayPoint hη ht)).div_const (2*Real.sqrt (ε*s))
  convert h.ofReal_comp.deriv using 1 <;>
    first | rfl | (congr 1; field_simp; ring)

/-- Quantitative mixed derivative estimate in true signed-square ray
coordinates. It is local/polynomial in the magnitudes, not a uniform tail
bound in the same-order diagonal weights. -/
theorem norm_deriv_deriv_hermiteResolventKernel_signedSquareRay_le
    (m : ℕ) (hm : 2 ≤ m) {ε η s t : ℝ}
    (hε : ε^2 = 1) (hη : η^2 = 1) (hs : 0 < ε*s) (ht : 0 < η*t) :
    ‖deriv (fun v => deriv (fun u => hermiteResolventKernel m
      (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) s) t‖ ≤
      (groupedRawMehlerMixedIntegralConstant m *
        groupedMehlerMixedBound (groupedSignedSquareRayPoint ε s)
          (groupedSignedSquareRayPoint η t)) /
            (4*Real.sqrt (ε*s)*Real.sqrt (η*t)) := by
  rw [deriv_deriv_hermiteResolventKernel_signedSquareRay m hm hε hη hs ht,
    Complex.norm_real, norm_div,
    Real.norm_of_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))]
  exact div_le_div_of_nonneg_right (norm_groupedRawMehlerMixedIntegral_le m hm _ _)
    (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

/-- Gaussian absorption for the mixed coefficient, retaining half of
both spatial damping terms. This is the analytic improvement over the
local polynomial majorant. -/
theorem grouped_gaussian_mixed_absorption
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (U V : ℝ) :
    |Real.pi^2*(a^2*U^2-b^2*V^2)+Real.pi*(b-a)| *
        Real.exp (-Real.pi/2*(a*U^2+b*V^2)) ≤
      4*Real.pi*b * Real.exp (-Real.pi/4*(a*U^2+b*V^2)) := by
  have hb : 0 ≤ b := ha.trans hab
  let z := Real.pi/4*(a*U^2+b*V^2)
  have hcoef : |Real.pi^2*(a^2*U^2-b^2*V^2)+Real.pi*(b-a)| ≤
      Real.pi*b*(4*z+1) := by
    have h₁ : |Real.pi^2*(a^2*U^2-b^2*V^2)| ≤
        Real.pi^2*(a^2*U^2+b^2*V^2) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity)])
    have h₂ : |Real.pi*(b-a)| ≤ Real.pi*b := by
      rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hab))]
      nlinarith [mul_nonneg Real.pi_pos.le ha]
    refine (abs_add_le _ _).trans ((add_le_add h₁ h₂).trans ?_)
    dsimp [z]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg Real.pi) ha)
      (sub_nonneg.mpr hab)) (sq_nonneg U)]
  have hexp : (4*z+1)*Real.exp (-2*z) ≤ 4*Real.exp (-z) := by
    have hlin : 4*z+1 ≤ 4*Real.exp z := by linarith [Real.add_one_le_exp z]
    refine (mul_le_mul_of_nonneg_right hlin (Real.exp_pos _).le).trans_eq ?_
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have heq : -Real.pi/2*(a*U^2+b*V^2) = -2*z := by dsimp [z]; ring
  have heq' : -Real.pi/4*(a*U^2+b*V^2) = -z := by dsimp [z]; ring
  rw [heq, heq']
  calc
    _ ≤ (Real.pi*b*(4*z+1))*Real.exp (-2*z) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ ≤ Real.pi*b*(4*Real.exp (-z)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hexp (mul_nonneg Real.pi_pos.le hb)
    _ = _ := by ring

/-- The actual mixed Mehler derivative costs only one inverse slow rate
after Gaussian absorption, while retaining a scaled genuine Mehler
kernel. This is suited to the half-order Cauchy--Schwarz bridge. -/
theorem abs_groupedMehlerMixedDerivative_le_scaledKernel
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x y : ℝ) :
    |groupedMehlerMixedDerivative r x y| ≤
      (4*Real.pi*((1+r)/(1-r))) *
        normalizedHermiteMehlerClosed r (x/Real.sqrt 2) (y/Real.sqrt 2) := by
  let a := (1-r)/(1+r)
  let b := (1+r)/(1-r)
  have hplus : 0 < 1+r := by linarith
  have hminus : 0 < 1-r := by linarith
  have hd : 0 < 1-r^2 := by nlinarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    rw [div_le_div_iff₀ hplus hminus]
    nlinarith
  have hcoef : groupedMehlerLogDerivative r x y * groupedMehlerLogDerivative r y x +
      4*Real.pi*r/(1-r^2) =
      Real.pi^2*(a^2*(x+y)^2-b^2*(x-y)^2)+Real.pi*(b-a) := by
    dsimp [groupedMehlerLogDerivative, a, b]
    field_simp
    ring
  have hquad := mehlerQuadratic_eq_sumDiff
    (show |r| < 1 by rwa [abs_of_nonneg hr0]) x y
  have hclosed : normalizedHermiteMehlerClosed r x y =
      Real.sqrt 2/Real.sqrt (1-r^2) *
        Real.exp (-Real.pi/2*(a*(x+y)^2+b*(x-y)^2)) := by
    unfold normalizedHermiteMehlerClosed
    rw [hquad]
    congr 2
    dsimp [a, b]
    field_simp
  have hsqrt : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have hscaled : normalizedHermiteMehlerClosed r (x/Real.sqrt 2) (y/Real.sqrt 2) =
      Real.sqrt 2/Real.sqrt (1-r^2) *
        Real.exp (-Real.pi/4*(a*(x+y)^2+b*(x-y)^2)) := by
    unfold normalizedHermiteMehlerClosed
    congr 2
    dsimp [a, b]
    field_simp
    rw [hsqrt]
    ring
  rw [groupedMehlerMixedDerivative, abs_mul, hcoef, hclosed,
    abs_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le), hscaled]
  calc
    _ = (Real.sqrt 2/Real.sqrt (1-r^2)) *
        (|Real.pi^2*(a^2*(x+y)^2-b^2*(x-y)^2)+Real.pi*(b-a)| *
          Real.exp (-Real.pi/2*(a*(x+y)^2+b*(x-y)^2))) := by ring
    _ ≤ (Real.sqrt 2/Real.sqrt (1-r^2)) *
        (4*Real.pi*b*Real.exp (-Real.pi/4*(a*(x+y)^2+b*(x-y)^2))) :=
      mul_le_mul_of_nonneg_left (grouped_gaussian_mixed_absorption ha hab (x+y) (x-y))
        (by positivity)
    _ = _ := by dsimp [b]; ring

theorem grouped_mehler_inverse_rate_le {t : ℝ} (ht : 0 < t) :
    (1+Real.exp (-t))/(1-Real.exp (-t)) ≤ 2*((1+t)/t) := by
  have he0 := Real.exp_pos (-t)
  have he1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  have h := mul_exp_neg_le_one_sub_exp_neg t
  have hinv : 1/(1-Real.exp (-t)) ≤ (1+t)/t := by
    rw [div_le_div_iff₀ (sub_pos.mpr he1) ht]
    nlinarith
  calc
    _ ≤ 2/(1-Real.exp (-t)) := div_le_div_of_nonneg_right (by linarith)
      (sub_pos.mpr he1).le
    _ ≤ _ := by rw [show 2/(1-Real.exp (-t)) = 2*(1/(1-Real.exp (-t))) by ring]; gcongr

/-- A free positive balancing parameter realizes the half-order
interpolation without assuming an additional fractional Hermite scale. -/
theorem grouped_inverse_time_balance {t A : ℝ} (ht : 0 < t) (hA : 0 < A) :
    (1+t)/t ≤ (1+A/2) + (1/(2*A))*(t⁻¹)^2 := by
  have h : 1/t ≤ A/2 + (1/(2*A))*(t⁻¹)^2 := by
    apply (div_le_iff₀ ht).mpr
    rw [← sub_nonneg]
    have hid : (A/2 + (1/(2*A))*(t⁻¹)^2)*t - 1 = (A*t-1)^2/(2*A*t) := by
      field_simp
      ring
    rw [hid]
    positivity
  have hleft : (1+t)/t = 1+1/t := by field_simp; ring
  rw [hleft]
  linarith

theorem groupedRawMehlerIntegrand_nonneg
    (m : ℕ) (x y : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ groupedRawMehlerIntegrand m x y t :=
  mul_nonneg (by positivity) (normalizedHermiteMehlerClosed_nonneg _ _ _)

/-- The genuine mixed integrand is controlled by two neighboring
integer-order integrands at the scaled physical points. The balancing
parameter can later be chosen from their spatial scales. -/
theorem norm_groupedRawMehlerMixedIntegrand_le_balanced
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) {t A : ℝ} (ht : 0 < t) (hA : 0 < A) :
    ‖groupedRawMehlerMixedIntegrand m x y t‖ ≤
      8*Real.pi*((1+A/2)*groupedRawMehlerIntegrand m (x/Real.sqrt 2) (y/Real.sqrt 2) t +
        (1/(2*A))*groupedRawMehlerIntegrand (m-1) (x/Real.sqrt 2) (y/Real.sqrt 2) t) := by
  have hr0 := (Real.exp_pos (-t)).le
  have hr1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  have hg := abs_groupedMehlerMixedDerivative_le_scaledKernel hr0 hr1 x y
  have htime := grouped_mehler_inverse_rate_le ht
  have hbalance := grouped_inverse_time_balance ht hA
  have hidentity : (t⁻¹)^2 * groupedRawMehlerIntegrand m
      (x/Real.sqrt 2) (y/Real.sqrt 2) t =
      groupedRawMehlerIntegrand (m-1) (x/Real.sqrt 2) (y/Real.sqrt 2) t := by
    unfold groupedRawMehlerIntegrand
    rw [show 2*m-1 = (2*(m-1)-1)+2 by omega, pow_add]
    field_simp
  rw [groupedRawMehlerMixedIntegrand, norm_mul, Real.norm_of_nonneg (by positivity),
    Real.norm_eq_abs]
  calc
    _ ≤ (t^(2*m-1)*Real.exp (-t)) * ((4*Real.pi*((1+Real.exp (-t))/(1-Real.exp (-t)))) *
        normalizedHermiteMehlerClosed (Real.exp (-t)) (x/Real.sqrt 2) (y/Real.sqrt 2)) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = 4*Real.pi*((1+Real.exp (-t))/(1-Real.exp (-t))) *
        groupedRawMehlerIntegrand m (x/Real.sqrt 2) (y/Real.sqrt 2) t := by
      unfold groupedRawMehlerIntegrand
      ring
    _ ≤ 8*Real.pi*((1+t)/t) *
        groupedRawMehlerIntegrand m (x/Real.sqrt 2) (y/Real.sqrt 2) t := by
      apply mul_le_mul_of_nonneg_right _ (groupedRawMehlerIntegrand_nonneg m _ _ ht)
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr htime)]
    _ ≤ 8*Real.pi*((1+A/2)+(1/(2*A))*(t⁻¹)^2) *
        groupedRawMehlerIntegrand m (x/Real.sqrt 2) (y/Real.sqrt 2) t := by
      gcongr
      exact groupedRawMehlerIntegrand_nonneg m _ _ ht
    _ = _ := by rw [← hidentity]; ring

theorem norm_groupedRawMehlerMixedIntegral_le_balanced
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) {A : ℝ} (hA : 0 < A) :
    ‖groupedRawMehlerMixedIntegral m x y‖ ≤ 8*Real.pi*
      ((1+A/2)*groupedRawMehlerIntegral m (x/Real.sqrt 2) (y/Real.sqrt 2) +
        (1/(2*A))*(((2*(m-1)-1).factorial : ℝ)/((2*m-1).factorial : ℝ))*
          groupedRawMehlerIntegral (m-1) (x/Real.sqrt 2) (y/Real.sqrt 2)) := by
  unfold groupedRawMehlerMixedIntegral
  rw [norm_mul, Real.norm_of_nonneg (by positivity)]
  have hi₁ := (integrable_groupedRawMehlerIntegrand m (by omega) (x/Real.sqrt 2)
    (y/Real.sqrt 2)).const_mul (1+A/2)
  have hi₂ := (integrable_groupedRawMehlerIntegrand (m-1) (by omega) (x/Real.sqrt 2)
    (y/Real.sqrt 2)).const_mul (1/(2*A))
  calc
    _ ≤ ((2*m-1).factorial : ℝ)⁻¹ *
        ∫ t : ℝ in Set.Ioi 0, ‖groupedRawMehlerMixedIntegrand m x y t‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ ((2*m-1).factorial : ℝ)⁻¹ *
        ∫ t : ℝ in Set.Ioi 0, 8*Real.pi*
          ((1+A/2)*groupedRawMehlerIntegrand m (x/Real.sqrt 2) (y/Real.sqrt 2) t +
            (1/(2*A))*groupedRawMehlerIntegrand (m-1) (x/Real.sqrt 2) (y/Real.sqrt 2) t) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_mono_ae (integrable_groupedRawMehlerMixedIntegrand m hm x y).norm
        ((hi₁.add hi₂).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_groupedRawMehlerMixedIntegrand_le_balanced m hm x y ht hA
    _ = _ := by
      rw [integral_const_mul, integral_add hi₁ hi₂]
      simp only [integral_const_mul, groupedRawMehlerIntegral]
      field_simp

theorem groupedRawMehlerIntegral_le_diagonalScales
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    groupedRawMehlerIntegral m x y ≤ hermiteRawNormalizationConstant m *
      (hermiteDiagonalScale x * hermiteDiagonalScale y)^(hermiteResolventHalfShape m/2) := by
  have h := norm_hermiteResolventKernel_le_diagonalScales m hm x y
  rw [hermiteResolventKernel_eq_groupedRawMehlerIntegral m hm x y, Complex.norm_real] at h
  have he : Real.exp (-(Real.pi/2)*abs (x*abs x-y*abs y)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) (abs_nonneg _)
  refine (le_abs_self (groupedRawMehlerIntegral m x y)).trans (h.trans ?_)
  have hc := hermiteRawNormalizationConstant_pos hm
  calc
    _ ≤ hermiteRawNormalizationConstant m * 1 *
        (hermiteDiagonalScale x * hermiteDiagonalScale y)^(hermiteResolventHalfShape m/2) := by
      gcongr
      exact Real.rpow_nonneg (mul_nonneg (hermiteDiagonalScale_pos x).le
        (hermiteDiagonalScale_pos y).le) _
    _ = _ := by rw [mul_one]

theorem grouped_rpow_balance
    {P R S : ℝ} (hP : 0 < P) (hP1 : P ≤ 1) (hR : 0 ≤ R) (_hS : 0 ≤ S) (a : ℝ) :
    (1+P^(-(1/2:ℝ))/2)*(R*P^(a/2)) +
      (1/(2*P^(-(1/2:ℝ))))*(S*P^((a-2)/2)) ≤
      ((3/2:ℝ)*R+(1/2:ℝ)*S)*P^((a-1)/2) := by
  have hp₁ : P^(-(1/2:ℝ))*P^(a/2) = P^((a-1)/2) := by
    rw [← Real.rpow_add hP]
    congr 1
    ring
  have hp₂ : (P^(-(1/2:ℝ)))⁻¹*P^((a-2)/2) = P^((a-1)/2) := by
    rw [← Real.rpow_neg hP.le, neg_neg, ← Real.rpow_add hP]
    congr 1
    ring
  have hp₃ : P^(a/2) ≤ P^((a-1)/2) :=
    Real.rpow_le_rpow_of_exponent_ge hP hP1 (by linarith)
  calc
    _ = R*P^(a/2) + (R/2)*(P^(-(1/2:ℝ))*P^(a/2)) +
        (S/2)*((P^(-(1/2:ℝ)))⁻¹*P^((a-2)/2)) := by
      simp only [one_div, mul_inv_rev]
      ring
    _ = R*P^(a/2) + (R/2)*P^((a-1)/2) + (S/2)*P^((a-1)/2) := by
      rw [hp₁, hp₂]
    _ ≤ R*P^((a-1)/2) + (R/2)*P^((a-1)/2) + (S/2)*P^((a-1)/2) := by
      gcongr
    _ = _ := by ring

/-- A spatially uniform constant from balancing neighboring resolvent orders. -/
def groupedRawMehlerWeightedMixedConstant (m : ℕ) : ℝ :=
  8*Real.pi*((3/2:ℝ)*hermiteRawNormalizationConstant m +
    (1/2:ℝ)*(((2*(m-1)-1).factorial : ℝ)/((2*m-1).factorial : ℝ))*
      hermiteRawNormalizationConstant (m-1))

theorem groupedRawMehlerWeightedMixedConstant_pos (m : ℕ) (hm : 2 ≤ m) :
    0 < groupedRawMehlerWeightedMixedConstant m := by
  unfold groupedRawMehlerWeightedMixedConstant
  have := hermiteRawNormalizationConstant_pos (m := m) (by omega)
  have := hermiteRawNormalizationConstant_pos (m := m-1) (by omega)
  positivity

/-- First mixed derivative with the sharp interpolated spatial power.
Unlike the local bound, its constant is independent of both coordinates. -/
theorem norm_groupedRawMehlerMixedIntegral_le_spatialScale
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) :
    ‖groupedRawMehlerMixedIntegral m x y‖ ≤
      groupedRawMehlerWeightedMixedConstant m *
        (hermiteDiagonalScale (x/Real.sqrt 2) * hermiteDiagonalScale (y/Real.sqrt 2))^
          ((hermiteResolventHalfShape m-1)/2) := by
  let P := hermiteDiagonalScale (x/Real.sqrt 2) * hermiteDiagonalScale (y/Real.sqrt 2)
  have hP : 0 < P := mul_pos (hermiteDiagonalScale_pos _) (hermiteDiagonalScale_pos _)
  have hP1 : P ≤ 1 := by
    exact mul_le_one₀ (hermiteDiagonalScale_le_one _) (hermiteDiagonalScale_pos _).le
      (hermiteDiagonalScale_le_one _)
  have hA : 0 < P^(-(1/2:ℝ)) := Real.rpow_pos_of_pos hP _
  have h := norm_groupedRawMehlerMixedIntegral_le_balanced m hm x y hA
  have hmshape : hermiteResolventHalfShape (m-1) = hermiteResolventHalfShape m-2 := by
    unfold hermiteResolventHalfShape
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
    ring
  have hl := groupedRawMehlerIntegral_le_diagonalScales (m-1) (by omega)
    (x/Real.sqrt 2) (y/Real.sqrt 2)
  rw [hmshape] at hl
  have hu := groupedRawMehlerIntegral_le_diagonalScales m (by omega)
    (x/Real.sqrt 2) (y/Real.sqrt 2)
  have hc := hermiteRawNormalizationConstant_pos (m := m) (by omega)
  have hlc := hermiteRawNormalizationConstant_pos (m := m-1) (by omega)
  refine h.trans ?_
  change _ ≤ groupedRawMehlerWeightedMixedConstant m * P^((hermiteResolventHalfShape m-1)/2)
  calc
    _ ≤ 8*Real.pi*((1+P^(-(1/2:ℝ))/2)*(hermiteRawNormalizationConstant m *
          P^(hermiteResolventHalfShape m/2)) + (1/(2*P^(-(1/2:ℝ))))*
          ((((2*(m-1)-1).factorial : ℝ)/((2*m-1).factorial : ℝ))*
            hermiteRawNormalizationConstant (m-1)*P^((hermiteResolventHalfShape m-2)/2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hu (by positivity)
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hl
          (show 0 ≤ (1/(2*P^(-(1/2:ℝ))))*
            (((2*(m-1)-1).factorial : ℝ)/((2*m-1).factorial : ℝ)) by positivity)
    _ ≤ _ := by
      have hb := grouped_rpow_balance hP hP1 hc.le
        (show 0 ≤ (((2*(m-1)-1).factorial : ℝ)/((2*m-1).factorial : ℝ))*
          hermiteRawNormalizationConstant (m-1) by positivity) (hermiteResolventHalfShape m)
      convert mul_le_mul_of_nonneg_left hb (show 0 ≤ 8*Real.pi by positivity) using 1 <;>
        first | rfl | (unfold groupedRawMehlerWeightedMixedConstant; ring)

theorem grouped_scaledDiagonalScale_le (x : ℝ) :
    hermiteDiagonalScale (x/Real.sqrt 2) ≤ 2*hermiteDiagonalScale x := by
  unfold hermiteDiagonalScale
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  rw [inv_eq_one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg x]

theorem grouped_scaledDiagonalScale_inv_half_le (x y : ℝ) :
    (hermiteDiagonalScale (x/Real.sqrt 2) * hermiteDiagonalScale (y/Real.sqrt 2))^
      (-(1/2:ℝ)) ≤ (1+|x|)*(1+|y|) := by
  let P := hermiteDiagonalScale (x/Real.sqrt 2) * hermiteDiagonalScale (y/Real.sqrt 2)
  have hp : 0 < P := mul_pos (hermiteDiagonalScale_pos _) (hermiteDiagonalScale_pos _)
  have hx : 1+(x/Real.sqrt 2)^2 ≤ (1+|x|)^2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    nlinarith [sq_abs x, abs_nonneg x]
  have hy : 1+(y/Real.sqrt 2)^2 ≤ (1+|y|)^2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    nlinarith [sq_abs y, abs_nonneg y]
  have hsquare : (P^(-(1/2:ℝ)))^2 = P⁻¹ := by
    rw [← Real.rpow_mul_natCast hp.le]
    norm_num
    exact Real.rpow_neg_one P
  have hinv : P⁻¹ ≤ ((1+|x|)*(1+|y|))^2 := by
    dsimp [P, hermiteDiagonalScale]
    rw [mul_inv_rev, inv_inv, inv_inv, mul_pow]
    nlinarith [mul_le_mul hx hy (show 0 ≤ 1+(y/Real.sqrt 2)^2 by positivity)
      (sq_nonneg (1+|x|))]
  have hnonneg := (Real.rpow_pos_of_pos hp (-(1/2:ℝ))).le
  change P^(-(1/2:ℝ)) ≤ _
  nlinarith [show 0 ≤ (1+|x|)*(1+|y|) by positivity]

theorem grouped_diagonalScale_floor_le_norm_mul
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    hermiteDiagonalFloorConstant m *
      (hermiteDiagonalScale x * hermiteDiagonalScale y)^(hermiteResolventHalfShape m/2) ≤
        ‖hermitePointMass m hm x‖ * ‖hermitePointMass m hm y‖ := by
  let P := hermiteDiagonalScale x * hermiteDiagonalScale y
  have hp : 0 < P := mul_pos (hermiteDiagonalScale_pos _) (hermiteDiagonalScale_pos _)
  have hsq : (hermiteDiagonalFloorConstant m * P^(hermiteResolventHalfShape m/2))^2 =
      hermiteDiagonalFloorConstant m^2 * P^hermiteResolventHalfShape m := by
    rw [mul_pow, ← Real.rpow_mul_natCast hp.le]
    congr 2
    push_cast
    ring
  have hle : hermiteDiagonalFloorConstant m^2 * P^hermiteResolventHalfShape m ≤
      (‖hermitePointMass m hm x‖*‖hermitePointMass m hm y‖)^2 := by
    rw [mul_pow, ← mul_hermitePointMassDiagonalFloor_eq m hm x y]
    exact mul_le_mul (hermitePointMassDiagonalFloor_le_norm_sq m hm x)
      (hermitePointMassDiagonalFloor_le_norm_sq m hm y)
      (hermitePointMassDiagonalFloor_pos m y).le (sq_nonneg _)
  have hl : 0 ≤ hermiteDiagonalFloorConstant m * P^(hermiteResolventHalfShape m/2) :=
    mul_nonneg (hermiteDiagonalFloorConstant_pos m).le (Real.rpow_pos_of_pos hp _).le
  have hr : 0 ≤ ‖hermitePointMass m hm x‖*‖hermitePointMass m hm y‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  change hermiteDiagonalFloorConstant m * P^(hermiteResolventHalfShape m/2) ≤ _
  nlinarith

/-- A coordinate-independent constant for the genuine same-order
weighted first mixed derivative estimate. -/
def groupedHermiteMixedDerivativeConstant (m : ℕ) : ℝ :=
  groupedRawMehlerWeightedMixedConstant m * (4:ℝ)^(hermiteResolventHalfShape m/2) /
    hermiteDiagonalFloorConstant m

theorem groupedHermiteMixedDerivativeConstant_pos (m : ℕ) (hm : 2 ≤ m) :
    0 < groupedHermiteMixedDerivativeConstant m := by
  unfold groupedHermiteMixedDerivativeConstant
  have := groupedRawMehlerWeightedMixedConstant_pos m hm
  have := hermiteDiagonalFloorConstant_pos m
  positivity

/-- The genuine `(1,1)` physical derivative obeys the same-order weighted
bound. This is a proved first-pair instance of the grouped source's crude
mixed derivative estimate, not a uniform-estimate assumption. -/
theorem norm_groupedRawMehlerMixedIntegral_le_weighted
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) :
    ‖groupedRawMehlerMixedIntegral m x y‖ ≤
      groupedHermiteMixedDerivativeConstant m * ((1+|x|)*(1+|y|)) *
        (‖hermitePointMass m (by omega) x‖ * ‖hermitePointMass m (by omega) y‖) := by
  let P := hermiteDiagonalScale (x/Real.sqrt 2) * hermiteDiagonalScale (y/Real.sqrt 2)
  let Q := hermiteDiagonalScale x * hermiteDiagonalScale y
  let a := hermiteResolventHalfShape m
  have hp : 0 < P := mul_pos (hermiteDiagonalScale_pos _) (hermiteDiagonalScale_pos _)
  have hq : 0 < Q := mul_pos (hermiteDiagonalScale_pos _) (hermiteDiagonalScale_pos _)
  have ha : 0 ≤ a/2 := div_nonneg (hermiteResolventHalfShape_pos (by omega : 1 ≤ m)).le
    (by norm_num)
  have hPQ : P ≤ 4*Q := by
    have h := mul_le_mul (grouped_scaledDiagonalScale_le x) (grouped_scaledDiagonalScale_le y)
      (hermiteDiagonalScale_pos _).le (mul_nonneg (by norm_num) (hermiteDiagonalScale_pos x).le)
    simpa only [P, Q] using h.trans_eq (by ring)
  have hpow : P^(a/2) ≤ (4:ℝ)^(a/2)*Q^(a/2) := by
    calc
      _ ≤ (4*Q)^(a/2) := Real.rpow_le_rpow hp.le hPQ ha
      _ = _ := Real.mul_rpow (by norm_num) hq.le
  have hfactor : P^((a-1)/2) = P^(-(1/2:ℝ))*P^(a/2) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  have hfloor : Q^(a/2) ≤
      (‖hermitePointMass m (by omega) x‖*‖hermitePointMass m (by omega) y‖) /
        hermiteDiagonalFloorConstant m := by
    apply (le_div_iff₀ (hermiteDiagonalFloorConstant_pos m)).mpr
    simpa only [mul_comm, Q, a] using grouped_diagonalScale_floor_le_norm_mul m (by omega) x y
  have hc := (groupedRawMehlerWeightedMixedConstant_pos m hm).le
  refine (norm_groupedRawMehlerMixedIntegral_le_spatialScale m hm x y).trans ?_
  change groupedRawMehlerWeightedMixedConstant m * P^((a-1)/2) ≤ _
  rw [hfactor]
  calc
    _ ≤ groupedRawMehlerWeightedMixedConstant m *
        (((1+|x|)*(1+|y|))*((4:ℝ)^(a/2)*Q^(a/2))) := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact mul_le_mul (grouped_scaledDiagonalScale_inv_half_le x y) hpow
        (Real.rpow_pos_of_pos hp _).le (by positivity)
    _ ≤ groupedRawMehlerWeightedMixedConstant m * (((1+|x|)*(1+|y|))*
        ((4:ℝ)^(a/2)*((‖hermitePointMass m (by omega) x‖*‖hermitePointMass m (by omega) y‖) /
          hermiteDiagonalFloorConstant m))) := by gcongr
    _ = _ := by unfold groupedHermiteMixedDerivativeConstant; dsimp [a]; ring

/-- The same physical-coordinate estimate directly on the pre-existing
spectral resolvent kernel. -/
theorem norm_deriv_deriv_hermiteResolventKernel_le_weighted
    (m : ℕ) (hm : 2 ≤ m) (x y : ℝ) :
    ‖deriv (fun v => deriv (fun u => hermiteResolventKernel m u v) x) y‖ ≤
      groupedHermiteMixedDerivativeConstant m * ((1+|x|)*(1+|y|)) *
        (‖hermitePointMass m (by omega) x‖ * ‖hermitePointMass m (by omega) y‖) := by
  rw [deriv_deriv_hermiteResolventKernel m hm x y, Complex.norm_real]
  exact norm_groupedRawMehlerMixedIntegral_le_weighted m hm x y

/-- A coordinate- and gap-independent same-order weighted bound for the
actual `(1,1)` signed-square derivative, on all four pairs of rays with
magnitudes at least one. No claim is made at the origin. -/
theorem norm_deriv_deriv_hermiteResolventKernel_signedSquareRay_le_weighted
    (m : ℕ) (hm : 2 ≤ m) {ε η s t : ℝ}
    (hε : ε^2 = 1) (hη : η^2 = 1) (hs : 1 ≤ ε*s) (ht : 1 ≤ η*t) :
    ‖deriv (fun v => deriv (fun u => hermiteResolventKernel m
      (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) s) t‖ ≤
      groupedHermiteMixedDerivativeConstant m *
        (‖hermitePointMass m (by omega) (groupedSignedSquareRayPoint ε s)‖ *
          ‖hermitePointMass m (by omega) (groupedSignedSquareRayPoint η t)‖) := by
  have hs0 : 0 < ε*s := lt_of_lt_of_le zero_lt_one hs
  have ht0 : 0 < η*t := lt_of_lt_of_le zero_lt_one ht
  have hsqrt : 1 ≤ Real.sqrt (ε*s) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hs
  have htqrt : 1 ≤ Real.sqrt (η*t) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ht
  have hd : 0 < 4*Real.sqrt (ε*s)*Real.sqrt (η*t) := by
    exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hs0)) (Real.sqrt_pos.mpr ht0)
  rw [deriv_deriv_hermiteResolventKernel_signedSquareRay m hm hε hη hs0 ht0,
    Complex.norm_real, norm_div, Real.norm_of_nonneg hd.le]
  apply (div_le_iff₀ hd).mpr
  refine (norm_groupedRawMehlerMixedIntegral_le_weighted m hm _ _).trans ?_
  rw [abs_groupedSignedSquareRayPoint hε, abs_groupedSignedSquareRayPoint hη]
  have hgeom : (1+Real.sqrt (ε*s))*(1+Real.sqrt (η*t)) ≤
      4*Real.sqrt (ε*s)*Real.sqrt (η*t) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt) (sub_nonneg.mpr htqrt)]
  have hc := (groupedHermiteMixedDerivativeConstant_pos m hm).le
  have hn : 0 ≤ ‖hermitePointMass m (by omega) (groupedSignedSquareRayPoint ε s)‖ *
      ‖hermitePointMass m (by omega) (groupedSignedSquareRayPoint η t)‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [mul_nonneg (mul_nonneg hc hn) (sub_nonneg.mpr hgeom)]

end

end MeyerGeneralProblem
