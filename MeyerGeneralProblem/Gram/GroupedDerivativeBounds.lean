module

public import MeyerGeneralProblem.Gram.QuantitativeMehler
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Derivative bounds feeding grouped Hermite traces

The diagonal normalization is differentiated as an actual Laplace integral,
not as a formal asymptotic symbol. Its rate is uniformly bounded, so every
derivative has a genuine integrable majorant. These estimates are independent
of node gaps. Signed-square magnitude is used explicitly: on the negative
ray it is the negative of the increasing signed-square coordinate.

This is the diagonal-normalization slice only. The mixed derivatives of
the raw two-variable resolvent kernel, higher derivatives of the reciprocal
normalizer, and differentiated asymptotic remainders remain separate
obligations; no grouped Gram compactness theorem is asserted here.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Filter
open scoped Topology

/-- The bounded positive Laplace rate in the signed-square-magnitude diagonal. -/
def groupedHermiteDiagonalRate (t : ℝ) : ℝ :=
  2 * Real.pi * mehlerSpatialRate t

theorem groupedHermiteDiagonalRate_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ groupedHermiteDiagonalRate t := by
  unfold groupedHermiteDiagonalRate
  exact mul_nonneg (by positivity) (mehlerSpatialRate_pos ht).le

theorem groupedHermiteDiagonalRate_le {t : ℝ} (_ht : 0 < t) :
    groupedHermiteDiagonalRate t ≤ 2 * Real.pi := by
  have he : 0 < Real.exp (-t) := Real.exp_pos _
  have hrate : mehlerSpatialRate t ≤ 1 := by
    unfold mehlerSpatialRate
    rw [div_le_one (by positivity)]
    linarith
  exact mul_le_of_le_one_right (by positivity) hrate

/-- The exact derivative-moment integrand for the Hermite diagonal. -/
def groupedHermiteDiagonalMomentIntegrand (m i : ℕ) (s t : ℝ) : ℝ :=
  (-groupedHermiteDiagonalRate t)^i *
    hermiteResolventDiagonalIntegrand m 0 t *
      Real.exp (-groupedHermiteDiagonalRate t * s)

theorem norm_groupedHermiteDiagonalMomentIntegrand_le
    (m i : ℕ) (s : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖groupedHermiteDiagonalMomentIntegrand m i s t‖ ≤
      ((2*Real.pi)^i * Real.exp (2*Real.pi*|s|)) *
        hermiteResolventDiagonalIntegrand m 0 t := by
  have hb0 := groupedHermiteDiagonalRate_nonneg ht
  have hb := groupedHermiteDiagonalRate_le ht
  have hA := hermiteResolventDiagonalIntegrand_nonneg m 0 ht
  have he : -groupedHermiteDiagonalRate t * s ≤ 2*Real.pi*|s| := by
    calc
      -groupedHermiteDiagonalRate t * s ≤ groupedHermiteDiagonalRate t * |s| := by
        nlinarith [neg_le_abs s]
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (abs_nonneg s)
  simp only [groupedHermiteDiagonalMomentIntegrand, norm_mul, norm_pow, norm_neg,
    Real.norm_eq_abs, abs_of_nonneg hb0, abs_of_nonneg hA,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (2*Real.pi)^i * hermiteResolventDiagonalIntegrand m 0 t *
        Real.exp (2*Real.pi*|s|) := by gcongr
    _ = _ := by ring

theorem integrable_groupedHermiteDiagonalMomentIntegrand
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) (s : ℝ) :
    IntegrableOn (groupedHermiteDiagonalMomentIntegrand m i s) (Set.Ioi 0) := by
  apply ((integrableOn_hermiteResolventDiagonalIntegrand m hm 0).const_mul
    ((2*Real.pi)^i * Real.exp (2*Real.pi*|s|))).mono'
  · have hmeas : Measurable (groupedHermiteDiagonalMomentIntegrand m i s) := by
      unfold groupedHermiteDiagonalMomentIntegrand groupedHermiteDiagonalRate
        mehlerSpatialRate hermiteResolventDiagonalIntegrand hermiteHeatDiagonalReal
      fun_prop
    exact hmeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_groupedHermiteDiagonalMomentIntegrand_le m i s ht

/-- The moment integrals, including the actual order-zero diagonal value. -/
def groupedHermiteDiagonalMoment (m i : ℕ) (s : ℝ) : ℝ :=
  ((2*m-1).factorial : ℝ)⁻¹ *
    ∫ t : ℝ in Set.Ioi 0, groupedHermiteDiagonalMomentIntegrand m i s t

/-- The moment's zeroth member equals the actual squared point-mass norm
at signed-square magnitude `s`, with the exact factorial normalization. -/
theorem groupedHermiteDiagonalMoment_zero_eq_norm_sq
    (m : ℕ) (hm : 1 ≤ m) {s : ℝ} (hs : 0 ≤ s) :
    groupedHermiteDiagonalMoment m 0 s =
      ‖hermitePointMass m hm (Real.sqrt s)‖^2 := by
  rw [norm_hermitePointMass_sq_eq_realIntegral]
  unfold groupedHermiteDiagonalMoment
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [groupedHermiteDiagonalMomentIntegrand, pow_zero, one_mul,
    hermiteResolventDiagonalIntegrand, hermiteHeatDiagonalReal, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, Real.exp_zero, mul_one, groupedHermiteDiagonalRate, mehlerSpatialRate,
    Real.sq_sqrt hs]
  rw [show -(2*Real.pi*((1-Real.exp (-t))/(1+Real.exp (-t)))) * s =
    -Real.pi*(2*(1-Real.exp (-t))/(1+Real.exp (-t))*s) by ring]
  ring

theorem hasDerivAt_groupedHermiteDiagonalMomentIntegrand
    (m i : ℕ) (s t : ℝ) :
    HasDerivAt (fun z => groupedHermiteDiagonalMomentIntegrand m i z t)
      (groupedHermiteDiagonalMomentIntegrand m (i+1) s t) s := by
  have h := (((hasDerivAt_id s).const_mul (-groupedHermiteDiagonalRate t)).exp).const_mul
    ((-groupedHermiteDiagonalRate t)^i * hermiteResolventDiagonalIntegrand m 0 t)
  apply h.congr_deriv
  simp only [groupedHermiteDiagonalMomentIntegrand, pow_succ, id_eq, mul_one]
  ring

/-- Differentiation under the genuine positive-half-line integral, with an
explicit local integrable majorant valid for every derivative order. -/
theorem hasDerivAt_groupedHermiteDiagonalMoment
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) (s : ℝ) :
    HasDerivAt (groupedHermiteDiagonalMoment m i)
      (groupedHermiteDiagonalMoment m (i+1) s) s := by
  let C : ℝ := (2*Real.pi)^(i+1) * Real.exp (2*Real.pi*(|s|+1))
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => groupedHermiteDiagonalMomentIntegrand m i z t)
    (F' := fun z t => groupedHermiteDiagonalMomentIntegrand m (i+1) z t)
    (bound := fun t => C * hermiteResolventDiagonalIntegrand m 0 t)
    (μ := volume.restrict (Set.Ioi 0))
    (s := Metric.ball s 1) (x₀ := s) (Metric.ball_mem_nhds s (by norm_num))
    (Eventually.of_forall (fun z =>
      (integrable_groupedHermiteDiagonalMomentIntegrand m hm i z).aestronglyMeasurable))
    (integrable_groupedHermiteDiagonalMomentIntegrand m hm i s)
    (integrable_groupedHermiteDiagonalMomentIntegrand m hm (i+1) s).aestronglyMeasurable
    ?_ ((integrableOn_hermiteResolventDiagonalIntegrand m hm 0).const_mul C)
    (Eventually.of_forall (fun t z hz =>
      hasDerivAt_groupedHermiteDiagonalMomentIntegrand m i z t))).2
  · exact h.const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    refine (norm_groupedHermiteDiagonalMomentIntegrand_le m (i+1) z ht).trans ?_
    have hzabs : |z| ≤ |s|+1 := by
      have hd : |z-s| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hz
      have hztriangle := abs_add_le (z-s) s
      rw [sub_add_cancel] at hztriangle
      linarith
    dsimp only [C]
    gcongr
    exact hermiteResolventDiagonalIntegrand_nonneg m 0 ht

/-- All iterated diagonal derivatives are exactly the corresponding
Laplace moments. No derivative of an asymptotic error is inferred from a
value-level estimate. -/
theorem iteratedDeriv_groupedHermiteDiagonalMoment
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) :
    iteratedDeriv i (groupedHermiteDiagonalMoment m 0) = groupedHermiteDiagonalMoment m i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    exact (hasDerivAt_groupedHermiteDiagonalMoment m hm i s).deriv

/-- A gap-independent relative derivative bound for the actual diagonal.
This is a crude bound; it does not assert the stronger `s⁻ⁱ` tail factor. -/
theorem norm_groupedHermiteDiagonalMoment_le
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) (s : ℝ) :
    ‖groupedHermiteDiagonalMoment m i s‖ ≤
      (2*Real.pi)^i * groupedHermiteDiagonalMoment m 0 s := by
  unfold groupedHermiteDiagonalMoment
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [show (2*Real.pi)^i * (((2*m-1).factorial : ℝ)⁻¹ *
      ∫ t : ℝ in Set.Ioi 0, groupedHermiteDiagonalMomentIntegrand m 0 s t) =
    ((2*m-1).factorial : ℝ)⁻¹ *
      ((2*Real.pi)^i * ∫ t : ℝ in Set.Ioi 0,
        groupedHermiteDiagonalMomentIntegrand m 0 s t) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  apply integral_mono_ae
  · exact (integrable_groupedHermiteDiagonalMomentIntegrand m hm i s).norm
  · exact (integrable_groupedHermiteDiagonalMomentIntegrand m hm 0 s).const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hb0 := groupedHermiteDiagonalRate_nonneg ht
    have hb := groupedHermiteDiagonalRate_le ht
    have hA := hermiteResolventDiagonalIntegrand_nonneg m 0 ht
    simp only [groupedHermiteDiagonalMomentIntegrand, pow_zero, one_mul,
      norm_mul, norm_pow, norm_neg, Real.norm_eq_abs, abs_of_nonneg hb0,
      abs_of_nonneg hA, abs_of_pos (Real.exp_pos _)]
    rw [← mul_assoc]
    gcongr

/-- The elementary Laplace-moment estimate retaining the inverse-power
tail factor. The parameter is positive; no estimate at the signed-square
origin is inferred from it. -/
theorem grouped_pow_mul_exp_neg_le_factorial_half
    (i : ℕ) {b s : ℝ} (hb : 0 ≤ b) (hs : 0 < s) :
    b^i * Real.exp (-b*s) ≤
      ((i.factorial : ℝ) / (s/2)^i) * Real.exp (-b*(s/2)) := by
  have hr : 0 < s/2 := by positivity
  have hpoly := Real.pow_div_factorial_le_exp (b*(s/2)) (mul_nonneg hb hr.le) i
  have hpoly' : (b*(s/2))^i ≤ Real.exp (b*(s/2)) * (i.factorial : ℝ) :=
    (div_le_iff₀ (by positivity)).mp hpoly
  have hmul := mul_le_mul_of_nonneg_right hpoly' (Real.exp_pos (-b*s)).le
  have hsum : b*(s/2) + -b*s = -b*(s/2) := by ring
  have hcross : (b^i * Real.exp (-b*s)) * (s/2)^i ≤
      (i.factorial : ℝ) * Real.exp (-b*(s/2)) := by
    calc
      _ = (b*(s/2))^i * Real.exp (-b*s) := by rw [mul_pow]; ring
      _ ≤ _ := hmul.trans_eq (by rw [mul_assoc, mul_left_comm, ← Real.exp_add, hsum])
  have h := (le_div_iff₀ (pow_pos hr i)).mpr hcross
  simpa only [div_mul_eq_mul_div] using h

/-- The actual diagonal derivative at magnitude `s` is bounded by the
diagonal at `s/2` times the exact factorial/inverse-power tail factor. -/
theorem norm_groupedHermiteDiagonalMoment_le_half
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) {s : ℝ} (hs : 0 < s) :
    ‖groupedHermiteDiagonalMoment m i s‖ ≤
      ((i.factorial : ℝ) / (s/2)^i) * groupedHermiteDiagonalMoment m 0 (s/2) := by
  unfold groupedHermiteDiagonalMoment
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [show ((i.factorial : ℝ) / (s/2)^i) * (((2*m-1).factorial : ℝ)⁻¹ *
      ∫ t : ℝ in Set.Ioi 0, groupedHermiteDiagonalMomentIntegrand m 0 (s/2) t) =
    ((2*m-1).factorial : ℝ)⁻¹ *
      (((i.factorial : ℝ) / (s/2)^i) * ∫ t : ℝ in Set.Ioi 0,
        groupedHermiteDiagonalMomentIntegrand m 0 (s/2) t) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  apply integral_mono_ae
  · exact (integrable_groupedHermiteDiagonalMomentIntegrand m hm i s).norm
  · exact (integrable_groupedHermiteDiagonalMomentIntegrand m hm 0 (s/2)).const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hb := groupedHermiteDiagonalRate_nonneg ht
    have hA := hermiteResolventDiagonalIntegrand_nonneg m 0 ht
    simp only [groupedHermiteDiagonalMomentIntegrand, pow_zero, one_mul,
      norm_mul, norm_pow, norm_neg, Real.norm_eq_abs, abs_of_nonneg hb,
      abs_of_nonneg hA, abs_of_pos (Real.exp_pos _)]
    calc
      _ = (groupedHermiteDiagonalRate t^i * Real.exp (-groupedHermiteDiagonalRate t*s)) *
          hermiteResolventDiagonalIntegrand m 0 t := by ring
      _ ≤ (((i.factorial : ℝ) / (s/2)^i) *
          Real.exp (-groupedHermiteDiagonalRate t*(s/2))) *
          hermiteResolventDiagonalIntegrand m 0 t :=
        mul_le_mul_of_nonneg_right (grouped_pow_mul_exp_neg_le_factorial_half i hb hs) hA
      _ = _ := by ring

theorem groupedHermiteDiagonalMoment_zero_le_scale
    (m : ℕ) (hm : 1 ≤ m) {s : ℝ} (hs : 0 ≤ s) :
    groupedHermiteDiagonalMoment m 0 s ≤
      hermiteRawNormalizationConstant m * ((1+s)⁻¹)^hermiteResolventHalfShape m := by
  rw [groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm hs]
  have h := norm_hermiteResolventKernel_le_diagonalScales m hm (Real.sqrt s) (Real.sqrt s)
  rw [← inner_hermitePointMass_eq_resolventKernel m hm,
    inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _)] at h
  simp only [sub_self, abs_zero, mul_zero, Real.exp_zero, mul_one,
    hermiteDiagonalScale, Real.sq_sqrt hs] at h
  convert h using 1
  rw [← sq, ← Real.rpow_natCast_mul (by positivity)]
  congr 2
  push_cast
  ring

theorem groupedHermiteDiagonalMoment_zero_ge_scale
    (m : ℕ) (hm : 1 ≤ m) {s : ℝ} (hs : 0 ≤ s) :
    hermiteDiagonalFloorConstant m * ((1+s)⁻¹)^hermiteResolventHalfShape m ≤
      groupedHermiteDiagonalMoment m 0 s := by
  rw [groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm hs]
  have h := hermitePointMassDiagonalFloor_le_norm_sq m hm (Real.sqrt s)
  rw [hermitePointMassDiagonalFloor_eq_rpow m hm] at h
  simpa only [hermiteDiagonalScale, Real.sq_sqrt hs] using h

/-- Explicit comparison of the diagonal at two fixed-ratio magnitudes.
This constant depends on the Hermite order, never on a cluster gap. -/
def groupedHermiteDiagonalRatioConstant (m : ℕ) : ℝ :=
  hermiteRawNormalizationConstant m / hermiteDiagonalFloorConstant m *
    (2 : ℝ)^hermiteResolventHalfShape m

theorem groupedHermiteDiagonalRatioConstant_pos
    (m : ℕ) (hm : 1 ≤ m) : 0 < groupedHermiteDiagonalRatioConstant m := by
  unfold groupedHermiteDiagonalRatioConstant
  have := hermiteRawNormalizationConstant_pos hm
  have := hermiteDiagonalFloorConstant_pos m
  positivity

theorem groupedHermiteDiagonalMoment_half_le
    (m : ℕ) (hm : 1 ≤ m) {s : ℝ} (hs : 0 ≤ s) :
    groupedHermiteDiagonalMoment m 0 (s/2) ≤
      groupedHermiteDiagonalRatioConstant m * groupedHermiteDiagonalMoment m 0 s := by
  have hf := hermiteDiagonalFloorConstant_pos m
  have hr := hermiteRawNormalizationConstant_pos hm
  have hscale : (1+s/2)⁻¹ ≤ 2*(1+s)⁻¹ := by
    rw [inv_eq_one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  have hpow : ((1+s/2)⁻¹)^hermiteResolventHalfShape m ≤
      (2 : ℝ)^hermiteResolventHalfShape m * ((1+s)⁻¹)^hermiteResolventHalfShape m := by
    calc
      _ ≤ (2*(1+s)⁻¹)^hermiteResolventHalfShape m :=
        Real.rpow_le_rpow (by positivity) hscale (hermiteResolventHalfShape_pos hm).le
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)
  have hlower : ((1+s)⁻¹)^hermiteResolventHalfShape m ≤
      groupedHermiteDiagonalMoment m 0 s / hermiteDiagonalFloorConstant m := by
    apply (le_div_iff₀ hf).mpr
    simpa only [mul_comm] using groupedHermiteDiagonalMoment_zero_ge_scale m hm hs
  calc
    _ ≤ hermiteRawNormalizationConstant m * ((1+s/2)⁻¹)^hermiteResolventHalfShape m :=
      groupedHermiteDiagonalMoment_zero_le_scale m hm (by positivity)
    _ ≤ hermiteRawNormalizationConstant m *
        ((2 : ℝ)^hermiteResolventHalfShape m * ((1+s)⁻¹)^hermiteResolventHalfShape m) :=
      mul_le_mul_of_nonneg_left hpow hr.le
    _ ≤ hermiteRawNormalizationConstant m *
        ((2 : ℝ)^hermiteResolventHalfShape m *
          (groupedHermiteDiagonalMoment m 0 s / hermiteDiagonalFloorConstant m)) := by
      gcongr
    _ = _ := by unfold groupedHermiteDiagonalRatioConstant; ring

/-- The full all-order relative inverse-power derivative estimate for the
actual diagonal. It uses differentiation of the integral, not differentiation
of a previously proved value-level asymptotic. -/
theorem norm_groupedHermiteDiagonalMoment_le_relative
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) {s : ℝ} (hs : 0 < s) :
    ‖groupedHermiteDiagonalMoment m i s‖ ≤
      (groupedHermiteDiagonalRatioConstant m * (2:ℝ)^i * (i.factorial : ℝ) / s^i) *
        groupedHermiteDiagonalMoment m 0 s := by
  refine (norm_groupedHermiteDiagonalMoment_le_half m hm i hs).trans ?_
  calc
    _ ≤ ((i.factorial : ℝ) / (s/2)^i) *
        (groupedHermiteDiagonalRatioConstant m * groupedHermiteDiagonalMoment m 0 s) :=
      mul_le_mul_of_nonneg_left (groupedHermiteDiagonalMoment_half_le m hm hs.le)
        (by positivity)
    _ = _ := by rw [div_pow]; field_simp

/-- Exact derivative formula on the positive signed-square ray. -/
theorem iteratedDeriv_norm_hermitePointMass_sqrt_sq
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) {s : ℝ} (hs : 0 < s) :
    iteratedDeriv i (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖^2) s =
      groupedHermiteDiagonalMoment m i s := by
  have hlocal : (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖^2) =ᶠ[𝓝 s]
      groupedHermiteDiagonalMoment m 0 := by
    filter_upwards [Ioi_mem_nhds hs] with z hz
    exact (groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm hz.le).symm
  rw [hlocal.iteratedDeriv_eq i, iteratedDeriv_groupedHermiteDiagonalMoment m hm]

/-- The normalized diagonal derivative input used by grouped traces,
stated for the actual positive-ray point-mass norm. -/
theorem norm_iteratedDeriv_norm_hermitePointMass_sqrt_sq_le
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) {s : ℝ} (hs : 0 < s) :
    ‖iteratedDeriv i (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖^2) s‖ ≤
      (groupedHermiteDiagonalRatioConstant m * (2:ℝ)^i * (i.factorial : ℝ) / s^i) *
        ‖hermitePointMass m hm (Real.sqrt s)‖^2 := by
  rw [iteratedDeriv_norm_hermitePointMass_sqrt_sq m hm i hs,
    ← groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm hs.le]
  exact norm_groupedHermiteDiagonalMoment_le_relative m hm i hs

theorem norm_hermitePointMass_neg_sq (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    ‖hermitePointMass m hm (-x)‖^2 = ‖hermitePointMass m hm x‖^2 := by
  rw [norm_hermitePointMass_sq_eq_realIntegral, norm_hermitePointMass_sq_eq_realIntegral]
  simp only [hermiteResolventDiagonalIntegrand, hermiteHeatDiagonalReal, neg_sq]

/-- The corresponding exact derivative formula in the increasing
signed-square coordinate on the negative ray. The orientation factor
`(-1)^i` is retained explicitly. -/
theorem iteratedDeriv_norm_hermitePointMass_neg_sqrt_neg_sq
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) {s : ℝ} (hs : s < 0) :
    iteratedDeriv i (fun z => ‖hermitePointMass m hm (-Real.sqrt (-z))‖^2) s =
      (-1:ℝ)^i * groupedHermiteDiagonalMoment m i (-s) := by
  simp_rw [norm_hermitePointMass_neg_sq]
  rw [iteratedDeriv_comp_neg i (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖^2),
    iteratedDeriv_norm_hermitePointMass_sqrt_sq m hm i (neg_pos.mpr hs), smul_eq_mul]

/-- Negative-ray derivative bound, using signed-square magnitude `-s`.
The constant agrees with the positive ray and does not depend on node gaps. -/
theorem norm_iteratedDeriv_norm_hermitePointMass_neg_sqrt_neg_sq_le
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) {s : ℝ} (hs : s < 0) :
    ‖iteratedDeriv i (fun z => ‖hermitePointMass m hm (-Real.sqrt (-z))‖^2) s‖ ≤
      (groupedHermiteDiagonalRatioConstant m * (2:ℝ)^i * (i.factorial : ℝ) / (-s)^i) *
        ‖hermitePointMass m hm (-Real.sqrt (-s))‖^2 := by
  rw [iteratedDeriv_norm_hermitePointMass_neg_sqrt_neg_sq m hm i hs,
    norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_hermitePointMass_neg_sq,
    ← groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm (neg_pos.mpr hs).le]
  exact norm_groupedHermiteDiagonalMoment_le_relative m hm i (neg_pos.mpr hs)

/-- The first derivative of the actual normalization weight, without a
choice of an auxiliary equivalent norm. -/
theorem hasDerivAt_norm_hermitePointMass_sqrt
    (m : ℕ) (hm : 1 ≤ m) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖)
      (groupedHermiteDiagonalMoment m 1 s /
        (2 * ‖hermitePointMass m hm (Real.sqrt s)‖)) s := by
  have hp : 0 < ‖hermitePointMass m hm (Real.sqrt s)‖ :=
    norm_pos_iff.mpr (hermitePointMass_ne_zero m hm _)
  have hD : 0 < groupedHermiteDiagonalMoment m 0 s := by
    rw [groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm hs.le]
    positivity
  have heq : Real.sqrt (groupedHermiteDiagonalMoment m 0 s) =
      ‖hermitePointMass m hm (Real.sqrt s)‖ := by
    rw [groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm hs.le,
      Real.sqrt_sq (norm_nonneg _)]
  have h := (hasDerivAt_groupedHermiteDiagonalMoment m hm 0 s).sqrt hD.ne'
  rw [heq] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with z hz
  rw [groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm hz.le,
    Real.sqrt_sq (norm_nonneg _)]

/-- Gap-independent first relative derivative estimate for the actual
diagonal normalization weight. -/
theorem norm_deriv_norm_hermitePointMass_sqrt_le
    (m : ℕ) (hm : 1 ≤ m) {s : ℝ} (hs : 0 < s) :
    ‖deriv (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖) s‖ ≤
      (groupedHermiteDiagonalRatioConstant m / s) *
        ‖hermitePointMass m hm (Real.sqrt s)‖ := by
  have hp : 0 < ‖hermitePointMass m hm (Real.sqrt s)‖ :=
    norm_pos_iff.mpr (hermitePointMass_ne_zero m hm _)
  rw [(hasDerivAt_norm_hermitePointMass_sqrt m hm hs).deriv,
    norm_div, Real.norm_of_nonneg (mul_pos (by norm_num) hp).le]
  apply (div_le_iff₀ (mul_pos (by norm_num) hp)).mpr
  have h := norm_groupedHermiteDiagonalMoment_le_relative m hm 1 hs
  rw [groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm hs.le] at h
  convert h using 1 <;> norm_num <;> first | rfl | ring

/-- The reciprocal weight is differentiated genuinely, so its derivative
can be used when normalizing the raw Gram kernel. -/
theorem hasDerivAt_inv_norm_hermitePointMass_sqrt
    (m : ℕ) (hm : 1 ≤ m) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖⁻¹)
      (-(groupedHermiteDiagonalMoment m 1 s /
        (2 * ‖hermitePointMass m hm (Real.sqrt s)‖)) /
          ‖hermitePointMass m hm (Real.sqrt s)‖^2) s :=
  (hasDerivAt_norm_hermitePointMass_sqrt m hm hs).inv
    (norm_ne_zero_iff.mpr (hermitePointMass_ne_zero m hm _))

theorem norm_deriv_inv_norm_hermitePointMass_sqrt_le
    (m : ℕ) (hm : 1 ≤ m) {s : ℝ} (hs : 0 < s) :
    ‖deriv (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖⁻¹) s‖ ≤
      (groupedHermiteDiagonalRatioConstant m / s) *
        ‖hermitePointMass m hm (Real.sqrt s)‖⁻¹ := by
  have hp : 0 < ‖hermitePointMass m hm (Real.sqrt s)‖ :=
    norm_pos_iff.mpr (hermitePointMass_ne_zero m hm _)
  rw [(hasDerivAt_inv_norm_hermitePointMass_sqrt m hm hs).deriv,
    norm_div, norm_neg, Real.norm_of_nonneg (pow_pos hp 2).le]
  have h := norm_deriv_norm_hermitePointMass_sqrt_le m hm hs
  rw [(hasDerivAt_norm_hermitePointMass_sqrt m hm hs).deriv] at h
  refine (div_le_div_of_nonneg_right h (pow_pos hp 2).le).trans_eq ?_
  field_simp

end

end MeyerGeneralProblem
