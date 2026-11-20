module

public import MeyerGeneralProblem.Distribution.CauchyDensityBoundary
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section

/-!
# Boundary phases of upper-half-plane Blaschke factors

Each factor has an increasing continuous real argument. On a bounded
real interval the increments for distant zeros are controlled by the
upper-half-plane Blaschke weight.
-/

namespace MeyerGeneralProblem

noncomputable section

open ComplexConjugate Filter Set
open scoped Topology

/-- The half-plane factor for a zero in the upper half-plane. -/
def upperHalfPlaneBlaschkeFactor (w z : ℂ) : ℂ := (z - w) / (z - conj w)

/-- A continuous argument for the factor on the real boundary. -/
def upperHalfPlaneBlaschkePhase (w : ℂ) (x : ℝ) : ℝ :=
  cayleyBoundaryAngle ((x - w.re) / w.im)

/-- The real argument exponentiates to the actual half-plane factor. -/
theorem exp_upperHalfPlaneBlaschkePhase {w : ℂ} (hw : 0 < w.im) (x : ℝ) :
    Complex.exp ((upperHalfPlaneBlaschkePhase w x : ℂ) * Complex.I) =
      upperHalfPlaneBlaschkeFactor w (x : ℂ) := by
  let t := (x - w.re) / w.im
  have hMul : w.im * t = x - w.re := by
    dsimp [t]
    field_simp [hw.ne']
  have hTop : (w.im : ℂ) * ((t : ℂ) - Complex.I) = (x : ℂ) - w := by
    apply Complex.ext
    · simpa only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, sub_zero, zero_mul] using hMul
    · simp [Complex.mul_im, Complex.sub_im]
  have hBot : (w.im : ℂ) * ((t : ℂ) + Complex.I) = (x : ℂ) - conj w := by
    apply Complex.ext
    · simpa only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.conj_re, add_zero, zero_mul, sub_zero] using hMul
    · simp [Complex.mul_im, Complex.sub_im]
  calc
    _ = circleMap 0 1 (cayleyBoundaryAngle t) := by
      simp only [upperHalfPlaneBlaschkePhase, t, circleMap_zero, Complex.ofReal_one, one_mul]
    _ = ((t : ℂ) - Complex.I) / ((t : ℂ) + Complex.I) := circleMap_cayleyBoundaryAngle t
    _ = ((w.im : ℂ) * ((t : ℂ) - Complex.I)) / ((w.im : ℂ) * ((t : ℂ) + Complex.I)) :=
      (mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hw.ne')).symm
    _ = _ := by rw [hTop, hBot]; rfl

/-- The boundary phase derivative is the positive Poisson kernel of the zero. -/
theorem hasDerivAt_upperHalfPlaneBlaschkePhase {w : ℂ} (hw : 0 < w.im) (x : ℝ) :
    HasDerivAt (upperHalfPlaneBlaschkePhase w)
      (2 * w.im / ((x - w.re) ^ 2 + w.im ^ 2)) x := by
  have hInner := ((hasDerivAt_id x).sub_const w.re).div_const w.im
  have hA := (Real.hasDerivAt_arctan' ((x - w.re) / w.im)).comp x hInner
  have h := (hA.const_mul 2).const_add Real.pi
  let b := 2 * ((1 + ((x - w.re) / w.im) ^ 2)⁻¹ * (1 / w.im))
  have hDer : HasDerivAt (upperHalfPlaneBlaschkePhase w) b x := h
  suffices he : b = 2 * w.im / ((x - w.re) ^ 2 + w.im ^ 2) by simpa only [he] using hDer
  have hDen : (x - w.re) ^ 2 + w.im ^ 2 ≠ 0 := (by positivity : 0 < (x - w.re) ^ 2 + w.im ^ 2).ne'
  have hDen' : 1 + ((x - w.re) / w.im) ^ 2 ≠ 0 := (by positivity : 0 < 1 + ((x - w.re) / w.im) ^ 2).ne'
  dsimp only [b]
  field_simp [hw.ne', hDen, hDen']
  ring

/-- Each upper-half-plane zero contributes a strictly increasing real phase. -/
theorem strictMono_upperHalfPlaneBlaschkePhase {w : ℂ} (hw : 0 < w.im) :
    StrictMono (upperHalfPlaneBlaschkePhase w) := by
  intro x y hxy
  have h := Real.arctan_strictMono (div_lt_div_of_pos_right (sub_lt_sub_right hxy w.re) hw)
  unfold upperHalfPlaneBlaschkePhase cayleyBoundaryAngle
  linarith only [h]

/-- The weight of a zero in the upper-half-plane Blaschke condition. -/
def upperHalfPlaneBlaschkeWeight (w : ℂ) : ℝ := w.im / (1 + ‖w‖ ^ 2)

private theorem norm_sq_real_sub (w : ℂ) (x : ℝ) :
    ‖(x : ℂ) - w‖ ^ 2 = (x - w.re) ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
  ring

private theorem upperHalfPlaneBlaschkePhase_derivative_le {w : ℂ} (hw : 0 < w.im) (x : ℝ) :
    2 * w.im / ((x - w.re) ^ 2 + w.im ^ 2) ≤ 2 / w.im := by
  apply (div_le_div_iff₀ (by positivity) hw).2
  nlinarith only [sq_nonneg (x - w.re)]

private theorem upperHalfPlaneBlaschkePhase_derivative_le_of_far {w : ℂ} (hw : 0 < w.im)
    {R x : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R) (hFar : 2 * R + 1 ≤ ‖w‖) :
    2 * w.im / ((x - w.re) ^ 2 + w.im ^ 2) ≤ 16 * upperHalfPlaneBlaschkeWeight w := by
  have hDiff : ‖w‖ - |x| ≤ ‖(x : ℂ) - w‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, norm_sub_rev] using norm_sub_norm_le w (x : ℂ)
  have hNorm : ‖w‖ ≤ 2 * ‖(x : ℂ) - w‖ := by linarith only [hFar, hx, hDiff]
  have hSq := pow_le_pow_left₀ (norm_nonneg w) hNorm 2
  have hW : (1 : ℝ) ≤ ‖w‖ := by linarith only [hFar, hR]
  have hWsq : (1 : ℝ) ≤ ‖w‖ ^ 2 := by simpa using pow_le_pow_left₀ zero_le_one hW 2
  have hD : 1 + ‖w‖ ^ 2 ≤ 8 * ((x - w.re) ^ 2 + w.im ^ 2) := by
    rw [← norm_sq_real_sub]
    nlinarith only [hSq, hWsq]
  rw [upperHalfPlaneBlaschkeWeight, ← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [mul_le_mul_of_nonneg_right hD hw.le]

/-- Uniform control of the real phase increments from a distant zero. -/
theorem abs_upperHalfPlaneBlaschkePhase_sub_le_of_far {w : ℂ} (hw : 0 < w.im)
    {R x y : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R) (hy : |y| ≤ R) (hFar : 2 * R + 1 ≤ ‖w‖) :
    |upperHalfPlaneBlaschkePhase w y - upperHalfPlaneBlaschkePhase w x| ≤
      (16 * upperHalfPlaneBlaschkeWeight w) * |y - x| := by
  have hD (t : ℝ) (_ : t ∈ Icc (-R) R) :=
    (hasDerivAt_upperHalfPlaneBlaschkePhase hw t).hasDerivWithinAt (s := Icc (-R) R)
  have hB (t : ℝ) (ht : t ∈ Icc (-R) R) :
      ‖2 * w.im / ((t - w.re) ^ 2 + w.im ^ 2)‖ ≤ 16 * upperHalfPlaneBlaschkeWeight w := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact upperHalfPlaneBlaschkePhase_derivative_le_of_far hw hR (abs_le.mpr ht) hFar
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hD hB (convex_Icc (-R) R) (abs_le.mp hx) (abs_le.mp hy)

/-- The phase sum uses each argument relative to its value at zero. -/
def upperHalfPlaneBlaschkePhaseSum {ι : Type*} (w : ι → ℂ) (x : ℝ) : ℝ :=
  ∑' i, (upperHalfPlaneBlaschkePhase (w i) x - upperHalfPlaneBlaschkePhase (w i) 0)

private theorem exists_summable_blaschke_phase_bound {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i))) {R : ℝ} (hR : 0 ≤ R) :
    ∃ b : ι → ℝ, Summable b ∧ ∀ i x, x ∈ Icc (-R) R →
      ‖upperHalfPlaneBlaschkePhase (w i) x - upperHalfPlaneBlaschkePhase (w i) 0‖ ≤ b i := by
  let d (i : ι) : ℝ :=
    if ‖w i‖ ≤ 2 * R + 1 then 2 / (w i).im else 16 * upperHalfPlaneBlaschkeWeight (w i)
  have hd : Summable d := by
    apply (hWeight.mul_left 16).congr_cofinite
    filter_upwards [(hFin (2 * R + 1)).compl_mem_cofinite] with i hi
    simp [d, (show ¬ ‖w i‖ ≤ 2 * R + 1 from hi)]
  have hB (i : ι) (x : ℝ) (hx : x ∈ Icc (-R) R) :
      ‖2 * (w i).im / ((x - (w i).re) ^ 2 + (w i).im ^ 2)‖ ≤ d i := by
    have hPos := hw i
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases hi : ‖w i‖ ≤ 2 * R + 1
    · simpa [d, hi] using upperHalfPlaneBlaschkePhase_derivative_le (hw i) x
    · simpa [d, hi] using
        upperHalfPlaneBlaschkePhase_derivative_le_of_far (hw i) hR (abs_le.mpr hx) (le_of_not_ge hi)
  have hZero : 0 ∈ Icc (-R) R := ⟨by linarith, hR⟩
  refine ⟨fun i => d i * R, hd.mul_right R, fun i x hx => ?_⟩
  have hD (y : ℝ) (_ : y ∈ Icc (-R) R) :=
    (hasDerivAt_upperHalfPlaneBlaschkePhase (hw i) y).hasDerivWithinAt (s := Icc (-R) R)
  have hδ : 0 ≤ d i := (norm_nonneg _).trans (hB i 0 hZero)
  refine (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hD (hB i) (convex_Icc (-R) R) hZero hx).trans ?_
  rw [sub_zero, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr hx) hδ

private theorem summable_upperHalfPlaneBlaschkePhase_increments {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i))) (x : ℝ) :
    Summable (fun i => upperHalfPlaneBlaschkePhase (w i) x - upperHalfPlaneBlaschkePhase (w i) 0) := by
  obtain ⟨b, hb, hB⟩ := exists_summable_blaschke_phase_bound hw hFin hWeight (abs_nonneg x)
  exact hb.of_norm_bounded (fun i => hB i x (abs_le.mp le_rfl))

/-- Under the Blaschke condition the real phase series is continuous. -/
theorem continuous_upperHalfPlaneBlaschkePhaseSum {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i))) :
    Continuous (upperHalfPlaneBlaschkePhaseSum w) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  let R := |x| + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hI : Icc (-R) R ∈ 𝓝 x := by
    rcases abs_le.mp (show |x| ≤ |x| from le_rfl) with ⟨hl, hr⟩
    dsimp [R]
    exact Icc_mem_nhds (by linarith only [hl]) (by linarith only [hr])
  obtain ⟨b, hb, hB⟩ := exists_summable_blaschke_phase_bound hw hFin hWeight hR
  have hCont (i : ι) : Continuous (upperHalfPlaneBlaschkePhase (w i)) :=
    continuous_cayleyBoundaryAngle.comp ((continuous_id.sub continuous_const).div_const _)
  have hC : ContinuousOn (upperHalfPlaneBlaschkePhaseSum w) (Icc (-R) R) :=
    continuousOn_tsum (fun i => ((hCont i).sub continuous_const).continuousOn) hb hB
  exact (hC x (mem_of_mem_nhds hI)).continuousAt hI

/-- The phase sum is nondecreasing on the real boundary. -/
theorem monotone_upperHalfPlaneBlaschkePhaseSum {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i))) :
    Monotone (upperHalfPlaneBlaschkePhaseSum w) := by
  intro x y hxy
  exact (summable_upperHalfPlaneBlaschkePhase_increments hw hFin hWeight x).tsum_le_tsum
    (fun i => sub_le_sub_right ((strictMono_upperHalfPlaneBlaschkePhase (hw i)).monotone hxy) _)
    (summable_upperHalfPlaneBlaschkePhase_increments hw hFin hWeight y)

/-- The nondecreasing phase exponentiates to the convergent product of
real-boundary factors normalized at zero. -/
theorem hasProd_upperHalfPlaneBlaschkeFactor_real {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i))) (x : ℝ) :
    HasProd (fun i => upperHalfPlaneBlaschkeFactor (w i) (x : ℂ) /
        upperHalfPlaneBlaschkeFactor (w i) 0)
      (Complex.exp ((upperHalfPlaneBlaschkePhaseSum w x : ℂ) * Complex.I)) := by
  let a (i : ι) := upperHalfPlaneBlaschkePhase (w i) x - upperHalfPlaneBlaschkePhase (w i) 0
  let E (y : ℝ) := Complex.exp ((y : ℂ) * Complex.I)
  have hSum : Tendsto (fun s : Finset ι => ∑ i ∈ s, a i) atTop
      (𝓝 (upperHalfPlaneBlaschkePhaseSum w x)) :=
    (summable_upperHalfPlaneBlaschkePhase_increments hw hFin hWeight x).hasSum
  have hE : Continuous E := Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  apply (hE.continuousAt.tendsto.comp hSum).congr
  intro s
  change Complex.exp (((∑ i ∈ s, a i : ℝ) : ℂ) * Complex.I) =
    ∏ i ∈ s, upperHalfPlaneBlaschkeFactor (w i) (x : ℂ) / upperHalfPlaneBlaschkeFactor (w i) 0
  rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  dsimp only [a]
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub,
    exp_upperHalfPlaneBlaschkePhase (hw i), exp_upperHalfPlaneBlaschkePhase (hw i), Complex.ofReal_zero]

end
end MeyerGeneralProblem
