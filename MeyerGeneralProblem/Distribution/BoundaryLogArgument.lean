module

public import MeyerGeneralProblem.Distribution.CauchyDensityBoundary
public import MeyerGeneralProblem.Distribution.DiskHerglotzWeak

@[expose] public section

/-!
# Weighted real-line estimates for the conjugate boundary integral

The Cayley coordinate transfers the angular weak bound to the
Cauchy weight on the real line. The resulting estimate supplies a
point with small conjugate value on every sufficiently long right
fractional window.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- The angular image of a real point on the unit circle. -/
def cayleyBoundaryPoint (x : ℝ) : ℂ :=
  circleMap 0 1 (cayleyBoundaryAngle x)

/-- The Cayley boundary map is continuous on the real line. -/
theorem continuous_cayleyBoundaryPoint : Continuous cayleyBoundaryPoint :=
  (continuous_circleMap 0 1).comp continuous_cayleyBoundaryAngle

/-- Each real boundary point maps to the unit circle. -/
theorem norm_cayleyBoundaryPoint (x : ℝ) : ‖cayleyBoundaryPoint x‖ = 1 := by
  simp [cayleyBoundaryPoint, norm_circleMap_zero]

/-- The real-line Cauchy weight in measure form. -/
def cauchyBoundaryMeasure : Measure ℝ :=
  volume.withDensity (fun x : ℝ => ENNReal.ofReal ((1 + x ^ 2)⁻¹))

/-- Angular length is exactly twice the Cauchy measure of its preimage. -/
theorem diskAngleMeasure_eq_two_mul_cauchyBoundaryMeasure_preimage
    {E : Set ℝ} (hE : MeasurableSet E) :
    diskAngleMeasure E = 2 * cauchyBoundaryMeasure (cayleyBoundaryAngle ⁻¹' E) := by
  have hPre : MeasurableSet (cayleyBoundaryAngle ⁻¹' E) :=
    continuous_cayleyBoundaryAngle.measurable hE
  rw [cauchyBoundaryMeasure, withDensity_apply _ hPre]
  calc
    _ = ∫⁻ θ in Ioo 0 (2 * Real.pi), E.indicator (fun _ => (1 : ℝ≥0∞)) θ :=
      (lintegral_indicator_one hE).symm
    _ = ∫⁻ x : ℝ, ENNReal.ofReal (2 / (1 + x ^ 2)) *
        E.indicator (fun _ => (1 : ℝ≥0∞)) (cayleyBoundaryAngle x) :=
      lintegral_cayleyBoundaryAngle _
    _ = _ := by
      rw [← lintegral_indicator hPre, ← lintegral_const_mul' _ _ (by norm_num)]
      apply lintegral_congr
      intro x
      by_cases hx : cayleyBoundaryAngle x ∈ E
      · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ cayleyBoundaryAngle ⁻¹' E from hx), mul_one]
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      · rw [indicator_of_notMem hx, indicator_of_notMem (show x ∉ cayleyBoundaryAngle ⁻¹' E from hx),
          mul_zero, mul_zero]

/-- The normalized Herglotz integral for a real boundary function, with
the factor 1/π in the upper-half-plane Poisson convention. -/
def weightedDiskHerglotzIntegral (u : ℝ → ℝ) : ℂ → ℂ :=
  diskHerglotzIntegral cayleyBoundaryPoint
    (fun x : ℝ => Real.pi⁻¹ * (u x / (1 + x ^ 2)))

/-- Subtraction of weighted real data commutes with the interior integral. -/
theorem weightedDiskHerglotzIntegral_sub {u v : ℝ → ℝ}
    (hu : Integrable (fun t : ℝ => u t / (1 + t ^ 2)))
    (hv : Integrable (fun t : ℝ => v t / (1 + t ^ 2))) {w : ℂ} (hw : ‖w‖ < 1) :
    weightedDiskHerglotzIntegral (fun t => u t - v t) w =
      weightedDiskHerglotzIntegral u w - weightedDiskHerglotzIntegral v w := by
  have hWeight : (fun t : ℝ => Real.pi⁻¹ * ((u t - v t) / (1 + t ^ 2))) =
      fun t => Real.pi⁻¹ * (u t / (1 + t ^ 2)) - Real.pi⁻¹ * (v t / (1 + t ^ 2)) := by
    funext t
    simp only [sub_div, mul_sub]
  simp only [weightedDiskHerglotzIntegral, hWeight]
  exact diskHerglotzIntegral_sub continuous_cayleyBoundaryPoint.measurable norm_cayleyBoundaryPoint
    (hu.const_mul _) (hv.const_mul _) hw

private theorem circleAverage_herglotzRieszKernel_unit {w : ℂ} (hw : ‖w‖ < 1) :
    Real.circleAverage (herglotzRieszKernel 0 w) 0 1 = 1 := by
  let F (z : ℂ) := z / (z - w)
  have hDen (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|) : z - w ≠ 0 := by
    refine sub_ne_zero.mpr fun he => ?_
    rw [Metric.mem_sphere, dist_zero_right, abs_one, he] at hz
    exact (ne_of_lt hw) hz
  have hFCont : ContinuousOn F (Metric.sphere (0 : ℂ) |(1 : ℝ)|) :=
    continuous_id.continuousOn.div (continuous_id.sub continuous_const).continuousOn hDen
  have hF : CircleIntegrable F 0 1 := hFCont.circleIntegrable'
  have hConst : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) (Metric.ball 0 |(1 : ℝ)|) :=
    (differentiableOn_const (1 : ℂ)).diffContOnCl_ball (subset_univ _)
  have hW : w ∈ Metric.ball (0 : ℂ) |(1 : ℝ)| := by
    simpa only [Metric.mem_ball, dist_zero_right, abs_one] using hw
  have hAvg : Real.circleAverage F 0 1 = 1 := by
    simpa only [F, sub_zero, smul_eq_mul, mul_one] using hConst.circleAverage_smul_div hW
  calc
    _ = Real.circleAverage (fun z : ℂ => (2 : ℂ) • F z - 1) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      simp only [herglotzRieszKernel_def, sub_zero, F, smul_eq_mul]
      field_simp [hDen z hz]
      ring
    _ = 1 := by
      have h2 : CircleIntegrable (fun z : ℂ => (2 : ℂ) • F z) 0 1 := hF.const_smul
      rw [Real.circleAverage_fun_sub h2 (circleIntegrable_const _ _ _),
        Real.circleAverage_fun_smul, hAvg, Real.circleAverage_const]
      norm_num

/-- A constant boundary datum contributes exactly that real constant
to the normalized Herglotz integral inside the unit disk. -/
theorem weightedDiskHerglotzIntegral_const {w : ℂ} (hw : ‖w‖ < 1) (c : ℝ) :
    weightedDiskHerglotzIntegral (fun _ => c) w = (c : ℂ) := by
  let P (θ : ℝ) := herglotzRieszKernel 0 w (circleMap 0 1 θ)
  calc
    _ = (↑(c / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, (2 / (1 + t ^ 2) : ℝ) • P (cayleyBoundaryAngle t) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine ae_of_all _ fun t => ?_
      change P (cayleyBoundaryAngle t) * (↑(Real.pi⁻¹ * (c / (1 + t ^ 2)) : ℝ) : ℂ) = _
      have hScalar : (c / (2 * Real.pi)) * (2 / (1 + t ^ 2)) =
          Real.pi⁻¹ * (c / (1 + t ^ 2)) := by
        field_simp [Real.pi_ne_zero, show 1 + t ^ 2 ≠ 0 by positivity]
      change _ = (↑(c / (2 * Real.pi) : ℝ) : ℂ) *
        ((↑(2 / (1 + t ^ 2) : ℝ) : ℂ) * P (cayleyBoundaryAngle t))
      rw [← mul_assoc, ← Complex.ofReal_mul, hScalar, mul_comm]
    _ = (c : ℂ) * Real.circleAverage (herglotzRieszKernel 0 w) 0 1 := by
      rw [← integral_cayleyBoundaryAngle P]
      change _ = (c : ℂ) * ((2 * Real.pi)⁻¹ • (∫ θ in 0..2 * Real.pi, P θ))
      rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_Ioc_eq_integral_Ioo,
        Algebra.smul_def, ← mul_assoc]
      change _ = (c : ℂ) * (↑((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (∫ θ in Ioo 0 (2 * Real.pi), P θ)
      rw [← Complex.ofReal_mul, ← div_eq_mul_inv]
    _ = _ := by rw [circleAverage_herglotzRieszKernel_unit hw, mul_one]

/-- Kolmogorov's weak estimate in the real-line Cauchy weight. The
boundary value is given in angular coordinates as a measurable
almost-everywhere radial limit. -/
theorem cauchyBoundaryMeasure_lt_abs_weightedDiskHerglotz_boundary
    {u v : ℝ → ℝ} (hu : Integrable (fun x : ℝ => u x / (1 + x ^ 2))) (hv : Measurable v)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (hr₁ : ∀ n, r n < 1)
    (hLim : ∀ᵐ θ ∂diskAngleMeasure, Tendsto
      (fun n : ℕ => (weightedDiskHerglotzIntegral u (circleMap 0 (r n) θ)).im) atTop (𝓝 (v θ)))
    {L : ℝ} (hL : 0 < L) :
    cauchyBoundaryMeasure {x | L < |v (cayleyBoundaryAngle x)|} ≤
      ENNReal.ofReal (4 * ((∫ x : ℝ, ‖u x / (1 + x ^ 2)‖) / L)) := by
  let E := {θ : ℝ | L < |v θ|}
  let g (x : ℝ) := Real.pi⁻¹ * (u x / (1 + x ^ 2))
  have hE : MeasurableSet E :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hv)
  have hg : Integrable g := hu.const_mul _
  have hNorm : (∫ x : ℝ, ‖g x‖) = Real.pi⁻¹ * ∫ x : ℝ, ‖u x / (1 + x ^ 2)‖ := by
    simp only [g, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr Real.pi_pos.le), integral_const_mul]
  have hD := diskAngleMeasure_lt_abs_diskHerglotz_boundary
    continuous_cayleyBoundaryPoint.measurable norm_cayleyBoundaryPoint hg hv r hr hr₁ hLim hL
  rw [hNorm] at hD
  have hPre : cauchyBoundaryMeasure (cayleyBoundaryAngle ⁻¹' E) =
      (2 : ℝ≥0∞)⁻¹ * diskAngleMeasure E := by
    rw [diskAngleMeasure_eq_two_mul_cauchyBoundaryMeasure_preimage hE]
    exact (ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)).symm
  change cauchyBoundaryMeasure (cayleyBoundaryAngle ⁻¹' E) ≤ _
  rw [hPre]
  have hMul : (2 : ℝ≥0∞)⁻¹ * diskAngleMeasure E ≤ (2 : ℝ≥0∞)⁻¹ *
      ENNReal.ofReal (8 * Real.pi * ((Real.pi⁻¹ * ∫ x : ℝ, ‖u x / (1 + x ^ 2)‖) / L)) := by
    gcongr
  refine hMul.trans_eq ?_
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp [Real.pi_ne_zero, hL.ne']
  ring

private theorem ofReal_fractional_window_le_cauchyBoundaryMeasure {ε r : ℝ}
    (hε₁ : ε ≤ 1) (hr : 1 ≤ r) :
    ENNReal.ofReal (ε / (2 * r)) ≤ cauchyBoundaryMeasure (Ioo ((1 - ε) * r) r) := by
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  let S := Ioo ((1 - ε) * r) r
  have hS : MeasurableSet S := measurableSet_Ioo
  have hLower (x : ℝ) (hx : x ∈ S) :
      ENNReal.ofReal ((2 * r ^ 2)⁻¹) ≤ ENNReal.ofReal ((1 + x ^ 2)⁻¹) := by
    have hx₀ : 0 ≤ x := (mul_nonneg (sub_nonneg.mpr hε₁) hr₀.le).trans hx.1.le
    have hx₁ : x ≤ r := hx.2.le
    have hSq : x ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hx₀ hx₁ 2
    have hrSq : 1 ≤ r ^ 2 := by simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hr 2
    exact ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity) (by linarith only [hSq, hrSq]))
  rw [cauchyBoundaryMeasure, withDensity_apply _ hS]
  calc
    _ = ∫⁻ _ in S, ENNReal.ofReal ((2 * r ^ 2)⁻¹) := by
      rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp [hr₀.ne']
      ring
    _ ≤ _ := setLIntegral_mono' hS hLower

/-- A sufficiently small weighted weak norm leaves a point with small
conjugate value in each right fractional window. A null exceptional
set may be excluded from the choice of point. -/
theorem exists_fractional_window_of_cauchyBoundaryMeasure_weak
    {v : ℝ → ℝ} {E : Set ℝ} (hE : cauchyBoundaryMeasure E = 0)
    {M ε δ r : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hr : 1 ≤ r)
    (hSmall : M < ε * δ / 8)
    (hWeak : cauchyBoundaryMeasure {x | δ * r < |v x|} ≤ ENNReal.ofReal (4 * (M / (δ * r)))) :
    ∃ x ∈ Ioo ((1 - ε) * r) r, x ∉ E ∧ |v x| ≤ δ * r := by
  by_contra! hNone
  let S := Ioo ((1 - ε) * r) r
  let B := {x : ℝ | δ * r < |v x|}
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  have hBR : 4 * (M / (δ * r)) < ε / (2 * r) := by
    rw [← mul_div_assoc]
    apply (div_lt_div_iff₀ (by positivity : 0 < δ * r) (by positivity : 0 < 2 * r)).mpr
    nlinarith only [mul_lt_mul_of_pos_right hSmall hr₀]
  have hSubset : S ⊆ B ∪ E := by
    intro x hx
    by_cases he : x ∈ E
    · exact Or.inr he
    · exact Or.inl (hNone x hx he)
  have hHi : cauchyBoundaryMeasure S < ENNReal.ofReal (ε / (2 * r)) :=
    calc
      _ ≤ cauchyBoundaryMeasure (B ∪ E) := measure_mono hSubset
      _ ≤ cauchyBoundaryMeasure B + cauchyBoundaryMeasure E := measure_union_le _ _
      _ = cauchyBoundaryMeasure B := by rw [hE, add_zero]
      _ ≤ ENNReal.ofReal (4 * (M / (δ * r))) := hWeak
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hBR
  exact (not_lt_of_ge (ofReal_fractional_window_le_cauchyBoundaryMeasure hε₁ hr)) hHi

private theorem ofReal_add_I_ne_zero (t : ℝ) : (t : ℂ) + Complex.I ≠ 0 := by
  intro h
  have hIm := congrArg Complex.im h
  simp at hIm

/-- The difference of two Cayley boundary points in real coordinates. -/
theorem cayleyBoundaryPoint_sub (t x : ℝ) :
    cayleyBoundaryPoint t - cayleyBoundaryPoint x =
      (2 * Complex.I * ((t : ℂ) - x)) / (((t : ℂ) + Complex.I) * ((x : ℂ) + Complex.I)) := by
  simp only [cayleyBoundaryPoint, circleMap_cayleyBoundaryAngle]
  field_simp [ofReal_add_I_ne_zero t, ofReal_add_I_ne_zero x]
  ring

theorem cayleyBoundaryPoint_injective : Function.Injective cayleyBoundaryPoint := by
  intro t x h
  by_contra hn
  have htx : (t : ℂ) - x ≠ 0 := sub_ne_zero.mpr (Complex.ofReal_injective.ne hn)
  have hn' : cayleyBoundaryPoint t - cayleyBoundaryPoint x ≠ 0 := by
    rw [cayleyBoundaryPoint_sub]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) htx)
      (mul_ne_zero (ofReal_add_I_ne_zero t) (ofReal_add_I_ne_zero x))
  exact hn' (sub_eq_zero.mpr h)

/-- The conjugate Herglotz kernel in the real boundary coordinate. -/
theorem herglotzRieszKernel_cayleyBoundaryPoint {t x : ℝ} (htx : t ≠ x) :
    herglotzRieszKernel 0 (cayleyBoundaryPoint x) (cayleyBoundaryPoint t) =
      Complex.I * (((1 + x * t) / (x - t) : ℝ) : ℂ) := by
  have hSum : cayleyBoundaryPoint t + cayleyBoundaryPoint x =
      (2 * ((t : ℂ) * x + 1)) / (((t : ℂ) + Complex.I) * ((x : ℂ) + Complex.I)) := by
    simp only [cayleyBoundaryPoint, circleMap_cayleyBoundaryAngle]
    field_simp [ofReal_add_I_ne_zero t, ofReal_add_I_ne_zero x]
    linear_combination -2 * Complex.I_sq
  have htx' : (t : ℂ) - x ≠ 0 := sub_ne_zero.mpr (Complex.ofReal_injective.ne htx)
  have hxt' : (x : ℂ) - t ≠ 0 := sub_ne_zero.mpr (Complex.ofReal_injective.ne htx.symm)
  simp only [herglotzRieszKernel_def, sub_zero, hSum, cayleyBoundaryPoint_sub,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_sub]
  field_simp [ofReal_add_I_ne_zero t, ofReal_add_I_ne_zero x, Complex.I_ne_zero, htx', hxt']
  linear_combination ((t : ℂ) * x + 1) * ((x : ℂ) - t) * Complex.I_sq

private theorem abs_boundary_herglotz_ratio_le {R t x : ℝ}
    (hR : 0 < R) (ht : |t| ≤ R) (hx : 2 * R < |x|) :
    |(1 + x * t) / (x - t)| ≤ 2 * R + R⁻¹ := by
  have hDiff := abs_sub_abs_le_abs_sub x t
  have hDen : R < |x - t| := by linarith
  have hNum : |1 + x * t| ≤ 1 + |x| * R := by
    calc
      _ ≤ |(1 : ℝ)| + |x * t| := abs_add_le _ _
      _ = 1 + |x| * |t| := by rw [abs_one, abs_mul]
      _ ≤ _ := by gcongr
  have hX : |x| ≤ 2 * |x - t| := by linarith
  rw [abs_div]
  apply (div_le_iff₀ (hR.trans hDen)).2
  calc
    _ ≤ 1 + |x| * R := hNum
    _ ≤ (2 * R + R⁻¹) * |x - t| := by
      have hInv : 1 ≤ R⁻¹ * |x - t| := by
        rw [← div_eq_inv_mul, le_div_iff₀ hR, one_mul]
        exact hDen.le
      have hProd := mul_le_mul_of_nonneg_right hX hR.le
      nlinarith only [hInv, hProd]

/-- A compactly supported weighted datum has a continuous Herglotz
integral at each point of the real boundary outside its support. -/
theorem continuousAt_weightedDiskHerglotzIntegral_of_compact
    {u : ℝ → ℝ} (hu : Integrable (fun t : ℝ => u t / (1 + t ^ 2)))
    {R x : ℝ} (hR : 0 ≤ R) (hx : R < |x|)
    (hsupp : ∀ᵐ t : ℝ, |t| ≤ R ∨ u t = 0) :
    ContinuousAt (weightedDiskHerglotzIntegral u) (cayleyBoundaryPoint x) := by
  let z := cayleyBoundaryPoint x
  let g (t : ℝ) := Real.pi⁻¹ * (u t / (1 + t ^ 2))
  let K (w : ℂ) (t : ℝ) := ((cayleyBoundaryPoint t + w) / (cayleyBoundaryPoint t - w)) * (g t : ℂ)
  have hg : Integrable g := hu.const_mul _
  have hz : ‖z‖ = 1 := norm_cayleyBoundaryPoint x
  have hNormCont : Continuous (fun t : ℝ => ‖cayleyBoundaryPoint t - z‖) :=
    (continuous_cayleyBoundaryPoint.sub continuous_const).norm
  obtain ⟨t₀, ht₀, hMin⟩ := (isCompact_Icc (a := -R) (b := R)).exists_isMinOn
    (nonempty_Icc.mpr (by linarith)) hNormCont.continuousOn
  let d := ‖cayleyBoundaryPoint t₀ - z‖
  have hd : 0 < d := by
    apply norm_pos_iff.mpr
    exact sub_ne_zero.mpr (cayleyBoundaryPoint_injective.ne fun he =>
      (not_le_of_gt hx) (abs_le.mpr (he ▸ ht₀)))
  have hLower (t : ℝ) (ht : |t| ≤ R) : d ≤ ‖cayleyBoundaryPoint t - z‖ :=
    hMin (abs_le.mp ht)
  have hEq : weightedDiskHerglotzIntegral u = fun w => ∫ t : ℝ, K w t := by
    funext w
    simp only [weightedDiskHerglotzIntegral, diskHerglotzIntegral, K, g,
      herglotzRieszKernel_def, sub_zero]
  rw [hEq]
  change Tendsto (fun w : ℂ => ∫ t : ℝ, K w t) (𝓝 z) (𝓝 (∫ t : ℝ, K z t))
  refine tendsto_integral_filter_of_dominated_convergence (l := 𝓝 z) (μ := volume) (F := K) (f := K z)
    (fun t : ℝ => ((2 + d / 2) / (d / 2)) * ‖g t‖) ?_ ?_ (hg.norm.const_mul _) ?_
  · apply Eventually.of_forall
    intro w
    have hC : Measurable (fun t : ℝ => (cayleyBoundaryPoint t + w) / (cayleyBoundaryPoint t - w)) :=
      (continuous_cayleyBoundaryPoint.measurable.add measurable_const).div
        (continuous_cayleyBoundaryPoint.measurable.sub measurable_const)
    exact hC.aestronglyMeasurable.mul (hg.ofReal (𝕜 := ℂ)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds z (show 0 < d / 2 by positivity)] with w hw
    have hw' : ‖w - z‖ < d / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    filter_upwards [hsupp] with t ht
    rcases ht with ht | ht
    · have hDen : d / 2 ≤ ‖cayleyBoundaryPoint t - w‖ := by
        have he := norm_add_le (cayleyBoundaryPoint t - w) (w - z)
        rw [sub_add_sub_cancel] at he
        linarith only [hLower t ht, he, hw']
      have hNum : ‖cayleyBoundaryPoint t + w‖ ≤ 2 + d / 2 := by
        have he := norm_add_le (cayleyBoundaryPoint t) w
        have hwN := norm_add_le (w - z) z
        rw [sub_add_cancel, hz] at hwN
        rw [norm_cayleyBoundaryPoint t] at he
        linarith only [he, hwN, hw']
      change ‖((cayleyBoundaryPoint t + w) / (cayleyBoundaryPoint t - w)) * (g t : ℂ)‖ ≤ _
      rw [norm_mul, Complex.norm_real, norm_div]
      exact mul_le_mul_of_nonneg_right
        (div_le_div₀ (by positivity) hNum (by positivity) hDen) (norm_nonneg _)
    · simp [K, g, ht]
  · filter_upwards [hsupp] with t ht
    rcases ht with ht | ht
    · have hne : cayleyBoundaryPoint t - z ≠ 0 :=
        norm_pos_iff.mp (hd.trans_le (hLower t ht))
      have hNum : ContinuousAt (fun w : ℂ => cayleyBoundaryPoint t + w) z :=
        continuousAt_const.add continuousAt_id
      have hDen : ContinuousAt (fun w : ℂ => cayleyBoundaryPoint t - w) z :=
        continuousAt_const.sub continuousAt_id
      exact ((hNum.div hDen hne).mul continuousAt_const).tendsto
    · simp [K, g, ht]

/-- The compact datum gives a real integral formula for the conjugate
at every boundary point off its support. -/
theorem im_weightedDiskHerglotzIntegral_cayleyBoundaryPoint_of_compact
    {u : ℝ → ℝ} {R x : ℝ} (hx : R < |x|)
    (hsupp : ∀ᵐ t : ℝ, |t| ≤ R ∨ u t = 0) :
    (weightedDiskHerglotzIntegral u (cayleyBoundaryPoint x)).im =
      ∫ t : ℝ, ((1 + x * t) / (x - t)) * (Real.pi⁻¹ * (u t / (1 + t ^ 2))) := by
  let q (t : ℝ) := ((1 + x * t) / (x - t)) * (Real.pi⁻¹ * (u t / (1 + t ^ 2)))
  have hEq : weightedDiskHerglotzIntegral u (cayleyBoundaryPoint x) =
      Complex.I * (((∫ t : ℝ, q t) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hsupp] with t ht
    rcases ht with ht | ht
    · have htx : t ≠ x := fun he => (not_le_of_gt hx) (he ▸ ht)
      rw [herglotzRieszKernel_cayleyBoundaryPoint htx]
      simp only [q, Complex.ofReal_mul, mul_assoc]
    · simp [ht, q]
  rw [hEq, Complex.mul_im]
  simp [q]

/-- The compact contribution has the uniform bound of the conjugate
kernel outside twice the support radius. -/
theorem abs_im_weightedDiskHerglotzIntegral_cayleyBoundaryPoint_le_of_compact
    {u : ℝ → ℝ} (hu : Integrable (fun t : ℝ => u t / (1 + t ^ 2)))
    {R x : ℝ} (hR : 0 < R) (hx : 2 * R < |x|)
    (hsupp : ∀ᵐ t : ℝ, |t| ≤ R ∨ u t = 0) :
    |(weightedDiskHerglotzIntegral u (cayleyBoundaryPoint x)).im| ≤
      (2 * R + R⁻¹) * (∫ t : ℝ, ‖u t / (1 + t ^ 2)‖) / Real.pi := by
  rw [im_weightedDiskHerglotzIntegral_cayleyBoundaryPoint_of_compact (by linarith) hsupp]
  let K := (2 * R + R⁻¹) * Real.pi⁻¹
  let q (t : ℝ) := ((1 + x * t) / (x - t)) * (Real.pi⁻¹ * (u t / (1 + t ^ 2)))
  let bound (t : ℝ) := K * ‖u t / (1 + t ^ 2)‖
  have hQ : AEStronglyMeasurable q := by
    have hMeas : Measurable (fun t : ℝ => (1 + x * t) / (x - t)) :=
      (measurable_const.add (measurable_const.mul measurable_id)).div
        (measurable_const.sub measurable_id)
    exact hMeas.aestronglyMeasurable.mul (hu.const_mul _).aestronglyMeasurable
  have hBound : ∀ᵐ t : ℝ, ‖q t‖ ≤ bound t := by
    filter_upwards [hsupp] with t ht
    rcases ht with ht | ht
    · calc
        ‖q t‖ = |(1 + x * t) / (x - t)| * (Real.pi⁻¹ * ‖u t / (1 + t ^ 2)‖) := by
          dsimp only [q]
          rw [norm_mul, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr Real.pi_pos.le), Real.norm_eq_abs]
        _ ≤ (2 * R + R⁻¹) * (Real.pi⁻¹ * ‖u t / (1 + t ^ 2)‖) :=
          mul_le_mul_of_nonneg_right (abs_boundary_herglotz_ratio_le hR ht hx) (by positivity)
        _ = bound t := by simp only [bound, K, mul_assoc]
    · simp [q, bound, ht]
  have hInt : Integrable bound := hu.norm.const_mul _
  calc
    _ = ‖∫ t : ℝ, q t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t : ℝ, ‖q t‖ := norm_integral_le_integral_norm q
    _ ≤ ∫ t : ℝ, bound t := integral_mono_ae (hInt.mono' hQ hBound).norm hInt hBound
    _ = _ := by rw [integral_const_mul]; dsimp [K]; ring

/-- A compact datum and a small weighted tail have a jointly controlled
conjugate value somewhere in the fractional window. The tail value is
specified as a measurable almost-everywhere radial limit. -/
theorem exists_fractional_window_of_small_weightedDiskHerglotz_tail
    {u₀ u₁ v : ℝ → ℝ}
    (hu₀ : Integrable (fun t : ℝ => u₀ t / (1 + t ^ 2)))
    (hu₁ : Integrable (fun t : ℝ => u₁ t / (1 + t ^ 2))) (hv : Measurable v)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 ≤ ρ n) (hρ₁ : ∀ n, ρ n < 1)
    (hLim : ∀ᵐ θ ∂diskAngleMeasure, Tendsto
      (fun n : ℕ => (weightedDiskHerglotzIntegral u₁ (circleMap 0 (ρ n) θ)).im)
      atTop (𝓝 (v θ)))
    {E : Set ℝ} (hE : cauchyBoundaryMeasure E = 0)
    {R ε δ r : ℝ} (hR : 0 < R) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ)
    (hr : 1 ≤ r) (hWindow : 2 * R ≤ (1 - ε) * r)
    (hsupp : ∀ᵐ t : ℝ, |t| ≤ R ∨ u₀ t = 0)
    (hSmall : (∫ t : ℝ, ‖u₁ t / (1 + t ^ 2)‖) < ε * δ / 8) :
    ∃ x ∈ Ioo ((1 - ε) * r) r, x ∉ E ∧
      |(weightedDiskHerglotzIntegral u₀ (cayleyBoundaryPoint x)).im + v (cayleyBoundaryAngle x)| ≤
        (2 * R + R⁻¹) * (∫ t : ℝ, ‖u₀ t / (1 + t ^ 2)‖) / Real.pi + δ * r := by
  have hWeak := cauchyBoundaryMeasure_lt_abs_weightedDiskHerglotz_boundary hu₁ hv
    ρ hρ hρ₁ hLim (L := δ * r) (by positivity)
  obtain ⟨x, hx, hxE, hvx⟩ :=
    exists_fractional_window_of_cauchyBoundaryMeasure_weak hE hε hε₁ hδ hr hSmall hWeak
  have hxR : 2 * R < x := hWindow.trans_lt hx.1
  have hxAbs : 2 * R < |x| := hxR.trans_le (le_abs_self x)
  refine ⟨x, hx, hxE, (abs_add_le _ _).trans ?_⟩
  exact add_le_add
    (abs_im_weightedDiskHerglotzIntegral_cayleyBoundaryPoint_le_of_compact hu₀ hR hxAbs hsupp) hvx

end
end MeyerGeneralProblem
