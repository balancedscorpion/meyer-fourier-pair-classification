module

public import MeyerGeneralProblem.Distribution.BlaschkeBoundaryDensity
public import Mathlib.Analysis.Complex.OpenMapping

@[expose] public section

/-!
# The weighted Herglotz representation of the Blaschke logarithm

The angular Poisson integral is the real part of the weighted
Herglotz integral for the corresponding real-line data. The
holomorphic logarithm is then determined up to an imaginary constant.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Metric Set
open scoped FourierTransform Topology

private theorem re_weightedDiskHerglotzIntegral_eq_angular {Q : ℂ → ℝ}
    (hQ : Integrable (fun θ : ℝ => Q (cayleyToUpperHalfPlane (circleMap 0 1 θ))) diskAngleMeasure)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (weightedDiskHerglotzIntegral (fun x : ℝ => Q x) w).re =
      ∫ θ, (Q (cayleyToUpperHalfPlane (circleMap 0 1 θ)) / (2 * Real.pi)) *
        diskBoundaryPoissonKernel w (diskAnglePoint θ) ∂diskAngleMeasure := by
  have hW := (integrable_weighted_cayleyBoundary Q hQ).1
  rw [weightedDiskHerglotzIntegral, re_diskHerglotzIntegral continuous_cayleyBoundaryPoint.measurable
    norm_cayleyBoundaryPoint (hW.const_mul _) (mem_ball_zero_iff.mp hw)]
  let P (θ : ℝ) := (Q (cayleyToUpperHalfPlane (circleMap 0 1 θ)) / (2 * Real.pi)) *
    diskBoundaryPoissonKernel w (diskAnglePoint θ)
  change (∫ x : ℝ, (herglotzRieszKernel 0 w (cayleyBoundaryPoint x)).re *
    (Real.pi⁻¹ * (Q x / (1 + x ^ 2)))) = ∫ θ in Ioo 0 (2 * Real.pi), P θ
  refine Eq.trans ?_ (integral_cayleyBoundaryAngle P).symm
  apply integral_congr_ae
  refine ae_of_all _ fun x => ?_
  change (herglotzRieszKernel 0 w (cayleyBoundaryPoint x)).re * _ =
    (2 / (1 + x ^ 2)) * ((Q (cayleyToUpperHalfPlane (circleMap 0 1 (cayleyBoundaryAngle x))) /
      (2 * Real.pi)) * (herglotzRieszKernel 0 w (cayleyBoundaryPoint x)).re)
  rw [cayleyToUpperHalfPlane_circleMap_cayleyBoundaryAngle]
  field_simp [Real.pi_ne_zero, show 1 + x ^ 2 ≠ 0 by positivity]

/-- The holomorphic remainder with the given Poisson real part equals
the weighted Herglotz integral, the linear term from infinity and an
imaginary constant. -/
theorem exists_blaschkeBoundaryLog_weighted_identity {H L : ℂ → ℂ} {A c : ℝ}
    (hL : DifferentiableOn ℂ L {z : ℂ | 0 < z.im})
    (hD : Integrable (fun θ : ℝ => A - Real.log ‖H (cayleyToUpperHalfPlane (circleMap 0 1 θ))‖)
      diskAngleMeasure)
    (hPoisson : ∀ w ∈ ball (0 : ℂ) 1, A - (L (cayleyToUpperHalfPlane w)).re =
      (∫ θ, ((A - Real.log ‖H (cayleyToUpperHalfPlane (circleMap 0 1 θ))‖) / (2 * Real.pi)) *
        diskBoundaryPoissonKernel w (diskAnglePoint θ) ∂diskAngleMeasure) + c * (cayleyToUpperHalfPlane w).im) :
    let u (x : ℝ) := Real.log ‖H (x : ℂ)‖
    Integrable (fun x : ℝ => u x / (1 + x ^ 2)) ∧ ∃ d : ℝ, ∀ w ∈ ball (0 : ℂ) 1,
      L (cayleyToUpperHalfPlane w) = weightedDiskHerglotzIntegral u w +
        (c : ℂ) * Complex.I * cayleyToUpperHalfPlane w + (d : ℂ) * Complex.I := by
  let C := cayleyToUpperHalfPlane
  let Q (z : ℂ) := A - Real.log ‖H z‖
  let u (x : ℝ) := Real.log ‖H (x : ℂ)‖
  let _ : IsFiniteMeasure diskAngleMeasure := by
    unfold diskAngleMeasure
    infer_instance
  have hA : Integrable (fun _ : ℝ => A) diskAngleMeasure := integrable_const _
  have hConst := (integrable_weighted_cayleyBoundary (fun _ => A) hA).1
  have hUInt : Integrable (fun θ : ℝ => Real.log ‖H (C (circleMap 0 1 θ))‖) diskAngleMeasure := by
    have he := hA.sub hD
    change Integrable (fun θ : ℝ => A - (A - Real.log ‖H (C (circleMap 0 1 θ))‖)) diskAngleMeasure at he
    simpa only [sub_sub_cancel] using he
  have hu : Integrable (fun x : ℝ => u x / (1 + x ^ 2)) :=
    (integrable_weighted_cayleyBoundary (fun z => Real.log ‖H z‖) hUInt).1
  let J (w : ℂ) := L (C w) - weightedDiskHerglotzIntegral u w - (c : ℂ) * Complex.I * C w
  have hMaps : MapsTo C (ball 0 1) {z : ℂ | 0 < z.im} :=
    fun _ hw => im_cayleyToUpperHalfPlane_pos (mem_ball_zero_iff.mp hw)
  have hWeighted : DifferentiableOn ℂ (weightedDiskHerglotzIntegral u) (ball 0 1) :=
    differentiableOn_diskHerglotzIntegral continuous_cayleyBoundaryPoint.measurable
      norm_cayleyBoundaryPoint (hu.const_mul _)
  have hJ : DifferentiableOn ℂ J (ball 0 1) :=
    ((hL.comp differentiableOn_cayleyToUpperHalfPlane hMaps).sub hWeighted).sub
      (differentiableOn_cayleyToUpperHalfPlane.const_mul _)
  have hJReal (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : (J w).re = 0 := by
    have he := hPoisson w hw
    have ha := re_weightedDiskHerglotzIntegral_eq_angular (Q := Q) hD hw
    rw [← ha] at he
    change A - (L (C w)).re = (weightedDiskHerglotzIntegral (fun x => A - u x) w).re + c * (C w).im at he
    have hw₁ := mem_ball_zero_iff.mp hw
    rw [weightedDiskHerglotzIntegral_sub hConst hu hw₁, weightedDiskHerglotzIntegral_const hw₁,
      Complex.sub_re, Complex.ofReal_re] at he
    have hTerm : ((c : ℂ) * Complex.I * C w).re = -(c * (C w).im) := by
      simp [Complex.mul_re, Complex.mul_im]
    simp only [J, Complex.sub_re, hTerm]
    linarith only [he]
  have hConn : IsConnected (ball (0 : ℂ) 1) :=
    ⟨⟨0, mem_ball_self zero_lt_one⟩, (convex_ball (0 : ℂ) 1).isPreconnected⟩
  obtain ⟨d, hd⟩ := (hJ.analyticOnNhd isOpen_ball).eq_re_add_const_mul_I_of_re_eq_const
    hJReal isOpen_ball hConn
  refine ⟨hu, d, fun w hw => ?_⟩
  have he := hd w hw
  simp only [J, Complex.ofReal_zero, zero_add] at he
  linear_combination he

/-- The actual heated transform has the weighted Herglotz
logarithm, with the true Fourier-edge factor and a nonnegative
linear contribution to its phase. -/
theorem eventually_edgeNormalizedHeat_blaschke_hasWeightedLogarithm
    {f : ℝ → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 ≤ b)
    (hEdge : ∀ c > b, ∃ ξ ∈ Ioo b c, 𝓕 (fun x : ℝ => (f x : ℂ)) ξ ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let H := edgeNormalizedHeatFourierLaplace t f b
      let B := upperHalfPlaneBlaschkeProduct (upperHalfPlaneZeroAtIndex H)
      let U : Set ℂ := {z : ℂ | 0 < z.im}
      let u (x : ℝ) := Real.log ‖H (x : ℂ)‖
      Summable (fun i : UpperHalfPlaneZeroIndex H =>
        upperHalfPlaneBlaschkeWeight (upperHalfPlaneZeroAtIndex H i)) ∧
      (∀ R : ℝ, {i : UpperHalfPlaneZeroIndex H | ‖upperHalfPlaneZeroAtIndex H i‖ ≤ R}.Finite) ∧
      Integrable (fun x : ℝ => u x / (1 + x ^ 2)) ∧
      ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L U ∧ EqOn H (fun z => B z * Complex.exp (L z)) U ∧
        ∃ c d : ℝ, 0 ≤ c ∧
          (∀ w ∈ ball (0 : ℂ) 1, L (cayleyToUpperHalfPlane w) =
            weightedDiskHerglotzIntegral u w + (c : ℂ) * Complex.I * cayleyToUpperHalfPlane w +
              (d : ℂ) * Complex.I) ∧
          ∀ z ∈ U, L z = weightedDiskHerglotzIntegral u (scaledUpperHalfPlaneToDisk 1 z) +
            (c : ℂ) * Complex.I * z + (d : ℂ) * Complex.I := by
  filter_upwards [eventually_edgeNormalizedHeat_blaschke_hasBoundaryPoissonRepresentation hf hb hEdge]
    with t hF
  obtain ⟨hSum, hFin, hD, L, hL, hEq, c, hc, hPoisson⟩ := hF
  obtain ⟨hU, d, hWeighted⟩ := exists_blaschkeBoundaryLog_weighted_identity hL.differentiableOn hD hPoisson
  refine ⟨hSum, hFin, hU, L, hL, hEq, c, d, hc, hWeighted, fun z hz => ?_⟩
  have hPos : 0 < (1 : ℝ) := zero_lt_one
  have hDisk := norm_scaledUpperHalfPlaneToDisk_lt_one hz hPos
  have he := hWeighted (scaledUpperHalfPlaneToDisk 1 z) (mem_ball_zero_iff.mpr hDisk)
  have hInverse := scaled_cayleyToUpperHalfPlane_scaledUpperHalfPlaneToDisk hz hPos
  simp only [Complex.ofReal_one, one_mul] at hInverse
  rwa [hInverse] at he

end
end MeyerGeneralProblem
