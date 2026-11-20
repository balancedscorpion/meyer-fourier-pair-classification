module

public import MeyerGeneralProblem.Distribution.DiskHerglotzWeak
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.Ultrafilter

@[expose] public section

/-!
# Positive Poisson representation on the unit disk

The angular densities of a nonnegative real part have common mass.
A cluster limit on the compact circle represents the real part
through the Poisson kernel.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

/-- The unit circle, used as the boundary of the disk. -/
abbrev DiskUnitBoundary := sphere (0 : ℂ) 1

instance : CompactSpace DiskUnitBoundary := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

/-- A real angle as a point of the unit circle. -/
def diskAnglePoint (θ : ℝ) : DiskUnitBoundary :=
  ⟨circleMap 0 1 θ, by simpa only [abs_one] using circleMap_mem_sphere' (0 : ℂ) 1 θ⟩

/-- Angular parametrization is continuous into the circle subtype. -/
theorem continuous_diskAnglePoint : Continuous diskAnglePoint :=
  (continuous_circleMap 0 1).subtype_mk _

private theorem integral_diskAngleMeasure_eq_circleAverage (r : ℝ) (V : ℂ → ℝ) :
    (∫ θ, V (circleMap 0 r θ) ∂diskAngleMeasure) = 2 * Real.pi * Real.circleAverage V 0 r := by
  change (∫ θ in Ioo 0 (2 * Real.pi), V (circleMap 0 r θ)) =
    (2 * Real.pi) * ((2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, V (circleMap 0 r θ))
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_Ioc_eq_integral_Ioo,
    ← mul_assoc, mul_inv_cancel₀ Real.two_pi_pos.ne', one_mul]

private def radialDiskBoundaryMeasure (F : ℂ → ℂ) (r : ℝ) : Measure DiskUnitBoundary :=
  (diskAngleMeasure.withDensity (fun θ =>
    ENNReal.ofReal ((F (circleMap 0 r θ)).re / (2 * Real.pi)))).map diskAnglePoint

private theorem continuous_radialDiskRealPart {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) :
    Continuous (fun θ : ℝ => (F (circleMap 0 r θ)).re) :=
  Complex.continuous_re.comp (hF.continuousOn.comp_continuous (continuous_circleMap 0 r) fun θ => by
    rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_nonneg hr]
    exact hr₁)

private theorem radialDiskBoundaryMeasure_mass {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hPos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (F z).re)
    {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) :
    radialDiskBoundaryMeasure F r univ = ENNReal.ofReal (F 0).re := by
  have hClosed : closedBall (0 : ℂ) |r| ⊆ ball 0 1 := by
    rw [abs_of_nonneg hr]
    exact closedBall_subset_ball hr₁
  have hI : CircleIntegrable F 0 r :=
    (hF.continuousOn.mono (sphere_subset_closedBall.trans hClosed)).circleIntegrable'
  have hMean := Complex.reCLM.circleAverage_comp_comm hI
  rw [(hF.diffContOnCl_ball hClosed).circleAverage] at hMean
  have hMean' : Real.circleAverage (fun z => (F z).re) 0 r = (F 0).re := hMean
  have hInt : Integrable (fun θ : ℝ => (F (circleMap 0 r θ)).re / (2 * Real.pi)) diskAngleMeasure :=
    (((continuous_radialDiskRealPart hF hr hr₁).div_const _).continuousOn.integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  have hNonneg (θ : ℝ) : 0 ≤ (F (circleMap 0 r θ)).re / (2 * Real.pi) := by
    apply div_nonneg (hPos _ ?_) Real.two_pi_pos.le
    rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_nonneg hr]
    exact hr₁
  rw [radialDiskBoundaryMeasure, Measure.map_apply continuous_diskAnglePoint.measurable MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ hNonneg)]
  congr 1
  simp only [div_eq_inv_mul, integral_const_mul]
  have hIntegral := integral_diskAngleMeasure_eq_circleAverage r (fun z => (F z).re)
  rw [hIntegral, hMean', ← mul_assoc,
    inv_mul_cancel₀ Real.two_pi_pos.ne', one_mul]

private def radialDiskBoundaryFiniteMeasure {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hPos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (F z).re)
    {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) : FiniteMeasure DiskUnitBoundary :=
  ⟨radialDiskBoundaryMeasure F r, ⟨by
    rw [radialDiskBoundaryMeasure_mass hF hPos hr hr₁]
    exact ENNReal.ofReal_lt_top⟩⟩

/-- The real Herglotz–Riesz kernel at an interior observation point. -/
def diskBoundaryPoissonKernel (w : ℂ) (ζ : DiskUnitBoundary) : ℝ :=
  (herglotzRieszKernel 0 w ζ.1).re

/-- The Poisson kernel at an interior point is continuous on the circle. -/
theorem continuous_diskBoundaryPoissonKernel {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    Continuous (diskBoundaryPoissonKernel w) := by
  have h := continuousOn_herglotzRieszKernel_sphere (R := (1 : ℝ)) (c := (0 : ℂ)) (w := w) (by simpa only [abs_one, mem_sphere] using (mem_ball.mp hw).ne)
  rw [abs_one] at h
  exact Complex.continuous_re.comp (continuousOn_iff_continuous_domRestrict.mp h)

private theorem integral_radialDiskBoundaryMeasure {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hPos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (F z).re)
    {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) (P : C(DiskUnitBoundary, ℝ)) :
    (∫ ζ, P ζ ∂radialDiskBoundaryMeasure F r) =
      ∫ θ, ((F (circleMap 0 r θ)).re / (2 * Real.pi)) * P (diskAnglePoint θ) ∂diskAngleMeasure := by
  have hD : Measurable (fun θ => ENNReal.ofReal ((F (circleMap 0 r θ)).re / (2 * Real.pi))) :=
    ENNReal.measurable_ofReal.comp ((continuous_radialDiskRealPart hF hr hr₁).div_const _).measurable
  rw [radialDiskBoundaryMeasure, integral_map continuous_diskAnglePoint.measurable.aemeasurable
    P.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hD (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  refine ae_of_all _ fun θ => ?_
  have hθ : circleMap 0 r θ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_nonneg hr]
    exact hr₁
  exact congrArg (fun c : ℝ => c * P (diskAnglePoint θ))
    (ENNReal.toReal_ofReal (div_nonneg (hPos _ hθ) Real.two_pi_pos.le))

private theorem integral_diskBoundaryPoissonKernel_radial {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hPos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (F z).re)
    {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (∫ ζ, diskBoundaryPoissonKernel w ζ ∂radialDiskBoundaryMeasure F r) = (F ((r : ℂ) * w)).re := by
  let P (q : ℂ) := (herglotzRieszKernel 0 w q).re
  let G (q : ℂ) := F ((r : ℂ) * q)
  let U := (fun q : ℂ => (r : ℂ) * q) ⁻¹' ball 0 1
  have hG : DifferentiableOn ℂ G U :=
    hF.comp ((differentiable_id.const_mul _).differentiableOn) (fun _ h => h)
  have hU : closedBall (0 : ℂ) |(1 : ℝ)| ⊆ U := by
    intro q hq
    change (r : ℂ) * q ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
    have hq' : ‖q‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right, abs_one] using hq
    exact (mul_le_of_le_one_right hr hq').trans_lt hr₁
  have hG' : DiffContOnCl ℂ G (ball 0 1) :=
    hG.diffContOnCl_ball (by simpa only [abs_one] using hU)
  have hP : ContinuousOn P (sphere 0 |(1 : ℝ)|) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere (R := (1 : ℝ)) (c := (0 : ℂ)) (w := w) (by simpa only [abs_one, mem_sphere] using (mem_ball.mp hw).ne))
  have hI : CircleIntegrable (P • G) 0 1 :=
    (hP.smul (hG.continuousOn.mono (sphere_subset_closedBall.trans hU))).circleIntegrable'
  have hMean := Complex.reCLM.circleAverage_comp_comm hI
  have hEq : Real.circleAverage (P • G) 0 1 = G w := hG'.circleAverage_re_herglotzRieszKernel_smul hw
  rw [hEq] at hMean
  have hReal : Real.circleAverage (fun q => P q * (G q).re) 0 1 = (G w).re := by
    have hFun : Complex.reCLM ∘ (P • G) = (fun q => P q * (G q).re) := by
      funext q
      change (P q • G q).re = _
      rw [Complex.smul_re, smul_eq_mul]
    rw [hFun] at hMean
    exact hMean
  let P₀ : C(DiskUnitBoundary, ℝ) := ⟨diskBoundaryPoissonKernel w, continuous_diskBoundaryPoissonKernel hw⟩
  change (∫ ζ, P₀ ζ ∂radialDiskBoundaryMeasure F r) = _
  rw [integral_radialDiskBoundaryMeasure hF hPos hr hr₁ P₀]
  calc
    _ = ∫ θ, (2 * Real.pi)⁻¹ * (P (circleMap 0 1 θ) * (G (circleMap 0 1 θ)).re) ∂diskAngleMeasure := by
      apply integral_congr_ae
      refine ae_of_all _ fun θ => ?_
      have hCircle : circleMap 0 r θ = (r : ℂ) * circleMap 0 1 θ := by
        simp only [circleMap_zero, Complex.ofReal_one, one_mul]
      change (F (circleMap 0 r θ)).re / (2 * Real.pi) * P (circleMap 0 1 θ) = _
      rw [hCircle]
      change (G (circleMap 0 1 θ)).re / (2 * Real.pi) * P (circleMap 0 1 θ) = _
      ring
    _ = _ := by
      rw [integral_const_mul]
      have hIntegral := integral_diskAngleMeasure_eq_circleAverage 1 (fun q => P q * (G q).re)
      rw [hIntegral, hReal, ← mul_assoc,
        inv_mul_cancel₀ Real.two_pi_pos.ne', one_mul]

/-- There is a sequence of nonnegative radii approaching one from
strictly inside the disk. -/
theorem exists_innerDiskRadialSequence :
    ∃ r : ℕ → ℝ, (∀ n, 0 ≤ r n) ∧ (∀ n, r n < 1) ∧ Tendsto r atTop (𝓝 1) := by
  let r (n : ℕ) := 1 - ((n : ℝ) + 2)⁻¹
  have hr₀ (n : ℕ) : 0 ≤ r n := by
    dsimp [r]
    have h : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      linarith only [Nat.cast_nonneg (α := ℝ) n]
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ h)
  have hr₁ (n : ℕ) : r n < 1 := by
    dsimp [r]
    exact sub_lt_self _ (by positivity)
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  refine ⟨r, hr₀, hr₁, ?_⟩
  simpa only [r, Function.comp_apply, sub_zero] using
    tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp ht)

/-- An almost-everywhere radial limit of a nonnegative harmonic real
part is angularly integrable by Fatou's lemma and the mean value law. -/
theorem integrable_diskAngleMeasure_of_radial_re_limit {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hPos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (F z).re)
    {D : ℝ → ℝ} (hLim : ∀ᵐ θ ∂diskAngleMeasure,
      Tendsto (fun r : ℝ => (F (circleMap 0 r θ)).re) (𝓝[<] (1 : ℝ)) (𝓝 (D θ))) :
    Integrable D diskAngleMeasure := by
  obtain ⟨r, hr₀, hr₁, hr⟩ := exists_innerDiskRadialSequence
  have hrWithin : Tendsto r atTop (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within r hr (Eventually.of_forall hr₁)
  let G (n : ℕ) (θ : ℝ) := (F (circleMap 0 (r n) θ)).re / (2 * Real.pi)
  have hGMeas (n : ℕ) : AEStronglyMeasurable (G n) diskAngleMeasure :=
    ((continuous_radialDiskRealPart hF (hr₀ n) (hr₁ n)).div_const _).aestronglyMeasurable
  have hGLim : ∀ᵐ θ ∂diskAngleMeasure,
      Tendsto (fun n => G n θ) atTop (𝓝 (D θ / (2 * Real.pi))) := by
    filter_upwards [hLim] with θ hθ
    exact (hθ.comp hrWithin).div_const _
  have hMass (n : ℕ) : ∫⁻ θ, ‖G n θ‖ₑ ∂diskAngleMeasure = ENNReal.ofReal (F 0).re := by
    have hm := radialDiskBoundaryMeasure_mass hF hPos (hr₀ n) (hr₁ n)
    rw [radialDiskBoundaryMeasure, Measure.map_apply continuous_diskAnglePoint.measurable MeasurableSet.univ,
      preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hm
    refine (lintegral_congr fun θ => Real.enorm_eq_ofReal ?_).trans hm
    apply div_nonneg (hPos _ ?_) Real.two_pi_pos.le
    rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_nonneg (hr₀ n)]
    exact hr₁ n
  have hInt := integrable_of_tendsto hGLim hGMeas (by
    simp only [hMass, liminf_const]
    exact ENNReal.ofReal_lt_top.ne)
  convert hInt.const_mul (2 * Real.pi) using 1
  funext θ
  field_simp [Real.pi_ne_zero]

/-- A Poisson representing measure realizes each radial test limit
that exists against a continuous boundary function. -/
theorem exists_diskBoundaryPoissonMeasure_of_test_limits {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hPos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (F z).re) :
    ∃ μ : FiniteMeasure DiskUnitBoundary, μ.mass = (F 0).re.toNNReal ∧
      (∀ w ∈ ball (0 : ℂ) 1, (∫ ζ, diskBoundaryPoissonKernel w ζ ∂(μ : Measure DiskUnitBoundary)) =
        (F w).re) ∧
      ∀ (P : C(DiskUnitBoundary, ℝ)) (I : ℝ),
        Tendsto (fun r : ℝ => ∫ θ, ((F (circleMap 0 r θ)).re / (2 * Real.pi)) *
          P (diskAnglePoint θ) ∂diskAngleMeasure) (𝓝[<] (1 : ℝ)) (𝓝 I) →
        (∫ ζ, P ζ ∂(μ : Measure DiskUnitBoundary)) = I := by
  obtain ⟨r, hr₀, hr₁, hr⟩ := exists_innerDiskRadialSequence
  let ν (n : ℕ) := radialDiskBoundaryFiniteMeasure hF hPos (hr₀ n) (hr₁ n)
  have hm (n : ℕ) : (ν n).mass = (F 0).re.toNNReal := by
    change (radialDiskBoundaryMeasure F (r n) univ).toNNReal = _
    rw [radialDiskBoundaryMeasure_mass hF hPos (hr₀ n) (hr₁ n), ENNReal.ofReal, ENNReal.toNNReal_coe]
  obtain ⟨μ, hμ, hCluster⟩ := (isCompact_setOfPred_finiteMeasure_eq_of_compactSpace
    DiskUnitBoundary (F 0).re.toNNReal).exists_mapClusterPt
      (tendsto_principal.mpr (Eventually.of_forall hm) :
        Tendsto ν atTop (𝓟 {μ : FiniteMeasure DiskUnitBoundary | μ.mass = (F 0).re.toNNReal}))
  obtain ⟨l, hl, hν⟩ := mapClusterPt_iff_ultrafilter.mp hCluster
  refine ⟨μ, hμ, ?_, ?_⟩
  · intro w hw
    let P : C(DiskUnitBoundary, ℝ) := ⟨diskBoundaryPoissonKernel w, continuous_diskBoundaryPoissonKernel hw⟩
    have hC := FiniteMeasure.continuous_integral_continuousMap P
    have hMeasure : Tendsto (fun n : ℕ => ∫ ζ, diskBoundaryPoissonKernel w ζ ∂(ν n : Measure DiskUnitBoundary))
        l (𝓝 (∫ ζ, diskBoundaryPoissonKernel w ζ ∂(μ : Measure DiskUnitBoundary))) :=
      hC.continuousAt.tendsto.comp hν
    have hScale : Tendsto (fun n : ℕ => (r n : ℂ) * w) atTop (𝓝 w) := by
      simpa only [Function.comp_apply, Complex.ofReal_one, one_mul] using
        (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).mul_const w
    have hReal : Tendsto (fun n : ℕ => (F ((r n : ℂ) * w)).re) atTop (𝓝 (F w).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp
        ((hF.continuousOn.continuousAt (isOpen_ball.mem_nhds hw)).tendsto.comp hScale)
    have hOther : Tendsto (fun n : ℕ => ∫ ζ, diskBoundaryPoissonKernel w ζ ∂(ν n : Measure DiskUnitBoundary))
        l (𝓝 (F w).re) :=
      (hReal.congr fun n =>
        (integral_diskBoundaryPoissonKernel_radial hF hPos (hr₀ n) (hr₁ n) hw).symm).mono_left hl
    exact tendsto_nhds_unique hMeasure hOther
  · intro P I hTest
    have hMeasure : Tendsto (fun n : ℕ => ∫ ζ, P ζ ∂(ν n : Measure DiskUnitBoundary))
        l (𝓝 (∫ ζ, P ζ ∂(μ : Measure DiskUnitBoundary))) :=
      (FiniteMeasure.continuous_integral_continuousMap P).continuousAt.tendsto.comp hν
    have hrWithin : Tendsto r l (𝓝[<] (1 : ℝ)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within r hr
        (Eventually.of_forall hr₁)).mono_left hl
    have hOther : Tendsto (fun n : ℕ => ∫ ζ, P ζ ∂(ν n : Measure DiskUnitBoundary)) l (𝓝 I) :=
      (hTest.comp hrWithin).congr fun n =>
        (integral_radialDiskBoundaryMeasure hF hPos (hr₀ n) (hr₁ n) P).symm
    exact tendsto_nhds_unique hMeasure hOther

/-- The nonnegative real part of a holomorphic disk function is
represented by a finite positive measure on the circle. -/
theorem exists_diskBoundaryPoissonMeasure {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hPos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (F z).re) :
    ∃ μ : FiniteMeasure DiskUnitBoundary, μ.mass = (F 0).re.toNNReal ∧
      ∀ w ∈ ball (0 : ℂ) 1, (∫ ζ, diskBoundaryPoissonKernel w ζ ∂(μ : Measure DiskUnitBoundary)) =
        (F w).re := by
  obtain ⟨μ, hμ, hPoisson, _⟩ := exists_diskBoundaryPoissonMeasure_of_test_limits hF hPos
  exact ⟨μ, hμ, hPoisson⟩

end
end MeyerGeneralProblem
