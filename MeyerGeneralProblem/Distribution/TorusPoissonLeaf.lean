module

public import MeyerGeneralProblem.Distribution.SupportCauchyIntegral
public import MeyerGeneralProblem.Distribution.TorusPoissonAnalytic
public import Mathlib.Analysis.Complex.Convex

@[expose] public section

/-!
# Normalized holomorphic representatives of the Poisson phase leaves

The actual Cauchy integral and the Haar positive-frequency field have
the same difference of real parts from height one. A holomorphic
`L²` field with identically zero real part is constant, so the shared
height-one value fixes the scalar representative on each leaf.
-/

namespace MeyerGeneralProblem

open Adaptive Filter MeasureTheory ProbabilityTheory Set UnitAddTorus
open scoped NNReal Topology

/-- A holomorphic field with constant real projection is constant if
the real and imaginary projections jointly separate its values. -/
theorem eq_of_differentiableOn_real_projection_constant
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E →L[ℝ] F)
    (hP : ∀ v, P v = 0 → P (Complex.I • v) = 0 → v = 0)
    {U : Set ℂ} (hOpen : IsOpen U) (hConvex : Convex ℝ U)
    (f : ℂ → E) (hf : DifferentiableOn ℂ f U)
    (c : F) (hRe : ∀ z ∈ U, P (f z) = c) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    f z = f w := by
  have hZero (x : ℂ) (hx : x ∈ U) : HasFDerivAt f (0 : ℂ →L[ℂ] E) x := by
    obtain ⟨D, hD⟩ := hf.differentiableAt (hOpen.mem_nhds hx)
    have hRD := P.hasFDerivAt.comp x (hD.restrictScalars ℝ)
    have hLocal : (fun y => P (f y)) =ᶠ[𝓝 x] fun _ => c := by
      filter_upwards [hOpen.mem_nhds hx] with y hy
      exact hRe y hy
    have hConst : HasFDerivAt (fun y => P (f y)) (0 : ℂ →L[ℝ] F) x :=
      (hasFDerivAt_const c x).congr_of_eventuallyEq hLocal
    have hKill (a : ℂ) : P (D a) = 0 := DFunLike.congr_fun (hRD.unique hConst) a
    have hD0 : D = 0 := by
      apply ContinuousLinearMap.ext
      intro a
      change D a = 0
      exact hP (D a) (hKill a) (by simpa only [map_smul] using hKill (Complex.I • a))
    rwa [← hD0]
  have hDist := hConvex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hZero x hx).hasFDerivWithinAt) (C := 0)
    (fun _ _ => by rw [norm_zero]) hw hz
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [zero_mul] using hDist))

/-- Fixed-point almost-everywhere vanishing of the real part suffices
to make a complex holomorphic `L²` field constant on a convex domain. -/
private theorem eq_of_differentiableOn_ae_re_zero {Θ : Type*} [MeasurableSpace Θ] {μ : Measure Θ}
    {U : Set ℂ} (hOpen : IsOpen U) (hConvex : Convex ℝ U)
    (f : ℂ → Lp ℂ 2 μ) (hf : DifferentiableOn ℂ f U)
    (hRe : ∀ z ∈ U, ∀ᵐ θ ∂μ, (f z θ).re = 0) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    f z = f w := by
  let P := Complex.reCLM.compLpL 2 μ
  have hSep (v : Lp ℂ 2 μ) (h₀ : P v = 0) (h₁ : P (Complex.I • v) = 0) : v = 0 := by
    have hv := Complex.reCLM.coeFn_compLpL v
    have hvI := Complex.reCLM.coeFn_compLpL (Complex.I • v)
    change (P v : Θ → ℝ) =ᵐ[μ] fun x => (v x).re at hv
    change (P (Complex.I • v) : Θ → ℝ) =ᵐ[μ] fun x => ((Complex.I • v : Lp ℂ 2 μ) x).re at hvI
    rw [h₀] at hv
    rw [h₁] at hvI
    apply Lp.ext
    filter_upwards [hv, hvI, Lp.coeFn_smul Complex.I v, Lp.coeFn_zero ℝ 2 μ,
      Lp.coeFn_zero ℂ 2 μ] with θ hReV hReI hMul hR0 hC0
    rw [hC0]
    apply Complex.ext
    · rw [hR0] at hReV
      exact hReV.symm
    · rw [hR0, hMul] at hReI
      have hI : (Complex.I * v θ).re = 0 := hReI.symm
      change (v θ).im = (0 : ℂ).im
      simpa only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
        zero_sub, neg_eq_zero, Complex.zero_im] using hI
  have hZ (a : ℂ) (ha : a ∈ U) : P (f a) = 0 := by
    apply Lp.ext
    filter_upwards [Complex.reCLM.coeFn_compLpL (f a), hRe a ha, Lp.coeFn_zero ℝ 2 μ]
      with θ hP hR h0
    exact hP.trans (hR.trans h0.symm)
  exact eq_of_differentiableOn_real_projection_constant P hSep hOpen hConvex f hf 0 hZ hz hw


noncomputable section

/-- Use normalized Haar measure on the phase torus. -/
local instance poissonLeafCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance poissonLeafCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation:max "TorusL2(" d ")" => Lp ℂ 2 (volume : Measure (UnitAddTorus d))

section PhaseFamily

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)

/-- The actual Haar positive-frequency field at the complex phase coordinate. -/
def torusPositivePoissonField (z : ℂ) : TorusL2(d) :=
  torusL2PhaseAdvance β z.re
    (torusSupportPositivePoissonL2 β S T hT hCont hCount z.im.toNNReal)

/-- In the upper half-plane the Haar positive-frequency field is the sum
of its height-one value and the normalized Cauchy integral. -/
theorem torusPositivePoissonField_eq_at_I_add_supportCauchyL2
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (z : ℂ) (hz : 0 < z.im) :
    torusPositivePoissonField β S T hT hCont hCount z =
      torusPositivePoissonField β S T hT hCont hCount Complex.I +
        supportCauchyL2 S T hT hCont hCount volume z := by
  let F := torusPositivePoissonField β S T hT hCont hCount
  let C := supportCauchyL2 S T hT hCont hCount volume
  let H (w : ℂ) := F w - F Complex.I - C w
  let U := {w : ℂ | 0 < w.im}
  have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hConvex : Convex ℝ U := convex_halfSpace_im_gt 0
  have hDiffF : DifferentiableOn ℂ F U :=
    (analyticOnNhd_torusSupportPositivePoissonL2 β S T hT hAdvance hCont hCount).differentiableOn
  have hDiffC : DifferentiableOn ℂ C U := by
    intro w hw
    have hw' : 0 < w.im := hw
    exact (differentiableAt_supportCauchyL2 S T hT hCont hCount volume w hw'.ne').differentiableWithinAt
  have hDiff : DifferentiableOn ℂ H U := (hDiffF.sub (differentiableOn_const (F Complex.I))).sub hDiffC
  have hReF (w : ℂ) (hw : 0 < w.im) :
      ∀ᵐ θ ∂volume, (F w θ).re =
        (∫ t, cauchyPDFReal w.re w.im.toNNReal t ∂discreteSupportCount (T θ)) / 2 :=
    ae_re_torusL2PhaseAdvance_supportPositivePoisson β S T hT hAdvance hCont hCount w.re
      (Real.toNNReal_pos.mpr hw)
  have hReFI : ∀ᵐ θ ∂volume, (F Complex.I θ).re =
      (∫ t, cauchyPDFReal 0 1 t ∂discreteSupportCount (T θ)) / 2 := by
    simpa only [Complex.I_re, Complex.I_im, Real.toNNReal_one] using hReF Complex.I (by simp)
  have hRe (w : ℂ) (hw : w ∈ U) : ∀ᵐ θ ∂volume, (H w θ).re = 0 := by
    have hw' : 0 < w.im := hw
    filter_upwards [Lp.coeFn_sub (F w - F Complex.I) (C w), Lp.coeFn_sub (F w) (F Complex.I),
      hReF w hw', hReFI, coeFn_supportCauchyL2 S T hT hCont hCount volume w hw'.ne']
      with θ hH hSub hF hI hC
    change ((F w - F Complex.I - C w) θ).re = 0
    simp only [Pi.sub_apply] at hH hSub
    rw [hH, hSub, Complex.sub_re, Complex.sub_re, hF, hI,
      show C w θ = _ from hC,
      re_integral_supportCauchyKernel_discreteSupportCount (S θ) (T θ) (hT θ) (hCount θ) w hw']
    ring
  have hConst := eq_of_differentiableOn_ae_re_zero hOpen hConvex H hDiff hRe
    (z := z) (w := Complex.I) hz (by simp [U])
  have hBase : H Complex.I = 0 := by
    simp [H, C, supportCauchyL2_at_I]
  change F z = F Complex.I + C z
  rw [hBase] at hConst
  have hMain : F z - F Complex.I = C z := sub_eq_zero.mp hConst
  calc
    F z = (F z - F Complex.I) + F Complex.I := (sub_add_cancel _ _).symm
    _ = _ := by rw [hMain, add_comm]

/-- The scalar representative prescribed by the Haar field at height one
and the Cauchy integral of the actual support-count measure. -/
def torusPositivePoissonLeaf (θ : UnitAddTorus d) (z : ℂ) : ℂ :=
  torusPositivePoissonField β S T hT hCont hCount Complex.I θ +
    ∫ t, supportCauchyKernel z t ∂discreteSupportCount (T θ)

/-- The scalar leaf formula is holomorphic on the upper half-plane at every phase. -/
theorem analyticOnNhd_torusPositivePoissonLeaf (θ : UnitAddTorus d) :
    AnalyticOnNhd ℂ (torusPositivePoissonLeaf β S T hT hCont hCount θ) {z : ℂ | 0 < z.im} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_im)
  intro z hz
  have hz' : 0 < z.im := hz
  exact (hasDerivAt_integral_supportCauchyKernel_discreteSupportCount
    (S θ) (T θ) (hT θ) (hCount θ) z hz'.ne').const_add
    (torusPositivePoissonField β S T hT hCont hCount Complex.I θ) |>.differentiableAt.differentiableWithinAt

/-- At every fixed upper-half-plane parameter, the normalized scalar
leaf is a representative of the true Haar positive-frequency field. -/
theorem ae_eq_torusPositivePoissonLeaf_field
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (z : ℂ) (hz : 0 < z.im) :
    (fun θ => torusPositivePoissonLeaf β S T hT hCont hCount θ z) =ᵐ[volume]
      torusPositivePoissonField β S T hT hCont hCount z := by
  rw [torusPositivePoissonField_eq_at_I_add_supportCauchyL2 β S T hT hCont hCount hAdvance z hz]
  filter_upwards [Lp.coeFn_add (torusPositivePoissonField β S T hT hCont hCount Complex.I)
      (supportCauchyL2 S T hT hCont hCount volume z),
    coeFn_supportCauchyL2 S T hT hCont hCount volume z hz.ne'] with θ hAdd hC
  rw [hAdd]
  simp only [torusPositivePoissonLeaf, Pi.add_apply, hC]

/-- A single full-measure set of phases has the exact real-part identity
at every upper-half-plane parameter for the normalized scalar leaf. -/
theorem ae_forall_re_torusPositivePoissonLeaf
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ)) :
    ∀ᵐ θ ∂volume, ∀ z : ℂ, 0 < z.im →
      (torusPositivePoissonLeaf β S T hT hCont hCount θ z).re =
        (∫ t, cauchyPDFReal z.re z.im.toNNReal t ∂discreteSupportCount (T θ)) / 2 := by
  filter_upwards [ae_re_torusL2PhaseAdvance_supportPositivePoisson
    β S T hT hAdvance hCont hCount 0 (y := 1) one_pos] with θ hθ
  have hBase : (torusPositivePoissonField β S T hT hCont hCount Complex.I θ).re =
      (∫ t, cauchyPDFReal 0 1 t ∂discreteSupportCount (T θ)) / 2 := by
    simpa only [torusPositivePoissonField, Complex.I_re, Complex.I_im, Real.toNNReal_one] using hθ
  intro z hz
  rw [torusPositivePoissonLeaf, Complex.add_re, hBase,
    re_integral_supportCauchyKernel_discreteSupportCount (S θ) (T θ) (hT θ) (hCount θ) z hz]
  ring

/-- For each fixed real translation there is a full-measure set of phases
on which the normalized scalar leaves obey flow covariance simultaneously
at every upper-half-plane parameter. -/
theorem ae_forall_torusPositivePoissonLeaf_phaseAdvance
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (s : ℝ) :
    ∀ᵐ θ ∂volume, ∀ z : ℂ, 0 < z.im →
      torusPositivePoissonLeaf β S T hT hCont hCount (unitAddTorusFlow β s θ) z =
        torusPositivePoissonLeaf β S T hT hCont hCount θ (z + (s : ℂ)) := by
  let U (t : ℝ) := unitAddTorusFlow β t
  let F := torusPositivePoissonField β S T hT hCont hCount
  let G := torusPositivePoissonLeaf β S T hT hCont hCount
  let b := Complex.I + (s : ℂ)
  have hb : 0 < b.im := by simp [b]
  have hZero (f : TorusL2(d)) : torusL2PhaseAdvance β 0 f = f := by
    apply (mFourierBasis (d := d)).repr.injective
    ext n
    rw [mFourierBasis_repr, mFourierBasis_repr, mFourierCoeff_torusL2PhaseAdvance]
    simp [combModulationCharacter_eq_exp]
  have hAtI : F Complex.I = torusSupportPositivePoissonL2 β S T hT hCont hCount 1 := by
    simp only [F, torusPositivePoissonField, Complex.I_re, Complex.I_im, Real.toNNReal_one, hZero]
  have hShift : F b = torusL2PhaseAdvance β s (F Complex.I) := by
    rw [hAtI]
    simp [F, b, torusPositivePoissonField]
  have hTransport := Lp.coeFn_compMeasurePreserving (F Complex.I) (measurePreserving_unitAddTorusFlow β s)
  have hRep := ae_eq_torusPositivePoissonLeaf_field β S T hT hCont hCount hAdvance b hb
  filter_upwards [hTransport, hRep] with θ hComp hRepθ
  have hNorm : F Complex.I (U s θ) = G θ b := by
    change torusL2PhaseAdvance β s (F Complex.I) θ = F Complex.I (U s θ) at hComp
    exact hComp.symm.trans ((congrArg (fun f : TorusL2(d) => f θ) hShift.symm).trans hRepθ.symm)
  intro z hz
  have hKernel (x : ℝ) : supportCauchyKernel z (-s + x) =
      supportCauchyKernel (z + (s : ℂ)) x - supportCauchyKernel b x := by
    have hShiftArg (w : ℂ) : ((-s + x : ℝ) : ℂ) - w = (x : ℂ) - (w + (s : ℂ)) := by
      push_cast
      ring
    simp only [supportCauchyKernel, broadCauchyKernel, pow_one, hShiftArg, b]
    ring
  let η := discreteSupportCount (T θ)
  have hInt (w : ℂ) (hw : w.im ≠ 0) : Integrable (supportCauchyKernel w) η :=
    integrable_supportCauchyKernel_discreteSupportCount (S θ) (T θ) (hT θ) (hCount θ) w hw
  have hη : (∫ x, supportCauchyKernel z x ∂discreteSupportCount (T (U s θ))) =
      (∫ x, supportCauchyKernel (z + (s : ℂ)) x ∂η) -
        (∫ x, supportCauchyKernel b x ∂η) := by
    change (∫ x, supportCauchyKernel z x ∂discreteSupportCount (T (unitAddTorusFlow β s θ))) = _
    rw [hAdvance, discreteSupportCount_combDistributionTranslation]
    rw [integral_map (show Measurable (fun x : ℝ => -s + x) by fun_prop).aemeasurable
      (measurable_supportCauchyKernel z).aestronglyMeasurable]
    simp_rw [hKernel]
    exact integral_sub (hInt _ (by simpa using hz.ne')) (hInt _ hb.ne')
  change G (U s θ) z = G θ (z + (s : ℂ))
  change F Complex.I (U s θ) +
    (∫ x, supportCauchyKernel z x ∂discreteSupportCount (T (U s θ))) =
      F Complex.I θ + ∫ x, supportCauchyKernel (z + (s : ℂ)) x ∂η
  rw [hNorm, hη]
  change (F Complex.I θ + ∫ x, supportCauchyKernel b x ∂η) + _ = _
  ring

end PhaseFamily

end
end MeyerGeneralProblem
