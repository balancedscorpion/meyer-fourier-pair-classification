module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayley
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

/-!
# Fourier coefficients of the bounded Cayley field

The normalized scalar Cayley leaves are uniformly bounded holomorphic
functions. Cauchy's derivative estimate permits differentiation of
each Haar Fourier coefficient. Phase covariance then determines its
complex exponential evolution.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Metric Set UnitAddTorus
open scoped NNReal Topology

private theorem hasDerivAt_integral_bounded_holomorphic_family
    {Θ : Type*} [MeasurableSpace Θ] {μ : Measure Θ} [IsFiniteMeasure μ]
    (F : ℂ → Θ → ℂ) (hMeas : ∀ z, AEStronglyMeasurable (F z) μ)
    (hGood : ∀ᵐ θ ∂μ, DifferentiableOn ℂ (fun z => F z θ) {z : ℂ | 0 < z.im} ∧
      ∀ z : ℂ, ‖F z θ‖ ≤ 1) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun v => ∫ θ, F v θ ∂μ) (∫ θ, deriv (fun v => F v θ) z ∂μ) z := by
  let U := {v : ℂ | 0 < v.im}
  have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hz' : 0 < z.im := hz
  let δ := z.im / 4
  have hδ : 0 < δ := div_pos hz' (by norm_num)
  have hIm (v w : ℂ) : v.im ≤ w.im + dist w v := by
    have hl := (le_abs_self ((v - w).im)).trans (Complex.abs_im_le_norm (v - w))
    rw [Complex.sub_im, ← dist_eq_norm, dist_comm] at hl
    linarith only [hl]
  have hClosed (v : ℂ) (hv : v ∈ ball z δ) : closedBall v δ ⊆ U := by
    intro w hw
    have hv' := mem_ball.mp hv
    have hw' := mem_closedBall.mp hw
    have h1 := hIm z v
    have h2 := hIm v w
    change 0 < w.im
    dsimp only [δ] at hv' hw'
    linarith only [hv', hw', h1, h2, hz']
  let D (v : ℂ) (θ : Θ) := deriv (fun w => F w θ) v
  have hFInt : Integrable (F z) μ :=
    Integrable.of_bound (hMeas z) 1 (hGood.mono fun _ h => h.2 z)
  have hDMeas : AEStronglyMeasurable (D z) μ := by
    apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ))
      (f := fun a θ => a⁻¹ • (F (z + a) θ - F z θ))
    · intro a
      exact ((hMeas (z + a)).sub (hMeas z)).const_smul (a⁻¹ : ℂ)
    · filter_upwards [hGood] with θ hθ
      exact ((hθ.1.differentiableAt (hOpen.mem_nhds hz)).hasDerivAt).tendsto_slope_zero
  have hD (θ : Θ) (hθ : DifferentiableOn ℂ (fun w => F w θ) U) (v : ℂ)
      (hv : v ∈ ball z δ) : HasDerivAt (fun w => F w θ) (D v θ) v :=
    (hθ.differentiableAt (hOpen.mem_nhds (hClosed v hv (mem_closedBall_self hδ.le)))).hasDerivAt
  have hBound : ∀ᵐ θ ∂μ, ∀ v ∈ ball z δ, ‖D v θ‖ ≤ 1 / δ := by
    filter_upwards [hGood] with θ hθ v hv
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ
      (hθ.1.diffContOnCl_ball (hClosed v hv)) (fun w _ => hθ.2 w)
  have hDeriv : ∀ᵐ θ ∂μ, ∀ v ∈ ball z δ, HasDerivAt (fun w => F w θ) (D v θ) v :=
    hGood.mono fun θ hθ v hv => hD θ hθ.1 v hv
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := D)
    (ball_mem_nhds z hδ) (Eventually.of_forall hMeas) hFInt hDMeas hBound
    (integrable_const (1 / δ)) hDeriv).2

/-- Use normalized Haar measure on each circle factor. -/
local instance cayleyFourierCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance cayleyFourierCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation:max "TorusL2(" d ")" => Lp ℂ 2 (volume : Measure (UnitAddTorus d))

private theorem norm_mFourier_apply_eq_one {d : Type*} [Fintype d] (n : d → ℤ)
    (θ : UnitAddTorus d) : ‖mFourier n θ‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe,
    Finset.prod_const_one]

section FourierCoefficients

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

/-- The Cayley field inherits the real covariance of the normalized leaves. -/
theorem torusPoissonCayleyL2_add_real (z : ℂ) (hz : 0 < z.im) (s : ℝ) :
    torusPoissonCayleyL2 β S T hT hCont hCount hAdvance (z + (s : ℂ)) =
      torusL2PhaseAdvance β s (torusPoissonCayleyL2 β S T hT hCont hCount hAdvance z) := by
  let C := torusPoissonCayleyL2 β S T hT hCont hCount hAdvance
  let F := torusPoissonCayleyField β S T hT hCont hCount
  let hPres := measurePreserving_unitAddTorusFlow β s
  have hAt : C z =ᵐ[volume] F z := coeFn_torusPoissonCayleyL2 β S T hT hCont hCount hAdvance z
  have hShift : C (z + (s : ℂ)) =ᵐ[volume] F (z + (s : ℂ)) :=
    coeFn_torusPoissonCayleyL2 β S T hT hCont hCount hAdvance _
  apply Lp.ext
  filter_upwards [hShift, hPres.quasiMeasurePreserving.ae_eq_comp hAt,
    Lp.coeFn_compMeasurePreserving (C z) hPres,
    ae_forall_torusPositivePoissonLeaf_phaseAdvance β S T hT hCont hCount hAdvance s]
    with θ hθ hLift hComp hCov
  change C (z + (s : ℂ)) θ = torusL2PhaseAdvance β s (C z) θ
  change C z (unitAddTorusFlow β s θ) = F z (unitAddTorusFlow β s θ) at hLift
  change torusL2PhaseAdvance β s (C z) θ = C z (unitAddTorusFlow β s θ) at hComp
  rw [hθ, hComp, hLift]
  have hz' : 0 < (z + (s : ℂ)).im := by simpa using hz
  simp only [F, torusPoissonCayleyField, ite_eq_left hz, ite_eq_left hz', hCov z hz]

/-- The normalized Haar Fourier coefficient of the bounded Cayley field. -/
def torusPoissonCayleyCoeff (n : d → ℤ) (z : ℂ) : ℂ :=
  mFourierCoeff (torusPoissonCayleyL2 β S T hT hCont hCount hAdvance z) n

/-- The coefficient integrates the scalar representative against the torus mode. -/
theorem torusPoissonCayleyCoeff_eq_integral (n : d → ℤ) (z : ℂ) :
    torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n z =
      ∫ θ, mFourier (-n) θ * torusPoissonCayleyField β S T hT hCont hCount z θ := by
  unfold torusPoissonCayleyCoeff mFourierCoeff
  apply integral_congr_ae
  filter_upwards [coeFn_torusPoissonCayleyL2 β S T hT hCont hCount hAdvance z] with θ hθ
  rw [hθ, smul_eq_mul]

/-- The derivative of a Cayley coefficient is the corresponding Haar
integral of the actual pointwise complex derivative. -/
theorem hasDerivAt_torusPoissonCayleyCoeff_eq_integral_deriv (n : d → ℤ)
    {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n)
      (∫ θ, mFourier (-n) θ * deriv (fun v => torusPoissonCayleyField β S T hT hCont hCount v θ) z) z := by
  let F := torusPoissonCayleyField β S T hT hCont hCount
  let χ := mFourier (-n)
  let G (v : ℂ) (θ : UnitAddTorus d) := χ θ * F v θ
  have hEq : torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n =
      fun v => ∫ θ, G v θ := funext
    (torusPoissonCayleyCoeff_eq_integral β S T hT hCont hCount hAdvance n)
  have hMeas (v : ℂ) : AEStronglyMeasurable (G v) volume :=
    χ.continuous.aestronglyMeasurable.mul
      (aemeasurable_torusPoissonCayleyField β S T hT hCont hCount hAdvance v).aestronglyMeasurable
  have hGood := ae_analyticOnNhd_norm_torusPoissonCayleyField β S T hT hCont hCount hAdvance
  have hA : ∀ᵐ θ ∂volume, DifferentiableOn ℂ (fun v => G v θ) {z : ℂ | 0 < z.im} ∧
      ∀ v : ℂ, ‖G v θ‖ ≤ 1 := by
    filter_upwards [hGood] with θ hθ
    refine ⟨(differentiableOn_const (χ θ)).mul hθ.1.differentiableOn, fun v => ?_⟩
    change ‖χ θ * F v θ‖ ≤ 1
    rw [norm_mul, norm_mFourier_apply_eq_one, one_mul]
    exact hθ.2 v
  have hD : (∫ θ, deriv (fun v => G v θ) z) =
      ∫ θ, χ θ * deriv (fun v => F v θ) z := by
    apply integral_congr_ae
    filter_upwards [hGood] with θ hθ
    exact ((hθ.1 z hz).differentiableAt.hasDerivAt.const_mul (χ θ)).deriv
  rw [hEq, ← hD]
  exact hasDerivAt_integral_bounded_holomorphic_family G hMeas hA hz

/-- The Fourier coefficient of the Cayley field is holomorphic on the upper half-plane. -/
theorem differentiableOn_torusPoissonCayleyCoeff (n : d → ℤ) :
    DifferentiableOn ℂ (torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n) {z : ℂ | 0 < z.im} :=
  fun _ hz => (hasDerivAt_torusPoissonCayleyCoeff_eq_integral_deriv
    β S T hT hCont hCount hAdvance n hz).differentiableAt.differentiableWithinAt

/-- Real covariance of a scalar coefficient is the physical frequency character. -/
theorem torusPoissonCayleyCoeff_add_real (n : d → ℤ) (z : ℂ) (hz : 0 < z.im) (s : ℝ) :
    torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n (z + (s : ℂ)) =
      combModulationCharacter (torusDirectionalFrequency β n) s *
        torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n z := by
  simp only [torusPoissonCayleyCoeff]
  rw [torusPoissonCayleyL2_add_real β S T hT hCont hCount hAdvance z hz s,
    mFourierCoeff_torusL2PhaseAdvance]

/-- Each scalar Fourier coefficient has modulus at most one. -/
theorem norm_torusPoissonCayleyCoeff_le_one (n : d → ℤ) (z : ℂ) :
    ‖torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n z‖ ≤ 1 := by
  rw [torusPoissonCayleyCoeff_eq_integral]
  have hBound : ∀ᵐ θ ∂volume,
      ‖mFourier (-n) θ * torusPoissonCayleyField β S T hT hCont hCount z θ‖ ≤ 1 := by
    filter_upwards [ae_analyticOnNhd_norm_torusPoissonCayleyField β S T hT hCont hCount hAdvance]
      with θ hθ
    rw [norm_mul, norm_mFourier_apply_eq_one, one_mul]
    exact hθ.2 z
  simpa using norm_integral_le_of_norm_le_const hBound


private theorem eq_of_differentiableOn_add_real_invariant (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hInv : ∀ z : ℂ, 0 < z.im → ∀ t : ℝ, f (z + (t : ℂ)) = f z)
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) : f z = f w := by
  let U := {v : ℂ | 0 < v.im}
  have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hZero (v : ℂ) (hv : v ∈ U) : HasDerivAt f 0 v := by
    have hD := (hf.differentiableAt (hOpen.mem_nhds hv)).hasDerivAt
    have hShift : HasDerivAt (fun a : ℂ => f (v + a)) (deriv f v) 0 := by
      have hLin : HasDerivAt (fun a : ℂ => v + a) 1 0 := (hasDerivAt_id' 0).const_add v
      simpa only [Function.comp_def, mul_one] using hD.comp_of_eq 0 hLin (by simp)
    have hReal : HasDerivAt (fun t : ℝ => f (v + (t : ℂ))) (deriv f v) 0 := by
      simpa only [Complex.ofReal_zero] using
        (show HasDerivAt (fun a : ℂ => f (v + a)) (deriv f v) ((0 : ℝ) : ℂ) from by
          simpa only [Complex.ofReal_zero] using hShift).comp_ofReal
    have hConst : HasDerivAt (fun t : ℝ => f (v + (t : ℂ))) (0 : ℂ) 0 :=
      (hasDerivAt_const 0 (f v)).congr_of_eventuallyEq
        (Eventually.of_forall (hInv v hv))
    have hD0 := hReal.unique hConst
    rwa [hD0] at hD
  have hB := (convex_halfSpace_im_gt 0).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (hZero v hv).hasDerivWithinAt) (C := 0)
    (fun _ _ => by rw [norm_zero]) hw hz
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [zero_mul] using hB))

/-- Complex phase and height evolution of the Cayley Fourier coefficient
is the exact exponential of the physical frequency. -/
theorem torusPoissonCayleyCoeff_eq_exp_mul (n : d → ℤ) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n w =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (torusDirectionalFrequency β n : ℂ) * (w - z)) *
        torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n z := by
  let A := torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n
  let κ := 2 * (Real.pi : ℂ) * Complex.I * (torusDirectionalFrequency β n : ℂ)
  let B (v : ℂ) := Complex.exp (-κ * v) * A v
  have hExp : Differentiable ℂ (fun v => Complex.exp (-κ * v)) := by fun_prop
  have hB : DifferentiableOn ℂ B {z : ℂ | 0 < z.im} :=
    hExp.differentiableOn.mul (differentiableOn_torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n)
  have hInv (v : ℂ) (hv : 0 < v.im) (s : ℝ) : B (v + (s : ℂ)) = B v := by
    change Complex.exp (-κ * (v + (s : ℂ))) * A (v + (s : ℂ)) = _
    have hA : A (v + (s : ℂ)) = Complex.exp (κ * (s : ℂ)) * A v := by
      simpa only [A, κ, combModulationCharacter_eq_exp] using
        torusPoissonCayleyCoeff_add_real β S T hT hCont hCount hAdvance n v hv s
    rw [hA, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have he := eq_of_differentiableOn_add_real_invariant B hB hInv hw hz
  change A w = Complex.exp (κ * (w - z)) * A z
  calc
    A w = Complex.exp (κ * w) * B w := by
      simp only [B, ← mul_assoc, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]
    _ = Complex.exp (κ * w) * B z := by rw [he]
    _ = _ := by
      simp only [B, ← mul_assoc, ← Complex.exp_add]
      congr 2
      ring

/-- The complex derivative of the coefficient multiplies it by the
signed physical frequency times `2πi`. -/
theorem hasDerivAt_torusPoissonCayleyCoeff (n : d → ℤ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n)
      (2 * (Real.pi : ℂ) * Complex.I * (torusDirectionalFrequency β n : ℂ) *
        torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n z) z := by
  let A := torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n
  let κ := 2 * (Real.pi : ℂ) * Complex.I * (torusDirectionalFrequency β n : ℂ)
  have h := ((((hasDerivAt_id' z).sub_const z).const_mul κ).cexp).mul_const (A z)
  have hD : HasDerivAt (fun w => Complex.exp (κ * (w - z)) * A z) (κ * A z) z := by
    simpa only [sub_self, mul_zero, Complex.exp_zero, mul_one, one_mul] using h
  apply hD.congr_of_eventuallyEq
  have hOpen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  filter_upwards [hOpen.mem_nhds hz] with w hw
  exact torusPoissonCayleyCoeff_eq_exp_mul β S T hT hCont hCount hAdvance n hz hw

private theorem continuous_mFourierCoeff_L2 (n : d → ℤ) :
    Continuous (fun f : TorusL2(d) => mFourierCoeff f n) := by
  simp_rw [← mFourierBasis_repr]
  exact (lp.evalCLM ℂ (fun _ : d → ℤ => ℂ) 2 n).continuous.comp
    (mFourierBasis (d := d)).repr.continuous

/-- The exact exponential coefficient at positive height is determined
by the actual unit-modulus Haar boundary value. -/
theorem torusPoissonCayleyCoeff_at_height (n : d → ℤ) (y : ℝ) (hy : 0 < y) :
    torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n ((y : ℂ) * Complex.I) =
      (Real.exp (-(2 * Real.pi * torusDirectionalFrequency β n * y)) : ℂ) *
        mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) n := by
  let A (v : ℝ) := torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n ((v : ℂ) * Complex.I)
  let B := mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) n
  let k := -(2 * Real.pi * torusDirectionalFrequency β n)
  let E (v : ℝ) : ℂ := (Real.exp (k * (y - v)) : ℝ)
  have hA : Tendsto A (𝓝[>] 0) (𝓝 B) :=
    ((continuous_mFourierCoeff_L2 n).tendsto _).comp
      (tendsto_torusPoissonCayleyBoundary_L2 β S T hT hCont hCount hAdvance)
  have hE : Tendsto E (𝓝[>] 0) (𝓝 (Real.exp (k * y) : ℂ)) := by
    have hContE : Continuous E := by unfold E; fun_prop
    simpa only [E, sub_zero] using
      (hContE.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hEq : (fun v => E v * A v) =ᶠ[𝓝[>] 0] fun _ => A y := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hv' : 0 < v := hv
    have hTime := torusPoissonCayleyCoeff_eq_exp_mul β S T hT hCont hCount hAdvance n
      (z := (v : ℂ) * Complex.I) (w := (y : ℂ) * Complex.I)
      (by simpa [Complex.mul_im] using hv') (by simpa [Complex.mul_im] using hy)
    have hArg :
        2 * (Real.pi : ℂ) * Complex.I * (torusDirectionalFrequency β n : ℂ) *
          ((y : ℂ) * Complex.I - (v : ℂ) * Complex.I) = Complex.ofReal (k * (y - v)) := by
      apply Complex.ext <;>
        simp only [k, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, Complex.re_ofNat, Complex.im_ofNat] <;> ring
    rw [hArg, ← Complex.ofReal_exp] at hTime
    exact hTime.symm
  have hLim : A y = (Real.exp (k * y) : ℂ) * B :=
    tendsto_nhds_unique tendsto_const_nhds ((hE.mul hA).congr' hEq)
  simpa only [A, B, k, neg_mul] using hLim

/-- The coherent Cayley boundary has zero coefficient at each negative
physical frequency. -/
theorem mFourierCoeff_torusPoissonCayleyBoundaryL2_eq_zero_of_neg (n : d → ℤ)
    (hn : torusDirectionalFrequency β n < 0) :
    mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) n = 0 := by
  let a := mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) n
  change a = 0
  by_contra ha
  have hPos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let k := -(2 * Real.pi * torusDirectionalFrequency β n)
  have hk : 0 < k := neg_pos.mpr (mul_neg_of_pos_of_neg Real.two_pi_pos hn)
  have hGrow : Tendsto (fun y : ℝ => Real.exp (k * y)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hk tendsto_id)
  have hEventually : ∀ᶠ y : ℝ in atTop, 0 < y ∧ (‖a‖)⁻¹ < Real.exp (k * y) :=
    (eventually_gt_atTop 0).and (hGrow.eventually_gt_atTop (norm a)⁻¹)
  obtain ⟨y, hy, hLarge⟩ := hEventually.exists
  have hNorm := norm_torusPoissonCayleyCoeff_le_one β S T hT hCont hCount hAdvance n
    ((y : ℂ) * Complex.I)
  rw [torusPoissonCayleyCoeff_at_height β S T hT hCont hCount hAdvance n y hy, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hNorm
  have hBound : Real.exp (k * y) * ‖a‖ ≤ 1 := by
    simpa only [k, a, neg_mul] using hNorm
  have hStrict : 1 < Real.exp (k * y) * ‖a‖ :=
    (div_lt_iff₀ hPos).mp (by simpa only [one_div] using hLarge)
  exact (not_lt_of_ge hBound) hStrict

/-- Parseval gives total squared Fourier mass one for the coherent boundary. -/
theorem hasSum_sq_torusPoissonCayleyBoundaryL2 :
    HasSum (fun n : d → ℤ =>
      ‖mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) n‖ ^ 2) 1 := by
  have he : (∫ θ, ‖torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance θ‖ ^ 2) = 1 := by
    calc
      _ = ∫ θ : UnitAddTorus d, (1 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_norm_torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance]
          with θ hθ
        rw [hθ, one_pow]
      _ = 1 := by simp
  rw [← he]
  exact hasSum_sq_mFourierCoeff _

end FourierCoefficients

end
end MeyerGeneralProblem
