module

public import MeyerGeneralProblem.Distribution.TorusPoissonPhaseDerivative
public import Mathlib.Analysis.Complex.LocallyUniformLimit

@[expose] public section

/-!
# Holomorphy of the positive Poisson field in the Haar norm

On the upper half-plane a nonnegative-frequency complex exponential
is a contractive multiplier on square-summable sequences. Uniform
norm approximation by finite Fourier sums makes the field
holomorphic with values in the Haar Hilbert space.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Metric ProbabilityTheory Set UnitAddTorus
open scoped FourierTransform NNReal Topology

private def halfPlaneWave (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * Complex.ofReal a * z)

private theorem norm_halfPlaneWave_le_one {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖halfPlaneWave a z‖ ≤ 1 := by
  rw [halfPlaneWave, Complex.norm_exp, Real.exp_le_one_iff]
  simpa only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero, zero_add, zero_sub, neg_mul] using
    (neg_nonpos.mpr (mul_nonneg ha hz))

private def lpHalfPlaneWave {ι : Type*} (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (z : ℂ) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  lpDiagonalMul (fun i => if 0 ≤ z.im then halfPlaneWave (a i) z else 0) zero_le_one
    (fun i => by
      split_ifs with hz
      · exact norm_halfPlaneWave_le_one (ha i) hz
      · simp)

private theorem lpHalfPlaneWave_apply {ι : Type*} (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {z : ℂ} (hz : 0 ≤ z.im) (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    lpHalfPlaneWave a ha z f i = halfPlaneWave (a i) z * f i := by
  simp [lpHalfPlaneWave, lpDiagonalMul_apply, hz]

private theorem norm_lpHalfPlaneWave_le {ι : Type*} (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (z : ℂ) (f : lp (fun _ : ι => ℂ) 2) : ‖lpHalfPlaneWave a ha z f‖ ≤ ‖f‖ := by
  simpa only [lpHalfPlaneWave, one_mul] using
    (norm_lpDiagonalMul_apply_le (fun i => if 0 ≤ z.im then halfPlaneWave (a i) z else 0)
      zero_le_one (fun i => by
        split_ifs with hz
        · exact norm_halfPlaneWave_le_one (ha i) hz
        · simp) f)

private theorem differentiableOn_lpHalfPlaneWave {ι : Type*}
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (f : lp (fun _ : ι => ℂ) 2) :
    DifferentiableOn ℂ (fun z => lpHalfPlaneWave a ha z f) {z : ℂ | 0 < z.im} := by
  classical
  let X (s : Finset ι) : lp (fun _ : ι => ℂ) 2 := ∑ i ∈ s, lp.single 2 i (f i)
  let F (s : Finset ι) (z : ℂ) : lp (fun _ : ι => ℂ) 2 :=
    ∑ i ∈ s, halfPlaneWave (a i) z • lp.single 2 i (f i)
  have hApprox (s : Finset ι) (z : ℂ) (hz : 0 ≤ z.im) :
      F s z = lpHalfPlaneWave a ha z (X s) := by
    simp only [F, X, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    ext j
    rw [lpHalfPlaneWave_apply a ha hz, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases h : j = i
    · subst j
      simp only [lp.single_apply_self]
    · rw [lp.single_apply_ne _ _ _ h, mul_zero, mul_zero]
  have hX : Tendsto X atTop (𝓝 f) := lp.hasSum_single (by norm_num) f
  have hUniform : TendstoUniformlyOn F (fun z => lpHalfPlaneWave a ha z f) atTop
      {z : ℂ | 0 < z.im} := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    filter_upwards [Metric.tendsto_nhds.mp hX ε hε] with s hs z hz
    have hz' : 0 < z.im := hz
    rw [dist_comm, hApprox s z hz'.le, dist_eq_norm, ← map_sub]
    exact (norm_lpHalfPlaneWave_le a ha z _).trans_lt (by simpa only [dist_eq_norm] using hs)
  apply hUniform.tendstoLocallyUniformlyOn.differentiableOn
  · apply Eventually.of_forall
    intro s
    apply Differentiable.differentiableOn
    apply Differentiable.fun_sum
    intro i _
    unfold halfPlaneWave
    fun_prop
  · exact isOpen_lt continuous_const Complex.continuous_im

/-- Use normalized Haar measure on each circle factor of the phase torus. -/
local instance poissonAnalyticCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

private theorem halfPlaneWave_eq_modulation_mul_damping {b : ℝ} (hb : 0 ≤ b)
    (z : ℂ) (a : ℝ) :
    halfPlaneWave (2 * Real.pi * |b|) (z - (a : ℂ) * Complex.I) =
      combModulationCharacter b z.re *
        (Real.exp (-(2 * Real.pi * (z.im - a)) * |b|) : ℂ) := by
  rw [halfPlaneWave, combModulationCharacter_eq_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, abs_of_nonneg hb] <;> ring

/-- The complex-height Poisson field is holomorphic in the normalized Haar
`L²` norm. It is built from the actual real phase advance and physical height. -/
theorem analyticOnNhd_torusSupportPositivePoissonL2 {d : Type*} [Fintype d]
    (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
    (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => torusL2PhaseAdvance β z.re
        (torusSupportPositivePoissonL2 β S T hT hCont hCount z.im.toNNReal))
      {z : ℂ | 0 < z.im} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_im)
  intro z₀ hz₀
  have hIm : 0 < z₀.im := hz₀
  let a := z₀.im / 2
  have ha : 0 < a := half_pos hIm
  have ha₀ : a < z₀.im := half_lt_self hIm
  let e := (mFourierBasis (d := d)).repr
  let G (y : ℝ) := torusSupportPositivePoissonL2 β S T hT hCont hCount y.toNNReal
  let rate (n : d → ℤ) := 2 * Real.pi * |torusDirectionalFrequency β n|
  have hRate (n : d → ℤ) : 0 ≤ rate n := mul_nonneg Real.two_pi_pos.le (abs_nonneg _)
  let w (z : ℂ) := z - (a : ℂ) * Complex.I
  have hw (z : ℂ) : (w z).im = z.im - a := by simp [w, Complex.mul_im]
  have hEq (z : ℂ) (hz : a < z.im) :
      torusL2PhaseAdvance β z.re (G z.im) =
        e.symm (lpHalfPlaneWave rate hRate (w z) (e (G a))) := by
    apply e.injective
    ext n
    rw [e.apply_symm_apply, lpHalfPlaneWave_apply rate hRate (by rw [hw]; linarith only [hz])]
    change (mFourierBasis (d := d)).repr (torusL2PhaseAdvance β z.re (G z.im)) n =
      _ * (mFourierBasis (d := d)).repr (G a) n
    rw [mFourierBasis_repr, mFourierBasis_repr, mFourierCoeff_torusL2PhaseAdvance]
    rcases lt_or_ge (torusDirectionalFrequency β n) 0 with hn | hn
    · have hZero (y : ℝ) : mFourierCoeff (G y) n = 0 :=
        mFourierCoeff_torusSupportPositivePoissonL2_eq_zero_of_neg β S T hT hCont hCount _ n hn
      rw [hZero, hZero, mul_zero, mul_zero]
    · let s := (z.im - a).toNNReal
      have hs : 0 < s := Real.toNNReal_pos.mpr (sub_pos.mpr hz)
      have hsa : (s : ℝ) = z.im - a := Real.coe_toNNReal _ (sub_nonneg.mpr hz.le)
      have hSum : s + a.toNNReal = z.im.toNNReal := by
        apply NNReal.eq
        rw [NNReal.coe_add, hsa, Real.coe_toNNReal _ ha.le, Real.coe_toNNReal _ (ha.trans hz).le]
        ring
      have hCoeff := mFourierCoeff_torusSupportPositivePoissonL2_add β S T hT hAdvance hCont hCount
        hs (Real.toNNReal_pos.mpr ha) n
      rw [hSum, hsa] at hCoeff
      change mFourierCoeff (G z.im) n = _ at hCoeff
      rw [hCoeff, ← mul_assoc]
      congr 1
      exact (halfPlaneWave_eq_modulation_mul_damping hn z a).symm
  have hOpen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hw₀ : w z₀ ∈ {z : ℂ | 0 < z.im} := by
    change 0 < (w z₀).im
    rw [hw]
    exact sub_pos.mpr ha₀
  have hWave := (differentiableOn_lpHalfPlaneWave rate hRate (e (G a))).differentiableAt
    (hOpen.mem_nhds hw₀)
  have hShift : DifferentiableAt ℂ w z₀ := by unfold w; fun_prop
  have hCompose : DifferentiableAt ℂ
      (fun z => e.symm (lpHalfPlaneWave rate hRate (w z) (e (G a)))) z₀ :=
    e.symm.toContinuousLinearEquiv.differentiableAt.comp z₀ (hWave.comp z₀ hShift)
  apply DifferentiableAt.differentiableWithinAt
  apply hCompose.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds ha₀] with z hz
  exact hEq z hz

/-- At every real center and positive height, the real part of the shifted
Haar field represents half the actual Poisson integral at that center. -/
theorem ae_re_torusL2PhaseAdvance_supportPositivePoisson {d : Type*} [Fintype d]
    (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
    (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
    (x : ℝ) {y : ℝ≥0} (hy : 0 < y) :
    ∀ᵐ θ ∂volume,
      (torusL2PhaseAdvance β x (torusSupportPositivePoissonL2 β S T hT hCont hCount y) θ).re =
        (∫ t, cauchyPDFReal x y t ∂discreteSupportCount (T θ)) / 2 := by
  let G := torusSupportPositivePoissonL2 β S T hT hCont hCount y
  let P (θ : UnitAddTorus d) := (∫ t, cauchyPDFReal 0 y t ∂discreteSupportCount (T θ)) / 2
  have hReal : (fun θ => (G θ).re) =ᵐ[volume] P :=
    ae_re_torusSupportPositivePoissonL2 β S T hT hCont hCount y
  let hPres := measurePreserving_unitAddTorusFlow β x
  filter_upwards [hPres.quasiMeasurePreserving.ae_eq_comp hReal,
    Lp.coeFn_compMeasurePreserving G hPres] with θ hθ hLift
  change torusL2PhaseAdvance β x G θ = G (unitAddTorusFlow β x θ) at hLift
  change (G (unitAddTorusFlow β x θ)).re = P (unitAddTorusFlow β x θ) at hθ
  change (torusL2PhaseAdvance β x G θ).re =
    (∫ t, cauchyPDFReal x y t ∂discreteSupportCount (T θ)) / 2
  rw [hLift, hθ]
  dsimp only [P]
  rw [hAdvance, integral_poisson_discreteSupportCount_translation _ _ _ hy, zero_sub, neg_neg]

end
end MeyerGeneralProblem
