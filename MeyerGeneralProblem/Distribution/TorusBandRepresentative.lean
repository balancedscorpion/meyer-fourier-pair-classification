module

public import MeyerGeneralProblem.Distribution.TorusOrbitAverage
public import MeyerGeneralProblem.Distribution.CompactFrequencyKernel
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# Entire representatives of bounded-band torus orbits

Convolution with the entire inverse Fourier kernel gives an entire
representative on almost every phase orbit. Its real restriction agrees
almost everywhere with the original measurable orbit.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set UnitAddTorus
open scoped ENNReal FourierTransform SchwartzMap Topology

/-- A function with finite weighted square integral pairs absolutely with
every measurable kernel dominated by the same integrable weight. -/
theorem integrable_mul_of_le_inverse_quadratic_weight
    (g k : ℝ → ℂ) (hg : Measurable g) (hk : Measurable k) (C : ℝ)
    (hSq : (∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2)⁻¹) *
      ENNReal.ofReal (‖g x‖ ^ 2)) < ∞)
    (hBound : ∀ x : ℝ, ‖k x‖ ≤ C * (1 + x ^ 2)⁻¹) :
    Integrable (fun x => k x * g x) := by
  let a (x : ℝ) := (1 + x ^ 2)⁻¹
  let w (x : ℝ) := ENNReal.ofReal (a x)
  let ν := (volume : Measure ℝ).withDensity w
  have ha (x : ℝ) : 0 ≤ a x := by dsimp [a]; positivity
  have hw : Measurable w := ENNReal.measurable_ofReal.comp
    ((measurable_const.add (measurable_id.pow_const 2)).inv)
  have hAbs : (fun x : ℝ => ENNReal.ofReal ‖a x‖) = w := by
    funext x
    exact congrArg ENNReal.ofReal (Real.norm_of_nonneg (ha x))
  have hwFin : (∫⁻ x, w x) < ∞ := by
    have h := integrable_inv_one_add_sq.hasFiniteIntegral
    change HasFiniteIntegral a volume at h
    rw [hasFiniteIntegral_iff_norm, hAbs] at h
    exact h
  have : IsFiniteMeasure ν := ⟨by
    change (volume : Measure ℝ).withDensity w univ < ∞
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hwFin⟩
  have hIntSq : Integrable (fun x : ℝ => ‖g x‖ ^ 2) ν := by
    refine ⟨(hg.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hNorm : (fun x : ℝ => ENNReal.ofReal ‖‖g x‖ ^ 2‖) =
        fun x : ℝ => ENNReal.ofReal (‖g x‖ ^ 2) := by
      funext x
      exact congrArg ENNReal.ofReal (Real.norm_of_nonneg (sq_nonneg _))
    rw [hNorm]
    change (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂(volume : Measure ℝ).withDensity w) < ∞
    calc
      _ = (∫⁻ x, w x * ENNReal.ofReal (‖g x‖ ^ 2)) :=
        lintegral_withDensity_eq_lintegral_mul volume hw
          (ENNReal.measurable_ofReal.comp (hg.norm.pow_const 2))
      _ < ∞ := hSq
  have hLp : MemLp g 2 ν := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr hIntSq
  have hInt : Integrable g ν := hLp.integrable (by norm_num)
  have hWeighted := (integrable_withDensity_iff_integrable_smul' hw
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hInt
  have hWeighted' : Integrable (fun x => a x • g x) := by
    simpa only [w, ENNReal.toReal_ofReal (ha _)] using hWeighted
  apply ((hWeighted'.norm).const_mul C).mono' (hk.mul hg).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    change ‖k x * g x‖ ≤ C * ‖a x • g x‖
    rw [norm_mul, norm_smul, Real.norm_of_nonneg (ha x)]
    calc
      ‖k x‖ * ‖g x‖ ≤ (C * a x) * ‖g x‖ :=
        mul_le_mul_of_nonneg_right (hBound x) (norm_nonneg _)
      _ = C * (a x * ‖g x‖) := mul_assoc _ _ _

/-- Local inverse-quadratic bounds on an entire kernel and its derivative
justify differentiation of its convolution with weighted square-integrable data. -/
theorem differentiable_integral_translate_mul_of_weighted_sq
    (g : ℝ → ℂ) (hg : Measurable g) (k k' : ℂ → ℂ) (hk' : Continuous k')
    (hDeriv : ∀ z, HasDerivAt k (k' z) z)
    (hSq : (∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2)⁻¹) *
      ENNReal.ofReal (‖g x‖ ^ 2)) < ∞)
    (hBound : ∀ z₀ : ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball z₀ 1, ∀ x : ℝ,
      ‖k (z - (x : ℂ))‖ ≤ C * (1 + x ^ 2)⁻¹ ∧
      ‖k' (z - (x : ℂ))‖ ≤ C * (1 + x ^ 2)⁻¹) :
    Differentiable ℂ (fun z => ∫ x : ℝ, k (z - (x : ℂ)) * g x) := by
  intro z₀
  obtain ⟨C, hC, hB⟩ := hBound z₀
  let w (x : ℝ) := (1 + x ^ 2)⁻¹
  let b (x : ℝ) := C * w x * ‖g x‖
  let H (z : ℂ) (x : ℝ) := k (z - (x : ℂ)) * g x
  let H' (z : ℂ) (x : ℝ) := k' (z - (x : ℂ)) * g x
  have hw (x : ℝ) : 0 ≤ w x := by dsimp [w]; positivity
  have hK : Continuous k := continuous_iff_continuousAt.mpr fun z => (hDeriv z).continuousAt
  have hc (z : ℂ) : Continuous (fun x : ℝ => z - (x : ℂ)) :=
    continuous_const.sub Complex.continuous_ofReal
  have hH (z : ℂ) : Measurable (H z) := (hK.comp (hc z)).measurable.mul hg
  have hH' : Measurable (H' z₀) := (hk'.comp (hc z₀)).measurable.mul hg
  have hz₀ : z₀ ∈ Metric.ball z₀ (1 : ℝ) := Metric.mem_ball_self one_pos
  have hInt : Integrable (H z₀) :=
    integrable_mul_of_le_inverse_quadratic_weight g (fun x : ℝ => k (z₀ - (x : ℂ)))
      hg (hK.comp (hc z₀)).measurable C hSq (fun x => (hB z₀ hz₀ x).1)
  have hWeight : Measurable (fun x : ℝ => ((C * w x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (measurable_const.mul ((measurable_const.add (measurable_id.pow_const 2)).inv))
  have hDom : Integrable b := by
    have hI := integrable_mul_of_le_inverse_quadratic_weight g
      (fun x : ℝ => ((C * w x : ℝ) : ℂ)) hg hWeight C hSq
      (fun x => by rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hC (hw x))])
    have hEq : (fun x : ℝ => ‖((C * w x : ℝ) : ℂ) * g x‖) = b := by
      funext x
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hC (hw x))]
    rw [← hEq]
    exact hI.norm
  have hDomBound : ∀ᵐ x ∂volume, ∀ z ∈ Metric.ball z₀ 1, ‖H' z x‖ ≤ b x :=
    Eventually.of_forall fun x z hz => by
      rw [show H' z x = k' (z - (x : ℂ)) * g x from rfl, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB z hz x).2 (norm_nonneg _)
  have hDiff : ∀ᵐ x ∂volume, ∀ z ∈ Metric.ball z₀ 1, HasDerivAt (fun z => H z x) (H' z x) z :=
    Eventually.of_forall fun x z _ => by
      have hz : HasDerivAt (fun z : ℂ => z - (x : ℂ)) 1 z :=
        (hasDerivAt_id z).sub_const (x : ℂ)
      simpa only [H, H', Function.comp_apply, mul_one] using
        ((hDeriv (z - (x : ℂ))).comp z hz).mul_const (g x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ one_pos) (Eventually.of_forall fun z => (hH z).aestronglyMeasurable)
    hInt hH'.aestronglyMeasurable hDomBound hDom hDiff).2.differentiableAt

/-- Use normalized Haar measure on the circle factors of the phase torus. -/
local instance bandRepresentativeCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩


/-- Phase advances add their real time parameters. -/
theorem unitAddTorusFlow_add_apply {d : Type*} (β : d → ℝ) (u v : ℝ)
    (θ : UnitAddTorus d) :
    unitAddTorusFlow β u (unitAddTorusFlow β v θ) = unitAddTorusFlow β (u + v) θ := by
  funext i
  simp only [unitAddTorusFlow, mul_add, AddCircle.coe_add]
  abel

/-- The Fourier multiplier of the reflected inverse Fourier kernel
is the original Schwartz cutoff. -/
theorem integral_neg_inverseFourier_mul_character (χ : SchwartzMap ℝ ℂ) (b : ℝ) :
    (∫ t : ℝ, (𝓕⁻ χ : SchwartzMap ℝ ℂ) (-t) * combModulationCharacter b t) = χ b := by
  let K : SchwartzMap ℝ ℂ := 𝓕⁻ χ
  let H (t : ℝ) := K (-t) * combModulationCharacter b t
  calc
    _ = ∫ t, H (-t) := (integral_neg_eq_self H volume).symm
    _ = (𝓕 (K : ℝ → ℂ)) b := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      apply integral_congr_ae
      filter_upwards with t
      simp only [H, neg_neg, combModulationCharacter_eq_exp, smul_eq_mul]
      rw [mul_comm]
      congr 2
      push_cast
      ring
    _ = χ b := by
      rw [← SchwartzMap.fourier_coe, show K = 𝓕⁻ χ from rfl, FourierTransform.fourier_fourierInv_eq]

/-- A bounded-band torus L² function has an entire representative
along almost every real phase orbit, with the original orbit as its
real restriction almost everywhere. The representative is the
compact-frequency convolution with a measurable Haar representative. -/
theorem exists_entire_torusOrbit_representative_of_bounded_band {d : Type*} [Fintype d]
    (β : d → ℝ) (W : ℝ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hBand : ∀ n : d → ℤ, torusDirectionalFrequency β n ∉ Icc 0 W → mFourierCoeff f n = 0) :
    ∃ (N : ℕ) (k : ℂ → ℂ) (F : UnitAddTorus d → ℂ), W ≤ (N : ℝ) + 1 ∧
      Differentiable ℂ k ∧
      (∀ x : ℝ, k (x : ℂ) = (𝓕⁻ (scaledCompactSchwartzCutoff N) : SchwartzMap ℝ ℂ) x) ∧
      Measurable F ∧ F =ᵐ[volume] f ∧
      ∀ᵐ θ ∂volume,
        Differentiable ℂ (fun z => ∫ t : ℝ, k (z - (t : ℂ)) * F (unitAddTorusFlow β t θ)) ∧
        ∀ᵐ x : ℝ ∂volume,
          (∫ t : ℝ, k ((x : ℂ) - (t : ℂ)) * F (unitAddTorusFlow β t θ)) =
            F (unitAddTorusFlow β x θ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt W
  let χ := scaledCompactSchwartzCutoff N
  obtain ⟨k, k', hk, hk', hkReal, hBound⟩ :=
    exists_entire_inverseFourierKernel_of_hasCompactSupport χ (scaledCompactSchwartzCutoff_hasCompactSupport N)
  obtain ⟨F, hF, hRep, hSq⟩ := exists_torusLp_representative_with_weighted_orbits β f
  have hkDiff : Differentiable ℂ k := fun z => (hk z).differentiableAt
  let K := (𝓕⁻ χ : SchwartzMap ℝ ℂ)
  let kn (t : ℝ) := k (-(t : ℂ))
  have hkNeg : kn = fun t : ℝ => K (-t) := by
    funext t
    simpa only [kn, Complex.ofReal_neg] using hkReal (-t)
  have hkn : Measurable kn := by
    rw [hkNeg]
    exact (K.continuous.comp continuous_neg).measurable
  have hkInt : Integrable kn := by
    rw [hkNeg]
    exact K.integrable.comp_neg
  have hPass (n : d → ℤ) (hn : mFourierCoeff f n ≠ 0) :
      (∫ t, kn t * combModulationCharacter (torusDirectionalFrequency β n) t) = 1 := by
    have hb : torusDirectionalFrequency β n ∈ Icc 0 W := by
      by_contra hc
      exact hn (hBand n hc)
    rw [hkNeg, integral_neg_inverseFourier_mul_character]
    exact scaledCompactSchwartzCutoff_eq_one N (by
      rw [abs_of_nonneg hb.1]
      exact hb.2.trans ((le_of_lt hN).trans (le_add_of_nonneg_right zero_le_one)))
  let A := torusOrbitAverage β kn F
  have hA : Measurable A := measurable_torusOrbitAverage β hkn hF
  have hAF : A =ᵐ[volume] F :=
    ae_torusOrbitAverage_eq_of_multiplier_one β f hkn hkInt hF hRep hPass
  have hOrbit := ae_torusOrbit_congr β A F hA hF hAF
  refine ⟨N, k, F, (le_of_lt hN).trans (le_add_of_nonneg_right zero_le_one),
    hkDiff, hkReal, hF, hRep, ?_⟩
  filter_upwards [hSq, hOrbit] with θ hθSq hθOrbit
  have hFθ : Measurable (fun t : ℝ => F (unitAddTorusFlow β t θ)) :=
    hF.comp ((continuous_unitAddTorusFlow β).measurable.comp (measurable_id.prodMk measurable_const))
  refine ⟨differentiable_integral_translate_mul_of_weighted_sq
    (fun t : ℝ => F (unitAddTorusFlow β t θ)) hFθ k k' hk' hk hθSq hBound, ?_⟩
  filter_upwards [hθOrbit] with x hx
  calc
    _ = ∫ t : ℝ, k ((x : ℂ) - ((t + x : ℝ) : ℂ)) * F (unitAddTorusFlow β (t + x) θ) :=
      (integral_add_right_eq_self
        (fun t : ℝ => k ((x : ℂ) - (t : ℂ)) * F (unitAddTorusFlow β t θ)) x).symm
    _ = A (unitAddTorusFlow β x θ) := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [A, torusOrbitAverage] at *
      rw [← unitAddTorusFlow_add_apply β t x, Complex.ofReal_add]
      have hT : (x : ℂ) - ((t : ℂ) + (x : ℂ)) = -(t : ℂ) := by abel
      rw [hT]
    _ = _ := hx

end
end MeyerGeneralProblem
