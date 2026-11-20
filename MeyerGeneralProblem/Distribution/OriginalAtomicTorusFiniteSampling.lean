module

public import MeyerGeneralProblem.Distribution.OriginalAtomicTorusPhaseFamily
public import MeyerGeneralProblem.Distribution.BroadCauchySupportJets
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Finite-band sampling on the original atomic phase family

The original spectral masses give the phase Fourier coefficients of each
Schwartz pairing. A finite sum of physical modulations gives the finite
sampling row with a common inverse Fourier test factor.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set UnitAddTorus
open scoped FourierTransform SchwartzMap Topology

/-- Use normalized Haar measure on each circle factor. -/
local instance phaseCoefficientCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

/-- Normalized Haar measure on the circle is a probability measure. -/
local instance phaseCoefficientCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem mFourierCoeff_monomial {d : Type*} [Fintype d]
    (i n : d → ℤ) [DecidableEq d] :
    mFourierCoeff (mFourier i : UnitAddTorus d → ℂ) n = if n = i then 1 else 0 := by
  classical
  have h :
      mFourierCoeff (mFourier i : UnitAddTorus d → ℂ) n = mFourierCoeff (mFourierLp 2 i) n := by
    simp only [mFourierCoeff]
    apply integral_congr_ae
    filter_upwards [coeFn_mFourierLp 2 i] with θ hθ
    rw [hθ]
  rw [h, ← mFourierBasis_repr, ← coe_mFourierBasis, HilbertBasis.repr_self]
  by_cases hi : n = i <;> simp [hi]

set_option maxHeartbeats 800000 in
/-- The Fourier coefficient of a phase-family test pairing is the exact
sum of its original spectral contributions with the indicated label. -/
theorem mFourierCoeff_originalPhasePhysicalRecord_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (f : SchwartzMap ℝ ℂ) (n : d → ℤ) :
    mFourierCoeff (fun θ => originalPhasePhysicalRecord B label N μ hν θ f) n =
      ∑' x : B.subtype, if label x = n then (𝓕 μ) (B.isolationSchwartz x) *
        (𝓕⁻ f : SchwartzMap ℝ ℂ) x else 0 := by
  classical
  let ν : TemperedDistribution ℝ ℂ := 𝓕 μ
  let g : SchwartzMap ℝ ℂ := 𝓕⁻ f
  let coeff (x : B.subtype) := ν (B.isolationSchwartz x)
  let c (x : B.subtype) := coeff x * g x
  let H (x : B.subtype) (θ : UnitAddTorus d) := mFourier (-n) θ * (mFourier (label x) θ * c x)
  have hNorm (k : d → ℤ) (θ : UnitAddTorus d) : ‖mFourier k θ‖ = 1 := by
    simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
      Circle.norm_coe, Finset.prod_const_one]
  have hMass : Summable (weightedAtomicMassTerm B coeff N) := hν.2
  have hSample : Summable (fun x : B.subtype => coeff x * g x) :=
    weightedAtomic_samples_summable B coeff N hMass g
  have hC : Summable (fun x : B.subtype => ‖c x‖) := hSample.norm
  have hAbs (x : B.subtype) (θ : UnitAddTorus d) : ‖H x θ‖ = ‖c x‖ := by
    simp only [H, norm_mul, hNorm, one_mul]
  have hI (x : B.subtype) : Integrable (H x) := by
    have hM : Continuous (H x) :=
      (mFourier (-n)).continuous.mul ((mFourier (label x)).continuous.mul continuous_const)
    exact (integrable_const ‖c x‖).mono' hM.aestronglyMeasurable
      (Eventually.of_forall fun θ => (hAbs x θ).le)
  have hSum : Summable (fun x : B.subtype => ∫ θ, ‖H x θ‖) := by
    simpa only [hAbs, integral_const, smul_eq_mul] using
      hC.mul_left (volume.real (Set.univ : Set (UnitAddTorus d)))
  have : Countable B.subtype := B.countable_carrier.to_subtype
  simp only [mFourierCoeff, originalPhasePhysicalRecord, TemperedDistribution.fourierInv_apply,
    originalPhaseSpectralRecord, weightedAtomicDistribution_apply, phaseAtomicCoefficient,
    smul_eq_mul]
  have hEq (θ : UnitAddTorus d) :
      mFourier (-n) θ * (∑' x : B.subtype, (mFourier (label x) θ * (𝓕 μ) (B.isolationSchwartz x)) *
        (𝓕⁻ f : SchwartzMap ℝ ℂ) x) = ∑' x, H x θ := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro x
    simp only [H, c, coeff, ν, g, mul_assoc]
  simp_rw [hEq]
  rw [← integral_tsum_of_summable_integral_norm hI hSum]
  apply tsum_congr
  intro x
  simp only [H, ← mul_assoc, integral_mul_const]
  change mFourierCoeff (mFourier (label x) : UnitAddTorus d → ℂ) n * c x = _
  rw [mFourierCoeff_monomial]
  by_cases h : label x = n
  · simp only [h, ite_true, one_mul, c, coeff, ν, g]
  · simp only [h, Ne.symm h, ite_false, zero_mul]

/-- A single band character shifts the spectral label, and the inverse
Fourier test is evaluated at the resulting physical frequency. -/
theorem mFourierCoeff_originalPhasePhysicalRecord_modulated
    {d : Type*} [Fintype d] [DecidableEq d]
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ) (β : d → ℝ)
    (hLabel : ∀ x : B.subtype, torusDirectionalFrequency β (label x) = (x : ℝ))
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (g : SchwartzMap ℝ ℂ) (j k : d → ℤ) :
    mFourierCoeff (fun θ => mFourier j θ *
      originalPhasePhysicalRecord B label N μ hν θ
        (combSchwartzModulation (torusDirectionalFrequency β j) g)) k =
      (𝓕⁻ g : SchwartzMap ℝ ℂ) (torusDirectionalFrequency β k) *
        ∑' x : B.subtype, if label x = k - j then (𝓕 μ) (B.isolationSchwartz x) else 0 := by
  classical
  let a := torusDirectionalFrequency β j
  have hShift (F : UnitAddTorus d → ℂ) :
      mFourierCoeff (fun θ => mFourier j θ * F θ) k = mFourierCoeff F (k - j) := by
    simp only [mFourierCoeff, smul_eq_mul, ← mul_assoc, ← mFourier_add]
    rw [show -k + j = -(k - j) by abel]
  have hInv : 𝓕⁻ (combSchwartzModulation a g) = combSchwartzTranslation a (𝓕⁻ g) := by
    change 𝓕⁻ (𝓕 (combSchwartzTranslation a (𝓕⁻ g))) = _
    exact FourierTransform.fourierInv_fourier_eq _
  rw [hShift, mFourierCoeff_originalPhasePhysicalRecord_apply, hInv, ← tsum_mul_left]
  apply tsum_congr
  intro x
  by_cases hx : label x = k - j
  · have hFreq : a + (x : ℝ) = torusDirectionalFrequency β k := by
      rw [← hLabel x, hx]
      simp only [a, torusDirectionalFrequency, Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
      abel
    rw [ite_eq_left hx, ite_eq_left hx, combSchwartzTranslation_apply, hFreq, mul_comm]
  · rw [ite_eq_right hx, ite_eq_right hx, mul_zero]

/-- The finite-band sampling coefficient is the original spectral row
with a common inverse-Fourier test factor. -/
theorem mFourierCoeff_originalPhasePhysicalRecord_finite_modulations
    {d : Type*} [Fintype d] [DecidableEq d]
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ) (β : d → ℝ)
    (hLabel : ∀ x : B.subtype, torusDirectionalFrequency β (label x) = (x : ℝ))
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (g : SchwartzMap ℝ ℂ) (J : Finset (d → ℤ)) (r : (d → ℤ) → ℂ) (k : d → ℤ) :
    mFourierCoeff (fun θ => ∑ j ∈ J, r j * (mFourier j θ *
      originalPhasePhysicalRecord B label N μ hν θ
        (combSchwartzModulation (torusDirectionalFrequency β j) g))) k =
      (𝓕⁻ g : SchwartzMap ℝ ℂ) (torusDirectionalFrequency β k) *
        ∑ j ∈ J, r j * ∑' x : B.subtype, if label x = k - j then (𝓕 μ) (B.isolationSchwartz x) else 0 := by
  classical
  let F (j : d → ℤ) (θ : UnitAddTorus d) := mFourier j θ *
    originalPhasePhysicalRecord B label N μ hν θ
      (combSchwartzModulation (torusDirectionalFrequency β j) g)
  change mFourierCoeff (fun θ => ∑ j ∈ J, r j * F j θ) k = _
  have hAdd : mFourierCoeff (fun θ => ∑ j ∈ J, r j * F j θ) k =
      ∑ j ∈ J, r j * mFourierCoeff (F j) k := by
    have hInt (j : d → ℤ) : Integrable (fun θ => mFourier (-k) θ * (r j * F j θ)) := by
      have hF : Continuous (F j) := (mFourier j).continuous.mul
        (continuous_originalPhasePhysicalRecord_apply B label N μ hν _)
      exact ((mFourier (-k)).continuous.mul (continuous_const.mul hF)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    simp only [mFourierCoeff, smul_eq_mul, Finset.mul_sum]
    rw [integral_finsetSum J (fun j _ => hInt j)]
    simp only [mul_left_comm (mFourier (-k) _) _, integral_const_mul]
  rw [hAdd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show mFourierCoeff (F j) k = _ from
    mFourierCoeff_originalPhasePhysicalRecord_modulated B label β hLabel N μ hν g j k]
  ring

/-- A common rectangular Schwartz seminorm bound for the physical
translations passes with the same constant to every original phase leaf. -/
theorem norm_originalPhasePhysicalRecord_le_of_translation_schwartzSeminorm_bound
    {d : Type*} [Fintype d] (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (β : d → ℝ)
    (hLabel : ∀ x : B.subtype, torusDirectionalFrequency β (label x) = (x : ℝ))
    (hIndep : ∀ k : d → ℤ, torusDirectionalFrequency β k = 0 → k = 0)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (weight order : ℕ) (C : ℝ)
    (hUniform : ∀ (t : ℝ) (f : SchwartzMap ℝ ℂ),
      ‖combDistributionTranslation (-t) μ f‖ ≤
        C * ((Finset.Iic (weight, order)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f)
    (θ : UnitAddTorus d) (f : SchwartzMap ℝ ℂ) :
    ‖originalPhasePhysicalRecord B label N μ hν θ f‖ ≤
      C * ((Finset.Iic (weight, order)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  obtain ⟨t, ht⟩ := exists_originalTranslation_seq_tendsto_originalPhasePhysicalRecord
    B label β hLabel hIndep N μ hν θ
  exact le_of_tendsto (ht f).norm (Eventually.of_forall fun j => hUniform (t j) f)

/-- The rectangular Schwartz bound passes from a uniform translation estimate
to all original phase leaves. -/
theorem originalPhasePhysicalRecord_hasSchwartzSeminormBound_of_translations
    {d : Type*} [Fintype d] (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (β : d → ℝ)
    (hLabel : ∀ x : B.subtype, torusDirectionalFrequency β (label x) = (x : ℝ))
    (hIndep : ∀ k : d → ℤ, torusDirectionalFrequency β k = 0 → k = 0)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (weight order : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hUniform : ∀ (t : ℝ) (f : SchwartzMap ℝ ℂ),
      ‖combDistributionTranslation (-t) μ f‖ ≤
        C * ((Finset.Iic (weight, order)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f)
    (θ : UnitAddTorus d) :
    HasSchwartzSeminormBound (originalPhasePhysicalRecord B label N μ hν θ) weight order :=
  ⟨C, hC, norm_originalPhasePhysicalRecord_le_of_translation_schwartzSeminorm_bound
    B label β hLabel hIndep N μ hν weight order C hUniform θ⟩

end
end MeyerGeneralProblem
