module

public import MeyerGeneralProblem.Distribution.PoissonFlowFourierMultiplier
public import Mathlib.Analysis.Fourier.AddCircleMulti

@[expose] public section

/-!
# Poisson multipliers on the finite-dimensional phase torus

The flow with velocity `β` preserves the normalized Haar measure.
The real frequency of the monomial of index `n` is the dot product
of `n` and `β`. This gives the height multiplier in the same
Fourier coefficients as Mathlib's torus Hilbert basis.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive MeasureTheory ProbabilityTheory Set UnitAddTorus
open scoped ComplexConjugate NNReal

/-- Use normalized Haar measure on each circle factor of the phase torus. -/
local instance poissonFlowCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance poissonFlowCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance poissonFlowCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The phase advance `θ + βt` on the real torus. -/
def unitAddTorusFlow {d : Type*} (β : d → ℝ) (t : ℝ) (θ : UnitAddTorus d) :
    UnitAddTorus d :=
  fun i => θ i + ((β i * t : ℝ) : UnitAddCircle)

/-- The physical frequency of a torus monomial along the phase flow. -/
def torusDirectionalFrequency {d : Type*} [Fintype d] (β : d → ℝ) (n : d → ℤ) : ℝ :=
  ∑ i, (n i : ℝ) * β i

/-- The real flow is jointly continuous in time and phase. -/
theorem continuous_unitAddTorusFlow {d : Type*} (β : d → ℝ) :
    Continuous (Function.uncurry (unitAddTorusFlow β)) := by
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp continuous_snd).add
    ((AddCircle.continuous_mk' 1).comp (continuous_const.mul continuous_fst))

/-- The real phase advance preserves normalized Haar measure. -/
theorem measurePreserving_unitAddTorusFlow {d : Type*} [Fintype d]
    (β : d → ℝ) (t : ℝ) :
    MeasurePreserving (unitAddTorusFlow β t)
      (volume : Measure (UnitAddTorus d)) volume :=
  measurePreserving_add_right _ (fun i => ((β i * t : ℝ) : UnitAddCircle))

/-- A torus Fourier mode acquires the physical modulation character under the phase advance. -/
theorem mFourier_unitAddTorusFlow {d : Type*} [Fintype d]
    (β : d → ℝ) (n : d → ℤ) (t : ℝ) (θ : UnitAddTorus d) :
    mFourier n (unitAddTorusFlow β t θ) =
      combModulationCharacter (torusDirectionalFrequency β n) t * mFourier n θ := by
  have hProduct :
      (∏ i, fourier (n i) ((β i * t : ℝ) : UnitAddCircle)) =
        combModulationCharacter (torusDirectionalFrequency β n) t := by
    simp only [fourier_coe_apply, Complex.ofReal_one, div_one,
      combModulationCharacter_eq_exp, ← Complex.exp_sum, torusDirectionalFrequency]
    congr 1
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hPoint (i : d) :
      fourier (n i) ((unitAddTorusFlow β t θ) i) =
        fourier (n i) (θ i) * fourier (n i) ((β i * t : ℝ) : UnitAddCircle) := by
    simp only [unitAddTorusFlow, fourier_apply, zsmul_add,
      AddCircle.toCircle_add, Circle.coe_mul]
  simp only [mFourier, ContinuousMap.coe_mk, hPoint, Finset.prod_mul_distrib, hProduct]
  exact mul_comm _ _

/-- The actual support detector has the prescribed Fourier coefficient
at the sum of two heights on a Haar phase torus. -/
theorem mFourierCoeff_poisson_discreteSupportCount_add {d : Type*} [Fintype d]
    (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
    (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
    {s y : ℝ≥0} (hs : 0 < s) (hy : 0 < y) (n : d → ℤ) :
    mFourierCoeff (fun θ => Complex.ofReal (∫ x, cauchyPDFReal 0 (s + y) x
      ∂discreteSupportCount (T θ))) n =
      (Real.exp (-(2 * Real.pi * (s : ℝ)) * |torusDirectionalFrequency β n|) : ℂ) *
        mFourierCoeff (fun θ => Complex.ofReal (∫ x, cauchyPDFReal 0 y x
          ∂discreteSupportCount (T θ))) n := by
  have hNorm (θ : UnitAddTorus d) : ‖mFourier n θ‖ = 1 := by
    simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
      Circle.norm_coe, Finset.prod_const_one]
  simpa only [mFourierCoeff, mFourier_neg, smul_eq_mul, mul_comm (conj _)] using
    integral_poisson_discreteSupportCount_mul_conj_mode volume S T (unitAddTorusFlow β)
      (continuous_unitAddTorusFlow β).measurable (measurePreserving_unitAddTorusFlow β)
      hT hAdvance hCont hCount (mFourier n) (mFourier n).continuous.measurable hNorm
      (torusDirectionalFrequency β n) (mFourier_unitAddTorusFlow β n) hs hy

/-- For nonzero hull leaves the Haar mean of the Poisson field is a
single strictly positive real number at all positive heights. -/
theorem exists_pos_mean_poisson_discreteSupportCount {d : Type*} [Fintype d]
    (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
    (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
    (hNonzero : ∀ θ, T θ ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ y : ℝ≥0, 0 < y →
      (∫ θ, ∫ x, cauchyPDFReal 0 y x ∂discreteSupportCount (T θ)) = m := by
  let F (y : ℝ≥0) (θ : UnitAddTorus d) :=
    ∫ x, cauchyPDFReal 0 y x ∂discreteSupportCount (T θ)
  have hCoeff (y : ℝ≥0) :
      mFourierCoeff (fun θ => Complex.ofReal (F y θ)) 0 = Complex.ofReal (∫ θ, F y θ) := by
    simp only [mFourierCoeff, neg_zero, mFourier_zero, ContinuousMap.one_apply, one_smul,
      integral_complex_ofReal]
  have hAdd {s y : ℝ≥0} (hs : 0 < s) (hy : 0 < y) :
      (∫ θ, F (s + y) θ) = ∫ θ, F y θ := by
    have h := mFourierCoeff_poisson_discreteSupportCount_add β S T hT hAdvance hCont hCount hs hy 0
    change mFourierCoeff (fun θ => Complex.ofReal (F (s + y) θ)) 0 =
      _ * mFourierCoeff (fun θ => Complex.ofReal (F y θ)) 0 at h
    rw [hCoeff, hCoeff] at h
    have h₀ : torusDirectionalFrequency β 0 = 0 := by simp [torusDirectionalFrequency]
    exact Complex.ofReal_injective (by simpa only [h₀, abs_zero, mul_zero, Real.exp_zero,
      Complex.ofReal_one, one_mul] using h)
  have hOne : 0 < (1 : ℝ≥0) := one_pos
  obtain ⟨C, hC, hBound⟩ := exists_lintegral_poisson_bound_of_discreteSupportCount K hOne
  have hPos (θ : UnitAddTorus d) : 0 < F 1 θ := by
    change 0 < ∫ x, cauchyPDFReal 0 1 x ∂discreteSupportCount (T θ)
    rw [integral_poisson_discreteSupportCount_eq _ _ hOne]
    exact ENNReal.toReal_pos
      (lintegral_poisson_discreteSupportCount_pos (S θ) (T θ) (hT θ) (hNonzero θ) 0 hOne).ne'
      ((hBound (S θ) (T θ) (hT θ) (hCount θ) 0).trans_lt hC).ne
  have hInt : Integrable (F 1) :=
    (memLp_poisson_discreteSupportCount S T hT hCont hCount volume 0 hOne).integrable
      (by simp)
  refine ⟨∫ θ, F 1 θ, ?_, ?_⟩
  · apply (integral_pos_iff_support_of_nonneg (fun θ => (hPos θ).le) hInt).mpr
    have hFull : Function.support (F 1) = univ :=
      eq_univ_of_forall fun θ => (hPos θ).ne'
    simp [hFull]
  · intro y hy
    change (∫ θ, F y θ) = ∫ θ, F 1 θ
    rcases lt_trichotomy y 1 with hY | rfl | hY
    · have h := hAdd (tsub_pos_of_lt hY) hy
      rw [tsub_add_cancel_of_le hY.le] at h
      exact h.symm
    · rfl
    · have h := hAdd (tsub_pos_of_lt hY) hOne
      rwa [tsub_add_cancel_of_le hY.le] at h

end
end MeyerGeneralProblem
