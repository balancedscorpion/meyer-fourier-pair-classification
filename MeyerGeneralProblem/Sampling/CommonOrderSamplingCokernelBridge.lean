module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-! The Schwartz conjugation lemmas used in the one-ray Fourier argument.
Extracted from the common-order sampling bridge at the pinned source commit. -/

@[expose] public section
open MeasureTheory
open scoped FourierTransform

noncomputable section

attribute [local instance] Classical.propDecidable

namespace MeyerGeneralProblem

/-- Complex conjugation of a Schwartz function, retained as a Schwartz map. -/
def complexConjugateSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap f

@[simp] theorem complexConjugateSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    complexConjugateSchwartz f x = starRingEnd ℂ (f x) := by
  simp [complexConjugateSchwartz]

theorem fourier_complexConjugateSchwartz (f : SchwartzMap ℝ ℂ) :
    FourierTransform.fourier (complexConjugateSchwartz f) =
      complexConjugateSchwartz (FourierTransform.fourierInv f) := by
  ext x
  rw [SchwartzMap.fourier_coe]
  simp only [complexConjugateSchwartz_apply, SchwartzMap.fourierInv_coe]
  rw [Real.fourier_eq, Real.fourierInv_eq, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [complexConjugateSchwartz_apply]
  change ((Real.fourierChar (-inner ℝ t x) : Circle) : ℂ) * starRingEnd ℂ (f t) =
    starRingEnd ℂ (((Real.fourierChar (inner ℝ t x) : Circle) : ℂ) * f t)
  rw [map_mul, Circle.starRingEnd_addChar]

end MeyerGeneralProblem
end
