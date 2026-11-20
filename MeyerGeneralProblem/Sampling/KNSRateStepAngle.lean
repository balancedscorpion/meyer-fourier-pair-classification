module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Tactic

@[expose] public section

/-!
# An explicit angle for a common Gaussian-rate step

For a positive real rate kappa, the half-angle parameter
`2*kappa/(1+2*kappa)` lies strictly between zero and one. The resulting
angle lies in the open first quadrant and satisfies the exact normalized
boundary-coefficient identity and a quantitative sine lower bound.
This is a numerical helper only: no Gaussian-rate, sector-growth,
supremum, iteration or uniqueness conclusion is asserted.
-/

namespace MeyerGeneralProblem

/-- The explicit doubled-arctangent angle associated with a real rate. -/
noncomputable def knsRateStepAngle (κ : ℝ) : ℝ :=
  2*Real.arctan (2*κ/(1+2*κ))

private theorem sin_two_arctan (t : ℝ) :
    Real.sin (2*Real.arctan t) = 2*t/(1+t^2) := by
  have ht := Real.tan_arctan t
  rw [Real.tan_eq_sin_div_cos] at ht
  have hs : Real.sin (Real.arctan t) = t*Real.cos (Real.arctan t) :=
    (div_eq_iff (Real.cos_arctan_pos t).ne').mp ht
  rw [Real.sin_two_mul, hs]
  calc
    _ = 2*t*(Real.cos (Real.arctan t)^2) := by ring
    _ = _ := by rw [Real.cos_sq_arctan]; ring

private theorem cos_two_arctan (t : ℝ) :
    Real.cos (2*Real.arctan t) = (1-t^2)/(1+t^2) := by
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  have hd : 1+t^2 ≠ 0 := ne_of_gt (by positivity : 0 < 1+t^2)
  field_simp
  ring

/-- A positive rate gives a genuine open-first-quadrant angle, exact
normalized boundary coefficient, and an explicit positive sine lower bound.
The positive-rate hypothesis excludes the zero-angle endpoint. -/
theorem knsRateStepAngle_properties {κ : ℝ} (hκ : 0 < κ) :
    0 < knsRateStepAngle κ ∧ knsRateStepAngle κ < Real.pi/2 ∧
      2*κ*Real.cos (knsRateStepAngle κ)+
          (1-Real.cos (knsRateStepAngle κ))/(4*κ) = Real.sin (knsRateStepAngle κ) ∧
      2*κ/(1+2*κ) ≤ Real.sin (knsRateStepAngle κ) := by
  let t : ℝ := 2*κ/(1+2*κ)
  have hdκ : 0 < 1+2*κ := by positivity
  have ht0 : 0 < t := by dsimp only [t]; positivity
  have ht1 : t < 1 := by
    dsimp only [t]
    apply (div_lt_one hdκ).mpr
    linarith
  have hat0 : 0 < Real.arctan t := Real.arctan_pos.mpr ht0
  have hat1 : Real.arctan t < Real.pi/4 := by
    simpa only [Real.arctan_one] using Real.arctan_strictMono ht1
  change 0 < 2*Real.arctan t ∧ 2*Real.arctan t < Real.pi/2 ∧
    2*κ*Real.cos (2*Real.arctan t)+(1-Real.cos (2*Real.arctan t))/(4*κ) =
      Real.sin (2*Real.arctan t) ∧ t ≤ Real.sin (2*Real.arctan t)
  refine ⟨by positivity, by linarith, ?_, ?_⟩
  · rw [cos_two_arctan, sin_two_arctan]
    dsimp only [t]
    field_simp
    ring
  · rw [sin_two_arctan]
    apply (le_div_iff₀ (by positivity : 0 < 1+t^2)).mpr
    have htSq : t^2 ≤ 1 := by nlinarith [mul_self_le_mul_self ht0.le ht1.le]
    calc
      t*(1+t^2) ≤ t*(1+1) :=
        mul_le_mul_of_nonneg_left (add_le_add_right htSq 1) ht0.le
      _ = 2*t := by ring

end MeyerGeneralProblem
