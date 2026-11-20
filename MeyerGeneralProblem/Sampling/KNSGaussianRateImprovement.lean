module

public import MeyerGeneralProblem.Sampling.KNSWeightedPrincipalRoot

@[expose] public section

/-!
# A global Gaussian rate from the actual weighted-root decay

Choose the positive damping parameter before applying the decay theorem.
The exact real restriction removes the weight using only positive
exponentials. The existing weaker Gaussian bound covers the finite prefix,
so no continuity or compactness premise is needed. The resulting rate has
no free epsilon, no optimal-attainment premise and no nonzero-function premise.
-/

namespace MeyerGeneralProblem

/-- A fixed positive damping and an actual eventual weighted-root estimate
give a stronger global selected-ray Gaussian rate. The explicit witness is
`max 1 (max D (C₀ * exp (δ * X₀)))`. The restrictions on the original rate,
tail constant and threshold are retained for the intended application;
the algebra does not need those three restrictions. The sign is arbitrary. -/
theorem exists_globalGaussian_improvement_of_weightedRoot_decay
    {E : ℂ → ℂ} {sgn κ δ C₀ D X₀ : ℝ}
    (_hκ : 0 < κ) (hδ : 0 < δ) (hC₀ : 0 ≤ C₀) (_hD : 0 ≤ D) (_hX₀ : 0 < X₀)
    (hbase : ∀ t : ℝ, 0 ≤ t →
      ‖E (((sgn * t : ℝ) : ℂ))‖ ≤ C₀ * Real.exp (-2 * Real.pi * κ * t^2))
    (htail : ∀ x : ℝ, X₀ ≤ x →
      ‖knsWeightedPrincipalRoot sgn κ δ E (x : ℂ)‖ ≤
        D * Real.exp (-2 * δ * x)) :
    ∃ C₁ > 0, ∀ t : ℝ, 0 ≤ t →
      ‖E (((sgn * t : ℝ) : ℂ))‖ ≤
        C₁ * Real.exp (-2 * Real.pi * (κ + δ / (2 * Real.pi)) * t^2) := by
  let C₁ := max 1 (max D (C₀ * Real.exp (δ * X₀)))
  have hDC : D ≤ C₁ := (le_max_left _ _).trans (le_max_right _ _)
  have hBC : C₀ * Real.exp (δ * X₀) ≤ C₁ :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C₁, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht
  have hrate : -2 * Real.pi * (κ + δ / (2 * Real.pi)) * t^2 =
      -(2 * Real.pi * κ + δ) * t^2 := by
    field_simp
  rw [hrate]
  by_cases hXt : X₀ ≤ t^2
  · have h := htail (t^2) hXt
    rw [knsWeightedPrincipalRoot_of_nonneg sgn κ δ E ht,
      norm_mul, Complex.norm_exp_ofReal] at h
    calc
      ‖E (((sgn * t : ℝ) : ℂ))‖ =
          Real.exp (-((2 * Real.pi * κ - δ) * t^2)) *
            (Real.exp ((2 * Real.pi * κ - δ) * t^2) *
              ‖E (((sgn * t : ℝ) : ℂ))‖) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp (-((2 * Real.pi * κ - δ) * t^2)) *
          (D * Real.exp (-2 * δ * t^2)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = D * Real.exp (-(2 * Real.pi * κ + δ) * t^2) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 1
        congr 1
        ring
      _ ≤ C₁ * Real.exp (-(2 * Real.pi * κ + δ) * t^2) :=
        mul_le_mul_of_nonneg_right hDC (Real.exp_pos _).le
  · have hδt : δ * t^2 ≤ δ * X₀ :=
      mul_le_mul_of_nonneg_left (le_of_not_ge hXt) hδ.le
    calc
      ‖E (((sgn * t : ℝ) : ℂ))‖ ≤
          C₀ * Real.exp (-2 * Real.pi * κ * t^2) := hbase t ht
      _ = (C₀ * Real.exp (δ * t^2)) *
          Real.exp (-(2 * Real.pi * κ + δ) * t^2) := by
        rw [mul_assoc C₀ (Real.exp (δ * t^2)) (Real.exp (-(2 * Real.pi * κ + δ) * t^2)),
          ← Real.exp_add]
        congr 1
        congr 1
        ring
      _ ≤ (C₀ * Real.exp (δ * X₀)) *
          Real.exp (-(2 * Real.pi * κ + δ) * t^2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hδt) hC₀)
          (Real.exp_pos _).le
      _ ≤ C₁ * Real.exp (-(2 * Real.pi * κ + δ) * t^2) :=
        mul_le_mul_of_nonneg_right hBC (Real.exp_pos _).le

end MeyerGeneralProblem
