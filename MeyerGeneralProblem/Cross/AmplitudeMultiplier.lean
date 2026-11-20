module

public import MeyerGeneralProblem.Cross.SymbolBounds
public import MeyerGeneralProblem.Sampling.PeriodThreeExtension

@[expose] public section

/-!
# Uniform multiplier bound for the normalized cross-block amplitude

This module consumes the fixed period-three extension theorem and the uniform
mixed-derivative estimate for `normalizedCrossBlockAmplitude`.  The result is
an assumption-free finite-matrix multiplier bound with one constant uniform in
the Hermite order, scale ratio, finite index types, and physical block points.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped Matrix.Norms.L2Operator

/-- The normalized cross-block amplitude is a uniformly bounded multiplier of
every finite matrix.  The constant is independent of the Hermite order, scale
ratio, finite carriers, and points in the physical logarithmic block. -/
theorem exists_uniform_normalizedCrossBlockAmplitude_l2MultiplierBound :
    ∃ C : NNReal,
      ∀ { ι κ : Type* }
        [Fintype ι] [Fintype κ]
        [DecidableEq ι] [DecidableEq κ],
      ∀ (m : ℕ), 1 ≤ m →
      ∀ {R : ℝ}, 1 ≤ R →
      ∀ (u : ι → ℝ) (v : κ → ℝ),
        (∀ i, u i ∈ Icc (0 : ℝ) 1) →
        (∀ j, v j ∈ Icc (0 : ℝ) 1) →
      ∀ A : Matrix ι κ ℂ,
        ‖amplitudeWeightedMatrix
            (fun i j => normalizedCrossBlockAmplitude m R (u i) (v j)) A‖ ≤
          (C : ℝ) * ‖A‖ := by
  obtain ⟨C₀, hC₀⟩ :=
    exists_uniform_normalizedCrossBlockAmplitude_mixedDeriv_bound
  refine ⟨periodThreeC4FourierL1Constant * C₀, ?_⟩
  intro ι κ _ _ _ _ m hm R hR u v hu hv A
  obtain ⟨F, hagree, _hnorm, hcoeff, hl1⟩ :=
    exists_periodThreeTorusExtension_with_mFourierCoeff_l1_bound
      (normalizedCrossBlockAmplitude m R)
      (normalizedCrossBlockAmplitude_contDiff m hm hR) C₀ (by
        intro a b hab x y hx hy
        simpa only [mixedIteratedDeriv] using
          hC₀ m hm hR a b hab hx hy)
  have hmatrix :=
    norm_periodThreeAmplitudeWeightedMatrix_le_of_summable_mFourierCoeff
      A F u v hcoeff
  have heq : amplitudeWeightedMatrix
      (fun i j => normalizedCrossBlockAmplitude m R (u i) (v j)) A =
      amplitudeWeightedMatrix
        (fun i j => F (unitAddTorusPair (periodThreeTorusPoint (u i))
          (periodThreeTorusPoint (v j)))) A := by
    ext i j
    simp only [amplitudeWeightedMatrix_apply]
    rw [hagree (hu i) (hv j)]
  rw [heq]
  calc
    ‖amplitudeWeightedMatrix
        (fun i j => F (unitAddTorusPair (periodThreeTorusPoint (u i))
          (periodThreeTorusPoint (v j)))) A‖ ≤
        (∑' n, ‖UnitAddTorus.mFourierCoeff F n‖) * ‖A‖ := hmatrix
    _ ≤ ((periodThreeC4FourierL1Constant : ℝ) * (C₀ : ℝ)) * ‖A‖ :=
      mul_le_mul_of_nonneg_right hl1 (norm_nonneg A)
    _ = ((periodThreeC4FourierL1Constant * C₀ : NNReal) : ℝ) * ‖A‖ := by
      norm_num

end

end MeyerGeneralProblem
