module

public import MeyerGeneralProblem.Hermite.CutoffNorm
public import MeyerGeneralProblem.Sampling.ClassicalFourierSobolev
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# Actual all-order Schwartz multiplier product rules

The first and binomial product rules hold for arbitrary tempered distributions.
Only the multiplier is Schwartz; no classical derivative or L2 domain is assumed.
-/

namespace MeyerGeneralProblem.SchwartzDistributionLeibniz

noncomputable section

open scoped BigOperators

/-- The derivative of a Schwartz-multiplied arbitrary tempered distribution
obeys the actual product rule, by transposition on smooth Schwartz tests. -/
theorem deriv_smul (g : SchwartzMap ℝ ℂ) (T : TemperedDistribution ℝ ℂ) :
    TemperedDistribution.derivCLM ℂ (TemperedDistribution.smulLeftCLM ℂ g T) =
      TemperedDistribution.smulLeftCLM ℂ (SchwartzMap.derivCLM ℂ ℂ g) T +
        TemperedDistribution.smulLeftCLM ℂ g (TemperedDistribution.derivCLM ℂ T) := by
  ext φ
  simp [TemperedDistribution.derivCLM_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, schwartzDerivative_mul]

/-- The exact binomial product rule at every natural order; the top
distributional derivative requires no classical regularity. -/
theorem iterate_deriv_smul (n : ℕ) (g : SchwartzMap ℝ ℂ)
    (T : TemperedDistribution ℝ ℂ) :
    ((TemperedDistribution.derivCLM ℂ)^[n])
        (TemperedDistribution.smulLeftCLM ℂ g T) =
      ∑ i ∈ Finset.range (n + 1), n.choose i •
        TemperedDistribution.smulLeftCLM ℂ
          (((SchwartzMap.derivCLM ℂ ℂ)^[i]) g)
          (((TemperedDistribution.derivCLM ℂ)^[n-i]) T) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_choose_succ_nsmul
      (fun i j => TemperedDistribution.smulLeftCLM ℂ
        (((SchwartzMap.derivCLM ℂ ℂ)^[i]) g)
        (((TemperedDistribution.derivCLM ℂ)^[j]) T)) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul,
      deriv_smul, smul_add, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ n := by simpa using hi
    rw [show n + 1 - i = (n-i)+1 by omega, Function.iterate_succ_apply']

end
end MeyerGeneralProblem.SchwartzDistributionLeibniz
