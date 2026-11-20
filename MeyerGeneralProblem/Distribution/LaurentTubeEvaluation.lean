module

public import MeyerGeneralProblem.Distribution.RealRootedLaurentSlices
public import MeyerGeneralProblem.Cardinal.Strong.DampedTubeJump

@[expose] public section

/-!
# Exact quotient evaluation by an absolutely convergent Laurent array

The finite denominator can act termwise on the full original array
at every point of absolute convergence. Frequencies are translated
inside the absolutely convergent sums, keeping all collisions.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- Multiplying an actual Laurent series by the finite entire denominator
recovers the entire numerator at every point of absolute convergence. -/
theorem complexExponentialSum_mul_tsum_of_arrayRecurrence
    (L : G →+ ℝ) (p R : AddMonoidAlgebra ℂ G) (u : G → ℂ) (z : ℂ)
    (hrec : ∀ n, annihilatorArrayConvolution p.coeff u n = R.coeff n)
    (hs : Summable (fun n => u n * complexExponentialCharacter L z (.ofAdd n))) :
    complexExponentialSum L p.coeff z *
      (∑' n, u n * complexExponentialCharacter L z (.ofAdd n)) =
      complexExponentialSum L R.coeff z := by
  classical
  let χ (n : G) := complexExponentialCharacter L z (.ofAdd n)
  let F (n : G) := u n * χ n
  have hχ (m n : G) : χ m * χ (n - m) = χ n := by
    change complexExponentialCharacter L z (.ofAdd m) *
      complexExponentialCharacter L z (.ofAdd (n - m)) = _
    rw [← map_mul]
    change χ (m + (n - m)) = _
    rw [add_comm, sub_add_cancel]
  have hterm (m n : G) :
      p.coeff m * χ m * F (n - m) = (p.coeff m * u (n - m)) * χ n := by
    calc
      _ = (p.coeff m * u (n - m)) * (χ m * χ (n - m)) := by dsimp [F]; ac_rfl
      _ = _ := by rw [hχ]
  have hShift (m : G) : Summable (fun n => (p.coeff m * u (n - m)) * χ n) := by
    rw [show (fun n => (p.coeff m * u (n - m)) * χ n) =
      fun n => (p.coeff m * χ m) * (F ∘ Equiv.subRight m) n from funext (fun n => (hterm m n).symm)]
    exact ((Equiv.subRight m).summable_iff.mpr hs).mul_left _
  have hz (q : AddMonoidAlgebra ℂ G) : complexExponentialSum L q.coeff z =
      ∑ n ∈ q.coeff.support, q.coeff n * χ n := rfl
  rw [hz p, hz R, Finset.sum_mul]
  calc
    _ = ∑ m ∈ p.coeff.support, ∑' n, (p.coeff m * u (n - m)) * χ n := by
      apply Finset.sum_congr rfl
      intro m hm
      change p.coeff m * χ m * (∑' n, F n) = _
      rw [← (Equiv.subRight m).tsum_eq (f := F), ← tsum_mul_left]
      exact tsum_congr (hterm m)
    _ = ∑' n, ∑ m ∈ p.coeff.support, (p.coeff m * u (n - m)) * χ n :=
      (Summable.tsum_finsetSum (fun m _ => hShift m)).symm
    _ = ∑' n, R.coeff n * χ n := by
      apply tsum_congr
      intro n
      rw [← Finset.sum_mul]
      exact congrArg (fun w : ℂ => w * χ n) (hrec n)
    _ = _ := tsum_eq_sum fun n hn => by rw [Finsupp.notMem_support_iff.mp hn, zero_mul]

/-- The real Fourier modulation has the same phase convention as the tube. -/
theorem unitPhase_mul_eq_combModulationCharacter (a x : ℝ) :
    StrongParity.unitPhase (a * x) = combModulationCharacter a x := by
  rw [combModulationCharacter_eq_exp]
  unfold StrongParity.unitPhase
  congr 1
  push_cast
  ring

/-- The entire character at a horizontal point and a signed height. -/
theorem complexExponentialCharacter_vertical (L : G →+ ℝ) (n : G) (x t : ℝ) :
    complexExponentialCharacter L ((x : ℂ) + (t : ℂ) * Complex.I) (.ofAdd n) =
      (Real.exp (-2 * Real.pi * L n * t) : ℂ) * combModulationCharacter (L n) x := by
  rw [← unitPhase_mul_eq_combModulationCharacter, ← StrongParity.complexUnitPhase_horizontal_vertical]
  change Complex.exp (2 * Real.pi * Complex.I * (L n : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I)) = _
  unfold StrongParity.complexUnitPhase
  congr 1
  push_cast
  ring

end

end MeyerGeneralProblem
