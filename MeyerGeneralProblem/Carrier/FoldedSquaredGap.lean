module

public import MeyerGeneralProblem.Carrier.SignedSquare

@[expose] public section

/-!
# Squared-coordinate gaps from larger-endpoint weighted gaps

On a same-sign adjacent pair, the signed-square increment is the ordinary
gap times the sum of endpoint magnitudes. Bounding that sum by twice its
maximum gives the exact factor two used by the folded-tail construction.
No asymptotic rate, zero set or analytic hypothesis enters this lemma.
-/

namespace MeyerGeneralProblem

/-- An actual same-sign larger-endpoint weighted-gap bound gives the
signed-square gap bound with factor two. The sign condition is explicit;
no reflection symmetry or positivity assumption on the given bound is used. -/
theorem signedSquare_sub_le_twice_of_weightedGap {x y ρ : ℝ}
    (hxy : x ≤ y) (hsign : y ≤ 0 ∨ 0 ≤ x)
    (hgap : max |x| |y| * (y-x) ≤ ρ) :
    signedSquare y - signedSquare x ≤ 2*ρ := by
  rw [signedSquare_sub_eq_gap_mul_abs_add hxy hsign]
  have hsum : |x|+|y| ≤ 2*max |x| |y| := by
    linarith [le_max_left |x| |y|, le_max_right |x| |y|]
  calc
    (y-x)*(|x|+|y|) ≤ (y-x)*(2*max |x| |y|) :=
      mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hxy)
    _ = 2*(max |x| |y| * (y-x)) := by ring
    _ ≤ 2*ρ := mul_le_mul_of_nonneg_left hgap (by norm_num)

end MeyerGeneralProblem
