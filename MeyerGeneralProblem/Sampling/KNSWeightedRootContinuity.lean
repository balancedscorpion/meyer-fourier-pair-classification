module

public import MeyerGeneralProblem.Sampling.KNSWeightedPrincipalRoot
public import Mathlib.Analysis.Calculus.DiffContOnCl

@[expose] public section

/-!
# Closed-right-half-plane continuity of the actual weighted root

The principal root is continuous at every point with nonnegative real part,
including zero and the imaginary axis. Thus the actual weighted composition
has the closure continuity required alongside its open-half-plane complex
differentiability. No analyticity at zero, continuity across the negative-real
cut, global continuity, or sector-growth estimate is asserted.
-/

namespace MeyerGeneralProblem

/-- The actual weighted principal-root composition is continuous at every
point of the closed right half-plane when its input function is continuous.
All three real parameters are unrestricted. -/
theorem continuousAt_knsWeightedPrincipalRoot (sgn κ ε : ℝ) {E : ℂ → ℂ}
    (hE : Continuous E) {w : ℂ} (hw : 0 ≤ w.re) :
    ContinuousAt (knsWeightedPrincipalRoot sgn κ ε E) w := by
  have hroot : ContinuousAt (fun z : ℂ => (sgn : ℂ) * Complex.sqrt z) w :=
    continuousAt_const.mul (Complex.continuousAt_sqrt (Or.inl hw))
  have hweight : ContinuousAt
      (fun z : ℂ => Complex.exp (((2 * Real.pi * κ - ε : ℝ) : ℂ) * z)) w := by
    fun_prop
  exact hweight.mul (hE.continuousAt.comp hroot)

/-- The actual weighted composition is continuous on the whole closed right
half-plane, without any sign or positivity restriction on its parameters. -/
theorem continuousOn_knsWeightedPrincipalRoot_closedRightHalfPlane
    (sgn κ ε : ℝ) {E : ℂ → ℂ} (hE : Continuous E) :
    ContinuousOn (knsWeightedPrincipalRoot sgn κ ε E) {w : ℂ | 0 ≤ w.re} :=
  fun _ hw => (continuousAt_knsWeightedPrincipalRoot sgn κ ε hE hw).continuousWithinAt

/-- An entire input gives complex differentiability on the open right
half-plane and continuity on its closure. The entire-input hypothesis remains
explicit; this statement does not assert differentiability on the boundary. -/
theorem diffContOnCl_knsWeightedPrincipalRoot (sgn κ ε : ℝ) {E : ℂ → ℂ}
    (hE : Differentiable ℂ E) :
    DiffContOnCl ℂ (knsWeightedPrincipalRoot sgn κ ε E) {w : ℂ | 0 < w.re} := by
  refine ⟨(analyticOnNhd_knsWeightedPrincipalRoot sgn κ ε hE).differentiableOn, ?_⟩
  apply (continuousOn_knsWeightedPrincipalRoot_closedRightHalfPlane
    sgn κ ε hE.continuous).mono
  exact closure_minimal (fun w (hw : 0 < w.re) => show 0 ≤ w.re from hw.le)
    (isClosed_le continuous_const Complex.continuous_re)

end MeyerGeneralProblem
