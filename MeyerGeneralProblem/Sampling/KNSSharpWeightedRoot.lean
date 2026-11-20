module

public import MeyerGeneralProblem.Sampling.KNSWeightedPrincipalRoot
public import MeyerGeneralProblem.Sampling.KNSSharpQuadraticEntire

@[expose] public section

/-!
# Sharp norm and boundary-ray bounds for the actual weighted principal root

The imaginary-direction Gaussian coefficient is preserved exactly. The
opposite-side rate is independent of the weight rate. These bounds and their
linear-type consequence do not supply a Phragmen-Lindelof sector estimate.
-/

namespace MeyerGeneralProblem

noncomputable section

private theorem kns_principalRoot_im_sq (w : ℂ) :
    (Complex.sqrt w).im ^ 2 = (‖w‖ - w.re) / 2 := by
  have h := Complex.abs_cpow_inv_two_im w
  change |(Complex.sqrt w).im| = Real.sqrt ((‖w‖ - w.re) / 2) at h
  have hs := congrArg (fun x : ℝ => x ^ 2) h
  rw [sq_abs, Real.sq_sqrt (by linarith [Complex.re_le_norm w])] at hs
  exact hs

/-- An actual sharp imaginary-direction bound gives the exact global
weighted-root norm bound, including zero and the branch cut. No analytic
extension across the cut or equality of the two rates is inferred. -/
theorem norm_knsWeightedPrincipalRoot_le_sharp
    {sgn κ ε η A : ℝ} {E : ℂ → ℂ}
    (hsgn : sgn = 1 ∨ sgn = -1) (hη : 0 < η)
    (hsharp : ∀ z : ℂ, ‖E z‖ ≤ A * Real.exp ((Real.pi / (2*η))*z.im^2))
    (w : ℂ) :
    ‖knsWeightedPrincipalRoot sgn κ ε E w‖ ≤
      A * Real.exp ((Real.pi / (4*η))*‖w‖ +
        (2*Real.pi*κ-ε-Real.pi/(4*η))*w.re) := by
  have him : (((sgn : ℂ)*Complex.sqrt w).im)^2 = (‖w‖-w.re)/2 := by
    rcases hsgn with rfl | rfl <;>
      simpa using kns_principalRoot_im_sq w
  simp only [knsWeightedPrincipalRoot, norm_mul, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    _ ≤ Real.exp ((2*Real.pi*κ-ε)*w.re) *
        (A * Real.exp ((Real.pi/(2*η))*(((sgn : ℂ)*Complex.sqrt w).im)^2)) :=
      mul_le_mul_of_nonneg_left (hsharp _) (Real.exp_pos _).le
    _ = A * Real.exp ((Real.pi/(4*η))*‖w‖ +
        (2*Real.pi*κ-ε-Real.pi/(4*η))*w.re) := by
      rw [him, mul_left_comm, ← Real.exp_add]
      congr 1
      congr 1
      field_simp
      ring

/-- The exact sharp bound on every polar ray with nonnegative radius.
It is a pointwise angular formula, not a sector Phragmen-Lindelof conclusion. -/
theorem norm_knsWeightedPrincipalRoot_ray_le_sharp
    {sgn κ ε η A : ℝ} {E : ℂ → ℂ}
    (hsgn : sgn = 1 ∨ sgn = -1) (hη : 0 < η)
    (hsharp : ∀ z : ℂ, ‖E z‖ ≤ A * Real.exp ((Real.pi / (2*η))*z.im^2))
    {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖knsWeightedPrincipalRoot sgn κ ε E
      ((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))‖ ≤
      A * Real.exp (r * ((2*Real.pi*κ-ε)*Real.cos θ +
        (Real.pi/(4*η))*(1-Real.cos θ))) := by
  have h := norm_knsWeightedPrincipalRoot_le_sharp (κ := κ) (ε := ε) hsgn hη hsharp
    ((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))
  have hre : ((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)).re = r*Real.cos θ := by
    simp [Complex.exp_re]
  have hn : ‖(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)‖ = r := by
    rw [norm_mul, Complex.norm_exp]
    simp [abs_of_nonneg hr]
  rw [hre, hn] at h
  have hexp : (Real.pi/(4*η))*r +
      (2*Real.pi*κ-ε-Real.pi/(4*η))*(r*Real.cos θ) =
      r*((2*Real.pi*κ-ε)*Real.cos θ+(Real.pi/(4*η))*(1-Real.cos θ)) := by
    ring
  rwa [hexp] at h

/-- On rays with nonnegative cosine, nonnegative epsilon can be discarded
from the upper exponent. The displayed boundary coefficient is independent
of epsilon; it still must be compared with the desired sector coefficient. -/
theorem norm_knsWeightedPrincipalRoot_ray_le_sharp_uniform
    {sgn κ ε η A : ℝ} {E : ℂ → ℂ}
    (hsgn : sgn = 1 ∨ sgn = -1) (hη : 0 < η) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hsharp : ∀ z : ℂ, ‖E z‖ ≤ A * Real.exp ((Real.pi / (2*η))*z.im^2))
    {r θ : ℝ} (hr : 0 ≤ r) (hcos : 0 ≤ Real.cos θ) :
    ‖knsWeightedPrincipalRoot sgn κ ε E
      ((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))‖ ≤
      A * Real.exp (Real.pi*r*(2*κ*Real.cos θ +
        (1-Real.cos θ)/(4*η))) := by
  apply (norm_knsWeightedPrincipalRoot_ray_le_sharp hsgn hη hsharp hr θ).trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply Real.exp_le_exp.mpr
  have heq : Real.pi*r*(2*κ*Real.cos θ+(1-Real.cos θ)/(4*η)) =
      r*((2*Real.pi*κ)*Real.cos θ+(Real.pi/(4*η))*(1-Real.cos θ)) := by
    ring
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ hr
  have hp : 0 ≤ ε * Real.cos θ := mul_nonneg hε hcos
  nlinarith

/-- The sharp bound also provides a genuine global linear exponential
majorant with its displayed coefficient. No BigO or sector-growth certificate
is an input. -/
theorem norm_knsWeightedPrincipalRoot_le_sharp_linear
    {sgn κ ε η A : ℝ} {E : ℂ → ℂ}
    (hsgn : sgn = 1 ∨ sgn = -1) (hη : 0 < η) (hA : 0 ≤ A)
    (hsharp : ∀ z : ℂ, ‖E z‖ ≤ A * Real.exp ((Real.pi / (2*η))*z.im^2))
    (w : ℂ) :
    ‖knsWeightedPrincipalRoot sgn κ ε E w‖ ≤
      A * Real.exp ((Real.pi/(4*η) +
        |2*Real.pi*κ-ε-Real.pi/(4*η)|)*‖w‖) := by
  apply (norm_knsWeightedPrincipalRoot_le_sharp hsgn hη hsharp w).trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply Real.exp_le_exp.mpr
  have hterm :
      (2*Real.pi*κ-ε-Real.pi/(4*η))*w.re ≤
        |2*Real.pi*κ-ε-Real.pi/(4*η)| * ‖w‖ := by
    calc
      _ ≤ |(2*Real.pi*κ-ε-Real.pi/(4*η))*w.re| := le_abs_self _
      _ = |2*Real.pi*κ-ε-Real.pi/(4*η)| * |w.re| := abs_mul _ _
      _ ≤ |2*Real.pi*κ-ε-Real.pi/(4*η)| * ‖w‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm w) (abs_nonneg _)
  nlinarith

end

end MeyerGeneralProblem
