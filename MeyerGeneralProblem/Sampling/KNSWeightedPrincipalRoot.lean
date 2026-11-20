module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The actual exponentially weighted principal-root composition

The two physical branches are represented by an explicit real sign multiplying
the principal square root. The composition is analytic on the open right
half-plane, has exact real and zero-tail restrictions, and converts a quadratic
norm bound to a linear one. These statements do not assert analyticity at the
origin, sector growth, an optimal Gaussian rate, or a uniqueness consequence.
-/

noncomputable section

namespace MeyerGeneralProblem

/-- The actual weighted principal-root composition, with the physical sign
outside the square root and the normalized real coefficient `2*pi*kappa-epsilon`. -/
def knsWeightedPrincipalRoot (sgn κ ε : ℝ) (E : ℂ → ℂ) (w : ℂ) : ℂ :=
  Complex.exp (((2 * Real.pi * κ - ε : ℝ) : ℂ) * w) *
    E ((sgn : ℂ) * Complex.sqrt w)

/-- The weighted composition of an entire function with either scaled
principal-root branch is analytic on the open right half-plane. No sign or
positivity restrictions on the three real parameters are needed here. -/
theorem analyticOnNhd_knsWeightedPrincipalRoot (sgn κ ε : ℝ) {E : ℂ → ℂ}
    (hE : Differentiable ℂ E) :
    AnalyticOnNhd ℂ (knsWeightedPrincipalRoot sgn κ ε E) {w : ℂ | 0 < w.re} := by
  have hsqrt : AnalyticOnNhd ℂ Complex.sqrt {w : ℂ | 0 < w.re} :=
    (Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane).mono
      (fun _ hw => Or.inl hw)
  intro w hw
  have hinner : AnalyticAt ℂ (fun z : ℂ => (sgn : ℂ) * Complex.sqrt z) w :=
    analyticAt_const.mul (hsqrt w hw)
  have hweight : AnalyticAt ℂ
      (fun z : ℂ => Complex.exp (((2 * Real.pi * κ - ε : ℝ) : ℂ) * z)) w := by
    fun_prop
  exact hweight.mul ((hE.analyticAt _).comp hinner)

/-- Evaluation at a nonnegative physical square recovers the signed physical
argument exactly, including physical zero. This is not an analyticity assertion
at zero. -/
theorem knsWeightedPrincipalRoot_of_nonneg (sgn κ ε : ℝ) (E : ℂ → ℂ)
    {t : ℝ} (ht : 0 ≤ t) :
    knsWeightedPrincipalRoot sgn κ ε E ((t ^ 2 : ℝ) : ℂ) =
      Complex.exp ((((2 * Real.pi * κ - ε) * t ^ 2 : ℝ) : ℂ)) *
        E (((sgn * t : ℝ) : ℂ)) := by
  have hsqrt : Complex.sqrt ((t ^ 2 : ℝ) : ℂ) = (t : ℂ) := by
    rw [Complex.sqrt_of_nonneg (Complex.zero_le_real.mpr (sq_nonneg t)),
      Complex.ofReal_re, Real.sqrt_sq ht]
  simp only [knsWeightedPrincipalRoot, hsqrt, ← Complex.ofReal_mul]

/-- An actual one-sided Gaussian bound on the selected physical branch gives
the exact real-axis exponential bound after weighting. The algebra holds for
arbitrary real parameters; positive epsilon makes this a decaying bound. -/
theorem norm_knsWeightedPrincipalRoot_real_le (sgn κ ε : ℝ)
    {E : ℂ → ℂ} {Creal : ℝ}
    (hreal : ∀ t : ℝ, 0 ≤ t →
      ‖E (((sgn * t : ℝ) : ℂ))‖ ≤ Creal * Real.exp (-2 * Real.pi * κ * t ^ 2))
    {x : ℝ} (hx : 0 ≤ x) :
    ‖knsWeightedPrincipalRoot sgn κ ε E (x : ℂ)‖ ≤
      Creal * Real.exp (-ε * x) := by
  have hrestriction := knsWeightedPrincipalRoot_of_nonneg sgn κ ε E (Real.sqrt_nonneg x)
  rw [Real.sq_sqrt hx] at hrestriction
  rw [hrestriction, norm_mul, Complex.norm_exp, Complex.ofReal_re]
  calc
    _ ≤ Real.exp ((2 * Real.pi * κ - ε) * x) *
        (Creal * Real.exp (-2 * Real.pi * κ * (Real.sqrt x) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hreal (Real.sqrt x) (Real.sqrt_nonneg x))
        (Real.exp_pos _).le
    _ = Creal * Real.exp (-ε * x) := by
      rw [Real.sq_sqrt hx, mul_left_comm, ← Real.exp_add]
      congr 1
      congr 1
      ring

/-- Actual zeros at nonnegative physical nodes transfer to their squared
coordinates on the selected branch. No zero-set, gap, or parity certificate is
substituted for the displayed point evaluations. -/
theorem knsWeightedPrincipalRoot_zero_tail (sgn κ ε : ℝ) (E : ℂ → ℂ)
    (z : ℕ → ℝ) (N : ℕ)
    (hzero : ∀ n ≥ N, 0 ≤ z n ∧ E (((sgn * z n : ℝ) : ℂ)) = 0) :
    ∀ n ≥ N, knsWeightedPrincipalRoot sgn κ ε E (((z n) ^ 2 : ℝ) : ℂ) = 0 := by
  intro n hn
  rw [knsWeightedPrincipalRoot_of_nonneg sgn κ ε E (hzero n hn).1, (hzero n hn).2]
  exact mul_zero _

/-- The principal square root has the exact norm-square of its input, even
at zero and on the branch cut; no analyticity at those points is used. -/
private theorem norm_sq_principalRoot (w : ℂ) : ‖Complex.sqrt w‖ ^ 2 = ‖w‖ := by
  have hsquare : (Complex.sqrt w) ^ 2 = w := by
    rw [Complex.sqrt, ← Complex.cpow_mul_nat]
    norm_num
  simpa only [norm_pow] using congrArg norm hsquare

/-- For a genuine sign, a global quadratic norm bound on the entire input
becomes the stated global linear bound on the weighted-root composition. This
norm estimate holds at every complex point and needs no sign assumption on B. -/
theorem norm_knsWeightedPrincipalRoot_le_exp_linear {sgn κ ε : ℝ} {E : ℂ → ℂ}
    {Cquad B : ℝ} (hsgn : sgn = 1 ∨ sgn = -1) (hCquad : 0 ≤ Cquad)
    (hquad : ∀ z : ℂ, ‖E z‖ ≤ Cquad * Real.exp (B * ‖z‖ ^ 2)) (w : ℂ) :
    ‖knsWeightedPrincipalRoot sgn κ ε E w‖ ≤
      Cquad * Real.exp ((|2 * Real.pi * κ - ε| + B) * ‖w‖) := by
  have hsignnorm : ‖(sgn : ℂ)‖ = 1 := by
    rcases hsgn with rfl | rfl <;> norm_num
  have hargnorm : ‖(sgn : ℂ) * Complex.sqrt w‖ ^ 2 = ‖w‖ := by
    rw [norm_mul, hsignnorm, one_mul, norm_sq_principalRoot]
  have hweight : (2 * Real.pi * κ - ε) * w.re ≤ |2 * Real.pi * κ - ε| * ‖w‖ := by
    calc
      _ ≤ |(2 * Real.pi * κ - ε) * w.re| := le_abs_self _
      _ = |2 * Real.pi * κ - ε| * |w.re| := abs_mul _ _
      _ ≤ |2 * Real.pi * κ - ε| * ‖w‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm w) (abs_nonneg _)
  simp only [knsWeightedPrincipalRoot, norm_mul, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    _ ≤ Real.exp ((2 * Real.pi * κ - ε) * w.re) *
        (Cquad * Real.exp (B * ‖(sgn : ℂ) * Complex.sqrt w‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (hquad _) (Real.exp_pos _).le
    _ = Cquad * Real.exp ((2 * Real.pi * κ - ε) * w.re + B * ‖w‖) := by
      rw [hargnorm, mul_left_comm, ← Real.exp_add]
    _ ≤ Cquad * Real.exp ((|2 * Real.pi * κ - ε| + B) * ‖w‖) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCquad
      nlinarith

/-- The weighted principal-root package under the standard positive-rate
inputs. The positivity of kappa and epsilon expresses the intended application,
but is not needed for the algebraic identities; the helper lemmas expose their
weaker exact hypotheses. No sector-growth conclusion is included. -/
theorem knsWeightedPrincipalRoot_properties {sgn κ ε Creal Cquad B : ℝ}
    {E : ℂ → ℂ} (hE : Differentiable ℂ E) (hsgn : sgn = 1 ∨ sgn = -1)
    (_hκ : 0 < κ) (_hε : 0 < ε) (_hCreal : 0 ≤ Creal) (hCquad : 0 < Cquad)
    (_hB : 0 ≤ B)
    (hreal : ∀ t : ℝ, 0 ≤ t →
      ‖E (((sgn * t : ℝ) : ℂ))‖ ≤ Creal * Real.exp (-2 * Real.pi * κ * t ^ 2))
    (hquad : ∀ z : ℂ, ‖E z‖ ≤ Cquad * Real.exp (B * ‖z‖ ^ 2)) :
    AnalyticOnNhd ℂ (knsWeightedPrincipalRoot sgn κ ε E) {w : ℂ | 0 < w.re} ∧
      (∀ t : ℝ, 0 ≤ t →
        knsWeightedPrincipalRoot sgn κ ε E ((t ^ 2 : ℝ) : ℂ) =
          Complex.exp ((((2 * Real.pi * κ - ε) * t ^ 2 : ℝ) : ℂ)) *
            E (((sgn * t : ℝ) : ℂ))) ∧
      (∀ x : ℝ, 0 ≤ x →
        ‖knsWeightedPrincipalRoot sgn κ ε E (x : ℂ)‖ ≤ Creal * Real.exp (-ε * x)) ∧
      (∀ (z : ℕ → ℝ) (N : ℕ),
        (∀ n ≥ N, 0 ≤ z n ∧ E (((sgn * z n : ℝ) : ℂ)) = 0) →
          ∀ n ≥ N, knsWeightedPrincipalRoot sgn κ ε E (((z n) ^ 2 : ℝ) : ℂ) = 0) ∧
      (∀ w : ℂ, ‖knsWeightedPrincipalRoot sgn κ ε E w‖ ≤
        Cquad * Real.exp ((|2 * Real.pi * κ - ε| + B) * ‖w‖)) := by
  exact ⟨analyticOnNhd_knsWeightedPrincipalRoot sgn κ ε hE,
    fun _ ht => knsWeightedPrincipalRoot_of_nonneg sgn κ ε E ht,
    fun _ hx => norm_knsWeightedPrincipalRoot_real_le sgn κ ε hreal hx,
    fun z N hz => knsWeightedPrincipalRoot_zero_tail sgn κ ε E z N hz,
    norm_knsWeightedPrincipalRoot_le_exp_linear hsgn hCquad.le hquad⟩

end MeyerGeneralProblem
