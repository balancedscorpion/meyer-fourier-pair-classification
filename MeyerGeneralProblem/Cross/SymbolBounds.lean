module

public import MeyerGeneralProblem.Cross.NormalizedRemainder
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic.Bound

@[expose] public section

/-!
# Differentiated normalized cross-block symbol

This module normalizes the spatial leading amplitude on logarithmic blocks of
width `1 / m`.  The scale ratio enters only through a logistic function taking
values in `[0, 1]`; coordinate differentiation therefore introduces no
positive power of `m`.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- Logistic ratio controlling every derivative of the normalized block
amplitude. -/
def normalizedCrossBlockLogistic (m : ℕ) (R u v : ℝ) : ℝ :=
  R * Real.exp (u / (m : ℝ)) /
    (R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ)))

/-- The normalized nonoscillatory leading amplitude in the direct power form
from the analytic proof. -/
def normalizedCrossBlockRawAmplitude (m : ℕ) (R u v : ℝ) : ℝ :=
  Real.exp (((m : ℝ) - 1 / 4) * (u + v) / (m : ℝ)) *
    ((1 + R) /
      (R * Real.exp (u / (m : ℝ)) +
        Real.exp (v / (m : ℝ)))) ^ (2 * m)

/-- Logarithm of the normalized block amplitude.  This form makes its
derivatives algebraic in `normalizedCrossBlockLogistic`. -/
def normalizedCrossBlockLogAmplitude (m : ℕ) (R u v : ℝ) : ℝ :=
  ((m : ℝ) - 1 / 4) * (u + v) / (m : ℝ) +
    (2 * m : ℝ) * Real.log
      ((1 + R) /
        (R * Real.exp (u / (m : ℝ)) +
          Real.exp (v / (m : ℝ))))

/-- Real normalized block amplitude before the harmless inclusion into `ℂ`. -/
def normalizedCrossBlockRealAmplitude (m : ℕ) (R u v : ℝ) : ℝ :=
  Real.exp (normalizedCrossBlockLogAmplitude m R u v)

/-- Smooth complex normalized block amplitude used by the differentiated-symbol
API.  The oscillatory Fourier phase is deliberately not part of this symbol. -/
def normalizedCrossBlockAmplitude (m : ℕ) (R u v : ℝ) : ℂ :=
  (normalizedCrossBlockRealAmplitude m R u v : ℂ)

/-- The logarithmic and direct-power definitions of the normalized amplitude
agree on the positive scale-ratio domain. -/
theorem normalizedCrossBlockAmplitude_eq_raw
    (m : ℕ) {R : ℝ} (hR : 0 ≤ R) (u v : ℝ) :
    normalizedCrossBlockRealAmplitude m R u v =
      normalizedCrossBlockRawAmplitude m R u v := by
  have hdenPos : 0 < R * Real.exp (u / (m : ℝ)) +
      Real.exp (v / (m : ℝ)) := by positivity
  have hquotPos : 0 < (1 + R) /
      (R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ))) := by
    positivity
  unfold normalizedCrossBlockRealAmplitude normalizedCrossBlockLogAmplitude
    normalizedCrossBlockRawAmplitude
  rw [Real.exp_add]
  congr 1
  rw [show (2 * m : ℝ) * Real.log
      ((1 + R) /
        (R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ)))) =
      (((2 * m : ℕ) : ℝ)) * Real.log
        ((1 + R) /
          (R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ)))) by
    push_cast
    ring,
    Real.exp_nat_mul, Real.exp_log hquotPos]

/-- Swapping the two logarithmic block coordinates replaces the scale ratio
by its reciprocal.  This is the exact symmetry used after conjugate-transpose
when the larger carrier block initially lies on the column side. -/
theorem normalizedCrossBlockAmplitude_inv_swap
    (m : ℕ) {R : ℝ} (hR : 0 < R) (u v : ℝ) :
    normalizedCrossBlockAmplitude m R u v =
      normalizedCrossBlockAmplitude m R⁻¹ v u := by
  apply congrArg Complex.ofReal
  rw [normalizedCrossBlockAmplitude_eq_raw m hR.le,
    normalizedCrossBlockAmplitude_eq_raw m (inv_nonneg.mpr hR.le)]
  unfold normalizedCrossBlockRawAmplitude
  congr 1
  · congr 1
    ring
  · congr 1
    field_simp [hR.ne']
    ring

/-- The logistic ratio is nonnegative for nonnegative scale ratio. -/
theorem normalizedCrossBlockLogistic_nonneg
    (m : ℕ) {R u v : ℝ} (hR : 0 ≤ R) :
    0 ≤ normalizedCrossBlockLogistic m R u v := by
  unfold normalizedCrossBlockLogistic
  positivity

/-- The logistic ratio is at most one for nonnegative scale ratio. -/
theorem normalizedCrossBlockLogistic_le_one
    (m : ℕ) {R u v : ℝ} (hR : 0 ≤ R) :
    normalizedCrossBlockLogistic m R u v ≤ 1 := by
  unfold normalizedCrossBlockLogistic
  have hden : 0 < R * Real.exp (u / (m : ℝ)) +
      Real.exp (v / (m : ℝ)) := by positivity
  rw [div_le_one hden]
  linarith [Real.exp_pos (v / (m : ℝ))]

/-- Differentiating the logistic ratio in the first block coordinate. -/
theorem hasDerivAt_normalizedCrossBlockLogistic_u
    (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R) (u v : ℝ) :
    HasDerivAt (fun z => normalizedCrossBlockLogistic m R z v)
      ((1 / (m : ℝ)) * normalizedCrossBlockLogistic m R u v *
        (1 - normalizedCrossBlockLogistic m R u v)) u := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hden : R * Real.exp (u / (m : ℝ)) +
      Real.exp (v / (m : ℝ)) ≠ 0 := by positivity
  have heu : HasDerivAt (fun z : ℝ => Real.exp (z / (m : ℝ)))
      (Real.exp (u / (m : ℝ)) / (m : ℝ)) u := by
    simpa [div_eq_mul_inv, mul_comm] using
      ((hasDerivAt_id u).div_const (m : ℝ)).exp
  have hnum := heu.const_mul R
  have hdenDeriv := hnum.add_const (Real.exp (v / (m : ℝ)))
  unfold normalizedCrossBlockLogistic
  apply (hnum.div hdenDeriv hden).congr_deriv
  field_simp [hm0, hden]

/-- Differentiating the logistic ratio in the second block coordinate. -/
theorem hasDerivAt_normalizedCrossBlockLogistic_v
    (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R) (u v : ℝ) :
    HasDerivAt (fun z => normalizedCrossBlockLogistic m R u z)
      (-(1 / (m : ℝ)) * normalizedCrossBlockLogistic m R u v *
        (1 - normalizedCrossBlockLogistic m R u v)) v := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hden : R * Real.exp (u / (m : ℝ)) +
      Real.exp (v / (m : ℝ)) ≠ 0 := by positivity
  have hev : HasDerivAt (fun z : ℝ => Real.exp (z / (m : ℝ)))
      (Real.exp (v / (m : ℝ)) / (m : ℝ)) v := by
    simpa [div_eq_mul_inv, mul_comm] using
      ((hasDerivAt_id v).div_const (m : ℝ)).exp
  have hnum := hasDerivAt_const v (R * Real.exp (u / (m : ℝ)))
  have hdenDeriv := hnum.add hev
  unfold normalizedCrossBlockLogistic
  apply (hnum.div hdenDeriv hden).congr_deriv
  simp only [Pi.add_apply]
  field_simp [hm0, hden]
  ring

/-- First logarithmic derivative in the first block coordinate. -/
theorem hasDerivAt_normalizedCrossBlockLogAmplitude_u
    (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R) (u v : ℝ) :
    HasDerivAt (fun z => normalizedCrossBlockLogAmplitude m R z v)
      (1 - 1 / (4 * (m : ℝ)) -
        2 * normalizedCrossBlockLogistic m R u v) u := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hden : R * Real.exp (u / (m : ℝ)) +
      Real.exp (v / (m : ℝ)) ≠ 0 := by positivity
  have heu : HasDerivAt (fun z : ℝ => Real.exp (z / (m : ℝ)))
      (Real.exp (u / (m : ℝ)) / (m : ℝ)) u := by
    simpa [div_eq_mul_inv, mul_comm] using
      ((hasDerivAt_id u).div_const (m : ℝ)).exp
  have hnum := heu.const_mul R
  have hdenDeriv := hnum.add_const (Real.exp (v / (m : ℝ)))
  have hquot := (hasDerivAt_const u (1 + R)).div hdenDeriv hden
  have hquotNe : (1 + R) /
      (R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ))) ≠ 0 := by
    positivity
  have hlog := hquot.log hquotNe
  have hlin : HasDerivAt
      (fun z : ℝ => ((m : ℝ) - 1 / 4) * (z + v) / (m : ℝ))
      (((m : ℝ) - 1 / 4) / (m : ℝ)) u := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id u).add_const v).const_mul
        ((m : ℝ) - 1 / 4)).div_const (m : ℝ)
  have htotal := hlin.add (hlog.const_mul (2 * m : ℝ))
  unfold normalizedCrossBlockLogAmplitude normalizedCrossBlockLogistic
  apply htotal.congr_deriv
  simp only [Pi.div_apply]
  field_simp [hm0, hden]
  ring

/-- First logarithmic derivative in the second block coordinate. -/
theorem hasDerivAt_normalizedCrossBlockLogAmplitude_v
    (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R) (u v : ℝ) :
    HasDerivAt (fun z => normalizedCrossBlockLogAmplitude m R u z)
      (1 - 1 / (4 * (m : ℝ)) -
        2 * (1 - normalizedCrossBlockLogistic m R u v)) v := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hden : R * Real.exp (u / (m : ℝ)) +
      Real.exp (v / (m : ℝ)) ≠ 0 := by positivity
  have hev : HasDerivAt (fun z : ℝ => Real.exp (z / (m : ℝ)))
      (Real.exp (v / (m : ℝ)) / (m : ℝ)) v := by
    simpa [div_eq_mul_inv, mul_comm] using
      ((hasDerivAt_id v).div_const (m : ℝ)).exp
  have hconst := hasDerivAt_const v (R * Real.exp (u / (m : ℝ)))
  have hdenDeriv := hconst.add hev
  have hquot := (hasDerivAt_const v (1 + R)).div hdenDeriv hden
  have hquotNe : (1 + R) /
      (R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ))) ≠ 0 := by
    positivity
  have hlog := hquot.log hquotNe
  have hlin : HasDerivAt
      (fun z : ℝ => ((m : ℝ) - 1 / 4) * (u + z) / (m : ℝ))
      (((m : ℝ) - 1 / 4) / (m : ℝ)) v := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id v).const_add u).const_mul
        ((m : ℝ) - 1 / 4)).div_const (m : ℝ)
  have htotal := hlin.add (hlog.const_mul (2 * m : ℝ))
  unfold normalizedCrossBlockLogAmplitude normalizedCrossBlockLogistic
  apply htotal.congr_deriv
  simp only [Pi.div_apply, Pi.add_apply]
  field_simp [hm0, hden]
  ring

/-- First derivative of the normalized amplitude in the first coordinate. -/
theorem hasDerivAt_normalizedCrossBlockAmplitude_u
    (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R) (u v : ℝ) :
    HasDerivAt (fun z => normalizedCrossBlockRealAmplitude m R z v)
      (normalizedCrossBlockRealAmplitude m R u v *
        (1 - 1 / (4 * (m : ℝ)) -
          2 * normalizedCrossBlockLogistic m R u v)) u := by
  simpa only [normalizedCrossBlockRealAmplitude] using
    (hasDerivAt_normalizedCrossBlockLogAmplitude_u m hm hR u v).exp

/-- First derivative of the normalized amplitude in the second coordinate. -/
theorem hasDerivAt_normalizedCrossBlockAmplitude_v
    (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R) (u v : ℝ) :
    HasDerivAt (fun z => normalizedCrossBlockRealAmplitude m R u z)
      (normalizedCrossBlockRealAmplitude m R u v *
        (1 - 1 / (4 * (m : ℝ)) -
          2 * (1 - normalizedCrossBlockLogistic m R u v))) v := by
  simpa only [normalizedCrossBlockRealAmplitude] using
    (hasDerivAt_normalizedCrossBlockLogAmplitude_v m hm hR u v).exp

/-- The affine part of either logarithmic derivative. -/
def normalizedCrossBlockLogSlope (m : ℕ) : ℝ :=
  1 - 1 / (4 * (m : ℝ))

/-- Polynomial update produced by one derivative in the first logarithmic
block coordinate. -/
def normalizedCrossBlockStepU (m : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  P * (Polynomial.C (normalizedCrossBlockLogSlope m) -
      Polynomial.C 2 * Polynomial.X) +
    P.derivative * Polynomial.C (1 / (m : ℝ)) *
      Polynomial.X * (1 - Polynomial.X)

/-- Polynomial update produced by one derivative in the second logarithmic
block coordinate. -/
def normalizedCrossBlockStepV (m : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  P * (Polynomial.C (normalizedCrossBlockLogSlope m - 2) +
      Polynomial.C 2 * Polynomial.X) +
    P.derivative * Polynomial.C (-(1 / (m : ℝ))) *
      Polynomial.X * (1 - Polynomial.X)

/-- Iterate the second-coordinate polynomial update from an arbitrary
polynomial. -/
def normalizedCrossBlockIterateV
    (m : ℕ) (P : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => P
  | b + 1 => normalizedCrossBlockStepV m
      (normalizedCrossBlockIterateV m P b)

/-- Iterate the second-coordinate polynomial update from the constant one. -/
def normalizedCrossBlockVPolynomial (m b : ℕ) : Polynomial ℝ :=
  normalizedCrossBlockIterateV m 1 b

/-- Starting with all second-coordinate derivatives, iterate the
first-coordinate update. -/
def normalizedCrossBlockIterateU
    (m : ℕ) (P : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => P
  | a + 1 => normalizedCrossBlockStepU m
      (normalizedCrossBlockIterateU m P a)

/-- Polynomial encoding `b` second-coordinate derivatives followed by `a`
first-coordinate derivatives. -/
def normalizedCrossBlockMixedPolynomial (m b a : ℕ) : Polynomial ℝ :=
  normalizedCrossBlockIterateU m (normalizedCrossBlockVPolynomial m b) a

/-- Concrete mixed derivative convention used by the multiplier theorem:
differentiate `b` times in the second coordinate and then `a` times in the
first coordinate. -/
def mixedIteratedDeriv
    (a b : ℕ) (f : ℝ → ℝ → ℂ) (u v : ℝ) : ℂ :=
  iteratedDeriv a
    (fun u' => iteratedDeriv b (fun v' => f u' v') v)
    u

private theorem hasDerivAt_normalizedCrossBlockPolynomial_u
    (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R)
    (P : Polynomial ℝ) (u v : ℝ) :
    HasDerivAt
      (fun z => normalizedCrossBlockRealAmplitude m R z v *
        P.eval (normalizedCrossBlockLogistic m R z v))
      (normalizedCrossBlockRealAmplitude m R u v *
        (normalizedCrossBlockStepU m P).eval
          (normalizedCrossBlockLogistic m R u v)) u := by
  let p := normalizedCrossBlockLogistic m R u v
  have hp := hasDerivAt_normalizedCrossBlockLogistic_u m hm hR u v
  have hP : HasDerivAt
      (fun z => P.eval (normalizedCrossBlockLogistic m R z v))
      (P.derivative.eval p * ((1 / (m : ℝ)) * p * (1 - p))) u := by
    exact (P.hasDerivAt p).comp u hp
  have hA := hasDerivAt_normalizedCrossBlockAmplitude_u m hm hR u v
  apply (hA.mul hP).congr_deriv
  simp only [normalizedCrossBlockStepU, normalizedCrossBlockLogSlope,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  dsimp only [p]
  ring

private theorem hasDerivAt_normalizedCrossBlockPolynomial_v
    (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R)
    (P : Polynomial ℝ) (u v : ℝ) :
    HasDerivAt
      (fun z => normalizedCrossBlockRealAmplitude m R u z *
        P.eval (normalizedCrossBlockLogistic m R u z))
      (normalizedCrossBlockRealAmplitude m R u v *
        (normalizedCrossBlockStepV m P).eval
          (normalizedCrossBlockLogistic m R u v)) v := by
  let p := normalizedCrossBlockLogistic m R u v
  have hp := hasDerivAt_normalizedCrossBlockLogistic_v m hm hR u v
  have hP : HasDerivAt
      (fun z => P.eval (normalizedCrossBlockLogistic m R u z))
      (P.derivative.eval p * (-(1 / (m : ℝ)) * p * (1 - p))) v := by
    exact (P.hasDerivAt p).comp v hp
  have hA := hasDerivAt_normalizedCrossBlockAmplitude_v m hm hR u v
  apply (hA.mul hP).congr_deriv
  simp only [normalizedCrossBlockStepV, normalizedCrossBlockLogSlope,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  dsimp only [p]
  ring

private theorem iteratedDeriv_normalizedCrossBlockPolynomial_v
    (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R)
    (P : Polynomial ℝ) (b : ℕ) (u v : ℝ) :
    iteratedDeriv b
        (fun z => ((normalizedCrossBlockRealAmplitude m R u z *
          P.eval (normalizedCrossBlockLogistic m R u z) : ℝ) : ℂ)) v =
      ((normalizedCrossBlockRealAmplitude m R u v *
        (normalizedCrossBlockIterateV m P b).eval
          (normalizedCrossBlockLogistic m R u v) : ℝ) : ℂ) := by
  induction b generalizing v with
  | zero => rfl
  | succ b ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv b
          (fun z => ((normalizedCrossBlockRealAmplitude m R u z *
            P.eval (normalizedCrossBlockLogistic m R u z) : ℝ) : ℂ)) =
          fun z => ((normalizedCrossBlockRealAmplitude m R u z *
            (normalizedCrossBlockIterateV m P b).eval
              (normalizedCrossBlockLogistic m R u z) : ℝ) : ℂ) := by
        funext z
        exact ih z
      rw [hfun]
      exact (hasDerivAt_normalizedCrossBlockPolynomial_v m hm hR _ u v).ofReal_comp.deriv

private theorem iteratedDeriv_normalizedCrossBlockPolynomial_u
    (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R)
    (P : Polynomial ℝ) (a : ℕ) (u v : ℝ) :
    iteratedDeriv a
        (fun z => ((normalizedCrossBlockRealAmplitude m R z v *
          P.eval (normalizedCrossBlockLogistic m R z v) : ℝ) : ℂ)) u =
      ((normalizedCrossBlockRealAmplitude m R u v *
        (normalizedCrossBlockIterateU m P a).eval
          (normalizedCrossBlockLogistic m R u v) : ℝ) : ℂ) := by
  induction a generalizing u with
  | zero => rfl
  | succ a ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv a
          (fun z => ((normalizedCrossBlockRealAmplitude m R z v *
            P.eval (normalizedCrossBlockLogistic m R z v) : ℝ) : ℂ)) =
          fun z => ((normalizedCrossBlockRealAmplitude m R z v *
            (normalizedCrossBlockIterateU m P a).eval
              (normalizedCrossBlockLogistic m R z v) : ℝ) : ℂ) := by
        funext z
        exact ih z
      rw [hfun]
      exact (hasDerivAt_normalizedCrossBlockPolynomial_u m hm hR _ u v).ofReal_comp.deriv

/-- Exact algebraic formula for every mixed derivative of the normalized
amplitude. -/
theorem mixedIteratedDeriv_normalizedCrossBlockAmplitude
    (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R)
    (a b : ℕ) (u v : ℝ) :
    mixedIteratedDeriv a b (normalizedCrossBlockAmplitude m R) u v =
      ((normalizedCrossBlockRealAmplitude m R u v *
        (normalizedCrossBlockMixedPolynomial m b a).eval
          (normalizedCrossBlockLogistic m R u v) : ℝ) : ℂ) := by
  unfold mixedIteratedDeriv normalizedCrossBlockAmplitude
  have hv (z : ℝ) := iteratedDeriv_normalizedCrossBlockPolynomial_v
    m hm hR 1 b z v
  simp only [Polynomial.eval_one, mul_one] at hv
  rw [show (fun z => iteratedDeriv b
        (fun v' => ((normalizedCrossBlockRealAmplitude m R z v' : ℝ) : ℂ)) v) =
      fun z => ((normalizedCrossBlockRealAmplitude m R z v *
        (normalizedCrossBlockVPolynomial m b).eval
          (normalizedCrossBlockLogistic m R z v) : ℝ) : ℂ) by
    funext z
    simpa only [normalizedCrossBlockVPolynomial] using hv z]
  simpa only [normalizedCrossBlockMixedPolynomial] using
    iteratedDeriv_normalizedCrossBlockPolynomial_u m hm hR
      (normalizedCrossBlockVPolynomial m b) a u v

/-- The normalized amplitude is strictly positive. -/
theorem normalizedCrossBlockAmplitude_pos (m : ℕ) (R u v : ℝ) :
    0 < normalizedCrossBlockRealAmplitude m R u v := by
  unfold normalizedCrossBlockRealAmplitude
  positivity

/-- The normalized nonoscillatory symbol is genuinely `C⁴`; this prevents
iterated-derivative bounds from being vacuous at nondifferentiable points. -/
theorem normalizedCrossBlockAmplitude_contDiff
    (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 1 ≤ R) :
    ContDiff ℝ 4
      (Function.uncurry (normalizedCrossBlockAmplitude m R)) := by
  change ContDiff ℝ 4 (fun p : ℝ × ℝ =>
    ((normalizedCrossBlockRealAmplitude m R p.1 p.2 : ℝ) : ℂ))
  have hreal : ContDiff ℝ 4 (fun p : ℝ × ℝ =>
      normalizedCrossBlockRealAmplitude m R p.1 p.2) := by
    unfold normalizedCrossBlockRealAmplitude normalizedCrossBlockLogAmplitude
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have hden : ∀ p : ℝ × ℝ,
        R * Real.exp (p.1 / (m : ℝ)) +
          Real.exp (p.2 / (m : ℝ)) ≠ 0 := by
      intro p
      positivity
    have hquot : ∀ p : ℝ × ℝ,
        (1 + R) /
          (R * Real.exp (p.1 / (m : ℝ)) +
            Real.exp (p.2 / (m : ℝ))) ≠ 0 := by
      intro p
      exact div_ne_zero (by positivity) (hden p)
    have hdenDiff : ContDiff ℝ 4 (fun p : ℝ × ℝ =>
        R * Real.exp (p.1 / (m : ℝ)) +
          Real.exp (p.2 / (m : ℝ))) := by
      fun_prop
    have hquotDiff : ContDiff ℝ 4 (fun p : ℝ × ℝ =>
        (1 + R) /
          (R * Real.exp (p.1 / (m : ℝ)) +
            Real.exp (p.2 / (m : ℝ)))) := by
      exact contDiff_const.div hdenDiff hden
    have hlogDiff := hquotDiff.log hquot
    have hlin : ContDiff ℝ 4 (fun p : ℝ × ℝ =>
        ((m : ℝ) - 1 / 4) * (p.1 + p.2) / (m : ℝ)) := by
      fun_prop
    exact (hlin.add (contDiff_const.mul hlogDiff)).exp
  exact Complex.ofRealCLM.contDiff.comp hreal

/-- Uniform zeroth-order bound on the unit logarithmic block. -/
theorem normalizedCrossBlockAmplitude_le_exp_two
    (m : ℕ) (hm : 1 ≤ m) {R u v : ℝ}
    (hR : 0 ≤ R) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    normalizedCrossBlockRealAmplitude m R u v ≤ Real.exp 2 := by
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have heu : 1 ≤ Real.exp (u / (m : ℝ)) :=
    Real.one_le_exp (div_nonneg hu0 hmPos.le)
  have hev : 1 ≤ Real.exp (v / (m : ℝ)) :=
    Real.one_le_exp (div_nonneg hv0 hmPos.le)
  have hdenPos : 0 < R * Real.exp (u / (m : ℝ)) +
      Real.exp (v / (m : ℝ)) := by positivity
  have hdenLower : 1 + R ≤
      R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ)) := by
    nlinarith
  have hq0 : 0 ≤ (1 + R) /
      (R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ))) := by
    positivity
  have hq1 : (1 + R) /
      (R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ))) ≤ 1 := by
    rw [div_le_one hdenPos]
    exact hdenLower
  have hpow : ((1 + R) /
      (R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ)))) ^
        (2 * m) ≤ 1 := pow_le_one₀ hq0 hq1
  have hcoef0 : 0 ≤ ((m : ℝ) - 1 / 4) / (m : ℝ) := by
    have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
    exact div_nonneg (by linarith) hmPos.le
  have hcoef1 : ((m : ℝ) - 1 / 4) / (m : ℝ) ≤ 1 := by
    rw [div_le_one hmPos]
    linarith
  have hexponent : ((m : ℝ) - 1 / 4) * (u + v) / (m : ℝ) ≤ 2 := by
    rw [show ((m : ℝ) - 1 / 4) * (u + v) / (m : ℝ) =
      (((m : ℝ) - 1 / 4) / (m : ℝ)) * (u + v) by ring]
    nlinarith
  rw [normalizedCrossBlockAmplitude_eq_raw m hR]
  unfold normalizedCrossBlockRawAmplitude
  calc
    Real.exp (((m : ℝ) - 1 / 4) * (u + v) / (m : ℝ)) *
          ((1 + R) /
            (R * Real.exp (u / (m : ℝ)) +
              Real.exp (v / (m : ℝ)))) ^ (2 * m) ≤
        Real.exp 2 * 1 := by
      exact mul_le_mul (Real.exp_le_exp.mpr hexponent) hpow
        (pow_nonneg hq0 _) (Real.exp_pos _).le
    _ = Real.exp 2 := mul_one _

/-- Uniform zeroth-order bound on the enlarged cutoff square required by the
Fourier-multiplier extension. -/
theorem normalizedCrossBlockAmplitude_le_exp_six
    (m : ℕ) (hm : 1 ≤ m) {R u v : ℝ}
    (hR : 0 ≤ R) (hu0 : -1 ≤ u) (hu1 : u ≤ 2)
    (hv0 : -1 ≤ v) (hv1 : v ≤ 2) :
    normalizedCrossBlockRealAmplitude m R u v ≤ Real.exp 6 := by
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have heu : Real.exp (-(1 / (m : ℝ))) ≤
      Real.exp (u / (m : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [show -(1 / (m : ℝ)) = (-1 : ℝ) / (m : ℝ) by ring]
    exact (div_le_div_iff_of_pos_right hmPos).mpr hu0
  have hev : Real.exp (-(1 / (m : ℝ))) ≤
      Real.exp (v / (m : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [show -(1 / (m : ℝ)) = (-1 : ℝ) / (m : ℝ) by ring]
    exact (div_le_div_iff_of_pos_right hmPos).mpr hv0
  have hdenPos : 0 < R * Real.exp (u / (m : ℝ)) +
      Real.exp (v / (m : ℝ)) := by positivity
  have hdenLower : (1 + R) * Real.exp (-(1 / (m : ℝ))) ≤
      R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left heu hR]
  have hq0 : 0 ≤ (1 + R) /
      (R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ))) := by
    positivity
  have hexpCancel : Real.exp (1 / (m : ℝ)) *
      ((1 + R) * Real.exp (-(1 / (m : ℝ)))) = 1 + R := by
    calc
      Real.exp (1 / (m : ℝ)) *
          ((1 + R) * Real.exp (-(1 / (m : ℝ)))) =
        (1 + R) *
          (Real.exp (1 / (m : ℝ)) *
            Real.exp (-(1 / (m : ℝ)))) := by ring
      _ = 1 + R := by rw [← Real.exp_add]; norm_num
  have hq1 : (1 + R) /
      (R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ))) ≤
        Real.exp (1 / (m : ℝ)) := by
    rw [div_le_iff₀ hdenPos]
    rw [← hexpCancel]
    exact mul_le_mul_of_nonneg_left hdenLower (Real.exp_pos _).le
  have hpowRaw := pow_le_pow_left₀ hq0 hq1 (2 * m)
  have hexpPow : Real.exp (1 / (m : ℝ)) ^ (2 * m) = Real.exp 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hpow : ((1 + R) /
      (R * Real.exp (u / (m : ℝ)) + Real.exp (v / (m : ℝ)))) ^
        (2 * m) ≤ Real.exp 2 := by
    exact hpowRaw.trans_eq hexpPow
  have hcoef0 : 0 ≤ ((m : ℝ) - 1 / 4) / (m : ℝ) := by
    exact div_nonneg (by linarith) hmPos.le
  have hcoef1 : ((m : ℝ) - 1 / 4) / (m : ℝ) ≤ 1 := by
    rw [div_le_one hmPos]
    linarith
  have hsumLower : -2 ≤ u + v := by linarith
  have hsumUpper : u + v ≤ 4 := by linarith
  have hexponent : ((m : ℝ) - 1 / 4) * (u + v) / (m : ℝ) ≤ 4 := by
    rw [show ((m : ℝ) - 1 / 4) * (u + v) / (m : ℝ) =
      (((m : ℝ) - 1 / 4) / (m : ℝ)) * (u + v) by ring]
    nlinarith
  rw [normalizedCrossBlockAmplitude_eq_raw m hR]
  unfold normalizedCrossBlockRawAmplitude
  calc
    Real.exp (((m : ℝ) - 1 / 4) * (u + v) / (m : ℝ)) *
          ((1 + R) /
            (R * Real.exp (u / (m : ℝ)) +
              Real.exp (v / (m : ℝ)))) ^ (2 * m) ≤
        Real.exp 4 * Real.exp 2 := by
      exact mul_le_mul (Real.exp_le_exp.mpr hexponent) hpow
        (pow_nonneg hq0 _) (Real.exp_pos _).le
    _ = Real.exp 6 := by rw [← Real.exp_add]; norm_num

set_option maxHeartbeats 1000000 in
/-- A deliberately loose absolute bound for the derivative polynomials
through total order four.  Its only purpose is to make independence of `m`
and the block ratio completely explicit. -/
theorem normalizedCrossBlockMixedPolynomial_eval_abs_le
    (m : ℕ) (hm : 1 ≤ m) (a b : ℕ) (hab : a + b ≤ 4)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |(normalizedCrossBlockMixedPolynomial m b a).eval p| ≤ 100000 := by
  have hr0 : 0 ≤ (m : ℝ)⁻¹ := by positivity
  have hr1 : (m : ℝ)⁻¹ ≤ 1 := by
    rw [← one_div, div_le_one (by positivity : (0 : ℝ) < m)]
    exact_mod_cast hm
  have hrp (i j : ℕ) :
      0 ≤ (m : ℝ)⁻¹ ^ i * p ^ j ∧ (m : ℝ)⁻¹ ^ i * p ^ j ≤ 1 := by
    constructor
    · exact mul_nonneg (pow_nonneg hr0 _) (pow_nonneg hp0 _)
    · exact mul_le_one₀ (pow_le_one₀ hr0 hr1)
        (pow_nonneg hp0 _) (pow_le_one₀ hp0 hp1)
  have hrp' (i j : ℕ) :
      0 ≤ ((m : ℝ) ^ i)⁻¹ * p ^ j ∧ ((m : ℝ) ^ i)⁻¹ * p ^ j ≤ 1 := by
    simpa only [← inv_pow] using hrp i j
  have h01 := hrp' 0 1
  have h02 := hrp' 0 2
  have h03 := hrp' 0 3
  have h04 := hrp' 0 4
  have h10 := hrp' 1 0
  have h11 := hrp' 1 1
  have h12 := hrp' 1 2
  have h13 := hrp' 1 3
  have h14 := hrp' 1 4
  have h20 := hrp' 2 0
  have h21 := hrp' 2 1
  have h22 := hrp' 2 2
  have h23 := hrp' 2 3
  have h24 := hrp' 2 4
  have h30 := hrp' 3 0
  have h31 := hrp' 3 1
  have h32 := hrp' 3 2
  have h33 := hrp' 3 3
  have h34 := hrp' 3 4
  have h40 := hrp' 4 0
  have h41 := hrp' 4 1
  have h42 := hrp' 4 2
  have h43 := hrp' 4 3
  have h44 := hrp' 4 4
  norm_num only [pow_zero, pow_one, inv_one, one_mul, mul_one] at h01 h02 h03 h04 h10 h11 h12 h13 h14 h20 h21 h22 h23 h24 h30 h31 h32 h33 h34 h40 h41 h42 h43 h44
  have ha : a ≤ 4 := by omega
  have hb : b ≤ 4 := by omega
  interval_cases a <;> interval_cases b <;> norm_num at hab
  all_goals
    simp only [normalizedCrossBlockMixedPolynomial,
      normalizedCrossBlockVPolynomial, normalizedCrossBlockIterateU,
      normalizedCrossBlockIterateV, normalizedCrossBlockStepU,
      normalizedCrossBlockStepV, normalizedCrossBlockLogSlope,
      Polynomial.derivative_zero, Polynomial.derivative_one,
      Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_X,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_zero, zero_mul, mul_zero, zero_add, add_zero,
      one_mul, mul_one, sub_zero]
    ring_nf
    try simp only [inv_pow]
    try norm_num
    try (rw [abs_le]; constructor <;> bound)

/-- One absolute constant controls every genuine mixed derivative through
total order four, uniformly in Hermite order, block ratio, and position on
the enlarged cutoff square. -/
theorem exists_uniform_normalizedCrossBlockAmplitude_mixedDeriv_bound :
    ∃ C : NNReal,
      ∀ (m : ℕ), 1 ≤ m →
      ∀ {R : ℝ}, 1 ≤ R →
      ∀ (a b : ℕ), a + b ≤ 4 →
      ∀ {u v : ℝ},
        u ∈ Set.Icc (-1 : ℝ) 2 →
        v ∈ Set.Icc (-1 : ℝ) 2 →
        ‖mixedIteratedDeriv a b
            (normalizedCrossBlockAmplitude m R) u v‖ ≤ (C : ℝ) := by
  refine ⟨⟨100000 * Real.exp 6, by positivity⟩, ?_⟩
  intro m hm R hR a b hab u v hu hv
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  let p := normalizedCrossBlockLogistic m R u v
  have hp0 : 0 ≤ p := normalizedCrossBlockLogistic_nonneg m hR0
  have hp1 : p ≤ 1 := normalizedCrossBlockLogistic_le_one m hR0
  have hA : normalizedCrossBlockRealAmplitude m R u v ≤ Real.exp 6 :=
    normalizedCrossBlockAmplitude_le_exp_six m hm hR0
      hu.1 hu.2 hv.1 hv.2
  have hP : |(normalizedCrossBlockMixedPolynomial m b a).eval p| ≤ 100000 :=
    normalizedCrossBlockMixedPolynomial_eval_abs_le m hm a b hab hp0 hp1
  rw [mixedIteratedDeriv_normalizedCrossBlockAmplitude m hm hR0]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  rw [abs_of_pos (normalizedCrossBlockAmplitude_pos m R u v)]
  calc
    normalizedCrossBlockRealAmplitude m R u v *
        |(normalizedCrossBlockMixedPolynomial m b a).eval p| ≤
      Real.exp 6 * 100000 := by
        exact mul_le_mul hA hP (abs_nonneg _) (Real.exp_pos _).le
    _ = 100000 * Real.exp 6 := by ring

/-- Exact bridge from the genuine Gram-normalized leading kernel to the
uniform logarithmic-block symbol. -/
theorem gramNormalizedCrossLeadingTerm_logBlock_factorization
    (m : ℕ) (hm : 1 ≤ m)
    {M N : ℝ} (hM : 0 < M) (hN : 0 < N)
    (u v x y : ℝ) :
    gramNormalizedCrossLeadingTerm m
        (M * Real.exp (u / (m : ℝ)))
        (N * Real.exp (v / (m : ℝ))) x y =
      ((((gramNormalization m *
        (M * N) ^ ((m : ℝ) - 1 / 4) /
        (M + N) ^ (2 * m) : ℝ) : ℂ) *
      normalizedCrossBlockAmplitude m (M / N) u v) *
      crossMehlerLeadingPhase x y) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hMN : 0 < M * N := mul_pos hM hN
  have hsum : 0 < M + N := add_pos hM hN
  have hscaledSum : 0 <
      M * Real.exp (u / (m : ℝ)) +
        N * Real.exp (v / (m : ℝ)) := by positivity
  have hratio : 0 ≤ M / N := (div_pos hM hN).le
  have hquot :
      (1 + M / N) /
          ((M / N) * Real.exp (u / (m : ℝ)) +
            Real.exp (v / (m : ℝ))) =
        (M + N) /
          (M * Real.exp (u / (m : ℝ)) +
            N * Real.exp (v / (m : ℝ))) := by
    field_simp [hN.ne']
    ring
  have hexpProduct :
      Real.exp (u / (m : ℝ)) * Real.exp (v / (m : ℝ)) =
        Real.exp ((u + v) / (m : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrpow :
      ((M * Real.exp (u / (m : ℝ))) *
          (N * Real.exp (v / (m : ℝ)))) ^
          ((m : ℝ) - 1 / 4) =
        (M * N) ^ ((m : ℝ) - 1 / 4) *
          Real.exp (((m : ℝ) - 1 / 4) * (u + v) / (m : ℝ)) := by
    rw [show (M * Real.exp (u / (m : ℝ))) *
          (N * Real.exp (v / (m : ℝ))) =
        (M * N) * Real.exp ((u + v) / (m : ℝ)) by
      rw [← hexpProduct]
      ring,
      Real.mul_rpow hMN.le (Real.exp_pos _).le,
      ← Real.exp_mul]
    congr 2
    ring
  have hreal :
      gramNormalization m *
          ((M * Real.exp (u / (m : ℝ))) *
            (N * Real.exp (v / (m : ℝ)))) ^
              ((m : ℝ) - 1 / 4) /
          (M * Real.exp (u / (m : ℝ)) +
            N * Real.exp (v / (m : ℝ))) ^ (2 * m) =
        (gramNormalization m *
            (M * N) ^ ((m : ℝ) - 1 / 4) /
            (M + N) ^ (2 * m)) *
          normalizedCrossBlockRealAmplitude m (M / N) u v := by
    rw [normalizedCrossBlockAmplitude_eq_raw m hratio]
    unfold normalizedCrossBlockRawAmplitude
    rw [hquot, hrpow]
    rw [div_pow]
    field_simp [hsum.ne', hscaledSum.ne']
  unfold gramNormalizedCrossLeadingTerm normalizedCrossBlockAmplitude
  rw [← Complex.ofReal_mul]
  exact congrArg (fun z : ℝ => (z : ℂ) * crossMehlerLeadingPhase x y) hreal

end

end MeyerGeneralProblem
