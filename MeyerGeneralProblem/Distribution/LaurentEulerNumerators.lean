module

public import MeyerGeneralProblem.Distribution.LaurentEulerRecurrence
public import Mathlib.RingTheory.Derivation.Basic

@[expose] public section

/-!
# Euler differentiation of finite recurrence numerators

Clearing the next denominator uses the Euler product rule on the
original array. At a prime of the denominator, the highest-order
numerator reduces to a product of the original Euler residues.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- The polynomial restriction of the original Euler weighting is a
complex-linear derivation of the Laurent ring. -/
def laurentEulerDerivation (e : G →+ ℂ) :
    Derivation ℂ (AddMonoidAlgebra ℂ G) (AddMonoidAlgebra ℂ G) where
  toFun := laurentEulerPolynomial e
  map_add' p q := by
    apply AddMonoidAlgebra.coeff_injective
    ext n
    simp only [laurentEulerPolynomial_coeff, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, mul_add]
  map_smul' c p := by
    apply AddMonoidAlgebra.coeff_injective
    ext n
    simp only [RingHom.id_apply, laurentEulerPolynomial_coeff,
      AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
    ring
  map_one_eq_zero' := by
    apply AddMonoidAlgebra.coeff_injective
    ext n
    by_cases hn : n = 0
    · simp [hn, laurentEulerPolynomial_coeff]
    · simp [laurentEulerPolynomial_coeff, AddMonoidAlgebra.one_def, hn]
  leibniz' p q := by
    apply AddMonoidAlgebra.coeff_injective
    ext n
    change (laurentEulerPolynomial e (p * q)).coeff n =
      (p * laurentEulerPolynomial e q + q * laurentEulerPolynomial e p).coeff n
    have h := congrFun (laurentEulerArray_convolution e p q.coeff) n
    simp only [Pi.add_apply] at h
    change _ = annihilatorArrayConvolution p.coeff (laurentEulerPolynomial e q).coeff n +
      annihilatorArrayConvolution (laurentEulerPolynomial e p).coeff q.coeff n at h
    have hpq : annihilatorArrayConvolution p.coeff q.coeff = (p * q).coeff :=
      funext (annihilatorArrayConvolution_finite p q)
    rw [hpq, annihilatorArrayConvolution_finite,
      annihilatorArrayConvolution_finite, laurentEulerArray,
      ← laurentEulerPolynomial_coeff] at h
    simpa only [mul_comm q (laurentEulerPolynomial e p),
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using h

theorem laurentEulerDerivation_apply (e : G →+ ℂ) (p : AddMonoidAlgebra ℂ G) :
    laurentEulerDerivation e p = laurentEulerPolynomial e p := rfl

private theorem mul_laurentEulerPolynomial_pow (e : G →+ ℂ)
    (p : AddMonoidAlgebra ℂ G) (m : ℕ) :
    p * laurentEulerPolynomial e (p ^ m) = m • (laurentEulerPolynomial e p * p ^ m) := by
  change p * laurentEulerDerivation e (p ^ m) = _
  cases m with
  | zero => simp
  | succ m =>
    rw [Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, laurentEulerDerivation_apply]
    simp only [nsmul_eq_mul, pow_succ]
    ring

/-- One Euler operator differentiates the finite numerator after the
next denominator power is cleared on the same original array. -/
theorem annihilatorArrayConvolution_eulerNumerator_step
    (e : G →+ ℂ) (p q : AddMonoidAlgebra ℂ G) (m : ℕ) (w : G → ℂ)
    (h : annihilatorArrayConvolution (p ^ m).coeff w = q.coeff) :
    annihilatorArrayConvolution (p ^ (m + 1)).coeff (laurentEulerArray e w) =
      (p * laurentEulerPolynomial e q - m • (laurentEulerPolynomial e p * q)).coeff := by
  have hd := laurentEulerArray_convolution e (p ^ m) w
  rw [h] at hd
  have hder :
      annihilatorArrayConvolution (p ^ m).coeff (laurentEulerArray e w) =
        laurentEulerArray e q.coeff -
          annihilatorArrayConvolution (laurentEulerPolynomial e (p ^ m)).coeff w :=
    eq_sub_of_add_eq hd.symm
  ext n
  rw [pow_succ', annihilatorArrayConvolution_mul, hder, annihilatorArrayConvolution_sub]
  change annihilatorArrayConvolution p.coeff (laurentEulerPolynomial e q).coeff n - _ = _
  rw [annihilatorArrayConvolution_finite, ← annihilatorArrayConvolution_mul,
    mul_laurentEulerPolynomial_pow, ← originalLaurentArrayAction_apply, map_nsmul]
  change (p * laurentEulerPolynomial e q).coeff n -
    m • originalLaurentArrayAction (laurentEulerPolynomial e p * p ^ m) w n = _
  rw [originalLaurentArrayAction_apply, annihilatorArrayConvolution_mul, h,
    annihilatorArrayConvolution_finite, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  rfl

/-- The successive finite numerator obtained from an ordered product of
Euler operators. The list order agrees with the actual array action. -/
def laurentEulerNumerator (p : AddMonoidAlgebra ℂ G) (m : ℕ)
    (q : AddMonoidAlgebra ℂ G) : List (G →+ ℂ) → AddMonoidAlgebra ℂ G
  | [] => q
  | e :: es =>
    let r := laurentEulerNumerator p m q es
    p * laurentEulerPolynomial e r - (m + es.length) • (laurentEulerPolynomial e p * r)

/-- The iterated numerator is the literal convolution of the same Euler
weighted array after the prescribed power of the denominator is cleared. -/
theorem annihilatorArrayConvolution_eulerNumerator
    (p q : AddMonoidAlgebra ℂ G) (m : ℕ) (w : G → ℂ)
    (h : annihilatorArrayConvolution (p ^ m).coeff w = q.coeff) (es : List (G →+ ℂ)) :
    annihilatorArrayConvolution (p ^ (m + es.length)).coeff
        (es.foldr laurentEulerArray w) = (laurentEulerNumerator p m q es).coeff := by
  induction es with
  | nil => simpa [laurentEulerNumerator] using h
  | cons e es ih =>
    exact annihilatorArrayConvolution_eulerNumerator_step e p _ (m + es.length) _ ih

/-- In any residue ring killing p, the exact leading numerator is the
rising factorial times the original numerator and the Euler residues. -/
theorem map_laurentEulerNumerator_of_map_eq_zero {R : Type*} [CommRing R]
    (φ : AddMonoidAlgebra ℂ G →+* R) (p q : AddMonoidAlgebra ℂ G) (hp : φ p = 0)
    (m : ℕ) (es : List (G →+ ℂ)) :
    φ (laurentEulerNumerator p m q es) =
      (-1 : R) ^ es.length * (m.ascFactorial es.length : R) *
        (es.map (fun e => φ (laurentEulerPolynomial e p))).prod * φ q := by
  induction es with
  | nil => simp [laurentEulerNumerator]
  | cons e es ih =>
    simp only [laurentEulerNumerator, map_sub, map_mul, hp, zero_mul, zero_sub, map_natCast,
      ih, List.length_cons, Nat.ascFactorial_succ, Nat.cast_mul, List.map_cons, List.prod_cons,
      pow_succ, nsmul_eq_mul]
    ring

/-- One differentiation step factors the exact forced power of a
chosen denominator prime, even in the presence of other factors and
partial cancellation in the original numerator. -/
theorem laurentEulerNumerator_factor_step (e : G →+ ℂ)
    (p q r : AddMonoidAlgebra ℂ G) (m a j : ℕ) :
    (p ^ (m + 1) * q) * laurentEulerPolynomial e (p ^ a * r) -
        (j + 1) • (laurentEulerPolynomial e (p ^ (m + 1) * q) * (p ^ a * r)) =
      p ^ (m + a) *
        (p * q * laurentEulerPolynomial e r +
          ((a : AddMonoidAlgebra ℂ G) - ((j + 1 : ℕ) : AddMonoidAlgebra ℂ G) *
            ((m + 1 : ℕ) : AddMonoidAlgebra ℂ G)) * (q * laurentEulerPolynomial e p * r) -
          (j + 1) • (p * laurentEulerPolynomial e q * r)) := by
  have hmul (s t : AddMonoidAlgebra ℂ G) :
      laurentEulerPolynomial e (s * t) =
        s * laurentEulerPolynomial e t + t * laurentEulerPolynomial e s := by
    simpa only [laurentEulerDerivation_apply, smul_eq_mul] using
      (laurentEulerDerivation e).leibniz s t
  have hpower : laurentEulerPolynomial e (p ^ (m + 1)) =
      (m + 1) • (p ^ m * laurentEulerPolynomial e p) := by
    simpa only [laurentEulerDerivation_apply, Nat.add_sub_cancel, smul_eq_mul] using
      (laurentEulerDerivation e).leibniz_pow p (m + 1)
  have hnum : p * laurentEulerPolynomial e (p ^ a * r) =
      p ^ a * (p * laurentEulerPolynomial e r + a • (laurentEulerPolynomial e p * r)) := by
    rw [hmul, mul_add, mul_left_comm p (p ^ a), mul_left_comm p r,
      mul_laurentEulerPolynomial_pow]
    simp only [nsmul_eq_mul]
    ring
  have hden : laurentEulerPolynomial e (p ^ (m + 1) * q) =
      p ^ m * ((m + 1) • (q * laurentEulerPolynomial e p) +
        p * laurentEulerPolynomial e q) := by
    rw [hmul, hpower, pow_succ]
    simp only [nsmul_eq_mul]
    ring
  have hfirst : (p ^ (m + 1) * q) * laurentEulerPolynomial e (p ^ a * r) =
      p ^ (m + a) * q *
        (p * laurentEulerPolynomial e r + a • (laurentEulerPolynomial e p * r)) := by
    calc
      _ = p ^ m * q * (p * laurentEulerPolynomial e (p ^ a * r)) := by rw [pow_succ]; ring
      _ = _ := by rw [hnum, pow_add]; ring
  rw [hfirst, hden, pow_add]
  simp only [nsmul_eq_mul]
  ring

/-- The exact residue after any product of Euler operators for an
arbitrary denominator with a distinguished prime power. The other
factors and the original numerator's partial cancellation are retained. -/
theorem exists_factor_laurentEulerNumerator_with_residue {R : Type*} [CommRing R]
    (φ : AddMonoidAlgebra ℂ G →+* R) (p q r : AddMonoidAlgebra ℂ G) (hp : φ p = 0)
    (m a : ℕ) (ha : a ≤ m + 1) (es : List (G →+ ℂ)) :
    ∃ w : AddMonoidAlgebra ℂ G,
      laurentEulerNumerator (p ^ (m + 1) * q) 1 (p ^ a * r) es =
        p ^ (m * es.length + a) * w ∧
      φ w = (-1 : R) ^ es.length * ((m + 1 - a).ascFactorial es.length : R) *
        (φ q) ^ es.length * (es.map (fun e => φ (laurentEulerPolynomial e p))).prod * φ r := by
  induction es with
  | nil => exact ⟨r, by simp [laurentEulerNumerator], by simp⟩
  | cons e es ih =>
    obtain ⟨w, hw, hres⟩ := ih
    let w' := p * q * laurentEulerPolynomial e w +
      (((m * es.length + a : ℕ) : AddMonoidAlgebra ℂ G) -
        ((es.length + 1 : ℕ) : AddMonoidAlgebra ℂ G) *
          ((m + 1 : ℕ) : AddMonoidAlgebra ℂ G)) * (q * laurentEulerPolynomial e p * w) -
      (es.length + 1) • (p * laurentEulerPolynomial e q * w)
    refine ⟨w', ?_, ?_⟩
    · rw [laurentEulerNumerator, hw, add_comm 1 es.length,
        laurentEulerNumerator_factor_step]
      have he : m + (m * es.length + a) = m * (e :: es).length + a := by
        rw [List.length_cons]
        ring
      rw [he]
    · have hscalar :
          ((m * es.length + a : ℕ) : R) - ((es.length + 1 : ℕ) : R) * ((m + 1 : ℕ) : R) =
            -((m + 1 - a + es.length : ℕ) : R) := by
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub ha, Nat.cast_one]
        ring
      simp only [w', nsmul_eq_mul, map_sub, map_add, map_mul, map_natCast, hp, zero_mul,
        zero_add, hscalar, hres, List.length_cons, Nat.ascFactorial_succ,
        Nat.cast_mul, List.map_cons, List.prod_cons, pow_succ]
      ring

end

end MeyerGeneralProblem
