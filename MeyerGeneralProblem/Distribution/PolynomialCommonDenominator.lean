module

public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Integral polynomial data from a fraction-field presentation

One denominator clears the finite family of polynomials at once.
Clearing a Bézout identity with the derivative produces an integral
identity with the square of that same denominator.
-/

namespace MeyerGeneralProblem

noncomputable section

open Polynomial
open scoped BigOperators

section Fraction
variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

/-- A finite family of univariate polynomials over a fraction field admits
one nonzero denominator for all its coefficients. -/
theorem exists_common_denominator_polynomial_family
    {ι : Type*} [Fintype ι] (f : ι → Polynomial F) :
    ∃ (D : R) (Q : ι → Polynomial R), D ≠ 0 ∧
      ∀ i, (Q i).map (algebraMap R F) = C (algebraMap R F D) * f i := by
  classical
  let J := Finset.univ.biUnion (fun i : ι => (f i).support.image (fun n => (i, n)))
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) J
    (fun p : ι × ℕ => (f p.1).coeff p.2)
  have hLift (i : ι) : ∃ q : Polynomial R,
      q.map (algebraMap R F) = C (algebraMap R F (d : R)) * f i := by
    apply (Polynomial.lifts_iff_set_range _).mp
    apply (Polynomial.lifts_iff_coeff_lifts _).mpr
    intro n
    rw [Polynomial.coeff_C_mul]
    by_cases hn : n ∈ (f i).support
    · have hJ : (i, n) ∈ J := Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ hn⟩
      simpa only [Algebra.smul_def, IsLocalization.IsInteger, RingHom.mem_rangeS,
        Set.mem_range] using
        hd (i, n) hJ
    · rw [Polynomial.notMem_support_iff.mp hn, mul_zero]
      exact ⟨0, map_zero _⟩
  choose Q hQ using hLift
  exact ⟨d, Q, nonZeroDivisors.ne_zero d.property, hQ⟩

/-- A monic polynomial, its Bézout identity, and all the source
representatives can be cleared by the same denominator. -/
theorem exists_cleared_polynomial_and_derivative_identity
    {ι : Type*} [Fintype ι] (f : Polynomial F) (hf : f.Monic)
    (hcop : IsCoprime f f.derivative) (s : ι → Polynomial F) :
    ∃ (D : R) (P U V : Polynomial R) (Q : ι → Polynomial R),
      D ≠ 0 ∧ P.coeff f.natDegree = D ∧
        U * P + V * P.derivative = C (D ^ 2) ∧
        P.map (algebraMap R F) = C (algebraMap R F D) * f ∧
        ∀ i, (Q i).map (algebraMap R F) = C (algebraMap R F D) * s i := by
  obtain ⟨u, v, huv⟩ := hcop
  let a : ι ⊕ Fin 3 → Polynomial F := Sum.elim s ![f, u, v]
  obtain ⟨D, q, hD, hq⟩ := exists_common_denominator_polynomial_family (R := R) a
  let P := q (.inr 0)
  let U := q (.inr 1)
  let V := q (.inr 2)
  let m := algebraMap R F
  have hP : P.map m = C (m D) * f := hq (.inr 0)
  have hU : U.map m = C (m D) * u := hq (.inr 1)
  have hV : V.map m = C (m D) * v := hq (.inr 2)
  have hinj : Function.Injective m := IsFractionRing.injective R F
  refine ⟨D, P, U, V, fun i => q (.inl i), hD, ?_, ?_, hP, fun i => hq (.inl i)⟩
  · apply hinj
    rw [← Polynomial.coeff_map, hP, Polynomial.coeff_C_mul, hf.coeff_natDegree, mul_one]
  · apply Polynomial.map_injective _ hinj
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      ← Polynomial.derivative_map, hP, hU, hV, Polynomial.derivative_C_mul, Polynomial.map_C,
      map_pow]
    calc
      _ = (C (m D)) ^ 2 * (u * f + v * f.derivative) := by ring
      _ = _ := by rw [huv, mul_one, map_pow]

end Fraction

end
end MeyerGeneralProblem
