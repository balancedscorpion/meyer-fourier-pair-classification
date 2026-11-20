module

public import MeyerGeneralProblem.Distribution.PolynomialPrimeDivisors
public import Mathlib.NumberTheory.Padics.Hensel

@[expose] public section

/-!
# Choosing a prime and lifting a simple polynomial root

A finite prime exclusion set and a cleared Bézout identity give one
prime with a simple root modulo that prime. Hensel lifting supplies
the original polynomial's root in the p-adic integers.
-/

namespace MeyerGeneralProblem

noncomputable section

open Polynomial

/-- A nonconstant integer polynomial with a cleared Bézout identity
against its derivative has a simple p-adic integer root for a prime
outside any given finite set. -/
theorem exists_padicSimpleRoot_not_mem_of_intPolynomial_bezout
    (P : Polynomial ℤ) (hP : 0 < P.natDegree) (S : Finset ℕ)
    (A B : Polynomial ℤ) (c : ℤ) (hc : c ≠ 0)
    (hbez : A * P + B * P.derivative = C c) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (z : ℤ_[p]), p ∉ S ∧
      P.aeval z = 0 ∧ ‖P.derivative.aeval z‖ = 1 := by
  obtain ⟨p, n, hp, hnot, hdiv, hderiv⟩ :=
    exists_prime_not_mem_dvd_eval_not_dvd_derivative P hP S A B c hc hbez
  let hprime : Fact p.Prime := ⟨hp⟩
  let _ := hprime
  have heval (Q : Polynomial ℤ) :
      Q.aeval (n : ℤ_[p]) = ((Q.eval n : ℤ) : ℤ_[p]) := by
    rw [aeval_def]
    exact eval₂_at_apply (p := Q) (Int.castRingHom ℤ_[p]) n
  have hsmall : ‖P.aeval (n : ℤ_[p])‖ < 1 := by
    rw [heval P, PadicInt.norm_intCast_lt_one_iff]
    exact hdiv
  have hunit : ‖P.derivative.aeval (n : ℤ_[p])‖ = 1 := by
    apply le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt ?_)
    rw [heval P.derivative, PadicInt.norm_intCast_lt_one_iff]
    exact hderiv
  have hnorm : ‖P.aeval (n : ℤ_[p])‖ < ‖P.derivative.aeval (n : ℤ_[p])‖ ^ 2 := by
    simpa only [hunit, one_pow] using hsmall
  obtain ⟨z, hz, _, hdz, _⟩ := hensels_lemma hnorm
  exact ⟨p, hprime, z, hnot, hz, hdz.trans hunit⟩

end
end MeyerGeneralProblem
