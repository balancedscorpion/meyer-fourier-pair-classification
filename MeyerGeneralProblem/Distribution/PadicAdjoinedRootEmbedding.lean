module

public import MeyerGeneralProblem.Distribution.PadicIntegerPolynomialSpecialization
public import MeyerGeneralProblem.Distribution.PolynomialCommonDenominator
public import Mathlib.RingTheory.IsAdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-!
# Embedding a simple extension of the rational function field

The integral parameter map extends to the fraction field by algebraic
independence. Hensel's root gives the map of the simple extension.
The cleared representatives of the prescribed source elements yield
their integrality under the same map.
-/

namespace MeyerGeneralProblem

noncomputable section

open Polynomial
open scoped BigOperators

private theorem padicInt_eval_injective_of_algIndependent
    (p : ℕ) [Fact p.Prime] {n : ℕ} (t : Fin n → ℤ_[p])
    (ht : AlgebraicIndependent ℚ (fun i => (t i : ℚ_[p]))) :
    Function.Injective ((algebraMap ℤ_[p] ℚ_[p]).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom ℤ_[p]) t)) := by
  let v (i : Fin n) := (t i : ℚ_[p])
  let m := MvPolynomial.map (σ := Fin n) (Int.castRingHom ℚ)
  have hm : Function.Injective m := MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have he :
      (algebraMap ℤ_[p] ℚ_[p]).comp (MvPolynomial.eval₂Hom (Int.castRingHom ℤ_[p]) t) =
        (MvPolynomial.aeval (R := ℚ) v).toRingHom.comp m := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [m, PadicInt.algebraMap_apply]
    · intro i
      simp [m, v, MvPolynomial.eval₂Hom_X', PadicInt.algebraMap_apply]
  rw [he]
  exact (algebraicIndependent_iff_injective_aeval.mp ht).comp hm

private theorem eval_mapped_of_common_denominator
    {R F A C₀ : Type*} [CommRing R] [CommRing F] [CommRing A] [CommRing C₀]
    (a : R →+* F) (σ : R →+* A) (j : A →+* C₀) (e : F →+* C₀)
    (h : e.comp a = j.comp σ) (z : A) (D : R)
    (B : Polynomial R) (b : Polynomial F) (hB : B.map a = C (a D) * b) :
    j ((B.map σ).eval z) = (j.comp σ) D * b.eval₂ e (j z) := by
  rw [← Polynomial.eval_map_apply, Polynomial.map_map, ← h, ← Polynomial.map_map, hB,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C,
    ← Polynomial.eval₂_eq_eval_map, ← RingHom.comp_apply, h]

/-- Any simple separable extension of the fraction field of an integer
polynomial ring has a p-adic embedding integral on a given finite set. -/
theorem exists_padicIntegralEmbedding_of_adjoinRoot_over_rationalFunctions
    (n : ℕ) {F L : Type*} [Field F] [Field L]
    [Algebra (MvPolynomial (Fin n) ℤ) F] [IsFractionRing (MvPolynomial (Fin n) ℤ) F]
    [Algebra F L]
    {f : Polynomial F} (hf : f.Monic) (hfdeg : 0 < f.natDegree)
    (hcop : IsCoprime f f.derivative) (hL : IsAdjoinRoot L f) (S : Finset L) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (g : L →+* ℚ_[p]), ∀ s ∈ S, ‖g s‖ ≤ 1 := by
  classical
  obtain ⟨D, P, U, V, Q, hD, hcoef, hbez, hP, hQ⟩ :=
    exists_cleared_polynomial_and_derivative_identity (R := MvPolynomial (Fin n) ℤ) f hf hcop
      (fun s : S => hL.repr s.val)
  obtain ⟨p, hp, t, z, hti, hunit, hz, _⟩ :=
    exists_padicRoot_at_independent_parameters D hD P U V f.natDegree hfdeg hcoef hbez
  let _ := hp
  let σ := MvPolynomial.eval₂Hom (Int.castRingHom ℤ_[p]) t
  let j := algebraMap ℤ_[p] ℚ_[p]
  let h := j.comp σ
  have hinj : Function.Injective h := padicInt_eval_injective_of_algIndependent p t hti
  let e : F →+* ℚ_[p] := IsFractionRing.lift hinj
  let a := algebraMap (MvPolynomial (Fin n) ℤ) F
  have hcomp : e.comp a = j.comp σ := by
    apply RingHom.ext
    intro x
    change e (a x) = h x
    exact IsFractionRing.lift_algebraMap (K := F) hinj x
  have hnormD : ‖h D‖ = 1 := by
    exact (PadicInt.isUnit_iff.mp hunit : ‖σ D‖ = 1)
  have hDne : h D ≠ 0 := by
    intro hzero
    simp [hzero] at hnormD
  have hfzero : f.eval₂ e (j z) = 0 := by
    have hEq := eval_mapped_of_common_denominator a σ j e hcomp z D P f hP
    rw [hz, map_zero] at hEq
    exact (mul_eq_zero.mp hEq.symm).resolve_left hDne
  let g := hL.lift e (j z) hfzero
  refine ⟨p, hp, g, fun s hs => ?_⟩
  have hsMap : g s = (hL.repr s).eval₂ e (j z) := rfl
  have he := eval_mapped_of_common_denominator a σ j e hcomp z D
    (Q ⟨s, hs⟩) (hL.repr s) (hQ ⟨s, hs⟩)
  rw [← hsMap] at he
  have heNorm := congrArg (fun x : ℚ_[p] => ‖x‖) he
  rw [norm_mul, hnormD, one_mul] at heNorm
  rw [← heNorm]
  exact PadicInt.norm_le_one _

end
end MeyerGeneralProblem
