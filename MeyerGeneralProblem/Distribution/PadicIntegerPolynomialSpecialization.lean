module

public import MeyerGeneralProblem.Distribution.PadicTranscendentalResidues
public import MeyerGeneralProblem.Distribution.PadicSimpleRootSelection
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# P-adic specialization of an integral polynomial with parameters

A nonzero denominator is kept nonzero at the integer specialization.
The cleared Bézout identity then permits a prime with a simple root
and with that denominator invertible. Moving the parameters within
their residue classes preserves both facts for Hensel lifting.
-/

namespace MeyerGeneralProblem

noncomputable section

open Polynomial

private theorem exists_nonzero_int_multipoly_eval {n : ℕ} (D : MvPolynomial (Fin n) ℤ)
    (hD : D ≠ 0) : ∃ a : Fin n → ℤ, MvPolynomial.eval a D ≠ 0 := by
  by_contra! h
  apply hD
  apply MvPolynomial.funext
  intro a
  rw [map_zero, h a]

private theorem padic_toZMod_eq_zero_iff_norm_lt_one (p : ℕ) [Fact p.Prime] (u : ℤ_[p]) :
    PadicInt.toZMod u = 0 ↔ ‖u‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton, PadicInt.norm_lt_one_iff_dvd]

private theorem reduce_multipoly_eval_of_lifts (p : ℕ) [Fact p.Prime]
    {n : ℕ} (a : Fin n → ℤ) (t : Fin n → ℤ_[p])
    (ht : ∀ i, PadicInt.toZMod (t i) = (a i : ZMod p)) :
    (PadicInt.toZMod : ℤ_[p] →+* ZMod p).comp
        (MvPolynomial.eval₂Hom (Int.castRingHom ℤ_[p]) t) =
      (Int.castRingHom (ZMod p)).comp (MvPolynomial.eval a) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp
  · intro i
    simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X,
      Int.coe_castRingHom] using ht i

/-- The algebraically independent p-adic parameter specialization has a
lifted root, with the cleared denominator and derivative both units. -/
theorem exists_padicRoot_at_independent_parameters {n : ℕ}
    (D : MvPolynomial (Fin n) ℤ) (hD : D ≠ 0)
    (P U V : Polynomial (MvPolynomial (Fin n) ℤ))
    (k : ℕ) (hk : 0 < k) (hcoeff : P.coeff k = D)
    (hbez : U * P + V * P.derivative = C (D ^ 2)) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (t : Fin n → ℤ_[p]) (z : ℤ_[p]),
      let σ := MvPolynomial.eval₂Hom (Int.castRingHom ℤ_[p]) t
      AlgebraicIndependent ℚ (fun i => (t i : ℚ_[p])) ∧
        IsUnit (σ D) ∧ (P.map σ).eval z = 0 ∧ ‖(P.map σ).derivative.eval z‖ = 1 := by
  classical
  obtain ⟨a, ha⟩ := exists_nonzero_int_multipoly_eval D hD
  let ρ := MvPolynomial.eval a
  let Q := P.map ρ
  have hQcoeff : Q.coeff k ≠ 0 := by
    rw [show Q = P.map ρ from rfl, coeff_map, hcoeff]
    exact ha
  have hQ : 0 < Q.natDegree := hk.trans_le (le_natDegree_of_ne_zero hQcoeff)
  have hQbez : U.map ρ * Q + V.map ρ * Q.derivative = C (ρ (D ^ 2)) := by
    have h := congrArg (fun f : Polynomial (MvPolynomial (Fin n) ℤ) => f.map ρ) hbez
    simpa only [Q, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.derivative_map] using h
  have hQconstant : ρ (D ^ 2) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ ha
  let S := Finset.range ((ρ D).natAbs + 1)
  obtain ⟨p, b, hp, hpS, hQb, hQ'b⟩ :=
    exists_prime_not_mem_dvd_eval_not_dvd_derivative Q hQ S
      (U.map ρ) (V.map ρ) (ρ (D ^ 2)) hQconstant hQbez
  let prime : Fact p.Prime := ⟨hp⟩
  let _ := prime
  have hpD : ¬ (p : ℤ) ∣ ρ D := by
    intro h
    have hpNat : p ∣ (ρ D).natAbs := by
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr h
    exact hpS (Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.le_of_dvd (Int.natAbs_pos.mpr ha) hpNat)))
  obtain ⟨t, hti, ht⟩ := exists_algebraicIndependent_padicInt_lifts p n a
  let σ := MvPolynomial.eval₂Hom (Int.castRingHom ℤ_[p]) t
  let π : ℤ_[p] →+* ZMod p := PadicInt.toZMod
  let j : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hcompat : π.comp σ = j.comp ρ := reduce_multipoly_eval_of_lifts p a t ht
  have hred (W : Polynomial (MvPolynomial (Fin n) ℤ)) :
      π ((W.map σ).eval (b : ℤ_[p])) = ((W.map ρ).eval b : ℤ) := by
    change π ((W.map σ).eval (b : ℤ_[p])) = j ((W.map ρ).eval b)
    rw [← Polynomial.eval_map_apply, Polynomial.map_map, hcompat,
      ← Polynomial.map_map]
    rw [show π (b : ℤ_[p]) = j b from map_intCast π b]
    exact Polynomial.eval_map_apply (p := W.map ρ) j b
  have hredD : π (σ D) = j (ρ D) := DFunLike.congr_fun hcompat D
  have hunit : IsUnit (σ D) := by
    apply PadicInt.isUnit_iff.mpr
    apply le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt ?_)
    intro hn
    have h := (padic_toZMod_eq_zero_iff_norm_lt_one p _).mpr hn
    change π (σ D) = 0 at h
    rw [hredD] at h
    exact hpD ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
  let B := P.map σ
  have hsmall : ‖B.eval (b : ℤ_[p])‖ < 1 := by
    apply (padic_toZMod_eq_zero_iff_norm_lt_one p _).mp
    change π ((P.map σ).eval (b : ℤ_[p])) = 0
    rw [hred P, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hQb
  have hderivUnit : ‖B.derivative.eval (b : ℤ_[p])‖ = 1 := by
    apply le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt ?_)
    intro hn
    have h := (padic_toZMod_eq_zero_iff_norm_lt_one p _).mpr hn
    change π ((P.map σ).derivative.eval (b : ℤ_[p])) = 0 at h
    rw [derivative_map, hred P.derivative, ← derivative_map,
      ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    exact hQ'b h
  have hnorm : ‖B.aeval (b : ℤ_[p])‖ < ‖B.derivative.aeval (b : ℤ_[p])‖ ^ 2 := by
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
      hderivUnit, one_pow] using hsmall
  obtain ⟨z, hz, _, hdz, _⟩ := hensels_lemma hnorm
  refine ⟨p, prime, t, z, hti, hunit, ?_, ?_⟩
  · simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using hz
  · rw [← hderivUnit]
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using hdz

end
end MeyerGeneralProblem
