module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Schur's prime-divisor theorem for integer polynomials

For a given finite prime exclusion set, vary the argument in a
progression on which a normalized value is congruent to one modulo
their product. The polynomial's growth supplies a new prime divisor.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Polynomial
open scoped Topology BigOperators

private theorem exists_int_eval_abs_gt (P : Polynomial ℤ) (hP : 0 < P.natDegree)
    (B : ℝ) : ∃ n : ℤ, B < |((P.eval n : ℤ) : ℝ)| := by
  let Q := P.map (Int.castRingHom ℝ)
  have hQ : 0 < Q.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (by
    rw [show Q = P.map (Int.castRingHom ℝ) from rfl,
      Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    exact hP)
  obtain ⟨a, ha⟩ := eventually_atTop.mp
    (Q.abs_tendsto_atTop hQ (eventually_gt_atTop B))
  obtain ⟨n, hn⟩ := exists_nat_gt a
  refine ⟨(n : ℤ), ?_⟩
  have he := ha n hn.le
  change B < |Q.eval (n : ℝ)| at he
  have hmap : Q.eval (((n : ℤ) : ℝ)) = ((P.eval (n : ℤ) : ℤ) : ℝ) := by
    change Q.eval ((Int.castRingHom ℝ) (n : ℤ)) = (Int.castRingHom ℝ) (P.eval (n : ℤ))
    exact Polynomial.eval_map_apply (p := P) (Int.castRingHom ℝ) (n : ℤ)
  simpa only [Int.cast_natCast, ← hmap] using he

/-- A nonconstant integer polynomial has a nonzero value divisible by
a prime outside any prescribed finite set. -/
theorem exists_prime_not_mem_dvd_nonzero_intPolynomial_eval
    (P : Polynomial ℤ) (hP : 0 < P.natDegree) (S : Finset ℕ) :
    ∃ (p : ℕ) (n : ℤ), p.Prime ∧ p ∉ S ∧ P.eval n ≠ 0 ∧ (p : ℤ) ∣ P.eval n := by
  classical
  obtain ⟨a, ha⟩ := exists_int_eval_abs_gt P hP 0
  let A := P.eval a
  have hA : A ≠ 0 := by
    change P.eval a ≠ 0
    intro h
    simp [h] at ha
  let f (p : ℕ) : ℤ := if p.Prime then (p : ℤ) else 1
  let M := ∏ p ∈ S, f p
  have hM : 0 < M := by
    apply Finset.prod_pos
    intro p _
    by_cases hp : p.Prime
    · simpa [f, hp] using hp.pos
    · simp [f, hp]
  let d := A * M
  have hd : d ≠ 0 := mul_ne_zero hA hM.ne'
  let Q := P.comp (C d * X + C a)
  have hQ : 0 < Q.natDegree := by
    unfold Q
    rw [Polynomial.natDegree_comp]
    have hL : (C d * X + C a).natDegree = 1 := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_C_mul_X d hd
      · rw [Polynomial.natDegree_C_mul_X d hd, Polynomial.natDegree_C]
        decide
    rwa [hL, mul_one]
  obtain ⟨k, hk⟩ := exists_int_eval_abs_gt Q hQ |(A : ℝ)|
  let n := a + d * k
  have hQeval : Q.eval k = P.eval n := by
    simp [Q, n, Polynomial.eval_comp, add_comm]
  have hgrow : |(A : ℝ)| < |((P.eval n : ℤ) : ℝ)| := by rwa [hQeval] at hk
  have hn : P.eval n ≠ 0 := by
    intro h
    rw [h, Int.cast_zero, abs_zero] at hgrow
    exact (not_lt_of_ge (abs_nonneg _)) hgrow
  have hdiv : d ∣ P.eval n - P.eval a := by
    apply dvd_trans ?_ (Polynomial.sub_dvd_eval_sub n a P)
    exact ⟨k, by unfold n; ring⟩
  obtain ⟨t, ht⟩ := hdiv
  let b := 1 + M * t
  have hvalue : P.eval n = A * b := by
    change P.eval n - A = (A * M) * t at ht
    dsimp [b]
    linear_combination ht
  have hb : 1 < b.natAbs := by
    rw [hvalue, Int.cast_mul, abs_mul] at hgrow
    have hApos : 0 < |(A : ℝ)| := abs_pos.mpr (by exact_mod_cast hA)
    have hreal : (1 : ℝ) < |(b : ℝ)| :=
      (lt_of_mul_lt_mul_left (by simpa only [mul_one] using hgrow) hApos.le)
    rw [← Int.cast_abs, ← Nat.cast_natAbs] at hreal
    exact_mod_cast hreal
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hb)
  have hp' : (p : ℤ) ∣ b := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa only [Int.natAbs_natCast] using hpd
  have hnot : p ∉ S := by
    intro hmem
    have hpM : (p : ℤ) ∣ M := by
      simpa [f, hp] using Finset.dvd_prod_of_mem f hmem
    have hdvd : (p : ℤ) ∣ 1 := by
      have h := dvd_sub hp' (dvd_mul_of_dvd_left hpM t)
      simpa only [b, add_sub_cancel_right] using h
    have hnat : p ∣ 1 := by
      exact_mod_cast hdvd
    exact hp.ne_one (Nat.dvd_one.mp hnat)
  refine ⟨p, n, hp, hnot, hn, ?_⟩
  rw [hvalue]
  exact dvd_mul_of_dvd_right hp' A

/-- A cleared Bézout identity with the derivative allows the new prime
to be chosen with a simple root modulo that prime. -/
theorem exists_prime_not_mem_dvd_eval_not_dvd_derivative
    (P : Polynomial ℤ) (hP : 0 < P.natDegree) (S : Finset ℕ)
    (A B : Polynomial ℤ) (c : ℤ) (hc : c ≠ 0)
    (hbez : A * P + B * P.derivative = C c) :
    ∃ (p : ℕ) (n : ℤ), p.Prime ∧ p ∉ S ∧
      (p : ℤ) ∣ P.eval n ∧ ¬ (p : ℤ) ∣ P.derivative.eval n := by
  classical
  let T := S ∪ Finset.range (c.natAbs + 1)
  obtain ⟨p, n, hp, hnot, _, hdp⟩ := exists_prime_not_mem_dvd_nonzero_intPolynomial_eval P hP T
  refine ⟨p, n, hp, fun hs => hnot (Finset.mem_union_left _ hs), hdp, ?_⟩
  intro hdd
  have he : A.eval n * P.eval n + B.eval n * P.derivative.eval n = c := by
    have h := congrArg (fun Q : Polynomial ℤ => Q.eval n) hbez
    simpa only [eval_mul, eval_add, eval_C] using h
  have hdc : (p : ℤ) ∣ c := he ▸ dvd_add
    (dvd_mul_of_dvd_right hdp (A.eval n)) (dvd_mul_of_dvd_right hdd (B.eval n))
  have hpn : p ∣ c.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdc
  have hple := Nat.le_of_dvd (Int.natAbs_pos.mpr hc) hpn
  exact hnot (Finset.mem_union_right _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hple)))

end
end MeyerGeneralProblem
