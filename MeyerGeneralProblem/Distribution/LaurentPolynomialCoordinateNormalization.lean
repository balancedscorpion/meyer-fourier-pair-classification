module

public import MeyerGeneralProblem.Distribution.ComplexLaurentPhase
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

/-!
# Ordinary polynomial coordinates in the original Laurent algebra

An integral basis embeds the nonnegative exponent monoid into the
original frequency module. Multiplication by one original Laurent
monomial clears all negative exponents, with exact evaluation on the
nonzero coordinate torus.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set

variable {G ι : Type*} [AddCommGroup G]

/-- The original label with the indicated nonnegative integral coordinates. -/
def basisNaturalExponent (b : Module.Basis ι ℤ G) : (ι →₀ ℕ) →+ G where
  toFun e := b.repr.symm (e.mapRange (fun n : ℕ => (n : ℤ)) (by simp))
  map_zero' := by simp
  map_add' e f := by
    rw [← map_add]
    congr 1
    ext i
    simp

@[simp]
theorem basisNaturalExponent_repr (b : Module.Basis ι ℤ G)
    (e : ι →₀ ℕ) (i : ι) : b.repr (basisNaturalExponent b e) i = (e i : ℤ) := by
  simp [basisNaturalExponent]

theorem basisNaturalExponent_injective (b : Module.Basis ι ℤ G) :
    Function.Injective (basisNaturalExponent b) := by
  intro e f h
  ext i
  have hi := congrArg (fun g : G => b.repr g i) h
  simpa only [basisNaturalExponent_repr, Nat.cast_inj] using hi

/-- Embed ordinary polynomials into the exact original Laurent algebra. -/
def basisPolynomialEmbedding (b : Module.Basis ι ℤ G) :
    MvPolynomial ι ℂ →ₐ[ℂ] AddMonoidAlgebra ℂ G :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (basisNaturalExponent b)

theorem basisPolynomialEmbedding_injective (b : Module.Basis ι ℤ G) :
    Function.Injective (basisPolynomialEmbedding b) :=
  AddMonoidAlgebra.mapDomain_injective (basisNaturalExponent_injective b)

@[simp]
theorem basisPolynomialEmbedding_monomial (b : Module.Basis ι ℤ G)
    (e : ι →₀ ℕ) (a : ℂ) :
    basisPolynomialEmbedding b (MvPolynomial.monomial e a) =
      AddMonoidAlgebra.single (basisNaturalExponent b e) a :=
  AddMonoidAlgebra.mapDomain_single

variable [Fintype ι]

@[simp]
theorem basisLaurentEvaluation_single (b : Module.Basis ι ℤ G) (v : ι → ℂˣ)
    (m : G) (a : ℂ) :
    basisLaurentEvaluation b v (AddMonoidAlgebra.single m a) =
      a * ∏ i, (v i : ℂ) ^ (b.repr m i) := by
  unfold basisLaurentEvaluation
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  rfl

/-- Ordinary polynomial evaluation is exact at the nonzero coordinates
of the original Laurent evaluation. -/
theorem basisPolynomialEmbedding_eval (b : Module.Basis ι ℤ G)
    (v : ι → ℂˣ) (P : MvPolynomial ι ℂ) :
    basisLaurentEvaluation b v (basisPolynomialEmbedding b P) =
      MvPolynomial.eval (fun i => (v i : ℂ)) P := by
  refine AddMonoidAlgebra.induction_linear P ?_ ?_ ?_
  · simp
  · intro P Q hp hq
    simp only [map_add, hp, hq]
  · intro e a
    change basisLaurentEvaluation b v (basisPolynomialEmbedding b (MvPolynomial.monomial e a)) =
      MvPolynomial.eval (fun i => (v i : ℂ)) (MvPolynomial.monomial e a)
    rw [basisPolynomialEmbedding_monomial, basisLaurentEvaluation_single,
      MvPolynomial.eval_monomial]
    simp only [basisNaturalExponent_repr, zpow_natCast]
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero (v i : ℂ))]

/-- A monomial of the original module clears every negative exponent
of any finite Laurent polynomial. -/
theorem exists_basisLaurent_polynomial_normalization (b : Module.Basis ι ℤ G)
    (p : AddMonoidAlgebra ℂ G) :
    ∃ g : G, ∃ P : MvPolynomial ι ℂ,
      basisPolynomialEmbedding b P = AddMonoidAlgebra.single g 1 * p := by
  classical
  let d (i : ι) : ℕ := ∑ m ∈ p.coeff.support, (-(b.repr m i)).toNat
  let g := b.equivFun.symm (fun i => (d i : ℤ))
  have hg (i : ι) : b.repr g i = (d i : ℤ) := by
    simpa only [g, Module.Basis.equivFun_apply] using
      congrFun (b.equivFun.apply_symm_apply fun i => (d i : ℤ)) i
  have hn (m : G) (hm : m ∈ p.coeff.support) (i : ι) :
      0 ≤ b.repr (g + m) i := by
    have ht : (-(b.repr m i)).toNat ≤ d i :=
      Finset.single_le_sum (fun m _ => Nat.zero_le ((-(b.repr m i)).toNat)) hm
    have ht' : (((-(b.repr m i)).toNat : ℕ) : ℤ) ≤ (d i : ℤ) := by exact_mod_cast ht
    rw [map_add, Finsupp.add_apply, hg]
    omega
  let e (m : G) : ι →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => (b.repr (g + m) i).toNat)
  have he (m : G) (hm : m ∈ p.coeff.support) : basisNaturalExponent b (e m) = g + m := by
    apply b.repr.injective
    ext i
    rw [basisNaturalExponent_repr]
    change (((b.repr (g + m) i).toNat : ℕ) : ℤ) = _
    exact Int.toNat_of_nonneg (hn m hm i)
  refine ⟨g, ∑ m ∈ p.coeff.support, MvPolynomial.monomial (e m) (p.coeff m), ?_⟩
  rw [map_sum]
  conv_rhs =>
    rhs
    rw [← AddMonoidAlgebra.sum_coeff_single p]
  rw [Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [basisPolynomialEmbedding_monomial, he m hm, AddMonoidAlgebra.single_mul_single, one_mul]

/-- Clearing negative exponents adds no zeros at nonzero coordinates. -/
theorem basisPolynomialNormalization_eval_eq_zero_iff
    (b : Module.Basis ι ℤ G) (v : ι → ℂˣ) (p : AddMonoidAlgebra ℂ G)
    (g : G) (P : MvPolynomial ι ℂ)
    (h : basisPolynomialEmbedding b P = AddMonoidAlgebra.single g 1 * p) :
    MvPolynomial.eval (fun i => (v i : ℂ)) P = 0 ↔ basisLaurentEvaluation b v p = 0 := by
  rw [← basisPolynomialEmbedding_eval b, h, map_mul, basisLaurentEvaluation_single, one_mul]
  have hne : (∏ i, (v i : ℂ) ^ (b.repr g i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (Units.ne_zero _)
  exact mul_eq_zero_iff_left hne

end

end MeyerGeneralProblem
