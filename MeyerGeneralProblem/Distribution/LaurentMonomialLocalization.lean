module

public import MeyerGeneralProblem.Distribution.LaurentPolynomialCoordinateNormalization
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

@[expose] public section

/-!
# Finite-rank Laurent factorization in the original exponent group

The existing ordinary polynomial coordinates identify the original
Laurent algebra as the localization at coefficient-one monomials.
Ordinary polynomial factorization then gives prime factorization in
that same Laurent algebra.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set

variable {G ι : Type*} [AddCommGroup G]

/-- The coefficient-one ordinary monomials used as denominators. -/
def polynomialMonomialSubmonoid (ι : Type*) : Submonoid (MvPolynomial ι ℂ) where
  carrier := range fun e : ι →₀ ℕ => MvPolynomial.monomial e (1 : ℂ)
  one_mem' := ⟨0, by simp [MvPolynomial.monomial_zero']⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by rw [MvPolynomial.monomial_mul_monomial, one_mul]⟩

private theorem polynomialMonomialSubmonoid_le_nonZeroDivisors (ι : Type*) :
    polynomialMonomialSubmonoid ι ≤ nonZeroDivisors (MvPolynomial ι ℂ) := by
  classical
  rintro _ ⟨a, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (by
    intro h
    have he := congrArg (MvPolynomial.coeff a) h
    simp [MvPolynomial.coeff_monomial] at he)

/-- A nonzero Laurent monomial is a unit, with inverse at the opposite
exponent in the original group. -/
theorem isUnit_laurentSingle (m : G) (c : ℂ) (hc : c ≠ 0) :
    IsUnit (AddMonoidAlgebra.single m c) := by
  have h : AddMonoidAlgebra.single m c * AddMonoidAlgebra.single (-m) c⁻¹ = 1 := by
    simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def, hc]
  exact ⟨Units.mkOfMulEqOne _ _ h, rfl⟩

/-- A coefficient-one Laurent monomial is a unit in the exact
original group ring. -/
theorem isUnit_laurentMonomial (m : G) :
    IsUnit (AddMonoidAlgebra.single m (1 : ℂ)) :=
  isUnit_laurentSingle m 1 one_ne_zero

private theorem exists_basisNaturalExponent_sub (b : Module.Basis ι ℤ G) (m : G) :
    ∃ a c : ι →₀ ℕ, m = basisNaturalExponent b a - basisNaturalExponent b c := by
  let a := (b.repr m).mapRange Int.toNat rfl
  let c := (-b.repr m).mapRange Int.toNat rfl
  refine ⟨a, c, b.repr.injective ?_⟩
  ext i
  simp only [map_sub, Finsupp.sub_apply, basisNaturalExponent_repr, a, c,
    Finsupp.mapRange_apply, Finsupp.neg_apply]
  omega

/-- Ordinary polynomial coordinates localize to the full original
Laurent algebra at the monomial submonoid. -/
theorem basisLaurent_isLocalization [Fintype ι] (b : Module.Basis ι ℤ G) :
    let _ : Algebra (MvPolynomial ι ℂ) (AddMonoidAlgebra ℂ G) :=
      (basisPolynomialEmbedding b).toRingHom.toAlgebra
    IsLocalization (polynomialMonomialSubmonoid ι) (AddMonoidAlgebra ℂ G) := by
  let _ : Algebra (MvPolynomial ι ℂ) (AddMonoidAlgebra ℂ G) :=
    (basisPolynomialEmbedding b).toRingHom.toAlgebra
  apply (isLocalization_iff (polynomialMonomialSubmonoid ι) (AddMonoidAlgebra ℂ G)).mpr
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨P, ⟨a, rfl⟩⟩
    change IsUnit (basisPolynomialEmbedding b (MvPolynomial.monomial a 1))
    rw [basisPolynomialEmbedding_monomial]
    exact isUnit_laurentMonomial _
  · intro p
    obtain ⟨g, P, hP⟩ := exists_basisLaurent_polynomial_normalization b p
    obtain ⟨a, c, hg⟩ := exists_basisNaturalExponent_sub b g
    have he : basisNaturalExponent b c + g = basisNaturalExponent b a := by
      rw [hg]
      abel
    refine ⟨⟨MvPolynomial.monomial c 1 * P, ⟨MvPolynomial.monomial a 1, ⟨a, rfl⟩⟩⟩, ?_⟩
    change p * basisPolynomialEmbedding b (MvPolynomial.monomial a 1) =
      basisPolynomialEmbedding b (MvPolynomial.monomial c 1 * P)
    rw [map_mul, hP, basisPolynomialEmbedding_monomial, basisPolynomialEmbedding_monomial,
      ← mul_assoc, AddMonoidAlgebra.single_mul_single, one_mul, he, mul_comm]
  · intro x y h
    change basisPolynomialEmbedding b x = basisPolynomialEmbedding b y at h
    rw [basisPolynomialEmbedding_injective b h]
    exact ⟨1, rfl⟩

private theorem localized_prime_or_unit {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (hM : M ≤ nonZeroDivisors R) (p : R) (hp : Prime p) :
    IsUnit (algebraMap R S p) ∨ Prime (algebraMap R S p) := by
  by_cases hu : IsUnit (algebraMap R S p)
  · exact Or.inl hu
  · right
    have hd : Disjoint (M : Set R) (Ideal.span ({p} : Set R) : Set R) := by
      apply Set.disjoint_left.mpr
      intro x hx hxp
      exact hu (isUnit_of_dvd_unit
        (map_dvd (algebraMap R S) (Ideal.mem_span_singleton.mp hxp))
        (IsLocalization.map_units S ⟨x, hx⟩))
    have hn : algebraMap R S p ≠ 0 := by
      intro he
      exact hp.ne_zero (IsLocalization.injective S hM (he.trans (map_zero _).symm))
    apply (Ideal.span_singleton_prime hn).mp
    have hi := IsLocalization.isPrime_of_isPrime_disjoint M S
      (Ideal.span ({p} : Set R)) (Ideal.isPrime_span_singleton_of_prime hp) hd
    simpa only [Ideal.map_span, Set.image_singleton] using hi

private theorem exists_prime_multiset_of_prime_or_unit {S : Type*} [CommMonoidWithZero S]
    (f : Multiset S) (h : ∀ x ∈ f, IsUnit x ∨ Prime x) :
    ∃ g : Multiset S, (∀ x ∈ g, Prime x) ∧ Associated g.prod f.prod := by
  induction f using Multiset.induction_on with
  | empty => exact ⟨0, by simp, Associated.rfl⟩
  | cons a f ih =>
    obtain ⟨g, hprime, hg⟩ := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    rcases h a (Multiset.mem_cons_self _ _) with ha | ha
    · refine ⟨g, hprime, ?_⟩
      rw [Multiset.prod_cons]
      exact hg.trans (associated_unit_mul_right f.prod a ha)
    · refine ⟨a ::ₘ g, ?_, ?_⟩
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hprime x hx
      · simpa only [Multiset.prod_cons] using hg.mul_left a

private theorem localization_uniqueFactorizationMonoid {R S : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) :
    UniqueFactorizationMonoid S := by
  let _ : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  apply UniqueFactorizationMonoid.iff_exists_prime_factors.mpr
  intro x hx
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj M x
  have hunit := IsLocalization.map_units S s
  have hn : r ≠ 0 := by
    intro hr
    exact mul_ne_zero hx hunit.ne_zero (by simpa [hr] using h)
  obtain ⟨f, hprime, hprod⟩ := UniqueFactorizationMonoid.exists_prime_factors r hn
  have hor (p : S) (hp : p ∈ f.map (algebraMap R S)) : IsUnit p ∨ Prime p := by
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact localized_prime_or_unit M hM q (hprime q hq)
  obtain ⟨g, hg, hgprod⟩ := exists_prime_multiset_of_prime_or_unit _ hor
  have hprod' : Associated (f.map (algebraMap R S)).prod (algebraMap R S r) := by
    rw [← map_multiset_prod]
    exact Associated.map (algebraMap R S) hprod
  have hunit' : Associated (algebraMap R S r) x := by
    rw [← h]
    exact associated_mul_unit_left x _ hunit
  exact ⟨g, hg, hgprod.trans (hprod'.trans hunit')⟩

/-- The finite-rank original Laurent algebra is an integral domain. -/
theorem basisLaurent_isDomain [Fintype ι] (b : Module.Basis ι ℤ G) :
    IsDomain (AddMonoidAlgebra ℂ G) := by
  let _ : Algebra (MvPolynomial ι ℂ) (AddMonoidAlgebra ℂ G) :=
    (basisPolynomialEmbedding b).toRingHom.toAlgebra
  let _ : IsLocalization (polynomialMonomialSubmonoid ι) (AddMonoidAlgebra ℂ G) :=
    basisLaurent_isLocalization b
  exact IsLocalization.isDomain_of_le_nonZeroDivisors _
    (polynomialMonomialSubmonoid_le_nonZeroDivisors ι)

/-- The original finite-rank Laurent algebra has unique prime factorization. -/
theorem basisLaurent_uniqueFactorizationMonoid [Fintype ι] (b : Module.Basis ι ℤ G) :
    UniqueFactorizationMonoid (AddMonoidAlgebra ℂ G) := by
  let _ : Algebra (MvPolynomial ι ℂ) (AddMonoidAlgebra ℂ G) :=
    (basisPolynomialEmbedding b).toRingHom.toAlgebra
  let _ : IsLocalization (polynomialMonomialSubmonoid ι) (AddMonoidAlgebra ℂ G) :=
    basisLaurent_isLocalization b
  exact localization_uniqueFactorizationMonoid _
    (polynomialMonomialSubmonoid_le_nonZeroDivisors ι)

end

end MeyerGeneralProblem
