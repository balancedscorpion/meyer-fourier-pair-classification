module

public import MeyerGeneralProblem.Distribution.LaurentSupportLine
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

/-!
# Rank-one Laurent factors and univariate splitting

An affine cyclic support stays in the original exponent group while a
monomial shift turns it into an ordinary univariate polynomial. Over
the complex numbers an irreducible nonunit can retain only one
nonunit linear factor.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {G ι : Type*} [AddCommGroup G]

/-- The literal binomial with constant term minus c. -/
def laurentBinomial (d : G) (c : ℂ) : AddMonoidAlgebra ℂ G :=
  AddMonoidAlgebra.single d 1 - AddMonoidAlgebra.single 0 c

private theorem laurent_isUnit_of_singleton_support
    (p : AddMonoidAlgebra ℂ G) (hp : p ≠ 0) (a : G)
    (h : ∀ n ∈ p.coeff.support, n = a) : IsUnit p := by
  classical
  have he : p = AddMonoidAlgebra.single a (p.coeff a) := by
    apply AddMonoidAlgebra.coeff_injective
    ext n
    by_cases hn : n = a
    · subst n
      simp
    · have hz : p.coeff n = 0 :=
        Finsupp.notMem_support_iff.mp (fun hm => hn (h n hm))
      simp [hz, Ne.symm hn]
  have hc : p.coeff a ≠ 0 := fun hc => hp (by simpa [hc] using he)
  rw [he]
  exact isUnit_laurentSingle _ _ hc

private theorem exists_univariate_laurent_normalization
    (p : AddMonoidAlgebra ℂ G) (hp : p ≠ 0) (a d : G)
    (h : ∀ n ∈ p.coeff.support, ∃ k : ℤ, n = a + k • d) :
    ∃ c : G, ∃ P : Polynomial ℂ,
      p = AddMonoidAlgebra.single c 1 * Polynomial.aeval (AddMonoidAlgebra.single d 1) P := by
  classical
  have hz (n : G) : ∃ k : ℤ, n ∈ p.coeff.support → n = a + k • d := by
    by_cases hn : n ∈ p.coeff.support
    · obtain ⟨k, hk⟩ := h n hn
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun hm => (hn hm).elim⟩
  choose z hz using hz
  have hp' : p.coeff ≠ 0 := fun he => hp (AddMonoidAlgebra.coeff_injective (by simpa using he))
  obtain ⟨n₀, hn₀, hmin⟩ :=
    p.coeff.support.exists_min_image z (Finsupp.support_nonempty_iff.mpr hp')
  let c := a + z n₀ • d
  let k (n : G) := (z n - z n₀).toNat
  let P := ∑ n ∈ p.coeff.support, Polynomial.monomial (k n) (p.coeff n)
  refine ⟨c, P, ?_⟩
  dsimp only [P]
  rw [map_sum, Finset.mul_sum]
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  rw [Finsupp.sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hkn : (k n : ℤ) = z n - z n₀ :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (hmin n hn))
  have he : c + k n • d = n := by
    calc
      _ = a + z n • d := by
        rw [← natCast_zsmul, hkn]
        dsimp only [c]
        rw [add_assoc, ← add_zsmul, show z n₀ + (z n - z n₀) = z n by omega]
      _ = _ := (hz n hn).symm
  rw [Polynomial.aeval_monomial, AddMonoidAlgebra.single_pow, one_pow]
  change AddMonoidAlgebra.single n (p.coeff n) =
    AddMonoidAlgebra.single c 1 *
      (AddMonoidAlgebra.single 0 (p.coeff n) * AddMonoidAlgebra.single (k n • d) 1)
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, zero_add,
    mul_one, one_mul, he]

private theorem isUnit_laurent_prod_of_isUnit {A : Type*} [CommMonoid A]
    (s : Multiset A) (h : ∀ a ∈ s, IsUnit a) : IsUnit s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self _ _)).mul
      (ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)))

/-- An irreducible Laurent polynomial whose support lacks a noncollinear
triple is associated to a binomial in the same original exponent group. -/
theorem exists_associated_laurentBinomial_of_irreducible
    (b : Module.Basis ι ℤ G) (p : AddMonoidAlgebra ℂ G) (hp : Irreducible p)
    (hline : ¬ LaurentHasNoncollinearSupport p) :
    ∃ d : G, d ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ Associated p (laurentBinomial d c) := by
  classical
  obtain ⟨a, d, h⟩ := exists_affineCyclic_support_of_not_noncollinear b p hp.ne_zero hline
  have hd : d ≠ 0 := by
    intro hz
    apply hp.not_isUnit
    apply laurent_isUnit_of_singleton_support p hp.ne_zero a
    intro n hn
    obtain ⟨k, hk⟩ := h n hn
    simpa [hz] using hk
  obtain ⟨g, P, hP⟩ := exists_univariate_laurent_normalization p hp.ne_zero a d h
  let E : Polynomial ℂ →ₐ[ℂ] AddMonoidAlgebra ℂ G :=
    Polynomial.aeval (AddMonoidAlgebra.single d (1 : ℂ))
  have hP' : P ≠ 0 := fun hzero => hp.ne_zero (by simpa [hzero] using hP)
  have heval (c : ℂ) : E (Polynomial.X - Polynomial.C c) = laurentBinomial d c := by
    simp only [E, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    rfl
  have he := congrArg (fun R : Polynomial ℂ => E R) (IsAlgClosed.splits P).eq_prod_roots
  rw [map_mul, map_multiset_prod, Multiset.map_map, Polynomial.aeval_C] at he
  simp only [Function.comp_def, heval] at he
  have hprod : p = AddMonoidAlgebra.single g 1 *
      (AddMonoidAlgebra.single 0 P.leadingCoeff * (P.roots.map (laurentBinomial d)).prod) := by
    change p = AddMonoidAlgebra.single g 1 * E P at hP
    rw [hP, he]
    rfl
  have hroot : ∃ c ∈ P.roots, ¬ IsUnit (laurentBinomial d c) := by
    by_contra hn
    have hall : ∀ x ∈ P.roots.map (laurentBinomial d), IsUnit x := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hx
      by_contra hu
      exact hn ⟨c, hc, hu⟩
    exact hp.not_isUnit (hprod ▸
      (isUnit_laurentMonomial g).mul ((isUnit_laurentSingle 0 _
        (Polynomial.leadingCoeff_ne_zero.mpr hP')).mul
        (isUnit_laurent_prod_of_isUnit _ hall)))
  obtain ⟨c, hc, hcu⟩ := hroot
  have hc' : c ≠ 0 := by
    intro hz
    apply hcu
    simpa [laurentBinomial, hz] using isUnit_laurentMonomial d
  have hdiv : laurentBinomial d c ∣ p := by
    rw [hprod]
    exact ((Multiset.dvd_prod (Multiset.mem_map.mpr ⟨c, hc, rfl⟩)).mul_left _).mul_left _
  obtain ⟨q, hq⟩ := hdiv
  have hqu := (hp.isUnit_or_isUnit hq).resolve_left hcu
  exact ⟨d, hd, c, hc', (Associated.of_eq hq).trans (associated_mul_unit_left _ _ hqu)⟩

end

end MeyerGeneralProblem
