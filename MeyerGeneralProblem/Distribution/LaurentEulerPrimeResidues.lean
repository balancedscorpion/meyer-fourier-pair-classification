module

public import MeyerGeneralProblem.Distribution.LaurentEulerRecurrence
public import MeyerGeneralProblem.Distribution.LaurentRecurrenceWidth
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-!
# Two independent projective Euler residues

Two coordinates that detect an affinely independent triple of occupied
monomials have no nonzero constant linear relation modulo the Laurent
polynomial. At a prime this makes their projective ratio transcendental
over the complex constants.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- A genuinely two-dimensional coordinate projection on the support
prevents any nonzero linear combination of the two Euler polynomials
from being divisible by the original polynomial. -/
theorem laurent_not_dvd_twoEulerCombination
    (L : G →+ ℝ) (hL : Function.Injective L) (p : AddMonoidAlgebra ℂ G)
    (e f : G →+ ℂ) (n₀ n₁ n₂ : G) (h₀ : p.coeff n₀ ≠ 0) (h₁ : p.coeff n₁ ≠ 0)
    (h₂ : p.coeff n₂ ≠ 0)
    (hdet : (e n₁ - e n₀) * (f n₂ - f n₀) - (e n₂ - e n₀) * (f n₁ - f n₀) ≠ 0)
    (a b : ℂ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ¬ p ∣ a • laurentEulerPolynomial e p + b • laurentEulerPolynomial f p := by
  classical
  let q := a • laurentEulerPolynomial e p + b • laurentEulerPolynomial f p
  have hcoeff (n : G) : q.coeff n = (a * e n + b * f n) * p.coeff n := by
    simp only [q, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_smul,
      Finsupp.smul_apply, smul_eq_mul, laurentEulerPolynomial_coeff]
    ring
  have hsub : q.coeff.support ⊆ p.coeff.support := by
    intro n hn
    rw [Finsupp.mem_support_iff, hcoeff] at hn
    exact Finsupp.mem_support_iff.mpr (mul_ne_zero_iff.mp hn).2
  intro hdvd
  obtain ⟨c, hcp⟩ : ∃ c : ℂ, q = c • p := by
    by_cases hq : q = 0
    · exact ⟨0, by simp [hq]⟩
    · obtain ⟨c, _, hc⟩ := laurent_eq_smul_of_dvd_and_support_subset L hL p q hq hsub hdvd
      exact ⟨c, hc⟩
  have hf (n : G) (hn : p.coeff n ≠ 0) : a * e n + b * f n = c := by
    apply mul_right_cancel₀ hn
    rw [← hcoeff, hcp, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  have h₁₀ : a * (e n₁ - e n₀) + b * (f n₁ - f n₀) = 0 := by
    linear_combination hf n₁ h₁ - hf n₀ h₀
  have h₂₀ : a * (e n₂ - e n₀) + b * (f n₂ - f n₀) = 0 := by
    linear_combination hf n₂ h₂ - hf n₀ h₀
  have ha : a * ((e n₁ - e n₀) * (f n₂ - f n₀) - (e n₂ - e n₀) * (f n₁ - f n₀)) = 0 := by
    linear_combination (f n₂ - f n₀) * h₁₀ - (f n₁ - f n₀) * h₂₀
  have hb : b * ((e n₁ - e n₀) * (f n₂ - f n₀) - (e n₂ - e n₀) * (f n₁ - f n₀)) = 0 := by
    linear_combination (e n₁ - e n₀) * h₂₀ - (e n₂ - e n₀) * h₁₀
  exact hab.elim (fun h => (mul_eq_zero.mp ha).elim h hdet)
    (fun h => (mul_eq_zero.mp hb).elim h hdet)

private theorem transcendental_div_of_nonproportional {K : Type*} [Field K] [Algebra ℂ K]
    (u v : K) (hu : u ≠ 0) (h : ∀ c : ℂ, v ≠ c • u) :
    Transcendental ℂ (v / u) := by
  refine transcendental_iff.mpr fun q hq => ?_
  by_contra hq0
  have hmem : v / u ∈ q.rootSet K := Polynomial.mem_rootSet.mpr ⟨hq0, hq⟩
  have hsplit : (q.map (algebraMap ℂ ℂ)).Splits := by
    simpa using IsAlgClosed.splits q
  rw [← hsplit.image_rootSet (Algebra.ofId ℂ K)] at hmem
  obtain ⟨c, _, hc⟩ := hmem
  apply h c
  rw [Algebra.smul_def]
  exact (div_eq_iff hu).mp hc.symm

/-- In the fraction field of the quotient by a prime Laurent polynomial,
the projective ratio of the two Euler residues is transcendental as
soon as their coordinates separate an affinely independent triple. -/
theorem laurent_primeEulerRatio_transcendental
    (L : G →+ ℝ) (hL : Function.Injective L) (p : AddMonoidAlgebra ℂ G) (hp : Prime p)
    (e f : G →+ ℂ) (n₀ n₁ n₂ : G) (h₀ : p.coeff n₀ ≠ 0) (h₁ : p.coeff n₁ ≠ 0)
    (h₂ : p.coeff n₂ ≠ 0)
    (hdet : (e n₁ - e n₀) * (f n₂ - f n₀) - (e n₂ - e n₀) * (f n₁ - f n₀) ≠ 0) :
    let I := Ideal.span ({p} : Set (AddMonoidAlgebra ℂ G))
    letI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
    let K := FractionRing ((AddMonoidAlgebra ℂ G) ⧸ I)
    let φ := (IsScalarTower.toAlgHom ℂ ((AddMonoidAlgebra ℂ G) ⧸ I) K).comp
      (Ideal.Quotient.mkₐ ℂ I)
    Transcendental ℂ (φ (laurentEulerPolynomial f p) / φ (laurentEulerPolynomial e p)) := by
  dsimp only
  let I := Ideal.span ({p} : Set (AddMonoidAlgebra ℂ G))
  let _ : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
  let K := FractionRing ((AddMonoidAlgebra ℂ G) ⧸ I)
  let φ := (IsScalarTower.toAlgHom ℂ ((AddMonoidAlgebra ℂ G) ⧸ I) K).comp
    (Ideal.Quotient.mkₐ ℂ I)
  change Transcendental ℂ (φ (laurentEulerPolynomial f p) / φ (laurentEulerPolynomial e p))
  have hker (q : AddMonoidAlgebra ℂ G) : φ q = 0 ↔ p ∣ q := by
    change algebraMap ((AddMonoidAlgebra ℂ G) ⧸ I) K (Ideal.Quotient.mk I q) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
  have hnd := laurent_not_dvd_twoEulerCombination L hL p e f n₀ n₁ n₂ h₀ h₁ h₂ hdet
  apply transcendental_div_of_nonproportional
  · exact (hker _).not.mpr (by simpa using hnd 1 0 (Or.inl one_ne_zero))
  · intro c hc
    apply hnd (-c) 1 (Or.inr one_ne_zero)
    apply (hker _).mp
    simp [hc, neg_smul]

/-- A transcendental projective ratio gives independent homogeneous
monomials in its two original residues in every degree. -/
theorem linearIndependent_homogeneous_powers_of_transcendental_ratio
    {K : Type*} [Field K] [Algebra ℂ K] (x y : K) (hx : x ≠ 0)
    (ht : Transcendental ℂ (y / x)) (k : ℕ) :
    LinearIndependent ℂ (fun j : Fin (k + 1) => x ^ (k - (j : ℕ)) * y ^ (j : ℕ)) := by
  have hi : Function.Injective (Polynomial.aeval (y / x) : Polynomial ℂ →ₐ[ℂ] K) :=
    transcendental_iff_injective.mp ht
  have hpow : LinearIndependent ℂ (fun j : ℕ => (y / x) ^ j) := by
    simpa only [Function.comp_def, Polynomial.coe_basisMonomials, AlgHom.toLinearMap_apply,
      Polynomial.aeval_monomial, map_one, one_mul] using
      (Polynomial.basisMonomials ℂ).linearIndependent.map'
        (Polynomial.aeval (y / x)).toLinearMap (LinearMap.ker_eq_bot.mpr hi)
  let M : K →ₗ[ℂ] K :=
    { toFun := fun z => x ^ k * z
      map_add' := fun z w => mul_add _ z w
      map_smul' := fun c z => mul_smul_comm _ _ _ }
  have hm : Function.Injective M := fun _ _ h => mul_left_cancel₀ (pow_ne_zero _ hx) h
  have he : (fun j : Fin (k + 1) => x ^ (k - (j : ℕ)) * y ^ (j : ℕ)) =
      M ∘ (fun j : ℕ => (y / x) ^ j) ∘ (fun j : Fin (k + 1) => (j : ℕ)) := by
    funext j
    have hj : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
    change x ^ (k - (j : ℕ)) * y ^ (j : ℕ) = x ^ k * (y / x) ^ (j : ℕ)
    rw [div_pow, ← mul_div_assoc, eq_div_iff (pow_ne_zero _ hx), mul_right_comm,
      ← pow_add, Nat.sub_add_cancel hj]
  rw [he]
  exact (hpow.comp (fun j : Fin (k + 1) => (j : ℕ)) Fin.val_injective).map' M
    (LinearMap.ker_eq_bot.mpr hm)

end

end MeyerGeneralProblem
