module

public import MeyerGeneralProblem.Distribution.LaurentQuadraticPrimeRemoval
public import MeyerGeneralProblem.Distribution.LaurentRankOneBinomial
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

@[expose] public section

/-!
# Exhaustive removal of noncollinear prime factors

Strict division in the original finite-rank Laurent algebra terminates
the checked one-prime removal. Every prime left in the common
annihilator is associated to a literal binomial.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped FourierTransform

variable {G ι : Type*} [AddCommGroup G] [Fintype ι]

/-- Trim the original denominator simultaneously for every locally
finite array in its kernel with vanishing quadratic lower count. -/
theorem exists_laurentTrimmedRecurrence (b : Module.Basis ι ℤ G)
    (L : G →+ ℝ) (hL : Function.Injective L)
    (P : AddMonoidAlgebra ℂ G) (hP : P ≠ 0) :
    ∃ Q : AddMonoidAlgebra ℂ G, Q ≠ 0 ∧ Q ∣ P ∧
      (∀ p : AddMonoidAlgebra ℂ G, Prime p → p ∣ Q → ¬ LaurentHasNoncollinearSupport p) ∧
      ∀ u : G → ℂ, FrequencyLocallyFinite L u → VanishingQuadraticLowerArrayCount L u →
        (∀ n, annihilatorArrayConvolution P.coeff u n = 0) →
        ∀ n, annihilatorArrayConvolution Q.coeff u n = 0 := by
  classical
  let _ : IsDomain (AddMonoidAlgebra ℂ G) := basisLaurent_isDomain b
  let _ : UniqueFactorizationMonoid (AddMonoidAlgebra ℂ G) :=
    basisLaurent_uniqueFactorizationMonoid b
  let C (D : AddMonoidAlgebra ℂ G) := D ≠ 0 →
    ∃ Q : AddMonoidAlgebra ℂ G, Q ≠ 0 ∧ Q ∣ D ∧
      (∀ p : AddMonoidAlgebra ℂ G, Prime p → p ∣ Q → ¬ LaurentHasNoncollinearSupport p) ∧
      ∀ u : G → ℂ, FrequencyLocallyFinite L u → VanishingQuadraticLowerArrayCount L u →
        (∀ n, annihilatorArrayConvolution D.coeff u n = 0) →
        ∀ n, annihilatorArrayConvolution Q.coeff u n = 0
  revert hP
  change C P
  refine wellFounded_dvdNotUnit.induction (C := C) P ?_
  intro P ih hP
  by_cases hbad : ∃ p : AddMonoidAlgebra ℂ G, Prime p ∧ p ∣ P ∧ LaurentHasNoncollinearSupport p
  · obtain ⟨p, hp, hdiv, e, f, n₀, n₁, n₂, h₀, h₁, h₂, hdet⟩ := hbad
    have hfin := FiniteMultiplicity.of_prime_left hp hP
    obtain ⟨q, hPq, hq⟩ := hfin.exists_eq_pow_mul_and_not_dvd
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
      (multiplicity_pos_of_dvd hdiv hfin).ne'
    have he : P = p ^ (m + 1) * q := by simpa only [hm] using hPq
    have hq' : q ≠ 0 := fun h => hP (by rw [he, h, mul_zero])
    have hstrict : DvdNotUnit q P := by
      refine ⟨hq', p ^ (m + 1), ?_, he.trans (mul_comm _ _)⟩
      intro hu
      exact hp.not_isUnit (isUnit_of_dvd_unit (dvd_pow_self p (Nat.succ_ne_zero m)) hu)
    obtain ⟨Q, hQ, hQq, hQp, hQrec⟩ := ih q hstrict hq'
    refine ⟨Q, hQ, hQq.trans ⟨p ^ (m + 1), he.trans (mul_comm _ _)⟩, hQp, ?_⟩
    intro u hu hcount hrec
    have hP' : P.coeff ≠ 0 := fun h => hP (AddMonoidAlgebra.coeff_injective (by simpa using h))
    obtain ⟨lo, hi, _, _, hb, _, _⟩ := finiteAnnihilator_extrema L hL P.coeff hP'
    let R := AddMonoidAlgebra.ofCoeff (finiteCutNumerator L P.coeff 0 (L lo) (L hi)
      (fun n hn => (hb n hn).1) (fun n hn => (hb n hn).2) u hu hrec)
    have hcut : cutArrayNumerator L P.coeff 0 u = R.coeff := by
      funext n
      rfl
    have hconv : annihilatorArrayConvolution (p ^ (m + 1) * q).coeff u = 0 := by
      rw [← he]
      exact funext hrec
    have hcut' : cutArrayNumerator L (p ^ (m + 1) * q).coeff 0 u = R.coeff := by
      rw [← he]
      exact hcut
    have hred := laurentRecurrence_cancel_primePower_of_vanishingQuadraticLowerCount L hL
      p q R m hp hq e f n₀ n₁ n₂ h₀ h₁ h₂ hdet 0 u hu hconv hcut' hcount
    exact hQrec u hu hcount hred.1
  · exact ⟨P, hP, dvd_rfl, fun p hp hd h => hbad ⟨p, hp, hd, h⟩, fun _ _ _ h => h⟩

/-- A finite list of literal binomials represents the trimmed
annihilator up to a unit in the original Laurent algebra. -/
theorem exists_laurentBinomial_product_of_collinear_primes
    (b : Module.Basis ι ℤ G) (P : AddMonoidAlgebra ℂ G) (hP : P ≠ 0)
    (hline : ∀ p : AddMonoidAlgebra ℂ G, Prime p → p ∣ P → ¬ LaurentHasNoncollinearSupport p) :
    ∃ l : List (G × ℂ), (∀ x ∈ l, x.1 ≠ 0 ∧ x.2 ≠ 0) ∧
      Associated (l.map (fun x => laurentBinomial x.1 x.2)).prod P := by
  classical
  let _ : IsDomain (AddMonoidAlgebra ℂ G) := basisLaurent_isDomain b
  let _ : UniqueFactorizationMonoid (AddMonoidAlgebra ℂ G) :=
    basisLaurent_uniqueFactorizationMonoid b
  obtain ⟨f, hf, hfP⟩ := UniqueFactorizationMonoid.exists_prime_factors P hP
  have hfbin (p : AddMonoidAlgebra ℂ G) (hp : p ∈ f) :
      ∃ d : G, d ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ Associated p (laurentBinomial d c) :=
    exists_associated_laurentBinomial_of_irreducible b p (hf p hp).irreducible
      (hline p (hf p hp) ((Multiset.dvd_prod hp).trans hfP.dvd))
  have haux (w : List (AddMonoidAlgebra ℂ G))
      (hw : ∀ p ∈ w, ∃ d : G, d ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ Associated p (laurentBinomial d c)) :
      ∃ l : List (G × ℂ), (∀ x ∈ l, x.1 ≠ 0 ∧ x.2 ≠ 0) ∧
        Associated (l.map (fun x => laurentBinomial x.1 x.2)).prod w.prod := by
    induction w with
    | nil => exact ⟨[], by simp, Associated.rfl⟩
    | cons p w ih =>
      obtain ⟨d, hd, c, hc, hp⟩ := hw p (by simp)
      obtain ⟨l, hl, hprod⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
      refine ⟨(d, c) :: l, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨hd, hc⟩
        · exact hl x hx
      · simpa only [List.map_cons, List.prod_cons] using hp.symm.mul_mul hprod
  obtain ⟨l, hl, hprod⟩ := haux f.toList (fun p hp => hfbin p (Multiset.mem_toList.mp hp))
  exact ⟨l, hl, hprod.trans (by simpa only [Multiset.prod_toList] using hfP)⟩

/-- Exhaustive trimming gives one binomial product for the complete
original Fourier-pair space under the quadratic lower count condition. -/
theorem exists_originalPairSpace_binomial_annihilator_of_vanishingQuadraticLowerCount
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L)
    (P : AddMonoidAlgebra ℂ G) (hP : P ≠ 0)
    (A B : LocallyFiniteCarrier) (hmodule : B.carrier ⊆ range L)
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L P.coeff x = 0)
    (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((B.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    ∃ l : List (G × ℂ), (∀ x ∈ l, x.1 ≠ 0 ∧ x.2 ≠ 0) ∧
      let Q := (l.map (fun x => laurentBinomial x.1 x.2)).prod
      Q ≠ 0 ∧ DistributionalMeyerPairSpace A B =
        DistributionalMeyerPairSpace (annihilatorZeroSubcarrier L Q.coeff A) B := by
  obtain ⟨Q, hQ, _, hcol, hrec⟩ := exists_laurentTrimmedRecurrence b L hL P hP
  obtain ⟨l, hl, hprod⟩ := exists_laurentBinomial_product_of_collinear_primes b Q hQ hcol
  let S := (l.map (fun x => laurentBinomial x.1 x.2)).prod
  obtain ⟨v, hv⟩ := hprod
  change S * (v : AddMonoidAlgebra ℂ G) = Q at hv
  have hS : S ≠ 0 := fun h => hQ (by rw [← hv, h, zero_mul])
  refine ⟨l, hl, hS, ?_⟩
  ext T
  rw [mem_distributionalMeyerPairSpace_iff, mem_distributionalMeyerPairSpace_iff]
  constructor
  · rintro ⟨hT, hFT⟩
    let u := originalFourierArray L B T
    have hu := hrec u (originalFourierArray_frequencyLocallyFinite L hL B T)
      (vanishingQuadraticLowerArrayCount_originalFourierArray L hL B T hcount)
      (originalFourierArray_annihilated L P.coeff A B T hT hFT hA)
    have he (n : G) : annihilatorArrayConvolution S.coeff u n = 0 := by
      calc
        _ = annihilatorArrayConvolution (↑v⁻¹ : AddMonoidAlgebra ℂ G).coeff
            (annihilatorArrayConvolution Q.coeff u) n := by
          rw [← annihilatorArrayConvolution_mul, ← hv, mul_left_comm, Units.inv_mul, mul_one]
        _ = _ := by rw [funext hu]; exact annihilatorArrayConvolution_zero _ n
    exact ⟨originalPair_atomicOn_zeroSubcarrier_of_arrayRecurrence L hL S A B hmodule T hT hFT he,
      hFT⟩
  · rintro ⟨hT, hFT⟩
    have hsub : (annihilatorZeroSubcarrier L S.coeff A).carrier ⊆ A.carrier :=
      fun _ hx => hx.1
    exact ⟨hT.mono hsub, hFT⟩

end

end MeyerGeneralProblem
