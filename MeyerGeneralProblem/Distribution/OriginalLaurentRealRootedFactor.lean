module

public import MeyerGeneralProblem.Distribution.LaurentPolynomialCoordinateNormalization
public import MeyerGeneralProblem.Distribution.PolynomialQuotientFactor

@[expose] public section

/-!
# The common real-rooted factor of an original Laurent annihilator

An ordinary polynomial denominator is obtained by an original monomial
shift. At every non-real phase point its quotient with the actual cut
numerator has a continuous local extension. Removing the irreducible
factors with zeros at those phases preserves their full multiplicities.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Set
open scoped FourierTransform

variable {G ι : Type*} [AddCommGroup G] [Fintype ι]

/-- All original Laurent points obtained from real torus phases at a
non-real leaf parameter. -/
def offRealLaurentPhaseSet (b : Module.Basis ι ℤ G) (L : G →+ ℝ) : Set (ι → ℂ) :=
  {v | ∃ (a : ι → ℝ) (c : ℂ), c.im ≠ 0 ∧
    (fun i => (basisLaurentPhasePoint b L (fun i => (a i : ℂ)) c i : ℂ)) = v}

private theorem polynomialQuotientRegularOn_of_originalPair
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L)
    (p R : AddMonoidAlgebra ℂ G) (hp : p.coeff ≠ 0)
    (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (hFT : AtomicOnCarrier B (𝓕 T))
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p.coeff x = 0) (s : ℝ)
    (hR : cutArrayNumerator L p.coeff s (originalFourierArray L B T) = (fun n => R.coeff n))
    (P Q : MvPolynomial ι ℂ) (m n : G)
    (hP : basisPolynomialEmbedding b P = AddMonoidAlgebra.single m 1 * p)
    (hQ : basisPolynomialEmbedding b Q = AddMonoidAlgebra.single n 1 * R) :
    PolynomialQuotientRegularOn (offRealLaurentPhaseSet b L) P Q := by
  rintro _ ⟨a, c, hc, rfl⟩
  obtain ⟨W, hW, ha, hnz, H, hH, hEq⟩ :=
    originalPair_laurent_local_factorization_near_nonreal_phase b L hL p R hp
      A B hB T hT hFT hA s hR a c hc
  let M (k : G) (w : ι → ℂ) : ℂ := ∏ i, w i ^ b.repr k i
  have hM (k : G) : ContinuousOn (M k) W := by
    apply continuousOn_finsetProd
    intro i _
    exact (continuous_apply i).continuousOn.zpow₀ _ (fun w hw => Or.inl (hnz w hw i))
  have hMne (k : G) (w : ι → ℂ) (hw : w ∈ W) : M k w ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hnz w hw i)
  let F (w : ι → ℂ) : ℂ := M n w / M m w * H w
  refine ⟨W, hW, ha, F, ((hM n).div (hM m) (hMne m)).mul hH, ?_⟩
  intro w hw
  let v (i : ι) : ℂˣ := Units.mk0 (w i) (hnz w hw i)
  have hpv : MvPolynomial.eval w P = M m w * basisLaurentEvaluation b v p := by
    change MvPolynomial.eval (fun i => (v i : ℂ)) P = _
    rw [← basisPolynomialEmbedding_eval b v, hP, map_mul, basisLaurentEvaluation_single, one_mul]
    rfl
  have hqv : MvPolynomial.eval w Q = M n w * basisLaurentEvaluation b v R := by
    change MvPolynomial.eval (fun i => (v i : ℂ)) Q = _
    rw [← basisPolynomialEmbedding_eval b v, hQ, map_mul, basisLaurentEvaluation_single, one_mul]
    rfl
  have hv := hEq v hw
  change basisLaurentEvaluation b v R = basisLaurentEvaluation b v p * H w at hv
  rw [hqv, hpv, hv]
  dsimp only [F]
  field_simp [hMne m w hw]

private theorem laurent_single_neg_mul_single (m : G) :
    (AddMonoidAlgebra.single (-m) 1 : AddMonoidAlgebra ℂ G) *
      AddMonoidAlgebra.single m 1 = 1 := by
  simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]

/-- Evaluation on the zero-phase leaf is the literal complex
exponential symbol in the original spectral module. -/
theorem basisLaurentEvaluation_zero_phase
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (p : AddMonoidAlgebra ℂ G) (z : ℂ) :
    basisLaurentEvaluation b (basisLaurentPhasePoint b L 0 z) p =
      complexExponentialSum L p.coeff z := by
  rw [← basisComplexPhaseExponentialSum_eq_laurentEvaluation,
    basisComplexPhaseExponentialSum_of_real b L p.coeff 0 (fun _ => Complex.zero_im) z]
  unfold basisTorusExponentialSum finiteEntireExponentialSum complexExponentialSum
  rw [← p.coeff.support.sum_coe_sort (fun m => p.coeff m *
    Complex.exp (2 * Real.pi * Complex.I * (L m : ℂ) * z))]
  apply Finset.sum_congr rfl
  intro m _
  simp [basisTorusCharacter, mFourier_torusLinearFlow]

/-- One real-rooted factor of the denominator works simultaneously for
every actual pair with this original annihilator. The discarded factor
divides every literal numerator, at every cut. The factorization takes
place in the original group algebra. -/
theorem exists_realRooted_factor_dvd_all_originalPair_numerators
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L)
    (p : AddMonoidAlgebra ℂ G) (hp : p ≠ 0) :
    ∃ d g : AddMonoidAlgebra ℂ G, p = d * g ∧ g ≠ 0 ∧
      (∀ a : ι → ℝ, ∀ c : ℂ, c.im ≠ 0 →
        basisLaurentEvaluation b (basisLaurentPhasePoint b L (fun i => (a i : ℂ)) c) g ≠ 0) ∧
      ∀ (A B : LocallyFiniteCarrier) (_ : B.carrier ⊆ range L)
        (T : TemperedDistribution ℝ ℂ) (_ : AtomicOnCarrier A T)
        (_ : AtomicOnCarrier B (𝓕 T))
        (_ : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p.coeff x = 0)
        (s : ℝ) (R : AddMonoidAlgebra ℂ G),
        cutArrayNumerator L p.coeff s (originalFourierArray L B T) = (fun n => R.coeff n) →
        d ∣ R := by
  obtain ⟨m, P, hP⟩ := exists_basisLaurent_polynomial_normalization b p
  have hP' : p = AddMonoidAlgebra.single (-m) 1 * basisPolynomialEmbedding b P := by
    rw [hP, ← mul_assoc, laurent_single_neg_mul_single, one_mul]
  have hPnz : P ≠ 0 := by
    intro h
    apply hp
    rw [hP', h, map_zero, mul_zero]
  obtain ⟨bad, good, hprod, _, hgood, hdivide⟩ :=
    exists_zeroFree_factor_for_local_polynomial_quotients (offRealLaurentPhaseSet b L) P hPnz
  let d := AddMonoidAlgebra.single (-m) 1 * basisPolynomialEmbedding b bad.prod
  let g := basisPolynomialEmbedding b good
  have hpg : p = d * g := by
    rw [hP', hprod, map_mul, ← mul_assoc]
  refine ⟨d, g, hpg, ?_, ?_, ?_⟩
  · intro h
    apply hp
    rw [hpg, h, mul_zero]
  · intro a c hc
    rw [basisPolynomialEmbedding_eval]
    exact hgood _ ⟨a, c, hc, rfl⟩
  · intro A B hB T hT hFT hA s R hR
    obtain ⟨n, Q, hQ⟩ := exists_basisLaurent_polynomial_normalization b R
    have hcoeff : p.coeff ≠ 0 := fun h => hp (AddMonoidAlgebra.coeff_injective (h.trans AddMonoidAlgebra.coeff_zero.symm))
    obtain ⟨q, hq⟩ := hdivide Q
      (polynomialQuotientRegularOn_of_originalPair b L hL p R hcoeff
        A B hB T hT hFT hA s hR P Q m n hP hQ)
    refine ⟨AddMonoidAlgebra.single m 1 *
      (AddMonoidAlgebra.single (-n) 1 * basisPolynomialEmbedding b q), ?_⟩
    calc
      R = AddMonoidAlgebra.single (-n) 1 * basisPolynomialEmbedding b Q := by
        rw [hQ, ← mul_assoc, laurent_single_neg_mul_single, one_mul]
      _ = AddMonoidAlgebra.single (-n) 1 *
          (basisPolynomialEmbedding b bad.prod * basisPolynomialEmbedding b q) := by
        rw [hq, map_mul]
      _ = d * _ := by
        calc
          _ = ((AddMonoidAlgebra.single (-m) 1 : AddMonoidAlgebra ℂ G) *
              AddMonoidAlgebra.single m 1) *
              (AddMonoidAlgebra.single (-n) 1 *
                (basisPolynomialEmbedding b bad.prod * basisPolynomialEmbedding b q)) := by
            rw [laurent_single_neg_mul_single, one_mul]
          _ = _ := by dsimp only [d]; ac_rfl

end

end MeyerGeneralProblem
