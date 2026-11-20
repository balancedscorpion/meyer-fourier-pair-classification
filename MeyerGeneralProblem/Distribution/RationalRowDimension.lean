module

public import MeyerGeneralProblem.Distribution.LaurentRowLinearity

@[expose] public section

/-! The full pair space is linearly equivalent to the common kernel of
the literal Fourier and physical equations on the finite numerator space. -/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped FourierTransform

variable {G : Type*} [AddCommGroup G]

/-- The derivative rows indexed by their actual physical positions and orders. -/
def physicalDerivativeRowIndex (A : LocallyFiniteCarrier) (p : ℂ → ℂ) : Type := by
  classical
  exact Σ a : ℝ, Fin (analyticOrderNatAt p (a : ℂ) - (if a ∈ A.carrier then 1 else 0))

/-- Evaluation of the exact Fourier deletion and physical derivative rows. -/
def literalRationalRows
    (L : G →+ ℝ) (p : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (A B : LocallyFiniteCarrier) (s : ℝ) :
    AddMonoidAlgebra.supported ℂ ℂ (literalNumeratorWindow L p.coeff lo hi B s) →ₗ[ℂ]
      (({n : G // L n ∉ B.carrier} → ℂ) ×
        (physicalDerivativeRowIndex A (complexExponentialSum L p.coeff) → ℂ)) := by
  let W := literalNumeratorWindow L p.coeff lo hi B s
  let V := AddMonoidAlgebra.supported ℂ ℂ W
  let J := orderedLaurentJumpLinearMap L p lo hi hlo hhi hmin hmax s W (fun n hn => hn.1)
  exact (LinearMap.pi fun n : {n : G // L n ∉ B.carrier} => (LinearMap.proj n.val).comp J).prod
    (LinearMap.pi fun q : physicalDerivativeRowIndex A (complexExponentialSum L p.coeff) =>
      (exponentialNumeratorDerivativeRow L q.1 q.2.val).comp V.subtype)

theorem mem_ker_literalRationalRows
    (L : G →+ ℝ) (p : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (A B : LocallyFiniteCarrier) (s : ℝ)
    (R : AddMonoidAlgebra.supported ℂ ℂ (literalNumeratorWindow L p.coeff lo hi B s)) :
    R ∈ LinearMap.ker (literalRationalRows L p lo hi hlo hhi hmin hmax A B s) ↔
      (∀ n, L n ∉ B.carrier → orderedLaurentJump p R.val lo hi n = 0) ∧
        quotientPhysicalRows A (complexExponentialSum L R.val.coeff) (complexExponentialSum L p.coeff) := by
  classical
  rw [LinearMap.mem_ker]
  change ((fun n : {n : G // L n ∉ B.carrier} => orderedLaurentJump p R.val lo hi n),
      (fun q : physicalDerivativeRowIndex A (complexExponentialSum L p.coeff) =>
        iteratedDeriv q.2.val (complexExponentialSum L R.val.coeff) (q.1 : ℂ))) = 0 ↔ _
  constructor
  · intro h
    exact ⟨fun n hn => congrFun (congrArg Prod.fst h) ⟨n, hn⟩,
      fun a j hj => congrFun (congrArg Prod.snd h) ⟨a, ⟨j, hj⟩⟩⟩
  · rintro ⟨hF, hP⟩
    apply Prod.ext
    · funext n
      exact hF n n.property
    · funext q
      exact hP q.1 q.2.val q.2.isLt

private theorem literalNumeratorWindow_contains_numerator
    (L : G →+ ℝ) (p : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hmin : ∀ n ∈ p.coeff.support, L lo ≤ L n)
    (hmax : ∀ n ∈ p.coeff.support, L n ≤ L hi)
    (A B : LocallyFiniteCarrier) (s : ℝ)
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p.coeff x = 0)
    (T : DistributionalMeyerPairSpace A B) :
    Function.support (cutArrayNumerator L p.coeff s (originalFourierArray L B T)) ⊆
      literalNumeratorWindow L p.coeff lo hi B s := by
  have hT := (mem_distributionalMeyerPairSpace_iff A B _).mp T.property
  apply cutArrayNumerator_support_subset_literalNumeratorWindow L p.coeff lo hi hmin hmax
  · intro n hn
    by_contra hb
    exact hn (by simp [originalFourierArray, extendedAtomicCoefficient, hb])
  · exact originalFourierArray_annihilated L p.coeff A B T hT.1 hT.2 hA

/-- For a prescribed real-rooted denominator the entire original pair space
has the dimension given by the literal numerator count minus the exact row
rank. The equivalence sends each source to its original cut numerator. -/
theorem originalPair_finrank_add_literalRationalRows_rank
    [Module.Finite ℤ G] [Module.IsTorsionFree ℤ G]
    (L : G →+ ℝ) (hL : Function.Injective L) (p : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0)
    (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p.coeff x = 0)
    (s : ℝ) :
    let W := literalNumeratorWindow L p.coeff lo hi B s
    let rows := literalRationalRows L p lo hi hlo hhi hmin hmax A B s
    (∃ e : DistributionalMeyerPairSpace A B ≃ₗ[ℂ] LinearMap.ker rows,
      ∀ T n, (e T).val.val.coeff n =
        cutArrayNumerator L p.coeff s (originalFourierArray L B T) n) ∧
    Module.finrank ℂ (DistributionalMeyerPairSpace A B) +
      Module.finrank ℂ (LinearMap.range rows) = W.ncard := by
  classical
  let W := literalNumeratorWindow L p.coeff lo hi B s
  let rows := literalRationalRows L p lo hi hlo hhi hmin hmax A B s
  let V := AddMonoidAlgebra.supported ℂ ℂ W
  have hmin' (n : G) (hn : n ∈ p.coeff.support) : L lo ≤ L n := by
    by_cases h : n = lo
    · rw [h]
    · exact (hmin n hn h).le
  have hmax' (n : G) (hn : n ∈ p.coeff.support) : L n ≤ L hi := by
    by_cases h : n = hi
    · rw [h]
    · exact (hmax n hn h).le
  have hW : W.Finite := literalNumeratorWindow_finite L hL p.coeff lo hi hmin' B s
  let _ : Fintype W := hW.fintype
  let eV : V ≃ₗ[ℂ] (W → ℂ) := (AddMonoidAlgebra.supportedEquivFinsupp (R := ℂ) (S := ℂ) W).trans
    (Finsupp.linearEquivFunOnFinite ℂ ℂ W)
  let M := originalPairLiteralNumeratorMap L p.coeff lo hi A B s
  let N : DistributionalMeyerPairSpace A B →ₗ[ℂ] V := eV.symm.toLinearMap.comp M
  have hcoef (T : DistributionalMeyerPairSpace A B) (n : G) :
      (N T).val.coeff n = cutArrayNumerator L p.coeff s (originalFourierArray L B T) n := by
    by_cases hn : n ∈ W
    · change (eV (eV.symm (M T))) ⟨n, hn⟩ = _
      rw [eV.apply_symm_apply]
      exact originalNumeratorRow_apply L p.coeff B s n T
    · rw [(AddMonoidAlgebra.mem_supported'.mp (N T).property) n hn]
      apply Eq.symm
      by_contra hne
      exact hn (literalNumeratorWindow_contains_numerator L p lo hi hmin' hmax' A B s hA T hne)
  have hrealize (R : V) :
      R ∈ LinearMap.ker rows ↔ ∃! T : DistributionalMeyerPairSpace A B,
        cutArrayNumerator L p.coeff s (originalFourierArray L B T) = (fun n => R.val.coeff n) :=
    (mem_ker_literalRationalRows L p lo hi hlo hhi hmin hmax A B s R).trans
      (literalNumerator_rows_iff_existsUnique_originalPair L hL p R.val lo hi hlo hhi hmin hmax hroot
        A B hB hA s R.property)
  have hin (T : DistributionalMeyerPairSpace A B) : N T ∈ LinearMap.ker rows := by
    apply (hrealize (N T)).mpr
    refine ⟨T, funext fun n => (hcoef T n).symm, ?_⟩
    intro U hU
    apply Subtype.ext
    have hp : p.coeff ≠ 0 := fun hp => hlo (by simp [hp])
    have hUp := (mem_distributionalMeyerPairSpace_iff A B _).mp U.property
    have hTp := (mem_distributionalMeyerPairSpace_iff A B _).mp T.property
    exact originalFourierPair_cutNumerator_injective L hL p.coeff hp A B hB U T
      hUp.1 hTp.1 hUp.2 hTp.2 hA s (hU.trans (funext (hcoef T)))
  let P := N.codRestrict (LinearMap.ker rows) hin
  have hPinj : Function.Injective P := by
    intro U T h
    have heq : N U = N T := congrArg Subtype.val h
    have hM : M U = M T := eV.symm.injective heq
    have hp : p.coeff ≠ 0 := fun hp => hlo (by simp [hp])
    exact originalPairLiteralNumeratorMap_injective L hL p.coeff hp lo hi hmin' hmax' A B hB hA s hM
  have hPsur : Function.Surjective P := by
    intro R
    obtain ⟨T, hT, _⟩ := (hrealize R.val).mp R.property
    refine ⟨T, Subtype.ext (Subtype.ext ?_)⟩
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro n
    exact (hcoef T n).trans (congrFun hT n)
  let E := LinearEquiv.ofBijective P ⟨hPinj, hPsur⟩
  refine ⟨⟨E, hcoef⟩, ?_⟩
  have : FiniteDimensional ℂ V := FiniteDimensional.of_injective eV.toLinearMap eV.injective
  rw [E.finrank_eq, add_comm]
  exact rows.finrank_range_add_finrank_ker.trans
    (eV.finrank_eq.trans (by
      simp only [Module.finrank_fintype_fun_eq_card, Set.fintypeCard_eq_ncard, W]))

end

end MeyerGeneralProblem
