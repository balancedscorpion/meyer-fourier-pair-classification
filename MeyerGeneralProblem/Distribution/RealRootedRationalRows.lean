module

public import MeyerGeneralProblem.Distribution.LaurentBoundary
public import MeyerGeneralProblem.Distribution.LiteralNumeratorWindow
public import MeyerGeneralProblem.Distribution.QuotientPhysicalRows
public import MeyerGeneralProblem.Distribution.LiteralAtomicSourceRecovery

@[expose] public section

/-!
# Exact original rational rows for a real-rooted denominator

For a fixed real-rooted denominator, the literal original Fourier rows
and the physical exclusion and multiplicity rows are necessary and
sufficient for synthesis of the unique original broad pair.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped FourierTransform

variable {G : Type*} [AddCommGroup G]

/-- The exact physical equations characterize the actual inverse of the
complete original Laurent jump. -/
theorem laurentInverse_atomicOnCarrier_iff_physicalRows
    (L : G →+ ℝ) (hL : Function.Injective L) (p R : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0)
    (s : ℝ) (hR : ∀ r ∈ R.coeff.support, L lo + s ≤ L r ∧ L r < L hi + s)
    (B : LocallyFiniteCarrier) (hB : B.carrier = L '' Function.support (orderedLaurentJump p R lo hi))
    (T : TemperedDistribution ℝ ℂ) (N : ℕ) (hT : 𝓕 T ∈ stronglyTemperedAtomicAtExponent B N)
    (harray : ∀ n, originalFourierArray L B T n = orderedLaurentJump p R lo hi n)
    (A : LocallyFiniteCarrier) :
    AtomicOnCarrier A T ↔
      quotientPhysicalRows A (complexExponentialSum L R.coeff) (complexExponentialSum L p.coeff) := by
  have hp := complexExponentialSum_entire L p.coeff
  exact atomicOnCarrier_iff_quotientPhysicalRows A T _ _ (complexExponentialSum_entire L R.coeff) hp
    (fun a => entire_analyticOrderAt_ne_top_of_exists_ne_zero _ hp
      ⟨Complex.I, hroot Complex.I (by simp)⟩ (a : ℂ))
    (laurentInverse_locally_eq_quotient_jets L hL p R lo hi hlo hhi hmin hmax hroot
      s hR B hB T N hT harray)

/-- Both literal sets of rows characterize the image of the original
numerator map. Every admitted numerator is attained by exactly one
member of the complete broad pair space for the given two carriers. -/
theorem literalNumerator_rows_iff_existsUnique_originalPair
    [Module.Finite ℤ G] [Module.IsTorsionFree ℤ G]
    (L : G →+ ℝ) (hL : Function.Injective L) (p R : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0)
    (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p.coeff x = 0)
    (s : ℝ) (hR : (R.coeff.support : Set G) ⊆ literalNumeratorWindow L p.coeff lo hi B s) :
    ((∀ n, L n ∉ B.carrier → orderedLaurentJump p R lo hi n = 0) ∧
      quotientPhysicalRows A (complexExponentialSum L R.coeff) (complexExponentialSum L p.coeff)) ↔
    ∃! T : DistributionalMeyerPairSpace A B,
      cutArrayNumerator L p.coeff s (originalFourierArray L B T) = (fun n => R.coeff n) := by
  have hslab (r : G) (hr : r ∈ R.coeff.support) : L lo + s ≤ L r ∧ L r < L hi + s :=
    (hR hr).1
  obtain ⟨N, C, hC, V, hV, hVArray, hVNum, _⟩ :=
    exists_tempered_inverse_with_realRooted_orderedLaurentJump L hL p R lo hi hlo hhi
      hmin hmax hroot s hslab
  have hv : AtomicOnCarrier A V ↔
      quotientPhysicalRows A (complexExponentialSum L R.coeff) (complexExponentialSum L p.coeff) :=
    laurentInverse_atomicOnCarrier_iff_physicalRows L hL p R lo hi hlo hhi hmin hmax hroot
      s hslab C hC V N hV hVArray A
  have hsv (hs : ∀ n, L n ∉ B.carrier → orderedLaurentJump p R lo hi n = 0) :
      AtomicOnCarrier B (𝓕 V) ∧
      originalFourierArray L B V = orderedLaurentJump p R lo hi := by
    have hsub : C.carrier ⊆ B.carrier := by
      rw [hC]
      rintro _ ⟨n, hn, rfl⟩
      by_contra hb
      exact hn (hs n hb)
    have hat := hasLocallyAtomicAction_of_carrier_subset hsub (𝓕 V) hV.1
    refine ⟨hasLocallyAtomicAction_atomicOnCarrier B _ hat, funext fun n => ?_⟩
    rw [← hVArray n, originalFourierArray, originalFourierArray]
    classical
    by_cases hb : L n ∈ B.carrier
    · rw [extendedAtomicCoefficient, dite_eq_left hb]
      exact atomic_isolation_apply_on_larger_carrier C B hsub _
        (hasLocallyAtomicAction_atomicOnCarrier C _ hV.1) ⟨L n, hb⟩
    · simp only [extendedAtomicCoefficient, dite_eq_right hb,
        dite_eq_right (fun hc => hb (hsub hc))]
  have horder (T : DistributionalMeyerPairSpace A B)
      (ht : cutArrayNumerator L p.coeff s (originalFourierArray L B T) = (fun n => R.coeff n)) :
      originalFourierArray L B T = orderedLaurentJump p R lo hi := by
    have hT := (mem_distributionalMeyerPairSpace_iff A B _).mp T.property
    exact originalArray_eq_orderedLaurentJump L p R lo hi hlo hhi hmin hmax s _
      (originalFourierArray_frequencyLocallyFinite L hL B T)
      (originalFourierArray_annihilated L p.coeff A B T hT.1 hT.2 hA) ht
  constructor
  · rintro ⟨hs, hr⟩
    obtain ⟨hVB, hVarray⟩ := hsv hs
    let V' : DistributionalMeyerPairSpace A B := ⟨V,
      (mem_distributionalMeyerPairSpace_iff A B _).mpr ⟨hv.mpr hr, hVB⟩⟩
    refine ⟨V', ?_, ?_⟩
    · change cutArrayNumerator L p.coeff s (originalFourierArray L B V) = _
      rw [hVarray, ← funext hVArray]
      exact funext hVNum
    · intro T ht
      apply Subtype.ext
      have hT := (mem_distributionalMeyerPairSpace_iff A B _).mp T.property
      exact originalFourierArray_injective L B hB T V hT.2 hVB ((horder T ht).trans hVarray.symm)
  · rintro ⟨T, ht, _⟩
    have hT := (mem_distributionalMeyerPairSpace_iff A B _).mp T.property
    have ht' := horder T ht
    have hs (n : G) (hn : L n ∉ B.carrier) : orderedLaurentJump p R lo hi n = 0 := by
      rw [← congrFun ht' n, originalFourierArray, extendedAtomicCoefficient, dite_eq_right hn]
    obtain ⟨hVB, hVarray⟩ := hsv hs
    have heq : (T : TemperedDistribution ℝ ℂ) = V :=
      originalFourierArray_injective L B hB T V hT.2 hVB (ht'.trans hVarray.symm)
    exact ⟨hs, hv.mp (heq ▸ hT.1)⟩

end

end MeyerGeneralProblem
