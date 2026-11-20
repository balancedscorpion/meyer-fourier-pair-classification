module

public import MeyerGeneralProblem.Distribution.LaurentSpectralCosets
public import MeyerGeneralProblem.Distribution.RealRootedLaurentSlices
public import MeyerGeneralProblem.Distribution.LiteralAtomicSourceRecovery

@[expose] public section

/-!
# Actual tempered inverses for the finite spectral cosets

Restricting the literal finite numerator to one shifted coset gives an
actual tempered inverse for the corresponding original spectral array.
The sum over the active cosets reconstructs the original distribution.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped FourierTransform

variable {G : Type*} [AddCommGroup G] [Module.Finite ℤ G] [Module.IsTorsionFree ℤ G]

/-- The original source is the sum of its actual tempered coset inverses.
Each inverse carries the exact restricted spectral array and the
literal finite numerator of that coset. -/
theorem exists_realRooted_coset_inverses
    (L : G →+ ℝ) (hL : Function.Injective L) (p R : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0)
    (s : ℝ) (hR : ∀ r ∈ R.coeff.support, L lo + s ≤ L r ∧ L r < L hi + s)
    (B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier B (𝓕 T))
    (hrec : ∀ n, annihilatorArrayConvolution p.coeff (originalFourierArray L B T) n = 0)
    (hcut : cutArrayNumerator L p.coeff s (originalFourierArray L B T) =
      (fun n => R.coeff n)) :
    let H := laurentSupportDifferenceSubgroup p.coeff lo
    let χ := QuotientAddGroup.mk' H
    let u := originalFourierArray L B T
    ∃ I : Finset (G ⧸ H), ∃ (C : (G ⧸ H) → LocallyFiniteCarrier)
      (m : (G ⧸ H) → ℕ) (U : (G ⧸ H) → TemperedDistribution ℝ ℂ)
      (Q : (G ⧸ H) → AddMonoidAlgebra ℂ G),
      (↑I : Set (G ⧸ H)) = {q | ∃ n, χ n = q ∧ u n ≠ 0} ∧
      (∑ q ∈ I, U q) = T ∧
      ∀ q, (C q).carrier = L '' Function.support (laurentCosetArray H q u) ∧
        𝓕 (U q) ∈ stronglyTemperedAtomicAtExponent (C q) (m q) ∧
        (∀ n, (Q q).coeff n = laurentCosetArray H q (fun k => R.coeff (k + lo)) (n - lo)) ∧
        (∀ r ∈ (Q q).coeff.support, L lo + s ≤ L r ∧ L r < L hi + s) ∧
        originalFourierArray L (C q) (U q) = laurentCosetArray H q u ∧
        originalFourierArray L (C q) (U q) = orderedLaurentJump p (Q q) lo hi := by
  classical
  let H := laurentSupportDifferenceSubgroup p.coeff lo
  let χ := QuotientAddGroup.mk' H
  let u := originalFourierArray L B T
  let active : Set (G ⧸ H) := {q | ∃ n, χ n = q ∧ u n ≠ 0}
  have hp : p.coeff ≠ 0 := fun h => hlo (by rw [h, Finsupp.zero_apply])
  have hu := originalFourierArray_frequencyLocallyFinite L hL B T
  have hfin : active.Finite := finite_activeLaurentCosets L hL p.coeff hp lo s u hu hrec
  let I := hfin.toFinset
  let v (q : G ⧸ H) := laurentCosetArray H q u
  let Q (q : G ⧸ H) : AddMonoidAlgebra ℂ G :=
    AddMonoidAlgebra.ofCoeff (R.coeff.filter (fun n => χ (n - lo) = q))
  have hQ (q : G ⧸ H) (n : G) :
      (Q q).coeff n = if χ (n - lo) = q then R.coeff n else 0 := by
    change (R.coeff.filter _ : G →₀ ℂ) n = _
    exact Finsupp.filter_apply _ _ _
  have hQ' (q : G ⧸ H) (n : G) :
      (Q q).coeff n = laurentCosetArray H q (fun k => R.coeff (k + lo)) (n - lo) := by
    rw [hQ, laurentCosetArray]
    simp only [sub_add_cancel]
    rfl
  have hsub (q : G ⧸ H) (r : G) (hr : (Q q).coeff r ≠ 0) : R.coeff r ≠ 0 := by
    rw [hQ] at hr
    split at hr
    · exact hr
    · exact (hr rfl).elim
  have hQslab (q : G ⧸ H) (r : G) (hr : r ∈ (Q q).coeff.support) :
      L lo + s ≤ L r ∧ L r < L hi + s :=
    hR r (Finsupp.mem_support_iff.mpr (hsub q r (Finsupp.mem_support_iff.mp hr)))
  have hvc (q : G ⧸ H) (n : G) : annihilatorArrayConvolution p.coeff (v q) n = 0 := by
    rw [annihilatorArrayConvolution_laurentCosetArray p.coeff lo u n q]
    unfold laurentCosetArray
    split
    · exact hrec _
    · rfl
  have hnum (q : G ⧸ H) : cutArrayNumerator L p.coeff s (v q) = (fun n => (Q q).coeff n) := by
    funext n
    rw [cutArrayNumerator_laurentCosetArray L p.coeff lo s u q n, hQ', hcut]
  have hvloc (q : G ⧸ H) : FrequencyLocallyFinite L (v q) := by
    intro a b
    apply (hu a b).subset
    intro n hn
    refine ⟨fun h => hn.1 ?_, hn.2⟩
    unfold v laurentCosetArray
    split
    · exact h
    · rfl
  have hvjump (q : G ⧸ H) : v q = orderedLaurentJump p (Q q) lo hi :=
    originalArray_eq_orderedLaurentJump L p (Q q) lo hi hlo hhi hmin hmax s
      (v q) (hvloc q) (hvc q) (hnum q)
  have hex (q : G ⧸ H) :
      ∃ k : ℕ, ∃ C : LocallyFiniteCarrier, ∃ U : TemperedDistribution ℝ ℂ,
        C.carrier = L '' Function.support (v q) ∧
        𝓕 U ∈ stronglyTemperedAtomicAtExponent C k ∧
        originalFourierArray L C U = v q := by
    obtain ⟨k, C, hC, U, hU, harray, _, _⟩ :=
      exists_tempered_inverse_with_realRooted_orderedLaurentJump
        L hL p (Q q) lo hi hlo hhi hmin hmax hroot s (hQslab q)
    exact ⟨k, C, U, hC.trans (congrArg (fun f : G → ℂ => L '' Function.support f) (hvjump q).symm), hU,
      (funext harray).trans (hvjump q).symm⟩
  choose m C U hC hU harray using hex
  have hAtom (q : G ⧸ H) : AtomicOnCarrier (C q) (𝓕 (U q)) :=
    hasLocallyAtomicAction_atomicOnCarrier _ _ (hU q).1
  have hsubB (q : G ⧸ H) : (C q).carrier ⊆ B.carrier := by
    rw [hC]
    rintro _ ⟨n, hn, rfl⟩
    by_contra hb
    have hx : u n = 0 := by simp [u, originalFourierArray, extendedAtomicCoefficient, hb]
    apply hn
    unfold v laurentCosetArray
    split <;> simp [hx]
  have hArrayB (q : G ⧸ H) (n : G) : originalFourierArray L B (U q) n = v q n := by
    refine (show originalFourierArray L B (U q) n = originalFourierArray L (C q) (U q) n from ?_).trans
      (congrFun (harray q) n)
    unfold originalFourierArray
    by_cases hb : L n ∈ B.carrier
    · rw [extendedAtomicCoefficient, dite_eq_left hb]
      exact atomic_isolation_apply_on_larger_carrier (C q) B (hsubB q) _ (hAtom q) ⟨L n, hb⟩
    · have hc : L n ∉ (C q).carrier := fun h => hb (hsubB q h)
      simp only [extendedAtomicCoefficient, dite_eq_right hb, dite_eq_right hc]
  have hSum := map_sum temperedFourierLinearMap (fun q => U q) I
  have hAtomicSum : AtomicOnCarrier B (𝓕 (∑ q ∈ I, U q)) := by
    rw [show 𝓕 (∑ q ∈ I, U q) = ∑ q ∈ I, 𝓕 (U q) from hSum]
    intro f hf
    simp only [_root_.sum_apply]
    exact Finset.sum_eq_zero fun q _ => hAtom q f (fun x hx => hf x (hsubB q hx))
  have hFinSum (n : G) :
      originalFourierArray L B (∑ q ∈ I, U q) n = ∑ q ∈ I, originalFourierArray L B (U q) n := by
    change extendedAtomicCoefficient B (𝓕 (∑ q ∈ I, U q)) (L n) = _
    rw [show 𝓕 (∑ q ∈ I, U q) = ∑ q ∈ I, 𝓕 (U q) from hSum]
    by_cases hb : L n ∈ B.carrier <;>
      simp [originalFourierArray, extendedAtomicCoefficient, hb, _root_.sum_apply]
  refine ⟨I, C, m, U, Q, hfin.coe_toFinset, ?_,
    fun q => ⟨hC q, hU q, hQ' q, hQslab q, harray q, (harray q).trans (hvjump q)⟩⟩
  apply originalFourierArray_injective L B hB _ _ hAtomicSum hT
  funext n
  rw [hFinSum]
  simp_rw [hArrayB]
  change (∑ q ∈ I, v q n) = u n
  by_cases hn : u n = 0
  · rw [hn]
    apply Finset.sum_eq_zero
    intro q _
    unfold v laurentCosetArray
    split <;> simp [hn]
  · have hi : χ n ∈ I := hfin.mem_toFinset.mpr ⟨n, rfl, hn⟩
    rw [Finset.sum_eq_single_of_mem (χ n) hi]
    · unfold v laurentCosetArray
      rw [ite_eq_left (show (QuotientAddGroup.mk' H) n = χ n from rfl)]
    · intro q _ hq
      unfold v laurentCosetArray
      rw [ite_eq_right (Ne.symm hq)]

end

end MeyerGeneralProblem
