module

public import MeyerGeneralProblem.Distribution.LaurentJumpPresentation
public import MeyerGeneralProblem.Distribution.PairedMeyerSpace

@[expose] public section

/-!
# The literal finite Laurent numerator window

Both spectral cuts contribute to the coordinate set. It is defined
from the carrier and the whole denominator, before looking at a source.
The original numerator embeds the entire paired space into this finite
coordinate space.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped FourierTransform

variable {G : Type*} [AddCommGroup G]

/-- The intersection of the half-open slab with the two literal shifted
allowed spectral windows. -/
def literalNumeratorWindow (L : G →+ ℝ) (p : G →₀ ℂ) (lo hi : G)
    (B : LocallyFiniteCarrier) (s : ℝ) : Set G :=
  {n | L n ∈ Ico (L lo + s) (L hi + s) ∧
    (∃ m ∈ p.support, L (n - m) ∈ B.carrier ∧ s ≤ L (n - m)) ∧
    (∃ m ∈ p.support, L (n - m) ∈ B.carrier ∧ L (n - m) < s)}

/-- The literal numerator window is finite even if the whole group is dense. -/
theorem literalNumeratorWindow_finite (L : G →+ ℝ) (hL : Function.Injective L)
    (p : G →₀ ℂ) (lo hi : G) (hlo : ∀ m ∈ p.support, L lo ≤ L m)
    (B : LocallyFiniteCarrier) (s : ℝ) :
    (literalNumeratorWindow L p lo hi B s).Finite := by
  let W := L ⁻¹' (B.carrier ∩ Icc s (s + L hi - L lo))
  have hW : W.Finite := (B.finite_inter_Icc _ _).preimage (hL.injOn)
  apply (p.support.finite_toSet.biUnion (fun m _ => hW.image (fun w => m + w))).subset
  rintro n ⟨hn, ⟨m, hm, hBm, hsm⟩, _⟩
  refine mem_biUnion hm ⟨n - m, ⟨hBm, hsm, ?_⟩, by change m + (n - m) = n; rw [add_comm, sub_add_cancel]⟩
  rw [map_sub]
  linarith [hn.2, hlo m hm]

/-- A nonzero original numerator coefficient belongs to both shifted
spectral sets, by the exact two original convolution identities. -/
theorem cutArrayNumerator_support_subset_literalNumeratorWindow
    (L : G →+ ℝ) (p : G →₀ ℂ) (lo hi : G)
    (hlo : ∀ m ∈ p.support, L lo ≤ L m) (hhi : ∀ m ∈ p.support, L m ≤ L hi)
    (B : LocallyFiniteCarrier) (s : ℝ) (u : G → ℂ)
    (hB : ∀ n, u n ≠ 0 → L n ∈ B.carrier)
    (hconv : ∀ n, annihilatorArrayConvolution p u n = 0) :
    Function.support (cutArrayNumerator L p s u) ⊆ literalNumeratorWindow L p lo hi B s := by
  classical
  intro n hn
  have hpos : annihilatorArrayConvolution p (arrayPositiveCut L s u) n ≠ 0 := hn
  have hneg : annihilatorArrayConvolution p (arrayNegativeCut L s u) n ≠ 0 := by
    intro h
    apply hn
    rw [cutArrayNumerator_eq_negative L p s u hconv, h, neg_zero]
  obtain ⟨m, hm, h₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
  obtain ⟨k, hk, h₂⟩ := Finset.exists_ne_zero_of_sum_ne_zero hneg
  have hc₁ := (mul_ne_zero_iff.mp h₁).2
  have hc₂ := (mul_ne_zero_iff.mp h₂).2
  have hp : s ≤ L (n - m) := by by_contra h; exact hc₁ (by simp only [arrayPositiveCut, ite_eq_right h])
  have hq : L (n - k) < s := by by_contra h; exact hc₂ (by simp only [arrayNegativeCut, ite_eq_right h])
  have hu₁ : u (n - m) ≠ 0 := by simpa only [arrayPositiveCut, ite_eq_left hp] using hc₁
  have hu₂ : u (n - k) ≠ 0 := by simpa only [arrayNegativeCut, ite_eq_left hq] using hc₂
  exact ⟨cutArrayNumerator_support_slab L p s (L lo) (L hi) hlo hhi u hconv hn,
    ⟨m, hm, hB _ hu₁, hp⟩, ⟨k, hk, hB _ hu₂, hq⟩⟩

def zeroExtendedCoefficientLinearMap
    (B : LocallyFiniteCarrier) (x : ℝ) : TemperedDistribution ℝ ℂ →ₗ[ℂ] ℂ := by
  classical
  exact if hx : x ∈ B.carrier then atomicCoefficientLinearMap B ⟨x, hx⟩ else 0

private theorem zeroExtendedCoefficientLinearMap_apply (B : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (x : ℝ) :
    zeroExtendedCoefficientLinearMap B x T = extendedAtomicCoefficient B T x := by
  classical
  by_cases hx : x ∈ B.carrier
  · rw [zeroExtendedCoefficientLinearMap, dite_eq_left hx, extendedAtomicCoefficient, dite_eq_left hx]
    rfl
  · simp [zeroExtendedCoefficientLinearMap, extendedAtomicCoefficient, hx]

def positiveCutObservation (L : G →+ ℝ) (B : LocallyFiniteCarrier)
    (s : ℝ) (k : G) : TemperedDistribution ℝ ℂ →ₗ[ℂ] ℂ := by
  classical
  exact if s ≤ L k then (zeroExtendedCoefficientLinearMap B (L k)).comp temperedFourierLinearMap else 0

private theorem positiveCutObservation_apply (L : G →+ ℝ) (B : LocallyFiniteCarrier)
    (s : ℝ) (k : G) (U : TemperedDistribution ℝ ℂ) :
    positiveCutObservation L B s k U = arrayPositiveCut L s (originalFourierArray L B U) k := by
  classical
  by_cases h : s ≤ L k <;>
    simp [positiveCutObservation, arrayPositiveCut, h, zeroExtendedCoefficientLinearMap_apply,
      originalFourierArray]

/-- The actual numerator at one label is the linear combination of its
original spectral coefficient observations. -/
def originalNumeratorRow (L : G →+ ℝ) (p : G →₀ ℂ) (B : LocallyFiniteCarrier) (s : ℝ)
    (n : G) : TemperedDistribution ℝ ℂ →ₗ[ℂ] ℂ :=
  ∑ m ∈ p.support, p m • positiveCutObservation L B s (n - m)

theorem originalNumeratorRow_apply (L : G →+ ℝ) (p : G →₀ ℂ) (B : LocallyFiniteCarrier)
    (s : ℝ) (n : G) (U : TemperedDistribution ℝ ℂ) :
    originalNumeratorRow L p B s n U = cutArrayNumerator L p s (originalFourierArray L B U) n := by
  simp only [originalNumeratorRow, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    positiveCutObservation_apply, cutArrayNumerator, annihilatorArrayConvolution]

/-- The complete original numerator map into the literal allowed
finite coordinate space. -/
def originalPairLiteralNumeratorMap (L : G →+ ℝ) (p : G →₀ ℂ) (lo hi : G)
    (A B : LocallyFiniteCarrier) (s : ℝ) :
    DistributionalMeyerPairSpace A B →ₗ[ℂ] (literalNumeratorWindow L p lo hi B s → ℂ) :=
  LinearMap.pi fun n =>
    (originalNumeratorRow L p B s n).comp (DistributionalMeyerPairSpace A B).subtype

/-- Every original source is determined by its exact Laurent numerator on
the literal window, with no real-rootedness or growth assumption. -/
theorem originalPairLiteralNumeratorMap_injective
    (L : G →+ ℝ) (hL : Function.Injective L) (p : G →₀ ℂ) (hp : p ≠ 0) (lo hi : G)
    (hlo : ∀ m ∈ p.support, L lo ≤ L m) (hhi : ∀ m ∈ p.support, L m ≤ L hi)
    (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (hz : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p x = 0) (s : ℝ) :
    Function.Injective (originalPairLiteralNumeratorMap L p lo hi A B s) := by
  intro U V hUV
  apply Subtype.ext
  have hU := (mem_distributionalMeyerPairSpace_iff A B _).mp U.property
  have hV := (mem_distributionalMeyerPairSpace_iff A B _).mp V.property
  apply originalFourierPair_cutNumerator_injective L hL p hp A B hB _ _ hU.1 hV.1 hU.2 hV.2 hz s
  have hs (T : DistributionalMeyerPairSpace A B) :
      Function.support (cutArrayNumerator L p s (originalFourierArray L B T)) ⊆
        literalNumeratorWindow L p lo hi B s := by
    have hT := (mem_distributionalMeyerPairSpace_iff A B _).mp T.property
    apply cutArrayNumerator_support_subset_literalNumeratorWindow L p lo hi hlo hhi B s
    · intro n hn
      by_contra hb
      exact hn (by simp [originalFourierArray, extendedAtomicCoefficient, hb])
    · exact originalFourierArray_annihilated L p A B _ hT.1 hT.2 hz
  funext n
  by_cases hn : n ∈ literalNumeratorWindow L p lo hi B s
  · have hh := congrFun hUV ⟨n, hn⟩
    change originalNumeratorRow L p B s n U = originalNumeratorRow L p B s n V at hh
    simpa only [originalNumeratorRow_apply] using hh
  · have hzero (T : DistributionalMeyerPairSpace A B) :
        cutArrayNumerator L p s (originalFourierArray L B T) n = 0 := by
      by_contra h; exact hn (hs T h)
    rw [hzero U, hzero V]

/-- Every numerator in the literal finite window satisfying the Fourier
exclusion rows has a unique locally finite formal array supported on
the allowed spectrum. This is the exact algebraic spectral step of the
row presentation, before the physical distribution is synthesized. -/
theorem literalNumerator_spectralRows_iff_exists_unique_array
    (L : G →+ ℝ) (p R : AddMonoidAlgebra ℂ G) (lo hi : G)
    (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ m ∈ p.coeff.support, m ≠ lo → L lo < L m)
    (hmax : ∀ m ∈ p.coeff.support, m ≠ hi → L m < L hi)
    (B : LocallyFiniteCarrier) (s : ℝ)
    (hR : (R.coeff.support : Set G) ⊆ literalNumeratorWindow L p.coeff lo hi B s) :
    (∀ n, L n ∉ B.carrier → orderedLaurentJump p R lo hi n = 0) ↔
      ∃! u : G → ℂ, FrequencyLocallyFinite L u ∧
        (∀ n, L n ∉ B.carrier → u n = 0) ∧
        (∀ n, annihilatorArrayConvolution p.coeff u n = 0) ∧
        cutArrayNumerator L p.coeff s u = (fun n => R.coeff n) := by
  have hslab (r : G) (hr : r ∈ R.coeff.support) : L lo + s ≤ L r ∧ L r < L hi + s :=
    (hR hr).1
  obtain ⟨hf, hconv, _, _, hnum⟩ :=
    orderedLaurentJump_exact_cuts L p R lo hi hlo hhi hmin hmax s hslab
  constructor
  · intro h
    refine ⟨orderedLaurentJump p R lo hi, ⟨hf, h, hconv, hnum⟩, ?_⟩
    rintro u ⟨huf, _, huc, hun⟩
    exact originalArray_eq_orderedLaurentJump L p R lo hi hlo hhi hmin hmax s u huf huc hun
  · rintro ⟨u, ⟨huf, hus, huc, hun⟩, _⟩
    rw [← originalArray_eq_orderedLaurentJump L p R lo hi hlo hhi hmin hmax s u huf huc hun]
    exact hus

/-- The literal algebraic numerator bound applies to the entire original
broad pair space, even when neither allowed carrier has bounded local counts. -/
theorem originalPair_finrank_le_literalNumeratorWindow
    (L : G →+ ℝ) (hL : Function.Injective L) (p : G →₀ ℂ) (hp : p ≠ 0) (lo hi : G)
    (hlo : ∀ m ∈ p.support, L lo ≤ L m) (hhi : ∀ m ∈ p.support, L m ≤ L hi)
    (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (hz : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p x = 0) (s : ℝ) :
    let W := literalNumeratorWindow L p lo hi B s
    FiniteDimensional ℂ (DistributionalMeyerPairSpace A B) ∧
      Module.finrank ℂ (DistributionalMeyerPairSpace A B) ≤ W.ncard := by
  let W := literalNumeratorWindow L p lo hi B s
  let _ : Fintype W := (literalNumeratorWindow_finite L hL p lo hi hlo B s).fintype
  have hinj := originalPairLiteralNumeratorMap_injective L hL p hp lo hi hlo hhi A B hB hz s
  refine ⟨FiniteDimensional.of_injective (originalPairLiteralNumeratorMap L p lo hi A B s) hinj, ?_⟩
  simpa only [Module.finrank_fintype_fun_eq_card, Set.fintypeCard_eq_ncard] using
    LinearMap.finrank_le_finrank_of_injective hinj

end

end MeyerGeneralProblem
