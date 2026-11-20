module

public import MeyerGeneralProblem.Distribution.LaurentEulerTwoSidedIndependence
public import MeyerGeneralProblem.Distribution.OriginalLaurentRealRootedCore

@[expose] public section

/-!
# The quadratic obstruction to a surviving Laurent prime

An occupied noncollinear triple in a surviving prime provides the two
Euler coordinates used in the support growth argument. A vanishing
quadratic lower count therefore cancels the full power of that prime
in the original numerator.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped FourierTransform Topology

variable {G : Type*} [AddCommGroup G]

/-- Vanishing quadratic lower count, expressed by arbitrarily large
windows for every strictly positive quadratic coefficient. -/
def VanishingQuadraticLowerArrayCount (L : G →+ ℝ) (u : G → ℂ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
    ({n : G | u n ≠ 0 ∧ L n ∈ Icc (-R) R}.ncard : ℝ) < c * R ^ 2

private theorem exists_positive_width_for_product
    (L : G →+ ℝ) (hL : Function.Injective L)
    (p q : AddMonoidAlgebra ℂ G) (m : ℕ) (hq : q ≠ 0)
    (n₀ n₁ : G) (h₀ : p.coeff n₀ ≠ 0) (h₁ : p.coeff n₁ ≠ 0) (hne : n₀ ≠ n₁) :
    let Q := p ^ (m + 1) * q
    ∃ lo hi, Q.coeff lo ≠ 0 ∧ Q.coeff hi ≠ 0 ∧
      (∀ n ∈ Q.coeff.support, L lo ≤ L n) ∧ (∀ n ∈ Q.coeff.support, L n ≤ L hi) ∧
      0 < L hi - L lo := by
  have hp' : p.coeff ≠ 0 := fun h => h₀ (by simp [h])
  have hq' : q.coeff ≠ 0 := fun h => hq (AddMonoidAlgebra.coeff_injective (by simpa using h))
  obtain ⟨p₀, p₁, hp₀, hp₁, hpB, _, _⟩ := finiteAnnihilator_extrema L hL p.coeff hp'
  obtain ⟨q₀, q₁, hq₀, hq₁, hqB, _, _⟩ := finiteAnnihilator_extrema L hL q.coeff hq'
  have hpd : 0 < L p₁ - L p₀ := by
    have hA := hpB n₀ (Finsupp.mem_support_iff.mpr h₀)
    have hB := hpB n₁ (Finsupp.mem_support_iff.mpr h₁)
    apply sub_pos.mpr
    rcases lt_or_gt_of_ne (hL.ne hne) with h | h
    · exact (hA.1.trans_lt h).trans_le hB.2
    · exact (hB.1.trans_lt h).trans_le hA.2
  have hqd : 0 ≤ L q₁ - L q₀ :=
    sub_nonneg.mpr (hqB q₀ (Finsupp.mem_support_iff.mpr hq₀)).2
  obtain ⟨hplo, hplB⟩ := laurentPower_lowerExtreme L hL p p₀ hp₀
    (fun n hn => (hpB n hn).1) (m + 1)
  obtain ⟨hphi, hphB⟩ := laurentPower_upperExtreme L hL p p₁ hp₁
    (fun n hn => (hpB n hn).2) (m + 1)
  let Q := p ^ (m + 1) * q
  let lo := (m + 1) • p₀ + q₀
  let hi := (m + 1) • p₁ + q₁
  obtain ⟨hlo, hlB⟩ := laurentProduct_lowerExtreme L hL (p ^ (m + 1)) q
    ((m + 1) • p₀) q₀ (hplo.trans_ne (pow_ne_zero _ hp₀)) hplB
    (fun n hn => (hqB n hn).1)
  obtain ⟨hhi, hhB⟩ := laurentProduct_upperExtreme L hL (p ^ (m + 1)) q
    ((m + 1) • p₁) q₁ (hphi.trans_ne (pow_ne_zero _ hp₁)) hphB
    (fun n hn => (hqB n hn).2)
  have hLo : Q.coeff lo ≠ 0 := hlo.trans_ne
    (mul_ne_zero (hplo.trans_ne (pow_ne_zero _ hp₀)) hq₀)
  have hHi : Q.coeff hi ≠ 0 := hhi.trans_ne
    (mul_ne_zero (hphi.trans_ne (pow_ne_zero _ hp₁)) hq₁)
  let D := L hi - L lo
  have he : D = (m + 1 : ℕ) * (L p₁ - L p₀) + (L q₁ - L q₀) := by
    simp only [D, hi, lo, map_add, map_nsmul, nsmul_eq_mul]
    ring
  have hD : 0 < D := by
    rw [he]
    exact add_pos_of_pos_of_nonneg (mul_pos (by positivity) hpd) hqd
  exact ⟨lo, hi, hLo, hHi, hlB, hhB, hD⟩

/-- A surviving prime with a two-dimensional support projection forces
the exact quadratic lower count for the original array. -/
theorem exists_quadratic_lowerCount_of_survivingPrime
    (L : G →+ ℝ) (hL : Function.Injective L)
    (p q r : AddMonoidAlgebra ℂ G) (m a : ℕ) (ha : a < m + 1)
    (hp : Prime p) (hq : ¬ p ∣ q) (hr : ¬ p ∣ r)
    (e f : G →+ ℂ) (n₀ n₁ n₂ : G) (h₀ : p.coeff n₀ ≠ 0) (h₁ : p.coeff n₁ ≠ 0)
    (h₂ : p.coeff n₂ ≠ 0)
    (hdet : (e n₁ - e n₀) * (f n₂ - f n₀) - (e n₂ - e n₀) * (f n₁ - f n₀) ≠ 0)
    (s : ℝ) (u : G → ℂ) (hu : FrequencyLocallyFinite L u)
    (hconv : annihilatorArrayConvolution (p ^ (m + 1) * q).coeff u = 0)
    (hcut : cutArrayNumerator L (p ^ (m + 1) * q).coeff s u = (p ^ a * r).coeff) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, c < 2 / D ^ 2 → ∀ᶠ R : ℝ in atTop,
      c * R ^ 2 ≤ ({n : G | u n ≠ 0 ∧ L n ∈ Icc (-R) R}.ncard : ℝ) := by
  let Q := p ^ (m + 1) * q
  have hq' : q ≠ 0 := fun h => hq (by rw [h]; exact dvd_zero _)
  have hne : n₀ ≠ n₁ := by
    intro h
    subst n₁
    exact hdet (by simp)
  obtain ⟨lo, hi, hLo, hHi, hlB, hhB, hD⟩ :=
    exists_positive_width_for_product L hL p q m hq' n₀ n₁ h₀ h₁ hne
  let D := L hi - L lo
  let b : Fin 2 → G →+ ℂ := Fin.cases e (fun _ => f)
  have hw (k : ℕ) (t : ℝ) : (2 + k).choose k ≤
      {n : G | u n ≠ 0 ∧ L n ∈ Ico t (t + (k + 1 : ℕ) * D)}.ncard := by
    have hLI : LinearIndependent ℂ (fun i : Sym (Option (Fin 2)) k =>
        laurentEulerMonomial b i u) := linearIndependent_twoEuler_of_survivingPrime
      L hL p q r m a ha hp hq hr e f n₀ n₁ n₂ h₀ h₁ h₂ hdet s u hcut k
    have h := choose_le_occupied_eulerWindow_of_independent
      L hL Q lo hi hLo hHi hlB hhB u hu hconv b k t hLI
    simpa only [Fintype.card_fin] using h
  exact ⟨D, hD, fun c hc =>
    eventually_quadratic_le_occupied_centeredCount L u D hD 2 le_rfl hw hu c hc⟩

private theorem factor_of_not_dvd_pow (p R : AddMonoidAlgebra ℂ G) (j : ℕ)
    (h : ¬ p ^ j ∣ R) : ∃ a < j, ∃ r, R = p ^ a * r ∧ ¬ p ∣ r := by
  induction j generalizing R with
  | zero => exact (h (by simp)).elim
  | succ j ih =>
    by_cases hp : p ∣ R
    · obtain ⟨r, rfl⟩ := hp
      have hn : ¬ p ^ j ∣ r := by
        rintro ⟨w, rfl⟩
        exact h ⟨w, by rw [pow_succ']; ring⟩
      obtain ⟨a, ha, w, hw, hpw⟩ := ih r hn
      exact ⟨a + 1, by omega, w, by rw [hw, pow_succ', mul_assoc], hpw⟩
    · exact ⟨0, by omega, R, by simp, hp⟩

/-- The full multiplicity of any prime with a noncollinear triple
divides the literal numerator at a cut when the quadratic lower count
of the original array vanishes. -/
theorem primePower_dvd_cutNumerator_of_vanishingQuadraticLowerCount
    (L : G →+ ℝ) (hL : Function.Injective L)
    (p q R : AddMonoidAlgebra ℂ G) (m : ℕ) (hp : Prime p) (hq : ¬ p ∣ q)
    (e f : G →+ ℂ) (n₀ n₁ n₂ : G) (h₀ : p.coeff n₀ ≠ 0) (h₁ : p.coeff n₁ ≠ 0)
    (h₂ : p.coeff n₂ ≠ 0)
    (hdet : (e n₁ - e n₀) * (f n₂ - f n₀) - (e n₂ - e n₀) * (f n₁ - f n₀) ≠ 0)
    (s : ℝ) (u : G → ℂ) (hu : FrequencyLocallyFinite L u)
    (hconv : annihilatorArrayConvolution (p ^ (m + 1) * q).coeff u = 0)
    (hcut : cutArrayNumerator L (p ^ (m + 1) * q).coeff s u = R.coeff)
    (hcount : VanishingQuadraticLowerArrayCount L u) : p ^ (m + 1) ∣ R := by
  by_contra hn
  obtain ⟨a, ha, r, hr, hpr⟩ := factor_of_not_dvd_pow p R (m + 1) hn
  rw [hr] at hcut
  obtain ⟨D, hD, hbound⟩ := exists_quadratic_lowerCount_of_survivingPrime L hL
    p q r m a ha hp hq hpr e f n₀ n₁ n₂ h₀ h₁ h₂ hdet s u hu hconv hcut
  let c := 1 / D ^ 2
  have hcp : 0 < c := by dsimp [c]; positivity
  have hct : c < 2 / D ^ 2 := by
    dsimp [c]
    exact div_lt_div_of_pos_right (by norm_num) (by positivity)
  obtain ⟨_, hsmall, hlarge⟩ := ((hcount c hcp).and_eventually (hbound c hct)).exists
  exact hsmall.not_ge hlarge

/-- Cancelling the full obstructing prime factor preserves the recurrence
of the whole original array and its literal reduced numerator. -/
theorem laurentRecurrence_cancel_primePower_of_vanishingQuadraticLowerCount
    (L : G →+ ℝ) (hL : Function.Injective L)
    (p q R : AddMonoidAlgebra ℂ G) (m : ℕ) (hp : Prime p) (hq : ¬ p ∣ q)
    (e f : G →+ ℂ) (n₀ n₁ n₂ : G) (h₀ : p.coeff n₀ ≠ 0) (h₁ : p.coeff n₁ ≠ 0)
    (h₂ : p.coeff n₂ ≠ 0)
    (hdet : (e n₁ - e n₀) * (f n₂ - f n₀) - (e n₂ - e n₀) * (f n₁ - f n₀) ≠ 0)
    (s : ℝ) (u : G → ℂ) (hu : FrequencyLocallyFinite L u)
    (hconv : annihilatorArrayConvolution (p ^ (m + 1) * q).coeff u = 0)
    (hcut : cutArrayNumerator L (p ^ (m + 1) * q).coeff s u = R.coeff)
    (hcount : VanishingQuadraticLowerArrayCount L u) :
    (∀ n, annihilatorArrayConvolution q.coeff u n = 0) ∧
      ∃ S : AddMonoidAlgebra ℂ G, cutArrayNumerator L q.coeff s u = S.coeff := by
  obtain ⟨S, hS⟩ := primePower_dvd_cutNumerator_of_vanishingQuadraticLowerCount L hL
    p q R m hp hq e f n₀ n₁ n₂ h₀ h₁ h₂ hdet s u hu hconv hcut hcount
  obtain ⟨_, b, _, hb, hB, _, _⟩ :=
    finiteAnnihilator_extrema L hL p.coeff (fun h => h₀ (by simp [h]))
  have hz : (p ^ (m + 1)).coeff ≠ 0 := by
    intro h
    have he := (laurentPower_upperExtreme L hL p b hb
      (fun n hn => (hB n hn).2) (m + 1)).1
    have hne := he.trans_ne (pow_ne_zero (m + 1) hb)
    exact hne (by rw [h]; rfl)
  obtain ⟨hrec, hnum⟩ := laurentRecurrence_cancel_common_factor L hL
    (p ^ (m + 1)) q S hz u hu s (congrFun hconv) (by simpa only [hS] using hcut)
  exact ⟨hrec, S, hnum⟩

/-- The actual Fourier array inherits every arbitrarily small quadratic
count bound of its locally finite Fourier carrier. -/
theorem vanishingQuadraticLowerArrayCount_originalFourierArray
    (L : G →+ ℝ) (hL : Function.Injective L) (B : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ)
    (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((B.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    VanishingQuadraticLowerArrayCount L (originalFourierArray L B T) := by
  intro c hc
  refine (hcount c hc).mono fun R hR => lt_of_le_of_lt ?_ hR
  let W := {n : G | originalFourierArray L B T n ≠ 0 ∧ L n ∈ Icc (-R) R}
  have hsub : L '' W ⊆ B.carrier ∩ Icc (-R) R := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨?_, hn.2⟩
    by_contra h
    exact hn.1 (by simp [originalFourierArray, extendedAtomicCoefficient, h])
  have hle : W.ncard ≤ (B.carrier ∩ Icc (-R) R).ncard := by
    rw [← Set.ncard_image_of_injective W hL]
    exact Set.ncard_le_ncard hsub (B.finite_inter_Icc _ _)
  exact_mod_cast hle

/-- Removing a specified high-rank prime power from a Laurent annihilator
preserves support of the same original source on the remaining zero carrier. -/
theorem originalPair_atomicOn_zeroSubcarrier_after_quadratic_prime_removal
    (L : G →+ ℝ) (hL : Function.Injective L)
    (p q : AddMonoidAlgebra ℂ G) (m : ℕ) (hp : Prime p) (hq : ¬ p ∣ q)
    (e f : G →+ ℂ) (n₀ n₁ n₂ : G) (h₀ : p.coeff n₀ ≠ 0) (h₁ : p.coeff n₁ ≠ 0)
    (h₂ : p.coeff n₂ ≠ 0)
    (hdet : (e n₁ - e n₀) * (f n₂ - f n₀) - (e n₂ - e n₀) * (f n₁ - f n₀) ≠ 0)
    (A B : LocallyFiniteCarrier) (hmodule : B.carrier ⊆ range L)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (hFT : AtomicOnCarrier B (𝓕 T))
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L (p ^ (m + 1) * q).coeff x = 0)
    (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((B.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    AtomicOnCarrier (annihilatorZeroSubcarrier L q.coeff A) T := by
  let P := p ^ (m + 1) * q
  let u := originalFourierArray L B T
  have hq' : q ≠ 0 := fun h => hq (h ▸ dvd_zero p)
  have hpow (j : ℕ) : p ^ j ≠ 0 := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ]; exact laurent_mul_ne_zero_of_injective L hL ih hp.ne_zero
  have hP : P ≠ 0 := laurent_mul_ne_zero_of_injective L hL (hpow (m + 1)) hq'
  have hP' : P.coeff ≠ 0 := fun h => hP (AddMonoidAlgebra.coeff_injective (by simpa using h))
  obtain ⟨R, hR⟩ := originalFourierPair_exists_finite_numerator L hL P.coeff hP'
    A B T hT hFT hA 0
  have hcut : cutArrayNumerator L P.coeff 0 u = R := funext fun n => (hR n).1.symm
  have hconv : annihilatorArrayConvolution P.coeff u = 0 :=
    funext (originalFourierArray_annihilated L P.coeff A B T hT hFT hA)
  have hR := laurentRecurrence_cancel_primePower_of_vanishingQuadraticLowerCount L hL
    p q (AddMonoidAlgebra.ofCoeff R) m hp hq e f n₀ n₁ n₂ h₀ h₁ h₂ hdet
    0 u (originalFourierArray_frequencyLocallyFinite L hL B T) hconv hcut
    (vanishingQuadraticLowerArrayCount_originalFourierArray L hL B T hcount)
  exact originalPair_atomicOn_zeroSubcarrier_of_arrayRecurrence L hL q A B hmodule T hT hFT hR.1

/-- Removing the specified prime power preserves the complete original
pair space on the prescribed carriers. -/
theorem distributionalMeyerPairSpace_eq_after_quadratic_prime_removal
    (L : G →+ ℝ) (hL : Function.Injective L)
    (p q : AddMonoidAlgebra ℂ G) (m : ℕ) (hp : Prime p) (hq : ¬ p ∣ q)
    (e f : G →+ ℂ) (n₀ n₁ n₂ : G) (h₀ : p.coeff n₀ ≠ 0) (h₁ : p.coeff n₁ ≠ 0)
    (h₂ : p.coeff n₂ ≠ 0)
    (hdet : (e n₁ - e n₀) * (f n₂ - f n₀) - (e n₂ - e n₀) * (f n₁ - f n₀) ≠ 0)
    (A B : LocallyFiniteCarrier) (hmodule : B.carrier ⊆ range L)
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L (p ^ (m + 1) * q).coeff x = 0)
    (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((B.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    DistributionalMeyerPairSpace A B =
      DistributionalMeyerPairSpace (annihilatorZeroSubcarrier L q.coeff A) B := by
  ext T
  rw [mem_distributionalMeyerPairSpace_iff, mem_distributionalMeyerPairSpace_iff]
  constructor
  · rintro ⟨hT, hFT⟩
    exact ⟨originalPair_atomicOn_zeroSubcarrier_after_quadratic_prime_removal L hL
      p q m hp hq e f n₀ n₁ n₂ h₀ h₁ h₂ hdet A B hmodule T hT hFT hA hcount, hFT⟩
  · rintro ⟨hT, hFT⟩
    have hsub : (annihilatorZeroSubcarrier L q.coeff A).carrier ⊆ A.carrier :=
      fun _ hx => hx.1
    exact ⟨hT.mono hsub, hFT⟩

end

end MeyerGeneralProblem
