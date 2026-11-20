module

public import MeyerGeneralProblem.Distribution.RealRootedCosetInverses
public import MeyerGeneralProblem.Distribution.CombinedDiracJetRows
public import MeyerGeneralProblem.Distribution.LaurentBoundary
public import MeyerGeneralProblem.Distribution.QuotientPhysicalRows

@[expose] public section

/-!
# Combined physical jets of the actual normalized coset inverses

Each actual coset inverse has a local Dirac jet obtained from its
Laurent quotient. Removing and restoring the coset modulation gives
the combined physical coefficients of the original distribution.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Set
open scoped FourierTransform

variable {G : Type*} [AddCommGroup G]

private theorem diracJets_of_realRootedLaurentInverse
    (L : G →+ ℝ) (hL : Function.Injective L) (p R : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0)
    (s : ℝ) (hR : ∀ r ∈ R.coeff.support, L lo + s ≤ L r ∧ L r < L hi + s)
    (B : LocallyFiniteCarrier) (hB : B.carrier = L '' Function.support (orderedLaurentJump p R lo hi))
    (T : TemperedDistribution ℝ ℂ) (m : ℕ) (hT : 𝓕 T ∈ stronglyTemperedAtomicAtExponent B m)
    (harray : ∀ n, originalFourierArray L B T n = orderedLaurentJump p R lo hi n)
    (x : ℝ) :
    let N := analyticOrderNatAt (complexExponentialSum L p.coeff) (x : ℂ)
    ∃ δ : ℝ, 0 < δ ∧ ∃ d : ℕ → ℂ,
      ∀ f : SchwartzMap ℝ ℂ, (∀ y : ℝ, f y ≠ 0 → |y - x| ≤ δ) →
        T f = (∑ k ∈ Finset.range N, d k • localDiracDerivative k x) f := by
  obtain ⟨δ, hδ, r, _, _, _, hact⟩ := laurentInverse_locally_eq_quotient_jets
    L hL p R lo hi hlo hhi hmin hmax hroot s hR B hB T m hT harray x
  let C : ℂ := -2 * (Real.pi : ℂ) * Complex.I
  let d (k : ℕ) : ℂ := r k * (C / (k.factorial : ℂ)) * (-1) ^ k
  refine ⟨δ, hδ, d, fun f hf => ?_⟩
  rw [hact f hf]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul, localDiracDerivative_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  change r k * (C * iteratedDeriv k f x / (k.factorial : ℂ)) =
    (r k * (C / (k.factorial : ℂ)) * (-1) ^ k) * ((-1) ^ k * iteratedDeriv k f x)
  calc
    _ = (r k * (C / (k.factorial : ℂ))) *
        ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * iteratedDeriv k f x := by
      rw [hsign, mul_one]
      ring
    _ = _ := by ac_rfl

/-- Opposite physical modulation shifts cancel on the original distribution. -/
theorem combDistributionModulation_neg_apply (a : ℝ) (T : TemperedDistribution ℝ ℂ) :
    combDistributionModulation a (combDistributionModulation (-a) T) = T := by
  ext f
  simp only [combDistributionModulation_apply]
  congr 1
  ext x
  rw [combSchwartzModulation_apply, combSchwartzModulation_apply, ← mul_assoc,
    ← combModulationCharacter_add_left, neg_add_cancel, combModulationCharacter_zero_left, one_mul]

private theorem modulation_preserves_test_support (a : ℝ) (f : SchwartzMap ℝ ℂ)
    (x δ : ℝ) (hf : ∀ y : ℝ, f y ≠ 0 → |y - x| ≤ δ) :
    ∀ y : ℝ, combSchwartzModulation a f y ≠ 0 → |y - x| ≤ δ := by
  intro y hy
  rw [combSchwartzModulation_apply] at hy
  exact hf y (mul_ne_zero_iff.mp hy).2

/-- Once the actual local actions have been reconstructed, the common
physical carrier condition is equivalent to the combined coset rows.
All higher derivatives are forbidden, and the value row is forbidden
exactly at points outside the proposed carrier. -/
theorem atomicOnCarrier_iff_combined_local_coset_rows
    {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (N : ℝ → ℕ) (d : ℝ → ι → ℕ → ℂ)
    (hlocal : ∀ x : ℝ, ∃ δ : ℝ, 0 < δ ∧
      ∀ f : SchwartzMap ℝ ℂ, (∀ y : ℝ, f y ≠ 0 → |y - x| ≤ δ) →
        T f = (∑ k ∈ Finset.range (N x),
          combinedDiracJetCoefficient a x (N x) (d x) k • localDiracDerivative k x) f) :
    AtomicOnCarrier A T ↔
      ∀ x k, k < N x → (k ≠ 0 ∨ x ∉ A.carrier) →
        combinedDiracJetCoefficient a x (N x) (d x) k = 0 := by
  classical
  constructor
  · intro hT x k hk hforbid
    obtain ⟨δ, hδ, hδval⟩ := hlocal x
    let b (j : ℕ) := combinedDiracJetCoefficient a x (N x) (d x) j
    let C : ℂ := -2 * (Real.pi : ℂ) * Complex.I
    have hC : C ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have hF (j : ℕ) : (j.factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero j
    let r (j : ℕ) := b j * (-1 : ℂ) ^ j * ((j.factorial : ℂ) / C)
    have hr (f : SchwartzMap ℝ ℂ) (hf : ∀ y : ℝ, f y ≠ 0 → |y - x| ≤ δ) :
        T f = ∑ j ∈ Finset.range (N x),
          r j * ((-2 * (Real.pi : ℂ) * Complex.I) * iteratedDeriv j f x / (j.factorial : ℂ)) := by
      rw [hδval f hf]
      simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul, localDiracDerivative_apply]
      apply Finset.sum_congr rfl
      intro j _
      change b j * ((-1 : ℂ) ^ j * iteratedDeriv j f x) =
        (b j * (-1 : ℂ) ^ j * ((j.factorial : ℂ) / C)) *
          (C * iteratedDeriv j f x / (j.factorial : ℂ))
      field_simp [hC, hF j]
    have hz : r k = 0 := localJetCoefficient_eq_zero_of_atomic A T hT x δ hδ (N x)
      r hr k hk hforbid
    exact ((mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right
      (div_ne_zero (hF k) hC))).resolve_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))
  · intro h
    apply atomicOnCarrier_of_locally_annihilates A T
    intro x
    obtain ⟨δ, hδ, hδval⟩ := hlocal x
    refine ⟨δ, hδ, fun f hf hv => ?_⟩
    rw [hδval f hf]
    simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hkbad : k ≠ 0 ∨ x ∉ A.carrier
    · rw [h x k (Finset.mem_range.mp hk) hkbad, zero_mul]
    · push Not at hkbad
      rw [hkbad.1, localDiracDerivative_apply, iteratedDeriv_zero, hv x hkbad.2, mul_zero, mul_zero]

/-- The local jets of the normalized actual spectral cosets add, after
modulation, to the original physical action. The coset translations
are representatives in the exact original spectral module. -/
theorem exists_original_combined_coset_physical_jets
    [Module.Finite ℤ G] [Module.IsTorsionFree ℤ G]
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
    let N (x : ℝ) := analyticOrderNatAt (complexExponentialSum L p.coeff) (x : ℂ)
    ∃ (I : Finset (G ⧸ H)) (c : I → G) (U : I → TemperedDistribution ℝ ℂ)
      (B₀ : I → LocallyFiniteCarrier) (d : ℝ → I → ℕ → ℂ),
      (↑I : Set (G ⧸ H)) = {q | ∃ n, χ n = q ∧ u n ≠ 0} ∧
      (∀ q, χ (c q) = q.val) ∧
      (∀ q, (B₀ q).carrier ⊆ L '' (H : Set G) ∧ AtomicOnCarrier (B₀ q) (𝓕 (U q))) ∧
      (∑ q, combDistributionModulation (L (c q)) (U q)) = T ∧
      (∀ x : ℝ, ∃ δ : ℝ, 0 < δ ∧
        (∀ q f, (∀ y : ℝ, f y ≠ 0 → |y - x| ≤ δ) →
          U q f = (∑ k ∈ Finset.range (N x), d x q k • localDiracDerivative k x) f) ∧
        ∀ f : SchwartzMap ℝ ℂ, (∀ y : ℝ, f y ≠ 0 → |y - x| ≤ δ) →
          T f = (∑ k ∈ Finset.range (N x),
            combinedDiracJetCoefficient (fun q => L (c q)) x (N x) (d x) k •
              localDiracDerivative k x) f) ∧
      ∀ A : LocallyFiniteCarrier, AtomicOnCarrier A T ↔
        ∀ x k, k < N x → (k ≠ 0 ∨ x ∉ A.carrier) →
          combinedDiracJetCoefficient (fun q => L (c q)) x (N x) (d x) k = 0 := by
  classical
  let H := laurentSupportDifferenceSubgroup p.coeff lo
  let χ := QuotientAddGroup.mk' H
  obtain ⟨I, C, m, V, Q, hI, hsum, hq⟩ := exists_realRooted_coset_inverses
    L hL p R lo hi hlo hhi hmin hmax hroot s hR B hB T hT hrec hcut
  have hrepr (q : I) : ∃ a : G, χ a = q.val := QuotientAddGroup.mk'_surjective H q.val
  choose c hc using hrepr
  let U (q : I) : TemperedDistribution ℝ ℂ := combDistributionModulation (-L (c q)) (V q)
  have hmod : (∑ q : I, combDistributionModulation (L (c q)) (U q)) = T := by
    calc
      _ = ∑ q : I, V q := by
        apply Finset.sum_congr rfl
        intro q _
        exact combDistributionModulation_neg_apply (L (c q)) (V q)
      _ = T := by rw [I.sum_coe_sort V, hsum]
  let B₀ (q : I) := (C q).translate (-L (c q))
  have hB₀ (q : I) : (B₀ q).carrier ⊆ L '' (H : Set G) ∧
      AtomicOnCarrier (B₀ q) (𝓕 (U q)) := by
    obtain ⟨hC, hV, _, _, _, _⟩ := hq q
    constructor
    · rintro y ⟨w, hw, rfl⟩
      obtain ⟨n, hn, rfl⟩ := hC ▸ hw
      have hclass : χ n = q.val := by
        by_contra h
        apply hn
        unfold laurentCosetArray
        rw [ite_eq_right h]
      refine ⟨n - c q, QuotientAddGroup.eq_iff_sub_mem.mp (hclass.trans (hc q).symm), ?_⟩
      rw [map_sub, sub_eq_add_neg, add_comm]
    · change AtomicOnCarrier (B₀ q) (𝓕 (combDistributionModulation (-L (c q)) (V q)))
      rw [MeyerGeneralProblem.fourier_combDistributionModulation]
      exact atomicOnCarrier_combDistributionTranslation (C q) _
        (hasLocallyAtomicAction_atomicOnCarrier _ _ hV.1) _
  let order (x : ℝ) := analyticOrderNatAt (complexExponentialSum L p.coeff) (x : ℂ)
  have hlocalData (x : ℝ) :
      ∃ δ : ℝ, 0 < δ ∧ ∃ d : I → ℕ → ℂ,
        (∀ q f, (∀ y : ℝ, f y ≠ 0 → |y - x| ≤ δ) →
          U q f = (∑ k ∈ Finset.range (order x), d q k • localDiracDerivative k x) f) ∧
        ∀ f : SchwartzMap ℝ ℂ, (∀ y : ℝ, f y ≠ 0 → |y - x| ≤ δ) →
          T f = (∑ k ∈ Finset.range (order x),
            combinedDiracJetCoefficient (fun q => L (c q)) x (order x) d k •
              localDiracDerivative k x) f := by
    let N := order x
    have hlocal (q : I) :
        ∃ r : ℝ, 0 < r ∧ ∃ d : ℕ → ℂ,
          ∀ f : SchwartzMap ℝ ℂ, (∀ y : ℝ, f y ≠ 0 → |y - x| ≤ r) →
            V q f = (∑ k ∈ Finset.range N, d k • localDiracDerivative k x) f := by
      obtain ⟨hC, hV, _, hslab, hv, harray⟩ := hq q
      have hC' : (C q).carrier = L '' Function.support (orderedLaurentJump p (Q q) lo hi) := by
        rw [hC, ← hv, harray]
      exact diracJets_of_realRootedLaurentInverse L hL p (Q q) lo hi hlo hhi hmin hmax
        hroot s hslab (C q) hC' (V q) (m q) hV (congrFun harray) x
    choose r hr D hD using hlocal
    let S := insert 1 (Finset.univ.image r)
    have hS : S.Nonempty := Finset.insert_nonempty _ _
    let δ := S.min' hS
    have hδ : 0 < δ := by
      have hm : δ ∈ S := S.min'_mem hS
      rcases Finset.mem_insert.mp hm with h | h
      · rw [h]
        exact zero_lt_one
      · obtain ⟨q, _, hq⟩ := Finset.mem_image.mp h
        rw [← hq]
        exact hr q
    have hδle (q : I) : δ ≤ r q :=
      S.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ q)))
    let d (q : I) := combinedDiracJetCoefficient (fun _ : Unit => -L (c q)) x N (fun _ => D q)
    have hU (q : I) (f : SchwartzMap ℝ ℂ)
        (hf : ∀ y : ℝ, f y ≠ 0 → |y - x| ≤ δ) :
        U q f = (∑ k ∈ Finset.range N, d q k • localDiracDerivative k x) f := by
      let J := ∑ k ∈ Finset.range N, D q k • localDiracDerivative k x
      have hmod := sum_modulatedDiracJets_eq_combined
        (fun _ : Unit => -L (c q)) x N (fun _ => D q)
      have hJ : combDistributionModulation (-L (c q)) J =
          ∑ k ∈ Finset.range N, d q k • localDiracDerivative k x := by
        simpa only [Fintype.sum_unique, J, d] using hmod
      rw [← hJ]
      change combDistributionModulation (-L (c q)) (V q) f =
        combDistributionModulation (-L (c q)) J f
      rw [combDistributionModulation_apply, combDistributionModulation_apply]
      exact hD q _ (fun y hy => (modulation_preserves_test_support _ _ _ _ hf y hy).trans (hδle q))
    refine ⟨δ, hδ, d, hU, fun f hf => ?_⟩
    rw [← hmod, ← sum_modulatedDiracJets_eq_combined]
    simp only [_root_.sum_apply, combDistributionModulation_apply]
    apply Finset.sum_congr rfl
    intro q _
    have h := hU q (combSchwartzModulation (L (c q)) f)
      (modulation_preserves_test_support (L (c q)) f x δ hf)
    simpa only [_root_.sum_apply, N] using h
  choose δ hδ d hU hd using hlocalData
  refine ⟨I, c, U, B₀, d, hI, hc, hB₀, hmod, fun x => ⟨δ x, hδ x, hU x, hd x⟩, ?_⟩
  intro A
  exact atomicOnCarrier_iff_combined_local_coset_rows (fun q => L (c q)) A T order d
    (fun x => ⟨δ x, hδ x, hd x⟩)


end

end MeyerGeneralProblem
