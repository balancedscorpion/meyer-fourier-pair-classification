module

public import MeyerGeneralProblem.Distribution.LaurentJumpPresentation
public import MeyerGeneralProblem.Distribution.WeightedAtomic
public import MeyerGeneralProblem.Distribution.ModuleAtomicAnnihilation
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Group.Submonoid.Finsupp

@[expose] public section

/-!
# Polynomial counts and tempered spectral realization of a Laurent jump

Finite step multiplicities give polynomial counts even in a dense frequency
group. With a coefficient growth bound, the exact spectral array then
constructs an actual weighted atomic Fourier record and an annihilated
tempered inverse.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped FourierTransform

/-- A polynomial counting bound and a polynomial coefficient bound give
absolute polynomially weighted summability on the original index set. -/
theorem summable_weighted_coefficients_of_centered_count {ι : Type*}
    (frequency : ι → ℝ) (b : ι → ℂ) (C d : ℕ) (M : ℝ) (k : ℕ) (hM : 0 ≤ M)
    (hcount : ∀ N : ℕ, {x | |frequency x| ≤ (N : ℝ)}.Finite ∧
      {x | |frequency x| ≤ (N : ℝ)}.ncard ≤ C * (N + 1) ^ d)
    (hb : ∀ x, ‖b x‖ ≤ M * (1 + |frequency x|) ^ k) :
    Summable (fun x => ‖b x‖ / (1 + |frequency x|) ^ (k + (d + 2))) := by
  classical
  let shell (x : ι) := ⌊|frequency x|⌋₊
  let E (n : ℕ) := {x : ι | shell x = n}
  let e : (Σ n, E n) ≃ ι := Equiv.sigmaFiberEquiv shell
  let a (x : ι) := ‖b x‖ / (1 + |frequency x|) ^ (k + (d + 2))
  have ha0 (x : ι) : 0 ≤ a x := by dsimp [a]; positivity
  have hE (n : ℕ) : E n ⊆ {x | |frequency x| ≤ ((n + 1 : ℕ) : ℝ)} := by
    intro x hx
    change shell x = n at hx
    change |frequency x| ≤ ((n + 1 : ℕ) : ℝ)
    have h := Nat.lt_floor_add_one (|frequency x|)
    change |frequency x| < (shell x : ℝ) + 1 at h
    simpa only [hx, Nat.cast_add, Nat.cast_one] using h.le
  let (n : ℕ) : Fintype (E n) := ((hcount (n + 1)).1.subset (hE n)).fintype
  have hcard (n : ℕ) : Fintype.card (E n) ≤ C * (n + 1 + 1) ^ d := by
    rw [Set.fintypeCard_eq_ncard]
    exact (Set.ncard_le_ncard (hE n) (hcount (n + 1)).1).trans (hcount (n + 1)).2
  have hsmall (n : ℕ) (x : E n) : a x ≤ M / (1 + (n : ℝ)) ^ (d + 2) := by
    have hn : (n : ℝ) ≤ |frequency x| := by
      have hfloor : shell (x : ι) = n := x.property
      have hx := Nat.floor_le (abs_nonneg (frequency x))
      change (shell (x : ι) : ℝ) ≤ _ at hx
      simpa only [hfloor] using hx
    have hx : 0 < 1 + |frequency x| := by positivity
    calc
      _ ≤ M * (1 + |frequency x|) ^ k / (1 + |frequency x|) ^ (k + (d + 2)) :=
        div_le_div_of_nonneg_right (hb x) (by positivity)
      _ = M / (1 + |frequency x|) ^ (d + 2) := by rw [pow_add]; field_simp
      _ ≤ _ := div_le_div_of_nonneg_left hM (by positivity)
        (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + (n : ℝ)) (add_le_add_right hn 1) _)
  have hseries : Summable (fun n : ℕ => ((C : ℝ) * 2 ^ d * M) / (1 + (n : ℝ)) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).comp_injective
      Nat.succ_injective
    simpa only [Function.comp_def, Nat.cast_succ, mul_one_div, add_comm] using
      h.mul_left ((C : ℝ) * 2 ^ d * M)
  apply e.summable_iff.mp
  change Summable (fun x : (Σ n, E n) => a x.2)
  have hsigma := summable_sigma_of_nonneg
    (f := fun x : (Σ n, E n) => a x.2) (fun x => ha0 x.2)
  apply hsigma.mpr
  refine ⟨fun n => (hasSum_fintype _).summable, ?_⟩
  apply Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun x : E n => ha0 x)) _ hseries
  intro n
  rw [tsum_fintype]
  have hcast : (Fintype.card (E n) : ℝ) ≤ (C : ℝ) * ((n : ℝ) + 1 + 1) ^ d := by
    exact_mod_cast hcard n
  have hpower : ((n : ℝ) + 1 + 1) ^ d ≤ (2 * (1 + (n : ℝ))) ^ d := by
    apply pow_le_pow_left₀ (by positivity)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ ∑ _x : E n, M / (1 + (n : ℝ)) ^ (d + 2) :=
      Finset.sum_le_sum fun x _ => hsmall n x
    _ = (Fintype.card (E n) : ℝ) * (M / (1 + (n : ℝ)) ^ (d + 2)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((C : ℝ) * (2 * (1 + (n : ℝ))) ^ d) * (M / (1 + (n : ℝ)) ^ (d + 2)) :=
      mul_le_mul_of_nonneg_right (hcast.trans (mul_le_mul_of_nonneg_left hpower (by positivity)))
        (by positivity)
    _ = _ := by
      rw [mul_pow, pow_add (1 + (n : ℝ))]
      have hn : 0 < 1 + (n : ℝ) := by positivity
      field_simp


variable {G : Type*} [AddCommGroup G]

/-- A finite union of translates of a positive finitely generated monoid
has polynomially many labels in each centered frequency window. -/
theorem positiveStepSupport_centered_count
    (L : G →+ ℝ) (S D : Finset G) (hD : ∀ d ∈ D, 0 < L d) (U : Set G)
    (hU : ∀ n ∈ U, ∃ r ∈ S, n - r ∈ AddSubmonoid.closure (D : Set G)) :
    ∃ C : ℕ, ∀ N : ℕ,
      (U ∩ {n | |L n| ≤ (N : ℝ)}).Finite ∧
      (U ∩ {n | |L n| ≤ (N : ℝ)}).ncard ≤ C * (N + 1) ^ D.card := by
  classical
  let A := ∑ r ∈ S, |L r|
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hlo (r : G) (hr : r ∈ S) : -A ≤ L r := by
    have h := Finset.single_le_sum (f := fun r => |L r|) (fun r _ => abs_nonneg (L r)) hr
    linarith [neg_le_abs (L r)]
  obtain ⟨δ, hδ, hδD⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ D, δ ≤ L d := by
    by_cases h : D.Nonempty
    · obtain ⟨d, hd, hmin⟩ := D.exists_min_image L h
      exact ⟨L d, hD d hd, hmin⟩
    · exact ⟨1, zero_lt_one, fun d hd => (h ⟨d, hd⟩).elim⟩
  obtain ⟨B, hB⟩ := exists_nat_gt ((1 + A) / δ)
  have hB' : 1 + A < (B : ℝ) * δ := (div_lt_iff₀ hδ).mp hB
  refine ⟨S.card * B ^ D.card, fun N => ?_⟩
  let K := B * (N + 1)
  have hK : (N : ℝ) + A < (K : ℝ) * δ := by
    calc
      _ ≤ ((N : ℝ) + 1) * (1 + A) := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
      _ < ((N : ℝ) + 1) * ((B : ℝ) * δ) := by gcongr
      _ = _ := by push_cast [K]; ring
  let f (t : S × (D → Fin K)) : G := (t.1 : G) + ∑ j : D, (t.2 j : ℕ) • (j : G)
  have hsub : U ∩ {n | |L n| ≤ (N : ℝ)} ⊆ Set.range f := by
    rintro n ⟨hn, hwin⟩
    change |L n| ≤ (N : ℝ) at hwin
    obtain ⟨r, hr, hmon⟩ := hU n hn
    obtain ⟨c, hc⟩ := AddSubmonoid.mem_closure_finset'.mp hmon
    have he : n = r + ∑ j : D, c j • (j : G) := by
      rw [← hc]
      abel
    have hsum : ((∑ j : D, c j : ℕ) : ℝ) * δ ≤ (N : ℝ) + A := by
      calc
        _ = ∑ j : D, (c j : ℝ) * δ := by rw [← Finset.sum_mul, Nat.cast_sum]
        _ ≤ ∑ j : D, L (c j • (j : G)) := Finset.sum_le_sum fun j _ => by
          rw [map_nsmul, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_left (hδD j j.property) (Nat.cast_nonneg _)
        _ = L n - L r := by rw [he, map_add, map_sum, add_sub_cancel_left]
        _ ≤ _ := sub_le_iff_le_add.mpr (by linarith [(abs_le.mp hwin).2, hlo r hr])
    have htotal : ∑ j : D, c j < K := by
      exact_mod_cast (lt_of_mul_lt_mul_right (hsum.trans_lt hK) hδ.le)
    let b (j : D) : Fin K :=
      ⟨c j, (Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) (Finset.mem_univ j)).trans_lt htotal⟩
    exact ⟨(⟨r, hr⟩, b), he.symm⟩
  refine ⟨(Set.finite_range f).subset hsub, (Set.ncard_le_ncard hsub (Set.finite_range f)).trans ?_⟩
  rw [← Set.image_univ]
  refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
  simp only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_fun, Fintype.card_fin, K, mul_pow, mul_assoc, le_refl]

private theorem orderedLaurentExpansion_centered_count
    (L : G →+ ℝ) (p R : AddMonoidAlgebra ℂ G) (m : G) (hm : p.coeff m ≠ 0)
    (hmin : ∀ x ∈ p.coeff.support, x ≠ m → L m < L x) :
    ∃ C : ℕ, ∀ N : ℕ,
      ((Function.support (orderedLaurentExpansion p R m)) ∩ {n | |L n| ≤ (N : ℝ)}).Finite ∧
      ((Function.support (orderedLaurentExpansion p R m)) ∩ {n | |L n| ≤ (N : ℝ)}).ncard ≤
        C * (N + 1) ^ p.coeff.support.card := by
  classical
  let S := R.coeff.support.image fun r => r - m
  let D := (p.coeff.support.erase m).image fun r => r - m
  have hD (d : G) (hd : d ∈ D) : 0 < L d := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    rw [map_sub]
    exact sub_pos.mpr (hmin x (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1)
  have hcard : D.card ≤ p.coeff.support.card :=
    Finset.card_image_le.trans (Finset.card_le_card (Finset.erase_subset _ _))
  have hU (n : G) (hn : n ∈ Function.support (orderedLaurentExpansion p R m)) :
      ∃ r ∈ S, n - r ∈ AddSubmonoid.closure (D : Set G) := by
    obtain ⟨r, hr, hmon⟩ := (orderedLaurentExpansion_at_extreme L p R m hm hmin).2.2 n hn
    refine ⟨r - m, Finset.mem_image_of_mem _ hr, ?_⟩
    apply AddSubmonoid.closure_mono _ hmon
    rintro _ ⟨x, hx, hne, rfl⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hne, hx⟩)
  obtain ⟨C, hC⟩ := positiveStepSupport_centered_count L S D hD _ hU
  exact ⟨C, fun N => ⟨(hC N).1, (hC N).2.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hcard))⟩⟩

/-- The complete two-sided jump has polynomial centered counts even when
its original frequency group is dense. -/
theorem orderedLaurentJump_centered_count
    (L : G →+ ℝ) (p R : AddMonoidAlgebra ℂ G) (lo hi : G)
    (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ x ∈ p.coeff.support, x ≠ lo → L lo < L x)
    (hmax : ∀ x ∈ p.coeff.support, x ≠ hi → L x < L hi) :
    ∃ C : ℕ, ∀ N : ℕ,
      ((Function.support (orderedLaurentJump p R lo hi)) ∩ {n | |L n| ≤ (N : ℝ)}).Finite ∧
      ((Function.support (orderedLaurentJump p R lo hi)) ∩ {n | |L n| ≤ (N : ℝ)}).ncard ≤
        C * (N + 1) ^ p.coeff.support.card := by
  classical
  have hmax' : ∀ x ∈ p.coeff.support, x ≠ hi → (-L) hi < (-L) x := by
    simpa only [AddMonoidHom.neg_apply, neg_lt_neg_iff] using hmax
  obtain ⟨Cp, hCp⟩ := orderedLaurentExpansion_centered_count L p R lo hlo hmin
  obtain ⟨Cm, hCm⟩ := orderedLaurentExpansion_centered_count (-L) p R hi hhi hmax'
  simp only [AddMonoidHom.neg_apply, abs_neg] at hCm
  refine ⟨Cp + Cm, fun N => ?_⟩
  let W : Set G := {n | |L n| ≤ (N : ℝ)}
  let P := Function.support (orderedLaurentExpansion p R lo) ∩ W
  let M := Function.support (orderedLaurentExpansion p R hi) ∩ W
  have hsub : Function.support (orderedLaurentJump p R lo hi) ∩ W ⊆ P ∪ M := by
    rintro n ⟨hn, hw⟩
    by_cases hp : orderedLaurentExpansion p R lo n = 0
    · right
      refine ⟨?_, hw⟩
      intro hm
      exact hn (by simp [orderedLaurentJump, hp, show orderedLaurentExpansion p R hi n = 0 from hm])
    · exact Or.inl ⟨hp, hw⟩
  have hfin : (P ∪ M).Finite := (hCp N).1.union (hCm N).1
  refine ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans ?_⟩
  calc
    _ ≤ P.ncard + M.ncard := Set.ncard_union_le _ _
    _ ≤ Cp * (N + 1) ^ p.coeff.support.card +
        Cm * (N + 1) ^ p.coeff.support.card := Nat.add_le_add (hCp N).2 (hCm N).2
    _ = (Cp + Cm) * (N + 1) ^ p.coeff.support.card := by rw [add_mul]


/-- The actual carrier of a locally finite array, including only nonzero coefficients. -/
def frequencyArrayCarrier (L : G →+ ℝ) (u : G → ℂ) (h : FrequencyLocallyFinite L u) :
    LocallyFiniteCarrier where
  carrier := L '' Function.support u
  finite_inter_Icc a b := by
    apply ((h a b).image L).subset
    rintro _ ⟨⟨n, hn, rfl⟩, hwin⟩
    exact ⟨n, ⟨hn, hwin⟩, rfl⟩

/-- A polynomial-growth Laurent jump with the required recurrence is the
exact Fourier record of an annihilated tempered distribution. Physical
exclusion and jet rows are separate obligations for that inverse. -/
theorem exists_tempered_inverse_with_orderedLaurentJump
    (L : G →+ ℝ) (hL : Function.Injective L) (p R : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ x ∈ p.coeff.support, x ≠ lo → L lo < L x)
    (hmax : ∀ x ∈ p.coeff.support, x ≠ hi → L x < L hi)
    (s : ℝ) (hR : ∀ r ∈ R.coeff.support, L lo + s ≤ L r ∧ L r < L hi + s)
    (M : ℝ) (k : ℕ) (hM : 0 ≤ M)
    (hgrowth : ∀ n, ‖orderedLaurentJump p R lo hi n‖ ≤ M * (1 + |L n|) ^ k) :
    let u := orderedLaurentJump p R lo hi
    ∃ B : LocallyFiniteCarrier, B.carrier = L '' Function.support u ∧
      ∃ T : TemperedDistribution ℝ ℂ,
        𝓕 T ∈ stronglyTemperedAtomicAtExponent B (k + (p.coeff.support.card + 2)) ∧
        (∀ n, originalFourierArray L B T n = u n) ∧
        (∀ n, cutArrayNumerator L p.coeff s (originalFourierArray L B T) n = R.coeff n) ∧
        finiteExponentialMultiplication (fun m : p.coeff.support => L m) (fun m => p.coeff m) T = 0 := by
  classical
  let u := orderedLaurentJump p R lo hi
  obtain ⟨hlocal, hrec, _, _, hnum⟩ :=
    orderedLaurentJump_exact_cuts L p R lo hi hlo hhi hmin hmax s hR
  let B := frequencyArrayCarrier L u hlocal
  let e : Function.support u ≃ B.subtype := Equiv.ofBijective
    (fun n => ⟨L n, ⟨n, n.property, rfl⟩⟩)
    ⟨fun _ _ h => Subtype.ext (hL (congrArg Subtype.val h)),
      fun ⟨_, ⟨n, hn, he⟩⟩ => ⟨⟨n, hn⟩, Subtype.ext he⟩⟩
  have he (n : Function.support u) : (e n : ℝ) = L n := rfl
  let b (x : B.subtype) := u (e.symm x)
  let d := p.coeff.support.card
  obtain ⟨C, hC⟩ := orderedLaurentJump_centered_count L p R lo hi hlo hhi hmin hmax
  have hcard (N : ℕ) :
      {n : Function.support u | |L n| ≤ (N : ℝ)}.Finite ∧
        {n : Function.support u | |L n| ≤ (N : ℝ)}.ncard ≤ C * (N + 1) ^ d := by
    refine ⟨((hC N).1.preimage Subtype.coe_injective.injOn).subset (fun n hn => ⟨n.property, hn⟩), ?_⟩
    rw [show {n : Function.support u | |L n| ≤ (N : ℝ)} =
      {n : Function.support u | (n : G) ∈ {n : G | |L n| ≤ (N : ℝ)}} by rfl, Set.ncard_subtype,
      Set.inter_comm]
    exact (hC N).2
  have hweights : Summable (weightedAtomicMassTerm B b (k + (d + 2))) := by
    apply e.summable_iff.mp
    simpa only [Function.comp_def, weightedAtomicMassTerm, b, Equiv.symm_apply_apply, he] using
      summable_weighted_coefficients_of_centered_count (fun n : Function.support u => L n)
        (fun n => u n) C d M k hM hcard (fun n => hgrowth n)
  let ν := weightedAtomicDistribution B b (k + (d + 2)) hweights
  have hν : AtomicOnCarrier B ν := weightedAtomicDistribution_atomicOnCarrier B b _ hweights
  have hcoef (n : G) : extendedAtomicCoefficient B ν (L n) = u n := by
    by_cases hn : u n ≠ 0
    · let j : Function.support u := ⟨n, hn⟩
      have hh : L n ∈ B.carrier := ⟨n, hn, rfl⟩
      rw [extendedAtomicCoefficient, dite_eq_left hh]
      have hj : (⟨L n, hh⟩ : B.subtype) = e j := Subtype.ext (he j).symm
      rw [hj, weightedAtomicDistribution_isolation B b _ hweights]
      simp [b, j]
    · have hh : L n ∉ B.carrier := by
        rintro ⟨m, hm, heq⟩
        exact hn (hL heq ▸ hm)
      rw [extendedAtomicCoefficient, dite_eq_right hh, not_ne_iff.mp hn]
  have hoff (x : ℝ) (hx : x ∉ Set.range L) : extendedAtomicCoefficient B ν x = 0 := by
    rw [extendedAtomicCoefficient, dite_eq_right]
    rintro ⟨n, _, rfl⟩
    exact hx (Set.mem_range_self n)
  have hconv : finiteCombConvolution (fun m : p.coeff.support => L m) (fun m => p.coeff m) ν = 0 := by
    apply finiteCombConvolution_eq_zero_of_module_recurrence B L
      (fun m : p.coeff.support => (m : G)) (fun m => p.coeff m) ν hν hoff
    intro n
    simp_rw [hcoef]
    rw [p.coeff.support.sum_coe_sort (fun m : G => p.coeff m * u (n - m))]
    exact hrec n
  let T : TemperedDistribution ℝ ℂ := 𝓕⁻ ν
  have hT : 𝓕 T = ν := FourierTransform.fourier_fourierInv_eq ν
  refine ⟨B, rfl, T, ?_, ?_, ?_, ?_⟩
  · rw [hT]
    exact weightedAtomicDistribution_mem_strongExponent B b _ hweights
  · intro n
    unfold originalFourierArray
    rw [hT, hcoef]
  · have harray : originalFourierArray L B T = u := by
      funext n
      unfold originalFourierArray
      rw [hT, hcoef]
    intro n
    rw [harray]
    exact congrFun hnum n
  · have hz := fourier_finiteExponentialMultiplication
      (fun m : p.coeff.support => L m) (fun m => p.coeff m) T
    rw [hT, hconv] at hz
    simpa only [FourierTransform.fourierInv_fourier_eq, FourierTransform.fourierInv_zero] using
      congrArg FourierTransform.fourierInv hz

end

end MeyerGeneralProblem
