module

public import MeyerGeneralProblem.Distribution.LaurentEulerNumerators
public import MeyerGeneralProblem.Distribution.LaurentEulerPrimeResidues
public import MeyerGeneralProblem.Distribution.LaurentEulerSupportGrowth

@[expose] public section

/-!
# Independent Euler twists of the complete original array

A putative relation survives the positive cut because the Euler action
is pointwise. Clearing the common denominator and factoring the smallest
prime power leaves only the top-degree residues at that prime.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set

variable {G : Type*} [AddCommGroup G]

/-- Equality for the two selected operators and the optional identity letter. -/
local instance : BEq (Option (Fin 2)) := instBEqOfDecidableEq

private theorem binaryEulerList_statistics {A R : Type*} [CommMonoid R]
    (f : Fin 2 → A) (g : A → R) (l : List (Option (Fin 2))) :
    (l.filterMap (Option.map f)).length = l.count (some 0) + l.count (some 1) ∧
      l.length = l.count none + l.count (some 0) + l.count (some 1) ∧
      ((l.filterMap (Option.map f)).map g).prod =
        g (f 0) ^ l.count (some 0) * g (f 1) ^ l.count (some 1) := by
  have h₀₁ : (0 : Fin 2) ≠ 1 := by decide
  have h₁₀ : (1 : Fin 2) ≠ 0 := by decide
  induction l with
  | nil => simp
  | cons a l ih =>
    cases a with
    | none =>
      rcases ih with ⟨h₁, h₂, h₃⟩
      simp [h₁, h₂, h₃, Nat.add_assoc, Nat.add_comm]
    | some i =>
      rcases ih with ⟨h₁, h₂, h₃⟩
      fin_cases i <;>
        simp [h₀₁, h₁₀, h₁, h₂, h₃, pow_add, mul_left_comm, mul_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem binaryEulerList_eq_of_length_and_second {A : Type*} (f : Fin 2 → A)
    {k : ℕ} (x y : Sym (Option (Fin 2)) k)
    (hlen : (x.val.toList.filterMap (Option.map f)).length =
      (y.val.toList.filterMap (Option.map f)).length)
    (hsecond : x.val.toList.count (some 1) = y.val.toList.count (some 1)) : x = y := by
  have hx := binaryEulerList_statistics f (fun _ => (1 : ℂ)) x.val.toList
  have hy := binaryEulerList_statistics f (fun _ => (1 : ℂ)) y.val.toList
  have hxl : x.val.toList.length = k := (Multiset.length_toList _).trans x.property
  have hyl : y.val.toList.length = k := (Multiset.length_toList _).trans y.property
  have hfirst : x.val.toList.count (some 0) = y.val.toList.count (some 0) := by omega
  have hnone : x.val.toList.count none = y.val.toList.count none := by omega
  apply Sym.ext
  apply Multiset.ext'
  intro i
  have hcount (t : Sym (Option (Fin 2)) k) :
      Multiset.count i t.val = t.val.toList.count i := by
    have h := congrArg (Multiset.count i) (Multiset.coe_toList t.val).symm
    simpa only [Multiset.coe_count] using h
  change Multiset.count i x.val = Multiset.count i y.val
  rw [hcount x, hcount y]
  cases i with
  | none => exact hnone
  | some i => fin_cases i <;> assumption

private theorem binaryEuler_relation_survives_cut (L : G →+ ℝ) (s : ℝ) (u : G → ℂ)
    {k : ℕ} (e : Fin 2 → G →+ ℂ) (S : Finset (Sym (Option (Fin 2)) k))
    (c : Sym (Option (Fin 2)) k → ℂ)
    (h : ∑ t ∈ S, c t • laurentEulerMonomial e t u = 0) :
    ∑ t ∈ S, c t • laurentEulerMonomial e t (arrayPositiveCut L s u) = 0 := by
  classical
  ext n
  by_cases hn : s ≤ L n
  · simpa only [Finset.sum_apply, Pi.smul_apply, laurentEulerMonomial, arrayPositiveCut,
      ite_eq_left hn] using congrFun h n
  · simp [Finset.sum_apply, laurentEulerMonomial, arrayPositiveCut, hn]

set_option maxHeartbeats 1400000 in
private theorem linearIndependent_twoEuler_of_residue {K : Type*} [Field K] [Algebra ℂ K]
    (L : G →+ ℝ) (hL : Function.Injective L)
    (p q r : AddMonoidAlgebra ℂ G) (m a : ℕ) (ha : a < m + 1)
    (φ : AddMonoidAlgebra ℂ G →ₐ[ℂ] K)
    (hp : p ≠ 0) (hp₀ : φ p = 0) (hq : φ q ≠ 0) (hr : φ r ≠ 0)
    (e f : G →+ ℂ) (hx : φ (laurentEulerPolynomial e p) ≠ 0)
    (hratio : Transcendental ℂ
      (φ (laurentEulerPolynomial f p) / φ (laurentEulerPolynomial e p)))
    (s : ℝ) (u : G → ℂ)
    (hcut : cutArrayNumerator L (p ^ (m + 1) * q).coeff s u = (p ^ a * r).coeff)
    (k : ℕ) :
    LinearIndependent ℂ (fun t : Sym (Option (Fin 2)) k =>
      laurentEulerMonomial (Fin.cases e (fun _ => f)) t u) := by
  classical
  let I := Sym (Option (Fin 2)) k
  let b : Fin 2 → G →+ ℂ := Fin.cases e (fun _ => f)
  let Q := p ^ (m + 1) * q
  let es (t : I) := t.val.toList.filterMap (Option.map b)
  let g (t : I) := (es t).length
  let j (t : I) := t.val.toList.count (some 1)
  let v := arrayPositiveCut L s u
  have hcutQ : annihilatorArrayConvolution (Q ^ 1).coeff v = (p ^ a * r).coeff := by
    rw [pow_one]
    exact hcut
  let x := φ (laurentEulerPolynomial e p)
  let y := φ (laurentEulerPolynomial f p)
  change LinearIndependent ℂ (fun t : I => laurentEulerMonomial b t u)
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  by_contra hi
  let C := Finset.univ.filter (fun t : I => c t ≠ 0)
  have hiC : i ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have hC : C.Nonempty := ⟨i, hiC⟩
  obtain ⟨t₀, ht₀, hmax⟩ := C.exists_max_image g hC
  let d := g t₀
  have hcnz (t : I) (ht : t ∈ C) : c t ≠ 0 := (Finset.mem_filter.mp ht).2
  have hrel : ∑ t ∈ C, c t • laurentEulerMonomial b t u = 0 := by
    rw [Finset.sum_subset (Finset.filter_subset _ _)]
    · exact hc
    · intro t _ ht
      have hz : c t = 0 := by
        by_contra hn
        exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
      rw [hz, zero_smul]
  have hvrel : ∑ t ∈ C, c t • laurentEulerMonomial b t v = 0 :=
    binaryEuler_relation_survives_cut L s u b C c hrel
  have hw (t : I) := exists_factor_laurentEulerNumerator_with_residue
    φ.toRingHom p q r hp₀ m a ha.le (es t)
  choose w hwfactor hwresidue using hw
  let B (t : I) := p ^ (d - g t) * q ^ (d - g t) * w t
  let P := p ^ (m * d + a)
  let Z := ∑ t ∈ C, c t • B t
  have hclear (t : I) (ht : t ∈ C) :
      originalLaurentArrayAction (Q ^ (d + 1)) (laurentEulerMonomial b t v) =
        (P * B t).coeff := by
    have hg : g t ≤ d := hmax t ht
    have hn := annihilatorArrayConvolution_eulerNumerator Q (p ^ a * r) 1 v hcutQ (es t)
    have he : d + 1 = (d - g t) + (1 + g t) := by omega
    have hpows : Q ^ (d - g t) * (p ^ (m * g t + a) * w t) = P * B t := by
      have hh : (m + 1) * (d - g t) + (m * g t + a) =
          m * d + a + (d - g t) := by
        calc
          _ = m * ((d - g t) + g t) + a + (d - g t) := by ring
          _ = _ := by rw [Nat.sub_add_cancel hg]
      dsimp only [Q, P, B]
      rw [mul_pow, ← pow_mul]
      calc
        _ = p ^ ((m + 1) * (d - g t) + (m * g t + a)) *
              (q ^ (d - g t) * w t) := by rw [pow_add]; ring
        _ = _ := by rw [hh, pow_add]; ring
    rw [laurentEulerMonomial_eq_foldr]
    ext n
    rw [originalLaurentArrayAction_apply, he, pow_add, annihilatorArrayConvolution_mul]
    change annihilatorArrayConvolution (Q ^ (d - g t)).coeff
      (annihilatorArrayConvolution (Q ^ (1 + (es t).length)).coeff
        ((es t).foldr laurentEulerArray v)) n = _
    rw [hn, annihilatorArrayConvolution_finite, hwfactor t, hpows]
  have hZprod : P * Z = 0 := by
    have hz := congrArg (originalLaurentArrayAction (Q ^ (d + 1))) hvrel
    simp only [map_sum, map_smul, map_zero] at hz
    have he :
        (∑ t ∈ C, c t • originalLaurentArrayAction (Q ^ (d + 1))
          (laurentEulerMonomial b t v)) = ((P * Z).coeff : G → ℂ) := by
      dsimp only [Z]
      rw [Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [hclear t ht, mul_smul_comm (c t) P (B t), AddMonoidAlgebra.coeff_smul,
        Finsupp.coe_smul]
    rw [he] at hz
    apply AddMonoidAlgebra.coeff_injective
    ext n
    exact congrFun hz n
  have hP (n : ℕ) : p ^ n ≠ 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; exact laurent_mul_ne_zero_of_injective L hL ih hp
  have hZ : Z = 0 := by
    by_contra hn
    exact laurent_mul_ne_zero_of_injective L hL (hP (m * d + a)) hn hZprod
  let H := C.filter (fun t : I => g t = d)
  have htH : t₀ ∈ H := Finset.mem_filter.mpr ⟨ht₀, rfl⟩
  let A := (-1 : K) ^ d * ((m + 1 - a).ascFactorial d : K) * (φ q) ^ d * φ r
  have hA : A ≠ 0 := by
    obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m + 1 - a ≠ 0)
    have hs : 0 < (m + 1 - a).ascFactorial d := by
      rw [hl]
      exact Nat.ascFactorial_pos l d
    have hs' : ((m + 1 - a).ascFactorial d : K) ≠ 0 := by
      rw [← map_natCast (algebraMap ℂ K)]
      simpa only [map_zero] using
        (algebraMap ℂ K).injective.ne (Nat.cast_ne_zero.mpr hs.ne')
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      hs') (pow_ne_zero _ hq)) hr
  let M (t : I) := x ^ (d - j t) * y ^ j t
  have hφ (t : I) (ht : t ∈ C) : φ (B t) = if g t = d then A * M t else 0 := by
    dsimp only [B]
    simp only [map_mul, map_pow, hp₀]
    by_cases he : g t = d
    · have hst := binaryEulerList_statistics b (fun e => φ (laurentEulerPolynomial e p))
        t.val.toList
      have hg : d = t.val.toList.count (some 0) + j t := he.symm.trans hst.1
      have hj : d - j t = t.val.toList.count (some 0) := by omega
      simp only [he, Nat.sub_self, pow_zero, mul_one, one_mul, ite_true]
      have hprod : ((es t).map (fun e => φ (laurentEulerPolynomial e p))).prod =
          x ^ (d - j t) * y ^ j t := by
        rw [hj]
        exact hst.2.2
      have hh : φ (w t) =
          (-1 : K) ^ (es t).length * ((m + 1 - a).ascFactorial (es t).length : K) *
            (φ q) ^ (es t).length *
            ((es t).map (fun e => φ (laurentEulerPolynomial e p))).prod * φ r := hwresidue t
      rw [hprod, show (es t).length = d from he] at hh
      rw [hh]
      dsimp only [A, M]
      ring
    · have hd : d - g t ≠ 0 := by have hle := hmax t ht; omega
      simp [he, zero_pow hd]
  have hφZ := congrArg φ hZ
  change φ (∑ t ∈ C, c t • B t) = φ 0 at hφZ
  simp only [map_sum, map_smul, map_zero] at hφZ
  have he :
      (∑ t ∈ C, c t • φ (B t)) = A * (∑ t ∈ H, c t • M t) := by
    rw [Finset.mul_sum]
    rw [Finset.sum_filter (s := C) (fun t : I => g t = d) (fun t => A * (c t • M t))]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hφ t ht]
    by_cases hd : g t = d
    · simp only [hd, ite_true, mul_smul_comm]
    · simp [hd]
  rw [he] at hφZ
  have hsum : ∑ t ∈ H, c t • M t = 0 := (mul_eq_zero.mp hφZ).resolve_left hA
  let index (t : {t // t ∈ H}) : Fin (d + 1) := ⟨j t, by
    have h := (binaryEulerList_statistics b (fun _ => (1 : ℂ)) t.val.val.toList).1
    have hg := (Finset.mem_filter.mp t.property).2
    change g t.val = t.val.val.toList.count (some 0) + j t.val at h
    omega⟩
  have hindex : Function.Injective index := by
    intro t z ht
    apply Subtype.ext
    apply binaryEulerList_eq_of_length_and_second b
    · exact ((Finset.mem_filter.mp t.property).2).trans
        ((Finset.mem_filter.mp z.property).2).symm
    · exact congrArg Fin.val ht
  have hlin : LinearIndependent ℂ (fun t : {t // t ∈ H} => M t) :=
    (linearIndependent_homogeneous_powers_of_transcendental_ratio x y hx hratio d).comp
      index hindex
  have hs : ∑ t : {t // t ∈ H}, c t • M t = 0 := by
    rw [H.sum_coe_sort (fun t => c t • M t)]
    exact hsum
  exact hcnz t₀ ht₀ (Fintype.linearIndependent_iff.mp hlin (fun t : {t // t ∈ H} => c t)
    hs ⟨t₀, htH⟩)

/-- A surviving prime with a noncollinear triple supplies every
degree-bounded independent Euler family on the original whole array. -/
theorem linearIndependent_twoEuler_of_survivingPrime
    (L : G →+ ℝ) (hL : Function.Injective L)
    (p q r : AddMonoidAlgebra ℂ G) (m a : ℕ) (ha : a < m + 1)
    (hp : Prime p) (hq : ¬ p ∣ q) (hr : ¬ p ∣ r)
    (e f : G →+ ℂ) (n₀ n₁ n₂ : G) (h₀ : p.coeff n₀ ≠ 0) (h₁ : p.coeff n₁ ≠ 0)
    (h₂ : p.coeff n₂ ≠ 0)
    (hdet : (e n₁ - e n₀) * (f n₂ - f n₀) - (e n₂ - e n₀) * (f n₁ - f n₀) ≠ 0)
    (s : ℝ) (u : G → ℂ)
    (hcut : cutArrayNumerator L (p ^ (m + 1) * q).coeff s u = (p ^ a * r).coeff)
    (k : ℕ) :
    LinearIndependent ℂ (fun t : Sym (Option (Fin 2)) k =>
      laurentEulerMonomial (Fin.cases e (fun _ => f)) t u) := by
  let I := Ideal.span ({p} : Set (AddMonoidAlgebra ℂ G))
  let _ : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
  let K := FractionRing ((AddMonoidAlgebra ℂ G) ⧸ I)
  let φ := (IsScalarTower.toAlgHom ℂ ((AddMonoidAlgebra ℂ G) ⧸ I) K).comp
    (Ideal.Quotient.mkₐ ℂ I)
  have hker (z : AddMonoidAlgebra ℂ G) : φ z = 0 ↔ p ∣ z := by
    change algebraMap ((AddMonoidAlgebra ℂ G) ⧸ I) K (Ideal.Quotient.mk I z) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
  have hnd := laurent_not_dvd_twoEulerCombination L hL p e f n₀ n₁ n₂ h₀ h₁ h₂ hdet
  have hx : φ (laurentEulerPolynomial e p) ≠ 0 :=
    (hker _).not.mpr (by simpa using hnd 1 0 (Or.inl one_ne_zero))
  have ht : Transcendental ℂ (φ (laurentEulerPolynomial f p) / φ (laurentEulerPolynomial e p)) :=
    laurent_primeEulerRatio_transcendental L hL p hp e f n₀ n₁ n₂ h₀ h₁ h₂ hdet
  exact linearIndependent_twoEuler_of_residue L hL p q r m a ha φ hp.ne_zero
    ((hker _).mpr dvd_rfl) ((hker _).not.mpr hq) ((hker _).not.mpr hr) e f hx ht s u hcut k

end

end MeyerGeneralProblem
