module

public import MeyerGeneralProblem.Cardinal.Strong.LaurentArrayAlgebraAction
public import MeyerGeneralProblem.Cardinal.Strong.OriginalPairNumerator
public import Mathlib.Algebra.MonoidAlgebra.Support

@[expose] public section

/-!
# Extremal frequencies and divisibility of Laurent polynomials

The extreme frequencies of a product add, with exactly one contribution
to each extreme coefficient. This gives the width of every recurrence
power and rules out divisibility of a nonzero proper subpolynomial by
its full Laurent polynomial.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped Pointwise

variable {G : Type*} [AddCommGroup G]

/-- The upper extremal coefficient of a product is the product of the
upper extremal coefficients. All other occupied frequencies lie below it. -/
theorem laurentProduct_upperExtreme (L : G →+ ℝ) (hL : Function.Injective L)
    (p q : AddMonoidAlgebra ℂ G) (a b : G)
    (ha : p.coeff a ≠ 0)
    (hp : ∀ m ∈ p.coeff.support, L m ≤ L a)
    (hq : ∀ m ∈ q.coeff.support, L m ≤ L b) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b ∧
      ∀ n ∈ (p * q).coeff.support, L n ≤ L (a + b) := by
  classical
  constructor
  · rw [← annihilatorArrayConvolution_finite, annihilatorArrayConvolution]
    rw [Finset.sum_eq_single_of_mem a (Finsupp.mem_support_iff.mpr ha)]
    · congr 2
      abel
    · intro m hm hma
      apply mul_eq_zero.mpr
      right
      by_contra h
      have h' := hq (a + b - m) (Finsupp.mem_support_iff.mpr h)
      rw [map_sub, map_add] at h'
      have hlt : L m < L a := lt_of_le_of_ne (hp m hm) (fun he => hma (hL he))
      linarith
  · intro n hn
    obtain ⟨m, hm, j, hj, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset p q hn)
    rw [map_add, map_add]
    exact add_le_add (hp m hm) (hq j hj)

/-- The corresponding lower extreme follows using the reversed frequency. -/
theorem laurentProduct_lowerExtreme (L : G →+ ℝ) (hL : Function.Injective L)
    (p q : AddMonoidAlgebra ℂ G) (a b : G)
    (ha : p.coeff a ≠ 0)
    (hp : ∀ m ∈ p.coeff.support, L a ≤ L m)
    (hq : ∀ m ∈ q.coeff.support, L b ≤ L m) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b ∧
      ∀ n ∈ (p * q).coeff.support, L (a + b) ≤ L n := by
  obtain ⟨h, hle⟩ := laurentProduct_upperExtreme (-L)
    (fun x y h => hL (neg_injective h)) p q a b ha
    (fun m hm => neg_le_neg (hp m hm)) (fun m hm => neg_le_neg (hq m hm))
  exact ⟨h, fun n hn => neg_le_neg_iff.mp (hle n hn)⟩

/-- The extreme coefficient witnesses nonvanishing of the product in an
injectively ordered Laurent ring. -/
theorem laurent_mul_ne_zero_of_injective (L : G →+ ℝ) (hL : Function.Injective L)
    {p q : AddMonoidAlgebra ℂ G} (hp : p ≠ 0) (hq : q ≠ 0) : p * q ≠ 0 := by
  have hp' : p.coeff ≠ 0 := fun h => hp (AddMonoidAlgebra.coeff_injective (by simpa using h))
  have hq' : q.coeff ≠ 0 := fun h => hq (AddMonoidAlgebra.coeff_injective (by simpa using h))
  obtain ⟨_, a, _, ha, hpa, _, _⟩ := finiteAnnihilator_extrema L hL p.coeff hp'
  obtain ⟨_, b, _, hb, hqb, _, _⟩ := finiteAnnihilator_extrema L hL q.coeff hq'
  have h := (laurentProduct_upperExtreme L hL p q a b ha
    (fun n hn => (hpa n hn).2) (fun n hn => (hqb n hn).2)).1
  intro hzero
  rw [hzero] at h
  exact mul_ne_zero ha hb (by simpa using h.symm)

/-- The upper extreme of a power is the original extremal monomial
raised to the same power, and its frequency bound is exact. -/
theorem laurentPower_upperExtreme (L : G →+ ℝ) (hL : Function.Injective L)
    (p : AddMonoidAlgebra ℂ G) (a : G) (ha : p.coeff a ≠ 0)
    (hp : ∀ m ∈ p.coeff.support, L m ≤ L a) (k : ℕ) :
    (p ^ k).coeff (k • a) = p.coeff a ^ k ∧
      ∀ n ∈ (p ^ k).coeff.support, L n ≤ L (k • a) := by
  classical
  induction k with
  | zero =>
    refine ⟨by simp, ?_⟩
    intro n hn
    have hz : n = 0 := by simpa using hn
    simp [hz]
  | succ k ih =>
    have hne : (p ^ k).coeff (k • a) ≠ 0 := ih.1.trans_ne (pow_ne_zero k ha)
    obtain ⟨hc, hb⟩ := laurentProduct_upperExtreme L hL (p ^ k) p (k • a) a hne ih.2 hp
    simpa only [pow_succ, succ_nsmul, ih.1] using And.intro hc hb

/-- The exact lower extreme of a power. Together the two extrema give
width k times the original width, including for the zeroth power. -/
theorem laurentPower_lowerExtreme (L : G →+ ℝ) (hL : Function.Injective L)
    (p : AddMonoidAlgebra ℂ G) (a : G) (ha : p.coeff a ≠ 0)
    (hp : ∀ m ∈ p.coeff.support, L a ≤ L m) (k : ℕ) :
    (p ^ k).coeff (k • a) = p.coeff a ^ k ∧
      ∀ n ∈ (p ^ k).coeff.support, L (k • a) ≤ L n := by
  obtain ⟨h, hle⟩ := laurentPower_upperExtreme (-L)
    (fun x y h => hL (neg_injective h)) p a ha (fun m hm => neg_le_neg (hp m hm)) k
  exact ⟨h, fun n hn => neg_le_neg_iff.mp (hle n hn)⟩

/-- A nonzero divisible polynomial whose support stays inside the
divisor's support differs from its divisor only by a nonzero scalar. -/
theorem laurent_eq_smul_of_dvd_and_support_subset (L : G →+ ℝ) (hL : Function.Injective L)
    (p q : AddMonoidAlgebra ℂ G) (hq : q ≠ 0)
    (hsub : q.coeff.support ⊆ p.coeff.support) (hdvd : p ∣ q) :
    ∃ c : ℂ, c ≠ 0 ∧ q = c • p := by
  classical
  obtain ⟨w, rfl⟩ := hdvd
  have hp : p ≠ 0 := fun h => hq (by rw [h, zero_mul])
  have hw : w ≠ 0 := fun h => hq (by rw [h, mul_zero])
  have hp' : p.coeff ≠ 0 := fun h => hp (AddMonoidAlgebra.coeff_injective (by simpa using h))
  have hw' : w.coeff ≠ 0 := fun h => hw (AddMonoidAlgebra.coeff_injective (by simpa using h))
  obtain ⟨a, b, ha, hb, hpc, _, _⟩ := finiteAnnihilator_extrema L hL p.coeff hp'
  obtain ⟨d, e, hd, he, hwc, _, _⟩ := finiteAnnihilator_extrema L hL w.coeff hw'
  have hlo := (laurentProduct_lowerExtreme L hL p w a d ha
    (fun m hm => (hpc m hm).1) (fun m hm => (hwc m hm).1)).1
  have hhi := (laurentProduct_upperExtreme L hL p w b e hb
    (fun m hm => (hpc m hm).2) (fun m hm => (hwc m hm).2)).1
  have h0d := (hpc (a + d) (hsub (Finsupp.mem_support_iff.mpr (hlo.trans_ne (mul_ne_zero ha hd))))).1
  have he0 := (hpc (b + e) (hsub (Finsupp.mem_support_iff.mpr (hhi.trans_ne (mul_ne_zero hb he))))).2
  rw [map_add] at h0d he0
  have hz (m : G) (hm : m ∈ w.coeff.support) : m = 0 := by
    apply hL
    rw [map_zero]
    obtain ⟨hl, hle⟩ := hwc m hm
    exact le_antisymm (hle.trans (by linarith)) ((show 0 ≤ L d by linarith).trans hl)
  have hn : d = 0 := hz d (Finsupp.mem_support_iff.mpr hd)
  let c := w.coeff 0
  have hc : c ≠ 0 := by simpa only [hn] using hd
  have hw0 : w = AddMonoidAlgebra.single 0 c := by
    apply AddMonoidAlgebra.coeff_injective
    ext m
    by_cases hm : m = 0
    · subst m
      simp [c]
    · have hz' : w.coeff m = 0 :=
        Finsupp.notMem_support_iff.mp (fun h => hm (hz m h))
      simp [hz', hm]
  refine ⟨c, hc, ?_⟩
  rw [hw0]
  apply AddMonoidAlgebra.coeff_injective
  ext m
  rw [AddMonoidAlgebra.coeff_mul_single_zero, AddMonoidAlgebra.coeff_smul,
    Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-- Omitting any occupied monomial prevents divisibility by the original
Laurent polynomial, for arbitrary other coefficients on the retained sites. -/
theorem laurent_not_dvd_of_support_ssubset (L : G →+ ℝ) (hL : Function.Injective L)
    (p q : AddMonoidAlgebra ℂ G) (hq : q ≠ 0)
    (hsub : q.coeff.support ⊂ p.coeff.support) : ¬ p ∣ q := by
  intro h
  obtain ⟨c, hc, hcq⟩ := laurent_eq_smul_of_dvd_and_support_subset L hL p q hq hsub.le h
  apply hsub.not_ge
  intro m hm
  rw [Finsupp.mem_support_iff, hcq, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_ne_zero hc (Finsupp.mem_support_iff.mp hm)

end

end MeyerGeneralProblem
