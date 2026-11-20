module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalPairNumerator

@[expose] public section

/-!
# Actual finite convolution with a literal Laurent numerator

A finite recurrence on the exact frequency module identifies the whole
convolution as the finite Dirac sum of the numerator.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped SchwartzMap

variable {G : Type*} [AddCommGroup G]

/-- An atomic recurrence with finite right hand side gives the actual
finite convolution identity, evaluated on any Schwartz test. -/
theorem finiteCombConvolution_apply_of_module_finite_numerator
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S T) (L : G →+ ℝ) (hL : Function.Injective L)
    (hS : S.carrier ⊆ range L) (p R : G →₀ ℂ)
    (hrec : ∀ n, annihilatorArrayConvolution p
      (fun j => extendedAtomicCoefficient S T (L j)) n = R n)
    (f : SchwartzMap ℝ ℂ) :
    finiteCombConvolution (fun j : p.support => L j) (fun j => p j) T f =
      ∑ n ∈ R.support, R n * f (L n) := by
  classical
  let a : p.support → ℝ := fun j => L j
  let c : p.support → ℂ := fun j => p j
  let C := finiteCombConvolutionCarrier S a
  let V := finiteCombConvolution a c T
  let D : TemperedDistribution ℝ ℂ :=
    ∑ n ∈ R.support, R n • TemperedDistribution.delta (L n)
  have hV : AtomicOnCarrier C V :=
    hasLocallyAtomicAction_atomicOnCarrier _ _
      (hasLocallyAtomicAction_finiteCombConvolution S T
        (atomicOnCarrier_hasLocallyAtomicAction S T hT) a c)
  have hcoef (n : G) : extendedAtomicCoefficient C V (L n) = R n := by
    rw [extendedAtomicCoefficient_finiteCombConvolution S T hT a c (L n)]
    simpa only [annihilatorArrayConvolution, a, c, ← map_sub,
      p.support.sum_coe_sort (fun j => p j * extendedAtomicCoefficient S T (L (n - j)))] using hrec n
  have hC : C.carrier ⊆ range L := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    obtain ⟨y, hy, rfl⟩ := (S.mem_translate (a j) x).mp hj
    obtain ⟨n, rfl⟩ := hS hy
    exact ⟨(j : G) + n, map_add L _ _⟩
  have hR (n : G) (hn : n ∈ R.support) : L n ∈ C.carrier := by
    by_contra hh
    exact (Finsupp.mem_support_iff.mp hn) ((hcoef n).symm.trans (by simp [extendedAtomicCoefficient, hh]))
  have hDtest (g : SchwartzMap ℝ ℂ) :
      D g = ∑ n ∈ R.support, R n * g (L n) := by
    simp only [D, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, TemperedDistribution.delta_apply]
  have hD : AtomicOnCarrier C D := by
    intro g hg
    rw [hDtest]
    apply Finset.sum_eq_zero
    intro n hn
    rw [hg _ (hR n hn), mul_zero]
  have heq : V = D := by
    apply atomic_eq_of_coefficients C _ _ hV hD
    intro x
    obtain ⟨n, hn⟩ := hC x.property
    have hx : L n ∈ C.carrier := hn ▸ x.property
    have he : (⟨L n, hx⟩ : C.subtype) = x := Subtype.ext hn
    have hleft := hcoef n
    rw [extendedAtomicCoefficient, dite_eq_left hx, he] at hleft
    rw [hleft, hDtest, Finset.sum_eq_single n]
    · rw [hn, C.isolationSchwartz_self, mul_one]
    · intro m hm hmn
      rw [C.isolationSchwartz_of_mem_of_ne x (hR m hm) (fun h => hmn (hL (h.trans hn.symm))), mul_zero]
    · intro h
      rw [Finsupp.notMem_support_iff.mp h, zero_mul]
  change V f = _
  rw [heq, hDtest]

end

end MeyerGeneralProblem
