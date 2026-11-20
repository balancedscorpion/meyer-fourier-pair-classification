module

public import MeyerGeneralProblem.Distribution.FinitePhaseCombKernel
public import MeyerGeneralProblem.Distribution.QuadraticLowerCountTranslation

@[expose] public section

/-!
# Actual carriers and counts for a class-eliminating translation product

The physical carrier grows by finite translates of a single original
carrier. The quadratic lower count is preserved without intersecting
independently chosen sequences of small counts.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set

/-- One locally finite carrier for the physical result after all factors. -/
def combTranslationFactorsPhysicalCarrier (w : ℝ) :
    List ℝ → LocallyFiniteCarrier → LocallyFiniteCarrier
  | [], A => A
  | _ :: modes, A => combTranslationFactorsPhysicalCarrier w modes ((A.translate w).union A)

theorem atomicOnCarrier_combTranslationFactors (w : ℝ) (modes : List ℝ)
    (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T) :
    AtomicOnCarrier (combTranslationFactorsPhysicalCarrier w modes A)
      (combTranslationFactors w modes T) := by
  induction modes generalizing A T with
  | nil => exact hT
  | cons s modes ih => exact ih _ _ (atomicOnCarrier_combTranslationFactor A T hT w s)

private theorem vanishingQuadraticLowerCount_union_translate (A : LocallyFiniteCarrier)
    (w : ℝ) (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((A.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((((A.translate w).union A).carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2 := by
  let a : Bool → ℝ := fun b => if b then w else 0
  let C := finiteCombConvolutionCarrier A a
  have hsub : ((A.translate w).union A).carrier ⊆ C.carrier := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩ | hx
    · exact mem_finiteCombConvolutionCarrier A a true hy
    · simpa only [a, Bool.false_eq_true, ite_false, zero_add] using
        mem_finiteCombConvolutionCarrier A a false hx
  intro c hc
  refine (vanishingQuadraticLowerCount_finiteCombConvolutionCarrier A a hcount c hc).mono ?_
  intro R hR
  exact (Nat.cast_le.mpr (ncard_le_ncard (inter_subset_inter_left _ hsub)
    (C.finite_inter_Icc (-R) R))).trans_lt hR

/-- The class-eliminating product preserves arbitrarily small quadratic
counts at arbitrarily large radii on its actual physical support carrier. -/
theorem vanishingQuadraticLowerCount_combTranslationFactorsPhysicalCarrier (w : ℝ)
    (modes : List ℝ) (A : LocallyFiniteCarrier)
    (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((A.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      (((combTranslationFactorsPhysicalCarrier w modes A).carrier ∩ Icc (-R) R).ncard : ℝ) <
        c * R ^ 2 := by
  induction modes generalizing A with
  | nil => exact hcount
  | cons s modes ih => exact ih _ (vanishingQuadraticLowerCount_union_translate A w hcount)

end
end MeyerGeneralProblem
