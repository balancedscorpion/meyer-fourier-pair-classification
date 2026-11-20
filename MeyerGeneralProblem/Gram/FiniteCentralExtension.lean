module

public import MeyerGeneralProblem.Carrier.CoefficientTail
public import MeyerGeneralProblem.Cross.CompactRemainder

@[expose] public section

/-!
# Restoring finitely many actual atoms

Finite central atoms give an explicit finite-rank synthesis. Adding it to
the extended tail synthesis proves the Bessel property for the full family.
Compactness of a genuine tail restriction similarly extends across the
central rows and columns, without estimates in a singular coordinate chart.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {ι H : Type*} [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace BesselAnalysis

/-- A genuine Bessel tail extends over an arbitrary finite set of original
atoms, by explicit synthesis of those atoms. -/
def of_finite_tail (v : ι → H) (F : Finset ι)
    (B : BesselAnalysis (fun i : {i : ι // i ∉ F} => v i.val)) :
    BesselAnalysis v := by
  let S : CoefficientSpace ι →L[ℂ] H :=
    (∑ i ∈ F, InnerProductSpace.rankOne ℂ (v i) (coefficientAtom i)) +
      B.synthesis ∘L (tailCoefficientEmbedding F).adjoint
  have hS (j : ι) : S (coefficientAtom j) = v j := by
    simp only [S, add_apply, _root_.sum_apply, InnerProductSpace.rankOne_apply,
      ContinuousLinearMap.comp_apply, tailCoefficientEmbedding_adjoint_coefficientAtom]
    simp_rw [show ∀ i, inner ℂ (coefficientAtom i) (coefficientAtom j) =
      if i = j then 1 else 0 from fun i =>
        orthonormal_iff_ite.mp (coefficientHilbertBasis ι).orthonormal i j]
    by_cases hj : j ∈ F
    · simp [hj]
    · simp [hj]
  refine ⟨S.adjoint, ?_⟩
  intro x i
  change (coefficientHilbertBasis ι).repr (S.adjoint x) i = _
  rw [(coefficientHilbertBasis ι).repr_apply_apply,
    ContinuousLinearMap.adjoint_inner_right]
  exact congrArg (fun y => inner ℂ y x) (hS i)

/-- A family is Bessel when an actual cofinite subfamily is Bessel. The
finite complement is retained with its original vectors. -/
def of_finite_complement (v : ι → H) (P : ι → Prop)
    (hfinite : Set.Finite {i | ¬ P i})
    (B : BesselAnalysis (fun i : {i // P i} => v i.val)) : BesselAnalysis v := by
  classical
  let F := hfinite.toFinset
  let e : {i : ι // i ∉ F} ↪ {i : ι // P i} :=
    ⟨fun i => ⟨i.val, by
      have h := i.property
      simpa only [F, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using h⟩,
      fun i j hij => Subtype.ext (congrArg (fun x : {i // P i} => x.val) hij)⟩
  exact of_finite_tail v F (B.reindex e)

end BesselAnalysis

/-- A bounded operator with compact actual tail restriction is compact
after all finitely many central rows and columns are restored. -/
theorem isCompactOperator_of_compact_tailRestriction
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) (F : Finset ι)
    (hT : IsCompactOperator
      ((tailCoefficientEmbedding F).adjoint ∘L T ∘L tailCoefficientEmbedding F)) :
    IsCompactOperator T := by
  have hQ : IsCompactOperator (cofiniteCoordinateCompression T F) := by
    have h := extendTailOperator_isCompact F _ hT
    convert h using 1
    unfold extendTailOperator cofiniteCoordinateCompression cofiniteCoordinateProjection
    rw [← tailCoefficientEmbedding_comp_adjoint F]
    simp only [ContinuousLinearMap.comp_assoc]
  have hsum := (finiteCentralTruncation_isCompact T F).add hQ
  have heq : finiteCentralTruncation T F + cofiniteCoordinateCompression T F = T := by
    have h := finiteCentralTruncation_sub_eq_neg_cofiniteCoordinateCompression T F
    apply sub_eq_zero.mp
    calc
      _ = (finiteCentralTruncation T F - T) + cofiniteCoordinateCompression T F := by abel
      _ = 0 := by rw [h]; exact neg_add_cancel _
  change IsCompactOperator (finiteCentralTruncation T F + cofiniteCoordinateCompression T F) at hsum
  rwa [heq] at hsum

end

end MeyerGeneralProblem
