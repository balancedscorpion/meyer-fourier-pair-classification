module

public import MeyerGeneralProblem.Carrier.SynthesisInjectivity
public import MeyerGeneralProblem.Carrier.CoefficientTail
public import MeyerGeneralProblem.Gram.CarrierUniversalCompactness
public import MeyerGeneralProblem.Gram.ClosedRange
public import MeyerGeneralProblem.Gram.CompactPositivePerturbation

@[expose] public section

/-!
# Strict positivity of the genuine carrier tail Gram

The compact comparison supplies a Fredholm operator, while genuine
distributional point-mass synthesis supplies injectivity.  Combining them
eliminates the possible finite-dimensional kernel of the carrier tail Gram.
-/

namespace MeyerGeneralProblem

noncomputable section

namespace CarrierUniversalTailData

variable {Λ : TwoSidedCarrier} (D : CarrierUniversalTailData Λ)

/-- The genuine normalized carrier synthesis remains injective after the
finite tail restriction. -/
theorem carrierSynthesis_injective
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    Function.Injective (D.carrierSynthesis m hm B) := by
  change Function.Injective (D.carrierBesselAnalysis m hm B).synthesis
  apply normalizedPointMassSynthesis_injective_of_isolatingSchwartz
    m hm (fun j : {j : ℤ // j ∉ D.F} => Λ j)
  intro i
  refine ⟨Λ.isolationSchwartz i, Λ.isolationSchwartz_self i, ?_⟩
  intro j hji
  exact Λ.isolationSchwartz_of_ne
    ((Subtype.coe_injective.ne hji).symm)

/-- The genuine carrier tail Gram has trivial kernel. -/
theorem carrierGramOperator_injective
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    Function.Injective (D.carrierGramOperator m hm B) := by
  let S := D.carrierSynthesis m hm B
  have hS : Function.Injective S := D.carrierSynthesis_injective m hm B
  have hGram := S.adjoint_comp_self_injective_iff.mpr hS
  simpa only [carrierGramOperator, coefficientGram,
    ContinuousLinearMap.coe_comp] using hGram

set_option linter.style.haveILetI false in
/-- The universal tail Gram is strictly positive, not merely nonnegative. -/
theorem gramOperator_strictlyPositive
    (m : ℕ) (hm : 1 ≤ m) :
    IsStrictlyPositive (D.gramOperator m hm) := by
  obtain ⟨j, hj⟩ := D.F.exists_not_mem_of_card_lt_enatCard (by simp)
  let jTail : {j : ℤ // j ∉ D.F} := ⟨j, hj⟩
  letI : Nontrivial (CoefficientSpace {j : ℤ // j ∉ D.F}) :=
    nontrivial_of_ne (coefficientAtom jTail) 0 (by
      apply norm_ne_zero_iff.mp
      rw [coefficientAtom_norm]
      norm_num)
  have hA : 0 < universalGramLowerConstant m D.a D.d :=
    universalGramLowerConstant_pos hm D.ha D.had
  exact strictlyPositive_of_positive_scalar_floor
    (D.gramOperator m hm) hA (D.gramOperator_lowerBound m hm)

set_option linter.style.haveILetI false in
/-- The genuine normalized carrier tail Gram is strictly positive.  The
Fredholm alternative removes the finite-dimensional kernel left open by the
compact comparison. -/
theorem carrierGramOperator_strictlyPositive
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    IsStrictlyPositive (D.carrierGramOperator m hm B) := by
  obtain ⟨j, hj⟩ := D.F.exists_not_mem_of_card_lt_enatCard (by simp)
  let jTail : {j : ℤ // j ∉ D.F} := ⟨j, hj⟩
  letI : Nontrivial (CoefficientSpace {j : ℤ // j ∉ D.F}) :=
    nontrivial_of_ne (coefficientAtom jTail) 0 (by
      apply norm_ne_zero_iff.mp
      rw [coefficientAtom_norm]
      norm_num)
  let G := D.carrierGramOperator m hm B
  let H := D.gramOperator m hm
  have hG : 0 ≤ G := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive).mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self
        (D.carrierSynthesis m hm B))
  have hcompact : IsCompactOperator (G - H) := by
    simpa only [G, H, carrierGramDifference] using
      D.carrierGramDifference_isCompact m hm B
  exact strictlyPositive_of_compact_perturbation_of_injective G H hG
    (D.gramOperator_strictlyPositive m hm) hcompact
    (D.carrierGramOperator_injective m hm B)

/-- Full carrier synthesis after extension by zero is exactly the separated
tail synthesis. -/
theorem carrierPointMassSynthesis_comp_tailCoefficientEmbedding
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    (carrierPointMassSynthesis m hm Λ B).comp
        (tailCoefficientEmbedding D.F) =
      D.carrierSynthesis m hm B := by
  apply ContinuousLinearMap.ext_on
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact coefficientAtom_dense_span
  · rintro _ ⟨j, rfl⟩
    rw [ContinuousLinearMap.comp_apply,
      tailCoefficientEmbedding_coefficientAtom,
      carrierPointMassSynthesis_coefficientAtom,
      carrierSynthesis,
      BesselAnalysis.synthesis_coefficientAtom]

/-- Restricting full carrier synthesis to coefficient vectors with zero
deleted coordinates has exactly the separated-tail range. -/
theorem carrierPointMassSynthesis_domRestrict_range_eq_tail
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    ((carrierPointMassSynthesis m hm Λ B).domRestrict
      (finiteCoordinateProjection D.F).toLinearMap.ker).range =
        (D.carrierSynthesis m hm B).range := by
  let S := carrierPointMassSynthesis m hm Λ B
  let E := tailCoefficientEmbedding D.F
  let A := (finiteCoordinateProjection D.F).toLinearMap.ker
  have hintertwine : S.comp E = D.carrierSynthesis m hm B := by
    exact D.carrierPointMassSynthesis_comp_tailCoefficientEmbedding m hm B
  have hErange : E.range = A := by
    exact tailCoefficientEmbedding_range_eq_ker D.F
  apply le_antisymm
  · rintro y ⟨c, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, E d = c := by
      have hc : c.1 ∈ E.range := by
        rw [hErange]
        exact c.2
      rcases hc with ⟨d, hd⟩
      exact ⟨d, hd⟩
    refine ⟨d, ?_⟩
    change D.carrierSynthesis m hm B d = S c.1
    have happly := congrArg
      (fun T : CoefficientSpace {j : ℤ // j ∉ D.F} →L[ℂ]
        HermiteScale (-(m : ℤ)) => T d) hintertwine
    simpa only [ContinuousLinearMap.comp_apply, hd] using happly.symm
  · rintro y ⟨d, rfl⟩
    have hEd : E d ∈ A := by
      rw [← hErange]
      exact ⟨d, rfl⟩
    refine ⟨⟨E d, hEd⟩, ?_⟩
    change S (E d) = D.carrierSynthesis m hm B d
    have happly := congrArg
      (fun T : CoefficientSpace {j : ℤ // j ∉ D.F} →L[ℂ]
        HermiteScale (-(m : ℤ)) => T d) hintertwine
    simpa only [ContinuousLinearMap.comp_apply] using happly

/-- The full genuine carrier synthesis has closed range.  Closed range first
holds on the separated tail by strict tail-Gram positivity, then passes across
the finitely many deleted coefficient coordinates. -/
theorem carrierPointMassSynthesis_isClosed_range
    (D : CarrierUniversalTailData Λ)
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    IsClosed (Set.range (carrierPointMassSynthesis m hm Λ B)) := by
  let S := carrierPointMassSynthesis m hm Λ B
  let A := (finiteCoordinateProjection D.F).toLinearMap.ker
  let _ : A.CoFG := by
    dsimp only [A]
    exact finiteCoordinateProjection_ker_coFG D.F
  have hAclosed : IsClosed (A : Set (CoefficientSpace ℤ)) := by
    dsimp only [A]
    exact (finiteCoordinateProjection D.F).isClosed_ker
  have htailClosed :
      IsClosed (Set.range (D.carrierSynthesis m hm B)) := by
    exact isClosed_range_of_coefficientGram_strictlyPositive
      (D.carrierSynthesis m hm B)
      (by simpa only [carrierGramOperator] using
        D.carrierGramOperator_strictlyPositive m hm B)
  have hrestrictedClosed :
      IsClosed (Set.range (S.domRestrict A)) := by
    change IsClosed ((S.domRestrict A).range :
      Set (HermiteScale (-(m : ℤ))))
    rw [show (S.domRestrict A).range =
        (D.carrierSynthesis m hm B).range by
      simpa only [S, A] using
        D.carrierPointMassSynthesis_domRestrict_range_eq_tail m hm B]
    exact htailClosed
  have hSinj : Function.Injective S :=
    carrierPointMassSynthesis_injective m hm Λ B
  have hrestrictedInj : Function.Injective (S.domRestrict A) := by
    intro x y hxy
    apply Subtype.ext
    exact hSinj hxy
  obtain ⟨K, hK⟩ :=
    (S.domRestrict A).antilipschitz_of_injective_of_isClosed_range
      hrestrictedInj hrestrictedClosed
  have hembedding : Topology.IsEmbedding (S.domRestrict A) :=
    hK.isEmbedding (S.domRestrict A).continuous
  have hrestrictedStrict : Topology.IsStrictMap (S.domRestrict A) :=
    (Topology.isEmbedding_iff_isStrictMap_injective.mp hembedding).1
  exact (S.isStrictMap_isClosed_range_iff_restrict A hAclosed).mpr
    ⟨hrestrictedStrict, hrestrictedClosed⟩ |>.2

/-- The full genuine normalized carrier Gram is strictly positive.  This is
the lower Riesz bound consumed by global coefficient whitening. -/
theorem carrierCoefficientGram_strictlyPositive
    (D : CarrierUniversalTailData Λ)
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    IsStrictlyPositive
      (coefficientGram (carrierPointMassSynthesis m hm Λ B)) := by
  let _ : Nontrivial (CoefficientSpace ℤ) :=
    nontrivial_of_ne (coefficientAtom (0 : ℤ)) 0 (by
      apply norm_ne_zero_iff.mp
      rw [coefficientAtom_norm]
      norm_num)
  let S := carrierPointMassSynthesis m hm Λ B
  have h := adjoint_comp_self_strictlyPositive_of_injective_of_isClosed_range
    S (carrierPointMassSynthesis_injective m hm Λ B)
      (D.carrierPointMassSynthesis_isClosed_range m hm B)
  simpa only [coefficientGram, S] using h

end CarrierUniversalTailData

end

end MeyerGeneralProblem
