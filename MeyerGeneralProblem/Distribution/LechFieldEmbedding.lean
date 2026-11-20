module

public import MeyerGeneralProblem.Distribution.PadicPowerSumZeros
public import MeyerGeneralProblem.Distribution.CombSupportCompletion
public import MeyerGeneralProblem.Distribution.PadicAdjoinedRootEmbedding
public import MeyerGeneralProblem.Distribution.RationalFunctionFieldPresentation

@[expose] public section

/-!
# Lech's embedding and the finite-hole classification

The original coefficients generate one finitely generated rational field.
The embedding places each prescribed base and its inverse in the
p-adic integers, making the image of every base a unit.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators

/-- Lech's field-embedding statement for finitely generated rational
subfields of the complex numbers and a prescribed finite set. -/
def LechPadicIntegralEmbedding : Prop :=
  ∀ L : IntermediateField ℚ ℂ, L.FG → ∀ S : Finset L,
    ∃ (p : ℕ) (_ : Fact p.Prime) (f : L →+* ℚ_[p]), ∀ x ∈ S, ‖f x‖ ≤ 1

/-- Every finitely generated rational subfield of the complex numbers
has a p-adic embedding integral on the prescribed finite set. -/
theorem lechPadicIntegralEmbedding : LechPadicIntegralEmbedding := by
  intro L hL S
  have : Algebra.EssFiniteType ℚ L := IntermediateField.essFiniteType_iff.mpr hL
  let : CharZero L := L.toSubfield.subtype.charZero
  obtain ⟨n, t, ht, f, hmonic, hdeg, hcop, ⟨hroot⟩⟩ :=
    exists_primitivePresentation_over_fin_transcendenceBasis L
  let F := IntermediateField.adjoin ℚ (Set.range t)
  let : Algebra (MvPolynomial (Fin n) ℤ) F := (integralTranscendenceEvaluation t).toAlgebra
  have : IsFractionRing (MvPolynomial (Fin n) ℤ) F :=
    isFractionRing_of_algIndependent_adjoin t ht.1
  exact exists_padicIntegralEmbedding_of_adjoinRoot_over_rationalFunctions n
    hmonic hdeg hcop hroot S

/-- Prescribe each phase and its inverse under the integral embedding
to transport a complex power sum to the p-adic unit theorem. -/
theorem complexPowerSumPadicEmbedding_of_lechIntegralEmbedding
    (hlech : LechPadicIntegralEmbedding) : ComplexPowerSumPadicEmbedding := by
  classical
  intro ι _ c z hz
  let W := range c ∪ range z
  have hW : W.Finite := (Set.finite_range c).union (Set.finite_range z)
  let L := IntermediateField.adjoin ℚ W
  have hL : L.FG := IntermediateField.fg_adjoin_of_finite hW
  have hcL (i : ι) : c i ∈ L := IntermediateField.subset_adjoin ℚ W
    (show c i ∈ W from Or.inl (mem_range_self i))
  have hzL (i : ι) : z i ∈ L := IntermediateField.subset_adjoin ℚ W
    (show z i ∈ W from Or.inr (mem_range_self i))
  let cL (i : ι) : L := ⟨c i, hcL i⟩
  let zL (i : ι) : L := ⟨z i, hzL i⟩
  let S := (Finset.univ.image cL) ∪ (Finset.univ.image zL) ∪
    (Finset.univ.image fun i => (zL i)⁻¹)
  obtain ⟨p, hp, f, hf⟩ := hlech L hL S
  let _ := hp
  refine ⟨p, hp, L.toSubfield, hcL, hzL, f, ?_⟩
  intro i
  change ‖f (zL i)‖ = 1
  have hbase : ‖f (zL i)‖ ≤ 1 := hf (zL i)
    (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  have hinv : ‖f ((zL i)⁻¹)‖ ≤ 1 := hf ((zL i)⁻¹)
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hnonzero : zL i ≠ 0 := fun h => hz i (congrArg Subtype.val h)
  have he : ‖f (zL i)‖ * ‖f ((zL i)⁻¹)‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hnonzero, map_one, norm_one]
  refine le_antisymm hbase ?_
  rw [← he]
  exact mul_le_of_le_one_right (norm_nonneg _) hinv

/-- Complex power-sum zeros are eventually periodic. -/
theorem complexPowerSum_eventuallyPeriodicZeros : OneSidedPowerSumEventuallyPeriodicZeros :=
  oneSidedPowerSumEventuallyPeriodicZeros_of_padicEmbedding
    (complexPowerSumPadicEmbedding_of_lechIntegralEmbedding lechPadicIntegralEmbedding)

/-- The actual coefficient support of every finite modulated comb has
a unique least full-lattice envelope with finite holes. -/
theorem IsFiniteModulatedDiracCombSum.exists_least_lattice_envelope
    (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier A T) (hcomb : IsFiniteModulatedDiracCombSum T) :
    ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, 0 < p.2) ∧
      ((affineLatticeUnionCarrier E).carrier \ actualAtomicSupport A T).Finite ∧
      IsLeast {L : Set ℝ | ∃ F : Finset (ℝ × ℝ), (∀ p ∈ F, 0 < p.2) ∧
        L = (affineLatticeUnionCarrier F).carrier ∧ actualAtomicSupport A T ⊆ L}
        (affineLatticeUnionCarrier E).carrier := by
  obtain ⟨E, hE, hcover, hh⟩ := hcomb.hasCofiniteLatticeCover_actualAtomicSupport
    (bilateralPowerSumCofiniteSupport_of_oneSidedEventuallyPeriodicZeros
      complexPowerSum_eventuallyPeriodicZeros) A T hT
  exact ⟨E, hE, hh, affineLatticeUnion_isLeast_of_cofinite_cover _ E hE hcover hh⟩

/-- The p-adic proof now gives the complete finite-hole dimension rule
as soon as the finitely generated field-embedding statement is supplied. -/
theorem boundedCount_commonSpace_holeClassification_of_lechIntegralEmbedding
    (hlech : LechPadicIntegralEmbedding) (S : LocallyFiniteCarrier) (K : ℕ)
    (hK : UnitCellBound S K) :
    let V := DistributionalMeyerPairSpace S S
    V = finiteHoleEnvelopeSpace S ∧
      (∃ E : FiniteHoleEnvelope S, V = E.embeddedSpace ∧
        Module.finrank ℂ V = E.nullity ∧ ∀ F : FiniteHoleEnvelope S, F.nullity ≤ E.nullity) ∧
      (V ≠ ⊥ ↔ ∃ E : FiniteHoleEnvelope S, 0 < E.nullity) :=
  boundedCount_commonSpace_holeClassification_of_powerSumSupport
    (bilateralPowerSumCofiniteSupport_of_oneSidedEventuallyPeriodicZeros
      (oneSidedPowerSumEventuallyPeriodicZeros_of_padicEmbedding
        (complexPowerSumPadicEmbedding_of_lechIntegralEmbedding hlech))) S K hK

/-- On every bounded-count common carrier the complete space equals a
finite-hole envelope kernel attaining the maximum nullity. -/
theorem boundedCount_commonSpace_holeClassification
    (S : LocallyFiniteCarrier) (K : ℕ) (hK : UnitCellBound S K) :
    let V := DistributionalMeyerPairSpace S S
    V = finiteHoleEnvelopeSpace S ∧
      (∃ E : FiniteHoleEnvelope S, V = E.embeddedSpace ∧
        Module.finrank ℂ V = E.nullity ∧ ∀ F : FiniteHoleEnvelope S, F.nullity ≤ E.nullity) ∧
      (V ≠ ⊥ ↔ ∃ E : FiniteHoleEnvelope S, 0 < E.nullity) :=
  boundedCount_commonSpace_holeClassification_of_lechIntegralEmbedding
    lechPadicIntegralEmbedding S K hK

end
end MeyerGeneralProblem
