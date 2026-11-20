module

public import MeyerGeneralProblem.Distribution.FiniteHoleEnvelope
public import MeyerGeneralProblem.Distribution.BoundedCountCombClosure

@[expose] public section

/-!
# From original cofinite supports to the whole bounded-count space

The remaining support-completion input is isolated at the original
nonzero coefficients of an individual finite comb. Once supplied,
the common-carrier theorem returns the full directed union and its
attained joint-hole nullity.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped FourierTransform

/-- The actual nonzero coefficient set of an original value-only record. -/
def actualAtomicSupport (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) : Set ℝ :=
  Function.support (extendedAtomicCoefficient A T)

/-- A positive-step full-lattice union containing the entire set and
differing from it by finitely many missing points. -/
def HasCofiniteLatticeCover (A : Set ℝ) : Prop :=
  ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, 0 < p.2) ∧ A ⊆ (affineLatticeUnionCarrier E).carrier ∧
    ((affineLatticeUnionCarrier E).carrier \ A).Finite

theorem actualAtomicSupport_subset (A : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) : actualAtomicSupport A T ⊆ A.carrier := by
  classical
  intro x hx
  by_contra hn
  exact hx (by simp [extendedAtomicCoefficient, hn])

private theorem atomicOnCarrier_commonCarrierIntersection_of_support
    (A L : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier A T) (hL : actualAtomicSupport A T ⊆ L.carrier) :
    AtomicOnCarrier (commonCarrierIntersection L A) T := by
  have hR : AtomicOnCarrier (A.restrict (A.carrier ∩ L.carrier) inter_subset_left) T := by
    apply (atomicOnCarrier_restrict_iff A _ inter_subset_left T).mpr
    refine ⟨hT, fun x hx => ?_⟩
    by_contra hzero
    apply hx
    refine ⟨x.property, hL ?_⟩
    change extendedAtomicCoefficient A T (x : ℝ) ≠ 0
    have hxA : (x : ℝ) ∈ A.carrier := x.property
    rw [extendedAtomicCoefficient, dite_eq_left hxA]
    exact hzero
  exact hR.mono (S := A.restrict (A.carrier ∩ L.carrier) inter_subset_left)
    (T := commonCarrierIntersection L A)
    (fun x (hx : x ∈ A.carrier ∩ L.carrier) => ⟨hx.2, hx.1⟩)

/-- Containment of all actual nonzero coefficients restricts the
original value-only action to the specified carrier. -/
theorem atomicOnCarrier_of_actualAtomicSupport_subset
    (A L : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier A T) (hL : actualAtomicSupport A T ⊆ L.carrier) :
    AtomicOnCarrier L T :=
  (atomicOnCarrier_commonCarrierIntersection_of_support A L T hT hL).mono inter_subset_left

/-- Cofinite original supports on the two records place the original
distribution in one literal joint-hole kernel. -/
theorem mem_finiteHoleEnvelopeSpace_of_cofinite_original_supports
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ DistributionalMeyerPairSpace S S)
    (hcover : HasCofiniteLatticeCover (actualAtomicSupport S T))
    (hFcover : HasCofiniteLatticeCover (actualAtomicSupport S (𝓕 T))) :
    T ∈ finiteHoleEnvelopeSpace S := by
  obtain ⟨E, hE, hcover, hfin⟩ := hcover
  obtain ⟨F, hF, hFcover, hFfin⟩ := hFcover
  have hE' : ((affineLatticeUnionCarrier E).carrier \ S.carrier).Finite :=
    hfin.subset fun _ hx => ⟨hx.1, fun hs => hx.2 (actualAtomicSupport_subset S T hs)⟩
  have hF' : ((affineLatticeUnionCarrier F).carrier \ S.carrier).Finite :=
    hFfin.subset fun _ hx => ⟨hx.1, fun hs => hx.2 (actualAtomicSupport_subset S (𝓕 T) hs)⟩
  let E' : FiniteHoleEnvelope S := ⟨E, hE, hE'⟩
  let F' : FiniteHoleEnvelope S := ⟨F, hF, hF'⟩
  let G := E'.union F'
  have hp := (mem_distributionalMeyerPairSpace_iff _ _ T).mp hT
  apply (mem_finiteHoleEnvelopeSpace S T).mpr
  refine ⟨G, (mem_distributionalMeyerPairSpace_iff _ _ T).mpr ⟨?_, ?_⟩⟩
  · exact atomicOnCarrier_commonCarrierIntersection_of_support S G.carrier T hp.1
      (hcover.trans (E'.carrier_subset_union_left F'))
  · exact atomicOnCarrier_commonCarrierIntersection_of_support S G.carrier (𝓕 T) hp.2
      (hFcover.trans (E'.carrier_subset_union_right F'))

/-- Whole-space directed union, finite attainment and the nonzero criterion
once finite-comb original support completion has been proved. -/
theorem boundedCount_commonSpace_holeClassification_of_combSupportCompletion
    (S : LocallyFiniteCarrier) (K : ℕ) (hK : UnitCellBound S K)
    (hcomplete : ∀ U : TemperedDistribution ℝ ℂ, AtomicOnCarrier S U →
      IsFiniteModulatedDiracCombSum U → HasCofiniteLatticeCover (actualAtomicSupport S U)) :
    let V := DistributionalMeyerPairSpace S S
    V = finiteHoleEnvelopeSpace S ∧
      (∃ E : FiniteHoleEnvelope S, V = E.embeddedSpace ∧
        Module.finrank ℂ V = E.nullity ∧ ∀ F : FiniteHoleEnvelope S, F.nullity ≤ E.nullity) ∧
      (V ≠ ⊥ ↔ ∃ E : FiniteHoleEnvelope S, 0 < E.nullity) := by
  have hEq : DistributionalMeyerPairSpace S S = finiteHoleEnvelopeSpace S := by
    apply le_antisymm ?_ (finiteHoleEnvelopeSpace_le S)
    intro T hT
    have hp := (mem_distributionalMeyerPairSpace_iff S S T).mp hT
    have hcomb := finiteModulatedDiracCombSum_pair_of_two_unitCellBounds S S K K hK hK T hT
    exact mem_finiteHoleEnvelopeSpace_of_cofinite_original_supports S T hT
      (hcomplete T hp.1 hcomb.1) (hcomplete (𝓕 T) hp.2 hcomb.2)
  dsimp only
  rw [hEq]
  exact ⟨rfl, exists_maximal_finiteHoleEnvelope S K hK, finiteHoleEnvelopeSpace_ne_bot_iff S K hK⟩

end
end MeyerGeneralProblem
