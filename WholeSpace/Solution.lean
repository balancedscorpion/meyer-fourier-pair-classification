module

public import MeyerGeneralProblem.Distribution.BoundedCountCombClosure
public import MeyerGeneralProblem.Distribution.CommonPairAnnihilator
public import MeyerGeneralProblem.Distribution.LechFieldEmbedding
public import MeyerGeneralProblem.Distribution.LatticeEnvelopeResidueCoordinates

@[expose] public section
noncomputable section
namespace MeyerGeneralProblem

open scoped FourierTransform

/-- On each Schwartz test, the action is evaluation on its pointwise product
with the positive-phase exponential polynomial. -/
theorem finiteExponentialMultiplication_on_tests {ι : Type} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    ∃ g : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, g x = (∑ i, c i * combModulationCharacter (a i) x) * f x) ∧
      finiteExponentialMultiplication a c T f = T g := by
  refine ⟨finiteCombSchwartzSymbol (fun i => -a i) c f, ?_, finiteExponentialMultiplication_apply a c T f⟩
  intro x
  simp only [finiteCombSchwartzSymbol_apply, finiteCombFourierSymbol, neg_neg]

theorem mem_atomicSupportUnion_iff (S : LocallyFiniteCarrier)
    (V : Submodule ℂ (TemperedDistribution ℝ ℂ)) (x : ℝ) :
    x ∈ (atomicSupportUnion S V).carrier ↔
      ∃ hx : x ∈ S.carrier, ∃ U : V,
        (U : TemperedDistribution ℝ ℂ) (S.isolationSchwartz ⟨x, hx⟩) ≠ 0 := Iff.rfl

theorem atomicCoefficientLinearMap_on_tests (A : LocallyFiniteCarrier) (x : A.subtype)
    (T : TemperedDistribution ℝ ℂ) :
    atomicCoefficientLinearMap A x T = T (A.isolationSchwartz x) := rfl

theorem commonCarrierHoleRows_apply_pair (L S : LocallyFiniteCarrier)
    (T : DistributionalMeyerPairSpace L L) (x : CommonCarrierHole L S) :
    commonCarrierHoleRows L S T x =
      ((T : TemperedDistribution ℝ ℂ) (L.isolationSchwartz x.val),
       (𝓕 (T : TemperedDistribution ℝ ℂ)) (L.isolationSchwartz x.val)) := rfl

namespace FiniteHoleEnvelope
theorem nullity_eq_dimension_sub_rank {S : LocallyFiniteCarrier} (E : FiniteHoleEnvelope S) :
    E.nullity = Module.finrank ℂ (DistributionalMeyerPairSpace E.carrier E.carrier) -
      Module.finrank ℂ (LinearMap.range (commonCarrierHoleRows E.carrier S)) := rfl
end FiniteHoleEnvelope

theorem latticeOrbitResidueRows_apply_entry {ι : Type*} (A : LocallyFiniteCarrier) (w : ℝ)
    (origin : ι → ℝ) (modes : List ℝ) (p : ℕ) (c : ι → Fin modes.length → ℂ)
    (r : ForbiddenLatticeOrbitResidue A w origin p) (n : Fin modes.length) :
    latticeOrbitResidueRows A w origin modes p c r n =
      ∑ j, c r.val.1 j * combModulationCharacter (modes.get j)
        (origin r.val.1 + (((r.val.2.val : ℤ) - (n.val : ℤ) * (p : ℤ) : ℤ) : ℝ) * w) := rfl

end MeyerGeneralProblem
end
