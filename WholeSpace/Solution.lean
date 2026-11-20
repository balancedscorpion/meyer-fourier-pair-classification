module

public import MeyerGeneralProblem.Distribution.BoundedCountCombClosure
public import MeyerGeneralProblem.Distribution.CommonPairAnnihilator
public import MeyerGeneralProblem.Distribution.LechFieldEmbedding
public import MeyerGeneralProblem.Distribution.LatticeEnvelopeResidueCoordinates

@[expose] public section
noncomputable section
namespace MeyerGeneralProblem

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

end MeyerGeneralProblem
end
