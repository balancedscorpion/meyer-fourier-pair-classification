module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Annihilation and finite-comb classification from finite lower density on one ray

A single sequence of arbitrarily large radii on either ray suffices for
annihilation. The two comb theorems use the actual carrier on the counted
side and zero lower quadratic density on the opposite side.
-/

@[expose] public section
noncomputable section
namespace MeyerGeneralProblem

open Set Filter
open scoped FourierTransform BigOperators SchwartzMap PointwiseConvergenceCLM

/-- A subset of the real line having finite intersection with every closed
bounded interval. -/
structure LocallyFiniteCarrier where
  /-- The underlying extensional carrier. -/
  carrier : Set ℝ
  /-- Every bounded closed interval contains only finitely many carrier points. -/
  finite_inter_Icc : ∀ a b : ℝ, (carrier ∩ Set.Icc a b).Finite

namespace LocallyFiniteCarrier

variable (S : LocallyFiniteCarrier)

/-- The type of points of an extensional carrier. -/
def subtype := S.carrier

/-- A complex Schwartz test isolating the selected physical carrier node. -/
def isolationSchwartz (x : S.subtype) : SchwartzMap ℝ ℂ := by
  sorry

theorem isolationSchwartz_apply_subtype (x y : S.subtype) :
    S.isolationSchwartz x y = if y = x then 1 else 0 := by
  sorry

end LocallyFiniteCarrier

/-- A Schwartz function vanishes on every point of an extensional locally
finite carrier. -/
def SchwartzVanishesOn (S : LocallyFiniteCarrier) (f : SchwartzMap ℝ ℂ) : Prop :=
  ∀ x ∈ S.carrier, f x = 0

/-- A tempered distribution is order-zero supported on `S` when it
annihilates every Schwartz function vanishing on the whole carrier. -/
def AtomicOnCarrier (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) : Prop :=
  ∀ f : SchwartzMap ℝ ℂ, SchwartzVanishesOn S f → T f = 0

/-- The actual positive Fourier character at a physical real point. -/
def combModulationCharacter (a x : ℝ) : ℂ := (Real.fourierChar (a*x) : ℂ)

/-- The original affine comb multiplied by the character of frequency `s`. -/
def modulatedAffineDiracComb (w : ℝ) (hw : 0 < w) (y s : ℝ) :
    TemperedDistribution ℝ ℂ := by
  sorry

theorem modulatedAffineDiracComb_apply (w : ℝ) (hw : 0 < w) (y s : ℝ)
    (f : SchwartzMap ℝ ℂ) :
    modulatedAffineDiracComb w hw y s f =
      ∑' k : ℤ, combModulationCharacter s (y + (k : ℝ) * w) * f (y + (k : ℝ) * w) := by
  sorry

/-- One summand in the finite affine comb expansion. -/
structure AffineCombTerm where
  /-- The frequency of the modulating character. -/
  frequency : ℝ
  /-- The translate of the physical lattice. -/
  origin : ℝ
  /-- The scalar amplitude multiplying the modulated comb. -/
  coefficient : ℂ

/-- The original tempered distribution defined by one comb summand. -/
def AffineCombTerm.distribution (q : AffineCombTerm) (w : ℝ) (hw : 0 < w) :
    TemperedDistribution ℝ ℂ :=
  q.coefficient • modulatedAffineDiracComb w hw q.origin q.frequency

/-- The distribution is a finite sum of actual modulated Dirac combs. -/
def IsFiniteModulatedDiracCombSum (T : TemperedDistribution ℝ ℂ) : Prop :=
  ∃ (ι : Type) (inst : Fintype ι), letI := inst
    ∃ (q : ι → AffineCombTerm) (w : ι → ℝ) (hw : ∀ i, 0 < w i),
      T = ∑ i, (q i).distribution (w i) (hw i)

/-- Multiplication by the literal positive-phase finite exponential symbol. -/
def finiteExponentialMultiplication {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ := by
  sorry

/-- On each Schwartz test, the action is evaluation on its pointwise product
with the positive-phase exponential polynomial. -/
theorem finiteExponentialMultiplication_on_tests {ι : Type} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    ∃ g : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, g x = (∑ i, c i * combModulationCharacter (a i) x) * f x) ∧
      finiteExponentialMultiplication a c T f = T g := by
  sorry

/-- The closed origin-based window on the positive or negative real ray. -/
def originalRayWindow (positive : Bool) (r : ℝ) : Set ℝ :=
  if positive then Icc 0 r else Icc (-r) 0

/-- The original point count on the chosen ray through radius `r`. -/
noncomputable def originalRayCount (A : LocallyFiniteCarrier) (positive : Bool) (r : ℝ) : ℕ :=
  (A.carrier ∩ originalRayWindow positive r).ncard

/-- Finite lower linear density on the chosen ray, expressed by a bound
on arbitrarily large radii. -/
def HasFiniteLowerRayCount (A : LocallyFiniteCarrier) (positive : Bool) : Prop :=
  ∃ C : ℝ, ∃ᶠ r : ℝ in atTop, (originalRayCount A positive r : ℝ) ≤ C * r

/-- One finite lower ray count gives a nonzero exponential polynomial
annihilating the entire physical record of an original broad pair. -/
theorem exists_finiteExponentialAnnihilator_of_finite_lower_ray_count
    (A B : LocallyFiniteCarrier) (positive : Bool)
    (hCount : HasFiniteLowerRayCount A positive) (U : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A U) (hB : AtomicOnCarrier B (𝓕 U)) :
    ∃ (ι : Type) (inst : Fintype ι), letI := inst
      ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
        (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
        finiteExponentialMultiplication a c U = 0 := by
  sorry

/-- One finite lower ray count and opposite quadratic lower density
zero imply finite modulated Dirac comb sums on both records. -/
theorem finiteModulatedDiracCombSum_pair_of_finite_lower_ray_count
    (A B : LocallyFiniteCarrier) (positive : Bool)
    (hCount : HasFiniteLowerRayCount A positive) (T : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (hActual : ∀ x : A.subtype, T (A.isolationSchwartz x) ≠ 0)
    (hQuadratic : ∀ c : ℝ, 0 < c → ∃ᶠ r : ℝ in atTop,
      ((B.carrier ∩ Icc (-r) r).ncard : ℝ) < c * r ^ 2) :
    IsFiniteModulatedDiracCombSum T ∧ IsFiniteModulatedDiracCombSum (𝓕 T) := by
  sorry

/-- The finite lower ray hypothesis may instead be on the original
Fourier record, with quadratic lower density zero on the physical record. -/
theorem finiteModulatedDiracCombSum_pair_of_fourier_finite_lower_ray_count
    (A B : LocallyFiniteCarrier) (positive : Bool)
    (hCount : HasFiniteLowerRayCount B positive) (T : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (hActual : ∀ x : B.subtype, (𝓕 T) (B.isolationSchwartz x) ≠ 0)
    (hQuadratic : ∀ c : ℝ, 0 < c → ∃ᶠ r : ℝ in atTop,
      ((A.carrier ∩ Icc (-r) r).ncard : ℝ) < c * r ^ 2) :
    IsFiniteModulatedDiracCombSum T ∧ IsFiniteModulatedDiracCombSum (𝓕 T) := by
  sorry

end MeyerGeneralProblem
end
