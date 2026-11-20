module

public import MeyerGeneralProblem.Fredholm.ExtendedIndex
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Path

@[expose] public section

/-!
# Extended-index transport along upper semi-Fredholm paths

The full extended index is locally constant on every continuous upper
semi-Fredholm family and hence constant on connected parameter sets.
The finite-versus-infinite cokernel predicate is also proved separately:
the minus-infinity branch persists along every continuous path, without
any finite-cokernel premise.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter
open scoped Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The full extended index of a continuous upper semi-Fredholm family is
locally constant, including at minus infinity. -/
theorem isLocallyConstant_extendedFredholmIndex
    {X : Type*} [TopologicalSpace X] (A : X → E →L[ℂ] F)
    (hA : Continuous A) (hupper : ∀ x, IsUpperSemiFredholm (A x)) :
    IsLocallyConstant (fun x => extendedFredholmIndex (A x)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  exact (hA.tendsto x).eventually (hupper x).eventually_extendedIndex_eq

/-- The extended index is constant on every connected continuous upper
semi-Fredholm family. -/
theorem extendedFredholmIndex_eq_of_preconnected_family
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (A : X → E →L[ℂ] F) (hA : Continuous A)
    (hupper : ∀ x, IsUpperSemiFredholm (A x)) (x y : X) :
    extendedFredholmIndex (A x) = extendedFredholmIndex (A y) :=
  (isLocallyConstant_extendedFredholmIndex A hA hupper).apply_eq_of_preconnectedSpace x y

/-- The full extended index agrees at the endpoints of every upper
semi-Fredholm path. -/
theorem extendedFredholmIndex_eq_of_upperSemiFredholm_path
    {T U : E →L[ℂ] F} (p : Path T U)
    (hp : ∀ t, IsUpperSemiFredholm (p t)) :
    extendedFredholmIndex T = extendedFredholmIndex U := by
  have h := extendedFredholmIndex_eq_of_preconnected_family p p.continuous hp 0 1
  simpa only [p.source, p.target] using h

/-- Along a continuous upper semi-Fredholm family, membership in the
minus-infinity branch of the extended index is locally constant. -/
theorem isLocallyConstant_extendedIndex_eq_bot
    {X : Type*} [TopologicalSpace X] (A : X → E →L[ℂ] F)
    (hA : Continuous A) (hupper : ∀ x, IsUpperSemiFredholm (A x)) :
    IsLocallyConstant (fun x => extendedFredholmIndex (A x) = ⊥) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [(hA.tendsto x).eventually
    (hupper x).eventually_extendedIndex_eq_bot_iff] with y hy
  exact propext hy

/-- On a connected parameter set, an upper semi-Fredholm family has an
infinite-dimensional cokernel either everywhere or nowhere. -/
theorem extendedIndex_eq_bot_iff_of_preconnected_family
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (A : X → E →L[ℂ] F) (hA : Continuous A)
    (hupper : ∀ x, IsUpperSemiFredholm (A x)) (x y : X) :
    extendedFredholmIndex (A x) = ⊥ ↔ extendedFredholmIndex (A y) = ⊥ := by
  exact Iff.of_eq ((isLocallyConstant_extendedIndex_eq_bot A hA hupper).apply_eq_of_preconnectedSpace
    x y)

/-- Finite-cokernel equivalence on a connected upper semi-Fredholm family,
stated directly for the actual quotient cokernels. -/
theorem finite_coker_iff_of_preconnected_family
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (A : X → E →L[ℂ] F) (hA : Continuous A)
    (hupper : ∀ x, IsUpperSemiFredholm (A x)) (x y : X) :
    (A x).range.CoFG ↔ (A y).range.CoFG := by
  have h := extendedIndex_eq_bot_iff_of_preconnected_family A hA hupper x y
  simp only [extendedFredholmIndex_eq_bot_iff] at h
  exact not_iff_not.mp h

/-- A continuous path of upper semi-Fredholm operators transports the
extended index's minus-infinity branch between its endpoints. -/
theorem extendedIndex_eq_bot_iff_of_upperSemiFredholm_path
    {T U : E →L[ℂ] F} (p : Path T U)
    (hp : ∀ t, IsUpperSemiFredholm (p t)) :
    extendedFredholmIndex T = ⊥ ↔ extendedFredholmIndex U = ⊥ := by
  have h := extendedIndex_eq_bot_iff_of_preconnected_family
    p p.continuous hp 0 1
  simpa only [p.source, p.target] using h

/-- The infinite-dimensional genuine quotient cokernel survives a path
which remains upper semi-Fredholm. -/
theorem infinite_coker_of_upperSemiFredholm_path
    {T U : E →L[ℂ] F} (p : Path T U)
    (hp : ∀ t, IsUpperSemiFredholm (p t))
    (hT : ¬ T.range.CoFG) : ¬ U.range.CoFG := by
  apply (extendedFredholmIndex_eq_bot_iff U).mp
  exact (extendedIndex_eq_bot_iff_of_upperSemiFredholm_path p hp).mp
    ((extendedFredholmIndex_eq_bot_iff T).mpr hT)

/-- Orthogonal-cokernel form of infinite-cokernel path transport, for
direct use with Hilbert-space endpoint subspaces. -/
theorem infinite_orthogonal_coker_of_upperSemiFredholm_path
    {T U : E →L[ℂ] F} (p : Path T U)
    (hp : ∀ t, IsUpperSemiFredholm (p t))
    (hT : ¬ FiniteDimensional ℂ T.rangeᗮ) :
    ¬ FiniteDimensional ℂ U.rangeᗮ := by
  have hsource : IsUpperSemiFredholm T := by simpa only [p.source] using hp 0
  have htarget : IsUpperSemiFredholm U := by simpa only [p.target] using hp 1
  have hcT : ¬ T.range.CoFG := fun h =>
    hT (hsource.finite_coker_iff_finite_orthogonal.mp h)
  exact fun h => infinite_coker_of_upperSemiFredholm_path p hp hcT
    (htarget.finite_coker_iff_finite_orthogonal.mpr h)

end

end MeyerGeneralProblem
