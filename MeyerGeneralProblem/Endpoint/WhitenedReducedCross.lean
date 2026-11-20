module

public import MeyerGeneralProblem.Endpoint.WhitenedRange
public import MeyerGeneralProblem.Endpoint.ReducedCross

@[expose] public section

/-!
# Exact reduced cross in Gram-whitened coefficient coordinates

For two synthesis maps with strictly positive coefficient Grams, global
whitening gives unitary coordinates on their genuine closed atomic supports.
This file transports the exact physical intersection complement through the
source coordinates and restricts the genuine whitened cross operator to that
domain.  No Riesz lower bound is manufactured here: strict positivity is an
explicit analytic input.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped lp

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exact reduced coefficient domain: the inverse image, in the whitened
source coordinates, of the orthogonal complement of the physical
intersection. -/
def coefficientReducedDomain
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (_hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T)) :
    Submodule ℂ (CoefficientSpace iota) :=
  ((intersectionIn (coefficientAtomicSupport T).toSubmodule
      (coefficientAtomicSupport S).toSubmodule).orthogonal).map
    (whitenedSynthesisEquivAtomicSupport T hT).symm.toLinearMap

/-- The source-support whitening equivalence restricted to the exact reduced
domains on the coefficient and physical sides. -/
def coefficientReducedDomainEquiv
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T)) :
    coefficientReducedDomain S T hS hT ≃ₗᵢ[ℂ]
      (intersectionIn (coefficientAtomicSupport T).toSubmodule
        (coefficientAtomicSupport S).toSubmodule).orthogonal :=
  (LinearIsometryEquiv.submoduleMap
    ((intersectionIn (coefficientAtomicSupport T).toSubmodule
      (coefficientAtomicSupport S).toSubmodule).orthogonal)
    (whitenedSynthesisEquivAtomicSupport T hT).symm).symm

@[simp]
theorem coe_coefficientReducedDomainEquiv_apply
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T))
    (c : coefficientReducedDomain S T hS hT) :
    (((coefficientReducedDomainEquiv S T hS hT c :
        (intersectionIn (coefficientAtomicSupport T).toSubmodule
          (coefficientAtomicSupport S).toSubmodule).orthogonal) :
      (coefficientAtomicSupport T).toSubmodule) : H) =
        whitenedSynthesis T (c : CoefficientSpace iota) :=
  rfl

/-- The genuine globally whitened coefficient cross, restricted to the exact
reduced coefficient domain. -/
def whitenedReducedCross
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T)) :
    coefficientReducedDomain S T hS hT →L[ℂ] CoefficientSpace iota :=
  (whitenedCoefficientCross S T).comp
    (coefficientReducedDomain S T hS hT).subtypeL

@[simp]
theorem whitenedReducedCross_apply
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T))
    (c : coefficientReducedDomain S T hS hT) :
    whitenedReducedCross S T hS hT c =
      whitenedCoefficientCross S T (c : CoefficientSpace iota) :=
  rfl

/-- The global whitened cross is exactly physical orthogonal projection when
read through the whitened support equivalences. -/
theorem whitenedCoefficientCross_eq_projection
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T))
    (c : CoefficientSpace iota) :
    whitenedSynthesisEquivAtomicSupport S hS
        (whitenedCoefficientCross S T c) =
      (coefficientAtomicSupport S).orthogonalProjectionOnto
        ((whitenedSynthesisEquivAtomicSupport T hT c :
          (coefficientAtomicSupport T).toSubmodule) : H) := by
  apply ext_inner_right ℂ
  intro z
  obtain ⟨d, rfl⟩ :=
    (whitenedSynthesisEquivAtomicSupport S hS).surjective z
  rw [LinearIsometryEquiv.inner_map_map]
  rw [(coefficientAtomicSupport S).inner_orthogonalProjectionOnto_eq_of_mem_right]
  change inner ℂ (whitenedCoefficientCross S T c) d =
    inner ℂ (whitenedSynthesis T c) (whitenedSynthesis S d)
  rw [← whitenedSynthesis_cross S T]
  exact (whitenedSynthesis S).adjoint_inner_left d (whitenedSynthesis T c)

/-- Intertwining of the actual reduced physical cross with its exact
Gram-whitened coefficient restriction. -/
theorem whitenedReducedCross_intertwines
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T))
    (c : coefficientReducedDomain S T hS hT) :
    whitenedSynthesisEquivAtomicSupport S hS
        (whitenedReducedCross S T hS hT c) =
      reducedCross (coefficientAtomicSupport T).toSubmodule
        (coefficientAtomicSupport S).toSubmodule
        (coefficientReducedDomainEquiv S T hS hT c) := by
  rw [whitenedReducedCross_apply, reducedCross_apply]
  rw [whitenedCoefficientCross_eq_projection S T hS hT]
  congr 2

/-- Exact preservation of the operator norm under the physical/coefficient
unitary transport. -/
theorem whitenedReducedCross_norm_eq_reducedCross_norm
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T)) :
    ‖whitenedReducedCross S T hS hT‖ =
      ‖reducedCross (coefficientAtomicSupport T).toSubmodule
        (coefficientAtomicSupport S).toSubmodule‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _
      (ContinuousLinearMap.opNorm_nonneg _)
    intro c
    calc
      ‖whitenedReducedCross S T hS hT c‖ =
          ‖whitenedSynthesisEquivAtomicSupport S hS
            (whitenedReducedCross S T hS hT c)‖ :=
        (whitenedSynthesisEquivAtomicSupport S hS).norm_map _ |>.symm
      _ = ‖reducedCross (coefficientAtomicSupport T).toSubmodule
          (coefficientAtomicSupport S).toSubmodule
          (coefficientReducedDomainEquiv S T hS hT c)‖ := by
        rw [whitenedReducedCross_intertwines]
      _ ≤ ‖reducedCross (coefficientAtomicSupport T).toSubmodule
            (coefficientAtomicSupport S).toSubmodule‖ *
          ‖coefficientReducedDomainEquiv S T hS hT c‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖reducedCross (coefficientAtomicSupport T).toSubmodule
            (coefficientAtomicSupport S).toSubmodule‖ * ‖c‖ := by
        rw [(coefficientReducedDomainEquiv S T hS hT).norm_map]
  · apply ContinuousLinearMap.opNorm_le_bound _
      (ContinuousLinearMap.opNorm_nonneg _)
    intro x
    let c := (coefficientReducedDomainEquiv S T hS hT).symm x
    calc
      ‖reducedCross (coefficientAtomicSupport T).toSubmodule
          (coefficientAtomicSupport S).toSubmodule x‖ =
          ‖reducedCross (coefficientAtomicSupport T).toSubmodule
            (coefficientAtomicSupport S).toSubmodule
            (coefficientReducedDomainEquiv S T hS hT c)‖ := by
        rw [(coefficientReducedDomainEquiv S T hS hT).apply_symm_apply]
      _ = ‖whitenedSynthesisEquivAtomicSupport S hS
          (whitenedReducedCross S T hS hT c)‖ := by
        rw [whitenedReducedCross_intertwines]
      _ = ‖whitenedReducedCross S T hS hT c‖ :=
        (whitenedSynthesisEquivAtomicSupport S hS).norm_map _
      _ ≤ ‖whitenedReducedCross S T hS hT‖ * ‖c‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖whitenedReducedCross S T hS hT‖ * ‖x‖ := by
        rw [(coefficientReducedDomainEquiv S T hS hT).symm.norm_map]

/-- The abstract endpoint radius of the genuine closed atomic supports is the
norm square of the exact restricted whitened coefficient cross. -/
theorem rho_eq_whitenedReducedCross_norm_sq
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T)) :
    TwoProjectionEndpoint.reducedEndpointRadius
        (coefficientAtomicSupport T).toSubmodule
        (coefficientAtomicSupport S).toSubmodule =
      ‖whitenedReducedCross S T hS hT‖ ^ 2 := by
  rw [TwoProjectionEndpoint.reducedEndpointRadius_eq_reducedCross_norm_sq,
    ← whitenedReducedCross_norm_eq_reducedCross_norm S T hS hT]

end

end MeyerGeneralProblem
