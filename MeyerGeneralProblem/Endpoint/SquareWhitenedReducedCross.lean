module

public import MeyerGeneralProblem.Endpoint.WhitenedReducedCross
public import MeyerGeneralProblem.Hilbert.OrthogonalProjectionExtension

@[expose] public section

/-!
# Square realization of the reduced whitened cross

The exact reduced coefficient cross is naturally rectangular: its source is
the transported complement of the physical intersection, while its target is
the full coefficient space.  Orthogonal projection onto that source gives a
square operator on the fixed coefficient Hilbert space.  The extension has
exactly the same norm, remains pointwise strictly contractive on unit vectors,
and therefore preserves the endpoint radius without an extra premise.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped lp

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The transported reduced coefficient domain is orthogonally complemented.
The explicit completeness instance is needed because its ambient subtype is
presented through the underlying submodule of a closed submodule. -/
theorem coefficientReducedDomain_hasOrthogonalProjection
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T)) :
    (coefficientReducedDomain S T hS hT).HasOrthogonalProjection := by
  unfold coefficientReducedDomain
  let K := (intersectionIn (coefficientAtomicSupport T).toSubmodule
      (coefficientAtomicSupport S).toSubmodule).orthogonal
  let e := (whitenedSynthesisEquivAtomicSupport T hT).symm
  letI : CompleteSpace (coefficientAtomicSupport T).toSubmodule :=
    (coefficientAtomicSupport T).isClosed'.completeSpace_coe
  letI : K.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace K
  exact Submodule.HasOrthogonalProjection.map_linearIsometryEquiv K e

/-- Square fixed-coefficient-space realization of the exact reduced whitened
cross.  It agrees with the rectangular cross on the reduced domain and is
zero on its orthogonal complement. -/
def squareWhitenedReducedCross
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T)) :
    CoefficientSpace iota →L[ℂ] CoefficientSpace iota := by
  letI := coefficientReducedDomain_hasOrthogonalProjection S T hS hT
  exact orthogonalProjectionExtension
    (coefficientReducedDomain S T hS hT)
    (whitenedReducedCross S T hS hT)

@[simp]
theorem squareWhitenedReducedCross_apply_mem
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T))
    (c : coefficientReducedDomain S T hS hT) :
    squareWhitenedReducedCross S T hS hT
        (c : CoefficientSpace iota) =
      whitenedReducedCross S T hS hT c := by
  letI := coefficientReducedDomain_hasOrthogonalProjection S T hS hT
  exact orthogonalProjectionExtension_apply_mem
    (coefficientReducedDomain S T hS hT)
    (whitenedReducedCross S T hS hT) c

/-- The rectangular reduced cross is pointwise strictly contractive away
from zero, by exact unitary transport of the physical Friedrichs cross. -/
theorem whitenedReducedCross_apply_norm_lt
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T))
    (c : coefficientReducedDomain S T hS hT) (hc : c ≠ 0) :
    ‖whitenedReducedCross S T hS hT c‖ < ‖c‖ := by
  let e := coefficientReducedDomainEquiv S T hS hT
  have hec : e c ≠ 0 := by
    intro hzero
    apply hc
    exact e.injective (by simpa using hzero)
  calc
    ‖whitenedReducedCross S T hS hT c‖ =
        ‖whitenedSynthesisEquivAtomicSupport S hS
          (whitenedReducedCross S T hS hT c)‖ :=
      (whitenedSynthesisEquivAtomicSupport S hS).norm_map _ |>.symm
    _ = ‖reducedCross (coefficientAtomicSupport T).toSubmodule
          (coefficientAtomicSupport S).toSubmodule (e c)‖ := by
      rw [whitenedReducedCross_intertwines]
    _ < ‖e c‖ := reducedCross_apply_norm_lt
      (coefficientAtomicSupport T).toSubmodule
      (coefficientAtomicSupport S).toSubmodule (e c) hec
    _ = ‖c‖ := e.norm_map c

/-- The square realization preserves the exact reduced-cross norm. -/
theorem squareWhitenedReducedCross_norm_eq
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T)) :
    ‖squareWhitenedReducedCross S T hS hT‖ =
      ‖whitenedReducedCross S T hS hT‖ := by
  letI := coefficientReducedDomain_hasOrthogonalProjection S T hS hT
  exact orthogonalProjectionExtension_norm_eq
    (coefficientReducedDomain S T hS hT)
    (whitenedReducedCross S T hS hT)

/-- The square realization is a contraction. -/
theorem squareWhitenedReducedCross_norm_le_one
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T)) :
    ‖squareWhitenedReducedCross S T hS hT‖ ≤ 1 := by
  rw [squareWhitenedReducedCross_norm_eq,
    whitenedReducedCross_norm_eq_reducedCross_norm]
  exact reducedCross_norm_le_one
    (coefficientAtomicSupport T).toSubmodule
    (coefficientAtomicSupport S).toSubmodule

/-- The square realization supplies the pointwise strict-contraction premise
of the fixed-space endpoint squeeze automatically. -/
theorem squareWhitenedReducedCross_apply_norm_lt_one
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T))
    (x : CoefficientSpace iota) (hx : ‖x‖ = 1) :
    ‖squareWhitenedReducedCross S T hS hT x‖ < 1 := by
  let K := coefficientReducedDomain S T hS hT
  letI : K.HasOrthogonalProjection :=
    coefficientReducedDomain_hasOrthogonalProjection S T hS hT
  let c : K := K.orthogonalProjectionOnto x
  by_cases hc : c = 0
  · change ‖whitenedReducedCross S T hS hT c‖ < 1
    rw [hc]
    norm_num
  · calc
      ‖squareWhitenedReducedCross S T hS hT x‖ =
          ‖whitenedReducedCross S T hS hT c‖ := rfl
      _ < ‖c‖ := whitenedReducedCross_apply_norm_lt S T hS hT c hc
      _ ≤ ‖x‖ := K.norm_orthogonalProjectionOnto_apply_le x
      _ = 1 := hx

/-- The physical endpoint radius is unchanged by replacing the rectangular
reduced cross with its square fixed-space realization. -/
theorem rho_eq_squareWhitenedReducedCross_norm_sq
    {iota : Type*} [DecidableEq iota]
    (S T : CoefficientSpace iota →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T)) :
    TwoProjectionEndpoint.reducedEndpointRadius
        (coefficientAtomicSupport T).toSubmodule
        (coefficientAtomicSupport S).toSubmodule =
      ‖squareWhitenedReducedCross S T hS hT‖ ^ 2 := by
  rw [rho_eq_whitenedReducedCross_norm_sq,
    squareWhitenedReducedCross_norm_eq]

end

end MeyerGeneralProblem
