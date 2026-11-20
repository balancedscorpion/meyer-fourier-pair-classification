module

public import MeyerGeneralProblem.Distribution.PairedMeyerSpace
public import MeyerGeneralProblem.Distribution.RestrictedAtomicRows
public import MeyerGeneralProblem.Distribution.AffineLineCenteredCount

@[expose] public section

/-!
# Original coefficient equations on a finite-hole envelope

Each missing site contributes its physical and Fourier evaluation on the
complete envelope space. The embedded kernel is the exact original space on
the intersection, and finite dimension gives the attained directed maximum.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators FourierTransform

/-- Restriction to the intersection of the envelope and the allowed carrier. -/
def commonCarrierIntersection (L S : LocallyFiniteCarrier) : LocallyFiniteCarrier :=
  L.restrict (L.carrier ∩ S.carrier) inter_subset_left

/-- Original holes indexed inside the locally finite envelope. -/
def CommonCarrierHole (L S : LocallyFiniteCarrier) : Type :=
  { x : L.subtype // (x : ℝ) ∉ S.carrier }

theorem finite_commonCarrierHole (L S : LocallyFiniteCarrier)
    (h : (L.carrier \ S.carrier).Finite) : Finite (CommonCarrierHole L S) := by
  let _ : Finite ↥(L.carrier \ S.carrier) := h.to_subtype
  exact Finite.of_injective
    (fun x : CommonCarrierHole L S => (⟨x.val, x.val.property, x.property⟩ :
      ↥(L.carrier \ S.carrier)))
    (fun _ _ he => Subtype.ext (Subtype.ext (congrArg (fun q : ↥(L.carrier \ S.carrier) => (q : ℝ)) he)))

/-- Both literal coefficient rows at each original missing site. -/
def commonCarrierHoleRows (L S : LocallyFiniteCarrier) :
    DistributionalMeyerPairSpace L L →ₗ[ℂ] (CommonCarrierHole L S → ℂ × ℂ) :=
  LinearMap.pi fun x =>
    ((atomicCoefficientLinearMap L x.val).comp (DistributionalMeyerPairSpace L L).subtype).prod
      ((atomicCoefficientLinearMap L x.val).comp
        (temperedFourierLinearMap.comp (DistributionalMeyerPairSpace L L).subtype))

theorem mem_ker_commonCarrierHoleRows (L S : LocallyFiniteCarrier)
    (T : DistributionalMeyerPairSpace L L) :
    T ∈ LinearMap.ker (commonCarrierHoleRows L S) ↔
      (T : TemperedDistribution ℝ ℂ) ∈ DistributionalMeyerPairSpace
        (commonCarrierIntersection L S) (commonCarrierIntersection L S) := by
  have hT := (mem_distributionalMeyerPairSpace_iff L L T).mp T.property
  rw [LinearMap.mem_ker, mem_distributionalMeyerPairSpace_iff, commonCarrierIntersection,
    atomicOnCarrier_restrict_iff, atomicOnCarrier_restrict_iff]
  constructor
  · intro hz
    have hrow (x : L.subtype) (hx : (x : ℝ) ∉ L.carrier ∩ S.carrier) :
        (T : TemperedDistribution ℝ ℂ) (L.isolationSchwartz x) = 0 ∧
          (𝓕 (T : TemperedDistribution ℝ ℂ)) (L.isolationSchwartz x) = 0 := by
      have h := congrFun hz (⟨x, fun hs => hx ⟨x.property, hs⟩⟩ : CommonCarrierHole L S)
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    exact ⟨⟨hT.1, fun x hx => (hrow x hx).1⟩, ⟨hT.2, fun x hx => (hrow x hx).2⟩⟩
  · rintro ⟨⟨_, hp⟩, _, hf⟩
    funext x
    have hx : (x.val : ℝ) ∉ L.carrier ∩ S.carrier := fun h => x.property h.2
    exact Prod.ext (hp x.val hx) (hf x.val hx)

/-- Evaluating the same two original rows on any complete basis gives
the identical row-map range and therefore the identical rank. -/
theorem range_commonCarrierHoleRows_comp_basis (L S : LocallyFiniteCarrier)
    {ι : Type*} (b : Module.Basis ι ℂ (DistributionalMeyerPairSpace L L)) :
    LinearMap.range ((commonCarrierHoleRows L S).comp b.repr.symm.toLinearMap) =
      LinearMap.range (commonCarrierHoleRows L S) :=
  b.repr.symm.range_comp _

/-- The hole kernel as a subspace of the original tempered distributions. -/
theorem map_ker_commonCarrierHoleRows (L S : LocallyFiniteCarrier) :
    (LinearMap.ker (commonCarrierHoleRows L S)).map
      (DistributionalMeyerPairSpace L L).subtype =
        DistributionalMeyerPairSpace (commonCarrierIntersection L S)
          (commonCarrierIntersection L S) := by
  ext T
  constructor
  · rintro ⟨U, hU, rfl⟩
    exact (mem_ker_commonCarrierHoleRows L S U).mp hU
  · intro hT
    have hs := (mem_distributionalMeyerPairSpace_iff _ _ T).mp hT
    have hL : T ∈ DistributionalMeyerPairSpace L L :=
      (mem_distributionalMeyerPairSpace_iff L L T).mpr
        ⟨hs.1.mono inter_subset_left, hs.2.mono inter_subset_left⟩
    exact ⟨⟨T, hL⟩, (mem_ker_commonCarrierHoleRows L S ⟨T, hL⟩).mpr hT, rfl⟩

theorem commonCarrierHoleSpace_finrank (L S : LocallyFiniteCarrier)
    [FiniteDimensional ℂ (DistributionalMeyerPairSpace L L)] :
    Module.finrank ℂ (DistributionalMeyerPairSpace (commonCarrierIntersection L S)
        (commonCarrierIntersection L S)) =
      Module.finrank ℂ (DistributionalMeyerPairSpace L L) -
        Module.finrank ℂ (LinearMap.range (commonCarrierHoleRows L S)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (commonCarrierHoleRows L S)
  rw [← map_ker_commonCarrierHoleRows, Submodule.finrank_map_subtype_eq]
  omega

end
end MeyerGeneralProblem
