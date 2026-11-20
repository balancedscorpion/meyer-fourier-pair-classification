module

public import MeyerGeneralProblem.Distribution.EnvelopeHoleRows

@[expose] public section

/-!
# Directed finite-hole envelopes of a common carrier

The envelope index includes the empty lattice union. Taking the union of
the line sets preserves cofinite admission and dominates both embedded
kernels. A bounded-count ambient space attains the maximum of these
literal nullities.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped FourierTransform

/-- Finite unions of full positive-step lattices with finitely many holes
in the given common carrier. -/
def FiniteHoleEnvelope (S : LocallyFiniteCarrier) :=
  {E : Finset (ℝ × ℝ) // (∀ p ∈ E, 0 < p.2) ∧
    ((affineLatticeUnionCarrier E).carrier \ S.carrier).Finite}

namespace FiniteHoleEnvelope

variable {S : LocallyFiniteCarrier}

/-- The locally finite carrier of the envelope before deleting holes. -/
def carrier (E : FiniteHoleEnvelope S) : LocallyFiniteCarrier :=
  affineLatticeUnionCarrier E.val

/-- The empty lattice union viewed as a finite-hole envelope. -/
def empty (S : LocallyFiniteCarrier) : FiniteHoleEnvelope S :=
  ⟨∅, by simp, by simp [affineLatticeUnionCarrier]⟩

instance : Nonempty (FiniteHoleEnvelope S) := ⟨empty S⟩

theorem finite_holes (E : FiniteHoleEnvelope S) :
    Finite (CommonCarrierHole E.carrier S) :=
  finite_commonCarrierHole _ _ E.property.2

/-- The envelope formed by taking the union of the two lists of full lattices. -/
def union (E F : FiniteHoleEnvelope S) : FiniteHoleEnvelope S := by
  classical
  refine ⟨E.val ∪ F.val, ?_, ?_⟩
  · intro p hp
    exact (Finset.mem_union.mp hp).elim (E.property.1 p) (F.property.1 p)
  · apply (E.property.2.union F.property.2).subset
    rintro x ⟨hx, hs⟩
    obtain ⟨p, hp, hxp⟩ := (mem_affineLatticeUnionCarrier _ x).mp hx
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Or.inl ⟨(mem_affineLatticeUnionCarrier _ x).mpr ⟨p, hp, hxp⟩, hs⟩
    · exact Or.inr ⟨(mem_affineLatticeUnionCarrier _ x).mpr ⟨p, hp, hxp⟩, hs⟩

theorem carrier_subset_union_left (E F : FiniteHoleEnvelope S) :
    E.carrier.carrier ⊆ (E.union F).carrier.carrier := by
  classical
  intro x hx
  obtain ⟨p, hp, hxp⟩ := (mem_affineLatticeUnionCarrier E.val x).mp hx
  exact (mem_affineLatticeUnionCarrier (E.union F).val x).mpr
    ⟨p, Finset.mem_union_left _ hp, hxp⟩

theorem carrier_subset_union_right (E F : FiniteHoleEnvelope S) :
    F.carrier.carrier ⊆ (E.union F).carrier.carrier := by
  classical
  intro x hx
  obtain ⟨p, hp, hxp⟩ := (mem_affineLatticeUnionCarrier F.val x).mp hx
  exact (mem_affineLatticeUnionCarrier (E.union F).val x).mpr
    ⟨p, Finset.mem_union_right _ hp, hxp⟩

/-- The original source subspace on the intersection with the envelope. -/
def embeddedSpace (E : FiniteHoleEnvelope S) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  DistributionalMeyerPairSpace (commonCarrierIntersection E.carrier S)
    (commonCarrierIntersection E.carrier S)

theorem embeddedSpace_eq_map_ker (E : FiniteHoleEnvelope S) :
    E.embeddedSpace = (LinearMap.ker (commonCarrierHoleRows E.carrier S)).map
      (DistributionalMeyerPairSpace E.carrier E.carrier).subtype :=
  (map_ker_commonCarrierHoleRows E.carrier S).symm

theorem embeddedSpace_le (E : FiniteHoleEnvelope S) :
    E.embeddedSpace ≤ DistributionalMeyerPairSpace S S := by
  intro T hT
  have h := (mem_distributionalMeyerPairSpace_iff _ _ T).mp hT
  exact (mem_distributionalMeyerPairSpace_iff _ _ T).mpr
    ⟨h.1.mono inter_subset_right, h.2.mono inter_subset_right⟩

theorem embeddedSpace_mono {E F : FiniteHoleEnvelope S}
    (h : E.carrier.carrier ⊆ F.carrier.carrier) : E.embeddedSpace ≤ F.embeddedSpace := by
  intro T hT
  have hs := (mem_distributionalMeyerPairSpace_iff _ _ T).mp hT
  have hi : (commonCarrierIntersection E.carrier S).carrier ⊆
      (commonCarrierIntersection F.carrier S).carrier := fun _ hx => ⟨h hx.1, hx.2⟩
  exact (mem_distributionalMeyerPairSpace_iff _ _ T).mpr ⟨hs.1.mono hi, hs.2.mono hi⟩

theorem directed_embeddedSpace (S : LocallyFiniteCarrier) :
    Directed (· ≤ ·) (embeddedSpace (S := S)) :=
  fun E F => ⟨E.union F, embeddedSpace_mono (E.carrier_subset_union_left F),
    embeddedSpace_mono (E.carrier_subset_union_right F)⟩

/-- The dimension of the entire envelope space minus the rank of all its
original physical and Fourier hole rows. -/
def nullity (E : FiniteHoleEnvelope S) : ℕ :=
  Module.finrank ℂ (DistributionalMeyerPairSpace E.carrier E.carrier) -
    Module.finrank ℂ (LinearMap.range (commonCarrierHoleRows E.carrier S))

theorem finrank_embeddedSpace (E : FiniteHoleEnvelope S) :
    Module.finrank ℂ E.embeddedSpace = E.nullity := by
  let _ := finiteDimensional_distributionalMeyerPairSpace_of_unitCellBound
    E.carrier E.carrier _ (unitCellBound_affineLatticeUnionCarrier E.val E.property.1)
  exact commonCarrierHoleSpace_finrank E.carrier S

end FiniteHoleEnvelope

/-- The directed union of the embedded kernels over all finite-hole envelopes. -/
def finiteHoleEnvelopeSpace (S : LocallyFiniteCarrier) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  ⨆ E : FiniteHoleEnvelope S, E.embeddedSpace

theorem mem_finiteHoleEnvelopeSpace (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) :
    T ∈ finiteHoleEnvelopeSpace S ↔ ∃ E : FiniteHoleEnvelope S, T ∈ E.embeddedSpace :=
  Submodule.mem_iSup_of_directed _ (FiniteHoleEnvelope.directed_embeddedSpace S)

theorem finiteHoleEnvelopeSpace_le (S : LocallyFiniteCarrier) :
    finiteHoleEnvelopeSpace S ≤ DistributionalMeyerPairSpace S S :=
  iSup_le fun E => E.embeddedSpace_le

/-- The full directed union of the original hole kernels is captured by
one envelope and its complex dimension is the attained maximum nullity. -/
theorem exists_maximal_finiteHoleEnvelope (S : LocallyFiniteCarrier)
    (K : ℕ) (hK : UnitCellBound S K) :
    ∃ E : FiniteHoleEnvelope S, finiteHoleEnvelopeSpace S = E.embeddedSpace ∧
      Module.finrank ℂ (finiteHoleEnvelopeSpace S) = E.nullity ∧
      ∀ F : FiniteHoleEnvelope S, F.nullity ≤ E.nullity := by
  let _ := finiteDimensional_distributionalMeyerPairSpace_of_unitCellBound S S K hK
  let R := Set.range fun E : FiniteHoleEnvelope S => Module.finrank ℂ E.embeddedSpace
  have hb : BddAbove R := ⟨Module.finrank ℂ (DistributionalMeyerPairSpace S S), by
    rintro n ⟨E, rfl⟩
    exact Submodule.finrank_mono E.embeddedSpace_le⟩
  have hne : R.Nonempty := ⟨_, FiniteHoleEnvelope.empty S, rfl⟩
  obtain ⟨d, hd, hmax⟩ := hb.exists_isGreatest_of_nonempty hne
  obtain ⟨E, rfl⟩ := hd
  have hle (F : FiniteHoleEnvelope S) :
      Module.finrank ℂ F.embeddedSpace ≤ Module.finrank ℂ E.embeddedSpace :=
    hmax ⟨F, rfl⟩
  have hassembly : finiteHoleEnvelopeSpace S = E.embeddedSpace := by
    apply (le_antisymm (iSup_le ?_) (le_iSup _ E))
    intro F
    let G := E.union F
    have hEG := FiniteHoleEnvelope.embeddedSpace_mono (E.carrier_subset_union_left F)
    have hFG := FiniteHoleEnvelope.embeddedSpace_mono (E.carrier_subset_union_right F)
    let _ := Submodule.finiteDimensional_of_le G.embeddedSpace_le
    have heq := Submodule.eq_of_le_of_finrank_le hEG (hle G)
    exact heq ▸ hFG
  refine ⟨E, hassembly, hassembly ▸ E.finrank_embeddedSpace, fun F => ?_⟩
  simpa only [← E.finrank_embeddedSpace, ← F.finrank_embeddedSpace] using hle F

/-- The directed union is nonzero exactly when a geometric envelope has
a strictly positive literal joint-hole nullity. -/
theorem finiteHoleEnvelopeSpace_ne_bot_iff (S : LocallyFiniteCarrier)
    (K : ℕ) (hK : UnitCellBound S K) :
    finiteHoleEnvelopeSpace S ≠ ⊥ ↔ ∃ E : FiniteHoleEnvelope S, 0 < E.nullity := by
  let _ := finiteDimensional_distributionalMeyerPairSpace_of_unitCellBound S S K hK
  let _ := Submodule.finiteDimensional_of_le (finiteHoleEnvelopeSpace_le S)
  obtain ⟨E, _, he, hmax⟩ := exists_maximal_finiteHoleEnvelope S K hK
  have hfin : 0 < Module.finrank ℂ (finiteHoleEnvelopeSpace S) ↔
      finiteHoleEnvelopeSpace S ≠ ⊥ := by
    rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
  rw [← hfin, he]
  exact ⟨fun h => ⟨E, h⟩, fun ⟨F, hF⟩ => hF.trans_le (hmax F)⟩

end
end MeyerGeneralProblem
