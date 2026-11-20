module

public import MeyerGeneralProblem.Distribution.LatticeCyclotomicRows
public import MeyerGeneralProblem.Distribution.LatticePartnerMatrices

@[expose] public section

/-!
# Original envelope coordinates from finite residue matrices

The finite partner matrices are assembled by the whole-space
partner equivalence. Each original hole uses the physical and
Fourier comb coefficients in these same coordinates.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators FourierTransform SchwartzMap

/-- One ordered partner with a literal finite residue kernel and its
original comb synthesis. -/
structure LatticePartnerResidueCoordinates (E F : Finset (ℝ × ℝ)) (w : ℝ) where
  /-- The index type of the distinct translation orbits. -/
  Orbit : Type
  /-- The finite enumeration of the orbit index type. -/
  orbitFintype : Fintype Orbit
  /-- The chosen representative of each translation orbit. -/
  origin : Orbit → ℝ
  /-- The modulation frequencies used on every orbit. -/
  modes : List ℝ
  /-- The common translation step for the orbits. -/
  orbitStep : ℝ
  orbitStep_pos : 0 < orbitStep
  modesDistinct : modes.Pairwise
    (fun s t => combModulationCharacter (-orbitStep) s ≠ combModulationCharacter (-orbitStep) t)
  /-- The positive modulus used to form one complete set of residue rows. -/
  modulus : ℕ
  modulus_pos : 0 < modulus
  /-- The coordinate equivalence from the residue kernel to the original partner space. -/
  equiv : LinearMap.ker (latticeOrbitResidueRows
    (affineLatticeUnionCarrier (latticeDirectionClass E (rationalLineDirection w)))
    orbitStep origin modes modulus) ≃ₗ[ℂ] latticePartnerPairSpace E F w
  equiv_apply : letI := orbitFintype
    ∀ c, (equiv c : TemperedDistribution ℝ ℂ) =
      latticeOrbitSynthesis orbitStep orbitStep_pos origin modes c

namespace LatticePartnerResidueCoordinates

variable {E F : Finset (ℝ × ℝ)} {w : ℝ}

/-- The finite row map of this ordered partner. -/
def residueRows (d : LatticePartnerResidueCoordinates E F w) :=
  latticeOrbitResidueRows
    (affineLatticeUnionCarrier (latticeDirectionClass E (rationalLineDirection w)))
    d.orbitStep d.origin d.modes d.modulus

/-- A physical coefficient, with ordinary addition at all coincident
sites of the original combs. -/
def physicalCoefficient (d : LatticePartnerResidueCoordinates E F w)
    (c : LinearMap.ker d.residueRows) (x : ℝ) : ℂ := by
  letI := d.orbitFintype
  exact ∑ i, ∑ j, (⟨d.modes.get j, d.origin i, c.val i j⟩ : AffineCombTerm).coefficientFunction
    d.orbitStep x

/-- A Fourier coefficient with the original reciprocal coset and
Poisson phase of each summand. -/
def fourierCoefficient (d : LatticePartnerResidueCoordinates E F w)
    (c : LinearMap.ker d.residueRows) (x : ℝ) : ℂ := by
  letI := d.orbitFintype
  exact ∑ i, ∑ j, ((⟨d.modes.get j, d.origin i, c.val i j⟩ : AffineCombTerm).fourierTerm
    d.orbitStep).coefficientFunction d.orbitStep⁻¹ x

private theorem extendedAtomicCoefficient_eq_of_two_carriers
    (A B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B T) (x : ℝ) :
    extendedAtomicCoefficient A T x = extendedAtomicCoefficient B T x :=
  (extendedAtomicCoefficient_on_larger_carrier A (A.union B) Set.subset_union_left T hA x).symm.trans
    (extendedAtomicCoefficient_on_larger_carrier B (A.union B) Set.subset_union_right T hB x)

theorem physicalCoefficient_eq_original (d : LatticePartnerResidueCoordinates E F w)
    (c : LinearMap.ker d.residueRows) (A : LocallyFiniteCarrier)
    (hA : AtomicOnCarrier A (d.equiv c)) (x : ℝ) :
    extendedAtomicCoefficient A (d.equiv c) x = d.physicalCoefficient c x := by
  classical
  let _ := d.orbitFintype
  let U := latticeOrbitUnion d.orbitStep d.origin
  let q (i : d.Orbit) (j : Fin d.modes.length) : AffineCombTerm :=
    ⟨d.modes.get j, d.origin i, c.val i j⟩
  have hT := d.equiv_apply c
  rw [hT] at hA ⊢
  rw [extendedAtomicCoefficient_eq_of_two_carriers A U _ hA
    (latticeOrbitSynthesis_atomicOnCarrier d.orbitStep d.orbitStep_pos d.origin d.modes c) x]
  change extendedAtomicCoefficient U
    (∑ i, ∑ j, (q i j).distribution d.orbitStep d.orbitStep_pos) x =
      ∑ i, ∑ j, (q i j).coefficientFunction d.orbitStep x
  simp_rw [extendedAtomicCoefficient_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact extendedAtomicCoefficient_affineCombTerm _ _ _ U
    (fun y hy => (mem_latticeOrbitUnion _ _ _).mpr ⟨i, hy⟩) x

theorem fourierCoefficient_eq_original (d : LatticePartnerResidueCoordinates E F w)
    (c : LinearMap.ker d.residueRows) (B : LocallyFiniteCarrier)
    (hB : AtomicOnCarrier B (𝓕 (d.equiv c : TemperedDistribution ℝ ℂ))) (x : ℝ) :
    extendedAtomicCoefficient B (𝓕 (d.equiv c : TemperedDistribution ℝ ℂ)) x =
      d.fourierCoefficient c x := by
  classical
  let _ := d.orbitFintype
  let U := latticeOrbitUnion d.orbitStep⁻¹ d.modes.get
  have hT := d.equiv_apply c
  rw [hT] at hB ⊢
  rw [extendedAtomicCoefficient_eq_of_two_carriers B U _ hB
    (fourier_latticeOrbitSynthesis_atomicOnCarrier d.orbitStep d.orbitStep_pos d.origin d.modes c) x]
  rw [extendedAtomicCoefficient_fourier_latticeOrbitSynthesis]
  rfl

/-- Choose the canonical residue kernel for a present reciprocal direction.
An absent reciprocal direction has an empty coefficient array. -/
theorem nonempty_of_present_physical
    (hE : ∀ v ∈ E, 0 < v.2) (hF : ∀ v ∈ F, 0 < v.2)
    (hP : (latticeDirectionClass E (rationalLineDirection w)).Nonempty) :
    Nonempty (LatticePartnerResidueCoordinates E F w) := by
  classical
  by_cases hQ : (latticeDirectionClass F (rationalLineDirection w⁻¹)).Nonempty
  · obtain ⟨a, b, ha, hb, physicalModes, modes, p, q, hp, hq, hc, hrel, haGen, hbGen,
        haModes, hbModes, hPhysical, hSpectral, κ, f, y, hcard, hCenter, hCover, hDisj, e, he⟩ :=
      exists_latticePartnerPairSpace_residueEquiv E F hE hF w hP hQ
    exact ⟨⟨κ, f, y, modes, b⁻¹, inv_pos.mpr hb, hbModes, p, hp, e, he⟩⟩
  · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hQ
    have hBot := latticePartnerPairSpace_eq_bot_of_empty_spectral_class E F w hEmpty
    let origin : Empty → ℝ := Empty.elim
    let V := latticePartnerPairSpace E F w
    let K := LinearMap.ker (latticeOrbitResidueRows
      (affineLatticeUnionCarrier (latticeDirectionClass E (rationalLineDirection w))) 1 origin [] 1)
    have hSurj : Function.Surjective (0 : K →ₗ[ℂ] V) := by
      intro v
      have hz : (v : TemperedDistribution ℝ ℂ) = 0 := by
        have h := v.property
        change (v : TemperedDistribution ℝ ℂ) ∈ latticePartnerPairSpace E F w at h
        rwa [hBot, Submodule.mem_bot] at h
      refine ⟨0, ?_⟩
      change (0 : V) = v
      exact Subtype.ext hz.symm
    let e := LinearEquiv.ofBijective (0 : K →ₗ[ℂ] V)
      ⟨fun _ _ _ => Subsingleton.elim _ _, hSurj⟩
    refine ⟨⟨Empty, inferInstance, origin, [], 1, zero_lt_one, by simp, 1, zero_lt_one, e, ?_⟩⟩
    intro c
    change (0 : TemperedDistribution ℝ ℂ) = latticeOrbitSynthesis 1 zero_lt_one origin [] c
    rw [latticeOrbitSynthesis_apply]
    simp

end LatticePartnerResidueCoordinates

namespace LatticePartnerResidueCoordinates

variable {E F : Finset (ℝ × ℝ)} {w : ℝ}

/-- Each block dimension is its number of coordinates minus its own
finite residue row rank. -/
theorem finrank_ker_residueRows (d : LatticePartnerResidueCoordinates E F w) :
    letI := d.orbitFintype
    Module.finrank ℂ (LinearMap.ker d.residueRows) =
      Fintype.card d.Orbit * d.modes.length - Module.finrank ℂ (LinearMap.range d.residueRows) := by
  let _ := d.orbitFintype
  have hd : Module.finrank ℂ (d.Orbit → Fin d.modes.length → ℂ) =
      Fintype.card d.Orbit * d.modes.length := by
    simp [Module.finrank_pi_fintype]
  have h := LinearMap.finrank_range_add_finrank_ker d.residueRows
  exact Nat.eq_sub_of_add_eq (by rw [add_comm]; exact h.trans hd)


/-- The single-period phase used to group the partner's original modes. -/
def phase (d : LatticePartnerResidueCoordinates E F w) (j : Fin d.modes.length) : ℂ :=
  combModulationCharacter (d.modes.get j) d.orbitStep

/-- Root-of-unity column indices in each powered-phase class. -/
def cyclotomicIndices (d : LatticePartnerResidueCoordinates E F w) :
    ∀ η : latticePhaseClasses d.phase d.modulus, LatticePhaseClass d.phase d.modulus η → Fin d.modulus := by
  letI := d.orbitFintype
  exact Classical.choose (exists_latticeOrbitResidueRows_cyclotomic_finrank
    (affineLatticeUnionCarrier (latticeDirectionClass E (rationalLineDirection w)))
    d.orbitStep d.origin d.modes d.modulus d.modulus_pos d.modesDistinct)

/-- The sum of exact cyclotomic block nullities for this partner. -/
def cyclotomicNullity (d : LatticePartnerResidueCoordinates E F w) : ℕ := by
  classical
  letI := d.orbitFintype
  let A := affineLatticeUnionCarrier (latticeDirectionClass E (rationalLineDirection w))
  let ζ := Complex.exp (2 * Real.pi * Complex.I / d.modulus)
  let R (i : d.Orbit) := {r : Fin d.modulus // d.origin i + (r.val : ℝ) * d.orbitStep ∉ A.carrier}
  exact ∑ i : d.Orbit, ∑ η : latticePhaseClasses d.phase d.modulus,
    (Fintype.card (LatticePhaseClass d.phase d.modulus η) -
      (latticeCyclotomicMatrix ζ
        (fun (r : R i) j => (d.cyclotomicIndices η j).val * r.val.val)).rank)

theorem finrank_ker_residueRows_eq_cyclotomicNullity (d : LatticePartnerResidueCoordinates E F w) :
    Module.finrank ℂ (LinearMap.ker d.residueRows) = d.cyclotomicNullity := by
  classical
  let _ := d.orbitFintype
  exact (Classical.choose_spec (exists_latticeOrbitResidueRows_cyclotomic_finrank
    (affineLatticeUnionCarrier (latticeDirectionClass E (rationalLineDirection w)))
    d.orbitStep d.origin d.modes d.modulus d.modulus_pos d.modesDistinct)).2.2

end LatticePartnerResidueCoordinates

/-- Pull the original joint hole kernel back along an envelope
coordinate equivalence. Its values are the original distributions. -/
theorem FiniteHoleEnvelope.exists_holeKernelEquiv_of_coordinates
    {S : LocallyFiniteCarrier} (E : FiniteHoleEnvelope S)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : V ≃ₗ[ℂ] DistributionalMeyerPairSpace E.carrier E.carrier) :
    ∃ h : LinearMap.ker ((commonCarrierHoleRows E.carrier S).comp e.toLinearMap) ≃ₗ[ℂ]
        E.embeddedSpace,
      ∀ c, (h c : TemperedDistribution ℝ ℂ) = (e c : TemperedDistribution ℝ ℂ) := by
  let M := DistributionalMeyerPairSpace E.carrier E.carrier
  let R := commonCarrierHoleRows E.carrier S
  let K := LinearMap.ker (R.comp e.toLinearMap)
  have hMap : K.map e.toLinearMap = LinearMap.ker R := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      apply LinearMap.mem_ker.mpr
      change R (e (e.symm x)) = 0
      rw [e.apply_symm_apply, LinearMap.mem_ker.mp hx]
  let j := M.subtype.comp e.toLinearMap
  have hj : Function.Injective j := Submodule.subtype_injective M |>.comp e.injective
  have hJ : K.map j = E.embeddedSpace := by
    rw [show j = M.subtype.comp e.toLinearMap from rfl, Submodule.map_comp, hMap,
      E.embeddedSpace_eq_map_ker]
  let eq := (Submodule.equivMapOfInjective j hj K).trans (LinearEquiv.ofEq _ _ hJ)
  exact ⟨eq, fun _ => rfl⟩

/-- Assemble all finite residue matrices in the whole envelope, and
impose both literal hole equations on their common coordinate space. -/
theorem FiniteHoleEnvelope.exists_latticeResidueMatrixCoordinates
    {S : LocallyFiniteCarrier} (E : FiniteHoleEnvelope S) :
    let dirs := E.val.image fun v => rationalLineDirection v.2
    ∃ (step : dirs → ℝ) (d : ∀ i : dirs, LatticePartnerResidueCoordinates E.val E.val (step i)),
      (∀ i, 0 < step i ∧ rationalLineDirection (step i) = i.val) ∧
      ∃ e : ((i : dirs) → LinearMap.ker (d i).residueRows) ≃ₗ[ℂ]
          DistributionalMeyerPairSpace E.carrier E.carrier,
        (∀ c, (e c : TemperedDistribution ℝ ℂ) =
          ∑ i, ((d i).equiv (c i) : TemperedDistribution ℝ ℂ)) ∧
        (∀ c h, commonCarrierHoleRows E.carrier S (e c) h =
          (∑ i, (d i).physicalCoefficient (c i) h.val,
           ∑ i, (d i).fourierCoefficient (c i) h.val)) ∧
        E.nullity = (∑ i, (d i).cyclotomicNullity) -
          Module.finrank ℂ (LinearMap.range ((commonCarrierHoleRows E.carrier S).comp e.toLinearMap)) ∧
        ∃ k : LinearMap.ker ((commonCarrierHoleRows E.carrier S).comp e.toLinearMap) ≃ₗ[ℂ]
            E.embeddedSpace,
          ∀ c, (k c : TemperedDistribution ℝ ℂ) = (e c : TemperedDistribution ℝ ℂ) := by
  classical
  let dirs := E.val.image fun v => rationalLineDirection v.2
  obtain ⟨step, hs, ep, hep, hrows, hnull⟩ := E.exists_latticePartnerHoleCoordinates
  have hex (i : dirs) : Nonempty (LatticePartnerResidueCoordinates E.val E.val (step i)) := by
    apply LatticePartnerResidueCoordinates.nonempty_of_present_physical E.property.1 E.property.1
    obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp i.property
    exact ⟨p, (mem_latticeDirectionClass _ _ _).mpr ⟨hp, hpi.trans (hs i).2.symm⟩⟩
  let d (i : dirs) := Classical.choice (hex i)
  let f := LinearEquiv.piCongrRight (fun i : dirs => (d i).equiv)
  let e := f.trans ep
  refine ⟨step, d, hs, e, ?_, ?_, ?_, E.exists_holeKernelEquiv_of_coordinates e⟩
  · intro c
    exact hep (f c)
  · intro c h
    change commonCarrierHoleRows E.carrier S (ep (f c)) h = _
    rw [hrows]
    have hx : (h.val : ℝ) ∈ E.carrier.carrier := h.val.property
    have hP (i : dirs) : ((d i).equiv (c i) : TemperedDistribution ℝ ℂ) ∈
        DistributionalMeyerPairSpace E.carrier E.carrier :=
      latticePartnerPairSpace_le E.val E.val (step i) ((d i).equiv (c i)).property
    have hPhysical (i : dirs) := (d i).physicalCoefficient_eq_original (c i) E.carrier
      ((mem_distributionalMeyerPairSpace_iff _ _ _).mp (hP i)).1 h.val
    have hFourier (i : dirs) := (d i).fourierCoefficient_eq_original (c i) E.carrier
      ((mem_distributionalMeyerPairSpace_iff _ _ _).mp (hP i)).2 h.val
    apply Prod.ext
    · apply Finset.sum_congr rfl
      intro i _
      change ((d i).equiv (c i) : TemperedDistribution ℝ ℂ) (E.carrier.isolationSchwartz h.val) =
        (d i).physicalCoefficient (c i) h.val
      simpa only [extendedAtomicCoefficient, dite_eq_left hx] using hPhysical i
    · apply Finset.sum_congr rfl
      intro i _
      change (𝓕 ((d i).equiv (c i) : TemperedDistribution ℝ ℂ)) (E.carrier.isolationSchwartz h.val) =
        (d i).fourierCoefficient (c i) h.val
      simpa only [extendedAtomicCoefficient, dite_eq_left hx] using hFourier i
  · have hDim : (∑ i : dirs, Module.finrank ℂ (latticePartnerPairSpace E.val E.val (step i))) =
        ∑ i : dirs, (d i).cyclotomicNullity :=
      Finset.sum_congr rfl fun i _ => (d i).equiv.finrank_eq.symm.trans
        (d i).finrank_ker_residueRows_eq_cyclotomicNullity
    have hRank := congrArg
      (fun R : Submodule ℂ (CommonCarrierHole E.carrier S → ℂ × ℂ) => Module.finrank ℂ R)
      ((ep.range_comp (commonCarrierHoleRows E.carrier S)).trans
        (e.range_comp (commonCarrierHoleRows E.carrier S)).symm)
    exact hnull.trans (congrArg₂ Nat.sub hDim hRank)

end
end MeyerGeneralProblem
