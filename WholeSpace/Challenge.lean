module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Finite-comb and finite-hole classification for relatively separated carriers

For the whole fixed-carrier space, maximize over finite unions of full
positive-step affine lattices whose difference from the carrier is finite.
At every missing site both original coefficients vanish. The rank of these
joint rows in the lattice residue coordinates determines the loss of dimension.
The one-record H6 theorem at the end uses a count bound only in physical space.
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

/-- A subcarrier of a locally finite carrier is locally finite. -/
def restrict (T : Set ℝ) (hT : T ⊆ S.carrier) : LocallyFiniteCarrier where
  carrier := T
  finite_inter_Icc a b :=
    (S.finite_inter_Icc a b).subset fun _ hx ↦ ⟨hT hx.1, hx.2⟩

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

attribute [-instance] instCommCStarAlgebraComplex in
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
abbrev AffineCombTerm.distribution (q : AffineCombTerm) (w : ℝ) (hw : 0 < w) :
    TemperedDistribution ℝ ℂ :=
  q.coefficient • modulatedAffineDiracComb w hw q.origin q.frequency

/-- The distribution is a finite sum of actual modulated Dirac combs. -/
abbrev IsFiniteModulatedDiracCombSum (T : TemperedDistribution ℝ ℂ) : Prop :=
  ∃ (ι : Type) (inst : Fintype ι), letI := inst
    ∃ (q : ι → AffineCombTerm) (w : ι → ℝ) (hw : ∀ i, 0 < w i),
      T = ∑ i, (q i).distribution (w i) (hw i)

attribute [-instance] instCommCStarAlgebraComplex in
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

/-- The number of carrier nodes in the half-open real window `[a, a + L)`. -/
noncomputable def windowCount (S : LocallyFiniteCarrier) (a L : ℝ) : ℕ :=
  Set.ncard (S.carrier ∩ Set.Ico a (a + L))

/-- The carrier has at most `K` points in each integer unit cell. -/
def UnitCellBound (S : LocallyFiniteCarrier) (K : ℕ) : Prop :=
  ∀ n : ℤ, windowCount S n 1 ≤ K

attribute [-instance] instCommCStarAlgebraComplex in
/-- Fourier transform on tempered distributions, characterized on every input. -/
def temperedFourierLinearMap :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] TemperedDistribution ℝ ℂ := by
  sorry

attribute [-instance] instCommCStarAlgebraComplex in
theorem temperedFourierLinearMap_apply (T : TemperedDistribution ℝ ℂ) :
    temperedFourierLinearMap T = FourierTransform.fourier T := by
  sorry

/-- The fixed-carrier space consists exactly of the atomic pairs in the next equivalence. -/
def DistributionalMeyerPairSpace (A B : LocallyFiniteCarrier) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) := by
  sorry

theorem mem_distributionalMeyerPairSpace_iff (A B : LocallyFiniteCarrier)
    (U : TemperedDistribution ℝ ℂ) :
    U ∈ DistributionalMeyerPairSpace A B ↔ AtomicOnCarrier A U ∧ AtomicOnCarrier B (𝓕 U) := by
  sorry

/-- The actual coefficient measured by the carrier isolation test. -/
def atomicCoefficientLinearMap (A : LocallyFiniteCarrier) (x : A.subtype) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] ℂ := by
  sorry

theorem atomicCoefficientLinearMap_on_tests (A : LocallyFiniteCarrier) (x : A.subtype)
    (T : TemperedDistribution ℝ ℂ) :
    atomicCoefficientLinearMap A x T = T (A.isolationSchwartz x) := by
  sorry

/-- All sites in `S` used by at least one vector of a space of distributions. -/
def atomicSupportUnion (S : LocallyFiniteCarrier)
    (V : Submodule ℂ (TemperedDistribution ℝ ℂ)) : LocallyFiniteCarrier :=
  by sorry

theorem mem_atomicSupportUnion_iff (S : LocallyFiniteCarrier)
    (V : Submodule ℂ (TemperedDistribution ℝ ℂ)) (x : ℝ) :
    x ∈ (atomicSupportUnion S V).carrier ↔
      ∃ hx : x ∈ S.carrier, ∃ U : V,
        (U : TemperedDistribution ℝ ℂ) (S.isolationSchwartz ⟨x, hx⟩) ≠ 0 := by
  sorry

/-- The full affine integer line, including the zero-step singleton. -/
def affineLatticeLine (y w : ℝ) : Set ℝ :=
  Set.range (fun k : ℤ => y + (k : ℝ) * w)

/-- The true finite union of the specified affine integer lines. -/
def affineLatticeUnionCarrier (E : Finset (ℝ × ℝ)) : LocallyFiniteCarrier := by
  sorry

/-- The carrier consists exactly of the translated integer lattices in the finite list. -/
theorem mem_affineLatticeUnionCarrier (E : Finset (ℝ × ℝ)) (x : ℝ) :
    x ∈ (affineLatticeUnionCarrier E).carrier ↔ ∃ p ∈ E, x ∈ affineLatticeLine p.1 p.2 := by
  sorry

/-- Restriction to the intersection of the envelope and the allowed carrier. -/
def commonCarrierIntersection (L S : LocallyFiniteCarrier) : LocallyFiniteCarrier :=
  L.restrict (L.carrier ∩ S.carrier) inter_subset_left

/-- Original holes indexed inside the locally finite envelope. -/
def CommonCarrierHole (L S : LocallyFiniteCarrier) : Type :=
  { x : L.subtype // (x : ℝ) ∉ S.carrier }

/-- Both literal coefficient rows at each original missing site. -/
def commonCarrierHoleRows (L S : LocallyFiniteCarrier) :
    DistributionalMeyerPairSpace L L →ₗ[ℂ] (CommonCarrierHole L S → ℂ × ℂ) := by
  sorry

theorem commonCarrierHoleRows_apply_pair (L S : LocallyFiniteCarrier)
    (T : DistributionalMeyerPairSpace L L) (x : CommonCarrierHole L S) :
    commonCarrierHoleRows L S T x =
      ((T : TemperedDistribution ℝ ℂ) (L.isolationSchwartz x.val),
       (𝓕 (T : TemperedDistribution ℝ ℂ)) (L.isolationSchwartz x.val)) := by
  sorry

/-- Finite unions of full positive-step lattices with finitely many holes
in the given common carrier. -/
abbrev FiniteHoleEnvelope (S : LocallyFiniteCarrier) :=
  {E : Finset (ℝ × ℝ) // (∀ p ∈ E, 0 < p.2) ∧
    ((affineLatticeUnionCarrier E).carrier \ S.carrier).Finite}

namespace FiniteHoleEnvelope

variable {S : LocallyFiniteCarrier}

/-- The locally finite carrier of the envelope before deleting holes. -/
abbrev carrier (E : FiniteHoleEnvelope S) : LocallyFiniteCarrier :=
  affineLatticeUnionCarrier E.val

/-- The original source subspace on the intersection with the envelope. -/
abbrev embeddedSpace (E : FiniteHoleEnvelope S) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  DistributionalMeyerPairSpace (commonCarrierIntersection E.carrier S)
    (commonCarrierIntersection E.carrier S)

/-- The dimension of the entire envelope space minus the rank of all its
original physical and Fourier hole rows. -/
def nullity (E : FiniteHoleEnvelope S) : ℕ := by
  sorry

theorem nullity_eq_dimension_sub_rank {S : LocallyFiniteCarrier} (E : FiniteHoleEnvelope S) :
    E.nullity = Module.finrank ℂ (DistributionalMeyerPairSpace E.carrier E.carrier) -
      Module.finrank ℂ (LinearMap.range (commonCarrierHoleRows E.carrier S)) := by
  sorry

end FiniteHoleEnvelope

/-- The directed union of the embedded kernels over all finite-hole envelopes. -/
def finiteHoleEnvelopeSpace (S : LocallyFiniteCarrier) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) := by
  sorry

theorem mem_finiteHoleEnvelopeSpace (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) :
    T ∈ finiteHoleEnvelopeSpace S ↔ ∃ E : FiniteHoleEnvelope S, T ∈ E.embeddedSpace := by
  sorry

/-- On every bounded-count common carrier the complete space equals a
finite-hole envelope kernel attaining the maximum nullity. -/
theorem boundedCount_commonSpace_holeClassification
    (S : LocallyFiniteCarrier) (K : ℕ) (hK : UnitCellBound S K) :
    let V := DistributionalMeyerPairSpace S S
    V = finiteHoleEnvelopeSpace S ∧
      (∃ E : FiniteHoleEnvelope S, V = E.embeddedSpace ∧
        Module.finrank ℂ V = E.nullity ∧ ∀ F : FiniteHoleEnvelope S, F.nullity ≤ E.nullity) ∧
      (V ≠ ⊥ ↔ ∃ E : FiniteHoleEnvelope S, 0 < E.nullity) := by
  sorry

/-- One relatively separated side suffices for finite dimension of the
whole broad pair space. No uniform separation or variation bound is used. -/
theorem finiteDimensional_distributionalMeyerPairSpace_of_unitCellBound
    (A B : LocallyFiniteCarrier) (K : ℕ) (hK : UnitCellBound A K) :
    FiniteDimensional ℂ (DistributionalMeyerPairSpace A B) := by
  sorry

/-- The rational direction of a real step, including its zero multiple. -/
def rationalLineDirection (d : ℝ) : Submodule ℚ ℝ :=
  Submodule.span ℚ ({d} : Set ℝ)

/-- The cosets in a finite lattice presentation having one direction. -/
def latticeDirectionClass (E : Finset (ℝ × ℝ)) (D : Submodule ℚ ℝ) :
    Finset (ℝ × ℝ) := by
  sorry

theorem mem_latticeDirectionClass (E : Finset (ℝ × ℝ)) (D : Submodule ℚ ℝ)
    (v : ℝ × ℝ) : v ∈ latticeDirectionClass E D ↔
      v ∈ E ∧ rationalLineDirection v.2 = D := by
  sorry

/-- Physical and reciprocal spectral direction carriers for one partner. -/
abbrev latticePartnerPairSpace (E F : Finset (ℝ × ℝ)) (w : ℝ) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  DistributionalMeyerPairSpace
    (affineLatticeUnionCarrier (latticeDirectionClass E (rationalLineDirection w)))
    (affineLatticeUnionCarrier (latticeDirectionClass F (rationalLineDirection w⁻¹)))

/-- A forbidden residue of an orbit with periodic physical incidence. -/
def ForbiddenLatticeOrbitResidue {ι : Type*} (A : LocallyFiniteCarrier) (w : ℝ)
    (origin : ι → ℝ) (p : ℕ) :=
  {j : ι × Fin p // origin j.1 + (j.2.val : ℝ) * w ∉ A.carrier}

/-- On each forbidden residue, sample the backward consecutive values
of the character sum along the residue progression. -/
def latticeOrbitResidueRows {ι : Type*} (A : LocallyFiniteCarrier) (w : ℝ)
    (origin : ι → ℝ) (modes : List ℝ) (p : ℕ) :
    (ι → Fin modes.length → ℂ) →ₗ[ℂ]
      (ForbiddenLatticeOrbitResidue A w origin p → Fin modes.length → ℂ) := by
  sorry

theorem latticeOrbitResidueRows_apply_entry {ι : Type*} (A : LocallyFiniteCarrier) (w : ℝ)
    (origin : ι → ℝ) (modes : List ℝ) (p : ℕ) (c : ι → Fin modes.length → ℂ)
    (r : ForbiddenLatticeOrbitResidue A w origin p) (n : Fin modes.length) :
    latticeOrbitResidueRows A w origin modes p c r n =
      ∑ j, c r.val.1 j * combModulationCharacter (modes.get j)
        (origin r.val.1 + (((r.val.2.val : ℤ) - (n.val : ℤ) * (p : ℤ) : ℤ) : ℝ) * w) := by
  sorry

/-- Synthesize the original distribution from the orbit coefficient array. -/
def latticeOrbitSynthesis {ι : Type*} [Fintype ι] (w : ℝ) (hw : 0 < w)
    (origin : ι → ℝ) (modes : List ℝ) :
    (ι → Fin modes.length → ℂ) →ₗ[ℂ] TemperedDistribution ℝ ℂ := by
  sorry

theorem latticeOrbitSynthesis_apply {ι : Type*} [Fintype ι] (w : ℝ) (hw : 0 < w)
    (origin : ι → ℝ) (modes : List ℝ) (c : ι → Fin modes.length → ℂ) :
    latticeOrbitSynthesis w hw origin modes c =
      ∑ i, ∑ j, c i j • modulatedAffineDiracComb w hw (origin i) (modes.get j) := by
  sorry

/-- The literal mass function of an affine modulated comb. -/
def AffineCombTerm.coefficientFunction (q : AffineCombTerm) (w : ℝ) : ℝ → ℂ :=
  (affineLatticeLine q.origin w).indicator
    (fun x => q.coefficient * combModulationCharacter q.frequency x)

/-- The exact Fourier image of a term, including its scalar phase. -/
def AffineCombTerm.fourierTerm (q : AffineCombTerm) (w : ℝ) : AffineCombTerm :=
  ⟨-q.origin, q.frequency,
    q.coefficient * ((w⁻¹ : ℝ) : ℂ) * combModulationCharacter q.origin q.frequency⟩

/-- The finite set of powered phases. -/
def latticePhaseClasses {ι : Type*} [Fintype ι] (z : ι → ℂ) (p : ℕ) : Finset ℂ := by
  classical
  exact Finset.univ.image fun i => z i ^ p

/-- The original frequencies in one powered-phase class. -/
abbrev LatticePhaseClass {ι : Type*} [Fintype ι] (z : ι → ℂ) (p : ℕ)
    (η : latticePhaseClasses z p) :=
  {i : ι // z i ^ p = η.val}

/-- The field generated by the chosen primitive root of unity. -/
def latticeCyclotomicField (ζ : ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({ζ} : Set ℂ)

/-- The exact root-of-unity matrix over the cyclotomic field. -/
def latticeCyclotomicMatrix {R C : Type*} (ζ : ℂ) (exponent : R → C → ℕ) :
    Matrix R C (latticeCyclotomicField ζ) :=
  Matrix.of fun r c =>
    (⟨ζ, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)⟩ : latticeCyclotomicField ζ) ^
      exponent r c

/-- The dimension of the literal residue kernel is the sum of the
cyclotomic nullities over all orbits and powered-phase classes. -/
theorem exists_latticeOrbitResidueRows_cyclotomic_finrank
    {ι : Type*} [Fintype ι] (A : LocallyFiniteCarrier) (w : ℝ) (origin : ι → ℝ)
    (modes : List ℝ) (p : ℕ) (hp : 0 < p)
    (hModes : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t)) :
    haveI := Classical.propDecidable
    let z (j : Fin modes.length) := combModulationCharacter (modes.get j) w
    let ζ := Complex.exp (2 * Real.pi * Complex.I / p)
    let R (i : ι) := {r : Fin p // origin i + (r.val : ℝ) * w ∉ A.carrier}
    ∃ k : ∀ η : latticePhaseClasses z p, LatticePhaseClass z p η → Fin p,
      (∀ η, Function.Injective (k η)) ∧
      (∀ c, c ∈ LinearMap.ker (latticeOrbitResidueRows A w origin modes p) ↔
        ∀ r : ForbiddenLatticeOrbitResidue A w origin p, ∀ η : latticePhaseClasses z p,
          (∑ j : LatticePhaseClass z p η,
            c r.val.1 j.val * combModulationCharacter (modes.get j.val) (origin r.val.1) *
              ζ ^ ((k η j).val * r.val.2.val)) = 0) ∧
      Module.finrank ℂ (LinearMap.ker (latticeOrbitResidueRows A w origin modes p)) =
        ∑ i : ι, ∑ η : latticePhaseClasses z p,
          (Fintype.card (LatticePhaseClass z p η) -
            (latticeCyclotomicMatrix ζ
              (fun (r : R i) j => (k η j).val * r.val.val)).rank) := by
  sorry

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
abbrev residueRows (d : LatticePartnerResidueCoordinates E F w) :=
  latticeOrbitResidueRows
    (affineLatticeUnionCarrier (latticeDirectionClass E (rationalLineDirection w)))
    d.orbitStep d.origin d.modes d.modulus

/-- A physical coefficient, with ordinary addition at all coincident
sites of the original combs. -/
abbrev physicalCoefficient (d : LatticePartnerResidueCoordinates E F w)
    (c : LinearMap.ker d.residueRows) (x : ℝ) : ℂ := by
  letI := d.orbitFintype
  exact ∑ i, ∑ j, (⟨d.modes.get j, d.origin i, c.val i j⟩ : AffineCombTerm).coefficientFunction
    d.orbitStep x

/-- A Fourier coefficient with the original reciprocal coset and
Poisson phase of each summand. -/
abbrev fourierCoefficient (d : LatticePartnerResidueCoordinates E F w)
    (c : LinearMap.ker d.residueRows) (x : ℝ) : ℂ := by
  letI := d.orbitFintype
  exact ∑ i, ∑ j, ((⟨d.modes.get j, d.origin i, c.val i j⟩ : AffineCombTerm).fourierTerm
    d.orbitStep).coefficientFunction d.orbitStep⁻¹ x

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

end LatticePartnerResidueCoordinates

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
  sorry

/-- Every broad value-only pair on two relatively separated allowed
carriers is a finite sum of modulated combs on each original record. -/
theorem finiteModulatedDiracCombSum_pair_of_two_unitCellBounds
    (A B : LocallyFiniteCarrier) (K M : ℕ) (hA : UnitCellBound A K) (hB : UnitCellBound B M)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ DistributionalMeyerPairSpace A B) :
    IsFiniteModulatedDiracCombSum T ∧ IsFiniteModulatedDiracCombSum (𝓕 T) := by
  sorry

attribute [-instance] instCommCStarAlgebraComplex in
/-- The exact module of the whole broad pair space is finitely generated.
One polynomial in that module vanishes on every active physical site
and annihilates every member of the space. -/
theorem spectralModule_fg_and_exists_common_finiteExponentialAnnihilator_of_unitCellBound
    (A B : LocallyFiniteCarrier) (K : ℕ) (hK : UnitCellBound A K) :
    let V := DistributionalMeyerPairSpace A B
    let B₀ := atomicSupportUnion B (V.map temperedFourierLinearMap)
    let A₀ := atomicSupportUnion A V
    (AddSubgroup.closure B₀.carrier).FG ∧
    ∃ (ι : Type) (f : Fintype ι), letI := f
      ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
        (∀ i, a i ∈ AddSubgroup.closure B₀.carrier) ∧
        (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
        (∀ x ∈ A₀.carrier, ∑ i, c i * combModulationCharacter (a i) x = 0) ∧
        ∀ U ∈ V, finiteExponentialMultiplication a c U = 0 := by
  sorry

end MeyerGeneralProblem
end
