module

public import MeyerGeneralProblem.Distribution.CenteredCountFiniteComb
public import MeyerGeneralProblem.Distribution.OriginalTranslationRecurrence
public import MeyerGeneralProblem.Distribution.CombCoefficientReconstruction
public import MeyerGeneralProblem.Distribution.EnvelopeHoleRows

@[expose] public section

/-!
# Exact coordinates for paired lattice orbits

One coefficient vector on each physical orbit describes the complete
pair space when the opposite carrier is a finite union of cosets at the
reciprocal step. Rows at the forbidden physical sites constrain the
vectors. The synthesis uses the original modulated Dirac combs.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators SchwartzMap FourierTransform

/-- The union of a finite family of full affine lattices of one step. -/
def latticeOrbitUnion {ι : Type*} [Fintype ι] (w : ℝ)
    (origin : ι → ℝ) : LocallyFiniteCarrier :=
  affineLatticeUnionCarrier (Finset.univ.image fun i => (origin i, w))

theorem mem_latticeOrbitUnion {ι : Type*} [Fintype ι] (w : ℝ)
    (origin : ι → ℝ) (x : ℝ) :
    x ∈ (latticeOrbitUnion w origin).carrier ↔
      ∃ i, x ∈ affineLatticeLine (origin i) w := by
  classical
  rw [latticeOrbitUnion, mem_affineLatticeUnionCarrier]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_exists_eq_and]

/-- Synthesize the original distribution from the orbit coefficient array. -/
def latticeOrbitSynthesis {ι : Type*} [Fintype ι] (w : ℝ) (hw : 0 < w)
    (origin : ι → ℝ) (modes : List ℝ) :
    (ι → Fin modes.length → ℂ) →ₗ[ℂ] TemperedDistribution ℝ ℂ where
  toFun c := ∑ i, ∑ j, c i j • modulatedAffineDiracComb w hw (origin i) (modes.get j)
  map_add' c d := by
    calc
      _ = ∑ i, ∑ j, (c i j • modulatedAffineDiracComb w hw (origin i) (modes.get j) +
          d i j • modulatedAffineDiracComb w hw (origin i) (modes.get j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          add_smul (c i j) (d i j) _
      _ = _ := by simp only [Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem latticeOrbitSynthesis_apply {ι : Type*} [Fintype ι] (w : ℝ) (hw : 0 < w)
    (origin : ι → ℝ) (modes : List ℝ) (c : ι → Fin modes.length → ℂ) :
    latticeOrbitSynthesis w hw origin modes c =
      ∑ i, ∑ j, c i j • modulatedAffineDiracComb w hw (origin i) (modes.get j) := rfl

/-- The missing physical sites indexed by their orbit and integer step. -/
def ForbiddenLatticeOrbitSite {ι : Type*} (A : LocallyFiniteCarrier) (w : ℝ)
    (origin : ι → ℝ) :=
  {j : ι × ℤ // origin j.1 + (j.2 : ℝ) * w ∉ A.carrier}

/-- The canonical pointwise rows on the forbidden sites of the orbits. -/
def latticeOrbitRestrictionRows {ι : Type*} (A : LocallyFiniteCarrier) (w : ℝ)
    (origin : ι → ℝ) (modes : List ℝ) :
    (ι → Fin modes.length → ℂ) →ₗ[ℂ] (ForbiddenLatticeOrbitSite A w origin → ℂ) where
  toFun c x := ∑ j, c x.val.1 j * combModulationCharacter (modes.get j)
    (origin x.val.1 + (x.val.2 : ℝ) * w)
  map_add' c d := by
    funext x
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, Finset.mul_sum, RingHom.id_apply]

theorem latticeOrbitRestrictionRows_apply {ι : Type*} (A : LocallyFiniteCarrier) (w : ℝ)
    (origin : ι → ℝ) (modes : List ℝ) (c : ι → Fin modes.length → ℂ)
    (x : ForbiddenLatticeOrbitSite A w origin) :
    latticeOrbitRestrictionRows A w origin modes c x =
      ∑ j, c x.val.1 j * combModulationCharacter (modes.get j)
        (origin x.val.1 + (x.val.2 : ℝ) * w) := rfl

theorem latticeOrbitSynthesis_atomicOnCarrier {ι : Type*} [Fintype ι]
    (w : ℝ) (hw : 0 < w) (origin : ι → ℝ) (modes : List ℝ)
    (c : ι → Fin modes.length → ℂ) :
    AtomicOnCarrier (latticeOrbitUnion w origin) (latticeOrbitSynthesis w hw origin modes c) := by
  intro f hf
  rw [latticeOrbitSynthesis_apply]
  simp only [_root_.sum_apply, smul_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [modulatedAffineDiracComb_apply]
  have hz (k : ℤ) : f (origin i + (k : ℝ) * w) = 0 :=
    hf _ ((mem_latticeOrbitUnion _ _ _).mpr ⟨i, k, rfl⟩)
  simp only [hz, mul_zero, tsum_zero, smul_zero]

theorem fourier_latticeOrbitSynthesis_atomicOnCarrier {ι : Type*} [Fintype ι]
    (w : ℝ) (hw : 0 < w) (origin : ι → ℝ) (modes : List ℝ)
    (c : ι → Fin modes.length → ℂ) :
    AtomicOnCarrier (latticeOrbitUnion w⁻¹ modes.get)
      (𝓕 (latticeOrbitSynthesis w hw origin modes c)) := by
  intro f hf
  rw [latticeOrbitSynthesis_apply, ← temperedFourierLinearMap_apply, map_sum]
  simp only [map_sum, map_smul, temperedFourierLinearMap_apply, _root_.sum_apply, smul_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have h := fourier_modulatedAffineDiracComb_atomicOnCarrier w hw (origin i) (modes.get j)
  rw [h f (fun x hx => (hf x ((mem_latticeOrbitUnion _ _ _).mpr
    ⟨j, by simpa only [affineDiracCombCarrier_eq_affineLatticeLine] using hx⟩))), smul_zero]

/-- Evaluation is the literal phase sum of the unique orbit containing
the point. -/
theorem extendedAtomicCoefficient_latticeOrbitSynthesis_on_orbit {ι : Type*} [Fintype ι]
    (w : ℝ) (hw : 0 < w) (origin : ι → ℝ)
    (hdisj : Pairwise fun i j => Disjoint (affineLatticeLine (origin i) w)
      (affineLatticeLine (origin j) w))
    (modes : List ℝ) (c : ι → Fin modes.length → ℂ)
    (i : ι) (x : ℝ) (hx : x ∈ affineLatticeLine (origin i) w) :
    extendedAtomicCoefficient (latticeOrbitUnion w origin) (latticeOrbitSynthesis w hw origin modes c) x =
      ∑ j, c i j * combModulationCharacter (modes.get j) x := by
  classical
  let A := latticeOrbitUnion w origin
  let q (b : ι) (j : Fin modes.length) : AffineCombTerm := ⟨modes.get j, origin b, c b j⟩
  have hEval (b : ι) (j : Fin modes.length) :
      extendedAtomicCoefficient A ((q b j).distribution w hw) x =
        (q b j).coefficientFunction w x :=
    extendedAtomicCoefficient_affineCombTerm (q b j) w hw A
      (fun y hy => (mem_latticeOrbitUnion _ _ _).mpr ⟨b, hy⟩) x
  change extendedAtomicCoefficient A (∑ b, ∑ j, (q b j).distribution w hw) x = _
  simp_rw [extendedAtomicCoefficient_finset_sum, hEval]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun b _ hb => ?_)]
  · simp only [AffineCombTerm.coefficientFunction, q, Set.indicator_of_mem hx]
  · have hn : x ∉ affineLatticeLine (origin b) w :=
      fun h => Set.disjoint_left.mp (hdisj hb) h hx
    simp only [AffineCombTerm.coefficientFunction, q, Set.indicator_of_notMem hn,
      Finset.sum_const_zero]

/-- The Fourier rows retain the full reciprocal coset condition and the
phase of each original modulated comb. -/
theorem extendedAtomicCoefficient_fourier_latticeOrbitSynthesis
    {ι : Type*} [Fintype ι] (w : ℝ) (hw : 0 < w) (origin : ι → ℝ)
    (modes : List ℝ) (c : ι → Fin modes.length → ℂ) (x : ℝ) :
    extendedAtomicCoefficient (latticeOrbitUnion w⁻¹ modes.get)
      (𝓕 (latticeOrbitSynthesis w hw origin modes c)) x =
    ∑ i, ∑ j, (affineLatticeLine (modes.get j) w⁻¹).indicator
      (fun z => c i j * ((w⁻¹ : ℝ) : ℂ) * combModulationCharacter (origin i) (modes.get j) *
        combModulationCharacter (-origin i) z) x := by
  classical
  let B := latticeOrbitUnion w⁻¹ modes.get
  let q (i : ι) (j : Fin modes.length) : AffineCombTerm := ⟨modes.get j, origin i, c i j⟩
  change extendedAtomicCoefficient B (𝓕 (∑ i, ∑ j, (q i j).distribution w hw)) x = _
  rw [← temperedFourierLinearMap_apply, map_sum]
  simp only [map_sum, temperedFourierLinearMap_apply, fourier_affineCombTerm]
  simp_rw [extendedAtomicCoefficient_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hsub : affineLatticeLine ((q i j).fourierTerm w).origin w⁻¹ ⊆ B.carrier :=
    fun y hy => (mem_latticeOrbitUnion _ _ _).mpr ⟨j, hy⟩
  rw [extendedAtomicCoefficient_affineCombTerm _ _ _ B hsub x]
  simp only [AffineCombTerm.coefficientFunction, AffineCombTerm.fourierTerm, q]

private theorem latticeOrbit_mode_coefficients_eq_zero
    (w y : ℝ) (modes : List ℝ)
    (hmodes : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t))
    (c : Fin modes.length → ℂ)
    (hz : ∀ k : ℤ, ∑ j, c j *
      combModulationCharacter (modes.get j) (y + (k : ℝ) * w) = 0) :
    c = 0 := by
  let phase (j : Fin modes.length) := combModulationCharacter (-w) (modes.get j)
  have hphase : Function.Injective phase := by
    intro i j he
    rcases lt_trichotomy i j with h | h | h
    · exact ((List.pairwise_iff_get.mp hmodes i j h) he).elim
    · exact h
    · exact ((List.pairwise_iff_get.mp hmodes j i h) he.symm).elim
  let V := (Matrix.vandermonde phase).transpose
  have hdet : V.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hphase
  have hinj : Function.Injective V.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det V).mpr (isUnit_iff_ne_zero.mpr hdet))
  let a (j : Fin modes.length) := c j * combModulationCharacter (modes.get j) y
  have hv : V.mulVec a = 0 := by
    funext n
    change (∑ j, phase j ^ n.val * a j) = 0
    rw [← hz (-(n.val : ℤ))]
    apply Finset.sum_congr rfl
    intro j _
    have he : y + ((-(n.val : ℤ) : ℤ) : ℝ) * w = y + (n.val : ℝ) * (-w) := by
      push_cast
      ring
    rw [he]
    have hchar : combModulationCharacter (modes.get j) (y + (n.val : ℝ) * (-w)) =
        combModulationCharacter (modes.get j) y * phase j ^ n.val := by
      simpa only [Int.cast_natCast, zpow_natCast, phase, combModulationCharacter, mul_comm (-w)] using
        combModulationCharacter_on_integer_affine (modes.get j) y (-w) (n.val : ℤ)
    rw [hchar]
    simp only [a]
    ring
  have hzero : a = 0 := hinj (by simpa only [Matrix.mulVec_zero] using hv)
  funext j
  have hzj : c j * combModulationCharacter (modes.get j) y = 0 := congrFun hzero j
  have hne : combModulationCharacter (modes.get j) y ≠ 0 :=
    norm_pos_iff.mp (by rw [norm_combModulationCharacter]; norm_num)
  exact (mul_eq_zero.mp hzj).resolve_right hne

theorem latticeOrbitSynthesis_injective {ι : Type*} [Fintype ι]
    (w : ℝ) (hw : 0 < w) (origin : ι → ℝ)
    (hdisj : Pairwise fun i j => Disjoint (affineLatticeLine (origin i) w)
      (affineLatticeLine (origin j) w))
    (modes : List ℝ)
    (hmodes : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t)) :
    Function.Injective (latticeOrbitSynthesis w hw origin modes) := by
  intro c d he
  have hz : latticeOrbitSynthesis w hw origin modes (c - d) = 0 := by
    rw [map_sub, he, sub_self]
  apply sub_eq_zero.mp
  funext i
  apply latticeOrbit_mode_coefficients_eq_zero w (origin i) modes hmodes
  intro k
  rw [← extendedAtomicCoefficient_latticeOrbitSynthesis_on_orbit w hw origin hdisj modes
    (c - d) i _ ⟨k, rfl⟩, hz]
  simp [extendedAtomicCoefficient]

/-- Literal orbit coordinates for the entire pair space. The prescribed reciprocal
cosets supply the spectral carrier. -/
theorem exists_latticeOrbitPairEquiv {ι : Type*} [Fintype ι]
    (A : LocallyFiniteCarrier) (w : ℝ) (hw : 0 < w) (origin : ι → ℝ)
    (hA : A.carrier ⊆ (latticeOrbitUnion w origin).carrier)
    (hdisj : Pairwise fun i j => Disjoint (affineLatticeLine (origin i) w)
      (affineLatticeLine (origin j) w))
    (modes : List ℝ)
    (hmodes : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t)) :
    ∃ e : LinearMap.ker (latticeOrbitRestrictionRows A w origin modes) ≃ₗ[ℂ]
        DistributionalMeyerPairSpace A (latticeOrbitUnion w⁻¹ modes.get),
      ∀ c, (e c : TemperedDistribution ℝ ℂ) = latticeOrbitSynthesis w hw origin modes c := by
  classical
  let U := latticeOrbitUnion w origin
  let B := latticeOrbitUnion w⁻¹ modes.get
  let W := LinearMap.ker (latticeOrbitRestrictionRows A w origin modes)
  let V := DistributionalMeyerPairSpace A B
  let synth := latticeOrbitSynthesis w hw origin modes
  have hmem (c : W) : synth c ∈ V := by
    apply (mem_distributionalMeyerPairSpace_iff _ _ _).mpr
    refine ⟨?_, fourier_latticeOrbitSynthesis_atomicOnCarrier w hw origin modes c⟩
    have hR : U.restrict A.carrier hA = A := LocallyFiniteCarrier.ext rfl
    rw [← hR, atomicOnCarrier_restrict_iff]
    refine ⟨latticeOrbitSynthesis_atomicOnCarrier w hw origin modes c, fun x hx => ?_⟩
    obtain ⟨i, k, he⟩ := (mem_latticeOrbitUnion w origin x).mp x.property
    change origin i + (k : ℝ) * w = (x : ℝ) at he
    let site : ForbiddenLatticeOrbitSite A w origin := ⟨(i, k), by
      change origin i + (k : ℝ) * w ∉ A.carrier
      rwa [he]⟩
    have hrow := congrFun (LinearMap.mem_ker.mp c.property) site
    rw [latticeOrbitRestrictionRows_apply, Pi.zero_apply] at hrow
    change (∑ j, c.val i j * combModulationCharacter (modes.get j)
      (origin i + (k : ℝ) * w)) = 0 at hrow
    rw [he] at hrow
    have hcoef := extendedAtomicCoefficient_latticeOrbitSynthesis_on_orbit w hw origin hdisj
      modes c i x ⟨k, he⟩
    rw [hrow] at hcoef
    change extendedAtomicCoefficient U (synth c) (x : ℝ) = 0 at hcoef
    have hxU : (x : ℝ) ∈ U.carrier := x.property
    rw [extendedAtomicCoefficient, dite_eq_left hxU] at hcoef
    exact hcoef
  let l : W →ₗ[ℂ] V := (synth.comp W.subtype).codRestrict V hmem
  have hInjective : Function.Injective l := by
    intro c d he
    apply Subtype.ext
    apply latticeOrbitSynthesis_injective w hw origin hdisj modes hmodes
    exact congrArg Subtype.val he
  have hSurjective : Function.Surjective l := by
    intro T
    obtain ⟨hT, hFT⟩ := (mem_distributionalMeyerPairSpace_iff A B T).mp T.property
    have hz : translationDifferenceProduct
        (modes.map fun s => (w, combModulationCharacter (-w) s))
        (extendedAtomicCoefficient A T) = 0 := by
      have hcover (x : ℝ) (hx : x ∈ B.carrier) :
          ∃ p ∈ [(w, modes)], ∃ s ∈ p.2, ∃ k : ℤ, x = s + (k : ℝ) * p.1⁻¹ := by
        obtain ⟨j, k, he⟩ := (mem_latticeOrbitUnion _ _ _).mp hx
        exact ⟨(w, modes), List.mem_cons_self, modes.get j, List.get_mem _ _, k, he.symm⟩
      simpa [combTranslationWeightsByClass] using
        translationDifferenceProduct_extendedAtomicCoefficient_eq_zero_of_spectral_cover
          [(w, modes)] (by simpa using hw) A B T hT hFT hcover
    choose c hc using fun i : ι =>
      exists_character_modes_on_affine_line w modes hmodes _ hz (origin i)
    have hcW : c ∈ W := by
      apply LinearMap.mem_ker.mpr
      funext x
      rw [latticeOrbitRestrictionRows_apply, ← hc x.val.1 x.val.2]
      simp only [extendedAtomicCoefficient, dite_eq_right x.property, Pi.zero_apply]
    refine ⟨⟨c, hcW⟩, Subtype.ext ?_⟩
    change synth c = (T : TemperedDistribution ℝ ℂ)
    apply atomic_eq_of_coefficients U _ _
      (latticeOrbitSynthesis_atomicOnCarrier w hw origin modes c) (hT.mono hA)
    intro x
    obtain ⟨i, k, he⟩ := (mem_latticeOrbitUnion w origin x).mp x.property
    change origin i + (k : ℝ) * w = (x : ℝ) at he
    have hS := extendedAtomicCoefficient_latticeOrbitSynthesis_on_orbit w hw origin hdisj
      modes c i x ⟨k, he⟩
    have hOrig := extendedAtomicCoefficient_on_larger_carrier A U hA T hT (x : ℝ)
    rw [← he, hc i k] at hOrig
    rw [he] at hOrig
    have h := hS.trans hOrig.symm
    change extendedAtomicCoefficient U (synth c) (x : ℝ) =
      extendedAtomicCoefficient U (T : TemperedDistribution ℝ ℂ) (x : ℝ) at h
    have hxU : (x : ℝ) ∈ U.carrier := x.property
    simp only [extendedAtomicCoefficient, dite_eq_left hxU] at h
    exact h
  exact ⟨LinearEquiv.ofBijective l ⟨hInjective, hSurjective⟩, fun _ => rfl⟩

end
end MeyerGeneralProblem
