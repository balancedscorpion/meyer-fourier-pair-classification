module

public import MeyerGeneralProblem.Distribution.PairedMeyerSpace
public import MeyerGeneralProblem.Distribution.FiniteAnnihilatorGeneration
public import MeyerGeneralProblem.Distribution.RestrictedAtomicRows
public import MeyerGeneralProblem.UniformDiscrete.GenericSupport

@[expose] public section

/-!
# A common annihilator on the whole broad pair space

A generic linear combination in the finite-dimensional space attains
both unions of actual nonzero supports. Its spectral module and its
physical support then give one annihilator for every source.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped FourierTransform SchwartzMap
open UniformDiscrete

/-- All sites in `S` used by at least one vector of a space of distributions. -/
def atomicSupportUnion (S : LocallyFiniteCarrier)
    (V : Submodule ℂ (TemperedDistribution ℝ ℂ)) : LocallyFiniteCarrier :=
  S.restrict {x | ∃ hx : x ∈ S.carrier, ∃ U : V, (U : TemperedDistribution ℝ ℂ)
    (S.isolationSchwartz ⟨x, hx⟩) ≠ 0} (fun _ ⟨hx, _⟩ => hx)

private theorem atomicOnCarrier_atomicSupportUnion (S : LocallyFiniteCarrier)
    (V : Submodule ℂ (TemperedDistribution ℝ ℂ)) (U : V)
    (hU : AtomicOnCarrier S (U : TemperedDistribution ℝ ℂ)) :
    AtomicOnCarrier (atomicSupportUnion S V) (U : TemperedDistribution ℝ ℂ) := by
  apply (atomicOnCarrier_restrict_iff _ _ _ _).2
  refine ⟨hU, fun x hnot => ?_⟩
  by_contra hx
  exact hnot ⟨x.property, U, hx⟩

/-- Restricting the allowed carriers while retaining both unions of
actual supports preserves the whole original pair space. -/
theorem distributionalMeyerPairSpace_eq_of_contains_atomicSupportUnion
    (A B A' B' : LocallyFiniteCarrier)
    (hA : A'.carrier ⊆ A.carrier) (hB : B'.carrier ⊆ B.carrier)
    (hA' : (atomicSupportUnion A (DistributionalMeyerPairSpace A B)).carrier ⊆ A'.carrier)
    (hB' : (atomicSupportUnion B ((DistributionalMeyerPairSpace A B).map
      temperedFourierLinearMap)).carrier ⊆ B'.carrier) :
    DistributionalMeyerPairSpace A B = DistributionalMeyerPairSpace A' B' := by
  apply le_antisymm
  · intro U hU
    have h := (mem_distributionalMeyerPairSpace_iff A B U).mp hU
    let V := DistributionalMeyerPairSpace A B
    let F := V.map temperedFourierLinearMap
    let W : F := ⟨𝓕 U, ⟨U, hU, rfl⟩⟩
    have ha := atomicOnCarrier_atomicSupportUnion A V ⟨U, hU⟩ h.1
    have hb := atomicOnCarrier_atomicSupportUnion B F W h.2
    exact (mem_distributionalMeyerPairSpace_iff A' B' U).mpr
      ⟨ha.mono hA', hb.mono hB'⟩
  · intro U hU
    have h := (mem_distributionalMeyerPairSpace_iff A' B' U).mp hU
    exact (mem_distributionalMeyerPairSpace_iff A B U).mpr
      ⟨h.1.mono hA, h.2.mono hB⟩

/-- At a nonzero physical atom, exact distributional annihilation forces
the finite exponential symbol to vanish at that point. -/
theorem finiteExponentialSymbol_eq_zero_of_annihilated_of_nonzero_atom
    {ι : Type*} [Fintype ι] (A : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hU : AtomicOnCarrier A U) (a : ι → ℝ) (c : ι → ℂ)
    (hz : finiteExponentialMultiplication a c U = 0)
    (x : A.subtype) (hx : U (A.isolationSchwartz x) ≠ 0) :
    ∑ i, c i * combModulationCharacter (a i) x = 0 := by
  have h := congrArg (fun T : TemperedDistribution ℝ ℂ => T (A.isolationSchwartz x)) hz
  change (∑ i, c i • combDistributionModulation (a i) : TemperedDistribution ℝ ℂ →L[ℂ]
    TemperedDistribution ℝ ℂ) U (A.isolationSchwartz x) = 0 at h
  simp only [_root_.sum_apply, smul_apply, smul_eq_mul,
    combDistributionModulation_isolation_apply A U (atomicOnCarrier_hasLocallyAtomicAction A U hU),
    ← mul_assoc, ← Finset.sum_mul] at h
  exact (mul_eq_zero.mp h).resolve_right hx

/-- For the actual supports of a broad pair, one bounded-count record
implies finite generation of the opposite module, and produces a nonzero
finite polynomial in exactly that module vanishing on the physical atoms. -/
theorem spectralModule_fg_and_exists_vanishing_exponential_of_unitCellBound
    (A B : LocallyFiniteCarrier) (K : ℕ) (hK : UnitCellBound A K)
    (U : TemperedDistribution ℝ ℂ) (hA : AtomicOnCarrier A U)
    (hB : AtomicOnCarrier B (𝓕 U))
    (hAactual : ∀ x : A.subtype, U (A.isolationSchwartz x) ≠ 0)
    (hBactual : ∀ x : B.subtype, (𝓕 U) (B.isolationSchwartz x) ≠ 0) :
    (AddSubgroup.closure B.carrier).FG ∧
      ∃ (ι : Type) (f : Fintype ι), letI := f
        ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
          (∀ i, a i ∈ AddSubgroup.closure B.carrier) ∧
          (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
          ∀ x ∈ A.carrier, ∑ i, c i * combModulationCharacter (a i) x = 0 := by
  obtain ⟨ι, f, a, c, ha, hfreq, hval, hz⟩ :=
    exists_finiteExponentialAnnihilator_in_module_of_unitCellBound A B K hK
      (AddSubgroup.closure B.carrier) AddSubgroup.subset_closure U hA hB
  let _ := f
  have hc : c ≠ 0 := by
    intro he
    obtain ⟨x, hx⟩ := hval
    exact hx (by simp [he])
  refine ⟨spectralModule_fg_of_finiteExponentialAnnihilator B U hB hBactual a c ha hc hfreq hz,
    ι, f, a, c, ha, hfreq, hval, fun x hx => ?_⟩
  exact finiteExponentialSymbol_eq_zero_of_annihilated_of_nonzero_atom A U hA a c hz
    ⟨x, hx⟩ (hAactual ⟨x, hx⟩)

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
  classical
  let V := DistributionalMeyerPairSpace A B
  let _ : FiniteDimensional ℂ V := finiteDimensional_distributionalMeyerPairSpace_of_unitCellBound A B K hK
  let b := Module.finBasis ℂ V
  let F := (V.map temperedFourierLinearMap)
  let A₀ := atomicSupportUnion A V
  let B₀ := atomicSupportUnion B F
  let row : A.subtype ⊕ B.subtype → V →ₗ[ℂ] ℂ := Sum.elim
    (fun x => (atomicCoefficientLinearMap A x).comp V.subtype)
    (fun y => (atomicCoefficientLinearMap B y).comp (temperedFourierLinearMap.comp V.subtype))
  obtain ⟨t, ht⟩ := exists_generic_linearCombination row b
  let U : V := finiteCombination b t
  have hgeneric {i : A.subtype ⊕ B.subtype} (W : V) (hW : row i W ≠ 0) :
      row i U ≠ 0 := by
    apply (ht i).mpr
    by_contra h
    push Not at h
    apply hW
    rw [← b.sum_repr W, map_sum]
    simp [h]
  have hUA (W : V) : AtomicOnCarrier A (W : TemperedDistribution ℝ ℂ) :=
    ((mem_distributionalMeyerPairSpace_iff A B _).mp W.property).1
  have hUB (W : V) : AtomicOnCarrier B (𝓕 (W : TemperedDistribution ℝ ℂ)) :=
    ((mem_distributionalMeyerPairSpace_iff A B _).mp W.property).2
  have hsmall (W : V) : AtomicOnCarrier A₀ (W : TemperedDistribution ℝ ℂ) :=
    atomicOnCarrier_atomicSupportUnion A V W (hUA W)
  let FU : F := ⟨𝓕 (U : TemperedDistribution ℝ ℂ), ⟨U, U.property, rfl⟩⟩
  have hFsmall : AtomicOnCarrier B₀ (𝓕 (U : TemperedDistribution ℝ ℂ)) :=
    atomicOnCarrier_atomicSupportUnion B F FU (hUB U)
  have hcap : UnitCellBound A₀ K := fun n =>
    (LocallyFiniteCarrier.windowCount_mono_carrier
      (show A₀.carrier ⊆ A.carrier from fun _ ⟨hx, _⟩ => hx) n 1).trans (hK n)
  obtain ⟨ι, fi, a, c, hai, haH, hnonzero, hz⟩ :=
    exists_finiteExponentialAnnihilator_in_module_of_unitCellBound A₀ B₀ K hcap
      (AddSubgroup.closure B₀.carrier) AddSubgroup.subset_closure U (hsmall U) hFsmall
  let _ := fi
  have hBsub : B₀.carrier ⊆ B.carrier := fun _ ⟨hx, _⟩ => hx
  have hBactual (x : B₀.subtype) :
      (𝓕 (U : TemperedDistribution ℝ ℂ)) (B₀.isolationSchwartz x) ≠ 0 := by
    obtain ⟨hx, Y, hY⟩ := x.property
    obtain ⟨W, hW, hWY⟩ := Y.property
    rw [← hWY] at hY
    have h := hgeneric (i := Sum.inr ⟨x, hx⟩) ⟨W, hW⟩ hY
    rw [← isolationAction_eq_of_carrier_subset hBsub _
      (atomicOnCarrier_hasLocallyAtomicAction B₀ _ hFsmall) x]
    exact h
  have hcnz : c ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := hnonzero
    exact hx (by simp [h])
  have hfg := spectralModule_fg_of_finiteExponentialAnnihilator B₀ U hFsmall
    hBactual a c hai hcnz haH hz
  have hzeros (x : ℝ) (hx : x ∈ A₀.carrier) :
      ∑ i, c i * combModulationCharacter (a i) x = 0 := by
    obtain ⟨hxA, W', hW'⟩ := hx
    have hrow := hgeneric (i := Sum.inl ⟨x, hxA⟩) W' hW'
    exact finiteExponentialSymbol_eq_zero_of_annihilated_of_nonzero_atom A U (hUA U)
      a c hz ⟨x, hxA⟩ hrow
  refine ⟨hfg, ι, fi, a, c, hai, haH, hnonzero, hzeros, fun W hW => ?_⟩
  exact finiteExponentialMultiplication_eq_zero A₀ W (hsmall ⟨W, hW⟩) a c hzeros

/-- The common polynomial uses frequencies in the exact module generated by
the spectral support union of the whole original broad pair space. -/
theorem exists_common_finiteExponentialAnnihilator_of_unitCellBound
    (A B : LocallyFiniteCarrier) (K : ℕ) (hK : UnitCellBound A K) :
    let V := DistributionalMeyerPairSpace A B
    let B₀ := atomicSupportUnion B (V.map temperedFourierLinearMap)
    ∃ (ι : Type) (f : Fintype ι), letI := f
      ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
        (∀ i, a i ∈ AddSubgroup.closure B₀.carrier) ∧
        (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
        ∀ U ∈ V, finiteExponentialMultiplication a c U = 0 := by
  obtain ⟨_, ι, fi, a, c, hai, haH, hnonzero, _, hz⟩ :=
    spectralModule_fg_and_exists_common_finiteExponentialAnnihilator_of_unitCellBound A B K hK
  exact ⟨ι, fi, a, c, hai, haH, hnonzero, hz⟩

end

end MeyerGeneralProblem
