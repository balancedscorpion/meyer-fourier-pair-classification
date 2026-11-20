module

public import MeyerGeneralProblem.Distribution.BilateralCombResidues
public import MeyerGeneralProblem.Distribution.CombCoefficientReconstruction
public import MeyerGeneralProblem.Distribution.LeastLatticeEnvelope

@[expose] public section

/-!
# Cofinite support of a common-direction comb sum

A common integer multiple of the original periods tiles every original
lattice by whole residue cosets. On each coset, the literal net coefficient
is a bilateral power sum, with every contributing original term retained.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators

/-- A positive integer multiple step splits the original lattice into
finitely many whole cosets of that step, with exact equality. -/
theorem exists_exact_lattice_refinement_of_integer_multiple (y w d : ℝ)
    (hw : 0 < w) (hd : 0 < d) (hdiv : d ∈ AddSubgroup.zmultiples w) :
    ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, p.2 = d) ∧
      (affineLatticeUnionCarrier E).carrier = affineLatticeLine y w := by
  classical
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hdiv
  rw [zsmul_eq_mul] at hm
  have hmpos : 0 < m := by
    by_contra! h
    have hm' : (m : ℝ) ≤ 0 := by exact_mod_cast h
    exact (not_lt_of_ge (hm ▸ mul_nonpos_of_nonpos_of_nonneg hm' hw.le)) hd
  let M := m.toNat
  have hM : (M : ℤ) = m := Int.toNat_of_nonneg hmpos.le
  have hMpos : 0 < M := by exact_mod_cast (hM.symm ▸ hmpos)
  let _ : NeZero M := ⟨hMpos.ne'⟩
  let split := Int.divModEquiv M
  let p (i : Fin M) := (y + (i.val : ℝ) * w, d)
  let E := Finset.univ.image p
  refine ⟨E, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    rfl
  · ext x
    constructor
    · intro hx
      obtain ⟨z, hz, hx⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact affineLatticeLine_subprogression (show (p i).1 ∈ affineLatticeLine y w from
        ⟨(i.val : ℤ), by simp [p]⟩) hdiv hx
    · rintro ⟨n, rfl⟩
      let i := (split n).2
      let j := (split n).1
      have hn : j * (M : ℤ) + (i.val : ℤ) = n := split.symm_apply_apply n
      refine (mem_affineLatticeUnionCarrier E _).mpr
        ⟨p i, Finset.mem_image_of_mem p (Finset.mem_univ i), j, ?_⟩
      change y + (i.val : ℝ) * w + (j : ℝ) * d = y + (n : ℝ) * w
      rw [← hn, hM, ← hm]
      push_cast
      ring

/-- The exact coefficient function before or after directional grouping. -/
def affineCombCoefficients {ι : Type*} [Fintype ι]
    (q : ι → AffineCombTerm) (w : ι → ℝ) (x : ℝ) : ℂ :=
  ∑ i, (q i).coefficientFunction (w i) x

theorem affineCombCoefficients_on_common_step
    {ι : Type*} [Fintype ι] (q : ι → AffineCombTerm) (w : ι → ℝ)
    (y d : ℝ) (hdiv : ∀ i, d ∈ AddSubgroup.zmultiples (w i)) :
    ∃ c z : ι → ℂ, (∀ i, z i ≠ 0) ∧
      ∀ n : ℤ, affineCombCoefficients q w (y + (n : ℝ) * d) = integerPowerSum c z n := by
  classical
  let c (i : ι) := (q i).coefficientFunction (w i) y
  let z (i : ι) := combModulationCharacter (q i).frequency d
  refine ⟨c, z, fun i => norm_pos_iff.mp (by rw [show z i = _ from rfl, norm_combModulationCharacter]; norm_num), ?_⟩
  intro n
  unfold affineCombCoefficients integerPowerSum
  apply Finset.sum_congr rfl
  intro i _
  let L := affineLatticeLine (q i).origin (w i)
  have hpoint : y + (n : ℝ) * d ∈ affineLatticeLine y d := ⟨n, rfl⟩
  by_cases hy : y ∈ L
  · have hn : y + (n : ℝ) * d ∈ L := affineLatticeLine_subprogression hy (hdiv i) hpoint
    dsimp [L] at hy hn
    simp only [c, z, AffineCombTerm.coefficientFunction, indicator_of_mem hy, indicator_of_mem hn,
      combModulationCharacter_on_integer_affine, mul_assoc]
  · have hn : y + (n : ℝ) * d ∉ L := not_mem_of_mem_subprogression hy (hdiv i) hpoint
    dsimp [L] at hy hn
    simp only [c, AffineCombTerm.coefficientFunction, indicator_of_notMem hy, indicator_of_notMem hn, zero_mul]

/-- A finite family of cofinite covers combines by taking the actual union
of their lines. The same spacing condition holds on all constituent lines. -/
theorem exists_lattice_cover_iUnion
    {ι : Type*} [Fintype ι] (X : ι → Set ℝ) (r : ℝ → Prop)
    (hX : ∀ i, ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, r p.2) ∧
      X i ⊆ (affineLatticeUnionCarrier E).carrier ∧
      ((affineLatticeUnionCarrier E).carrier \ X i).Finite) :
    ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, r p.2) ∧
      (⋃ i, X i) ⊆ (affineLatticeUnionCarrier E).carrier ∧
      ((affineLatticeUnionCarrier E).carrier \ ⋃ i, X i).Finite := by
  classical
  choose F hstep hcover hfin using hX
  let E := Finset.univ.biUnion F
  refine ⟨E, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hp
    exact hstep i p hpi
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    obtain ⟨p, hp, hxp⟩ := (mem_affineLatticeUnionCarrier (F i) x).mp (hcover i hxi)
    exact (mem_affineLatticeUnionCarrier E x).mpr
      ⟨p, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hp⟩, hxp⟩
  · apply (Set.finite_iUnion hfin).subset
    rintro x ⟨hx, hout⟩
    obtain ⟨p, hp, hxp⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
    obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hp
    exact mem_iUnion.mpr ⟨i, (mem_affineLatticeUnionCarrier (F i) x).mpr ⟨p, hpi, hxp⟩,
      fun hi => hout (mem_iUnion.mpr ⟨i, hi⟩)⟩

/-- Conditional only on the scalar zero-set theorem, a finite comb family
with a common integer multiple of its periods has exact cofinite support. -/
theorem exists_cofinite_cover_affineCombCoefficients_of_common_step
    (hscalar : BilateralPowerSumCofiniteSupport)
    {ι : Type} [Fintype ι] (q : ι → AffineCombTerm) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (d : ℝ) (hd : 0 < d)
    (hdiv : ∀ i, d ∈ AddSubgroup.zmultiples (w i)) :
    ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, 0 < p.2 ∧ rationalLineDirection p.2 = rationalLineDirection d) ∧
      Function.support (affineCombCoefficients q w) ⊆ (affineLatticeUnionCarrier E).carrier ∧
      ((affineLatticeUnionCarrier E).carrier \ Function.support (affineCombCoefficients q w)).Finite := by
  classical
  have hrefine (i : ι) := exists_exact_lattice_refinement_of_integer_multiple
    (q i).origin (w i) d (hw i) hd (hdiv i)
  choose F hstep hline using hrefine
  let K := Finset.univ.biUnion F
  let f := affineCombCoefficients q w
  let X (p : K) := Function.support f ∩ affineLatticeLine p.val.1 d
  have hsubset : Function.support f ⊆ (affineLatticeUnionCarrier K).carrier := by
    intro x hx
    by_contra hout
    apply hx
    unfold f affineCombCoefficients
    apply Finset.sum_eq_zero
    intro i _
    have hnot : x ∉ affineLatticeLine (q i).origin (w i) := by
      intro h
      rw [← hline i] at h
      obtain ⟨v, hv, hxv⟩ := (mem_affineLatticeUnionCarrier (F i) x).mp h
      exact hout ((mem_affineLatticeUnionCarrier K x).mpr
        ⟨v, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hv⟩, hxv⟩)
    simp only [AffineCombTerm.coefficientFunction, indicator_of_notMem hnot]
  have heq : Function.support f = ⋃ p : K, X p := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp, hxp⟩ := (mem_affineLatticeUnionCarrier K x).mp (hsubset hx)
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
      rw [hstep i p hi] at hxp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, hx, hxp⟩
    · intro hx
      obtain ⟨p, hxp⟩ := mem_iUnion.mp hx
      exact hxp.1
  have hc (p : K) :
      ∃ E : Finset (ℝ × ℝ), (∀ v ∈ E, 0 < v.2 ∧ rationalLineDirection v.2 = rationalLineDirection d) ∧
        X p ⊆ (affineLatticeUnionCarrier E).carrier ∧ ((affineLatticeUnionCarrier E).carrier \ X p).Finite := by
    obtain ⟨c, z, hz, hvalues⟩ := affineCombCoefficients_on_common_step q w p.val.1 d hdiv
    obtain ⟨a, m, R, hm, hs, hf⟩ := hscalar ι c z hz
    have himage : (fun n : ℤ => p.val.1 + (n : ℝ) * d) '' Function.support (integerPowerSum c z) = X p := by
      ext x
      constructor
      · rintro ⟨n, hn, rfl⟩
        refine ⟨?_, n, rfl⟩
        change affineCombCoefficients q w (p.val.1 + (n : ℝ) * d) ≠ 0
        rw [hvalues]
        exact hn
      · rintro ⟨hx, n, rfl⟩
        refine ⟨n, ?_, rfl⟩
        change integerPowerSum c z n ≠ 0
        rw [← hvalues]
        exact hx
    rw [← himage]
    exact exists_lattice_cover_of_integer_residue_support _ _ _ _ hm hs hf p.val.1 d hd
  rw [heq]
  exact exists_lattice_cover_iUnion X (fun t => 0 < t ∧ rationalLineDirection t = rationalLineDirection d) hc

end
end MeyerGeneralProblem
