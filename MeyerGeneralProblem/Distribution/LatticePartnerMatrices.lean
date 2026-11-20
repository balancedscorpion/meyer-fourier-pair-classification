module

public import MeyerGeneralProblem.Distribution.LatticeOrbitResidueRows
public import MeyerGeneralProblem.Distribution.LatticePartnerDecomposition

@[expose] public section

/-!
# Finite residue matrices on normalized partner classes

Exact full-coset representatives and the reduced ratio of two
reciprocal periods put the original carriers in the domain of the
paired orbit matrix.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators FourierTransform SchwartzMap

/-- Exact representatives of a full union of cosets at one period. -/
theorem exists_latticeOrbitUnion_eq_of_common_step (E : Finset (ℝ × ℝ))
    (w : ℝ) (hw : 0 < w) (hE : ∀ p ∈ E, p.2 = w) :
    ∃ modes : List ℝ, modes.Pairwise
      (fun s t => combModulationCharacter (-w⁻¹) s ≠ combModulationCharacter (-w⁻¹) t) ∧
      latticeOrbitUnion w modes.get = affineLatticeUnionCarrier E := by
  classical
  by_cases h : E.Nonempty
  · obtain ⟨modes, _, hd, hset⟩ := exists_distinct_modes_exact_cover_of_common_step E h w hw hE
    refine ⟨modes, hd, LocallyFiniteCarrier.ext ?_⟩
    ext x
    rw [mem_latticeOrbitUnion, hset]
    constructor
    · rintro ⟨j, k, hk⟩
      exact ⟨modes.get j, List.get_mem _ _, k, by simpa only [inv_inv] using hk.symm⟩
    · rintro ⟨s, hs, k, hk⟩
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hs
      exact ⟨j, k, by simpa only [inv_inv] using hk.symm⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    refine ⟨[], by simp, LocallyFiniteCarrier.ext ?_⟩
    ext x
    simp [mem_latticeOrbitUnion, mem_affineLatticeUnionCarrier]

/-- Positive commensurate periods give the reduced positive integer ratio. -/
theorem exists_coprime_lattice_period_relation (a w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hD : rationalLineDirection a = rationalLineDirection w) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ p.Coprime q ∧ (q : ℝ) * a = (p : ℝ) * w := by
  have hmem : a ∈ rationalLineDirection w := hD ▸ Submodule.mem_span_singleton_self a
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
  have hre : a = (r : ℝ) * w := by simpa only [Rat.smul_def] using hr.symm
  have hrpos : 0 < r := by
    have h : (0 : ℝ) < r := by
      by_contra! hn
      exact ha.not_ge (hre ▸ mul_nonpos_of_nonpos_of_nonneg hn hw.le)
    exact_mod_cast h
  have hnum := Rat.num_pos.mpr hrpos
  have hn : (r.num.natAbs : ℤ) = r.num := Int.natAbs_of_nonneg hnum.le
  have hnpos : 0 < r.num.natAbs := Int.natAbs_pos.mpr hnum.ne'
  refine ⟨r.num.natAbs, r.den, hnpos, r.pos, r.reduced, ?_⟩
  have hcast : (r.num.natAbs : ℝ) = (r.num : ℝ) := by
    rw [← Int.cast_natCast, hn]
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  rw [hre, Rat.cast_def, hcast]
  field_simp

/-- The local finite matrix applies directly to a normalized physical
and reciprocal spectral class. -/
theorem exists_latticeClassPair_residueEquiv_of_common_steps
    (A B : Finset (ℝ × ℝ)) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hA : ∀ p ∈ A, p.2 = a) (hB : ∀ p ∈ B, p.2 = b)
    (hD : rationalLineDirection a = rationalLineDirection b⁻¹) :
    ∃ (physicalModes modes : List ℝ) (p q : ℕ),
      0 < p ∧ 0 < q ∧ p.Coprime q ∧ (q : ℝ) * a = (p : ℝ) * b⁻¹ ∧
      physicalModes.Pairwise
        (fun s t => combModulationCharacter (-a⁻¹) s ≠ combModulationCharacter (-a⁻¹) t) ∧
      modes.Pairwise
        (fun s t => combModulationCharacter (-b⁻¹) s ≠ combModulationCharacter (-b⁻¹) t) ∧
      (∀ v : ℝ, v ∈ (affineLatticeUnionCarrier A).carrier ↔
        ∃ j : Fin physicalModes.length, v ∈ affineLatticeLine (physicalModes.get j) a) ∧
      (∀ v : ℝ, v ∈ (affineLatticeUnionCarrier B).carrier ↔
        ∃ j : Fin modes.length, v ∈ affineLatticeLine (modes.get j) b) ∧
      ∃ (κ : Type) (f : Fintype κ), letI := f
        ∃ y : κ → ℝ, Fintype.card κ ≤ q * physicalModes.length ∧
          (∀ i, y i ∈ (affineLatticeUnionCarrier A).carrier) ∧
          (affineLatticeUnionCarrier A).carrier ⊆ (latticeOrbitUnion b⁻¹ y).carrier ∧
          (Pairwise fun i j => Disjoint (affineLatticeLine (y i) b⁻¹)
            (affineLatticeLine (y j) b⁻¹)) ∧
          ∃ e : LinearMap.ker (latticeOrbitResidueRows (affineLatticeUnionCarrier A) b⁻¹ y modes p)
              ≃ₗ[ℂ] DistributionalMeyerPairSpace (affineLatticeUnionCarrier A)
                (affineLatticeUnionCarrier B),
            ∀ c, (e c : TemperedDistribution ℝ ℂ) =
              latticeOrbitSynthesis b⁻¹ (inv_pos.mpr hb) y modes c := by
  obtain ⟨physicalModes, haModes, hAeq⟩ := exists_latticeOrbitUnion_eq_of_common_step A a ha hA
  obtain ⟨modes, hd, hBeq⟩ := exists_latticeOrbitUnion_eq_of_common_step B b hb hB
  obtain ⟨p, q, hp, hq, hcop, hper⟩ := exists_coprime_lattice_period_relation a b⁻¹ ha
    (inv_pos.mpr hb) hD
  obtain ⟨κ, f, y, hcard, hCenter, hCover, hDisj, e, he⟩ := exists_pairedLatticeClass_residueEquiv
    a b⁻¹ (inv_pos.mpr hb) physicalModes.get modes hd p q hp hq hper
  let _ := f
  have hFin : Fintype.card κ ≤ q * physicalModes.length := by simpa only [Fintype.card_fin] using hcard
  let K := LinearMap.ker (latticeOrbitResidueRows (affineLatticeUnionCarrier A) b⁻¹ y modes p)
  let K₀ := LinearMap.ker
    (latticeOrbitResidueRows (latticeOrbitUnion a physicalModes.get) b⁻¹ y modes p)
  have hK : K = K₀ := by dsimp only [K, K₀]; rw [hAeq]
  have hv : DistributionalMeyerPairSpace (latticeOrbitUnion a physicalModes.get)
      (latticeOrbitUnion (b⁻¹)⁻¹ modes.get) =
      DistributionalMeyerPairSpace (affineLatticeUnionCarrier A) (affineLatticeUnionCarrier B) := by
    rw [hAeq, inv_inv, hBeq]
  let ei := LinearEquiv.ofEq K K₀ hK
  let eo := LinearEquiv.ofEq _ _ hv
  refine ⟨physicalModes, modes, p, q, hp, hq, hcop, hper, haModes, hd, ?_, ?_, κ, f, y, hFin,
    (fun i => hAeq ▸ hCenter i), hAeq ▸ hCover, hDisj, ei.trans (e.trans eo), ?_⟩
  · intro v
    rw [← hAeq, mem_latticeOrbitUnion]
  · intro v
    rw [← hBeq, mem_latticeOrbitUnion]
  · intro c
    change ((e (ei c) : TemperedDistribution ℝ ℂ)) = _
    rw [he]
    rfl

/-- The original ordered partner space has a complete finite residue
matrix whenever both of its direction classes are present. The periods
here generate the exact intersections in the original lattice data. -/
theorem exists_latticePartnerPairSpace_residueEquiv
    (E F : Finset (ℝ × ℝ)) (hE : ∀ v ∈ E, 0 < v.2) (hF : ∀ v ∈ F, 0 < v.2)
    (w : ℝ) (hP : (latticeDirectionClass E (rationalLineDirection w)).Nonempty)
    (hQ : (latticeDirectionClass F (rationalLineDirection w⁻¹)).Nonempty) :
    let P := latticeDirectionClass E (rationalLineDirection w)
    let Q := latticeDirectionClass F (rationalLineDirection w⁻¹)
    ∃ (a b : ℝ) (_ : 0 < a) (hb : 0 < b) (physicalModes modes : List ℝ) (p q : ℕ),
      0 < p ∧ 0 < q ∧ p.Coprime q ∧ (q : ℝ) * a = (p : ℝ) * b⁻¹ ∧
      AddSubgroup.zmultiples a = (⨅ v : P.image Prod.snd, AddSubgroup.zmultiples v.val) ∧
      AddSubgroup.zmultiples b = (⨅ v : Q.image Prod.snd, AddSubgroup.zmultiples v.val) ∧
      physicalModes.Pairwise
        (fun s t => combModulationCharacter (-a⁻¹) s ≠ combModulationCharacter (-a⁻¹) t) ∧
      modes.Pairwise
        (fun s t => combModulationCharacter (-b⁻¹) s ≠ combModulationCharacter (-b⁻¹) t) ∧
      (∀ v : ℝ, v ∈ (affineLatticeUnionCarrier P).carrier ↔
        ∃ j : Fin physicalModes.length, v ∈ affineLatticeLine (physicalModes.get j) a) ∧
      (∀ v : ℝ, v ∈ (affineLatticeUnionCarrier Q).carrier ↔
        ∃ j : Fin modes.length, v ∈ affineLatticeLine (modes.get j) b) ∧
      ∃ (κ : Type) (f : Fintype κ), letI := f
        ∃ y : κ → ℝ, Fintype.card κ ≤ q * physicalModes.length ∧
          (∀ i, y i ∈ (affineLatticeUnionCarrier P).carrier) ∧
          (affineLatticeUnionCarrier P).carrier ⊆ (latticeOrbitUnion b⁻¹ y).carrier ∧
          (Pairwise fun i j => Disjoint (affineLatticeLine (y i) b⁻¹)
            (affineLatticeLine (y j) b⁻¹)) ∧
          ∃ e : LinearMap.ker (latticeOrbitResidueRows (affineLatticeUnionCarrier P) b⁻¹ y modes p)
              ≃ₗ[ℂ] latticePartnerPairSpace E F w,
            ∀ c, (e c : TemperedDistribution ℝ ℂ) =
              latticeOrbitSynthesis b⁻¹ (inv_pos.mpr hb) y modes c := by
  classical
  let P := latticeDirectionClass E (rationalLineDirection w)
  let Q := latticeDirectionClass F (rationalLineDirection w⁻¹)
  obtain ⟨u, hu⟩ := hP
  obtain ⟨v, hv⟩ := hQ
  have huD := (mem_latticeDirectionClass _ _ _).mp hu
  have hvD := (mem_latticeDirectionClass _ _ _).mp hv
  have hPref (x : ℝ × ℝ) (hx : x ∈ P) : 0 < x.2 ∧ x.2 ∈ rationalLineDirection u.2 := by
    obtain ⟨hxE, hxD⟩ := (mem_latticeDirectionClass _ _ _).mp hx
    exact ⟨hE x hxE, (hxD.trans huD.2.symm) ▸ Submodule.mem_span_singleton_self _⟩
  have hQref (x : ℝ × ℝ) (hx : x ∈ Q) : 0 < x.2 ∧ x.2 ∈ rationalLineDirection v.2 := by
    obtain ⟨hxF, hxD⟩ := (mem_latticeDirectionClass _ _ _).mp hx
    exact ⟨hF x hxF, (hxD.trans hvD.2.symm) ▸ Submodule.mem_span_singleton_self _⟩
  obtain ⟨a, A, ha, haD, haGen, hA, hAeq⟩ := exists_exact_common_period_lattice_refinement
    P u.2 (hE u huD.1) (Finset.mem_image_of_mem _ hu) hPref
  obtain ⟨b, B, hb, hbD, hbGen, hB, hBeq⟩ := exists_exact_common_period_lattice_refinement
    Q v.2 (hF v hvD.1) (Finset.mem_image_of_mem _ hv) hQref
  have hbInv : rationalLineDirection b⁻¹ = rationalLineDirection w := by
    simpa only [inv_inv] using
      (rationalLineDirection_inv_eq_iff hb.ne').mpr (hbD.trans hvD.2)
  obtain ⟨physicalModes, modes, p, q, hp, hq, hc, hrel, haModes, hbModes, hPhysical, hSpectral,
      κ, f, y, hcard, hCenter, hCover, hDisj, e, he⟩ :=
    exists_latticeClassPair_residueEquiv_of_common_steps A B a b ha hb hA hB
      (haD.trans (huD.2.trans hbInv.symm))
  let _ := f
  have hPcar := LocallyFiniteCarrier.ext hAeq
  have hQcar := LocallyFiniteCarrier.ext hBeq
  have hK : LinearMap.ker (latticeOrbitResidueRows (affineLatticeUnionCarrier P) b⁻¹ y modes p) =
      LinearMap.ker (latticeOrbitResidueRows (affineLatticeUnionCarrier A) b⁻¹ y modes p) := by
    rw [hPcar]
  have hV : DistributionalMeyerPairSpace (affineLatticeUnionCarrier A) (affineLatticeUnionCarrier B) =
      latticePartnerPairSpace E F w := by
    rw [latticePartnerPairSpace, hPcar, hQcar]
  let ei := LinearEquiv.ofEq _ _ hK
  let eo := LinearEquiv.ofEq _ _ hV
  refine ⟨a, b, ha, hb, physicalModes, modes, p, q, hp, hq, hc, hrel, haGen, hbGen,
    haModes, hbModes, ?_, ?_, κ, f, y, hcard, (fun i => hPcar ▸ hCenter i),
    hPcar ▸ hCover, hDisj, ei.trans (e.trans eo), ?_⟩
  · intro x
    rw [← hAeq]
    exact hPhysical x
  · intro x
    rw [← hBeq]
    exact hSpectral x
  · intro c
    change (e (ei c) : TemperedDistribution ℝ ℂ) = _
    rw [he]
    rfl

end
end MeyerGeneralProblem
