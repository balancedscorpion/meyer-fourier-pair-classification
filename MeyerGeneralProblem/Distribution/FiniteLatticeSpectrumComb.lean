module

public import MeyerGeneralProblem.Distribution.NormalizedLatticeSpectrumComb
public import MeyerGeneralProblem.Distribution.LaurentBinomialZeros

@[expose] public section

/-!
# Normalizing finite spectral lattice covers

Within each rational direction, finitely many lines with one chosen step
cover the original lines. Equal Fourier phases represent the same
coset. The normalized count theorem then applies to the original
record on any finite full-lattice spectral cover.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Filter
open scoped BigOperators SchwartzMap FourierTransform

private theorem inverse_step_not_parallel_of_different_directions (a b : ℝ)
    (ha : a ≠ 0) (h : rationalLineDirection a ≠ rationalLineDirection b) :
    a⁻¹ ∉ rationalLineDirection b⁻¹ := by
  intro he
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp he
  have hv := congrArg Inv.inv (show (r : ℝ) * b⁻¹ = a⁻¹ by simpa only [Rat.smul_def] using hr)
  have haref : a ∈ rationalLineDirection b := by
    apply Submodule.mem_span_singleton.mpr
    refine ⟨r⁻¹,?_⟩
    simpa only [Rat.smul_def,Rat.cast_inv,mul_inv,inv_inv] using hv
  exact h (rationalLineDirection_eq_of_mem_ne_zero a b ha haref)

/-- Distinct phases represent precisely the full cosets at the common step. -/
theorem exists_distinct_modes_exact_cover_of_common_step
    (E : Finset (ℝ × ℝ)) (hE : E.Nonempty) (τ : ℝ) (hτ : 0 < τ)
    (hStep : ∀ p ∈ E, p.2 = τ) :
    ∃ modes : List ℝ, modes ≠ [] ∧ modes.Pairwise
      (fun s t => combModulationCharacter (-τ⁻¹) s ≠ combModulationCharacter (-τ⁻¹) t) ∧
      ∀ x, x ∈ (affineLatticeUnionCarrier E).carrier ↔
        ∃ s ∈ modes, ∃ k : ℤ, x = s + (k : ℝ) * (τ⁻¹)⁻¹ := by
  classical
  let phase (s : ℝ) := combModulationCharacter (-τ⁻¹) s
  let phases := E.image fun p => phase p.1
  have hrep (z : phases) : ∃ p ∈ E, phase p.1 = z.val := Finset.mem_image.mp z.property
  choose rep hrepE hPhase using hrep
  let modes := (Finset.univ : Finset (↑phases : Type)).toList.map (fun z => (rep z).1)
  have hmemMode (z : phases) : (rep z).1 ∈ modes :=
    List.mem_map.mpr ⟨z,Finset.mem_toList.mpr (Finset.mem_univ _),rfl⟩
  refine ⟨modes,?_ ,?_ ,?_⟩
  · obtain ⟨p,hp⟩ := hE
    let z : phases := ⟨phase p.1,Finset.mem_image_of_mem _ hp⟩
    intro he
    have h := hmemMode z
    rw [he] at h
    exact List.not_mem_nil h
  · apply List.pairwise_map.mpr
    exact (List.nodup_iff_pairwise_ne.mp (Finset.nodup_toList _)).imp
      (fun {z₁ z₂} hne he => hne (Subtype.ext ((hPhase z₁).symm.trans (he.trans (hPhase z₂)))))
  · intro x
    constructor
    · intro hx
      obtain ⟨p,hp,⟨n,hn⟩⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
      let z : phases := ⟨phase p.1,Finset.mem_image_of_mem _ hp⟩
      have hm : phase p.1 = phase (rep z).1 := (hPhase z).symm
      obtain ⟨k,hk⟩ := (realCharacter_eq_iff_periodic (-τ⁻¹)
        (neg_ne_zero.mpr (inv_ne_zero hτ.ne')) (rep z).1 p.1).mp hm
      refine ⟨(rep z).1,hmemMode z,n-k,?_⟩
      rw [← hn,hStep p hp,hk,inv_inv,div_neg,div_inv_eq_mul]
      push_cast
      ring

    · rintro ⟨s, hs, k, rfl⟩
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hs
      refine (mem_affineLatticeUnionCarrier E _).mpr ⟨rep z, hrepE z, k, ?_⟩
      rw [hStep (rep z) (hrepE z), inv_inv]

/-- A finite union of positive-step affine lattices admits a normalized
reciprocal-class cover. This operation is applied to the spectral
carrier, so every original Fourier coefficient remains literal. -/
theorem exists_normalized_lattice_spectral_cover
    (E : Finset (ℝ × ℝ)) (hStep : ∀ p ∈ E, 0 < p.2) :
    ∃ classes : List (ℝ × List ℝ),
      (∀ p ∈ classes, 0 < p.1) ∧ (∀ p ∈ classes, p.2 ≠ []) ∧
      (∀ p ∈ classes, p.2.Pairwise
        (fun s t => combModulationCharacter (-p.1) s ≠ combModulationCharacter (-p.1) t)) ∧
      classes.Pairwise (fun p q => p.1 ∉ rationalLineDirection q.1) ∧
      ∀ x ∈ (affineLatticeUnionCarrier E).carrier, ∃ p ∈ classes, ∃ s ∈ p.2, ∃ k : ℤ,
        x = s + (k : ℝ) * p.1⁻¹ := by
  classical
  let D := E.image fun p => rationalLineDirection p.2
  have hreps (i : D) : ∃ p ∈ E, rationalLineDirection p.2 = i.val := Finset.mem_image.mp i.property
  choose rep hRep hDir using hreps
  let τ (i : D) := (rep i).2
  have hτ (i : D) : 0 < τ i := hStep (rep i) (hRep i)
  let E₀ (i : D) := E.filter fun p => rationalLineDirection p.2 = i.val
  have hOne (i : D) : ∃ modes : List ℝ, modes ≠ [] ∧ modes.Pairwise
      (fun s t => combModulationCharacter (-(τ i)⁻¹) s ≠ combModulationCharacter (-(τ i)⁻¹) t) ∧
      ∀ x ∈ (affineLatticeUnionCarrier (E₀ i)).carrier,
        ∃ s ∈ modes, ∃ k : ℤ, x = s + (k : ℝ) * ((τ i)⁻¹)⁻¹ := by
    obtain ⟨F,hF,hRef⟩ := exists_affineLatticeUnion_refinement_of_rationalLineDirection (E₀ i) (τ i)
      (fun p hp => by
        have hp' := (Finset.mem_filter.mp hp).2
        rw [show rationalLineDirection (τ i) = i.val from hDir i, ← hp']
        exact Submodule.mem_span_singleton_self p.2)
    have hbase : (rep i).1 ∈ (affineLatticeUnionCarrier (E₀ i)).carrier :=
      (mem_affineLatticeUnionCarrier _ _).mpr
        ⟨rep i,Finset.mem_filter.mpr ⟨hRep i,hDir i⟩,⟨0,by simp⟩⟩
    obtain ⟨p,hp,_⟩ := (mem_affineLatticeUnionCarrier F _).mp (hRef hbase)
    obtain ⟨modes,hN,hM,hC⟩ := exists_distinct_modes_exact_cover_of_common_step F ⟨p,hp⟩
      (τ i) (hτ i) hF
    exact ⟨modes,hN,hM,fun x hx => (hC x).mp (hRef hx)⟩
  choose modes hModesN hModesDistinct hC using hOne
  let cls (i : D) : ℝ × List ℝ := ((τ i)⁻¹,modes i)
  let classes := (Finset.univ : Finset (↑D : Type)).toList.map cls
  have hcls (i : D) : cls i ∈ classes :=
    List.mem_map.mpr ⟨i,Finset.mem_toList.mpr (Finset.mem_univ _),rfl⟩
  refine ⟨classes, ?_,?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact inv_pos.mpr (hτ i)
  · intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact hModesN i
  · intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact hModesDistinct i
  · apply List.pairwise_map.mpr
    apply (List.nodup_iff_pairwise_ne.mp (Finset.nodup_toList _)).imp
    intro i j hij
    apply inverse_step_not_parallel_of_different_directions _ _ (hτ i).ne'
    intro he
    exact hij (Subtype.ext ((hDir i).symm.trans (he.trans (hDir j))))
  · intro x hx
    obtain ⟨p,hp,hx⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
    let i : D := ⟨rationalLineDirection p.2,Finset.mem_image_of_mem _ hp⟩
    have hx₁ := (mem_affineLatticeUnionCarrier (E₀ i) x).mpr
      ⟨p,Finset.mem_filter.mpr ⟨hp,rfl⟩,hx⟩
    obtain ⟨s,hs,k,hk⟩ := hC i x hx₁
    exact ⟨cls i,hcls i,s,hs,k,hk⟩

/-- Vanishing quadratic lower count and a finite lattice cover of the
opposite record give a whole finite modulated comb sum. -/
theorem exists_finite_spectralClassCombSum_of_finite_lattice_spectral_cover
    (A B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier A T) (hFT : AtomicOnCarrier B (𝓕 T))
    (E : Finset (ℝ × ℝ)) (hStep : ∀ p ∈ E, 0 < p.2)
    (hE : B.carrier ⊆ (affineLatticeUnionCarrier E).carrier)
    (hcount : ∀ e : ℝ, 0 < e → ∃ᶠ R : ℝ in atTop,
      ((A.carrier ∩ Icc (-R) R).ncard : ℝ) < e * R ^ 2) :
    ∃ classes : List (ℝ × List ℝ), IsFiniteSpectralClassCombSum classes T := by
  obtain ⟨classes,hpos,hN,hM,hsep,hcover⟩ := exists_normalized_lattice_spectral_cover E hStep
  exact ⟨classes,isFiniteSpectralClassCombSum_of_normalized_lattice_spectrum
    classes hpos hN hM hsep A B T hT hFT (fun x hx => hcover x (hE hx)) hcount⟩

end
end MeyerGeneralProblem
