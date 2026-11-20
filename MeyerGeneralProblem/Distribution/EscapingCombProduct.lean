module

public import MeyerGeneralProblem.Distribution.EscapingCombIntegral
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# An exact right inverse for the class-eliminating translation product

Lagrange interpolation combines the actual outgoing quadrant integrals.
All phases in one product have the same physical shift. The input comb
may have a different shift.
-/

namespace MeyerGeneralProblem

noncomputable section

open Polynomial
open scoped BigOperators SchwartzMap

private abbrev TranslationEnd := Module.End ℂ (TemperedDistribution ℝ ℂ)

private def translationPolynomial (w : ℝ) (modes : List ℝ) : ℂ[X] :=
  (modes.map fun s => X - C (combModulationCharacter (-w) s)).prod

private theorem translationFactor_aeval (w s : ℝ) :
    Polynomial.aeval ((combDistributionTranslation w).toLinearMap : TranslationEnd)
      (X - C (combModulationCharacter (-w) s)) = combTranslationFactor w s := by
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  rfl

private theorem translationFactors_aeval (w : ℝ) (modes : List ℝ) :
    Polynomial.aeval ((combDistributionTranslation w).toLinearMap : TranslationEnd)
      (translationPolynomial w modes) = combTranslationFactors w modes := by
  induction modes with
  | nil => simp only [translationPolynomial, List.map_nil, List.prod_nil, map_one]; rfl
  | cons s modes ih =>
      change Polynomial.aeval ((combDistributionTranslation w).toLinearMap : TranslationEnd)
        ((X - C (combModulationCharacter (-w) s)) * translationPolynomial w modes) = _
      rw [mul_comm, map_mul, ih, translationFactor_aeval]
      rfl

private theorem phases_injOn (w : ℝ) (modes : List ℝ)
    (hdistinct : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t)) :
    Set.InjOn (combModulationCharacter (-w)) (modes.toFinset : Set ℝ) := by
  intro s hs t ht he
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hs)
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp ht)
  rcases lt_trichotomy i j with hlt | h | hgt
  · exact (List.pairwise_iff_get.mp hdistinct i j hlt he).elim
  · rw [h]
  · exact (List.pairwise_iff_get.mp hdistinct j i hgt he.symm).elim

/-- The actual finite Lagrange combination of the two outgoing quadrants
for each phase of the specified class. -/
def escapingCombProductIntegral (q : AffineCombTerm) (a w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (modes : List ℝ) : TemperedDistribution ℝ ℂ := by
  classical
  exact ∑ s ∈ modes.toFinset, Lagrange.nodalWeight modes.toFinset (combModulationCharacter (-w)) s •
    escapingCombIntegral q a w ha hw s

/-- Every term has the same two quadrant containers, regardless of phase. -/
theorem escapingCombProductIntegral_atomicOnCarrier (q : AffineCombTerm) (a w : ℝ)
    (ha : 0 < a) (hw : 0 < w) (modes : List ℝ) :
    AtomicOnCarrier (escapingCombIntegralCarrier q.origin a w ha hw)
      (escapingCombProductIntegral q a w ha hw modes) := by
  intro f hf
  simp only [escapingCombProductIntegral, _root_.sum_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro s _
  rw [escapingCombIntegral_atomicOnCarrier q a w ha hw s f hf, mul_zero]

/-- On each original comb summand, the complete class-eliminating product
has the explicit outgoing right inverse. -/
theorem combTranslationFactors_escapingCombProductIntegral (q : AffineCombTerm) (a w : ℝ)
    (ha : 0 < a) (hw : 0 < w) (modes : List ℝ) (h_nonempty : modes ≠ [])
    (hdistinct : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t)) :
    combTranslationFactors w modes (escapingCombProductIntegral q a w ha hw modes) =
      q.distribution a ha := by
  classical
  let E := modes.toFinset
  let v := combModulationCharacter (-w)
  let eval : ℂ[X] →ₐ[ℂ] TranslationEnd :=
    Polynomial.aeval (combDistributionTranslation w).toLinearMap
  have hE : E.Nonempty := by
    cases modes with
    | nil => exact (h_nonempty rfl).elim
    | cons s modes => exact ⟨s, List.mem_toFinset.mpr List.mem_cons_self⟩
  have hlist : modes.Nodup := List.nodup_iff_pairwise_ne.mpr
    (hdistinct.imp fun h he => h (congrArg v he))
  have hnodal : Lagrange.nodal E v = translationPolynomial w modes := by
    simp only [Lagrange.nodal, translationPolynomial, E, v, List.prod_toFinset _ hlist]
  have hproduct : combTranslationFactors w modes = eval (Lagrange.nodal E v) := by
    rw [hnodal]
    exact (translationFactors_aeval w modes).symm
  have hLag :
      (∑ s ∈ E, C (Lagrange.nodalWeight E v s) * Lagrange.nodal (E.erase s) v) = 1 := by
    calc
      _ = ∑ s ∈ E, Lagrange.basis E v s := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hs,
          Lagrange.nodal_erase_eq_nodal_div hs]
      _ = 1 := Lagrange.sum_basis (phases_injOn w modes hdistinct) hE
  change combTranslationFactors w modes
    (∑ s ∈ E, Lagrange.nodalWeight E v s • escapingCombIntegral q a w ha hw s) = _
  rw [hproduct, map_sum]
  calc
    _ = ∑ s ∈ E, eval (C (Lagrange.nodalWeight E v s) *
        Lagrange.nodal (E.erase s) v) (q.distribution a ha) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [map_smul, Lagrange.nodal_eq_mul_nodal_erase hs,
        mul_comm (X - C (v s))]
      change Lagrange.nodalWeight E v s •
        (eval (Lagrange.nodal (E.erase s) v * (X - C (v s))))
          (escapingCombIntegral q a w ha hw s) = _
      rw [map_mul, Module.End.mul_apply]
      have hfactor : eval (X - C (v s)) = combTranslationFactor w s :=
        translationFactor_aeval w s
      rw [hfactor, combTranslationFactor_escapingCombIntegral]
      simp only [map_mul, Module.End.mul_apply, eval, Polynomial.aeval_C]
      rfl
    _ = q.distribution a ha := by
      rw [← LinearMap.sum_apply, ← map_sum, hLag, map_one]
      rfl

/-- Exact mixed-period decomposition when the class-eliminated record has
already been expanded into affine combs. The correction in the original
class again uses only value-only atomic action of the physical record. -/
theorem exists_quadrant_comb_decomposition_of_combTranslationFactors
    {ι : Type*} [Fintype ι] (q : ι → AffineCombTerm) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (w : ℝ) (hw : 0 < w) (modes : List ℝ) (h_nonempty : modes ≠ [])
    (hdistinct : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t))
    (hD : combTranslationFactors w modes T = ∑ i, (q i).distribution (a i) (ha i)) :
    ∃ terms : List AffineCombTerm,
      T = (∑ i, escapingCombProductIntegral (q i) (a i) w (ha i) hw modes) +
        affineCombTermSum w hw terms ∧ ∀ t ∈ terms, t.frequency ∈ modes := by
  let Q := ∑ i, escapingCombProductIntegral (q i) (a i) w (ha i) hw modes
  let S : ι → LocallyFiniteCarrier := fun i =>
    escapingCombIntegralCarrier (q i).origin (a i) w (ha i) hw
  let C : LocallyFiniteCarrier :=
    { carrier := ⋃ i, (S i).carrier
      finite_inter_Icc := fun l r => by
        rw [Set.iUnion_inter]
        exact Set.finite_iUnion fun i => (S i).finite_inter_Icc l r }
  have hQ : AtomicOnCarrier C Q := by
    intro f hf
    simp only [Q, _root_.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    exact escapingCombProductIntegral_atomicOnCarrier (q i) (a i) w (ha i) hw modes f
      (fun x hx => hf x (Set.mem_iUnion.mpr ⟨i, hx⟩))
  have hCQ : AtomicOnCarrier (A.union C) (T - Q) := by
    intro f hf
    simp only [sub_apply]
    rw [hT f (fun x hx => hf x (Or.inl hx)), hQ f (fun x hx => hf x (Or.inr hx)), sub_self]
  have hzero : combTranslationFactors w modes (T - Q) = 0 := by
    rw [map_sub, hD]
    simp only [Q, map_sum, combTranslationFactors_escapingCombProductIntegral _ _ _ _ _
      _ h_nonempty hdistinct, sub_self]
  obtain ⟨terms, hterms, hfreq⟩ :=
    exists_affineCombTermSum_of_combTranslationFactors_eq_zero w hw modes hdistinct
      (A.union C) (T - Q) hCQ hzero
  refine ⟨terms, ?_, hfreq⟩
  rw [← hterms]
  change T = Q + (T - Q)
  abel

end
end MeyerGeneralProblem
