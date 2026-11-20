module

public import MeyerGeneralProblem.Distribution.CombCoefficientReconstruction
public import MeyerGeneralProblem.Distribution.LineDirectionAssembly

@[expose] public section

/-!
# Exact class combs from affine lattice-line support

The original recurrence is recovered on each rational line direction.
Only one spectral class can act parallel to a given direction. The
resulting original coefficient functions are realized as genuine
modulated combs, and the finite-support kernel removes the crossings.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators SchwartzMap FourierTransform

/-- Finite genuine combs whose frequencies and periods belong to the
prescribed reciprocal spectral classes. -/
def IsFiniteSpectralClassCombSum (classes : List (ℝ × List ℝ))
    (T : TemperedDistribution ℝ ℂ) : Prop :=
  ∃ (ι : Type) (inst : Fintype ι), letI := inst
    ∃ (q : ι → AffineCombTerm) (w : ι → ℝ) (hw : ∀ i, 0 < w i),
      T = ∑ i, (q i).distribution (w i) (hw i) ∧
      ∀ i, ∃ p ∈ classes, p.1 = w i ∧ (q i).frequency ∈ p.2

private def parallelSpectralClasses (classes : List (ℝ × List ℝ)) (d : ℝ) :
    List (ℝ × List ℝ) := by
  classical
  exact classes.filter fun p => decide (p.1 ∈ rationalLineDirection d)

private theorem parallel_filter_class_weights (classes : List (ℝ × List ℝ)) (d : ℝ) :
    parallelTranslationFactors (combTranslationWeightsByClass classes) d =
      combTranslationWeightsByClass (parallelSpectralClasses classes d) := by
  classical
  induction classes with
  | nil => rfl
  | cons p classes ih =>
      obtain ⟨w,modes⟩ := p
      have hmode : (modes.map fun s => (w,combModulationCharacter (-w) s)).filter
          (fun p => decide (p.1 ∈ rationalLineDirection d)) =
            if w ∈ rationalLineDirection d then modes.map fun s => (w,combModulationCharacter (-w) s) else [] := by
        induction modes with
        | nil => split <;> rfl
        | cons s modes ih => by_cases h : w ∈ rationalLineDirection d <;> simp [h,ih]
      change (((modes.map fun s => (w,combModulationCharacter (-w) s)) ++
        combTranslationWeightsByClass classes).filter (fun p => decide (p.1 ∈ rationalLineDirection d))) = _
      rw [List.filter_append,hmode]
      change _ ++ parallelTranslationFactors (combTranslationWeightsByClass classes) d = _
      rw [ih]
      by_cases h : w ∈ rationalLineDirection d <;>
        simp [h,combTranslationWeightsByClass,parallelSpectralClasses]

private theorem parallel_classes_filter_eq_nil_or_single
    (classes : List (ℝ × List ℝ)) (d : ℝ)
    (hpos : ∀ p ∈ classes, 0 < p.1)
    (hsep : classes.Pairwise (fun p q => p.1 ∉ rationalLineDirection q.1)) :
    parallelSpectralClasses classes d = [] ∨
      ∃ p ∈ classes, p.1 ∈ rationalLineDirection d ∧ parallelSpectralClasses classes d = [p] := by
  classical
  induction classes with
  | nil => exact Or.inl rfl
  | cons p classes ih =>
      obtain ⟨hHead,hTail⟩ := List.pairwise_cons.mp hsep
      by_cases hp : p.1 ∈ rationalLineDirection d
      · have hEmpty : parallelSpectralClasses classes d = [] := by
          unfold parallelSpectralClasses
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro q hq
          have hqm := (List.mem_filter.mp hq).1
          have hqd : q.1 ∈ rationalLineDirection d := by simpa using (List.mem_filter.mp hq).2
          apply hHead q hqm
          rwa [rationalLineDirection_eq_of_mem_ne_zero q.1 d
            (hpos q (List.mem_cons_of_mem _ hqm)).ne' hqd]
        exact Or.inr ⟨p,List.mem_cons_self,hp,by simpa [parallelSpectralClasses,hp] using hEmpty⟩
      · rcases ih (fun q hq => hpos q (List.mem_cons_of_mem _ hq)) hTail with hn | ⟨q,hq,hqd,he⟩
        · exact Or.inl (by simpa [parallelSpectralClasses,hp] using hn)
        · exact Or.inr ⟨q,List.mem_cons_of_mem _ hq,hqd,by simpa [parallelSpectralClasses,hp] using he⟩

private theorem translationDifferenceProduct_eq_zero_of_parallel
    (factors : List (ℝ × ℂ)) (d : ℝ) (f : ℝ → ℂ)
    (hf : translationDifferenceProduct (parallelTranslationFactors factors d) f = 0) :
    translationDifferenceProduct factors f = 0 := by
  classical
  let pred (p : ℝ × ℂ) : Bool := decide (p.1 ∈ rationalLineDirection d)
  rw [← translationDifferenceProduct_eq_of_perm (List.filter_append_perm pred factors) f,
    translationDifferenceProduct_append]
  change translationDifferenceProduct (factors.filter fun p => !pred p)
    (translationDifferenceProduct (parallelTranslationFactors factors d) f) = 0
  rw [hf, ← translationDifferenceProductLinearMap_apply,map_zero]

private theorem affineCombTermSum_eq_sum_get
    (w : ℝ) (hw : 0 < w) (terms : List AffineCombTerm) :
    affineCombTermSum w hw terms =
      ∑ j : Fin terms.length, (terms.get j).distribution w hw := by
  have he : (terms.map fun q => q.distribution w hw) =
      List.ofFn (fun j : Fin terms.length => (terms.get j).distribution w hw) := by
    change (terms.map fun q => q.distribution w hw) =
      List.ofFn ((fun q : AffineCombTerm => q.distribution w hw) ∘ terms.get)
    rw [← List.map_ofFn,List.ofFn_get]
  rw [affineCombTermSum,he,List.sum_ofFn]

/-- Under normalized spectral classes, the bilateral recurrence and a
finite physical line carrier give an exact genuine class-comb sum. -/
theorem isFiniteSpectralClassCombSum_of_recurrence_and_affine_lattice_cover
    (classes : List (ℝ × List ℝ))
    (hpos : ∀ p ∈ classes, 0 < p.1)
    (hModes : ∀ p ∈ classes, p.2.Pairwise
      (fun s t => combModulationCharacter (-p.1) s ≠ combModulationCharacter (-p.1) t))
    (hsep : classes.Pairwise (fun p q => p.1 ∉ rationalLineDirection q.1))
    (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (E : Finset (ℝ × ℝ))
    (hcover : AtomicOnCarrier (affineLatticeUnionCarrier E) T)
    (hz : translationDifferenceProduct (combTranslationWeightsByClass classes)
      (extendedAtomicCoefficient A T) = 0) :
    IsFiniteSpectralClassCombSum classes T := by
  classical
  let factors := combTranslationWeightsByClass classes
  let f := extendedAtomicCoefficient A T
  let D := (E.filter fun p => p.2 ≠ 0).image fun p => rationalLineDirection p.2
  have hf : Function.support f ⊆ (affineLatticeUnionCarrier E).carrier := by
    let B := affineLatticeUnionCarrier E
    let U := A.union B
    intro x hx
    by_contra hxB
    have he : extendedAtomicCoefficient U T x = f x :=
      extendedAtomicCoefficient_on_larger_carrier _ _ Set.subset_union_left _ hT x
    have he' : extendedAtomicCoefficient U T x = 0 := by
      rw [extendedAtomicCoefficient_on_larger_carrier B U Set.subset_union_right T hcover,
        extendedAtomicCoefficient,dite_eq_right hxB]
    exact hx (he.symm.trans he')
  have hvalid (p : ℝ × ℂ) (hp : p ∈ factors) :
      p.2 ≠ 0 ∧ Function.Injective (fun n : ℕ => n • p.1) := by
    obtain ⟨cls,hcls,hp'⟩ := List.mem_flatMap.mp hp
    obtain ⟨s, _,rfl⟩ := List.mem_map.mp hp'
    have hc : 0 < ‖combModulationCharacter (-cls.1) s‖ := by
      rw [norm_combModulationCharacter]; norm_num
    refine ⟨norm_pos_iff.mp hc, ?_⟩
    intro m n he
    have hh : (m : ℝ) = (n : ℝ) := mul_right_cancel₀ (hpos cls hcls).ne' (by
      simpa only [nsmul_eq_mul] using he)
    exact_mod_cast hh
  have hphase (p : ℝ × ℂ) (hp : p ∈ factors) : p.2 ≠ 0 := (hvalid p hp).1
  have hreps (i : D) : ∃ d : ℝ, d ≠ 0 ∧ rationalLineDirection d = i.val := by
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp i.property
    exact ⟨p.2,(Finset.mem_filter.mp hp).2,he⟩
  choose d hd₀ hd using hreps
  have hDirInj : Function.Injective (fun i => rationalLineDirection (d i)) := by
    intro i j he
    change rationalLineDirection (d i) = rationalLineDirection (d j) at he
    exact Subtype.ext ((hd i).symm.trans (he.trans (hd j)))
  have hDirCover (p : ℝ × ℝ) (hp : p ∈ E) (hn : p.2 ≠ 0) :
      ∃ i : D, rationalLineDirection p.2 = rationalLineDirection (d i) := by
    let i : D := ⟨rationalLineDirection p.2,Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨hp,hn⟩)⟩
    exact ⟨i,(hd i).symm⟩
  have hSolve (i : D) : ∃ (w : ℝ) (hw : 0 < w) (q : List AffineCombTerm),
      (∀ t ∈ q, ∃ c ∈ classes, c.1 = w ∧ t.frequency ∈ c.2) ∧
      let u := extendedAtomicCoefficient (affineCombTermSumCarrier w hw q) (affineCombTermSum w hw q)
      translationDifferenceProduct factors u = 0 ∧
      (Function.support (restrictToParallelAffineLines E (d i) f - u)).Finite := by
    have hfilter := parallel_filter_class_weights classes (d i)
    rcases parallel_classes_filter_eq_nil_or_single classes (d i) hpos hsep with
      hEmpty | ⟨c,hc,hcd,hOne⟩
    · obtain ⟨u,hu,hfin⟩ := exists_parallel_kernel_approximation_of_affine_line_cover
        E factors hphase f hf hz (d i)
      change translationDifferenceProduct (parallelTranslationFactors
        (combTranslationWeightsByClass classes) (d i)) u = 0 at hu
      rw [hfilter,hEmpty] at hu
      change u = 0 at hu
      refine ⟨1,zero_lt_one,[],by simp,?_⟩
      have hcoeff : extendedAtomicCoefficient (affineCombTermSumCarrier 1 zero_lt_one [])
          (affineCombTermSum 1 zero_lt_one []) = 0 := by
        funext x
        simp [affineCombTermSumCarrier,extendedAtomicCoefficient]
      dsimp only
      rw [hcoeff]
      refine ⟨by rw [← translationDifferenceProductLinearMap_apply,map_zero],?_⟩
      simpa only [hu] using hfin
    · have hw := hpos c hc
      have hsel : parallelTranslationFactors factors (d i) =
          c.2.map fun s => (c.1,combModulationCharacter (-c.1) s) := by
        change parallelTranslationFactors (combTranslationWeightsByClass classes) (d i) = _
        rw [hfilter,hOne]
        simp [combTranslationWeightsByClass]
      have hSteps (p : ℝ × ℂ) (hp : p ∈ parallelTranslationFactors factors (d i)) :
          p.1 = c.1 := by
        rw [hsel] at hp
        obtain ⟨s,_,rfl⟩ := List.mem_map.mp hp
        rfl
      obtain ⟨F,hF,u,hU,hu,hfin⟩ :=
        exists_supported_parallel_kernel_approximation_of_affine_line_cover
          E factors hphase f hf hz (d i) c.1 hw.ne' hcd hSteps
      obtain ⟨q,hq,hqF,hcoef⟩ := exists_affineCombTermSum_of_exact_coefficient_recurrence
        F c.1 hw hF c.2 (hModes c hc) u hU (hsel ▸ hu)
      refine ⟨c.1,hw,q,fun t ht => ⟨c,hc,rfl,hq t ht⟩,?_⟩
      have hcoef' : extendedAtomicCoefficient (affineCombTermSumCarrier c.1 hw q)
          (affineCombTermSum c.1 hw q) = u := by
        funext x
        exact (extendedAtomicCoefficient_on_larger_carrier _ _ hqF _
          (atomicOnCarrier_affineCombTermSum _ _ _) x).symm.trans (hcoef x)
      dsimp only
      rw [hcoef']
      exact ⟨translationDifferenceProduct_eq_zero_of_parallel factors (d i) u hu,hfin⟩
  choose w hw q hq hsol using hSolve
  let C (i : D) := affineCombTermSumCarrier (w i) (hw i) (q i)
  let S (i : D) := affineCombTermSum (w i) (hw i) (q i)
  let u (i : D) := extendedAtomicCoefficient (C i) (S i)
  have hEq : f = ∑ i, u i := eq_sum_of_parallel_kernel_approximations
    E f hf d hDirInj hDirCover factors hvalid hz u (fun i => (hsol i).1) (fun i => (hsol i).2)
  let A' : LocallyFiniteCarrier :=
    { carrier := ⋃ i : D, (C i).carrier
      finite_inter_Icc := fun l r => by
        rw [Set.iUnion_inter]
        exact Set.finite_iUnion fun i => (C i).finite_inter_Icc l r }
  let U := A.union A'
  have hsub (i : D) : (C i).carrier ⊆ U.carrier := fun x hx =>
    Or.inr (Set.mem_iUnion.mpr ⟨i,hx⟩)
  have hAtom (i : D) : AtomicOnCarrier (C i) (S i) :=
    atomicOnCarrier_affineCombTermSum _ _ _
  have hAtomSum : AtomicOnCarrier U (∑ i, S i) := by
    intro g hg
    simp only [_root_.sum_apply]
    exact Finset.sum_eq_zero fun i _ => hAtom i g (fun x hx => hg x (hsub i hx))
  have hTsum : T = ∑ i, S i := by
    apply atomic_eq_of_coefficients U _ _ (hT.mono Set.subset_union_left) hAtomSum
    intro x
    have hm : (x : ℝ) ∈ U.carrier := x.property
    have hx : extendedAtomicCoefficient U T x = extendedAtomicCoefficient U (∑ i, S i) x := by
      rw [extendedAtomicCoefficient_on_larger_carrier A U Set.subset_union_left T hT,
        extendedAtomicCoefficient_finset_sum]
      have he := congrFun hEq (x : ℝ)
      change f (x : ℝ) = _
      rw [he,Finset.sum_apply]
      exact Finset.sum_congr rfl (fun i _ =>
        (extendedAtomicCoefficient_on_larger_carrier _ _ (hsub i) _ (hAtom i) _).symm)
    simpa only [extendedAtomicCoefficient,dite_eq_left hm] using hx
  let I := Σ i : D, Fin (q i).length
  refine ⟨I,inferInstance,(fun j => (q j.1).get j.2),(fun j => w j.1),
    (fun j => hw j.1), ?_, ?_⟩
  · rw [hTsum,Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun i _ => affineCombTermSum_eq_sum_get _ _ _)
  · exact fun j => hq j.1 _ (List.get_mem _ _)

end
end MeyerGeneralProblem
