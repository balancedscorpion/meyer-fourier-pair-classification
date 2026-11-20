module

public import MeyerGeneralProblem.Distribution.ParallelLineRecurrence

@[expose] public section

/-!
# Exact assembly of direction-wise comb approximations

Distinct rational directions can overlap only at finitely many crossing
sites. The original coefficient record equals the sum of its exact
directional solutions after the full recurrence removes the resulting
finitely supported difference.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators

theorem finite_affineLatticeLine_inter_of_rationalLineDirection_ne
    (y w z v : ℝ) (h : rationalLineDirection w ≠ rationalLineDirection v) :
    (affineLatticeLine y w ∩ affineLatticeLine z v).Finite := by
  by_cases hv : v = 0
  · rw [hv, affineLatticeLine_zero]
    exact (Set.finite_singleton z).subset Set.inter_subset_right
  · have hout : v ∉ rationalLineDirection w := fun hm =>
      h (rationalLineDirection_eq_of_mem_ne_zero v w hv hm).symm
    refine (finite_affineLatticeLine_inter_rationalLineFiber z v w hout
      (rationalLineProjection w y)).subset ?_
    rintro x ⟨⟨k,rfl⟩,hx⟩
    refine ⟨hx,?_⟩
    change rationalLineProjection w (y + (k : ℝ) * w) = rationalLineProjection w y
    have hw : rationalLineProjection w w = 0 :=
      (rationalLineProjection_eq_zero_iff w w).mpr (Submodule.mem_span_singleton_self w)
    rw [rationalLineProjection_affine_integer, hw, smul_zero, add_zero]

private theorem finite_support_sub_sum_parallel_components
    {ι : Type*} [Fintype ι] (E : Finset (ℝ × ℝ)) (f : ℝ → ℂ)
    (hf : Function.support f ⊆ (affineLatticeUnionCarrier E).carrier)
    (d : ι → ℝ)
    (hdistinct : Function.Injective (fun i => rationalLineDirection (d i)))
    (hcover : ∀ p ∈ E, p.2 ≠ 0 → ∃ i, rationalLineDirection p.2 = rationalLineDirection (d i)) :
    (Function.support (f - ∑ i, restrictToParallelAffineLines E (d i) f)).Finite := by
  classical
  let Z := (E.filter (fun p => p.2 = 0)).image Prod.fst
  let crossed (p q : E) : Set ℝ :=
    if rationalLineDirection p.val.2 = rationalLineDirection q.val.2 then ∅
    else affineLatticeLine p.val.1 p.val.2 ∩ affineLatticeLine q.val.1 q.val.2
  have hCrossFin (p q : E) : (crossed p q).Finite := by
    by_cases he : rationalLineDirection p.val.2 = rationalLineDirection q.val.2
    · simpa only [crossed, ite_eq_left he] using (Set.finite_empty : (∅ : Set ℝ).Finite)
    · simpa only [crossed, ite_eq_right he] using
        finite_affineLatticeLine_inter_of_rationalLineDirection_ne
          p.val.1 p.val.2 q.val.1 q.val.2 he
  let X := (Z : Set ℝ) ∪ ⋃ p : E, ⋃ q : E, crossed p q
  have hX : X.Finite := Z.finite_toSet.union
    (Set.finite_iUnion fun p => Set.finite_iUnion (hCrossFin p))
  apply hX.subset
  intro x hx
  by_contra hnot
  have hfne : f x ≠ 0 := by
    intro he
    apply hx
    simp only [Pi.sub_apply, Finset.sum_apply, restrictToParallelAffineLines, he, zero_sub, neg_eq_zero]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hm : x ∈ (affineLatticeUnionCarrier (parallelAffineLines E (d i))).carrier
    · rw [Set.indicator_of_mem hm, he]
    · exact Set.indicator_of_notMem hm f
  have hstep (p : ℝ × ℝ) (hp : p ∈ E) (hxp : x ∈ affineLatticeLine p.1 p.2) : p.2 ≠ 0 := by
    intro he
    apply hnot
    apply Or.inl
    rw [he,affineLatticeLine_zero] at hxp
    rw [Set.mem_singleton_iff.mp hxp]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hp,he⟩)
  obtain ⟨p,hp,hxp⟩ := (mem_affineLatticeUnionCarrier E x).mp (hf hfne)
  obtain ⟨i,hi⟩ := hcover p hp (hstep p hp hxp)
  have hxi : x ∈ (affineLatticeUnionCarrier (parallelAffineLines E (d i))).carrier :=
    (mem_affineLatticeUnionCarrier _ x).mpr ⟨p,Finset.mem_filter.mpr ⟨hp,
      hi ▸ Submodule.mem_span_singleton_self p.2⟩,hxp⟩
  have hOut (j : ι) (hj : j ≠ i) :
      x ∉ (affineLatticeUnionCarrier (parallelAffineLines E (d j))).carrier := by
    intro hxj
    obtain ⟨q,hq,hxq⟩ := (mem_affineLatticeUnionCarrier _ x).mp hxj
    have hq' := Finset.mem_filter.mp hq
    have hj' := rationalLineDirection_eq_of_mem_ne_zero q.2 (d j) (hstep q hq'.1 hxq) hq'.2
    have hne : rationalLineDirection p.2 ≠ rationalLineDirection q.2 := by
      intro he
      exact hj (hdistinct (hj'.symm.trans (he.symm.trans hi)))
    apply hnot
    refine Or.inr (Set.mem_iUnion.mpr ⟨⟨p,hp⟩,Set.mem_iUnion.mpr ⟨⟨q,hq'.1⟩,?_⟩⟩)
    simp only [crossed, ite_eq_right hne, mem_inter_iff, hxp, hxq, and_self]
  apply hx
  simp only [Pi.sub_apply, Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j _ hj => by
    exact Set.indicator_of_notMem (hOut j hj) f)]
  rw [restrictToParallelAffineLines, Set.indicator_of_mem hxi, sub_self]

private theorem finite_support_sum_of_finite {ι G : Type*} [Fintype ι] (g : ι → G → ℂ)
    (hg : ∀ i, (Function.support (g i)).Finite) :
    (Function.support (∑ i, g i)).Finite := by
  classical
  refine (Set.finite_iUnion hg).subset ?_
  intro x hx
  by_contra hn
  apply hx
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun i _ => not_ne_iff.mp
    (fun he => hn (Set.mem_iUnion.mpr ⟨i,he⟩))

/-- The approximations by whole parallel solutions determine the
original record exactly because their remaining error has finite support. -/
theorem eq_sum_of_parallel_kernel_approximations
    {ι : Type*} [Fintype ι] (E : Finset (ℝ × ℝ)) (f : ℝ → ℂ)
    (hf : Function.support f ⊆ (affineLatticeUnionCarrier E).carrier)
    (d : ι → ℝ)
    (hdistinct : Function.Injective (fun i => rationalLineDirection (d i)))
    (hcover : ∀ p ∈ E, p.2 ≠ 0 → ∃ i, rationalLineDirection p.2 = rationalLineDirection (d i))
    (factors : List (ℝ × ℂ)) (hFactors : ∀ p ∈ factors,
      p.2 ≠ 0 ∧ Function.Injective (fun n : ℕ => n • p.1))
    (hz : translationDifferenceProduct factors f = 0) (u : ι → ℝ → ℂ)
    (hu : ∀ i, translationDifferenceProduct factors (u i) = 0)
    (happrox : ∀ i, (Function.support (restrictToParallelAffineLines E (d i) f - u i)).Finite) :
    f = ∑ i, u i := by
  classical
  let g (i : ι) := restrictToParallelAffineLines E (d i) f
  have hfinite := finite_support_sub_sum_parallel_components E f hf d hdistinct hcover
  have hsum := finite_support_sum_of_finite (fun i => g i - u i) happrox
  have he : f - ∑ i, u i = (f - ∑ i, g i) + ∑ i, (g i - u i) := by
    rw [Finset.sum_sub_distrib]
    abel
  have hdiff : (Function.support (f - ∑ i, u i)).Finite := by
    rw [he]
    refine (hfinite.union hsum).subset ?_
    intro x hx
    by_cases h₁ : (f - ∑ i, g i) x = 0
    · refine Or.inr ?_
      intro h₂
      exact hx (by rw [Pi.add_apply, h₁,h₂,add_zero])
    · exact Or.inl h₁
  have hUsum : translationDifferenceProduct factors (∑ i, u i) = 0 := by
    rw [← translationDifferenceProductLinearMap_apply, map_sum]
    exact Finset.sum_eq_zero fun i _ =>
      by simpa only [translationDifferenceProductLinearMap_apply] using hu i
  have hZ : translationDifferenceProduct factors (f - ∑ i, u i) = 0 := by
    rw [translationDifferenceProduct_sub, hz, hUsum, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_translationDifferenceProduct_of_finite_support
    factors hFactors _ hdiff hZ)

end
end MeyerGeneralProblem
