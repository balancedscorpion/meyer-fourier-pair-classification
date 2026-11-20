module

public import MeyerGeneralProblem.Distribution.TranslationFiberApproximation
public import MeyerGeneralProblem.Distribution.AffineLineCenteredCount
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-!
# Parallel recurrence of the original finite-line record

The rational quotient collapses precisely the lines in the selected
direction. All other lines meet each quotient fiber in at most one site.
Applying the fiber support argument recovers the parallel recurrence
up to finitely many original coefficients.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set

/-- The rational direction of a real step, including its zero multiple. -/
def rationalLineDirection (d : ℝ) : Submodule ℚ ℝ :=
  Submodule.span ℚ ({d} : Set ℝ)

/-- The quotient by one rational direction. -/
abbrev rationalLineProjection (d : ℝ) : ℝ →+ ℝ ⧸ rationalLineDirection d :=
  (rationalLineDirection d).mkQ.toAddMonoidHom

theorem rationalLineProjection_eq_zero_iff (d x : ℝ) :
    rationalLineProjection d x = 0 ↔ x ∈ rationalLineDirection d := by
  change (rationalLineDirection d).mkQ x = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- The finite subfamily of physical lines parallel to the selected
direction. A line with zero step contributes its one point. -/
def parallelAffineLines (E : Finset (ℝ × ℝ)) (d : ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact E.filter fun p => p.2 ∈ rationalLineDirection d

/-- The original coefficient on the genuine union of the parallel lines. -/
def restrictToParallelAffineLines (E : Finset (ℝ × ℝ)) (d : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  ((affineLatticeUnionCarrier (parallelAffineLines E d)).carrier).indicator f

theorem rationalLineProjection_affine_integer
    (d y w : ℝ) (k : ℤ) :
    rationalLineProjection d (y + (k : ℝ) * w) =
      rationalLineProjection d y + k • rationalLineProjection d w := by
  rw [← zsmul_eq_mul, map_add, map_zsmul]

theorem finite_affineLatticeLine_inter_rationalLineFiber
    (y w d : ℝ) (hw : w ∉ rationalLineDirection d) (z : ℝ ⧸ rationalLineDirection d) :
    (affineLatticeLine y w ∩ rationalLineProjection d ⁻¹' {z}).Finite := by
  have hπ : rationalLineProjection d w ≠ 0 := fun he =>
    hw ((rationalLineProjection_eq_zero_iff d w).mp he)
  apply Set.Subsingleton.finite
  rintro x ⟨⟨m,rfl⟩,hm⟩ x' ⟨⟨n,rfl⟩,hn⟩
  change rationalLineProjection d (y + (m : ℝ) * w) = z at hm
  change rationalLineProjection d (y + (n : ℝ) * w) = z at hn
  rw [rationalLineProjection_affine_integer] at hm hn
  have he : m • rationalLineProjection d w = n • rationalLineProjection d w :=
    add_left_cancel (hm.trans hn.symm)
  have heq : (m : ℚ) = (n : ℚ) := smul_left_injective ℚ hπ (by
    simpa only [Int.cast_smul_eq_zsmul] using he)
  have hn' : m = n := by exact_mod_cast heq
  rw [hn']

private theorem finite_image_support_restrictToParallelAffineLines
    (E : Finset (ℝ × ℝ)) (d : ℝ) (f : ℝ → ℂ) :
    (rationalLineProjection d '' Function.support (restrictToParallelAffineLines E d f)).Finite := by
  classical
  let P := parallelAffineLines E d
  let K := P.image fun p => rationalLineProjection d p.1
  apply K.finite_toSet.subset
  rintro _ ⟨x,hx,rfl⟩
  have hx' : x ∈ (affineLatticeUnionCarrier P).carrier := by
    by_contra h
    exact hx (Set.indicator_of_notMem h f)
  obtain ⟨p,hp,⟨k,rfl⟩⟩ := (mem_affineLatticeUnionCarrier P x).mp hx'
  have hp' : p.2 ∈ rationalLineDirection d := (Finset.mem_filter.mp hp).2
  have hzero := (rationalLineProjection_eq_zero_iff d p.2).mpr hp'
  rw [rationalLineProjection_affine_integer, hzero, smul_zero, add_zero]
  exact Finset.mem_image_of_mem _ hp

private theorem finite_support_sub_restrictToParallelAffineLines_inter_fiber
    (E : Finset (ℝ × ℝ)) (d : ℝ) (f : ℝ → ℂ)
    (hf : Function.support f ⊆ (affineLatticeUnionCarrier E).carrier)
    (z : ℝ ⧸ rationalLineDirection d) :
    (Function.support (f - restrictToParallelAffineLines E d f) ∩
      rationalLineProjection d ⁻¹' {z}).Finite := by
  classical
  let P := parallelAffineLines E d
  let Q := E.filter fun p => p.2 ∉ rationalLineDirection d
  have hfin (p : Q) : (affineLatticeLine p.val.1 p.val.2 ∩
      rationalLineProjection d ⁻¹' {z}).Finite :=
    finite_affineLatticeLine_inter_rationalLineFiber _ _ d (Finset.mem_filter.mp p.property).2 z
  apply (Set.finite_iUnion hfin).subset
  rintro x ⟨hx,hz⟩
  have hnot : x ∉ (affineLatticeUnionCarrier P).carrier := by
    intro h
    apply hx
    change f x - (affineLatticeUnionCarrier P).carrier.indicator f x = 0
    rw [Set.indicator_of_mem h, sub_self]
  have hfx : x ∈ Function.support f := by
    intro h
    apply hx
    change f x - (affineLatticeUnionCarrier P).carrier.indicator f x = 0
    rw [Set.indicator_of_notMem hnot, sub_zero, h]
  obtain ⟨p,hp,hxp⟩ := (mem_affineLatticeUnionCarrier E x).mp (hf hfx)
  have hn : p.2 ∉ rationalLineDirection d := by
    intro he
    exact hnot ((mem_affineLatticeUnionCarrier P x).mpr ⟨p, Finset.mem_filter.mpr ⟨hp,he⟩, hxp⟩)
  exact Set.mem_iUnion.mpr ⟨⟨p,Finset.mem_filter.mpr ⟨hp,hn⟩⟩,hxp,hz⟩

/-- The factors whose shifts lie in the chosen rational direction. -/
def parallelTranslationFactors (factors : List (ℝ × ℂ)) (d : ℝ) : List (ℝ × ℂ) := by
  classical
  exact factors.filter fun p => decide (p.1 ∈ rationalLineDirection d)

/-- The component in any one direction agrees, off finitely many
crossing defects, with an exact bilateral solution of its parallel
factors. The original two ends use the same solution. -/
theorem exists_parallel_kernel_approximation_of_affine_line_cover
    (E : Finset (ℝ × ℝ)) (factors : List (ℝ × ℂ)) (hphase : ∀ p ∈ factors, p.2 ≠ 0)
    (f : ℝ → ℂ) (hf : Function.support f ⊆ (affineLatticeUnionCarrier E).carrier)
    (hz : translationDifferenceProduct factors f = 0) (d : ℝ) :
    ∃ u : ℝ → ℂ, translationDifferenceProduct (parallelTranslationFactors factors d) u = 0 ∧
      (Function.support (restrictToParallelAffineLines E d f - u)).Finite := by
  classical
  let keep (p : ℝ × ℂ) : Bool := decide (p.1 ∈ rationalLineDirection d)
  let P := factors.filter keep
  let Q := factors.filter fun p => !keep p
  have htrans (p : ℝ × ℂ) (hp : p ∈ Q) : p.2 ≠ 0 ∧
      Function.Injective (fun n : ℕ => n • rationalLineProjection d p.1) := by
    have hp' := List.mem_filter.mp hp
    refine ⟨hphase p hp'.1, ?_⟩
    have hout : p.1 ∉ rationalLineDirection d := by simpa [keep] using hp'.2
    have hπ : rationalLineProjection d p.1 ≠ 0 := fun he =>
      hout ((rationalLineProjection_eq_zero_iff d p.1).mp he)
    intro m n he
    have h : (m : ℚ) = (n : ℚ) := smul_left_injective ℚ hπ (by
      simpa only [Nat.cast_smul_eq_nsmul] using he)
    exact_mod_cast h
  have hprod : translationDifferenceProduct (P ++ Q) f = 0 :=
    (translationDifferenceProduct_eq_of_perm (List.filter_append_perm keep factors) f).trans hz
  have hparallel (p : ℝ × ℂ) (hp : p ∈ P) : rationalLineProjection d p.1 = 0 :=
    (rationalLineProjection_eq_zero_iff d p.1).mpr (by simpa [keep] using (List.mem_filter.mp hp).2)
  exact exists_parallel_kernel_approximation_of_original_product
    (rationalLineProjection d) P Q hparallel htrans f (restrictToParallelAffineLines E d f)
    (finite_image_support_restrictToParallelAffineLines E d f)
    (finite_support_sub_restrictToParallelAffineLines_inter_fiber E d f hf) hprod

theorem rationalLineDirection_eq_of_mem_ne_zero (w d : ℝ) (hw : w ≠ 0)
    (hwd : w ∈ rationalLineDirection d) :
    rationalLineDirection w = rationalLineDirection d := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hwd
  have hne : r ≠ 0 := by
    intro hz
    apply hw
    rw [← hr, hz, zero_smul]
  unfold rationalLineDirection
  rw [← hr]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hne) d

private theorem exists_refinement_of_affineLatticeLine_of_rat_multiple (y a w : ℝ)
    (r : ℚ) (hr : a = (r : ℝ) * w) :
    ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, p.2 = w) ∧
      affineLatticeLine y a ⊆ (affineLatticeUnionCarrier E).carrier := by
  classical
  let _ : NeZero r.den := ⟨r.den_nz⟩
  let index := Int.divModEquiv r.den
  let E := Finset.univ.image (fun i : Fin r.den => (y + (i.val : ℝ) * a,w))
  refine ⟨E, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    rfl
  · rintro x ⟨n,rfl⟩
    let i := (index n).2
    let m := (index n).1
    have hn : m * (r.den : ℤ) + (i.val : ℤ) = n := index.symm_apply_apply n
    have ha : (r.den : ℝ) * a = (r.num : ℝ) * w := by
      have hD : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
      rw [hr, Rat.cast_def]
      field_simp
    refine (mem_affineLatticeUnionCarrier E _).mpr ⟨(y + (i.val : ℝ) * a,w),
      Finset.mem_image_of_mem _ (Finset.mem_univ i), ⟨m * r.num,?_⟩⟩
    rw [← hn]
    push_cast
    linear_combination -(m : ℝ) * ha

/-- Finitely many parallel source lines are covered by finitely many
lines of a specified step in that direction. Each residue uses its
actual original affine origin. -/
theorem exists_affineLatticeUnion_refinement_of_rationalLineDirection
    (E : Finset (ℝ × ℝ)) (w : ℝ) (hE : ∀ p ∈ E, p.2 ∈ rationalLineDirection w) :
    ∃ F : Finset (ℝ × ℝ), (∀ p ∈ F, p.2 = w) ∧
      (affineLatticeUnionCarrier E).carrier ⊆ (affineLatticeUnionCarrier F).carrier := by
  classical
  have hline (p : E) : ∃ F : Finset (ℝ × ℝ), (∀ q ∈ F, q.2 = w) ∧
      affineLatticeLine p.val.1 p.val.2 ⊆ (affineLatticeUnionCarrier F).carrier := by
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp (hE p p.property)
    exact exists_refinement_of_affineLatticeLine_of_rat_multiple _ _ _ r
      (by simpa only [Rat.smul_def] using hr.symm)
  choose F hF hcover using hline
  refine ⟨Finset.univ.biUnion F, ?_, ?_⟩
  · intro q hq
    obtain ⟨p,_,hq⟩ := Finset.mem_biUnion.mp hq
    exact hF p q hq
  · intro x hx
    obtain ⟨p,hp,hx⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
    obtain ⟨q,hq,hx⟩ := (mem_affineLatticeUnionCarrier _ x).mp (hcover ⟨p,hp⟩ hx)
    exact (mem_affineLatticeUnionCarrier _ x).mpr
      ⟨q,Finset.mem_biUnion.mpr ⟨⟨p,hp⟩,Finset.mem_univ _,hq⟩,hx⟩

private theorem affineLatticeLine_sub_step_iff (y w x : ℝ) :
    x - w ∈ affineLatticeLine y w ↔ x ∈ affineLatticeLine y w := by
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k + 1,?_⟩
    push_cast
    linear_combination hk
  · rintro ⟨k,hk⟩
    refine ⟨k - 1,?_⟩
    push_cast
    linear_combination hk

/-- When the parallel factors share a nonzero step, the genuine
bilateral approximation may be chosen on finitely many cosets of
that exact step. It agrees with the original direction component
away from a finite set on the entire real line. -/
theorem exists_supported_parallel_kernel_approximation_of_affine_line_cover
    (E : Finset (ℝ × ℝ)) (factors : List (ℝ × ℂ)) (hphase : ∀ p ∈ factors, p.2 ≠ 0)
    (f : ℝ → ℂ) (hf : Function.support f ⊆ (affineLatticeUnionCarrier E).carrier)
    (hz : translationDifferenceProduct factors f = 0) (d w : ℝ)
    (hw : w ≠ 0) (hwd : w ∈ rationalLineDirection d)
    (hsteps : ∀ p ∈ parallelTranslationFactors factors d, p.1 = w) :
    ∃ F : Finset (ℝ × ℝ), (∀ p ∈ F, p.2 = w) ∧ ∃ u : ℝ → ℂ,
      Function.support u ⊆ (affineLatticeUnionCarrier F).carrier ∧
      translationDifferenceProduct (parallelTranslationFactors factors d) u = 0 ∧
      (Function.support (restrictToParallelAffineLines E d f - u)).Finite := by
  classical
  let P := parallelAffineLines E d
  have hPar (p : ℝ × ℝ) (hp : p ∈ P) : p.2 ∈ rationalLineDirection w := by
    rw [rationalLineDirection_eq_of_mem_ne_zero w d hw hwd]
    exact (Finset.mem_filter.mp hp).2
  obtain ⟨F,hF,hcover⟩ := exists_affineLatticeUnion_refinement_of_rationalLineDirection P w hPar
  let A := (affineLatticeUnionCarrier F).carrier
  have hA (p : ℝ × ℂ) (hp : p ∈ parallelTranslationFactors factors d) (x : ℝ) :
      x - p.1 ∈ A ↔ x ∈ A := by
    rw [hsteps p hp]
    constructor
    · intro hx
      obtain ⟨q,hq,hx⟩ := (mem_affineLatticeUnionCarrier F _).mp hx
      have he := hF q hq
      rw [he] at hx
      refine (mem_affineLatticeUnionCarrier F x).mpr ⟨q,hq,?_⟩
      rw [he]
      exact (affineLatticeLine_sub_step_iff _ _ _).mp hx
    · intro hx
      obtain ⟨q,hq,hx⟩ := (mem_affineLatticeUnionCarrier F _).mp hx
      have he := hF q hq
      rw [he] at hx
      refine (mem_affineLatticeUnionCarrier F (x-w)).mpr ⟨q,hq,?_⟩
      rw [he]
      exact (affineLatticeLine_sub_step_iff _ _ _).mpr hx
  obtain ⟨u,hu,hfinite⟩ :=
    exists_parallel_kernel_approximation_of_affine_line_cover E factors hphase f hf hz d
  have hS : Function.support (restrictToParallelAffineLines E d f) ⊆ A := by
    intro x hx
    apply hcover
    by_contra h
    exact hx (Set.indicator_of_notMem h f)
  exact ⟨F,hF,exists_supported_translationKernel_approximation _ A hA _ u hS hu hfinite⟩

end
end MeyerGeneralProblem
