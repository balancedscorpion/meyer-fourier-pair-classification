module

public import MeyerGeneralProblem.Distribution.LineDirectionAssembly

@[expose] public section

/-!
# Least cofinite full-lattice envelopes

A missing point on one lattice gives a full subprogression disjoint from
every parallel target line. Nonparallel lines cut this subprogression in
only finitely many points. Therefore finite exceptions cannot conceal a
failure of inclusion between finite full-lattice unions.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set

/-- A finite set of positive commensurate steps has a common positive
integer-multiple step. The original positive step is included. -/
theorem exists_common_integer_lattice_step (E : Finset ℝ) (w : ℝ) (hw : 0 < w)
    (hE : ∀ v ∈ E, 0 < v ∧ v ∈ rationalLineDirection w) :
    ∃ d : ℝ, 0 < d ∧ d ∈ AddSubgroup.zmultiples w ∧
      ∀ v ∈ E, d ∈ AddSubgroup.zmultiples v := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    exact ⟨w, hw, AddSubgroup.mem_zmultiples_iff.mpr ⟨1, one_zsmul _⟩, by simp⟩
  | insert v E hv ih =>
    obtain ⟨hvpos, hvdir⟩ := hE v (Finset.mem_insert_self _ _)
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hvdir
    have hvrel : v = (r : ℝ) * w := by simpa only [Rat.smul_def] using hr.symm
    have hrpos : 0 < r := by
      have hreal : (0 : ℝ) < r := by
        by_contra! h
        exact (not_lt_of_ge ((hvrel.trans_le (mul_nonpos_of_nonpos_of_nonneg h hw.le)))) hvpos
      exact_mod_cast hreal
    have hnum : 0 < r.num := Rat.num_pos.mpr hrpos
    have hdenom : (r.den : ℝ) * v = (r.num : ℝ) * w := by
      have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
      rw [hvrel, Rat.cast_def]
      field_simp
    obtain ⟨d, hd, hdw, hprev⟩ := ih fun u hu => hE u (Finset.mem_insert_of_mem hu)
    refine ⟨r.num • d, ?_, (AddSubgroup.zmultiples w).zsmul_mem hdw r.num, ?_⟩
    · rw [zsmul_eq_mul]
      exact mul_pos (by exact_mod_cast hnum) hd
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hdw
        apply AddSubgroup.mem_zmultiples_iff.mpr
        refine ⟨m * (r.den : ℤ), ?_⟩
        rw [← hm]
        simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
        linear_combination (m : ℝ) * hdenom
      · exact (AddSubgroup.zmultiples u).zsmul_mem (hprev u hu) r.num

theorem affineLatticeLine_subprogression {x y d w : ℝ}
    (hx : x ∈ affineLatticeLine y w) (hd : d ∈ AddSubgroup.zmultiples w) :
    affineLatticeLine x d ⊆ affineLatticeLine y w := by
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hd
  obtain ⟨k, rfl⟩ := hx
  rintro _ ⟨n, rfl⟩
  refine ⟨k + n * m, ?_⟩
  rw [← hm, zsmul_eq_mul]
  push_cast
  ring

theorem not_mem_of_mem_subprogression {x y d w z : ℝ}
    (hx : x ∉ affineLatticeLine y w) (hd : d ∈ AddSubgroup.zmultiples w)
    (hz : z ∈ affineLatticeLine x d) : z ∉ affineLatticeLine y w := by
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hd
  obtain ⟨n, rfl⟩ := hz
  rintro ⟨k, hk⟩
  apply hx
  refine ⟨k - n * m, ?_⟩
  rw [← hm, zsmul_eq_mul] at hk
  push_cast
  linear_combination hk

/-- A full positive-step lattice that lies in a finite union of full
positive-step lattices up to finite exceptions is contained outright. -/
theorem affineLatticeLine_subset_of_finite_sdiff (y w : ℝ) (hw : 0 < w)
    (F : Finset (ℝ × ℝ)) (hF : ∀ p ∈ F, 0 < p.2)
    (hfin : (affineLatticeLine y w \ (affineLatticeUnionCarrier F).carrier).Finite) :
    affineLatticeLine y w ⊆ (affineLatticeUnionCarrier F).carrier := by
  classical
  intro x hx
  by_contra hmiss
  let P := (F.filter fun p => p.2 ∈ rationalLineDirection w).image Prod.snd
  have hP (v : ℝ) (hv : v ∈ P) : 0 < v ∧ v ∈ rationalLineDirection w := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨hF p (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
  obtain ⟨d, hd, hdw, hperiod⟩ := exists_common_integer_lattice_step P w hw hP
  have hdDir : rationalLineDirection d = rationalLineDirection w := by
    apply rationalLineDirection_eq_of_mem_ne_zero d w hd.ne'
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hdw
    exact Submodule.mem_span_singleton.mpr ⟨(m : ℚ), by
      simpa only [Rat.smul_def, Rat.cast_intCast, zsmul_eq_mul] using hm⟩
  let X (p : F) : Set ℝ :=
    if p.val.2 ∈ rationalLineDirection w then ∅
    else affineLatticeLine x d ∩ affineLatticeLine p.val.1 p.val.2
  have hX (p : F) : (X p).Finite := by
    by_cases hp : p.val.2 ∈ rationalLineDirection w
    · simp [X, hp]
    · simp only [X, ite_eq_right hp]
      apply finite_affineLatticeLine_inter_of_rationalLineDirection_ne
      intro he
      apply hp
      rw [← hdDir, he]
      exact Submodule.mem_span_singleton_self _
  have hfinite : (affineLatticeLine x d).Finite := by
    apply (hfin.union (Set.finite_iUnion hX)).subset
    intro z hz
    by_cases hzF : z ∈ (affineLatticeUnionCarrier F).carrier
    · obtain ⟨p, hp, hzp⟩ := (mem_affineLatticeUnionCarrier F z).mp hzF
      have hpOut : p.2 ∉ rationalLineDirection w := by
        intro hpar
        have hpD := hperiod p.2 (Finset.mem_image_of_mem _
          (Finset.mem_filter.mpr ⟨hp, hpar⟩))
        have hxOut : x ∉ affineLatticeLine p.1 p.2 := fun h =>
          hmiss ((mem_affineLatticeUnionCarrier F x).mpr ⟨p, hp, h⟩)
        exact (not_mem_of_mem_subprogression hxOut hpD hz) hzp
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨p, hp⟩, by simpa only [X, ite_eq_right hpOut] using ⟨hz, hzp⟩⟩)
    · exact Or.inl ⟨affineLatticeLine_subprogression hx hdw hz, hzF⟩
  apply (Set.infinite_range_of_injective (f := fun n : ℤ => x + (n : ℝ) * d) ?_) hfinite
  intro k l hk
  exact_mod_cast mul_right_cancel₀ hd.ne' (add_left_cancel hk)

/-- Finite differences between positive-step full-lattice unions imply
literal containment. -/
theorem affineLatticeUnion_subset_of_finite_sdiff (E F : Finset (ℝ × ℝ))
    (hE : ∀ p ∈ E, 0 < p.2) (hF : ∀ p ∈ F, 0 < p.2)
    (hfin : ((affineLatticeUnionCarrier E).carrier \ (affineLatticeUnionCarrier F).carrier).Finite) :
    (affineLatticeUnionCarrier E).carrier ⊆ (affineLatticeUnionCarrier F).carrier := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
  apply affineLatticeLine_subset_of_finite_sdiff p.1 p.2 (hE p hp) F hF _ hxp
  exact hfin.subset fun z hz =>
    ⟨(mem_affineLatticeUnionCarrier E z).mpr ⟨p, hp, hz.1⟩, hz.2⟩

/-- Any cofinite positive-step full-lattice envelope is the least one
containing the source support. Consequently it is unique as a set. -/
theorem affineLatticeUnion_isLeast_of_cofinite_cover (A : Set ℝ)
    (E : Finset (ℝ × ℝ)) (hE : ∀ p ∈ E, 0 < p.2)
    (hcover : A ⊆ (affineLatticeUnionCarrier E).carrier)
    (hfin : ((affineLatticeUnionCarrier E).carrier \ A).Finite) :
    IsLeast {L : Set ℝ | ∃ F : Finset (ℝ × ℝ),
      (∀ p ∈ F, 0 < p.2) ∧ L = (affineLatticeUnionCarrier F).carrier ∧ A ⊆ L}
      (affineLatticeUnionCarrier E).carrier := by
  refine ⟨⟨E, hE, rfl, hcover⟩, ?_⟩
  rintro L ⟨F, hF, rfl, hAF⟩
  exact affineLatticeUnion_subset_of_finite_sdiff E F hE hF
    (hfin.subset fun _ hx => ⟨hx.1, fun ha => hx.2 (hAF ha)⟩)

end
end MeyerGeneralProblem
