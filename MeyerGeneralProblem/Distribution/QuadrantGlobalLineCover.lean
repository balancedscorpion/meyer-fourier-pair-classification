module

public import MeyerGeneralProblem.Distribution.AffineCellQuadraticCount
public import MeyerGeneralProblem.Distribution.QuadrantResidueCharacters
public import MeyerGeneralProblem.Distribution.QuadrantRationalSpans

@[expose] public section

/-!
# Finite lattice-line cover of the complete original record

For each source, use its own rational-span family to compute all
aggregate residue coefficients. Sources outside that family can
change a coefficient in the chart only on the exceptional lines.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped BigOperators SchwartzMap

private theorem affineLatticeUnionCarrier_subset_of_finset_subset
    {E F : Finset (ℝ × ℝ)} (h : E ⊆ F) :
    (affineLatticeUnionCarrier E).carrier ⊆ (affineLatticeUnionCarrier F).carrier := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
  exact (mem_affineLatticeUnionCarrier F x).mpr ⟨p, h hp, hxp⟩

private theorem exists_combTermSumCarrier_affine_line_cover
    (w : ℝ) (hw : 0 < w) (terms : List AffineCombTerm) :
    ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, p.2 = w) ∧
      (affineCombTermSumCarrier w hw terms).carrier ⊆ (affineLatticeUnionCarrier E).carrier := by
  classical
  induction terms with
  | nil => exact ⟨∅, by simp, fun x hx => hx.elim⟩
  | cons q qs ih =>
      obtain ⟨E, hE, hsub⟩ := ih
      refine ⟨insert (q.origin,w) E, ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · rfl
        · exact hE p hp
      · intro x hx
        rcases hx with hx | hx
        · obtain ⟨k, hk⟩ := (mem_affineDiracCombCarrier w hw q.origin x).mp hx
          exact (mem_affineLatticeUnionCarrier _ x).mpr
            ⟨(q.origin,w), Finset.mem_insert_self _ _, ⟨k,hk.symm⟩⟩
        · exact affineLatticeUnionCarrier_subset_of_finset_subset (Finset.subset_insert _ _) (hsub hx)

private theorem exists_line_cover_in_common_chart
    {ι : Type*} [Fintype ι] {a : ι → ℝ} {w : ℝ} (C : CommonQuadrantCoordinates a w)
    (q : ι → AffineCombTerm) (ha : ∀ i, 0 < a i) (hw : 0 < w) (modes : List ℝ)
    (U : LocallyFiniteCarrier)
    (hsub : ∀ i, (escapingCombIntegralCarrier (q i).origin (a i) w (ha i) hw).carrier ⊆ U.carrier)
    (A X : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (y : ℝ) (G : AddSubgroup ℝ)
    (hdir : ∀ k, C.residueDirection k ∈ G)
    (hcoeff : ∀ x ∈ affineLatticePlane y C.grid, x ∉ X.carrier →
      extendedAtomicCoefficient A T x = extendedAtomicCoefficient U
        (∑ i, escapingCombProductIntegral (q i) (a i) w (ha i) hw modes) x)
    (hX : ∃ b : ℝ, 0 ≤ b ∧ ∀ᶠ R : ℝ in atTop,
      ((X.carrier ∩ Icc (-R) R).ncard : ℝ) ≤ b * R)
    (hcount : ∀ e : ℝ, 0 < e → ∃ᶠ R : ℝ in atTop,
      ((A.carrier ∩ Icc (-R) R).ncard : ℝ) < e * R ^ 2) :
    ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, p.2 ∈ G) ∧
      ∀ x ∈ affineLatticePlane y C.grid, x ∉ X.carrier →
        extendedAtomicCoefficient A T x ≠ 0 → x ∈ (affineLatticeUnionCarrier E).carrier := by
  classical
  let R := Fin C.modulus × Fin C.modulus
  let origin (r : R) := y + C.grid ((r.1.val : ℤ), (r.2.val : ℤ))
  have hsite (r : R) (k : ℤ × ℤ) : origin r + C.residueDirection k ∈ affineLatticePlane y C.grid := by
    refine ⟨((r.1.val : ℤ), (r.2.val : ℤ)) + (C.modulus : ℤ) • k, ?_⟩
    change y + C.grid (((r.1.val : ℤ), (r.2.val : ℤ)) + (C.modulus : ℤ) • k) = _
    rw [map_add, ← add_assoc]
    rfl
  have hres (r : R) : ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, p.2 ∈ G) ∧
      ∀ k, origin r + C.residueDirection k ∉ X.carrier →
        extendedAtomicCoefficient A T (origin r + C.residueDirection k) ≠ 0 →
        origin r + C.residueDirection k ∈ (affineLatticeUnionCarrier E).carrier := by
    obtain ⟨u,c,hCells,hFormula⟩ :=
      exists_affineCells_escapingCombProductIntegrals_on_residue C q ha hw modes U hsub (origin r)
    have hone (bits : ι × Bool → Bool) : ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, p.2 ∈ G) ∧
        ∀ k ∈ integerAffineCell (u bits) (c bits), origin r + C.residueDirection k ∉ X.carrier →
          extendedAtomicCoefficient A T (origin r + C.residueDirection k) ≠ 0 →
          origin r + C.residueDirection k ∈ (affineLatticeUnionCarrier E).carrier := by
      obtain ⟨coeff,α,β,hα,hβ,hform⟩ := hFormula bits
      have htotal (k : ℤ × ℤ) (hk : k ∈ integerAffineCell (u bits) (c bits))
          (hx : origin r + C.residueDirection k ∉ X.carrier) :
          extendedAtomicCoefficient A T (origin r + C.residueDirection k) =
            planarCharacterSum coeff α β k := (hcoeff _ (hsite r k) hx).trans (hform k hk)
      obtain ⟨E,hE,hcover⟩ :=
        exists_finite_affine_lattice_cover_on_affineCell_with_constant_constraints
          coeff α β hα hβ (u bits) (c bits) C.residueDirection C.residueDirection_injective
          (origin r) A X T htotal hX hcount
      refine ⟨E, ?_, ?_⟩
      · intro p hp
        obtain ⟨k, hk⟩ := (hE p hp).2
        rw [← hk]
        exact hdir k
      · intro k hk hx hn
        obtain ⟨p,hp,t,ht⟩ := hcover k hk hx hn
        exact (mem_affineLatticeUnionCarrier E _).mpr ⟨p,hp,⟨t,ht.symm⟩⟩
    choose E hE hCover using hone
    let P := Finset.univ.biUnion E
    refine ⟨P, ?_, ?_⟩
    · intro p hp
      obtain ⟨bits, _, hp⟩ := Finset.mem_biUnion.mp hp
      exact hE bits p hp
    · intro k hx hn
      obtain ⟨bits, hk⟩ := hCells k
      exact affineLatticeUnionCarrier_subset_of_finset_subset
        (fun p hp => Finset.mem_biUnion.mpr ⟨bits, Finset.mem_univ _, hp⟩)
        (hCover bits k hk hx hn)
  choose E hE hCover using hres
  let P := Finset.univ.biUnion E
  refine ⟨P, ?_, ?_⟩
  · intro p hp
    obtain ⟨r, _, hp⟩ := Finset.mem_biUnion.mp hp
    exact hE r p hp
  · rintro x ⟨p, rfl⟩ hx hn
    obtain ⟨r,k,hk⟩ := C.exists_residue_location y p
    change y + C.grid p ∉ X.carrier at hx
    change extendedAtomicCoefficient A T (y + C.grid p) ≠ 0 at hn
    change y + C.grid p ∈ (affineLatticeUnionCarrier P).carrier
    rw [hk] at hx hn ⊢
    exact affineLatticeUnionCarrier_subset_of_finset_subset
      (fun p hp => Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, hp⟩)
      (hCover r k hx hn)

/-- The complete mixed-period record under vanishing quadratic lower count
has its actual nonzero coefficients on finitely many affine lattice
lines. The directions stay in any group containing the original steps. -/
theorem exists_finite_affine_lattice_cover_of_quadrant_decomposition
    {ι : Type*} [Fintype ι] (q : ι → AffineCombTerm) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (w : ℝ) (hw : 0 < w) (modes : List ℝ) (terms : List AffineCombTerm)
    (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (hdecomp : T = (∑ i, escapingCombProductIntegral (q i) (a i) w (ha i) hw modes) +
      affineCombTermSum w hw terms)
    (hIndep : ∀ i, Function.Injective (integerPlaneMap (a i) w))
    (G : AddSubgroup ℝ) (haG : ∀ i, a i ∈ G) (hwG : w ∈ G)
    (hcount : ∀ e : ℝ, 0 < e → ∃ᶠ R : ℝ in atTop,
      ((A.carrier ∩ Icc (-R) R).ncard : ℝ) < e * R ^ 2) :
    ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, p.2 ∈ G) ∧
      ∀ x, extendedAtomicCoefficient A T x ≠ 0 → x ∈ (affineLatticeUnionCarrier E).carrier := by
  classical
  let source (i : ι) := escapingCombProductIntegral (q i) (a i) w (ha i) hw modes
  let S (i : ι) := escapingCombIntegralCarrier (q i).origin (a i) w (ha i) hw
  let Q : LocallyFiniteCarrier :=
    { carrier := ⋃ i, (S i).carrier
      finite_inter_Icc := fun l r => by
        rw [Set.iUnion_inter]
        exact Set.finite_iUnion fun i => (S i).finite_inter_Icc l r }
  let C := affineCombTermSum w hw terms
  let W := affineCombTermSumCarrier w hw terms
  let U := A.union (Q.union W)
  have hsub (i) : (S i).carrier ⊆ U.carrier :=
    fun x hx => Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨i,hx⟩))
  have hW : W.carrier ⊆ U.carrier := fun _ hx => Or.inr (Or.inr hx)
  obtain ⟨P,hP,hPW⟩ := exists_combTermSumCarrier_affine_line_cover w hw terms
  have hC (x : ℝ) (hx : x ∉ (affineLatticeUnionCarrier P).carrier) :
      extendedAtomicCoefficient U C x = 0 := by
    rw [extendedAtomicCoefficient_on_larger_carrier W U hW C
      (atomicOnCarrier_affineCombTermSum w hw terms)]
    exact by rw [extendedAtomicCoefficient, dite_eq_right (fun hx' => hx (hPW hx'))]
  have hwhole (x : ℝ) : extendedAtomicCoefficient A T x =
      (∑ i, extendedAtomicCoefficient U (source i) x) + extendedAtomicCoefficient U C x := by
    rw [← extendedAtomicCoefficient_on_larger_carrier A U (fun _ h => Or.inl h) T hT,
      hdecomp, extendedAtomicCoefficient_add, extendedAtomicCoefficient_finset_sum]
  have hoff (i : ι) (x : ℝ)
      (hx : x ∉ affineLatticePlane (q i).origin (integerPlaneMap (a i) w)) :
      extendedAtomicCoefficient U (source i) x = 0 :=
    escapingCombProductIntegral_extendedCoefficient_off_lattice (q i) (a i) w (ha i) hw modes U
      (hsub i) x hx
  have hcoverGroup (j₀ : ι) : ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, p.2 ∈ G) ∧
      ∀ x ∈ affineLatticePlane (q j₀).origin (integerPlaneMap (a j₀) w),
        extendedAtomicCoefficient A T x ≠ 0 → x ∈ (affineLatticeUnionCarrier E).carrier := by
    let V := quadrantRationalSpan (a j₀) w
    let I := {i // a i ∈ V}
    let J := {i // a i ∉ V}
    let i₀ : I := ⟨j₀, quadrantRationalSpan_left _ _⟩
    let a' (i : I) := a i.val
    let y := (q j₀).origin
    obtain ⟨D⟩ := nonempty_commonQuadrantCoordinates_of_rat_span a' (a j₀) w (hIndep j₀)
      (fun i => exists_nonzero_rat_coordinate_of_quadrantRationalSpan _ _ _ (hIndep i) i.property)
    have hgrid (p) : D.grid p ∈ V :=
      (mem_quadrantRationalSpan_iff _ _ _).mpr (D.exists_rat_grid_coordinates i₀ p)
    have hstep (k) : D.residueDirection k ∈ G := by
      change D.grid ((D.modulus : ℤ) • k) ∈ G
      rw [← D.lift_location i₀, integerPlaneMap_apply]
      exact G.add_mem (G.zsmul_mem (haG _) _) (G.zsmul_mem hwG _)
    choose center hcenter using fun j : J =>
      exists_affineLatticeLine_cover_cross_span V D.grid hgrid y (q j).origin (a j) w
        (quadrantRationalSpan_right _ _) j.property
    let F := P ∪ Finset.univ.image (fun j : J => (center j,w))
    let X := affineLatticeUnionCarrier F
    have hX : ∃ b : ℝ, 0 ≤ b ∧ ∀ᶠ R : ℝ in atTop,
        ((X.carrier ∩ Icc (-R) R).ncard : ℝ) ≤ b * R := by
      obtain ⟨b,hb,hl⟩ := exists_affineLatticeUnionCarrier_linear_count F
      exact ⟨b,hb,(eventually_ge_atTop (1 : ℝ)).mono hl⟩
    have hcoeff (x : ℝ) (hx : x ∈ affineLatticePlane y D.grid) (hXx : x ∉ X.carrier) :
        extendedAtomicCoefficient A T x =
          extendedAtomicCoefficient U
            (∑ i : I, escapingCombProductIntegral (q i) (a' i) w (ha i) hw modes) x := by
      have hPc : x ∉ (affineLatticeUnionCarrier P).carrier := fun hp =>
        hXx (affineLatticeUnionCarrier_subset_of_finset_subset
          (fun p hp => Finset.mem_union.mpr (Or.inl hp)) hp)
      have hout (j : J) : extendedAtomicCoefficient U (source j) x = 0 := by
        apply hoff j x
        intro hq
        apply hXx
        refine (mem_affineLatticeUnionCarrier F x).mpr ⟨(center j,w), ?_, hcenter j ⟨hx,hq⟩⟩
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
      rw [hwhole, hC x hPc, add_zero, extendedAtomicCoefficient_finset_sum]
      let f (i : ι) := extendedAtomicCoefficient U (source i) x
      change (∑ i, f i) = ∑ i : I, f i.val
      calc
        _ = ∑ i ∈ Finset.univ.filter (fun i => a i ∈ V), f i := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro j _ hj
          exact hout ⟨j, by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj⟩
        _ = _ := Finset.sum_subtype _ (fun i => by simp) f
    obtain ⟨E,hE,hEcover⟩ := exists_line_cover_in_common_chart D (fun i : I => q i.val)
      (fun i => ha i) hw modes U (fun i => hsub i) A X T y G hstep hcoeff hX hcount
    refine ⟨F ∪ E, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_union.mp hp with hF | hp
      · rcases Finset.mem_union.mp hF with hP' | hCross
        · rw [hP p hP']
          exact hwG
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hCross
          exact hwG
      · exact hE p hp
    · intro x hx hn
      by_cases hXx : x ∈ X.carrier
      · exact affineLatticeUnionCarrier_subset_of_finset_subset
          (fun p hp => Finset.mem_union.mpr (Or.inl hp)) hXx
      · obtain ⟨p,hp⟩ := hx
        have hchart : x ∈ affineLatticePlane y D.grid :=
          ⟨D.source i₀ p, by
            change y + D.grid (D.source i₀ p) = x
            rw [D.source_location]
            exact hp⟩
        exact affineLatticeUnionCarrier_subset_of_finset_subset
          (fun p hp => Finset.mem_union.mpr (Or.inr hp)) (hEcover x hchart hXx hn)
  choose E hE hcover using hcoverGroup
  let F := P ∪ Finset.univ.biUnion E
  refine ⟨F, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rw [hP p hp]
      exact hwG
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
      exact hE i p hi
  · intro x hx
    by_cases hP' : x ∈ (affineLatticeUnionCarrier P).carrier
    · exact affineLatticeUnionCarrier_subset_of_finset_subset
        (fun p hp => Finset.mem_union.mpr (Or.inl hp)) hP'
    · by_cases hSource : ∃ i, x ∈ affineLatticePlane (q i).origin (integerPlaneMap (a i) w)
      · obtain ⟨i,hi⟩ := hSource
        exact affineLatticeUnionCarrier_subset_of_finset_subset
          (fun p hp => Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
            ⟨i,Finset.mem_univ _,hp⟩))) (hcover i x hi hx)
      · have hzero : ∑ i, extendedAtomicCoefficient U (source i) x = 0 :=
          Finset.sum_eq_zero fun i _ => hoff i x (fun hi => hSource ⟨i,hi⟩)
        exact (hx ((hwhole x).trans (by rw [hzero, hC x hP', add_zero]))).elim

/-- The mixed-period induction step reaches a finite full-lattice
carrier for the actual original record whenever the removed class
leaves a finite comb sum on independent source periods. -/
theorem exists_atomicOnCarrier_affineLatticeUnion_of_combTranslationFactors
    {ι : Type*} [Fintype ι] (q : ι → AffineCombTerm) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (w : ℝ) (hw : 0 < w) (modes : List ℝ) (h_nonempty : modes ≠ [])
    (hdistinct : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t))
    (hD : combTranslationFactors w modes T = ∑ i, (q i).distribution (a i) (ha i))
    (hIndep : ∀ i, Function.Injective (integerPlaneMap (a i) w))
    (G : AddSubgroup ℝ) (haG : ∀ i, a i ∈ G) (hwG : w ∈ G)
    (hcount : ∀ e : ℝ, 0 < e → ∃ᶠ R : ℝ in atTop,
      ((A.carrier ∩ Icc (-R) R).ncard : ℝ) < e * R ^ 2) :
    ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, p.2 ∈ G) ∧
      AtomicOnCarrier (affineLatticeUnionCarrier E) T := by
  classical
  obtain ⟨terms,hterms,_⟩ := exists_quadrant_comb_decomposition_of_combTranslationFactors
    q a ha A T hT w hw modes h_nonempty hdistinct hD
  obtain ⟨E,hE,hcover⟩ := exists_finite_affine_lattice_cover_of_quadrant_decomposition
    q a ha w hw modes terms A T hT hterms hIndep G haG hwG hcount
  refine ⟨E,hE, ?_⟩
  let B := affineLatticeUnionCarrier E
  apply AtomicOnCarrier.mono (S := A.restrict (A.carrier ∩ B.carrier) inter_subset_left)
    inter_subset_right
  refine (atomicOnCarrier_restrict_iff _ _ _ _).mpr ⟨hT, ?_⟩
  intro x hx
  have hm : (x : ℝ) ∈ A.carrier := x.property
  have he : extendedAtomicCoefficient A T x = 0 := by
    by_contra hne
    exact hx ⟨hm,hcover x hne⟩
  rwa [extendedAtomicCoefficient, dite_eq_left hm] at he

end
end MeyerGeneralProblem
