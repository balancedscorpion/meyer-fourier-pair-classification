module

public import MeyerGeneralProblem.Distribution.CommensurateCombSupport
public import MeyerGeneralProblem.Distribution.FiniteHoleCombSpace

@[expose] public section

/-!
# Exact support completion for the original finite comb

Class supports are completed separately at the level of coefficient
functions. Only finitely many sites see two different rational
directions. Keeping the net sum at those sites gives holes in a cover
and cannot produce an original atom outside it.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators FourierTransform

/-- Finite lattice unions in disjoint sets of directions have finite intersection. -/
theorem finite_latticeUnion_inter_of_different_directions
    (E F : Finset (ℝ × ℝ))
    (h : ∀ p ∈ E, ∀ q ∈ F, rationalLineDirection p.2 ≠ rationalLineDirection q.2) :
    ((affineLatticeUnionCarrier E).carrier ∩ (affineLatticeUnionCarrier F).carrier).Finite := by
  let X (p : E) (q : F) := affineLatticeLine p.val.1 p.val.2 ∩ affineLatticeLine q.val.1 q.val.2
  have hX (p : E) (q : F) : (X p q).Finite :=
    finite_affineLatticeLine_inter_of_rationalLineDirection_ne _ _ _ _ (h p p.property q q.property)
  apply (Set.finite_iUnion fun p => Set.finite_iUnion (hX p)).subset
  rintro x ⟨hx, hy⟩
  obtain ⟨p, hp, hxp⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
  obtain ⟨q, hq, hxq⟩ := (mem_affineLatticeUnionCarrier F x).mp hy
  exact mem_iUnion.mpr ⟨⟨p, hp⟩, mem_iUnion.mpr ⟨⟨q, hq⟩, hxp, hxq⟩⟩

/-- Finite crossings between distinct directions account for all new holes
when directional coefficient functions are added. -/
theorem hasCofiniteLatticeCover_support_sum_of_distinct_directions
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ) (D : ι → Submodule ℚ ℝ)
    (hD : Function.Injective D)
    (h : ∀ i, ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, 0 < p.2 ∧ rationalLineDirection p.2 = D i) ∧
      Function.support (f i) ⊆ (affineLatticeUnionCarrier E).carrier ∧
      ((affineLatticeUnionCarrier E).carrier \ Function.support (f i)).Finite) :
    HasCofiniteLatticeCover (Function.support (∑ i, f i)) := by
  classical
  choose F hstep hcover hfin using h
  have hc (i : ι) : ∃ E : Finset (ℝ × ℝ), (∀ p ∈ E, 0 < p.2) ∧
      Function.support (f i) ⊆ (affineLatticeUnionCarrier E).carrier ∧
      ((affineLatticeUnionCarrier E).carrier \ Function.support (f i)).Finite :=
    ⟨F i, fun p hp => (hstep i p hp).1, hcover i, hfin i⟩
  obtain ⟨E, hE, hUE, hEfin⟩ := exists_lattice_cover_iUnion
    (fun i => Function.support (f i)) (0 < ·) hc
  let X (i j : ι) : Set ℝ := if i = j then ∅
    else (affineLatticeUnionCarrier (F i)).carrier ∩ (affineLatticeUnionCarrier (F j)).carrier
  have hX (i j : ι) : (X i j).Finite := by
    by_cases hij : i = j
    · simp [X, hij]
    · simp only [X, ite_eq_right hij]
      apply finite_latticeUnion_inter_of_different_directions
      intro p hp q hq
      rw [(hstep i p hp).2, (hstep j q hq).2]
      exact fun he => hij (hD he)
  have hsub : Function.support (∑ i, f i) ⊆ ⋃ i, Function.support (f i) := by
    intro x hx
    by_contra hout
    apply hx
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero (fun i _ => by
      by_contra hi
      exact hout (mem_iUnion.mpr ⟨i, hi⟩))
  refine ⟨E, hE, hsub.trans hUE, ?_⟩
  apply (hEfin.union (Set.finite_iUnion fun i => Set.finite_iUnion (hX i))).subset
  rintro x ⟨hxE, hxout⟩
  by_cases hx : x ∈ ⋃ i, Function.support (f i)
  · right
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    by_contra hnot
    have hz (j : ι) (hji : j ≠ i) : f j x = 0 := by
      by_contra hj
      apply hnot
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, by
        simp only [X, ite_eq_right (Ne.symm hji)]
        exact ⟨hcover i hi, hcover j hj⟩⟩⟩
    have hval : (∑ j, f j) x = f i x := by
      rw [Finset.sum_apply]
      exact Finset.sum_eq_single i (fun j _ hji => hz j hji) (by simp)
    exact hxout (by change (∑ j, f j) x ≠ 0; rwa [hval])
  · exact Or.inl ⟨hxE, hx⟩

/-- The actual support of all finite comb coefficients has a cofinite
full-lattice envelope once the scalar zero-set statement is supplied. -/
theorem hasCofiniteLatticeCover_affineCombCoefficients
    (hscalar : BilateralPowerSumCofiniteSupport)
    {ι : Type} [Fintype ι] (q : ι → AffineCombTerm) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) :
    HasCofiniteLatticeCover (Function.support (affineCombCoefficients q w)) := by
  classical
  let dirs := Finset.univ.image (fun i => rationalLineDirection (w i))
  let cls (i : ι) : dirs :=
    ⟨rationalLineDirection (w i), Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  let I (j : dirs) := {i : ι // cls i = j}
  let f (j : dirs) : ℝ → ℂ :=
    affineCombCoefficients (fun i : I j => q i.val) (fun i => w i.val)
  have hsum : affineCombCoefficients q w = ∑ j, f j := by
    funext x
    rw [Finset.sum_apply]
    unfold affineCombCoefficients
    rw [← Finset.sum_fiberwise Finset.univ cls (fun i => (q i).coefficientFunction (w i) x)]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_subtype (p := fun i => cls i = j)
      (Finset.univ.filter (fun i => cls i = j)) (by simp)
      (fun i => (q i).coefficientFunction (w i) x)
  rw [hsum]
  apply hasCofiniteLatticeCover_support_sum_of_distinct_directions f Subtype.val Subtype.val_injective
  intro j
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp j.property
  let W := Finset.univ.image (fun i : I j => w i.val)
  have hW (v : ℝ) (hv : v ∈ W) : 0 < v ∧ v ∈ rationalLineDirection (w k) := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    have hi : rationalLineDirection (w i.val) = j.val := congrArg Subtype.val i.property
    exact ⟨hw i.val, by rw [hk, ← hi]; exact Submodule.mem_span_singleton_self _⟩
  obtain ⟨d, hd, hdk, hdiv⟩ := exists_common_integer_lattice_step W (w k) (hw k) hW
  have hdDir : rationalLineDirection d = j.val := by
    rw [← hk]
    apply rationalLineDirection_eq_of_mem_ne_zero d (w k) hd.ne'
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hdk
    exact Submodule.mem_span_singleton.mpr ⟨(m : ℚ), by
      simpa only [Rat.smul_def, Rat.cast_intCast, zsmul_eq_mul] using hm⟩
  rw [← hdDir]
  exact exists_cofinite_cover_affineCombCoefficients_of_common_step hscalar
    (fun i : I j => q i.val) (fun i => w i.val) (fun i => hw i.val) d hd
    (fun i => hdiv _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))

/-- Transfer the exact support result to the literal original isolation
coefficients on any allowed locally finite carrier. -/
theorem IsFiniteModulatedDiracCombSum.hasCofiniteLatticeCover_actualAtomicSupport
    (hscalar : BilateralPowerSumCofiniteSupport)
    (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier A T) (hcomb : IsFiniteModulatedDiracCombSum T) :
    HasCofiniteLatticeCover (actualAtomicSupport A T) := by
  classical
  obtain ⟨ι, inst, q, w, hw, heq⟩ := hcomb
  let _ := inst
  let E := Finset.univ.image (fun i => ((q i).origin, w i))
  let U := A.union (affineLatticeUnionCarrier E)
  have hsub (i : ι) : affineLatticeLine (q i).origin (w i) ⊆ U.carrier := by
    intro x hx
    exact Or.inr ((mem_affineLatticeUnionCarrier E x).mpr
      ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ i), hx⟩)
  have hcoeff : extendedAtomicCoefficient A T = affineCombCoefficients q w := by
    funext x
    rw [← extendedAtomicCoefficient_on_larger_carrier A U Set.subset_union_left T hT x,
      heq, extendedAtomicCoefficient_finset_sum]
    unfold affineCombCoefficients
    exact Finset.sum_congr rfl (fun i _ =>
      extendedAtomicCoefficient_affineCombTerm _ _ _ _ (hsub i) _)
  unfold actualAtomicSupport
  rw [hcoeff]
  exact hasCofiniteLatticeCover_affineCombCoefficients hscalar q w hw

/-- The bounded-count common-carrier classification reduces to the scalar
characteristic-zero power-sum zero sets. -/
theorem boundedCount_commonSpace_holeClassification_of_powerSumSupport
    (hscalar : BilateralPowerSumCofiniteSupport)
    (S : LocallyFiniteCarrier) (K : ℕ) (hK : UnitCellBound S K) :
    let V := DistributionalMeyerPairSpace S S
    V = finiteHoleEnvelopeSpace S ∧
      (∃ E : FiniteHoleEnvelope S, V = E.embeddedSpace ∧
        Module.finrank ℂ V = E.nullity ∧ ∀ F : FiniteHoleEnvelope S, F.nullity ≤ E.nullity) ∧
      (V ≠ ⊥ ↔ ∃ E : FiniteHoleEnvelope S, 0 < E.nullity) :=
  boundedCount_commonSpace_holeClassification_of_combSupportCompletion S K hK
    (IsFiniteModulatedDiracCombSum.hasCofiniteLatticeCover_actualAtomicSupport hscalar S)

end
end MeyerGeneralProblem
