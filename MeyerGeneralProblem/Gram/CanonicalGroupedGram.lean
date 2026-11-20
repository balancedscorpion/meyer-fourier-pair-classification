module

public import MeyerGeneralProblem.Gram.GroupedGramCompactness
public import MeyerGeneralProblem.Carrier.CanonicalClusterGeometry
public import MeyerGeneralProblem.Sampling.CanonicalGroupedRiesz
public import MeyerGeneralProblem.Gram.GroupedUniversalBounds
public import MeyerGeneralProblem.Gram.FiniteCentralExtension

@[expose] public section

/-!+# Actual canonical grouped Gram operators

The source grouping is the exact signed-square short-gap quotient. Central
excision removes whole clusters; square-root charts are used only on the
remaining one-ray groups. The physical Hilbert order is unchanged.
-/

namespace MeyerGeneralProblem

noncomputable section

open Finset MeasureTheory

namespace OrderedCarrierGrouping

variable {S : LocallyFiniteCarrier} {κ : Type*} (G : OrderedCarrierGrouping S κ)

/-- The source anchor minimizes absolute signed-square coordinate too. -/
theorem abs_realNodes_anchor_le (C : κ) (i : Fin (G.size C)) :
    |G.realNodes C (G.anchor C)| ≤ |G.realNodes C i| := by
  simp only [realNodes,abs_signedSquare]
  exact pow_le_pow_left₀ (abs_nonneg _) (G.anchor_min C i) 2

/-- Reindexing whole selected groups is exactly the corresponding subtype
of the full dependent coordinate index. -/
def selectedGroupIndexEquiv (P : κ → Prop) :
    (Σ C : {C : κ // P C}, Fin (G.size C.val)) ≃ {x : G.Index // P x.1} where
  toFun x := ⟨⟨x.1.val,x.2⟩,x.1.property⟩
  invFun x := ⟨⟨x.val.1,x.property⟩,x.val.2⟩
  left_inv := by rintro ⟨⟨C,hC⟩,i⟩; rfl
  right_inv := by rintro ⟨⟨C,i⟩,hC⟩; rfl

end OrderedCarrierGrouping

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ}
  (horder : BoundedClusterOrder S.signedSquareImage d q)

/-- The actual physical grouping associated to the canonical square groups. -/
abbrev signedGrouping := canonicalSignedSquareGrouping S horder

theorem signedGrouping_realNodes (C : CanonicalClusterIndex S.signedSquareImage d)
    (i : Fin (horder.clusterSize C)) :
    horder.signedGrouping.realNodes C i = horder.realClusterNode C i := by
  change signedSquare (S.signedSquareSubtypeEquiv.symm (horder.orderedClusterNode C i)) =
    (horder.orderedClusterNode C i : ℝ)
  exact congrArg Subtype.val (S.signedSquareSubtypeEquiv.apply_symm_apply _)

/-- Signed-square coordinate of the actual minimum-modulus physical anchor. -/
def signedAnchorCoordinate (C : CanonicalClusterIndex S.signedSquareImage d) : ℝ :=
  horder.signedGrouping.realNodes C (horder.signedGrouping.anchor C)

theorem signedAnchorCoordinate_separated
    {C E : CanonicalClusterIndex S.signedSquareImage d} (hne : C ≠ E) :
    d ≤ |horder.signedAnchorCoordinate C-horder.signedAnchorCoordinate E| := by
  unfold signedAnchorCoordinate
  rw [horder.signedGrouping_realNodes C (horder.signedGrouping.anchor C),
    horder.signedGrouping_realNodes E (horder.signedGrouping.anchor E)]
  exact horder.realClusterNode_separated hne _ _

theorem signedGrouping_node_anchor_distance (hd : 0 < d)
    (C : CanonicalClusterIndex S.signedSquareImage d) (i : Fin (horder.clusterSize C)) :
    |horder.signedGrouping.realNodes C i-horder.signedAnchorCoordinate C| ≤ (q:ℝ)*d := by
  unfold signedAnchorCoordinate
  rw [horder.signedGrouping_realNodes C i,
    horder.signedGrouping_realNodes C (horder.signedGrouping.anchor C)]
  simpa only [Real.dist_eq] using horder.realClusterNode_diameter hd C i (horder.signedGrouping.anchor C)

/-- Whole-cluster exterior beyond its uniform diameter and the unit chart
boundary. This removes every cluster meeting the central region. -/
def exteriorGroup (C : CanonicalClusterIndex S.signedSquareImage d) : Prop :=
  (q:ℝ)*d+1 < |horder.signedAnchorCoordinate C|

/-- The fixed physical ray of one exterior canonical group. -/
def exteriorRay (C : CanonicalClusterIndex S.signedSquareImage d) : ℝ :=
  if 0 ≤ horder.signedAnchorCoordinate C then 1 else -1

theorem exteriorRay_sq (C : CanonicalClusterIndex S.signedSquareImage d) :
    (horder.exteriorRay C)^2=1 := by unfold exteriorRay; split_ifs <;> norm_num

theorem exterior_anchorMagnitude (C : CanonicalClusterIndex S.signedSquareImage d) :
    horder.signedGrouping.anchorMagnitude (horder.exteriorRay C) C =
      |horder.signedAnchorCoordinate C| := by
  change horder.exteriorRay C*horder.signedAnchorCoordinate C=|horder.signedAnchorCoordinate C|
  unfold exteriorRay
  split_ifs with h
  · rw [one_mul,abs_of_nonneg h]
  · rw [neg_one_mul,abs_of_neg (lt_of_not_ge h)]

theorem exterior_anchorMagnitude_ge_one (hd : 0 < d)
    (C : CanonicalClusterIndex S.signedSquareImage d) (hC : horder.exteriorGroup C) :
    1 ≤ horder.signedGrouping.anchorMagnitude (horder.exteriorRay C) C := by
  rw [horder.exterior_anchorMagnitude]
  have hD : 0 ≤ (q:ℝ)*d := by positivity
  exact (by dsimp [exteriorGroup] at hC; linarith)

/-- Every actual exterior-group node is on its declared ray and lies in
the anchor-based magnitude interval of width q*d. -/
theorem exterior_magnitudeNodes_mem (hd : 0 < d)
    (C : CanonicalClusterIndex S.signedSquareImage d) (hC : horder.exteriorGroup C)
    (i : Fin (horder.clusterSize C)) :
    horder.signedGrouping.magnitudeNodes (horder.exteriorRay C) C i ∈
      Set.Icc (horder.signedGrouping.anchorMagnitude (horder.exteriorRay C) C)
        (horder.signedGrouping.anchorMagnitude (horder.exteriorRay C) C+(q:ℝ)*d) := by
  have hdist := horder.signedGrouping_node_anchor_distance hd C i
  have hmin := horder.signedGrouping.abs_realNodes_anchor_le C i
  change |horder.signedAnchorCoordinate C| ≤ |horder.signedGrouping.realNodes C i| at hmin
  rw [horder.exterior_anchorMagnitude]
  dsimp [OrderedCarrierGrouping.magnitudeNodes,exteriorRay]
  dsimp [exteriorGroup] at hC
  split_ifs with hsign
  · rw [one_mul,abs_of_nonneg hsign] at *
    have hx : 0 ≤ horder.signedGrouping.realNodes C i := by
      have hlo := (abs_le.mp hdist).1
      linarith
    rw [abs_of_nonneg hx] at hmin
    exact ⟨hmin,by have := (abs_le.mp hdist).2; linarith⟩
  · have hs : horder.signedAnchorCoordinate C < 0 := lt_of_not_ge hsign
    rw [neg_one_mul,abs_of_neg hs] at *
    have hx : horder.signedGrouping.realNodes C i ≤ 0 := by
      have hhi := (abs_le.mp hdist).2
      linarith
    rw [abs_of_nonpos hx] at hmin
    exact ⟨hmin,by have := (abs_le.mp hdist).1; linarith⟩

/-- Bounded signed anchor bands contain finitely many whole canonical groups. -/
theorem finite_signedAnchorCoordinate_band (hd : 0 < d) (R : ℝ) :
    {C : CanonicalClusterIndex S.signedSquareImage d | |horder.signedAnchorCoordinate C| ≤ R}.Finite := by
  classical
  have hfinite := finite_grouped_anchor_abs_le (fun C => horder.clusterSize C) horder.clusterSize_le
    horder.signedAnchorCoordinate hd (fun C E hne => horder.signedAnchorCoordinate_separated hne) R
  apply (hfinite.image Sigma.fst).subset
  intro C hC
  exact ⟨⟨C,⟨0,horder.clusterSize_pos C⟩⟩,hC,rfl⟩

/-- The omitted coordinates are finite, and omission is by whole groups. -/
theorem finite_non_exterior_coordinates (hd : 0 < d) :
    {x : horder.signedGrouping.Index | ¬ horder.exteriorGroup x.1}.Finite := by
  classical
  change Set.Finite {x : Σ C, Fin (horder.clusterSize C) | ¬ horder.exteriorGroup x.1}
  simpa only [exteriorGroup,not_lt] using
    finite_grouped_anchor_abs_le (fun C => horder.clusterSize C) horder.clusterSize_le
      horder.signedAnchorCoordinate hd (fun C E hne => horder.signedAnchorCoordinate_separated hne)
      ((q:ℝ)*d+1)

/-- Any whole group containing the physical origin is excised before using
signed-square ray coordinates. No artificial order-zero Dirac is involved. -/
theorem not_exterior_of_point_eq_zero (hd : 0 < d)
    (C : CanonicalClusterIndex S.signedSquareImage d) (i : Fin (horder.clusterSize C))
    (hi : (horder.signedGrouping.point C i : ℝ)=0) : ¬ horder.exteriorGroup C := by
  have hmin := horder.signedGrouping.abs_realNodes_anchor_le C i
  change |horder.signedAnchorCoordinate C| ≤ |signedSquare (horder.signedGrouping.point C i)| at hmin
  rw [hi] at hmin
  simp only [signedSquare,abs_zero,mul_zero] at hmin
  have hD : 0 ≤ (q:ℝ)*d := by positivity
  intro hC
  dsimp [exteriorGroup] at hC
  linarith

/-- The actual canonical exterior Gram remainder is a compact self-adjoint
operator, with no Bessel or compactness certificate among its assumptions. -/
theorem exists_compact_exteriorGramRemainder (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    ∃ A : CoefficientSpace (Σ C : {C : CanonicalClusterIndex S.signedSquareImage d // horder.exteriorGroup C},
        Fin (horder.clusterSize C.val)) →L[ℂ]
      CoefficientSpace (Σ C : {C : CanonicalClusterIndex S.signedSquareImage d // horder.exteriorGroup C},
        Fin (horder.clusterSize C.val)),
      IsSelfAdjoint A ∧ IsCompactOperator A ∧ ∀ i j,
        inner ℂ (coefficientAtom i) (A (coefficientAtom j)) =
          horder.signedGrouping.gramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨i.1.val,i.2⟩ ⟨j.1.val,j.2⟩ -
          horder.signedGrouping.universalGroupedGramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨i.1.val,i.2⟩ ⟨j.1.val,j.2⟩ := by
  apply horder.signedGrouping.exists_compact_gramRemainder_on_tail horder.exteriorGroup q m hm
    (fun C => horder.exteriorRay C.val) (fun C => horder.exteriorRay_sq C.val)
    ((q:ℝ)*d) d (by positivity) hd
    (fun C => horder.clusterSize_le C.val)
    (fun C => horder.exterior_anchorMagnitude_ge_one hd C.val C.property)
    (fun C => horder.exterior_magnitudeNodes_mem hd C.val C.property)
  intro C E hne
  exact horder.signedAnchorCoordinate_separated (Subtype.coe_injective.ne hne)

/-- Genuine global universal grouped Bessel analysis, including all central
groups, from the actual model kernel and canonical geometry. -/
def universalGroupedBesselAnalysis (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    BesselAnalysis (horder.signedGrouping.universalAtom m (by have := (le_max_left _ _).trans hm; omega)) := by
  classical
  exact horder.signedGrouping.universalBesselAnalysisOfGeometry q m hm ((q:ℝ)*d) d (by positivity) hd
    horder.signedAnchorCoordinate horder.clusterSize_le (horder.signedGrouping_node_anchor_distance hd)
    (fun _ _ hne => horder.signedAnchorCoordinate_separated hne)

/-- Exact inclusion of the whole exterior-group coordinates in the original
grouped coordinate index. -/
def exteriorIndexEmbedding :
    (Σ C : {C : CanonicalClusterIndex S.signedSquareImage d // horder.exteriorGroup C},
      Fin (horder.clusterSize C.val)) ↪ horder.signedGrouping.Index where
  toFun x := ⟨x.1.val,x.2⟩
  inj' := by
    intro x y h
    apply (horder.signedGrouping.selectedGroupIndexEquiv horder.exteriorGroup).injective
    exact Subtype.ext h

/-- The actual Hermite grouped tail is Bessel: its model is Bessel and their
proved compact Gram remainder is, in particular, bounded. -/
def exteriorGroupedBesselAnalysis (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    BesselAnalysis (fun x => horder.signedGrouping.atom m
      (by have := (le_max_left _ _).trans hm; omega) (horder.exteriorIndexEmbedding x)) := by
  classical
  apply Classical.choice
  obtain ⟨A,_hA,_hcompact,hentry⟩ := horder.exists_compact_exteriorGramRemainder hd m hm
  exact ⟨BesselAnalysis.of_gramDifference _ _
    ((horder.universalGroupedBesselAnalysis hd m hm).reindex horder.exteriorIndexEmbedding) A hentry⟩

set_option maxHeartbeats 1000000 in
/-- All actual canonical grouped atoms form a Bessel family. The finite
central complement is restored with its original physical Hilbert vectors. -/
def actualGroupedBesselAnalysis (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    BesselAnalysis (horder.signedGrouping.atom m (by have := (le_max_left _ _).trans hm; omega)) := by
  classical
  let P : horder.signedGrouping.Index → Prop := fun x => horder.exteriorGroup x.1
  let e : {x : horder.signedGrouping.Index // P x} ↪
      (Σ C : {C : CanonicalClusterIndex S.signedSquareImage d // horder.exteriorGroup C},
        Fin (horder.clusterSize C.val)) :=
    ⟨fun x => ⟨⟨x.val.1,x.property⟩,x.val.2⟩,by
      intro x y h
      apply Subtype.ext
      exact congrArg horder.exteriorIndexEmbedding h⟩
  let B := (horder.exteriorGroupedBesselAnalysis hd m hm).reindex e
  exact BesselAnalysis.of_finite_complement (horder.signedGrouping.atom m
    (by have := (le_max_left _ _).trans hm; omega)) P (horder.finite_non_exterior_coordinates hd) B

/-- Actual full Hermite grouped coefficient Gram operator. -/
def actualGroupedGramOperator (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    CoefficientSpace horder.signedGrouping.Index →L[ℂ] CoefficientSpace horder.signedGrouping.Index :=
  coefficientGram (horder.actualGroupedBesselAnalysis hd m hm).synthesis

/-- Actual full universal grouped coefficient Gram operator. -/
def universalGroupedGramOperator (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    CoefficientSpace horder.signedGrouping.Index →L[ℂ] CoefficientSpace horder.signedGrouping.Index :=
  coefficientGram (horder.universalGroupedBesselAnalysis hd m hm).synthesis

set_option maxHeartbeats 1000000 in
/-- Full actual canonical Hermite-minus-universal grouped Gram compactness.
The finite central rows and columns are restored only after both original
families have genuine bounded synthesis operators. -/
theorem actualGroupedGram_sub_universal_isCompact (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    IsCompactOperator (horder.actualGroupedGramOperator hd m hm-horder.universalGroupedGramOperator hd m hm) := by
  classical
  let F := (horder.finite_non_exterior_coordinates hd).toFinset
  have hF (i : horder.signedGrouping.Index) : i ∉ F ↔ horder.exteriorGroup i.1 := by
    simp only [F,Set.Finite.mem_toFinset,Set.mem_ofPred_eq,not_not]
  let e : {i : horder.signedGrouping.Index // i ∉ F} ↪
      (Σ C : {C : CanonicalClusterIndex S.signedSquareImage d // horder.exteriorGroup C},
        Fin (horder.clusterSize C.val)) :=
    ⟨fun i => ⟨⟨i.val.1,(hF i.val).mp i.property⟩,i.val.2⟩,by
      intro i j hij
      apply Subtype.ext
      exact congrArg horder.exteriorIndexEmbedding hij⟩
  let U := ((coefficientBesselAnalysis).reindex e).synthesis
  obtain ⟨A,_hA,hcompact,hentry⟩ := horder.exists_compact_exteriorGramRemainder hd m hm
  let T := horder.actualGroupedGramOperator hd m hm-horder.universalGroupedGramOperator hd m hm
  apply isCompactOperator_of_compact_tailRestriction T F
  have heq : (tailCoefficientEmbedding F).adjoint ∘L T ∘L tailCoefficientEmbedding F =
      U.adjoint ∘L A ∘L U := by
    apply coefficientOperator_eq_of_entries
    intro i j
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
      tailCoefficientEmbedding_coefficientAtom]
    have hU (i : {i : horder.signedGrouping.Index // i ∉ F}) : U (coefficientAtom i)=coefficientAtom (e i) :=
      BesselAnalysis.synthesis_coefficientAtom _ i
    rw [hU,hU,hentry]
    change inner ℂ (coefficientAtom i.val)
      ((horder.actualGroupedGramOperator hd m hm-horder.universalGroupedGramOperator hd m hm) (coefficientAtom j.val)) = _
    simp only [sub_apply,inner_sub_right,actualGroupedGramOperator,universalGroupedGramOperator,
      coefficientGram,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
      BesselAnalysis.synthesis_coefficientAtom]
    rfl
  rw [heq]
  exact (hcompact.comp_clm U).clm_comp U.adjoint

end BoundedClusterOrder

end

end MeyerGeneralProblem
