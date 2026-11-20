module

public import MeyerGeneralProblem.Sampling.SignedSquareNormalizedReciprocal
public import MeyerGeneralProblem.Sampling.KNSGraphChart
public import MeyerGeneralProblem.Sampling.CanonicalGraphData
public import MeyerGeneralProblem.Sampling.GroupedSpectralGap
public import MeyerGeneralProblem.Gram.CanonicalGroupedGram
public import MeyerGeneralProblem.Interpolation.CanonicalGlobalInterpolation

@[expose] public section

namespace MeyerGeneralProblem.CanonicalPrefixTail
noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators
open SignedSquareNormalizedReciprocal

theorem multiplier_mul_chart_eq {k : ℕ} {c ε s : ℝ}
    (hs : 4 ≤ ε * s) (f : ℝ → ℂ) :
    multiplier k c ε s * signedSquareCutoffChart k 2 ε f (ε * s) =
      (anchorWeight k c : ℂ) * f (ε * Real.sqrt (ε * s)) := by
  rw [multiplier, reciprocalScalar_raw k c (by linarith),
    signedSquareCutoffChart_eq k 2 ε f (by norm_num at hs ⊢; exact hs)]
  simp only [signedSquareWeightedChart, signedSquareChartMonomial,
    iteratedDeriv_zero, Algebra.smul_def, map_mul, mul_one]
  change ((anchorWeight k c : ℂ) * ((ε * s) ^ (-exponent k) : ℝ)) *
      (((ε * s) ^ exponent k : ℝ) * f (ε * Real.sqrt (ε * s))) = _
  have ht : 0 < ε * s := by linarith
  have hp : (ε * s) ^ (-exponent k) * (ε * s) ^ exponent k = 1 := by
    rw [← Real.rpow_add ht]
    simp
  have hpC : (((ε * s) ^ (-exponent k) : ℝ) : ℂ) *
      (((ε * s) ^ exponent k : ℝ) : ℂ) = 1 := by exact_mod_cast hp
  calc
    ((anchorWeight k c : ℂ) * ((ε * s) ^ (-exponent k) : ℝ)) *
        (((ε * s) ^ exponent k : ℝ) * f (ε * Real.sqrt (ε * s))) =
      (anchorWeight k c : ℂ) *
        (((ε * s) ^ (-exponent k) : ℝ) * ((ε * s) ^ exponent k : ℝ)) *
          f (ε * Real.sqrt (ε * s)) := by ring
    _ = (anchorWeight k c : ℂ) * f (ε * Real.sqrt (ε * s)) := by rw [hpC]; simp

theorem anchorWeight_magnitude_eq_canonicalGraphWeight
    {S : LocallyFiniteCarrier} {d : ℝ} {q k : ℕ}
    (ho : BoundedClusterOrder S.signedSquareImage d q) (hd : 0<d)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
    (C : CanonicalClusterIndex S.signedSquareImage d) (hC : ho.exteriorGroup C) :
    anchorWeight k
        (ho.signedGrouping.magnitudeNodes (ho.exteriorRay C) C (anchor C)) =
      ho.canonicalGraphWeight k anchor C := by
  have hε : (ho.exteriorRay C)^2=1 := ho.exteriorRay_sq C
  have hc := ho.exterior_magnitudeNodes_mem hd C hC (anchor C)
  have hc0 : 0≤ho.signedGrouping.magnitudeNodes (ho.exteriorRay C) C (anchor C) :=
    (show 0≤ho.signedGrouping.anchorMagnitude (ho.exteriorRay C) C by
      linarith [ho.exterior_anchorMagnitude_ge_one hd C hC]).trans hc.1
  have hr := congrFun
    (ho.signedGrouping.realNodes_eq_sign_magnitudeNodes (ho.exteriorRay C) hε C) (anchor C)
  have hεabs : |ho.exteriorRay C|=1 := by
    rcases sq_eq_one_iff.mp hε with h | h <;> rw [h] <;> norm_num
  have habs : |ho.realClusterNode C (anchor C)| =
      ho.signedGrouping.magnitudeNodes (ho.exteriorRay C) C (anchor C) := by
    rw [← ho.signedGrouping_realNodes C (anchor C), hr, abs_mul, hεabs, one_mul,
      abs_of_nonneg hc0]
  unfold anchorWeight BoundedClusterOrder.canonicalGraphWeight
  rw [habs]

theorem multiplier_chart_node_eq_weighted_raw
    {S : LocallyFiniteCarrier} {d : ℝ} {q k : ℕ}
    (ho : BoundedClusterOrder S.signedSquareImage d q) (hd : 0<d)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
    (v : KNSGraphSpace k) (C : CanonicalClusterIndex S.signedSquareImage d)
    (hC : ho.exteriorGroup C) (hA : 4≤|ho.signedAnchorCoordinate C|)
    (i : Fin (ho.clusterSize C)) :
    multiplier k (ho.signedGrouping.magnitudeNodes (ho.exteriorRay C) C (anchor C))
        (ho.exteriorRay C) (ho.realClusterNode C i) *
        signedSquareCutoffChart k 2 (ho.exteriorRay C) (KNSGraphSpace.representative k v)
          (ho.exteriorRay C*ho.realClusterNode C i) =
      (ho.canonicalGraphWeight k anchor C : ℂ)*
        S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)
          (ho.realClusterNode C i) := by
  have hε : (ho.exteriorRay C)^2=1 := ho.exteriorRay_sq C
  have hi := ho.exterior_magnitudeNodes_mem hd C hC i
  have hi0 : 0≤ho.signedGrouping.magnitudeNodes (ho.exteriorRay C) C i :=
    (show 0≤ho.signedGrouping.anchorMagnitude (ho.exteriorRay C) C by
      linarith [ho.exterior_anchorMagnitude_ge_one hd C hC]).trans hi.1
  have hσ : ho.exteriorRay C*ho.realClusterNode C i =
      ho.signedGrouping.magnitudeNodes (ho.exteriorRay C) C i := by
    dsimp [OrderedCarrierGrouping.magnitudeNodes]
    rw [ho.signedGrouping_realNodes C i]
  have hp := ho.signedGrouping.point_eq_sign_sqrt_magnitudeNodes
    (ho.exteriorRay C) hε C i hi0
  have hpoint := congrArg (KNSGraphSpace.representative k v) hp
  have hraw :
      S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)
          (ho.realClusterNode C i) =
        KNSGraphSpace.representative k v (ho.signedGrouping.point C i) := by
    change S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)
          (ho.orderedClusterNode C i) =
      KNSGraphSpace.representative k v
        (S.signedSquareSubtypeEquiv.symm (ho.orderedClusterNode C i))
    exact S.physicalSignedSquarePullbackMap_on_carrier
      (KNSGraphSpace.representative k v) (ho.orderedClusterNode C i)
  rw [multiplier_mul_chart_eq (f := KNSGraphSpace.representative k v) (by
    rw [hσ]
    exact hA.trans (by simpa only [ho.exterior_anchorMagnitude] using hi.1))]
  rw [hσ, ← hpoint, ← hraw]
  rw [anchorWeight_magnitude_eq_canonicalGraphWeight ho hd anchor C hC]

/-- One actual exterior cluster's weighted original prefixes are bounded by
the original-order prefixes of its reflected smooth chart. No inverse internal
gap enters, and the arbitrary chosen graph anchor need not minimize modulus. -/
theorem weighted_original_prefix_le_chart_prefix_sum_of_bound
    {S : LocallyFiniteCarrier} {d : ℝ} {q k : ℕ}
    (ho : BoundedClusterOrder S.signedSquareImage d q) (hd : 0<d)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
    (v : KNSGraphSpace k) (C : CanonicalClusterIndex S.signedSquareImage d)
    (hC : ho.exteriorGroup C) (hA : 4≤|ho.signedAnchorCoordinate C|)
    {M : ℝ} (hM : 0≤M)
    (hbound : ∀ s : ℝ,
      ho.exteriorRay C*s ∈ Set.Icc |ho.signedAnchorCoordinate C|
          (|ho.signedAnchorCoordinate C|+(q:ℝ)*d) →
        ∀ r≤q, ‖iteratedDeriv r
          (multiplier k
            (ho.signedGrouping.magnitudeNodes (ho.exteriorRay C) C (anchor C))
            (ho.exteriorRay C)) s‖≤M)
    (j : Fin (ho.clusterSize C)) :
    ‖(ho.canonicalGraphWeight k anchor C : ℂ) *
        ho.canonicalPrefixData
          (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j‖ ≤
      M * ∑ r ∈ Finset.range (j.val+1),
        ‖analyticDividedDifference
          (finiteNodeSequence (ho.realClusterNode C)) r
          (fun s => signedSquareCutoffChart k 2 (ho.exteriorRay C)
            (KNSGraphSpace.representative k v) (ho.exteriorRay C*s))‖ := by
  let nodes := finiteNodeSequence (ho.realClusterNode C)
  let chart : ℝ → ℂ := fun s => signedSquareCutoffChart k 2 (ho.exteriorRay C)
    (KNSGraphSpace.representative k v) (ho.exteriorRay C*s)
  let mult : ℝ → ℂ := multiplier k
    (ho.signedGrouping.magnitudeNodes (ho.exteriorRay C) C (anchor C))
    (ho.exteriorRay C)
  have hjq : j.val≤q := j.isLt.le.trans (ho.clusterSize_le C)
  have hdistinct : ∀ a≤j.val, ∀ b≤j.val, a≠b → nodes a≠nodes b := by
    intro a ha b hb hab
    have han : a<ho.clusterSize C := ha.trans_lt j.isLt
    have hbn : b<ho.clusterSize C := hb.trans_lt j.isLt
    simp only [nodes, finiteNodeSequence, dite_eq_left han, dite_eq_left hbn]
    intro heq
    apply hab
    exact congrArg Fin.val ((ho.realClusterNode_strictMono C).injective heq)
  have heq : analyticDividedDifference nodes j.val (fun s => chart s*mult s) =
      (ho.canonicalGraphWeight k anchor C : ℂ)*
        analyticDividedDifference nodes j.val
          (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) := by
    calc
      _ = analyticDividedDifference nodes j.val (fun s =>
          (ho.canonicalGraphWeight k anchor C : ℂ)*
            S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v) s) := by
        apply analyticDividedDifference_congr_values_of_distinct _ _ _ _ hdistinct
        intro a ha
        have han : a<ho.clusterSize C := ha.trans_lt j.isLt
        simp only [nodes, finiteNodeSequence, dite_eq_left han, chart, mult]
        rw [mul_comm]
        exact multiplier_chart_node_eq_weighted_raw ho hd anchor v C hC hA ⟨a,han⟩
      _ = _ := analyticDividedDifference_const_mul_complex _ _ _ _
  have hg : ContDiff ℝ j.val mult :=
    (multiplier_contDiff k
      (ho.signedGrouping.magnitudeNodes (ho.exteriorRay C) C (anchor C))
      (ho.exteriorRay C)).of_le (by simp)
  have hb : ‖analyticDividedDifference nodes j.val (fun s => chart s*mult s)‖ ≤
      M*∑ r∈Finset.range (j.val+1), ‖analyticDividedDifference nodes r chart‖ := by
    rcases sq_eq_one_iff.mp (ho.exteriorRay_sq C) with hε | hε
    · have hnodes : ∀ a≤j.val, nodes a∈Set.Icc |ho.signedAnchorCoordinate C|
          (|ho.signedAnchorCoordinate C|+(q:ℝ)*d) := by
        intro a ha
        have han : a<ho.clusterSize C := ha.trans_lt j.isLt
        have hm := ho.exterior_magnitudeNodes_mem hd C hC ⟨a,han⟩
        rw [ho.exterior_anchorMagnitude] at hm
        simp only [OrderedCarrierGrouping.magnitudeNodes, hε, one_mul] at hm
        rw [ho.signedGrouping_realNodes C ⟨a,han⟩] at hm
        simpa only [nodes, finiteNodeSequence, dite_eq_left han, one_mul] using hm
      exact norm_analyticDividedDifference_mul_le_of_derivative_bound nodes j.val
        hdistinct chart hg hM hnodes (by
          intro r hr x hx
          exact hbound x (by simpa only [hε,one_mul] using hx) r (hr.trans hjq))
    · have hnodes : ∀ a≤j.val, nodes a∈Set.Icc
          (-(|ho.signedAnchorCoordinate C|+(q:ℝ)*d)) (-|ho.signedAnchorCoordinate C|) := by
        intro a ha
        have han : a<ho.clusterSize C := ha.trans_lt j.isLt
        have hm := ho.exterior_magnitudeNodes_mem hd C hC ⟨a,han⟩
        rw [ho.exterior_anchorMagnitude] at hm
        simp only [OrderedCarrierGrouping.magnitudeNodes, hε, neg_one_mul] at hm
        rw [ho.signedGrouping_realNodes C ⟨a,han⟩] at hm
        simp only [nodes, finiteNodeSequence, dite_eq_left han] at hm ⊢
        constructor <;> linarith [hm.1,hm.2]
      exact norm_analyticDividedDifference_mul_le_of_derivative_bound nodes j.val
        hdistinct chart hg hM hnodes (by
          intro r hr x hx
          apply hbound x _ r (hr.trans hjq)
          simp only [hε,neg_one_mul]
          constructor <;> linarith [hx.1,hx.2])
  rw [heq] at hb
  simpa only [BoundedClusterOrder.canonicalPrefixData, nodes, chart] using hb

/-- The reciprocal multiplier theorem supplies one location-independent
constant for every genuine exterior cluster of fixed diameter `q*d`. -/
theorem exists_weighted_original_prefix_tail_cluster_bound
    {S : LocallyFiniteCarrier} {d : ℝ} {q k : ℕ}
    (ho : BoundedClusterOrder S.signedSquareImage d q) (hd : 0<d) (hk : 1≤k) :
    ∃ M>0, ∀
      (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
      (v : KNSGraphSpace k)
      (C : CanonicalClusterIndex S.signedSquareImage d), ho.exteriorGroup C →
      4≤|ho.signedAnchorCoordinate C| → ∀ j : Fin (ho.clusterSize C),
      ‖(ho.canonicalGraphWeight k anchor C : ℂ) *
          ho.canonicalPrefixData
            (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j‖ ≤
        M * ∑ r ∈ Finset.range (j.val+1),
          ‖analyticDividedDifference
            (finiteNodeSequence (ho.realClusterNode C)) r
            (fun s => signedSquareCutoffChart k 2 (ho.exteriorRay C)
              (KNSGraphSpace.representative k v) (ho.exteriorRay C*s))‖ := by
  obtain ⟨M,hM,hbound⟩ := exists_normalized_reciprocal_multiplier_bound
    k q hk ((q:ℝ)*d) (by positivity)
  refine ⟨M,hM,?_⟩
  intro anchor v C hC hA j
  apply weighted_original_prefix_le_chart_prefix_sum_of_bound ho hd anchor v C hC hA hM.le
  intro s hs r hr
  exact ((hbound |ho.signedAnchorCoordinate C|
    (ho.signedGrouping.magnitudeNodes (ho.exteriorRay C) C (anchor C))
    (ho.exteriorRay C) hA (by
      have hc := ho.exterior_magnitudeNodes_mem hd C hC (anchor C)
      simpa only [ho.exterior_anchorMagnitude] using hc)
    (ho.exteriorRay_sq C)).2 s hs).2 r hr

/-- The genuine arbitrary-graph chart estimate and the exterior original-prefix
estimate have constants fixed before the graph vector, ray, cluster and prefix.
This is the clusterwise package; it does not assert the subsequent global sum. -/
theorem exists_original_prefix_tail_chart_package
    {S : LocallyFiniteCarrier} {d : ℝ} {q k : ℕ}
    (ho : BoundedClusterOrder S.signedSquareImage d q) (hd : 0<d)
    (hq : q+1≤k) :
    ∃ M>0, ∃ B>0,
      (∀ (v : KNSGraphSpace k) (ε : ℝ), ε^2=1 →
        ContDiff ℝ q (signedSquareCutoffChart k 2 ε (KNSGraphSpace.representative k v)) ∧
        ∀ r≤q, ∃ hJ : MemLp (iteratedDeriv r
          (signedSquareCutoffChart k 2 ε (KNSGraphSpace.representative k v))) 2,
          ‖hJ.toLp‖^2≤B*‖v‖^2) ∧
      ∀ (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
        (v : KNSGraphSpace k)
        (C : CanonicalClusterIndex S.signedSquareImage d), ho.exteriorGroup C →
        4≤|ho.signedAnchorCoordinate C| → ∀ j : Fin (ho.clusterSize C),
        ‖(ho.canonicalGraphWeight k anchor C : ℂ) *
            ho.canonicalPrefixData
              (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j‖ ≤
          M * ∑ r ∈ Finset.range (j.val+1),
            ‖analyticDividedDifference
              (finiteNodeSequence (ho.realClusterNode C)) r
              (fun s => signedSquareCutoffChart k 2 (ho.exteriorRay C)
                (KNSGraphSpace.representative k v) (ho.exteriorRay C*s))‖ := by
  obtain ⟨M,hM,hprefix⟩ := exists_weighted_original_prefix_tail_cluster_bound
    ho hd (by omega : 1≤k)
  obtain ⟨B,hB,hchart⟩ := KNSGraphChart.exists_graph_chart_bound q k hq
    (R := 2) (by norm_num)
  exact ⟨M,hM,B,hB,hchart,hprefix⟩

end
end MeyerGeneralProblem.CanonicalPrefixTail
