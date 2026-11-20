module

public import MeyerGeneralProblem.Sampling.CanonicalGraphData
public import MeyerGeneralProblem.Sampling.KNSGraphPointBound
public import MeyerGeneralProblem.Gram.CanonicalGroupedGram

@[expose] public section

/-!
# Finite-central forward canonical-prefix bound

This module proves the finite-central part of the canonical sampler. It uses
the forward values-to-divided-differences map on each original ordered
canonical cluster and the pointwise bound for the chosen actual graph
representative. It never invokes the reverse `canonicalDataValueMap_sq_le`
estimate and never promotes an almost-everywhere identity to a pointwise one.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set MeasureTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace BoundedClusterOrder

variable (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
  (ho : BoundedClusterOrder S.signedSquareImage d q)

def graphPointBoundConstant : ℝ :=
  4 * ‖memLp_inverse_one_add_abs.toLp‖

def canonicalForwardNorm
    (C : CanonicalClusterIndex S.signedSquareImage d) : ℝ :=
  ‖(ho.canonicalValuesEquiv C).toContinuousLinearEquiv.toContinuousLinearMap‖

private def allAnchorWeight (k : ℕ)
    (C : CanonicalClusterIndex S.signedSquareImage d) : ℝ :=
  ∑ i : Fin (ho.clusterSize C),
    (1 + Real.sqrt |ho.realClusterNode C i|) ^ (2 * k - 1)

private def finiteCanonicalForwardConstant (k : ℕ)
    (F : Finset (CanonicalClusterIndex S.signedSquareImage d)) : ℝ :=
  1 + ∑ C ∈ F,
    allAnchorWeight S ho k C *
      ((ho.clusterSize C : ℝ) * canonicalForwardNorm S ho C ^ 2 *
        graphPointBoundConstant ^ 2)

/-- On one actual cluster, original canonical prefix data are the forward
values-to-divided-differences transform of the representative's values at the
unique physical preimages. The order is the original increasing canonical
order. -/
theorem canonicalPrefixData_representative_eq_forward_values
    {k : ℕ} (v : KNSGraphSpace k)
    (C : CanonicalClusterIndex S.signedSquareImage d) :
    ho.canonicalPrefixData
        (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C =
      ho.canonicalValuesEquiv C (fun i =>
        KNSGraphSpace.representative k v
          (S.signedSquareSubtypeEquiv.symm (ho.orderedClusterNode C i))) := by
  funext j
  rw [canonicalPrefixData, analyticDividedDifference_eq_dividedDifferences
    (ho.realClusterNode C) (ho.realClusterNode_strictMono C).injective]
  congr 2
  funext i
  exact S.physicalSignedSquarePullbackMap_on_carrier _ (ho.orderedClusterNode C i)

/-- The unweighted squared original-prefix energy of one fixed canonical
cluster is bounded by its genuine forward Newton operator norm and the uniform
graph point bound. -/
theorem canonicalPrefixData_representative_class_sq_le
    {k : ℕ} (hk : 1 ≤ k) (v : KNSGraphSpace k)
    (C : CanonicalClusterIndex S.signedSquareImage d) :
    ∑ j, ‖ho.canonicalPrefixData
        (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j‖ ^ 2 ≤
      (ho.clusterSize C : ℝ) * canonicalForwardNorm S ho C ^ 2 *
        graphPointBoundConstant ^ 2 * ‖v‖ ^ 2 := by
  let values : Fin (ho.clusterSize C) → ℂ := fun i =>
    KNSGraphSpace.representative k v
      (S.signedSquareSubtypeEquiv.symm (ho.orderedClusterNode C i))
  let L := (ho.canonicalValuesEquiv C).toContinuousLinearEquiv.toContinuousLinearMap
  let P := graphPointBoundConstant
  have hP : 0 ≤ P := by
    dsimp [P, graphPointBoundConstant]
    positivity
  have hvalues : ‖values‖ ≤ P * ‖v‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hP (norm_nonneg v))).mpr
    intro i
    exact KNSGraphSpace.norm_representative_le_graph hk v _
  have hprefix :
      ‖ho.canonicalPrefixData
          (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C‖ ≤
        ‖L‖ * (P * ‖v‖) := by
    rw [ho.canonicalPrefixData_representative_eq_forward_values S v C]
    change ‖L values‖ ≤ _
    exact (L.le_opNorm values).trans
      (mul_le_mul_of_nonneg_left hvalues (norm_nonneg L))
  calc
    _ ≤ ∑ _j : Fin (ho.clusterSize C),
        ‖ho.canonicalPrefixData
          (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_le_pi_norm
          (ho.canonicalPrefixData
            (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C) j) 2
    _ = (ho.clusterSize C : ℝ) *
        ‖ho.canonicalPrefixData
          (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C‖ ^ 2 := by
      simp
    _ ≤ (ho.clusterSize C : ℝ) * (‖L‖ * (P * ‖v‖)) ^ 2 := by
      gcongr
    _ = (ho.clusterSize C : ℝ) * canonicalForwardNorm S ho C ^ 2 *
        graphPointBoundConstant ^ 2 * ‖v‖ ^ 2 := by
      dsimp [L, P, canonicalForwardNorm]
      ring

/-- A finite family of whole canonical clusters has one positive
carrier/geometry-dependent forward sampling constant, fixed before every
actual anchor choice and every graph vector. -/
theorem exists_finite_canonicalPrefixData_representative_energy_bound
    (k : ℕ) (hk : 1 ≤ k)
    (F : Finset (CanonicalClusterIndex S.signedSquareImage d)) :
    ∃ A : ℝ, 0 < A ∧
      ∀ anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
          Fin (ho.clusterSize C),
      ∀ v : KNSGraphSpace k,
        ∑ C ∈ F,
          (1 + Real.sqrt |ho.realClusterNode C (anchor C)|) ^ (2 * k - 1) *
            (∑ j, ‖ho.canonicalPrefixData
              (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j‖ ^ 2) ≤
          A * ‖v‖ ^ 2 := by
  let A := finiteCanonicalForwardConstant S ho k F
  have hall_nonneg (C : CanonicalClusterIndex S.signedSquareImage d) :
      0 ≤ allAnchorWeight S ho k C := by
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hclass_nonneg (C : CanonicalClusterIndex S.signedSquareImage d) :
      0 ≤ (ho.clusterSize C : ℝ) * canonicalForwardNorm S ho C ^ 2 *
        graphPointBoundConstant ^ 2 := by positivity
  have hsum_nonneg : 0 ≤ ∑ C ∈ F,
      allAnchorWeight S ho k C *
        ((ho.clusterSize C : ℝ) * canonicalForwardNorm S ho C ^ 2 *
          graphPointBoundConstant ^ 2) := by
    exact Finset.sum_nonneg (fun C _ =>
      mul_nonneg (hall_nonneg C) (hclass_nonneg C))
  refine ⟨A, by dsimp [A, finiteCanonicalForwardConstant]; linarith, ?_⟩
  intro anchor v
  have hweight (C : CanonicalClusterIndex S.signedSquareImage d) :
      (1 + Real.sqrt |ho.realClusterNode C (anchor C)|) ^ (2 * k - 1) ≤
        allAnchorWeight S ho k C := by
    dsimp [allAnchorWeight]
    exact Finset.single_le_sum
      (f := fun i : Fin (ho.clusterSize C) =>
        (1 + Real.sqrt |ho.realClusterNode C i|) ^ (2 * k - 1))
      (fun i _ => by positivity) (Finset.mem_univ (anchor C))
  calc
    _ ≤ ∑ C ∈ F,
        allAnchorWeight S ho k C *
          (((ho.clusterSize C : ℝ) * canonicalForwardNorm S ho C ^ 2 *
            graphPointBoundConstant ^ 2) * ‖v‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro C hC
      apply mul_le_mul (hweight C)
        (ho.canonicalPrefixData_representative_class_sq_le S hk v C)
        (Finset.sum_nonneg (fun j _ => sq_nonneg _))
        (hall_nonneg C)
    _ = (∑ C ∈ F,
        allAnchorWeight S ho k C *
          ((ho.clusterSize C : ℝ) * canonicalForwardNorm S ho C ^ 2 *
            graphPointBoundConstant ^ 2)) * ‖v‖ ^ 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro C hC
      ring
    _ ≤ A * ‖v‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖v‖)
      dsimp [A, finiteCanonicalForwardConstant]
      linarith

/-- The canonical finite band supplied by the existing whole-cluster
finiteness theorem is an immediate specialization of the finite-family
forward bound. -/
theorem exists_signedAnchorCoordinate_band_canonicalPrefixData_representative_energy_bound
    (k : ℕ) (hk : 1 ≤ k) (hd : 0 < d) (R : ℝ) :
    ∃ A : ℝ, 0 < A ∧
      ∀ anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
          Fin (ho.clusterSize C),
      ∀ v : KNSGraphSpace k,
        ∑ C ∈ (ho.finite_signedAnchorCoordinate_band hd R).toFinset,
          (1 + Real.sqrt |ho.realClusterNode C (anchor C)|) ^ (2 * k - 1) *
            (∑ j, ‖ho.canonicalPrefixData
              (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j‖ ^ 2) ≤
          A * ‖v‖ ^ 2 :=
  ho.exists_finite_canonicalPrefixData_representative_energy_bound S k hk
    (ho.finite_signedAnchorCoordinate_band hd R).toFinset

end BoundedClusterOrder

end

end MeyerGeneralProblem
