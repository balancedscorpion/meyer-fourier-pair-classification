module

public import MeyerGeneralProblem.Carrier.CanonicalClusterGeometry
public import MeyerGeneralProblem.Sampling.GroupedDensityRiesz

@[expose] public section

/-!
# The genuine canonical grouped exponential Riesz theorem

Canonical groups are exact connected components of the strict d-gap relation.
Nodes are increasing, and coordinates are every initial segment. The quotient
enumeration covers every carrier point exactly once. Finite whole-group tests
with arbitrary coefficients cover every finitely supported coordinate vector.
Both constants are selected before those tests and before every internal gap.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory

/-- The canonical initial-prefix grouped exponentials form a Riesz sequence
on [-W,W] whenever the exact numerical upper density is below 2W. The formula
uses all coefficients on arbitrary finite sets of distinct canonical groups,
which is the finite-synthesis characterization on the full dependent index. -/
theorem groupedExponential_isRieszSequence
    (S : LocallyFiniteCarrier) {q : ℕ} {d W : ℝ}
    (horder : BoundedClusterOrder S d q) (hd : 0 < d) (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S < ENNReal.ofReal (2*W)) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ n
      (groups : Fin n ↪ CanonicalClusterIndex S d)
      (c : (g : Fin n) → Fin (horder.clusterSize (groups g)) → ℂ),
      A * (∑ g, ∑ j, ‖c g j‖^2) ≤
          ∫ t : ℝ in Set.Icc (-W) W,
            ‖∑ g, ∑ j, c g j *
              groupedExponentialInitial (horder.realClusterNode (groups g)) j t‖^2 ∧
      (∫ t : ℝ in Set.Icc (-W) W,
            ‖∑ g, ∑ j, c g j *
              groupedExponentialInitial (horder.realClusterNode (groups g)) j t‖^2) ≤
          B * ∑ g, ∑ j, ‖c g j‖^2 := by
  obtain ⟨A, hA, hlower⟩ := exists_groupedExponentialInitial_uniform_lower_of_upperDensity_lt
    S q hW hd (show 0 ≤ (q:ℝ)*d by positivity) hS
  obtain ⟨B, hB, hupper⟩ := exists_groupedExponentialInitial_uniform_upper q hW.le hd
  refine ⟨A, B, hA, hB, ?_⟩
  intro n groups c
  constructor
  · exact hlower n (fun g => horder.clusterSize (groups g))
      (fun g => horder.clusterSize_pos (groups g)) (fun g => horder.clusterSize_le (groups g))
      (fun g => horder.realClusterNode (groups g))
      (fun g => (horder.realClusterNode_strictMono (groups g)).injective)
      (fun g => horder.realClusterNode_mem (groups g))
      (fun g => horder.realClusterNode_diameter hd (groups g))
      (fun g h hgh => horder.realClusterNode_separated (groups.injective.ne hgh)) c
  · exact hupper n (fun g => horder.clusterSize (groups g))
      (fun g => horder.clusterSize_pos (groups g)) (fun g => horder.clusterSize_le (groups g))
      (fun g => horder.realClusterNode (groups g))
      (fun g => horder.clusterLower (groups g)) (fun g => horder.clusterUpper (groups g))
      (fun g => horder.realClusterNode_mem_hull (groups g))
      (fun g h hgh x hx y hy => horder.cluster_hulls_separated hd
        (groups.injective.ne hgh) hx hy) c

end

end MeyerGeneralProblem
