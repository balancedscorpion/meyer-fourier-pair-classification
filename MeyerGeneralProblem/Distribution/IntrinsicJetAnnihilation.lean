module

public import MeyerGeneralProblem.Distribution.BroadCauchySupportJets
public import MeyerGeneralProblem.Distribution.DiscreteSupportCounting

@[expose] public section

/-!
# Annihilation by vanishing jets on intrinsic support

Compact-test jet formulas and Schwartz cutoff density give multiplication
by a temperate function that vanishes through the distributional order.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Distribution Filter MeasureTheory Set
open scoped ContDiff SchwartzMap Topology

/-- A temperate multiplier with the required zero jets on the intrinsic
support annihilates a distribution of the corresponding Schwartz order. -/
theorem temperedDistribution_smulLeft_eq_zero_of_intrinsic_zero_jets
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : DistributionSupportedOn S.carrier T) (weight q : ℕ)
    (hOrder : HasSchwartzSeminormBound T weight q)
    (r : ℝ → ℂ) (hr : r.HasTemperateGrowth)
    (hJets : ∀ a ∈ dsupport T, ∀ j ≤ q, iteratedDeriv j r a = 0) :
    TemperedDistribution.smulLeftCLM ℂ r T = 0 := by
  classical
  let U := S.restrict (dsupport T) (dsupport_subset_of_discrete_support S T hT)
  have hU : DistributionSupportedOn U.carrier T :=
    distributionSupportedOn_dsupport_of_discrete_support S T hT
  obtain ⟨c, hc⟩ := supportedOn_compact_jet_formula_of_schwartzSeminormBound U T weight q hU hOrder
  let A := TemperedDistribution.smulLeftCLM ℂ r T
  have hCompact (g : SchwartzMap ℝ ℂ) (hg : HasCompactSupport (g : ℝ → ℂ)) : A g = 0 := by
    let f := SchwartzMap.smulLeftCLM ℂ r g
    have hf : HasCompactSupport (f : ℝ → ℂ) := by
      apply hg.of_isClosed_subset (isClosed_tsupport _)
      exact (SchwartzMap.tsupport_smulLeftCLM_subset r g).trans inter_subset_left
    have hJets' (a : U.subtype) (j : ℕ) (hj : j ≤ q) :
        iteratedDeriv j (f : ℝ → ℂ) (a : ℝ) = 0 := by
      have he : (f : ℝ → ℂ) = fun x => r x * g x := by
        funext x
        rw [show f x = (SchwartzMap.smulLeftCLM ℂ r g) x from rfl,
          SchwartzMap.smulLeftCLM_apply_apply hr, smul_eq_mul]
      rw [he, iteratedDeriv_fun_mul
        ((hr.1.of_le (by simp : (j : ℕ∞ω) ≤ ∞)).contDiffAt)
        ((g.smooth (j : ℕ∞)).contDiffAt)]
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : i ≤ q := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hj
      rw [hJets a a.property i hi', mul_zero, zero_mul]
    obtain ⟨R, hR⟩ := hf.isBounded.subset_ball 0
    let E : Set U.subtype := Subtype.val ⁻¹' (U.carrier ∩ Icc (-R) R)
    have hE : E.Finite :=
      (U.finite_inter_Icc (-R) R).preimage (Set.injOn_of_injective Subtype.val_injective)
    have hAway (a : U.subtype) (ha : a ∉ hE.toFinset) : (f : ℝ → ℂ) =ᶠ[𝓝 (a : ℝ)] 0 := by
      have hOut : (a : ℝ) ∉ tsupport (f : ℝ → ℂ) := by
        intro hm
        have hr : |(a : ℝ)| < R := by
          simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hR hm
        exact ha (hE.mem_toFinset.mpr ⟨a.property, abs_le.mp hr.le⟩)
      filter_upwards [(isClosed_tsupport (f : ℝ → ℂ)).isOpen_compl.mem_nhds hOut] with x hx
      exact image_eq_zero_of_notMem_tsupport hx
    change T f = 0
    rw [hc f hf hE.toFinset hAway]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro j hj
    rw [hJets' a j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), mul_zero]
  ext g
  change A g = 0
  have hlim : Tendsto (fun N => A (compactSchwartzApproximation N g)) atTop (𝓝 (A g)) :=
    (A.continuous.tendsto g).comp (compactSchwartzApproximation_tendsto g)
  have h0 (N : ℕ) : A (compactSchwartzApproximation N g) = 0 :=
    hCompact _ (compactSchwartzApproximation_hasCompactSupport N g)
  have hlimit : Tendsto (fun N => A (compactSchwartzApproximation N g)) atTop (𝓝 0) := by
    simp only [h0, tendsto_const_nhds]
  exact tendsto_nhds_unique hlim hlimit

end
end MeyerGeneralProblem
