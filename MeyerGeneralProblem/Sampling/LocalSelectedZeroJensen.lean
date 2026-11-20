module

public import Mathlib.Analysis.Complex.JensenFormula

@[expose] public section

/-!
# Local Jensen estimates for a chosen finite set of actual zeros

Only analyticity on a neighborhood of the closed disk is required. The
selected zeros need not exhaust the zero divisor, and zeros on the boundary
are allowed. Unselected divisor terms are nonnegative. The logarithmic
estimate requires a nonzero center; the product estimate treats a zero
center separately and uses the actual logarithmic circle average.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Filter Metric MeromorphicOn
open scoped Topology

private theorem local_one_le_divisor_of_zero {F : ℂ → ℂ} {c z : ℂ} {r : ℝ}
    (hr : 0 < r) (hF : AnalyticOnNhd ℂ F (closedBall c r))
    (hc : F c ≠ 0) (hz : z ∈ closedBall c r) (hzero : F z = 0) :
    (1 : ℤ) ≤ divisor F (closedBall c r) z := by
  have hfinite : analyticOrderAt F z ≠ ⊤ := by
    intro htop
    have heq : F =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
    exact hc ((hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall c r).isPreconnected hz heq) (by simp [hr.le]))
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hm := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 1) (hF z hz)).mpr
    (by
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simpa only [iteratedDeriv_zero] using hzero)
  rw [← hk] at hm
  rw [hF.divisor_apply hz, ← hk]
  simpa using (by exact_mod_cast hm : (1 : ℤ) ≤ k)

private theorem local_divisor_log_weight_nonneg {F : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hF : AnalyticOnNhd ℂ F (closedBall c r)) (u : ℂ) :
    0 ≤ (divisor F (closedBall c r) u : ℝ)*Real.log (r/‖c-u‖) := by
  by_cases hu : u ∈ closedBall c r
  · apply mul_nonneg (by exact_mod_cast hF.divisor_nonneg u)
    by_cases huc : u = c
    · simp [huc]
    · apply Real.log_nonneg
      apply (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc)))).mpr
      simpa only [mem_closedBall, dist_eq_norm'] using hu
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

/-- Every finite set of actual zeros in the closed disk gives a logarithmic
Jensen upper bound at a nonzero center. No other zeros need to be selected,
and no nonvanishing assumption is made on the integration circle. -/
theorem log_norm_le_circleAverage_sub_sum_log_of_selected_zeros
    {F : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ F (closedBall c r)) (hc : F c ≠ 0)
    (Z : Finset ℂ) (hzeros : ∀ z ∈ Z, F z = 0)
    (hnodes : ∀ z ∈ Z, ‖c-z‖ ≤ r) :
    Real.log ‖F c‖ ≤ Real.circleAverage (fun z => Real.log ‖F z‖) c r -
      ∑ z ∈ Z, Real.log (r/‖c-z‖) := by
  classical
  let w : ℂ → ℝ := fun u => (divisor F (closedBall c r) u : ℝ)*Real.log (r/‖c-u‖)
  have hfin : (Function.support w).Finite :=
    ((divisor F (closedBall c r)).finiteSupport (isCompact_closedBall c r)).subset
      (fun u hu => by
        contrapose! hu
        have hu' : divisor F (closedBall c r) u = 0 := by simpa using hu
        simp [w, Function.mem_support, hu'])
  have hnonneg : ∀ u, 0 ≤ w u := local_divisor_log_weight_nonneg hF
  have hsum : (∑ z ∈ Z, Real.log (r/‖c-z‖)) ≤ ∑ᶠ u, w u := by
    rw [finsum_eq_sum_of_support_subset w (s := Z ∪ hfin.toFinset)
      (by simp only [Finset.coe_union, Set.Finite.coe_toFinset]; tauto_set)]
    apply le_trans (Finset.sum_le_sum (s := Z) (g := w) ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun u _ _ => hnonneg u))
    intro z hz
    have hcz : c ≠ z := fun heq => hc (heq ▸ hzeros z hz)
    have hd : 0 < ‖c-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcz)
    have hlog : 0 ≤ Real.log (r/‖c-z‖) :=
      Real.log_nonneg ((one_le_div hd).mpr (hnodes z hz))
    have horder : (1 : ℝ) ≤ (divisor F (closedBall c r) z : ℝ) := by
      exact_mod_cast local_one_le_divisor_of_zero hr hF hc
        (by simpa only [mem_closedBall, dist_eq_norm'] using hnodes z hz) (hzeros z hz)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right horder hlog
  have hFabs : AnalyticOnNhd ℂ F (closedBall c |r|) := by
    simpa only [abs_of_pos hr] using hF
  have hjensen := hFabs.circleAverage_log_norm hr.ne' hc
  rw [abs_of_pos hr] at hjensen
  simp only [← div_eq_mul_inv] at hjensen
  change Real.circleAverage (fun z => Real.log ‖F z‖) c r =
    (∑ᶠ u, w u)+Real.log ‖F c‖ at hjensen
  linarith

/-- The finite-selected-zero Jensen estimate in a zero-safe product form.
The actual circle average is retained, including when zeros lie on the circle.
If the center is itself a zero, nonnegativity proves the bound directly. -/
theorem norm_le_exp_circleAverage_mul_prod_of_selected_zeros
    {F : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ F (closedBall c r))
    (Z : Finset ℂ) (hzeros : ∀ z ∈ Z, F z = 0)
    (hnodes : ∀ z ∈ Z, ‖c-z‖ ≤ r) :
    ‖F c‖ ≤ Real.exp (Real.circleAverage (fun z => Real.log ‖F z‖) c r)*
      ∏ z ∈ Z, ‖c-z‖/r := by
  by_cases hc : F c = 0
  · rw [hc, norm_zero]
    exact mul_nonneg (Real.exp_pos _).le
      (Finset.prod_nonneg (fun z _ => div_nonneg (norm_nonneg _) hr.le))
  · have h := Real.exp_le_exp.mpr
      (log_norm_le_circleAverage_sub_sum_log_of_selected_zeros hr hF hc Z hzeros hnodes)
    rw [Real.exp_log (norm_pos_iff.mpr hc), sub_eq_add_neg, Real.exp_add] at h
    have hprod : Real.exp (-(∑ z ∈ Z, Real.log (r/‖c-z‖))) =
        ∏ z ∈ Z, ‖c-z‖/r := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      apply Finset.prod_congr rfl
      intro z hz
      have hcz : c ≠ z := fun heq => hc (heq ▸ hzeros z hz)
      have hd : 0 < ‖c-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcz)
      rw [Real.exp_neg, Real.exp_log (div_pos hr hd), inv_div]
    rwa [hprod] at h

end

end MeyerGeneralProblem
