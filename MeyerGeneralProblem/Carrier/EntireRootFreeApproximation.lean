module

public import MeyerGeneralProblem.Carrier.EntireRealZeroCounts
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

/-!
# Nonvanishing of a nonzero entire limit of zero-free approximations

The argument uses an isolated zero, a positive minimum on a small
boundary circle, and the maximum principle for the reciprocal of a
nearby nonvanishing analytic function.
-/

namespace MeyerGeneralProblem

open Filter Metric Set
open scoped Topology

/-- A lower bound for a nonvanishing function on the boundary propagates to the center. -/
theorem norm_ge_at_center_of_nonvanishing_closedBall
    (f : ℂ → ℂ) (c : ℂ) (r κ : ℝ) (hr : 0 < r) (hκ : 0 < κ)
    (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hnz : ∀ w ∈ closedBall c r, f w ≠ 0)
    (hbound : ∀ w ∈ sphere c r, κ ≤ ‖f w‖) :
    κ ≤ ‖f c‖ := by
  have hdiff : DiffContOnCl ℂ (fun w => (f w)⁻¹) (ball c r) := by
    apply DifferentiableOn.diffContOnCl
    apply (hf.differentiableOn.mono closure_ball_subset_closedBall).inv
    exact fun w hw => hnz w (closure_ball_subset_closedBall hw)
  have hinv (w : ℂ) (hw : w ∈ sphere c r) : ‖(f w)⁻¹‖ ≤ κ⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hκ (hbound w hw)
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 0 hr hdiff hinv
  simp only [iteratedDeriv_zero, norm_inv, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero,
    div_one] at hc
  exact inv_le_inv₀ (norm_pos_iff.mpr (hnz c (mem_closedBall_self hr.le))) hκ |>.mp hc

/-- Local uniform approximation by nonvanishing analytic functions
forces a nonzero entire function to be nonvanishing at the center. -/
theorem entire_ne_zero_at_of_closedBall_approximation
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) (hne : ∃ z, f z ≠ 0)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (closedBall c ρ) ∧ (∀ w ∈ closedBall c ρ, g w ≠ 0) ∧
      ∀ w ∈ closedBall c ρ, ‖g w - f w‖ < ε) :
    f c ≠ 0 := by
  intro hz
  have hno := entire_analyticOrderAt_ne_top_of_exists_ne_zero f hf hne c
  have hloc := ((hf c (mem_univ c)).eventually_eq_zero_or_eventually_ne_zero).resolve_left
    (fun h => hno (analyticOrderAt_eq_top.mpr h))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hloc
  obtain ⟨δ, hδ, hlocal⟩ := hloc
  let r := min (ρ / 2) (δ / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrl : r ≤ ρ := (min_le_left _ _).trans (by linarith)
  have hrd : r < δ := (min_le_right _ _).trans_lt (by linarith)
  have hboundary (w : ℂ) (hw : w ∈ sphere c r) : f w ≠ 0 := by
    have hd := mem_sphere.mp hw
    have hwc : w ≠ c := by
      intro h
      subst w
      rw [dist_self] at hd
      exact hr.ne' hd.symm
    exact hlocal (hd.trans_lt hrd) (by simpa using hwc)
  have hnons : (sphere c r).Nonempty := by
    refine ⟨c + (r : ℂ), ?_⟩
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
  obtain ⟨w, hw, hwmin⟩ := (isCompact_sphere c r).exists_isMinOn hnons
    ((hf.continuousOn.mono (subset_univ _)).norm)
  let κ := ‖f w‖
  have hκ : 0 < κ := norm_pos_iff.mpr (hboundary w hw)
  obtain ⟨g, hg, hgnz, hdiff⟩ := happrox (κ / 3) (by positivity)
  have hsub : closedBall c r ⊆ closedBall c ρ := closedBall_subset_closedBall hrl
  have hgbound (u : ℂ) (hu : u ∈ sphere c r) : κ / 2 ≤ ‖g u‖ := by
    have hmin : κ ≤ ‖f u‖ := hwmin hu
    have herr := hdiff u (hsub (sphere_subset_closedBall hu))
    have h := norm_sub_norm_le (f u) (g u)
    rw [norm_sub_rev] at h
    linarith
  have hgc := norm_ge_at_center_of_nonvanishing_closedBall g c r (κ / 2) hr
    (by positivity) (hg.mono hsub) (fun u hu => hgnz u (hsub hu)) hgbound
  have he := hdiff c (mem_closedBall_self hρ.le)
  rw [hz, sub_zero] at he
  linarith

end MeyerGeneralProblem
