module

public import MeyerGeneralProblem.Carrier.EntireRootFreeApproximation
public import Mathlib.Analysis.Analytic.Polynomial

@[expose] public section

/-!
# Root-free polynomial deformation in a disk

A continuous polynomial family that is nonvanishing on the unit circle
throughout positive parameters and on the closed disk at one positive
parameter is nonvanishing on the open disk at the limiting parameter.
-/

namespace MeyerGeneralProblem

open Filter Metric Set
open scoped Topology

/-- Boundary nonvanishing along the positive parameter axis prevents roots
from entering the open disk, including at the limiting parameter. -/
theorem polynomial_openUnitDisc_ne_zero_of_deformation
    (P : ℝ → Polynomial ℂ) (hcont : Continuous (fun p : ℝ × ℂ => (P p.1).eval p.2))
    (hP : ∀ t, (P t).eval 0 ≠ 0)
    (hboundary : ∀ t : ℝ, 0 < t → ∀ z : ℂ, ‖z‖ = 1 → (P t).eval z ≠ 0)
    (hstart : ∃ t : ℝ, 0 < t ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → (P t).eval z ≠ 0)
    (z : ℂ) (hz : ‖z‖ < 1) : (P 0).eval z ≠ 0 := by
  let D := closedBall (0 : ℂ) 1
  let U := {t : ℝ | ∀ w ∈ D, (P t).eval w ≠ 0}
  let S := Ioi (0 : ℝ) ∩ U
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    apply (isCompact_closedBall (0 : ℂ) 1).eventually_forall_of_forall_eventually
    intro w hw
    exact hcont.continuousAt.eventually_ne (ht w hw)
  have hS : IsOpen S := isOpen_Ioi.inter hU
  have hlimit (t : ℝ) (ht : t ∈ closure S) (c : ℂ) (hc : ‖c‖ < 1) : (P t).eval c ≠ 0 := by
    let ρ := (1 - ‖c‖) / 2
    have hρ : 0 < ρ := by dsimp [ρ]; linarith
    have hsub : closedBall c ρ ⊆ D := by
      intro w hw
      have hdist := mem_closedBall.mp hw
      rw [dist_eq_norm] at hdist
      simp only [D, mem_closedBall, dist_zero_right]
      dsimp [ρ] at hdist
      linarith [norm_sub_norm_le w c]
    apply entire_ne_zero_at_of_closedBall_approximation (fun w => (P t).eval w)
      (AnalyticOnNhd.eval_polynomial (P t)) ⟨0, hP t⟩ c ρ hρ
    intro ε hε
    have hcont' : Continuous (fun p : ℝ × ℂ => ‖(P p.1).eval p.2 - (P t).eval p.2‖) :=
      (hcont.sub ((P t).continuous.comp continuous_snd)).norm
    have hnear : ∀ᶠ u in 𝓝 t, ∀ w ∈ closedBall c ρ, ‖(P u).eval w - (P t).eval w‖ < ε := by
      apply (isCompact_closedBall c ρ).eventually_forall_of_forall_eventually
      intro w _
      apply hcont'.continuousAt.eventually_lt continuousAt_const
      simpa only [sub_self, norm_zero] using hε
    obtain ⟨u, hu, hd⟩ := ((mem_closure_iff_frequently.mp ht).and_eventually hnear).exists
    exact ⟨fun w => (P u).eval w, (AnalyticOnNhd.eval_polynomial (P u)).mono (subset_univ _),
      fun w hw => hu.2 w (hsub hw), hd⟩
  have hcover : Ioi (0 : ℝ) ⊆ S ∪ (closure S)ᶜ := by
    intro t ht
    by_cases hs : t ∈ closure S
    · left
      refine ⟨ht, fun c hc => ?_⟩
      have hn : ‖c‖ ≤ 1 := by simpa only [D, mem_closedBall, dist_zero_right] using hc
      rcases lt_or_eq_of_le hn with hn | hn
      · exact hlimit t hs c hn
      · exact hboundary t ht c hn
    · exact Or.inr hs
  have hnonempty : (Ioi (0 : ℝ) ∩ S).Nonempty := by
    obtain ⟨t, ht, hD⟩ := hstart
    refine ⟨t, ht, ht, fun w hw => hD w ?_⟩
    simpa only [D, mem_closedBall, dist_zero_right] using hw
  have hall : Ioi (0 : ℝ) ⊆ S :=
    isPreconnected_Ioi.subset_left_of_subset_union hS isClosed_closure.isOpen_compl
      (disjoint_left.mpr fun t hs hc => hc (subset_closure hs)) hcover hnonempty
  have hzero : (0 : ℝ) ∈ closure S := (closure_mono hall) (by rw [closure_Ioi]; exact mem_Ici.mpr le_rfl)
  exact hlimit 0 hzero z hz

end MeyerGeneralProblem
