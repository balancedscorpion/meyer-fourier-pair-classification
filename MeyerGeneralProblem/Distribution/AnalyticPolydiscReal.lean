module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section

/-!
# Uniqueness from the real section of a finite polydisc

The ordinary one-variable analytic identity theorem extends a real
section one coordinate at a time. The proof needs only analyticity of
each coordinate slice.
-/

namespace MeyerGeneralProblem

noncomputable section

open Complex Metric Set

private theorem analyticOnNhd_ball_eq_zero_of_real_section
    (a ρ : ℝ) (hρ : 0 < ρ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball (a : ℂ) ρ))
    (hzero : ∀ z ∈ ball (a : ℂ) ρ, z.im = 0 → f z = 0) :
    ∀ z ∈ ball (a : ℂ) ρ, f z = 0 := by
  have hcl : (a : ℂ) ∈ closure ({z | f z = 0} \ ({(a : ℂ)} : Set ℂ)) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let d := min ε ρ / 2
    have hd : 0 < d := div_pos (lt_min hε hρ) (by norm_num)
    have hdε : d < ε := by dsimp [d]; linarith [min_le_left ε ρ]
    have hdρ : d < ρ := by dsimp [d]; linarith [min_le_right ε ρ]
    let w : ℂ := (a + d : ℝ)
    have hdist : dist w (a : ℂ) = d := by
      rw [dist_eq_norm, show w - (a : ℂ) = (d : ℂ) by simp [w], norm_real,
        Real.norm_eq_abs, abs_of_pos hd]
    refine ⟨w, ⟨hzero w (mem_ball.mpr (hdist.trans_lt hdρ)) (by simp [w]), ?_⟩, ?_⟩
    · rw [mem_singleton_iff]
      intro he
      rw [he, dist_self] at hdist
      linarith
    · rw [dist_comm, hdist]
      exact hdε
  exact hf.eqOn_zero_of_preconnected_of_mem_closure
    isPreconnected_ball (mem_ball_self hρ) hcl

/-- A separately analytic function on a finite polydisc centered at a
real point is determined by its whole real section. -/
theorem eq_zero_of_separatelyAnalyticOn_real_polydisc
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (f : (ι → ℂ) → ℂ)
    (hf : ∀ v : ι → ℂ, (∀ i, v i ∈ ball (a i : ℂ) ρ) → ∀ j,
      AnalyticOnNhd ℂ (fun w : ℂ => f (Function.update v j w)) (ball (a j : ℂ) ρ))
    (hzero : ∀ v : ι → ℂ, (∀ i, v i ∈ ball (a i : ℂ) ρ) → (∀ i, (v i).im = 0) → f v = 0)
    (v : ι → ℂ) (hv : ∀ i, v i ∈ ball (a i : ℂ) ρ) : f v = 0 := by
  classical
  let P (s : Finset ι) : Prop := ∀ u : ι → ℂ, (∀ i, u i ∈ ball (a i : ℂ) ρ) →
    (∀ i ∉ s, (u i).im = 0) → f u = 0
  have hP : ∀ s, P s := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro u hu hr
      exact hzero u hu (fun i => hr i (Finset.notMem_empty i))
    | @insert j s hjs ih =>
      intro u hu hr
      have hup (w : ℂ) (hw : w ∈ ball (a j : ℂ) ρ) :
          ∀ i, Function.update u j w i ∈ ball (a i : ℂ) ρ := by
        intro i
        by_cases he : i = j
        · subst i
          simpa only [Function.update_self] using hw
        · simpa only [Function.update_of_ne he] using hu i
      have hcut (w : ℂ) (hw : w ∈ ball (a j : ℂ) ρ) (hwR : w.im = 0) :
          f (Function.update u j w) = 0 := by
        apply ih _ (hup w hw)
        intro i hi
        by_cases he : i = j
        · subst i
          simpa only [Function.update_self] using hwR
        · rw [Function.update_of_ne he]
          exact hr i (by simp [he, hi])
      have he := analyticOnNhd_ball_eq_zero_of_real_section _ _ hρ _ (hf u hu j) hcut (u j) (hu j)
      simpa only [Function.update_eq_self] using he
  exact hP Finset.univ v hv (fun i hi => False.elim (hi (Finset.mem_univ i)))

end

end MeyerGeneralProblem
