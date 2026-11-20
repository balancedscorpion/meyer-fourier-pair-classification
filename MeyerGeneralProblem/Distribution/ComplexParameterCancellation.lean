module

public import MeyerGeneralProblem.Distribution.AnalyticCircleParameter
public import MeyerGeneralProblem.Distribution.AnalyticPolydiscReal

@[expose] public section

/-!
# Analytic cancellation under complex changes of phase

A quotient that is analytic on a leaf disk at every real phase is
represented by the same Cauchy contour. This supplies an analytic
extension in each complex phase coordinate, so multiplication by the
denominator agrees with the original numerator on a complex polydisc.
-/

namespace MeyerGeneralProblem

noncomputable section

open Complex Metric Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem continuous_update_prod (u : ι → ℂ) (j : ι) :
    Continuous (fun a : ℂ × ℂ => (Function.update u j a.1, a.2)) := by
  apply Continuous.prodMk _ continuous_snd
  apply continuous_pi
  intro i
  by_cases he : i = j
  · subst i
    simpa only [Function.update_self] using
      (continuous_fst : Continuous (Prod.fst : ℂ × ℂ → ℂ))
  · simp only [Function.update_of_ne he]
    exact continuous_const

set_option maxHeartbeats 1000000 in
/-- Analytic factorization on all real leaves extends to a neighborhood
of the original parameter, with the actual denominator and numerator
throughout the disk. The factor is analytic in each phase coordinate. -/
theorem exists_complex_polydisc_leaf_factorization
    (a : ι → ℝ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (f p : (ι → ℂ) → ℂ → ℂ) (df dp : ι → (ι → ℂ) → ℂ → ℂ)
    (hf : Continuous (fun v : (ι → ℂ) × ℂ => f v.1 v.2))
    (hp : Continuous (fun v : (ι → ℂ) × ℂ => p v.1 v.2))
    (hdf : ∀ j, Continuous (fun v : (ι → ℂ) × ℂ => df j v.1 v.2))
    (hdp : ∀ j, Continuous (fun v : (ι → ℂ) × ℂ => dp j v.1 v.2))
    (hf' : ∀ j u w z, HasDerivAt (fun v : ℂ => f (Function.update u j v) z)
      (df j (Function.update u j w) z) w)
    (hp' : ∀ j u w z, HasDerivAt (fun v : ℂ => p (Function.update u j v) z)
      (dp j (Function.update u j w) z) w)
    (hcircle : ∀ z ∈ sphere c r, p (fun i => (a i : ℂ)) z ≠ 0)
    (hreal : ∀ u : ι → ℂ, (∀ i, (u i).im = 0) →
      ∃ K : ℂ → ℂ, AnalyticOnNhd ℂ K (closedBall c r) ∧
        ∀ z ∈ closedBall c r, f u z = p u z * K z) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ H : (ι → ℂ) → ℂ → ℂ,
      ContinuousOn (fun u => H u c) (ball (fun i => (a i : ℂ)) δ) ∧
      (∀ u : ι → ℂ, (∀ i, u i ∈ ball (a i : ℂ) δ) →
        ∀ z ∈ ball c r, f u z = p u z * H u z) ∧
      ∀ z ∈ ball c r, ∀ u : ι → ℂ, (∀ i, u i ∈ ball (a i : ℂ) δ) → ∀ j,
        AnalyticOnNhd ℂ (fun v : ℂ => H (Function.update u j v) z) (ball (a j : ℂ) δ) := by
  let aC (i : ι) : ℂ := a i
  let V := {v : (ι → ℂ) × ℂ | p v.1 v.2 ≠ 0}
  have hV : IsOpen V := (isOpen_ne : IsOpen {z : ℂ | z ≠ 0}).preimage hp
  have hV₀ : ({aC} : Set (ι → ℂ)) ×ˢ sphere c r ⊆ V := by
    rintro ⟨u, z⟩ ⟨hu, hz⟩
    change u = aC at hu
    subst u
    exact hcircle z hz
  obtain ⟨W, Y, hW, _, hWa, hY, hWY⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_sphere c r) hV hV₀
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds (hWa (mem_singleton aC)))
  have hDen (u : ι → ℂ) (hu : ∀ i, u i ∈ ball (a i : ℂ) δ)
      (z : ℂ) (hz : z ∈ sphere c r) : p u z ≠ 0 := by
    have huW : u ∈ W := hδW (mem_ball.mpr ((dist_pi_lt_iff hδ).mpr fun i => mem_ball.mp (hu i)))
    exact hWY (show (u, z) ∈ W ×ˢ Y from ⟨huW, hY hz⟩)
  let H (u : ι → ℂ) (z : ℂ) : ℂ :=
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ w in C(c, r), (w - z)⁻¹ • (f u w / p u w))
  let D := ball aC δ
  have hHc : ContinuousOn (fun u => H u c) D := by
    let K (u : ι → ℂ) (w : ℂ) := (w - c)⁻¹ * (f u w / p u w)
    let J := D ×ˢ sphere c r
    have hKnz (v : (ι → ℂ) × ℂ) (hv : v ∈ J) : p v.1 v.2 ≠ 0 := by
      apply hDen v.1 _ v.2 hv.2
      intro i
      exact mem_ball.mpr ((dist_pi_lt_iff hδ).mp (mem_ball.mp hv.1) i)
    have hinv : ContinuousOn (fun v : (ι → ℂ) × ℂ => (v.2 - c)⁻¹) J := by
      apply (continuous_snd.sub continuous_const).continuousOn.inv₀
      intro v hv
      apply sub_ne_zero.mpr
      intro h
      have hdist := mem_sphere.mp hv.2
      rw [h, dist_self] at hdist
      exact hr.ne' hdist.symm
    have hK : ContinuousOn (fun v : (ι → ℂ) × ℂ => K v.1 v.2) J :=
      hinv.mul (hf.continuousOn.div hp.continuousOn hKnz)
    have hI := circleIntegral_continuousOn_of_continuous_parameter D c r hr.le K hK
    apply (hI.const_smul ((2 * Real.pi * Complex.I : ℂ)⁻¹)).congr
    intro u _
    simp only [H, K, Pi.smul_apply, smul_eq_mul]
  have hH (z : ℂ) (hz : z ∈ ball c r) (u : ι → ℂ)
      (hu : ∀ i, u i ∈ ball (a i : ℂ) δ) (j : ι) :
      AnalyticOnNhd ℂ (fun v : ℂ => H (Function.update u j v) z) (ball (a j : ℂ) δ) := by
    let D := ball (a j : ℂ) δ
    let W := D ×ˢ sphere c r
    let A (v : ℂ) (w : ℂ) := f (Function.update u j v) w
    let B (v : ℂ) (w : ℂ) := p (Function.update u j v) w
    let A' (v : ℂ) (w : ℂ) := df j (Function.update u j v) w
    let B' (v : ℂ) (w : ℂ) := dp j (Function.update u j v) w
    let C (w : ℂ) := (w - z)⁻¹
    let K (v : ℂ) (w : ℂ) := C w * (A v w / B v w)
    let K' (v : ℂ) (w : ℂ) :=
      C w * ((A' v w * B v w - A v w * B' v w) / (B v w) ^ 2)
    have hBne (v : ℂ) (hv : v ∈ D) (w : ℂ) (hw : w ∈ sphere c r) : B v w ≠ 0 := by
      apply hDen _ _ _ hw
      intro i
      by_cases hi : i = j
      · subst i
        simpa only [Function.update_self] using hv
      · simpa only [Function.update_of_ne hi] using hu i
    have hAc : Continuous (fun v : ℂ × ℂ => A v.1 v.2) :=
      hf.comp (continuous_update_prod u j)
    have hBc : Continuous (fun v : ℂ × ℂ => B v.1 v.2) :=
      hp.comp (continuous_update_prod u j)
    have hA'c : Continuous (fun v : ℂ × ℂ => A' v.1 v.2) :=
      (hdf j).comp (continuous_update_prod u j)
    have hB'c : Continuous (fun v : ℂ × ℂ => B' v.1 v.2) :=
      (hdp j).comp (continuous_update_prod u j)
    have hC : ContinuousOn (fun v : ℂ × ℂ => C v.2) W := by
      apply (continuous_snd.sub continuous_const).continuousOn.inv₀
      intro v hv
      apply sub_ne_zero.mpr
      intro he
      have h := mem_sphere.mp hv.2
      rw [he] at h
      exact (ne_of_lt (mem_ball.mp hz)) h
    have hK : ContinuousOn (fun v : ℂ × ℂ => K v.1 v.2) W :=
      hC.mul (hAc.continuousOn.div hBc.continuousOn (fun v hv => hBne _ hv.1 _ hv.2))
    have hK' : ContinuousOn (fun v : ℂ × ℂ => K' v.1 v.2) W :=
      hC.mul (((hA'c.mul hBc).sub (hAc.mul hB'c)).continuousOn.div
        (hBc.pow 2).continuousOn (fun v hv => pow_ne_zero _ (hBne _ hv.1 _ hv.2)))
    have hder (v : ℂ) (hv : v ∈ D) (w : ℂ) (hw : w ∈ sphere c r) :
        HasDerivAt (fun v => K v w) (K' v w) v :=
      ((hf' j u v w).div (hp' j u v w) (hBne _ hv _ hw)).const_mul (C w)
    have hI := circleIntegral_analyticOnNhd_of_continuous_parameter_derivative D isOpen_ball
      c r hr K K' hK hK' hder
    simpa only [H, K, C, A, B, smul_eq_mul] using
      (analyticOnNhd_const (v := (2 * Real.pi * Complex.I : ℂ)⁻¹)).mul hI
  have hHreal (u : ι → ℂ) (hu : ∀ i, u i ∈ ball (a i : ℂ) δ) (huR : ∀ i, (u i).im = 0)
      (z : ℂ) (hz : z ∈ ball c r) : f u z = p u z * H u z := by
    obtain ⟨Q, hQ, hQval⟩ := hreal u huR
    have hdiff : DiffContOnCl ℂ Q (ball c r) :=
      (hQ.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
    have he : H u z = Q z := by
      dsimp only [H]
      rw [circleIntegral.integral_congr hr.le (g := fun w => (w - z)⁻¹ • Q w)]
      · exact hdiff.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz
      · intro w hw
        change (w - z)⁻¹ • (f u w / p u w) = (w - z)⁻¹ • Q w
        have hfce : f u w / p u w = Q w := (div_eq_iff (hDen _ hu _ hw)).mpr
          ((hQval w (sphere_subset_closedBall hw)).trans (mul_comm _ _))
        rw [hfce]
    rw [he]
    exact hQval z (ball_subset_closedBall hz)
  refine ⟨δ, hδ, H, hHc, ?_, hH⟩
  intro u hu z hz
  apply sub_eq_zero.mp
  apply eq_zero_of_separatelyAnalyticOn_real_polydisc a δ hδ
    (fun v => f v z - p v z * H v z) _ _ u hu
  · intro v hv j
    have hfD : DifferentiableOn ℂ (fun w : ℂ => f (Function.update v j w) z) (ball (a j : ℂ) δ) :=
      fun w _ => (hf' j v w z).differentiableAt.differentiableWithinAt
    have hpD : DifferentiableOn ℂ (fun w : ℂ => p (Function.update v j w) z) (ball (a j : ℂ) δ) :=
      fun w _ => (hp' j v w z).differentiableAt.differentiableWithinAt
    exact (hfD.analyticOnNhd isOpen_ball).sub ((hpD.analyticOnNhd isOpen_ball).mul (hH z hz v hv j))
  · intro v hv hvR
    exact sub_eq_zero.mpr (hHreal v hv hvR z hz)

end

end MeyerGeneralProblem
