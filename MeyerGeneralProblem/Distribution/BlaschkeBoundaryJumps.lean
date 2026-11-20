module

public import MeyerGeneralProblem.Distribution.BlaschkeLocalLog
public import MeyerGeneralProblem.Distribution.BlaschkePhaseLimit
public import MeyerGeneralProblem.Distribution.DownwardPhaseCrossings

@[expose] public section

/-!
# Downward phase jumps at real zeros

The logarithm of the displacement has boundary imaginary part pi to
the left of a real zero and zero to its right. The analytic remainder
has the same limit from both sides.
-/

namespace MeyerGeneralProblem

noncomputable section

open ComplexConjugate Filter MeasureTheory Metric Set
open scoped FourierTransform Topology

private theorem tendsto_im_log_sub_of_tendsto_real_from_upper {ι : Type*}
    {l : Filter ι} {P : ι → ℂ} {x y : ℝ} (hP : Tendsto P l (𝓝 (y : ℂ)))
    (hUpper : ∀ᶠ r in l, 0 ≤ (P r).im) (hne : y ≠ x) :
    Tendsto (fun r => (Complex.log (P r - (x : ℂ))).im) l
      (𝓝 (if y < x then Real.pi else 0)) := by
  have hSub : Tendsto (fun r => P r - (x : ℂ)) l (𝓝 ((y : ℂ) - (x : ℂ))) := hP.sub_const _
  simp only [Complex.log_im]
  by_cases hlt : y < x
  · have hLeft : ((y : ℂ) - (x : ℂ)).re < 0 := by
      simpa only [Complex.sub_re, Complex.ofReal_re] using sub_neg.mpr hlt
    have hToClosed : Tendsto (fun r => P r - (x : ℂ)) l
        (𝓝[{z : ℂ | 0 ≤ z.im}] ((y : ℂ) - (x : ℂ))) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hSub
        (hUpper.mono fun _ hr => by simpa using hr)
    rw [ite_eq_left hlt]
    exact (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hLeft (by simp)).comp hToClosed
  · have hgt : x < y := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    have hSlit : (y : ℂ) - (x : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using sub_pos.mpr hgt))
    rw [ite_eq_right hlt]
    have he := (Complex.continuousAt_arg hSlit).tendsto.comp hSub
    change Tendsto (fun r => Complex.arg (P r - (x : ℂ))) l
      (𝓝 (Complex.arg ((y : ℂ) - (x : ℂ)))) at he
    simpa only [← Complex.ofReal_sub,
      Complex.arg_ofReal_of_nonneg (sub_nonneg.mpr hgt.le)] using he

/-- The compensated conjugate and the affine phase are continuous
at nonzero real points. At a zero of positive order (n), their
right limit is (nπ) below their left limit. -/
theorem hasDownwardPhaseJumps_blaschkeLog_boundary {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).im) (hFin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hSum : Summable (fun i => upperHalfPlaneBlaschkeWeight (a i)))
    {H L : ℂ → ℂ} (hH : Differentiable ℂ H) (hH₀ : ∃ z, H z ≠ 0)
    (hL : AnalyticOnNhd ℂ L {z : ℂ | 0 < z.im})
    (hFactor : EqOn H (fun z => upperHalfPlaneBlaschkeProduct a z * Complex.exp (L z))
      {z : ℂ | 0 < z.im})
    (hu : Integrable (fun y : ℝ => Real.log ‖H (y : ℂ)‖ / (1 + y ^ 2)))
    {c d : ℝ}
    (hW : ∀ w ∈ ball (0 : ℂ) 1, L (cayleyToUpperHalfPlane w) =
      weightedDiskHerglotzIntegral (fun y : ℝ => Real.log ‖H (y : ℂ)‖) w +
        (c : ℂ) * Complex.I * cayleyToUpperHalfPlane w + (d : ℂ) * Complex.I) :
    HasDownwardPhaseJumps (fun x => weightedDiskHerglotzBoundaryConjugate
      (fun y : ℝ => Real.log ‖H (y : ℂ)‖) x + c * x + d) {x | H (x : ℂ) ≠ 0} := by
  let D := {x : ℝ | H (x : ℂ) ≠ 0}
  let p (x : ℝ) := weightedDiskHerglotzBoundaryConjugate
    (fun y : ℝ => Real.log ‖H (y : ℂ)‖) x + c * x + d
  have hOpen : IsOpen D := (isClosed_eq (hH.continuous.comp Complex.continuous_ofReal) continuous_const).isOpen_compl
  have hLocal (x : ℝ) : ∃ n : ℕ, ∃ q : ℝ → ℝ, ContinuousAt q x ∧
      (H (x : ℂ) = 0 ↔ 0 < n) ∧ (∀ᶠ y in 𝓝[≠] x, y ∈ D) ∧
      ∀ᶠ y in 𝓝 x, y ∈ D → p y = (n : ℝ) * (if y < x then Real.pi else 0) + q y := by
    obtain ⟨n, R, δ, hδ, hR, hOrder, hIso, hModel⟩ :=
      exists_local_upperHalfPlane_blaschkeLog_model ha hFin hSum hH hH₀ hL hFactor x
    let q (y : ℝ) := (R (y : ℂ)).im
    have hBall : ∀ᶠ y : ℝ in 𝓝 x, (y : ℂ) ∈ ball (x : ℂ) δ :=
      Complex.continuous_ofReal.continuousAt.tendsto.eventually (ball_mem_nhds _ hδ)
    have hQ : ContinuousAt q x :=
      Complex.continuous_im.continuousAt.comp
        ((hR _ (mem_ball_self hδ)).continuousAt.comp Complex.continuous_ofReal.continuousAt)
    refine ⟨n, q, hQ, hOrder, ?_, ?_⟩
    · filter_upwards [hBall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy (hne : y ≠ x)
      exact hIso _ hy (fun he => hne (Complex.ofReal_injective he))
    · filter_upwards [hBall] with y hy hyD
      let P (r : ℝ) := cayleyToUpperHalfPlane ((r : ℂ) * cayleyBoundaryPoint y)
      have hP : Tendsto P (𝓝[<] (1 : ℝ)) (𝓝 (y : ℂ)) := tendsto_cayleyBoundaryRadial y
      have hUp : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < (P r).im :=
        (eventually_mul_cayleyBoundaryPoint_mem_ball y).mono fun _ hr =>
          im_cayleyToUpperHalfPlane_pos (mem_ball_zero_iff.mp hr)
      have hNear := hP.eventually (isOpen_ball.mem_nhds hy)
      have hQLim : Tendsto (fun r => (R (P r)).im) (𝓝[<] (1 : ℝ)) (𝓝 (q y)) :=
        Complex.continuous_im.continuousAt.tendsto.comp ((hR _ hy).continuousAt.tendsto.comp hP)
      have hModelLim : Tendsto (fun r => (L (P r)).im) (𝓝[<] (1 : ℝ))
          (𝓝 ((n : ℝ) * (if y < x then Real.pi else 0) + q y)) := by
        by_cases he : y = x
        · subst y
          have hn : n = 0 := Nat.eq_zero_of_not_pos (fun hp => hyD (hOrder.mpr hp))
          have hEq : ∀ᶠ r in 𝓝[<] (1 : ℝ), (R (P r)).im = (L (P r)).im := by
            filter_upwards [hNear, hUp] with r hr hri
            simp [hModel _ hr hri, hn]
          simpa only [hn, Nat.cast_zero, zero_mul, zero_add] using hQLim.congr' hEq
        · have hArg := tendsto_im_log_sub_of_tendsto_real_from_upper hP (hUp.mono fun _ hr => hr.le) he
          refine ((hArg.const_mul (n : ℝ)).add hQLim).congr' ?_
          filter_upwards [hNear, hUp] with r hr hri
          have hEq := congrArg Complex.im (hModel _ hr hri)
          simpa only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
            zero_mul, add_zero] using hEq.symm
      exact tendsto_nhds_unique (tendsto_im_blaschkeLog_radial_of_weighted_identity hH hu hW hyD) hModelLim
  refine ⟨hOpen, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, q, hQ, hOrder, _, hNear⟩ := hLocal x
    have hn : n = 0 := Nat.eq_zero_of_not_pos (fun hp => hx (hOrder.mpr hp))
    have he : q =ᶠ[𝓝 x] p := by
      filter_upwards [hNear, hOpen.mem_nhds hx] with y hy hyD
      simpa only [hn, Nat.cast_zero, zero_mul, zero_add] using (hy hyD).symm
    show Tendsto p (𝓝 x) (𝓝 (p x))
    rw [← he.eq_of_nhds]
    exact hQ.tendsto.congr' he
  · intro x hx
    obtain ⟨n, q, hQ, hOrder, hIso, hNear⟩ := hLocal x
    have hn : 0 < n := hOrder.mp (not_ne_iff.mp hx)
    refine ⟨hIso, (n : ℝ) * Real.pi + q x, q x, ?_, ?_, ?_⟩
    · linarith only [mul_pos (by exact_mod_cast hn : (0 : ℝ) < n) Real.pi_pos]
    · have hIsoL : 𝓝[<] x ≤ 𝓝[≠] x := nhdsWithin_mono _ fun y hy => (show y < x from hy).ne
      refine (tendsto_const_nhds.add (hQ.tendsto.mono_left nhdsWithin_le_nhds)).congr' ?_
      filter_upwards [hNear.filter_mono nhdsWithin_le_nhds, hIso.filter_mono hIsoL, self_mem_nhdsWithin]
        with y hy hyD (hlt : y < x)
      simpa only [ite_eq_left hlt] using (hy hyD).symm
    · have hIsoR : 𝓝[>] x ≤ 𝓝[≠] x := nhdsWithin_mono _ fun y hy => (show x < y from hy).ne'
      refine (hQ.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [hNear.filter_mono nhdsWithin_le_nhds, hIso.filter_mono hIsoR, self_mem_nhdsWithin]
        with y hy hyD (hlt : x < y)
      simpa only [ite_eq_right hlt.not_gt, mul_zero, zero_add] using (hy hyD).symm

/-- Endpoint control of the compensated conjugate gives a quantitative
sign-alternation bound for the actual heated density. The jump and
monotonicity estimates consume no allowance per real zero. -/
theorem exists_eventually_heatSignAlternations_of_boundary_conjugate
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0)
    {s : ℝ} (hs : 0 ≤ s)
    (hGap : EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo (-s) s)) :
    ∃ b : ℝ, s ≤ b ∧ ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let T := heatFourierLaplace t f 0
      let v := weightedDiskHerglotzBoundaryConjugate (fun x : ℝ => Real.log ‖T (x : ℂ)‖)
      ∀ {l r : ℝ} (_ : l < r) (_ : T (l : ℂ) ≠ 0) (_ : T (r : ℂ) ≠ 0) {n : ℕ},
        ((n : ℝ) + 1) * Real.pi < (2 * Real.pi * b) * (r - l) + (v r - v l) →
        HasSignAlternations (realGaussianSmoothing t f) (Icc l r) n := by
  obtain ⟨b, hb, hF⟩ := exists_eventually_heatFourierLaplace_boundary_phase_of_gap hf hfCont hf₀ hs hGap
  refine ⟨b, hb, ?_⟩
  have hTime : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hTime, hF] with t ht hOne
  obtain ⟨hSum, hFin, hu, hH₀, hNorm, L, c, d, hL, hFactor, hc, hW, _, hPhase⟩ := hOne
  let H := edgeNormalizedHeatFourierLaplace t f b
  let T := heatFourierLaplace t f 0
  let u (x : ℝ) := Real.log ‖T (x : ℂ)‖
  let v := weightedDiskHerglotzBoundaryConjugate u
  let B := upperHalfPlaneBlaschkePhaseSum (upperHalfPlaneZeroAtIndex H)
  let p (x : ℝ) := (2 * Real.pi * b) * x + B x + v x + c * x + d
  let D := {x : ℝ | T (x : ℂ) ≠ 0}
  have hUeq : (fun x : ℝ => Real.log ‖H (x : ℂ)‖) = u :=
    funext fun x => congrArg Real.log (hNorm x)
  have hDomain : {x : ℝ | H (x : ℂ) ≠ 0} = D := by
    ext x
    change H (x : ℂ) ≠ 0 ↔ T (x : ℂ) ≠ 0
    exact (norm_ne_zero_iff.symm.trans (by rw [hNorm x])).trans norm_ne_zero_iff
  have hUInt : Integrable (fun x : ℝ => Real.log ‖H (x : ℂ)‖ / (1 + x ^ 2)) :=
    (congrArg (fun g : ℝ → ℝ => Integrable (fun x : ℝ => g x / (1 + x ^ 2))) hUeq).mpr hu
  have hWH : ∀ w ∈ ball (0 : ℂ) 1, L (cayleyToUpperHalfPlane w) =
      weightedDiskHerglotzIntegral (fun x : ℝ => Real.log ‖H (x : ℂ)‖) w +
        (c : ℂ) * Complex.I * cayleyToUpperHalfPlane w + (d : ℂ) * Complex.I := by
    intro w hw
    rw [hUeq]
    exact hW w hw
  have hJump := hasDownwardPhaseJumps_blaschkeLog_boundary (fun i => i.1.2) hFin hSum
    (differentiable_edgeNormalizedHeatFourierLaplace hf ht b) hH₀ hL hFactor hUInt hWH
  change HasDownwardPhaseJumps (fun x => weightedDiskHerglotzBoundaryConjugate
    (fun y : ℝ => Real.log ‖H (y : ℂ)‖) x + c * x + d) {x : ℝ | H (x : ℂ) ≠ 0} at hJump
  rw [hUeq, hDomain] at hJump
  have hBCont : Continuous B := continuous_upperHalfPlaneBlaschkePhaseSum (fun i => i.1.2) hFin hSum
  have hBMono : Monotone B := monotone_upperHalfPlaneBlaschkePhaseSum (fun i => i.1.2) hFin hSum
  have hJumps : HasDownwardPhaseJumps p D := by
    have hBase : Continuous (fun x : ℝ => (2 * Real.pi * b) * x + B x) :=
      (continuous_id.const_mul _).add hBCont
    simpa only [p, B, v, add_assoc] using hJump.continuous_add hBase
  have hZeroGap : EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo (-(0 : ℝ)) 0) := by simp
  have hCos (x : ℝ) : realGaussianSmoothing t f x = (2 * ‖T (x : ℂ)‖) * Real.cos (p x) := by
    have hReal := congrArg Complex.re
      (ofReal_realGaussianSmoothing_eq_heatFourierLaplace_add_conj hf ht le_rfl hZeroGap x)
    have he := hPhase x
    change T (x : ℂ) = (‖T (x : ℂ)‖ : ℂ) * Complex.exp ((p x : ℂ) * Complex.I) at he
    have hExp : (Complex.exp ((p x : ℂ) * Complex.I)).re = Real.cos (p x) := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    calc
      _ = 2 * (T (x : ℂ)).re := by
        simpa only [T, Complex.ofReal_re, Complex.add_re, Complex.conj_re, two_mul] using hReal
      _ = _ := by
        have hT := congrArg Complex.re he
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hExp] at hT
        rw [hT]
        ring
  change ∀ {l r : ℝ}, l < r → T (l : ℂ) ≠ 0 → T (r : ℂ) ≠ 0 → ∀ {n : ℕ},
    ((n : ℝ) + 1) * Real.pi < (2 * Real.pi * b) * (r - l) + (v r - v l) →
      HasSignAlternations (realGaussianSmoothing t f) (Icc l r) n
  intro l r hlr hl hr n hInc
  refine hJumps.hasSignAlternations (A := fun x => 2 * ‖T (x : ℂ)‖)
    (fun x hx => mul_pos (by norm_num) (norm_pos_iff.mpr hx))
    (fun x _ => hCos x) hlr hl hr ?_
  have hInc' : (2 * Real.pi * b) * (r - l) + (v r - v l) ≤ p r - p l := by
    dsimp only [p]
    linarith only [hBMono hlr.le, mul_nonneg hc (sub_nonneg.mpr hlr.le)]
  exact hInc.trans_le hInc'

end
end MeyerGeneralProblem
