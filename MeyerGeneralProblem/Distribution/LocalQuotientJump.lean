module

public import MeyerGeneralProblem.Distribution.CauchyPoleJump
public import MeyerGeneralProblem.Distribution.LocalPrincipalPart
public import MeyerGeneralProblem.Cardinal.Strong.ContinuousRemainderJump

@[expose] public section

/-!
# Exact localized jump of an analytic quotient at a real point

A compact test supported in a small pole neighborhood sees just the
finite principal part. The integrated analytic remainder vanishes.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Metric MeasureTheory Set
open scoped SchwartzMap Topology

/-- A local analytic quotient has an exact integrated jump on all tests
in a common positive neighborhood of its real pole. -/
theorem analyticAt_quotient_jump_integral_tendsto_with_principalPart
    (f p : ℂ → ℂ) (a : ℝ) (hf : AnalyticAt ℂ f (a : ℂ)) (hp : AnalyticAt ℂ p (a : ℂ))
    (hp' : analyticOrderAt p (a : ℂ) ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ (r : ℕ → ℂ) (H : ℂ → ℂ), AnalyticAt ℂ H (a : ℂ) ∧
      ((fun z => f z / p z) =ᶠ[𝓝[≠] (a : ℂ)]
        fun z => (∑ k ∈ Finset.range (analyticOrderNatAt p (a : ℂ)),
          r k * ((z - (a : ℂ))⁻¹) ^ (k + 1)) + H z) ∧
      ∀ φ : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, φ x ≠ 0 → |x - a| ≤ δ) →
      Tendsto (fun t : ℝ => ∫ x : ℝ,
        (f ((x : ℂ) + (t : ℂ) * Complex.I) / p ((x : ℂ) + (t : ℂ) * Complex.I) -
          f ((x : ℂ) - (t : ℂ) * Complex.I) / p ((x : ℂ) - (t : ℂ) * Complex.I)) * φ x)
        (𝓝[>] (0 : ℝ)) (𝓝 (∑ k ∈ Finset.range (analyticOrderNatAt p (a : ℂ)),
          r k * ((-2 * (Real.pi : ℂ) * Complex.I) * iteratedDeriv k φ a / (k.factorial : ℂ)))) := by
  classical
  obtain ⟨r, H, hH, he⟩ := analyticAt_quotient_exists_local_principalPart f p (a : ℂ) hf hp hp'
  let s := Finset.range (analyticOrderNatAt p (a : ℂ))
  have he' := eventually_nhdsWithin_iff.mp he
  obtain ⟨ρ, hρ, hρdata⟩ := Metric.eventually_nhds_iff.mp (hH.eventually_analyticAt.and he')
  let δ := ρ / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let K := closedBall (a : ℂ) (2 * δ)
  have hK (z : ℂ) (hz : z ∈ K) : dist z (a : ℂ) < ρ := by
    have hh : dist z (a : ℂ) ≤ 2 * δ := mem_closedBall.mp hz
    dsimp [δ] at hh
    linarith
  have hHc : ContinuousOn H K := fun z hz => ((hρdata (hK z hz)).1).continuousAt.continuousWithinAt
  let H' : ℂ → ℂ := K.piecewise H 0
  have hH'c : ContinuousOn H' K := hHc.congr fun z hz => by simp [H', hz]
  have hH'm : Measurable H' := hHc.measurable_piecewise continuousOn_const measurableSet_closedBall
  refine ⟨δ, hδ, r, H, hH, he, fun φ hsupport => ?_⟩
  have hφc : HasCompactSupport φ := by
    apply (isCompact_Icc (a := a - δ) (b := a + δ)).of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have h := abs_le.mp (hsupport x hx)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hparts := tendsto_cauchyPoleJump_finset s r a φ hφc
  have hrem := StrongParity.continuousRemainder_jump_integral_tendsto H' a hδ hH'm hH'c φ hsupport
  have hlim := hparts.add hrem
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)),
    mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds hδ)] with t ht htd
  have hInt (k : ℕ) : Integrable (fun x : ℝ => (r k * cauchyPoleJumpKernel (k + 1) a t x) * φ x) :=
    ((continuous_const.mul (continuous_cauchyPoleJumpKernel_succ k a t ht)).mul
      φ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have hJInt : Integrable (fun x : ℝ => (∑ k ∈ s, r k * cauchyPoleJumpKernel (k + 1) a t x) * φ x) := by
    simp_rw [Finset.sum_mul]
    exact integrable_finsetSum _ (fun k _ => hInt k)
  have hRInt := StrongParity.continuousRemainder_jump_mul_integrable H' a hH'm hH'c ⟨ht, htd⟩ φ hsupport
  rw [← integral_add hJInt hRInt]
  apply integral_congr_ae
  refine ae_of_all _ fun x => ?_
  by_cases hx : φ x = 0
  · simp [hx]
  let zp : ℂ := (x : ℂ) + (t : ℂ) * Complex.I
  let zm : ℂ := (x : ℂ) - (t : ℂ) * Complex.I
  have hzp : zp ∈ K := mem_closedBall.mpr ((StrongParity.real_vertical_dist_le x a t).trans (by
    rw [abs_of_pos (show 0 < t from ht)]
    linarith [hsupport x hx]))
  have hzm : zm ∈ K := mem_closedBall.mpr (by
    have h := StrongParity.real_vertical_dist_le x a (-t)
    simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg, abs_neg] at h
    apply h.trans
    rw [abs_of_pos (show 0 < t from ht)]
    linarith [hsupport x hx])
  have hpne : zp ≠ (a : ℂ) := by
    intro h
    have := congrArg Complex.im h
    simp [zp, Complex.mul_im] at this
    exact ht.ne' this
  have hmne : zm ≠ (a : ℂ) := by
    intro h
    have := congrArg Complex.im h
    simp [zm, Complex.mul_im] at this
    exact ht.ne' this
  have hpEq := (hρdata (hK zp hzp)).2 (by simpa using hpne)
  have hmEq := (hρdata (hK zm hzm)).2 (by simpa using hmne)
  dsimp only at hpEq hmEq
  change (∑ k ∈ s, r k * cauchyPoleJumpKernel (k + 1) a t x) * φ x +
    (H' zp - H' zm) * φ x = (f zp / p zp - f zm / p zm) * φ x
  rw [hpEq, hmEq, show H' zp = H zp by simp [H', hzp],
    show H' zm = H zm by simp [H', hzm]]
  have hJ : (∑ k ∈ s, r k * cauchyPoleJumpKernel (k + 1) a t x) =
      (∑ k ∈ s, r k * ((zp - (a : ℂ))⁻¹) ^ (k + 1)) -
        ∑ k ∈ s, r k * ((zm - (a : ℂ))⁻¹) ^ (k + 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hep : zp - (a : ℂ) = (x : ℂ) - (a : ℂ) + (t : ℂ) * Complex.I := by dsimp [zp]; ring
    have hem : zm - (a : ℂ) = (x : ℂ) - (a : ℂ) - (t : ℂ) * Complex.I := by dsimp [zm]; ring
    rw [hep, hem, cauchyPoleJumpKernel, mul_sub]
  rw [hJ]
  ring

/-- A local analytic quotient has an exact integrated jump on all tests
in a common positive neighborhood of its real pole. -/
theorem analyticAt_quotient_jump_integral_tendsto
    (f p : ℂ → ℂ) (a : ℝ) (hf : AnalyticAt ℂ f (a : ℂ)) (hp : AnalyticAt ℂ p (a : ℂ))
    (hp' : analyticOrderAt p (a : ℂ) ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ r : ℕ → ℂ, ∀ φ : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, φ x ≠ 0 → |x - a| ≤ δ) →
      Tendsto (fun t : ℝ => ∫ x : ℝ,
        (f ((x : ℂ) + (t : ℂ) * Complex.I) / p ((x : ℂ) + (t : ℂ) * Complex.I) -
          f ((x : ℂ) - (t : ℂ) * Complex.I) / p ((x : ℂ) - (t : ℂ) * Complex.I)) * φ x)
        (𝓝[>] (0 : ℝ)) (𝓝 (∑ k ∈ Finset.range (analyticOrderNatAt p (a : ℂ)),
          r k * ((-2 * (Real.pi : ℂ) * Complex.I) * iteratedDeriv k φ a / (k.factorial : ℂ)))) := by
  obtain ⟨δ, hδ, r, _, _, _, hlim⟩ :=
    analyticAt_quotient_jump_integral_tendsto_with_principalPart f p a hf hp hp'
  exact ⟨δ, hδ, r, hlim⟩

end

end MeyerGeneralProblem
