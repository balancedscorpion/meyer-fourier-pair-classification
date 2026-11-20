module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# The exact radial kernel for the symmetric product

One logarithmic factor is the integral of this kernel beyond the
modulus of its carrier point. Multiplying by the linear count removes
the singular factor at zero and gives the sharp arctangent integral.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- The nonnegative kernel whose tail gives one factor's radial log. -/
def radialCarrierKernel (r t : ℝ) : ℝ := 2 * r ^ 2 / (t * (t ^ 2 + r ^ 2))

private theorem hasDerivAt_neg_log_radialCarrierKernel (r t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => -Real.log (1 + r ^ 2 / y ^ 2)) (radialCarrierKernel r t) t := by
  have ht' : t ^ 2 ≠ 0 := pow_ne_zero _ ht.ne'
  have ha : 0 < 1 + r ^ 2 / t ^ 2 := by positivity
  have hdiv := (hasDerivAt_const (x := t) (r ^ 2)).div ((hasDerivAt_id t).pow 2) ht'
  have hlog := (hdiv.const_add 1).log ha.ne'
  convert! hlog.neg using 1
  simp only [radialCarrierKernel, Pi.div_apply, Pi.pow_apply, id_eq, zero_mul, zero_sub,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp [ht.ne', ht', ha.ne', show t ^ 2 + r ^ 2 ≠ 0 by positivity]

private theorem tendsto_neg_log_radialCarrierKernel (r : ℝ) :
    Tendsto (fun t : ℝ => -Real.log (1 + r ^ 2 / t ^ 2)) atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => t ^ (2 : ℕ)) atTop atTop := tendsto_pow_atTop (by decide)
  have hz : Tendsto (fun t : ℝ => r ^ 2 / t ^ 2) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hp
  have h1 : Tendsto (fun t : ℝ => 1 + r ^ 2 / t ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hz
  simpa only [Function.comp_apply, Real.log_one, neg_zero] using
    (((Real.continuousAt_log (x := (1 : ℝ)) one_ne_zero).tendsto.comp h1).neg)

/-- Every positive carrier modulus gives the exact logarithmic tail integral. -/
theorem integral_radialCarrierKernel_Ioi (r s : ℝ) (hs : 0 < s) :
    (∫ t in Ioi s, radialCarrierKernel r t) = Real.log (1 + r ^ 2 / s ^ 2) := by
  simpa only [zero_sub, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_nonneg'
      (a := s) (g := fun t : ℝ => -Real.log (1 + r ^ 2 / t ^ 2))
      (g' := radialCarrierKernel r)
      (fun t ht => hasDerivAt_neg_log_radialCarrierKernel r t (hs.trans_le ht))
      (fun t ht => by unfold radialCarrierKernel; have ht' := hs.trans (mem_Ioi.mp ht); positivity)
      (tendsto_neg_log_radialCarrierKernel r)

/-- The radial kernel is integrable above any positive carrier modulus. -/
theorem integrableOn_radialCarrierKernel_Ioi (r s : ℝ) (hs : 0 < s) :
    IntegrableOn (radialCarrierKernel r) (Ioi s) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (g := fun t : ℝ => -Real.log (1 + r ^ 2 / t ^ 2)) (g' := radialCarrierKernel r)
    (fun t ht => hasDerivAt_neg_log_radialCarrierKernel r t (hs.trans_le ht))
    (fun t ht => by unfold radialCarrierKernel; have ht' := hs.trans (mem_Ioi.mp ht); positivity)
    (tendsto_neg_log_radialCarrierKernel r)

private theorem radialCarrierKernel_linear_Ioi (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun t => 2 * r ^ 2 / (t ^ 2 + r ^ 2)) (Ioi (0 : ℝ)) ∧
      (∫ t in Ioi (0 : ℝ), 2 * r ^ 2 / (t ^ 2 + r ^ 2)) = Real.pi * r := by
  let g (t : ℝ) := (2 * r) * Real.arctan (t / r)
  let w (t : ℝ) := 2 * r ^ 2 / (t ^ 2 + r ^ 2)
  have hder (t : ℝ) : HasDerivAt g (w t) t := by
    have he := ((Real.hasDerivAt_arctan' (t / r)).comp t
      ((hasDerivAt_id t).div_const r)).const_mul (2 * r)
    convert! he using 1
    dsimp only [w]
    field_simp [hr.ne', show t ^ 2 + r ^ 2 ≠ 0 by positivity]
    ring
  have hdiv : Tendsto (fun t : ℝ => t / r) atTop atTop := tendsto_id.atTop_div_const hr
  have harc : Tendsto (fun t : ℝ => Real.arctan (t / r)) atTop (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hdiv
  have hg : Tendsto g atTop (𝓝 ((2 * r) * (Real.pi / 2))) := tendsto_const_nhds.mul harc
  have hw (t : ℝ) : 0 ≤ w t := by dsimp [w]; positivity
  have hint : IntegrableOn w (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hder t) (fun t _ => hw t) hg
  refine ⟨hint, ?_⟩
  calc
    _ = (2 * r) * (Real.pi / 2) - g 0 :=
      integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hder t) hint hg
    _ = _ := by simp [g]; ring

/-- The linear-density comparison is integrable down to radius zero. -/
theorem integrableOn_radialCarrierKernel_linear_Ioi (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun t => 2 * r ^ 2 / (t ^ 2 + r ^ 2)) (Ioi (0 : ℝ)) :=
  (radialCarrierKernel_linear_Ioi r hr).1

/-- The linear-density comparison has exactly the mass `π r`. -/
theorem integral_radialCarrierKernel_linear_Ioi (r : ℝ) (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), 2 * r ^ 2 / (t ^ 2 + r ^ 2)) = Real.pi * r :=
  (radialCarrierKernel_linear_Ioi r hr).2

end

end MeyerGeneralProblem
