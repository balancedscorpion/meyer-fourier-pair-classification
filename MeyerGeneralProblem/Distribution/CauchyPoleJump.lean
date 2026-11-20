module

public import MeyerGeneralProblem.Cardinal.Strong.CauchyJump
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Boundary jump of an isolated Cauchy pole of any order

The simple-pole limit is the existing Poisson profile calculation.
Integration by parts obtains all higher pole orders and keeps the
sign and factorial of the positive-height boundary convention.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Filter Set
open scoped Topology SchwartzMap

/-- Upper-minus-lower Cauchy kernel for a pole of order `k` at `a`. -/
def cauchyPoleJumpKernel (k : ℕ) (a t x : ℝ) : ℂ :=
  ((x : ℂ) - (a : ℂ) + (t : ℂ) * Complex.I)⁻¹ ^ k -
    ((x : ℂ) - (a : ℂ) - (t : ℂ) * Complex.I)⁻¹ ^ k

private theorem tendsto_cauchyPoleJump_one (a : ℝ) (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, cauchyPoleJumpKernel 1 a t x * φ x)
      (𝓝[>] (0 : ℝ)) (𝓝 ((-2 * (Real.pi : ℂ) * Complex.I) * φ a)) := by
  simpa only [cauchyPoleJumpKernel, StrongParity.realPoleJump, pow_one,
    one_div, mul_one, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sub, neg_mul] using
      StrongParity.realPoleJump_integral_tendsto 1 φ.integrable
        (φ.continuous.continuousAt (x := a))

private theorem hasDerivAt_cauchyPoleJumpKernel (k : ℕ) (a t x : ℝ) (ht : 0 < t) :
    HasDerivAt (cauchyPoleJumpKernel (k + 1) a t)
      (-((k + 1 : ℕ) : ℂ) * cauchyPoleJumpKernel (k + 2) a t x) x := by
  let c := (t : ℂ) * Complex.I
  have hplus : (x : ℂ) - (a : ℂ) + c ≠ 0 := by
    intro h
    have he := congrArg Complex.im h
    simp [c, Complex.mul_im] at he
    exact ht.ne' he
  have hminus : (x : ℂ) - (a : ℂ) - c ≠ 0 := by
    intro h
    have he := congrArg Complex.im h
    simp [c, Complex.mul_im] at he
    exact ht.ne' he
  have hbase : HasDerivAt (fun y : ℂ => y - (a : ℂ)) (1 : ℂ) (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).sub_const _
  have hpole (δ : ℂ) (hd : (x : ℂ) - a + δ ≠ 0) :
      HasDerivAt (fun y : ℂ => (y - a + δ)⁻¹ ^ (k + 1))
        (-((k + 1 : ℕ) : ℂ) * ((x : ℂ) - a + δ)⁻¹ ^ (k + 2)) (x : ℂ) := by
    let d := (x : ℂ) - a + δ
    have h := ((hbase.add_const δ).fun_inv hd).fun_pow (k + 1)
    have he : ((k + 1 : ℕ) : ℂ) * d⁻¹ ^ k * (-1 / d ^ 2) =
        -((k + 1 : ℕ) : ℂ) * d⁻¹ ^ (k + 2) := by
      rw [pow_add d⁻¹ k 2, inv_pow, div_eq_mul_inv]
      ring_nf
    simpa only [Nat.add_sub_cancel, he, d] using h
  have hp := (hpole c hplus).comp_ofReal
  have hm := (hpole (-c) (by simpa only [sub_eq_add_neg] using hminus)).comp_ofReal
  convert! hp.sub hm using 1
  simp only [cauchyPoleJumpKernel, sub_eq_add_neg, c, mul_add, mul_neg]

/-- Every positive-height pole difference is continuous on the real line. -/
theorem continuous_cauchyPoleJumpKernel_succ (k : ℕ) (a t : ℝ) (ht : 0 < t) :
    Continuous (cauchyPoleJumpKernel (k + 1) a t) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_cauchyPoleJumpKernel k a t x ht).continuousAt

private theorem integral_cauchyPoleJump_succ_succ
    (k : ℕ) (a : ℝ) (φ : SchwartzMap ℝ ℂ) (hφ : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ, cauchyPoleJumpKernel (k + 2) a t x * φ x) =
      (((k + 1 : ℕ) : ℂ)⁻¹) *
        ∫ x : ℝ, cauchyPoleJumpKernel (k + 1) a t x * SchwartzMap.derivCLM ℂ ℂ φ x := by
  let N : ℂ := (k + 1 : ℕ)
  let u := cauchyPoleJumpKernel (k + 1) a t
  let v := cauchyPoleJumpKernel (k + 2) a t
  let ψ := SchwartzMap.derivCLM ℂ ℂ φ
  have hψ : HasCompactSupport ψ := by
    change HasCompactSupport (deriv (φ : ℝ → ℂ))
    exact hφ.deriv
  have hU : Continuous u := continuous_cauchyPoleJumpKernel_succ k a t ht
  have hV : Continuous v := continuous_cauchyPoleJumpKernel_succ (k + 1) a t ht
  have hprod : Integrable ((φ : ℝ → ℂ) * (fun x => -N * v x)) :=
    (φ.continuous.mul (continuous_const.mul hV)).integrable_of_hasCompactSupport (hφ.mul_right)
  have hleft : Integrable ((ψ : ℝ → ℂ) * u) :=
    (ψ.continuous.mul hU).integrable_of_hasCompactSupport hψ.mul_right
  have hmain : Integrable ((φ : ℝ → ℂ) * u) :=
    (φ.continuous.mul hU).integrable_of_hasCompactSupport hφ.mul_right
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable (u := (φ : ℝ → ℂ))
    (u' := (ψ : ℝ → ℂ)) (v := u) (v' := fun x => -N * v x)
    (fun x _ => by simpa only [ψ, SchwartzMap.derivCLM_apply] using φ.hasDerivAt x)
    (fun x _ => hasDerivAt_cauchyPoleJumpKernel k a t x ht)
    hprod hleft hmain
  have heq : (fun x : ℝ => φ x * (-N * v x)) = (fun x => -N * (v x * φ x)) := by
    funext x
    ac_rfl
  have heq' : (fun x : ℝ => ψ x * u x) = fun x => u x * ψ x := by
    funext x
    rw [mul_comm]
  rw [heq, integral_const_mul, heq'] at hparts
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast Nat.succ_ne_zero k
  change (∫ x : ℝ, v x * φ x) = N⁻¹ * ∫ x : ℝ, u x * ψ x
  apply mul_left_cancel₀ (neg_ne_zero.mpr hN)
  rw [hparts, ← mul_assoc, neg_mul, mul_inv_cancel₀ hN, neg_mul, one_mul]

/-- The exact upper-minus-lower jump of a pole of order `k + 1`,
tested against the original compact Schwartz test. -/
theorem tendsto_cauchyPoleJump_succ (k : ℕ) (a : ℝ) (φ : SchwartzMap ℝ ℂ) (hφ : HasCompactSupport φ) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, cauchyPoleJumpKernel (k + 1) a t x * φ x)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((-2 * (Real.pi : ℂ) * Complex.I) * iteratedDeriv k φ a / (k.factorial : ℂ))) := by
  induction k generalizing φ with
  | zero =>
    simpa only [Nat.zero_add, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] using
      tendsto_cauchyPoleJump_one a φ
  | succ k ih =>
    let ψ := SchwartzMap.derivCLM ℂ ℂ φ
    have hψ : HasCompactSupport ψ := by
      change HasCompactSupport (deriv (φ : ℝ → ℂ))
      exact hφ.deriv
    have hC (t : ℝ) (ht : 0 < t) := integral_cauchyPoleJump_succ_succ k a φ hφ t ht
    have hLimit := (ih ψ hψ).const_mul (((k + 1 : ℕ) : ℂ)⁻¹)
    have he : iteratedDeriv k ψ a = iteratedDeriv (k + 1) φ a := by
      rw [iteratedDeriv_succ']
      rfl
    rw [he] at hLimit
    convert hLimit.congr' (Filter.EventuallyEq.symm ?_) using 2
    · simp only [Nat.factorial_succ, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
      ring_nf
    · filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
      exact hC t ht


/-- A finite principal part contributes the sum of its exact jet rows. -/
theorem tendsto_cauchyPoleJump_finset (s : Finset ℕ) (r : ℕ → ℂ) (a : ℝ)
    (φ : SchwartzMap ℝ ℂ) (hφ : HasCompactSupport φ) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, (∑ k ∈ s, r k * cauchyPoleJumpKernel (k + 1) a t x) * φ x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ k ∈ s, r k *
        ((-2 * (Real.pi : ℂ) * Complex.I) * iteratedDeriv k φ a / (k.factorial : ℂ)))) := by
  have h := tendsto_finsetSum s fun k _ => (tendsto_cauchyPoleJump_succ k a φ hφ).const_mul (r k)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
  have hInt (k : ℕ) :
      Integrable (fun x : ℝ => (r k * cauchyPoleJumpKernel (k + 1) a t x) * φ x) :=
    ((continuous_const.mul (continuous_cauchyPoleJumpKernel_succ k a t ht)).mul
      φ.continuous).integrable_of_hasCompactSupport hφ.mul_left
  rw [show (fun x : ℝ => (∑ k ∈ s, r k * cauchyPoleJumpKernel (k + 1) a t x) * φ x) =
    (fun x => ∑ k ∈ s, (r k * cauchyPoleJumpKernel (k + 1) a t x) * φ x) by
      funext x; rw [Finset.sum_mul]]
  rw [integral_finsetSum _ (fun k _ => hInt k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun _ => (mul_assoc _ _ _).symm

end

end MeyerGeneralProblem
