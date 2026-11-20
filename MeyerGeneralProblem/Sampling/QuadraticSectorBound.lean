module

public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A global bound from six subcritical quadratic-growth sectors

An entire function of finite quadratic growth is controlled by its bounds on
the whole real axis and four rays at angles plus or minus pi/3 and 2*pi/3.
Six logarithmic strips of width pi/3 cover the punctured plane. The actual
quadratic growth gives strip exponent two, strictly less than three. The
origin uses the real-axis bound, and the negative-axis boundary is included.
No interior-sector or global boundedness conclusion is assumed.
-/

open Set Filter Asymptotics

namespace MeyerGeneralProblem

/-- A horizontal line exponentiates to the corresponding actual polar ray. -/
private theorem quadraticStrip_exp_on_horizontal {ζ : ℂ} {θ : ℝ}
    (hζ : ζ.im = θ) :
    Complex.exp ζ = (Real.exp ζ.re : ℂ)*Complex.exp ((θ : ℂ)*Complex.I) := by
  calc
    Complex.exp ζ = Complex.exp ((ζ.re : ℂ)+(θ : ℂ)*Complex.I) := by
      rw [← hζ, Complex.re_add_im]
    _ = (Real.exp ζ.re : ℂ)*Complex.exp ((θ : ℂ)*Complex.I) := by
      rw [Complex.exp_add, Complex.ofReal_exp]

/-- The actual quadratic norm bound supplies double-exponential strip growth
with exponent two, including negative real logarithmic coordinates. -/
private theorem quadraticStrip_growth {G : ℂ → ℂ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hquad : ∀ z : ℂ, ‖G z‖ ≤ A*Real.exp (B*‖z‖^2)) (ζ : ℂ) :
    ‖G (Complex.exp ζ)‖ ≤ A*Real.exp (B*Real.exp (2*|ζ.re|)) := by
  calc
    ‖G (Complex.exp ζ)‖ ≤ A*Real.exp (B*‖Complex.exp ζ‖^2) := hquad _
    _ = A*Real.exp (B*Real.exp (ζ.re+ζ.re)) := by
      rw [Complex.norm_exp, pow_two, ← Real.exp_add]
    _ ≤ A*Real.exp (B*Real.exp (2*|ζ.re|)) := by
      gcongr
      linarith [le_abs_self ζ.re]

/-- Actual bounds on the two rays of a sector of width less than pi/2
propagate to its closed logarithmic strip under genuine quadratic growth. -/
private theorem quadraticStrip_bound {G : ℂ → ℂ} {A B M l u : ℝ}
    (hG : Differentiable ℂ G) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hquad : ∀ z : ℂ, ‖G z‖ ≤ A*Real.exp (B*‖z‖^2))
    (hwidth : 0 < u-l) (hsubcritical : 2*(u-l) < Real.pi)
    (hl : ∀ r : ℝ, 0 ≤ r →
      ‖G ((r : ℂ)*Complex.exp ((l : ℂ)*Complex.I))‖ ≤ M)
    (hu : ∀ r : ℝ, 0 ≤ r →
      ‖G ((r : ℂ)*Complex.exp ((u : ℂ)*Complex.I))‖ ≤ M)
    {ζ : ℂ} (hζl : l ≤ ζ.im) (hζu : ζ.im ≤ u) :
    ‖G (Complex.exp ζ)‖ ≤ M := by
  apply PhragmenLindelof.horizontal_strip
    (f := fun w => G (Complex.exp w)) (z := ζ) (a := l) (b := u)
  · exact (hG.comp Complex.differentiable_exp).diffContOnCl
  · refine ⟨2, (lt_div_iff₀ hwidth).mpr hsubcritical, B, ?_⟩
    apply Asymptotics.IsBigO.of_bound A
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs, Real.abs_exp] using quadraticStrip_growth hA hB hquad z
  · intro z hz
    rw [quadraticStrip_exp_on_horizontal hz]
    exact hl _ (Real.exp_pos _).le
  · intro z hz
    rw [quadraticStrip_exp_on_horizontal hz]
    exact hu _ (Real.exp_pos _).le
  · exact hζl
  · exact hζu

/-- An entire function with actual quadratic growth and common bounds on the
real axis and the four displayed rays is bounded everywhere by that same
constant. Six closed sectors have width pi/3, so strip exponent two is strictly
subcritical. Zero and the negative axis are included. The retained nonnegativity
of M already follows from the real-axis hypothesis and is not otherwise needed. -/
theorem norm_le_of_quadraticGrowth_real_fourRays {G : ℂ → ℂ} {A B M : ℝ}
    (hG : Differentiable ℂ G) (hA : 0 ≤ A) (hB : 0 ≤ B) (_hM : 0 ≤ M)
    (hquad : ∀ z : ℂ, ‖G z‖ ≤ A*Real.exp (B*‖z‖^2))
    (hreal : ∀ x : ℝ, ‖G (x : ℂ)‖ ≤ M)
    (hrays : ∀ r : ℝ, 0 ≤ r → ∀ θ : ℝ,
      (θ=-(2*Real.pi/3) ∨ θ=-(Real.pi/3) ∨ θ=Real.pi/3 ∨ θ=2*Real.pi/3) →
        ‖G ((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))‖ ≤ M)
    (z : ℂ) : ‖G z‖ ≤ M := by
  by_cases hz : z=0
  · simpa only [hz, Complex.ofReal_zero] using hreal 0
  have hzero (r : ℝ) (_hr : 0 ≤ r) :
      ‖G ((r : ℂ)*Complex.exp (((0 : ℝ) : ℂ)*Complex.I))‖ ≤ M := by
    simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] using hreal r
  have hpi (r : ℝ) (_hr : 0 ≤ r) :
      ‖G ((r : ℂ)*Complex.exp ((Real.pi : ℂ)*Complex.I))‖ ≤ M := by
    simpa only [Complex.exp_pi_mul_I, mul_neg_one, Complex.ofReal_neg] using hreal (-r)
  have hnegpi (r : ℝ) (_hr : 0 ≤ r) :
      ‖G ((r : ℂ)*Complex.exp (((-Real.pi : ℝ) : ℂ)*Complex.I))‖ ≤ M := by
    simpa only [Complex.ofReal_neg, neg_mul, Complex.exp_neg_pi_mul_I, mul_neg_one] using
      hreal (-r)
  have hm2 := fun r hr => hrays r hr (-(2*Real.pi/3)) (Or.inl rfl)
  have hm1 := fun r hr => hrays r hr (-(Real.pi/3)) (Or.inr (Or.inl rfl))
  have hp1 := fun r hr => hrays r hr (Real.pi/3) (Or.inr (Or.inr (Or.inl rfl)))
  have hp2 := fun r hr => hrays r hr (2*Real.pi/3) (Or.inr (Or.inr (Or.inr rfl)))
  have hlo : -Real.pi ≤ (Complex.log z).im := (Complex.neg_pi_lt_log_im z).le
  have hhi : (Complex.log z).im ≤ Real.pi := Complex.log_im_le_pi z
  rw [← Complex.exp_log hz]
  by_cases h1 : (Complex.log z).im ≤ -(2*Real.pi/3)
  · exact quadraticStrip_bound hG hA hB hquad
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hnegpi hm2 hlo h1
  by_cases h2 : (Complex.log z).im ≤ -(Real.pi/3)
  · exact quadraticStrip_bound hG hA hB hquad
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hm2 hm1
      (lt_of_not_ge h1).le h2
  by_cases h3 : (Complex.log z).im ≤ 0
  · exact quadraticStrip_bound hG hA hB hquad
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hm1 hzero
      (lt_of_not_ge h2).le h3
  by_cases h4 : (Complex.log z).im ≤ Real.pi/3
  · exact quadraticStrip_bound hG hA hB hquad
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hzero hp1
      (lt_of_not_ge h3).le h4
  by_cases h5 : (Complex.log z).im ≤ 2*Real.pi/3
  · exact quadraticStrip_bound hG hA hB hquad
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hp1 hp2
      (lt_of_not_ge h4).le h5
  · exact quadraticStrip_bound hG hA hB hquad
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hp2 hpi
      (lt_of_not_ge h5).le hhi

end MeyerGeneralProblem
