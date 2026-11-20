module

public import MeyerGeneralProblem.Sampling.QuadraticSectorBound
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite whole-line Gaussian rates under an actual quadratic growth bound

An entire function with a supplied global quadratic norm bound is either
zero or has every positive whole-line Gaussian rate at most `B/pi`.
The proof uses the actual Gaussian twist on the whole complex plane,
four diagonal rays and six subcritical sectors, then Liouville and decay
on the real axis. No bounded-rate certificate or optimal-rate attainment
is assumed. This is a nonsharp finite-type bound, not Hardy uncertainty.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace MeyerGeneralProblem

/-- A positive whole-line Gaussian rate with a genuine positive finite
constant. The definition is zero-safe and does not take logarithms of E. -/
def HasWholeGaussianRate (E : ℂ → ℂ) (κ : ℝ) : Prop :=
  0 < κ ∧ ∃ C > 0, ∀ x : ℝ,
    ‖E (x : ℂ)‖ ≤ C*Real.exp (-2*Real.pi*κ*x^2)

private theorem gaussianTwist_norm (E : ℂ → ℂ) (K : ℝ) (z : ℂ) :
    ‖Complex.exp ((K : ℂ)*z^2)*E z‖ =
      Real.exp (K*(z^2).re)*‖E z‖ := by
  simp [Complex.norm_exp]

private theorem gaussianTwist_quadraticBound {E : ℂ → ℂ} {A B K : ℝ}
    (hK : 0 ≤ K) (hquad : ∀ z : ℂ, ‖E z‖ ≤ A*Real.exp (B*‖z‖^2)) (z : ℂ) :
    ‖Complex.exp ((K : ℂ)*z^2)*E z‖ ≤ A*Real.exp ((B+K)*‖z‖^2) := by
  rw [gaussianTwist_norm]
  have hre : (z^2).re ≤ ‖z‖^2 :=
    (Complex.re_le_norm (z^2)).trans_eq (Complex.norm_pow z 2)
  calc
    _ ≤ Real.exp (K*‖z‖^2)*(A*Real.exp (B*‖z‖^2)) := by
      apply mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hre hK))
        (hquad z) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring

private theorem gaussianTwist_realBound {E : ℂ → ℂ} {C κ K : ℝ}
    (hreal : ∀ x : ℝ, ‖E (x : ℂ)‖ ≤ C*Real.exp (-2*Real.pi*κ*x^2)) (x : ℝ) :
    ‖Complex.exp ((K : ℂ)*(x : ℂ)^2)*E (x : ℂ)‖ ≤
      C*Real.exp ((K-2*Real.pi*κ)*x^2) := by
  rw [gaussianTwist_norm]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  calc
    _ ≤ Real.exp (K*x^2)*(C*Real.exp (-2*Real.pi*κ*x^2)) :=
      mul_le_mul_of_nonneg_left (hreal x) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring

private theorem gaussian_fourRay_sq_re {r θ : ℝ}
    (hθ : θ = -(2*Real.pi/3) ∨ θ = -(Real.pi/3) ∨
      θ = Real.pi/3 ∨ θ = 2*Real.pi/3) :
    (((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))^2).re = -(r^2)/2 := by
  have hcos2 : Real.cos (2*Real.pi/3) = -(1/2 : ℝ) := by
    rw [show 2*Real.pi/3 = Real.pi-Real.pi/3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  have hcos : Real.cos θ^2 = (1/4 : ℝ) := by
    rcases hθ with rfl | rfl | rfl | rfl <;>
      norm_num [Real.cos_neg, Real.cos_pi_div_three, hcos2]
  have hdiff : Real.cos θ^2-Real.sin θ^2 = -(1/2 : ℝ) := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hcoords :
      (((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))^2).re =
        r^2*(Real.cos θ^2-Real.sin θ^2) := by
    simp [pow_two, Complex.mul_re, Complex.exp_re, Complex.exp_im]
    ring
  rw [hcoords, hdiff]
  ring

private theorem gaussian_fourRay_norm_sq (r θ : ℝ) :
    ‖(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)‖^2 = r^2 := by
  simp [Complex.norm_exp, sq_abs]

private theorem gaussianTwist_fourRayBound {E : ℂ → ℂ} {A B K : ℝ}
    (hA : 0 ≤ A) (hKB : 2*B ≤ K)
    (hquad : ∀ z : ℂ, ‖E z‖ ≤ A*Real.exp (B*‖z‖^2))
    (r θ : ℝ) (hθ : θ = -(2*Real.pi/3) ∨ θ = -(Real.pi/3) ∨
      θ = Real.pi/3 ∨ θ = 2*Real.pi/3) :
    ‖Complex.exp ((K : ℂ)*((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))^2)*
      E ((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))‖ ≤ A := by
  rw [gaussianTwist_norm, gaussian_fourRay_sq_re hθ]
  calc
    _ ≤ Real.exp (K*(-(r^2)/2))*(A*Real.exp (B*r^2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [gaussian_fourRay_norm_sq] using
        hquad ((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))
    _ = A*Real.exp ((B-K/2)*r^2) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ A := by
      apply mul_le_of_le_one_right hA
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg r))

private theorem gaussianTwist_eq_zero_of_bounded {E : ℂ → ℂ} {C κ K M : ℝ}
    (hE : Differentiable ℂ E) (hKκ : K < 2*Real.pi*κ)
    (hreal : ∀ x : ℝ, ‖E (x : ℂ)‖ ≤ C*Real.exp (-2*Real.pi*κ*x^2))
    (hbound : ∀ z : ℂ, ‖Complex.exp ((K : ℂ)*z^2)*E z‖ ≤ M) : E = 0 := by
  let G : ℂ → ℂ := fun z => Complex.exp ((K : ℂ)*z^2)*E z
  have hG : Differentiable ℂ G := by dsimp only [G]; fun_prop
  have hb : Bornology.IsBounded (Set.range G) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hbound z
  have hc (z : ℂ) : G z = G 0 := hG.apply_eq_apply_of_bounded hb z 0
  have hexp : Tendsto (fun x : ℝ => C*Real.exp ((K-2*Real.pi*κ)*x^2))
      atTop (𝓝 0) := by
    have hpow : Tendsto (fun x : ℝ => x^2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    have he := Real.tendsto_exp_atBot.comp
      (hpow.const_mul_atTop_of_neg (by linarith : K-2*Real.pi*κ < 0))
    simpa using tendsto_const_nhds.mul he
  have hn : ‖G 0‖ ≤ 0 := ge_of_tendsto hexp (Filter.Eventually.of_forall (fun x => by
    rw [← hc (x : ℂ)]
    exact gaussianTwist_realBound hreal x))
  have hzero : G 0 = 0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  funext z
  change E z = 0
  have hz : Complex.exp ((K : ℂ)*z^2)*E z = 0 := (hc z).trans hzero
  exact (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)

/-- An actual entire quadratic-growth bound forces every positive whole-line
Gaussian rate to be at most `B/pi`, unless the function is identically zero.
The zero alternative is retained explicitly; no supremum is formed and no
division by a value of the function occurs. -/
theorem eq_zero_or_gaussianRate_le_of_quadraticType {E : ℂ → ℂ}
    (hE : Differentiable ℂ E) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hquad : ∀ z : ℂ, ‖E z‖ ≤ A*Real.exp (B*‖z‖^2)) :
    E = 0 ∨ ∀ κ, HasWholeGaussianRate E κ → κ ≤ B/Real.pi := by
  classical
  by_cases hzero : E = 0
  · exact Or.inl hzero
  refine Or.inr ?_
  intro κ hrate
  by_contra hκB
  have hBκ : B < Real.pi*κ := by
    have h := (div_lt_iff₀ Real.pi_pos).mp (lt_of_not_ge hκB)
    nlinarith
  let K : ℝ := B+Real.pi*κ
  have hKB : 2*B < K := by dsimp only [K]; linarith
  have hKκ : K < 2*Real.pi*κ := by dsimp only [K]; linarith
  have hK : 0 ≤ K := (by linarith : 0 ≤ 2*B).trans hKB.le
  obtain ⟨_hκ, C, hC, hreal⟩ := hrate
  let G : ℂ → ℂ := fun z => Complex.exp ((K : ℂ)*z^2)*E z
  have hG : Differentiable ℂ G := by dsimp only [G]; fun_prop
  have hbound (z : ℂ) : ‖G z‖ ≤ max A C := by
    apply norm_le_of_quadraticGrowth_real_fourRays
      (G := G) (A := A) (B := B+K) (M := max A C)
      hG hA (add_nonneg hB hK) (hA.trans (le_max_left A C))
      (gaussianTwist_quadraticBound hK hquad)
    · intro x
      apply (gaussianTwist_realBound hreal x).trans
      apply le_trans _ (le_max_right A C)
      apply mul_le_of_le_one_right hC.le
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg x))
    · intro r _hr θ hθ
      exact (gaussianTwist_fourRayBound hA hKB.le hquad r θ hθ).trans
        (le_max_left A C)
  exact hzero (gaussianTwist_eq_zero_of_bounded hE hKκ hreal hbound)

end MeyerGeneralProblem
