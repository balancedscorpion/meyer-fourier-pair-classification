module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

/-! A uniform reciprocal denominator bound for univariate restrictions of
a Lee–Yang polynomial to monomial curves in an ordered direction. -/

namespace MeyerGeneralProblem

private theorem linearFactors_norm_lower (s : Multiset ℂ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (hs : ∀ w ∈ s, 1 ≤ ‖w‖) :
    ‖(s.map ((0 : ℂ) - ·)).prod‖ * (1 - ‖z‖) ^ s.card ≤
      ‖(s.map (z - ·)).prod‖ := by
  induction s using Multiset.induction with
  | empty => simp
  | cons w s ih =>
    have hw := hs w (Multiset.mem_cons_self w s)
    have htail := ih (fun v hv => hs v (Multiset.mem_cons_of_mem hv))
    have hterm : ‖(0 : ℂ) - w‖ * (1 - ‖z‖) ≤ ‖z - w‖ := by
      rw [zero_sub, norm_neg, norm_sub_rev z w]
      have hprod : ‖z‖ ≤ ‖w‖ * ‖z‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg z)
      linarith [norm_sub_norm_le w z]
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ]
    calc
      _ = (‖0 - w‖ * (1 - ‖z‖)) *
          (‖(s.map ((0 : ℂ) - ·)).prod‖ * (1 - ‖z‖) ^ s.card) := by ring
      _ ≤ ‖z - w‖ * ‖(s.map (z - ·)).prod‖ :=
        mul_le_mul hterm htail (mul_nonneg (norm_nonneg _) (pow_nonneg (sub_nonneg.mpr hz) _))
          (norm_nonneg _)

/-- A polynomial root-free in the open unit disk has a polynomial lower
bound uniform in the phase of the test point. Roots on the boundary,
including their multiplicities, are allowed. -/
theorem polynomial_eval_norm_lower_of_unitDisc_rootFree (P : Polynomial ℂ)
    (hP : ∀ w : ℂ, ‖w‖ < 1 → P.eval w ≠ 0) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖P.eval 0‖ * (1 - ‖z‖) ^ P.natDegree ≤ ‖P.eval z‖ := by
  have hroots (w : ℂ) (hw : w ∈ P.roots) : 1 ≤ ‖w‖ := by
    exact le_of_not_gt fun hn => hP w hn (Polynomial.isRoot_of_mem_roots hw)
  have hsplit := IsAlgClosed.splits P
  rw [hsplit.natDegree_eq_card_roots, hsplit.eval_eq_prod_roots 0, hsplit.eval_eq_prod_roots z]
  simp only [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (linearFactors_norm_lower P.roots z hz hroots) (norm_nonneg _)

/-- Uniform growth near the unit circle on a radial restriction, with an
explicit exponent given by the degree of the polynomial. -/
theorem polynomial_eval_norm_lower_of_unitDisc_rootFree_radial (P : Polynomial ℂ)
    (hP : ∀ w : ℂ, ‖w‖ < 1 → P.eval w ≠ 0)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (t : ℝ) (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    ‖P.eval 0‖ * (t / 2) ^ P.natDegree ≤
      ‖P.eval (ζ * (Real.exp (-t) : ℂ))‖ := by
  have hnorm : ‖ζ * (Real.exp (-t) : ℂ)‖ = Real.exp (-t) := by
    rw [norm_mul, hζ, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hle : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have hdiff : t / 2 ≤ 1 - Real.exp (-t) := by
    rw [Real.exp_neg]
    have hpos : 0 < 1 + t := by positivity
    have hi : (Real.exp t)⁻¹ ≤ (1 + t)⁻¹ := by
      exact inv_anti₀ hpos (by simpa only [add_comm] using Real.add_one_le_exp t)
    have hrat : t / 2 ≤ 1 - (1 + t)⁻¹ := by
      apply (mul_le_mul_iff_left₀ hpos).mp
      field_simp
      nlinarith
    linarith
  have h := polynomial_eval_norm_lower_of_unitDisc_rootFree P hP
    (ζ * (Real.exp (-t) : ℂ)) (by rw [hnorm]; exact hle)
  rw [hnorm] at h
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hdiff _) (norm_nonneg _)).trans h

/-- The genuine Taylor coefficients of a polynomial quotient with a
root-free unit disk grow at most as a power of their order. The bound
depends only on the degree, the constant denominator coefficient and
the numerator's unit-disk bound. -/
theorem polynomialQuotient_taylorCoefficient_norm_le
    (P Q : Polynomial ℂ) (hP : ∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0)
    (M : ℝ) (hM : 0 ≤ M) (hQ : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖Q.eval z‖ ≤ M)
    (n : ℕ) :
    ‖iteratedDeriv n (fun z => Q.eval z / P.eval z) 0 / (n.factorial : ℂ)‖ ≤
      (Real.exp 1 * M / ‖P.eval 0‖) * (2 * (1 + (n : ℝ))) ^ P.natDegree := by
  let a : ℝ := 1 + (n : ℝ)
  let t : ℝ := 1 / a
  let r : ℝ := Real.exp (-t)
  let d := P.natDegree
  let B : ℝ := M * (2 * a) ^ d / ‖P.eval 0‖
  have ha : 0 < a := by positivity
  have ht : 0 < t := div_pos zero_lt_one ha
  have ht₁ : t ≤ 1 := (div_le_one ha).mpr (le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) n))
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  have hp₀ : 0 < ‖P.eval 0‖ := norm_pos_iff.mpr (hP 0 (by simp))
  have hdiff : DiffContOnCl ℂ (fun z => Q.eval z / P.eval z) (Metric.ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    apply Q.differentiable.differentiableOn.div P.differentiable.differentiableOn
    intro z hz
    exact hP z ((by simpa only [Metric.mem_closedBall, dist_zero_right] using
      Metric.closure_ball_subset_closedBall hz : ‖z‖ ≤ r).trans_lt hr₁)
  have hb (z : ℂ) (hz : z ∈ Metric.sphere 0 r) : ‖Q.eval z / P.eval z‖ ≤ B := by
    have hzr : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    let ζ := z / (r : ℂ)
    have hζ : ‖ζ‖ = 1 := by
      rw [show ζ = z / (r : ℂ) by rfl, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, hzr, div_self hr.ne']
    have heq : ζ * (Real.exp (-t) : ℂ) = z := by
      change z / (r : ℂ) * (r : ℂ) = z
      exact div_mul_cancel₀ _ (by exact_mod_cast hr.ne')
    have hl := polynomial_eval_norm_lower_of_unitDisc_rootFree_radial P hP ζ hζ t ht.le ht₁
    have hta' : t / 2 = (2 * a)⁻¹ := by
      rw [show t = a⁻¹ by simp [t], div_eq_mul_inv, mul_inv_rev]
    rw [heq, hta', inv_pow] at hl
    have hd : 0 < (2 * a) ^ d := by positivity
    have hPz : 0 < ‖P.eval z‖ := norm_pos_iff.mpr (hP z (hzr ▸ hr₁))
    rw [norm_div, div_le_iff₀ hPz]
    have hl' : ‖P.eval 0‖ / (2 * a) ^ d ≤ ‖P.eval z‖ := by
      simpa only [div_eq_mul_inv, d] using hl
    calc
      _ ≤ M := hQ z (hzr.trans_le hr₁.le)
      _ = B * (‖P.eval 0‖ / (2 * a) ^ d) := by
        dsimp [B]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hl' (by dsimp [B]; positivity)
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hdiff hb
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hrn : (r ^ n)⁻¹ ≤ Real.exp 1 := by
    dsimp [r]
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have hta : a * t = 1 := mul_div_cancel₀ _ ha.ne'
    have hna : (n : ℝ) ≤ a := by dsimp [a]; linarith
    have hprod := (mul_le_mul_of_nonneg_right hna ht.le).trans_eq hta
    linarith
  rw [norm_div, norm_natCast]
  calc
    _ ≤ B / r ^ n := (div_le_iff₀ hn).mpr
      (hc.trans_eq (by rw [mul_div_assoc, mul_comm (n.factorial : ℝ)]))
    _ ≤ B * Real.exp 1 := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hrn (by dsimp [B]; positivity)
    _ = _ := by dsimp [B, a, d]; ring


open Filter
open scoped Topology

/-- Formal power series whose entries are the actual complex Taylor coefficients at zero. -/
noncomputable def actualTaylorSeriesAtZero (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => iteratedDeriv n f 0 / (n.factorial : ℂ)

private theorem actualTaylorSeriesAtZero_mul (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    actualTaylorSeriesAtZero (f * g) = actualTaylorSeriesAtZero f * actualTaylorSeriesAtZero g := by
  ext n
  rw [actualTaylorSeriesAtZero, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hchoose :
      (n.choose j : ℂ) * (j.factorial : ℂ) * ((n - j).factorial : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj'
  have h0 (k : ℕ) : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  simp only [actualTaylorSeriesAtZero, PowerSeries.coeff_mk]
  field_simp [h0]
  linear_combination (iteratedDeriv j f 0 * iteratedDeriv (n - j) g 0) * hchoose

private theorem actualTaylorSeriesAtZero_polynomial (P : Polynomial ℂ) :
    actualTaylorSeriesAtZero (fun z => P.eval z) = (P : PowerSeries ℂ) := by
  have hd (n : ℕ) (P : Polynomial ℂ) (x : ℂ) :
      iteratedDeriv n (fun z => P.eval z) x = ((Polynomial.derivative^[n]) P).eval x := by
    induction n generalizing P x with
    | zero => rfl
    | succ n ih =>
      rw [iteratedDeriv_succ, show iteratedDeriv n (fun z => P.eval z) =
        fun x => ((Polynomial.derivative^[n]) P).eval x from funext (ih P),
        Polynomial.deriv, Function.iterate_succ_apply']
  ext n
  rw [actualTaylorSeriesAtZero, PowerSeries.coeff_mk, Polynomial.coeff_coe, hd,
    ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero n)

/-- Multiplication by the actual denominator in the formal series ring
recovers the numerator at every Taylor order. -/
theorem polynomial_mul_actualTaylorSeriesAtZero_div (P Q : Polynomial ℂ) (hP : P.eval 0 ≠ 0) :
    (P : PowerSeries ℂ) * actualTaylorSeriesAtZero (fun z => Q.eval z / P.eval z) =
      (Q : PowerSeries ℂ) := by
  let f (z : ℂ) := P.eval z
  let g (z : ℂ) := Q.eval z / P.eval z
  have hf : AnalyticAt ℂ f 0 := AnalyticOnNhd.eval_polynomial P 0 (Set.mem_univ 0)
  have hg : AnalyticAt ℂ g 0 := by
    exact (AnalyticOnNhd.eval_polynomial Q 0 (Set.mem_univ 0)).div hf hP
  have he : f * g =ᶠ[𝓝 0] (fun z => Q.eval z) := by
    filter_upwards [hf.continuousAt.eventually_ne hP] with z hz
    change f z * (Q.eval z / f z) = Q.eval z
    exact mul_div_cancel₀ _ hz
  rw [← actualTaylorSeriesAtZero_polynomial P, ← actualTaylorSeriesAtZero_mul f g hf hg,
    ← actualTaylorSeriesAtZero_polynomial Q]
  ext n
  simp only [actualTaylorSeriesAtZero, PowerSeries.coeff_mk, he.iteratedDeriv_eq]

end MeyerGeneralProblem
