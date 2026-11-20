module

public import MeyerGeneralProblem.Distribution.TorusDirectionalHilbert
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Positive-time derivative of exponential damping in square-summable space

The rates need no uniform upper bound. A positive time margin bounds
the first and second scalar derivatives uniformly over all nonnegative
rates, which gives the derivative with respect to the square-summable norm.
-/

namespace MeyerGeneralProblem

noncomputable section

open Asymptotics Filter Set
open scoped Topology

private def dampingScalar (a t : ℝ) := Real.exp (-a * t)

private def dampingDerivative (a t : ℝ) := -a * dampingScalar a t

private theorem hasDerivAt_dampingScalar (a t : ℝ) :
    HasDerivAt (dampingScalar a) (dampingDerivative a t) t := by
  change HasDerivAt (fun x : ℝ => Real.exp (-a * x)) (-a * Real.exp (-a * t)) t
  simpa only [id_eq, mul_one, mul_comm (Real.exp (-a * t)) (-a)] using
    ((hasDerivAt_id t).const_mul (-a)).exp

private theorem hasDerivAt_dampingDerivative (a t : ℝ) :
    HasDerivAt (dampingDerivative a) (a ^ 2 * dampingScalar a t) t := by
  change HasDerivAt (fun x => -a * dampingScalar a x) (a ^ 2 * dampingScalar a t) t
  simpa only [dampingDerivative, mul_neg, neg_mul, neg_neg, pow_two, mul_assoc] using
    (hasDerivAt_dampingScalar a t).const_mul (-a)

private theorem rate_mul_dampingScalar_le_inv {a δ t : ℝ} (ha : 0 ≤ a)
    (hδ : 0 < δ) (ht : δ ≤ t) :
    a * dampingScalar a t ≤ δ⁻¹ := by
  rw [← one_div, le_div_iff₀ hδ]
  calc
    _ = (δ * a) * Real.exp (-a * t) := by unfold dampingScalar; ring
    _ ≤ (δ * a) * Real.exp (-(δ * a)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hδ.le ha)
      apply Real.exp_le_exp.mpr
      linarith only [mul_le_mul_of_nonneg_left ht ha]
    _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one _
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)

private theorem norm_dampingSecondDerivative_le {a δ t : ℝ} (ha : 0 ≤ a)
    (hδ : 0 < δ) (ht : δ ≤ t) :
    ‖a ^ 2 * dampingScalar a t‖ ≤ ((δ / 2)⁻¹) ^ 2 := by
  have hEq : a ^ 2 * dampingScalar a t = (a * dampingScalar a (t / 2)) ^ 2 := by
    rw [mul_pow, pow_two (dampingScalar a (t / 2))]
    unfold dampingScalar
    rw [← Real.exp_add]
    congr 2
    ring
  rw [hEq, Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (mul_nonneg ha (Real.exp_pos _).le)
    (rate_mul_dampingScalar_le_inv ha (half_pos hδ) (by linarith only [ht])) 2

private theorem norm_dampingScalar_taylor_remainder_le {a δ u v : ℝ} (ha : 0 ≤ a)
    (hδ : 0 < δ) (hu : δ ≤ u) (hv : δ ≤ v) :
    ‖dampingScalar a v - dampingScalar a u - (v - u) * dampingDerivative a u‖ ≤
      ((δ / 2)⁻¹) ^ 2 * ‖v - u‖ ^ 2 := by
  let J := Icc (min u v) (max u v)
  have huJ : u ∈ J := ⟨min_le_left _ _, le_max_left _ _⟩
  have hvJ : v ∈ J := ⟨min_le_right _ _, le_max_right _ _⟩
  have hδJ (x : ℝ) (hx : x ∈ J) : δ ≤ x := (le_min hu hv).trans hx.1
  have hDist (x : ℝ) (hx : x ∈ J) : ‖x - u‖ ≤ ‖v - u‖ := by
    change min u v ≤ x ∧ x ≤ max u v at hx
    rcases le_total u v with h | h
    · rw [min_eq_left h, max_eq_right h] at hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx.1),
        abs_of_nonneg (sub_nonneg.mpr h)]
      linarith only [hx.2]
    · rw [min_eq_right h, max_eq_left h] at hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hx.2),
        abs_of_nonpos (sub_nonpos.mpr h)]
      linarith only [hx.1]
  let B := ((δ / 2)⁻¹) ^ 2
  have hSlope (x : ℝ) (hx : x ∈ J) :
      ‖dampingDerivative a x - dampingDerivative a u‖ ≤ B * ‖v - u‖ := by
    refine ((convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (hasDerivAt_dampingDerivative a z).hasDerivWithinAt)
      (fun z hz => norm_dampingSecondDerivative_le ha hδ (hδJ z hz)) huJ hx).trans ?_
    exact mul_le_mul_of_nonneg_left (hDist x hx) (sq_nonneg _)
  let R (x : ℝ) := dampingScalar a x - (x - u) * dampingDerivative a u
  have hR (x : ℝ) : HasDerivAt R (dampingDerivative a x - dampingDerivative a u) x := by
    change HasDerivAt (dampingScalar a - fun y => (y - u) * dampingDerivative a u)
      (dampingDerivative a x - dampingDerivative a u) x
    simpa only [id_eq, one_mul] using
      (hasDerivAt_dampingScalar a x).sub
        (((hasDerivAt_id x).sub_const u).mul_const (dampingDerivative a u))
  have hM := (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (hR z).hasDerivWithinAt) hSlope huJ hvJ
  have hEq : R v - R u = dampingScalar a v - dampingScalar a u -
      (v - u) * dampingDerivative a u := by unfold R; ring
  rw [hEq] at hM
  simpa only [B, pow_two ‖v - u‖, mul_assoc] using hM

/-- Apply the multiplier `exp(-rate * t)` at a nonnegative time.
The time is clamped to zero externally so that this defines a function
on the real line for the positive-time derivative. -/
def lpExponentialDamping {ι : Type*} (rate : ι → ℝ) (hRate : ∀ i, 0 ≤ rate i) (t : ℝ) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  lpDiagonalMul (fun i => Complex.ofReal (dampingScalar (rate i) (max t 0))) zero_le_one
    (fun i => by
      rw [Complex.norm_real, dampingScalar, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (hRate i)) (le_max_right _ _)))

theorem lpExponentialDamping_apply {ι : Type*} (rate : ι → ℝ) (hRate : ∀ i, 0 ≤ rate i)
    (t : ℝ) (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    lpExponentialDamping rate hRate t f i =
      Complex.ofReal (Real.exp (-rate i * max t 0)) * f i := rfl

/-- Positive-time exponential damping of any square-summable sequence
has a norm derivative with the differentiated scalar coefficients. -/
theorem exists_lpExponentialDamping_hasDerivAt {ι : Type*}
    (rate : ι → ℝ) (hRate : ∀ i, 0 ≤ rate i) (f : lp (fun _ : ι => ℂ) 2)
    {t : ℝ} (ht : 0 < t) :
    ∃ v : lp (fun _ : ι => ℂ) 2,
      HasDerivAt (fun s : ℝ => lpExponentialDamping rate hRate s f) v t ∧
      ∀ i, v i = Complex.ofReal (-rate i * Real.exp (-rate i * t)) * f i := by
  let v := lpDiagonalMul (fun i => Complex.ofReal (dampingDerivative (rate i) t))
    (inv_nonneg.mpr ht.le) (fun i => by
      rw [Complex.norm_real, Real.norm_eq_abs, dampingDerivative, abs_mul, abs_neg,
        abs_of_nonneg (hRate i), abs_of_pos (show 0 < dampingScalar (rate i) t from Real.exp_pos _)]
      exact rate_mul_dampingScalar_le_inv (hRate i) ht le_rfl) f
  have hv (i : ι) : v i = Complex.ofReal (dampingDerivative (rate i) t) * f i := rfl
  refine ⟨v, hasDerivAt_iff_isLittleO_nhds_zero.mpr ?_, hv⟩
  let δ := t / 2
  have hδ : 0 < δ := half_pos ht
  let B := ((δ / 2)⁻¹) ^ 2
  let R (h : ℝ) := lpExponentialDamping rate hRate (t + h) f -
    lpExponentialDamping rate hRate t f - h • v
  have hBig : R =O[𝓝 0] (fun h : ℝ => h ^ 2) := by
    refine isBigO_iff.mpr ⟨B * ‖f‖, ?_⟩
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    have hh' : |h| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hh
    have ht' : δ ≤ t + h := by
      have h := (abs_lt.mp hh').1
      dsimp only [δ] at h ⊢
      linarith only [h]
    let K := B * ‖h‖ ^ 2
    have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hLe (i : ι) : ‖R h i‖ ≤ ‖(((K : ℂ) • f) : lp (fun _ : ι => ℂ) 2) i‖ := by
      have ht₀ : δ ≤ t := (half_lt_self ht).le
      simp only [R, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, hv,
        lpExponentialDamping_apply, max_eq_left (hδ.le.trans ht'), max_eq_left ht.le]
      have hEq :
          Complex.ofReal (dampingScalar (rate i) (t + h)) * f i -
              Complex.ofReal (dampingScalar (rate i) t) * f i -
                h • (Complex.ofReal (dampingDerivative (rate i) t) * f i) =
            Complex.ofReal (dampingScalar (rate i) (t + h) - dampingScalar (rate i) t -
              h * dampingDerivative (rate i) t) * f i := by
        simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_mul]
        ring
      change ‖Complex.ofReal (dampingScalar (rate i) (t + h)) * f i -
        Complex.ofReal (dampingScalar (rate i) t) * f i -
          h • (Complex.ofReal (dampingDerivative (rate i) t) * f i)‖ ≤ ‖(K : ℂ) • f i‖
      rw [hEq, norm_mul, Complex.norm_real, norm_smul, Complex.norm_real, Real.norm_of_nonneg hK]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [B, K, add_sub_cancel_left] using
        norm_dampingScalar_taylor_remainder_le (hRate i) hδ ht₀ ht'
    calc
      ‖R h‖ ≤ ‖(K : ℂ) • f‖ := lp.norm_mono (by norm_num) hLe
      _ = (B * ‖f‖) * ‖h ^ 2‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hK, norm_pow]
        unfold K
        ring
  exact hBig.trans_isLittleO (isLittleO_pow_id (by norm_num))

end
end MeyerGeneralProblem
