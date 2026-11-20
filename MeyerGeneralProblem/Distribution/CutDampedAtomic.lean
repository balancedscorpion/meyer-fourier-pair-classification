module

public import MeyerGeneralProblem.Distribution.DampedAtomic

@[expose] public section

/-!
# Damping on either side of an arbitrary real spectral cut

The upper and lower heights damp the positive and negative cut records.
Moving the cut away from zero may amplify a bounded frequency interval.
The bounds retain those terms and yield the full weak boundary limit.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology

/-- The coefficient multiplier for the upper side at and above the cut,
and for the lower side below it. -/
def cutExponentialDamping (s x t : ℝ) : ℝ :=
  if s ≤ x then Real.exp (-2 * Real.pi * x * t) else Real.exp (2 * Real.pi * x * t)

theorem cutExponentialDamping_nonneg (s x t : ℝ) : 0 ≤ cutExponentialDamping s x t := by
  unfold cutExponentialDamping
  split <;> positivity

theorem cutExponentialDamping_tendsto (s x : ℝ) :
    Tendsto (cutExponentialDamping s x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hc : Continuous (cutExponentialDamping s x) := by
    unfold cutExponentialDamping
    split <;> fun_prop
  have h0 : cutExponentialDamping s x 0 = 1 := by simp [cutExponentialDamping]
  rw [← h0]
  exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem cutExponentialDamping_le_symmetric (s x t : ℝ) (ht : 0 ≤ t) :
    cutExponentialDamping s x t ≤
      Real.exp ((2 * Real.pi * t) * (2 * |s|)) * atomicExponentialDamping x t := by
  unfold cutExponentialDamping atomicExponentialDamping
  rw [← Real.exp_add]
  have hA : 0 ≤ 2 * Real.pi * t := by positivity
  split
  · rename_i hs
    apply Real.exp_le_exp.mpr
    have h : -x ≤ 2 * |s| - |x| := by
      by_cases hx : 0 ≤ x
      · rw [abs_of_nonneg hx]; linarith [abs_nonneg s]
      · rw [abs_of_neg (lt_of_not_ge hx)]
        linarith [neg_le_abs s]
    nlinarith [mul_le_mul_of_nonneg_left h hA]
  · rename_i hs
    apply Real.exp_le_exp.mpr
    have h : x ≤ 2 * |s| - |x| := by
      by_cases hx : 0 ≤ x
      · rw [abs_of_nonneg hx]; linarith [le_abs_self s]
      · rw [abs_of_neg (lt_of_not_ge hx)]; linarith [abs_nonneg s]
    nlinarith [mul_le_mul_of_nonneg_left h hA]

/-- Exponential damping controls every fixed polynomial weight on a half-line. -/
theorem polynomial_mul_exp_neg_le (a : ℝ) (ha : 0 < a) (N : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ N * Real.exp (-a * r) ≤
      (N.factorial : ℝ) / a ^ N * Real.exp a := by
  have H : (a * (1 + r)) ^ N / (N.factorial : ℝ) ≤ Real.exp (a * (1 + r)) :=
    Real.pow_div_factorial_le_exp (a * (1 + r)) (by positivity) N
  have hf : 0 < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have haN : 0 < a ^ N := pow_pos ha _
  have h := (div_le_iff₀ hf).mp H
  rw [mul_pow, mul_comm (a ^ N), ← le_div_iff₀ haN] at h
  calc
    _ ≤ (Real.exp (a * (1 + r)) * (N.factorial : ℝ) / a ^ N) * Real.exp (-a * r) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = _ := by
      rw [show Real.exp (a * (1 + r)) * (N.factorial : ℝ) / a ^ N =
        ((N.factorial : ℝ) / a ^ N) * Real.exp (a * (1 + r)) by ring,
        mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Any polynomially weighted summable array becomes absolutely
summable after damping at a positive height on the two sides. -/
theorem summable_norm_cutDamped {ι : Type*} (a : ι → ℝ) (b : ι → ℂ)
    (N : ℕ) (h : Summable (fun i => ‖b i‖ / (1 + |a i|) ^ N))
    (s t : ℝ) (ht : 0 < t) :
    Summable (fun i => cutExponentialDamping s (a i) t * ‖b i‖) := by
  let y := 2 * Real.pi * t
  let C := Real.exp (y * (2 * |s|)) * ((N.factorial : ℝ) / y ^ N * Real.exp y)
  have hy : 0 < y := by positivity
  have hpt (i : ι) :
      cutExponentialDamping s (a i) t * (1 + |a i|) ^ N ≤ C := by
    calc
      _ ≤ (Real.exp (y * (2 * |s|)) * atomicExponentialDamping (a i) t) * (1 + |a i|) ^ N :=
        mul_le_mul_of_nonneg_right (cutExponentialDamping_le_symmetric s (a i) t ht.le) (by positivity)
      _ = Real.exp (y * (2 * |s|)) * ((1 + |a i|) ^ N * Real.exp (-y * |a i|)) := by
        have he : atomicExponentialDamping (a i) t = Real.exp (-y * |a i|) := by
          unfold atomicExponentialDamping
          congr 1
          dsimp [y]
          ring
        rw [he]
        ring
      _ ≤ C := mul_le_mul_of_nonneg_left (polynomial_mul_exp_neg_le y hy N |a i| (abs_nonneg _))
        (Real.exp_pos _).le
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (cutExponentialDamping_nonneg _ _ _) (norm_nonneg _))
    _ (h.mul_left C)
  intro i
  have hp : 0 < (1 + |a i|) ^ N := by positivity
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hp).mpr
  calc
    _ = (cutExponentialDamping s (a i) t * (1 + |a i|) ^ N) * ‖b i‖ := by ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (hpt i) (norm_nonneg _)

theorem cutExponentialDamping_le_near_zero (s x : ℝ) {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    cutExponentialDamping s x t ≤ Real.exp (4 * Real.pi * |s|) := by
  calc
    _ ≤ Real.exp ((2 * Real.pi * t) * (2 * |s|)) * atomicExponentialDamping x t :=
      cutExponentialDamping_le_symmetric s x t ht
    _ ≤ Real.exp ((2 * Real.pi * t) * (2 * |s|)) :=
      mul_le_of_le_one_right (Real.exp_pos _).le (atomicExponentialDamping_le_one x ht)
    _ ≤ _ := Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_left ht₁ (show 0 ≤ 4 * Real.pi * |s| by positivity)])

/-- The damped coefficient sum at an arbitrary cut tends to the same
literal weighted atomic record on every Schwartz test. -/
theorem cutDampedAtomic_sum_tendsto (S : LocallyFiniteCarrier) (b : S.subtype → ℂ)
    (N : ℕ) (hs : Summable (weightedAtomicMassTerm S b N)) (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun t : ℝ => ∑' x : S.subtype, (cutExponentialDamping s x t : ℂ) * (b x * f x))
      (𝓝[>] (0 : ℝ)) (𝓝 (weightedAtomicDistribution S b N hs f)) := by
  rw [weightedAtomicDistribution_apply]
  have hl := (weightedAtomic_samples_summable S b N hs f).norm.mul_left (Real.exp (4 * Real.pi * |s|))
  apply tendsto_tsum_of_dominated_convergence hl
  · intro x
    have h := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp (cutExponentialDamping_tendsto s x)
    simpa only [Function.comp_def, Complex.ofReal_one, one_mul] using h.mul_const (b x * f x)
  · filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)),
      mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with t ht ht₁ x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cutExponentialDamping_nonneg _ _ _)]
    exact mul_le_mul_of_nonneg_right
      (cutExponentialDamping_le_near_zero s x (show 0 ≤ t from ht.le) ht₁.le) (norm_nonneg _)

end

end MeyerGeneralProblem
