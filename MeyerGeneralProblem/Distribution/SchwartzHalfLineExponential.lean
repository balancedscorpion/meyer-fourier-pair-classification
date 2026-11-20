module

public import MeyerGeneralProblem.Distribution.TemperedAtomicHalfCut
public import MeyerGeneralProblem.Distribution.CutDampedAtomic
public import MeyerGeneralProblem.Cardinal.Adaptive.UniformSchwartzTails

@[expose] public section

/-!
# Half-line exponential Schwartz tests

An exponential that decays on the right is made into a Schwartz test
without changing it at or above a fixed left endpoint. All Schwartz
seminorms are bounded uniformly on compact parameter ranges strictly
inside the decaying half-plane.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped ContDiff Topology

private def halfLineExponentialProfile (b : ℝ) (w : ℂ) (x : ℝ) : ℂ :=
  (Real.smoothTransition (x - b + 1) : ℂ) * Complex.exp (w * (x : ℂ))

private theorem iteratedDeriv_cexp_mul_real (w : ℂ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (w * (y : ℂ))) x =
      w ^ n * Complex.exp (w * (x : ℂ)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    have hcomplex : HasDerivAt (fun z : ℂ => Complex.exp (w * z))
        (Complex.exp (w * (x : ℂ)) * w) (x : ℂ) := by
      simpa only [id_eq, mul_one] using (((hasDerivAt_id (x : ℂ)).const_mul w).cexp)
    have hreal : HasDerivAt (fun y : ℝ => Complex.exp (w * (y : ℂ)))
        (Complex.exp (w * (x : ℂ)) * w) x := by
      simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
        hcomplex.comp x Complex.ofRealCLM.hasDerivAt
    rw [(hreal.const_mul (w ^ n)).deriv, pow_succ]
    ac_rfl

private theorem halfLine_exp_weight_le (b a M : ℝ) (ha : 0 < a) (hM : 0 ≤ M)
    (q : ℕ) (w : ℂ) (hw : w.re ≤ -a) (hwM : ‖w‖ ≤ M)
    (x : ℝ) (hx : b - 1 ≤ x) :
    (1 + |x|) ^ q * Real.exp (w.re * x) ≤
      (q.factorial : ℝ) / a ^ q * Real.exp a +
        (1 + max 0 (1 - b)) ^ q * Real.exp (M * max 0 (1 - b)) := by
  by_cases hx0 : 0 ≤ x
  · rw [abs_of_nonneg hx0]
    calc
      _ ≤ (1 + x) ^ q * Real.exp (-a * x) := by
        gcongr
      _ ≤ _ := (polynomial_mul_exp_neg_le a ha q x hx0).trans (le_add_of_nonneg_right (by positivity))
  · have hxB : |x| ≤ max 0 (1 - b) := by
      rw [abs_of_neg (lt_of_not_ge hx0)]
      exact (by linarith : -x ≤ 1 - b).trans (le_max_right _ _)
    have hre : w.re * x ≤ M * max 0 (1 - b) := by
      calc
        w.re * x ≤ |w.re * x| := le_abs_self _
        _ = |w.re| * |x| := abs_mul _ _
        _ ≤ _ := mul_le_mul (Complex.abs_re_le_norm w |>.trans hwM) hxB (abs_nonneg _) hM
    have h : (1 + |x|) ^ q * Real.exp (w.re * x) ≤
        (1 + max 0 (1 - b)) ^ q * Real.exp (M * max 0 (1 - b)) := by
      gcongr
    exact h.trans (le_add_of_nonneg_left (by positivity))

private theorem halfLineExponentialProfile_uniform_decay (b a M : ℝ)
    (ha : 0 < a) (hM : 0 ≤ M) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re ≤ -a → ‖w‖ ≤ M → ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (halfLineExponentialProfile b w) x‖ ≤ C := by
  let u (x : ℝ) : ℂ := Real.smoothTransition (x - b + 1)
  have hu : u.HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp
      (smoothTransition_hasTemperateGrowth.comp (by fun_prop))
  obtain ⟨d, B, hB, hb⟩ := hu.norm_iteratedFDeriv_le_uniform n
  let H := ((k + d).factorial : ℝ) / a ^ (k + d) * Real.exp a +
    (1 + max 0 (1 - b)) ^ (k + d) * Real.exp (M * max 0 (1 - b))
  let C := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B * (1 + M) ^ n * H
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => by dsimp [H]; positivity
  refine ⟨C, hC, fun w hw hwM x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hx : x < b - 1
  · have he : halfLineExponentialProfile b w =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp only [halfLineExponentialProfile, Real.smoothTransition.zero_of_nonpos (by linarith [show y < b - 1 from hy] : y - b + 1 ≤ 0),
        Complex.ofReal_zero, zero_mul]
    rw [he.iteratedDeriv_eq n]
    simpa [iteratedDeriv_const] using hC
  · have huw : ContDiff ℝ ∞ (fun y : ℝ => Complex.exp (w * (y : ℂ))) :=
      Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
    change ‖x‖ ^ k * ‖iteratedDeriv n
      (fun y : ℝ => u y * Complex.exp (w * (y : ℂ))) x‖ ≤ C
    rw [iteratedDeriv_fun_mul (hu.1.of_le (by simp)).contDiffAt (huw.of_le (by simp)).contDiffAt]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hiu := hb i hin x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hiu
    have hwPow : ‖w‖ ^ (n - i) ≤ (1 + M) ^ n :=
      (pow_le_pow_left₀ (norm_nonneg _) (hwM.trans (by linarith)) _).trans
        (pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _))
    have hxPow : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
    have hwExp : (w * (x : ℂ)).re = w.re * x := by simp [Complex.mul_re]
    have hweight : (1 + ‖x‖) ^ (k + d) * Real.exp (w.re * x) ≤ H := by
      simpa only [Real.norm_eq_abs, H] using
        halfLine_exp_weight_le b a M ha hM (k + d) w hw hwM x (le_of_not_gt hx)
    rw [iteratedDeriv_cexp_mul_real, norm_mul, norm_mul, norm_mul, Complex.norm_natCast,
      norm_pow, Complex.norm_exp, hwExp]
    calc
      _ ≤ (1 + ‖x‖) ^ k * ((n.choose i : ℝ) * (B * (1 + ‖x‖) ^ d) *
          ((1 + M) ^ n * Real.exp (w.re * x))) := by gcongr
      _ = ((n.choose i : ℝ) * B * (1 + M) ^ n) *
          ((1 + ‖x‖) ^ (k + d) * Real.exp (w.re * x)) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)

/-- The actual right-sided Schwartz test of a decaying complex exponential. -/
def halfLineExponentialTest (b : ℝ) (w : ℂ) (hw : w.re < 0) : SchwartzMap ℝ ℂ where
  toFun := halfLineExponentialProfile b w
  smooth' := (Complex.ofRealCLM.contDiff.comp
      (Real.smoothTransition.contDiff.comp (by fun_prop))).mul
    (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))
  decay' k n := by
    obtain ⟨C, _, hC⟩ := halfLineExponentialProfile_uniform_decay b (-w.re) ‖w‖
      (neg_pos.mpr hw) (norm_nonneg _) k n
    exact ⟨C, hC w (by linarith) le_rfl⟩

/-- On the entire required half-line the test equals the uncut exponential. -/
theorem halfLineExponentialTest_apply_of_le (b : ℝ) (w : ℂ) (hw : w.re < 0)
    (x : ℝ) (hx : b ≤ x) :
    halfLineExponentialTest b w hw x = Complex.exp (w * (x : ℂ)) := by
  change halfLineExponentialProfile b w x = _
  simp only [halfLineExponentialProfile,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x - b + 1), Complex.ofReal_one, one_mul]

/-- The actual action of every tempered distribution is uniformly bounded on
these exponentially damped tests when the decay rate is bounded away from zero. -/
theorem halfLineExponentialTest_pairing_uniform_bound (T : TemperedDistribution ℝ ℂ)
    (b a M : ℝ) (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : ℂ) (hw : w.re < 0), w.re ≤ -a → ‖w‖ ≤ M →
      ‖T (halfLineExponentialTest b w hw)‖ ≤ C := by
  let E := {w : ℂ // w.re ≤ -a ∧ ‖w‖ ≤ M}
  let f (w : E) : SchwartzMap ℝ ℂ :=
    halfLineExponentialTest b w (lt_of_le_of_lt w.property.1 (by linarith))
  have h : Adaptive.SchwartzFamilyBounded f := by
    intro k n
    obtain ⟨C, hC, hbound⟩ := halfLineExponentialProfile_uniform_decay b a M ha hM k n
    refine ⟨C, hC, fun w => SchwartzMap.seminorm_le_bound ℂ k n _ hC ?_⟩
    exact hbound w w.property.1 w.property.2
  let q := (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨C, hC, hbound⟩ := h.continuous_seminorm q hq
  exact ⟨C, hC, fun w _ hw hwm => hbound ⟨w, hw, hwm⟩⟩

end

end MeyerGeneralProblem
