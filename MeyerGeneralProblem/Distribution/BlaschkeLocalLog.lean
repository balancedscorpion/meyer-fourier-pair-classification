module

public import MeyerGeneralProblem.Distribution.BlaschkeHalfPlaneJensen
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

@[expose] public section

/-!
# Local complex logarithms at the real boundary

At a real point, the entire numerator splits into a power and a
nonvanishing factor. The logarithm in the upper half-plane splits
with the same power and a holomorphic remainder across the boundary.
-/

namespace MeyerGeneralProblem

noncomputable section

open ComplexConjugate Filter Metric Set
open scoped Topology

private theorem exists_local_exp_eq {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : AnalyticAt ℂ g z₀) (hg₀ : g z₀ ≠ 0) :
    ∃ W : ℂ → ℂ, AnalyticAt ℂ W z₀ ∧ ∀ᶠ z in 𝓝 z₀, Complex.exp (W z) = g z := by
  let k (z : ℂ) := g z / g z₀
  have hk : AnalyticAt ℂ k z₀ := hg.div_const
  have hk₀ : k z₀ = 1 := div_self hg₀
  let W (z : ℂ) := Complex.log (k z) + Complex.log (g z₀)
  have hSlit : k z₀ ∈ Complex.slitPlane := hk₀ ▸ Complex.one_mem_slitPlane
  refine ⟨W, (hk.clog hSlit).add analyticAt_const, ?_⟩
  filter_upwards [hg.continuousAt.eventually_ne hg₀] with z hz
  change Complex.exp (Complex.log (k z) + Complex.log (g z₀)) = g z
  rw [Complex.exp_add, Complex.exp_log (div_ne_zero hz hg₀), Complex.exp_log hg₀]
  exact div_mul_cancel₀ (g z) hg₀

/-- A holomorphic Blaschke logarithm has, on a small upper half-disk
at any real point, the principal logarithm of the displacement
multiplied by the local zero order, plus a holomorphic remainder. -/
theorem exists_local_upperHalfPlane_blaschkeLog_model {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).im) (hFin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hSum : Summable (fun i => upperHalfPlaneBlaschkeWeight (a i)))
    {H L : ℂ → ℂ} (hH : Differentiable ℂ H) (hH₀ : ∃ z, H z ≠ 0)
    (hL : AnalyticOnNhd ℂ L {z : ℂ | 0 < z.im})
    (hFactor : EqOn H (fun z => upperHalfPlaneBlaschkeProduct a z * Complex.exp (L z))
      {z : ℂ | 0 < z.im}) (x : ℝ) :
    ∃ (n : ℕ) (R : ℂ → ℂ) (δ : ℝ), 0 < δ ∧ AnalyticOnNhd ℂ R (ball (x : ℂ) δ) ∧
      (H (x : ℂ) = 0 ↔ 0 < n) ∧
      (∀ z ∈ ball (x : ℂ) δ, z ≠ (x : ℂ) → H z ≠ 0) ∧
      ∀ z ∈ ball (x : ℂ) δ, 0 < z.im →
        L z = (n : ℂ) * Complex.log (z - (x : ℂ)) + R z := by
  let X : ℂ := x
  let B := upperHalfPlaneBlaschkeProduct a
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  have hB : AnalyticAt ℂ B X := by
    apply analyticAt_upperHalfPlaneBlaschkeProduct_of_avoids_poles ha hFin hSum
    intro i he
    have hi := congrArg Complex.im he
    simp only [X, Complex.ofReal_im, Complex.conj_im] at hi
    linarith only [hi, ha i]
  have hB₀ : B X ≠ 0 := by
    rw [show B X = _ from upperHalfPlaneBlaschkeProduct_real ha hFin hSum x]
    exact Complex.exp_ne_zero _
  have hEntire : AnalyticOnNhd ℂ H univ := hH.differentiableOn.analyticOnNhd isOpen_univ
  have hHnear : ¬ ∀ᶠ z in 𝓝 X, H z = 0 := by
    intro he
    obtain ⟨z, hz⟩ := hH₀
    exact hz (hEntire.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ X) he (mem_univ z))
  obtain ⟨n, f, hf, hf₀, hModel⟩ :=
    (hEntire X (mem_univ X)).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hHnear
  have hOrder : H X = 0 ↔ 0 < n := by
    have hAt : H X = (X - X) ^ n • f X :=
      (show H =ᶠ[𝓝 X] (fun z => (z - X) ^ n • f z) from hModel).eq_of_nhds
    rw [hAt, sub_self, smul_eq_mul]
    by_cases hn : n = 0
    · simp [hn, hf₀]
    · simp [zero_pow hn, Nat.pos_of_ne_zero hn]
  let g (z : ℂ) := f z / B z
  have hg : AnalyticAt ℂ g X := hf.div hB hB₀
  have hg₀ : g X ≠ 0 := div_ne_zero hf₀ hB₀
  obtain ⟨W, hW, hExpW⟩ := exists_local_exp_eq hg hg₀
  have hInfo := hModel.and ((hB.continuousAt.eventually_ne hB₀).and
    (hW.eventually_analyticAt.and (hExpW.and (hf.continuousAt.eventually_ne hf₀))))
  obtain ⟨δ, hδ, hBall⟩ := Metric.mem_nhds_iff.mp hInfo
  let S := ball X δ ∩ U
  have hS : IsOpen S := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hSConv : Convex ℝ S := (convex_ball X δ).inter (convex_halfSpace_im_gt 0)
  have hSNonempty : S.Nonempty := by
    refine ⟨X + ((δ / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_I,
        Real.norm_of_nonneg (half_pos hδ).le, mul_one]
      exact half_lt_self hδ
    · change 0 < (X + ((δ / 2 : ℝ) : ℂ) * Complex.I).im
      simpa [X, Complex.mul_im] using half_pos hδ
  let K (z : ℂ) := L z - (n : ℂ) * Complex.log (z - X) - W z
  have hK : AnalyticOnNhd ℂ K S := by
    intro z hz
    have him : (z - X).im = z.im := by simp [X]
    have hSlit : z - X ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr (by
      rw [him]
      exact (show 0 < z.im from hz.2).ne'))
    have hLog : AnalyticAt ℂ (fun w => Complex.log (w - X)) z :=
      (analyticAt_id.sub analyticAt_const).clog hSlit
    exact ((hL z hz.2).sub (analyticAt_const.mul hLog)).sub (hBall hz.1).2.2.1
  have hKRe (z : ℂ) (hz : z ∈ S) : (K z).re = 0 := by
    obtain ⟨hHz, hBz, _, hWz, _⟩ := hBall hz.1
    have hLX : Complex.exp (L z) = H z / B z := (eq_div_iff hBz).mpr
      ((mul_comm _ _).trans (hFactor hz.2).symm)
    have hZ : z - X ≠ 0 := by
      intro he
      have him := congrArg Complex.im (sub_eq_zero.mp he)
      exact (show 0 < z.im from hz.2).ne' (by simpa [X] using him)
    have he : Complex.exp (L z) =
        Complex.exp ((n : ℂ) * Complex.log (z - X)) * Complex.exp (W z) := by
      rw [Complex.exp_nat_mul, Complex.exp_log hZ, hWz, hLX, hHz, smul_eq_mul, mul_div_assoc]
    have hKexp : Complex.exp (K z) = 1 := by
      simp only [K, Complex.exp_sub, he]
      field_simp [Complex.exp_ne_zero]
    have hNorm := congrArg norm hKexp
    rwa [Complex.norm_exp, norm_one, Real.exp_eq_one_iff] at hNorm
  obtain ⟨d, hd⟩ := hK.eq_re_add_const_mul_I_of_re_eq_const
    hKRe hS ⟨hSNonempty, hSConv.isPreconnected⟩
  refine ⟨n, (fun z => W z + (d : ℂ) * Complex.I), δ, hδ,
    fun z hz => (hBall hz).2.2.1.add analyticAt_const, hOrder, ?_, ?_⟩
  · intro z hz hne
    obtain ⟨hHz, _, _, _, hfz⟩ := hBall hz
    rw [hHz, smul_eq_mul]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hne)) hfz
  intro z hz hUpper
  have he := hd z ⟨hz, hUpper⟩
  simp only [K, Complex.ofReal_zero, zero_add] at he
  linear_combination he

end
end MeyerGeneralProblem
